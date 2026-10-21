"""Test evidence retention rather than interpreting solver output as proof."""

import hashlib
import importlib.util
import json
from pathlib import Path
import os
import select
import signal
import subprocess
import sys
import tempfile
import unittest


RUNNER = Path(__file__).with_name("tool_integration_run.py")
AUDITOR_PATH = RUNNER.parent / "audit_tool_records.py"
AUDITOR_SPEC = importlib.util.spec_from_file_location("integration_audit", AUDITOR_PATH)
AUDITOR = importlib.util.module_from_spec(AUDITOR_SPEC)
AUDITOR_SPEC.loader.exec_module(AUDITOR)


class ToolIntegrationRunTests(unittest.TestCase):
    def invoke(self, output, code, timeout="5"):
        return subprocess.run(
            [sys.executable, str(RUNNER), "--output", str(output),
             "--phase", "diagnostic", "--timeout", timeout, "--",
             sys.executable, "-c", code], capture_output=True, text=True,
            timeout=10,
        )

    def test_failed_command_preserves_status_and_both_streams(self):
        with tempfile.TemporaryDirectory() as root:
            output = Path(root) / "failure"
            run = self.invoke(output, "import sys; print('out'); print('err', file=sys.stderr); sys.exit(7)")
            self.assertEqual(run.returncode, 7)
            record = json.loads((output / "run.json").read_text())
            self.assertEqual((record["status"], record["returncode"]), ("completed", 7))
            self.assertFalse(record["proof_claim"])
            for name, content in [("stdout.txt", b"out\n"), ("stderr.txt", b"err\n")]:
                self.assertEqual((output / name).read_bytes(), content)
                self.assertEqual(record["streams"][name]["sha256"], hashlib.sha256(content).hexdigest())

    def test_timeout_keeps_partial_output_and_distinct_status(self):
        with tempfile.TemporaryDirectory() as root:
            output = Path(root) / "timeout"
            run = self.invoke(output, "import time; print('partial', flush=True); time.sleep(30)", "0.3")
            self.assertEqual(run.returncode, 124)
            record = json.loads((output / "run.json").read_text())
            self.assertEqual(record["status"], "timeout")
            self.assertIsNone(record["returncode"])
            self.assertEqual((output / "stdout.txt").read_text(), "partial\n")

    def test_success_cannot_overwrite_existing_evidence(self):
        with tempfile.TemporaryDirectory() as root:
            output = Path(root) / "success"
            self.assertEqual(self.invoke(output, "print('original')").returncode, 0)
            original = (output / "run.json").read_bytes()
            self.assertNotEqual(self.invoke(output, "print('replacement')").returncode, 0)
            self.assertEqual((output / "run.json").read_bytes(), original)
            self.assertEqual((output / "stdout.txt").read_text(), "original\n")

    def test_audit_detects_altered_output(self):
        with tempfile.TemporaryDirectory() as root:
            output = Path(root) / "runs" / "case"
            self.assertEqual(self.invoke(output, "print('recorded')").returncode, 0)
            self.assertEqual(AUDITOR.audit(Path(root))["integrity_errors"], [])
            (output / "stdout.txt").write_text("altered\n")
            self.assertTrue(AUDITOR.audit(Path(root))["integrity_errors"])

    def test_audit_rejects_unfinished_record_and_inferred_proof(self):
        with tempfile.TemporaryDirectory() as root:
            output = Path(root) / "runs" / "case"
            self.assertEqual(self.invoke(output, "pass").returncode, 0)
            path = output / "run.json"
            record = json.loads(path.read_text())
            record.update(status="running", proof_claim=True)
            path.write_text(json.dumps(record))
            self.assertEqual(len(AUDITOR.audit(Path(root))["integrity_errors"]), 2)

    def check_descendant_cleanup(self, interrupt):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            output = root / "runs" / "case"
            endpoint = root / "child.pipe"
            os.mkfifo(endpoint)
            child = (
                "import os,signal,time; "
                "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                f"fd=os.open({str(endpoint)!r},os.O_WRONLY); "
                "os.write(fd,b'r'); time.sleep(30)"
            )
            command = (
                "import subprocess,sys,time; "
                f"subprocess.Popen([sys.executable,'-c',{child!r}]); "
                "print('launched',flush=True); time.sleep(30)"
            )
            reader = os.open(endpoint, os.O_RDONLY | os.O_NONBLOCK)
            try:
                process = subprocess.Popen(
                    [sys.executable, str(RUNNER), "--output", str(output),
                     "--phase", "diagnostic", "--timeout", "2" if interrupt is None else "30",
                     "--", sys.executable, "-c", command],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                )
                try:
                    self.assertTrue(select.select([reader], [], [], 10)[0])
                    self.assertEqual(os.read(reader, 1), b"r")
                    if interrupt is not None:
                        process.send_signal(interrupt)
                    stdout, stderr = process.communicate(timeout=10)
                    # EOF establishes that the TERM-ignoring grandchild also exited.
                    self.assertTrue(select.select([reader], [], [], 3)[0])
                    self.assertEqual(os.read(reader, 1), b"")
                finally:
                    if process.poll() is None:
                        process.kill()
                        process.communicate()
                record = json.loads((output / "run.json").read_text())
                self.assertEqual(process.returncode, 124 if interrupt is None else 128 + interrupt)
                self.assertEqual(record["status"], "timeout" if interrupt is None else "interrupted")
                self.assertIsNone(record["returncode"])
                self.assertIn('launched', (output / "stdout.txt").read_text())
                self.assertNotIn("Traceback", stderr)
                self.assertIn(record["status"], stdout)
                if interrupt is not None:
                    self.assertEqual(record["interrupt_signal"], interrupt)
                self.assertEqual(AUDITOR.audit(root)["integrity_errors"], [])
            finally:
                os.close(reader)

    def test_interrupt_finalizes_evidence_and_stops_descendants(self):
        for interrupt in [signal.SIGINT, signal.SIGTERM]:
            with self.subTest(signal=interrupt):
                self.check_descendant_cleanup(interrupt)

    def test_timeout_stops_the_whole_group_including_term_ignoring_workers(self):
        self.check_descendant_cleanup(None)

    def test_nonfinite_timeout_is_rejected_before_launch(self):
        for timeout in ["nan", "inf"]:
            with self.subTest(timeout=timeout), tempfile.TemporaryDirectory() as root:
                output = Path(root) / "invalid"
                run = self.invoke(output, "raise RuntimeError('must not run')", timeout)
                self.assertEqual(run.returncode, 2)
                self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()

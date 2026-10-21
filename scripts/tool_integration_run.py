#!/usr/bin/env python3
"""Retain a bounded local tool invocation; a successful exit is not a proof."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import time


def stop_group(process):
    """Kill the bounded command group before reaping its leader.

    One SIGKILL also stops TERM-ignoring workers. Keeping the leader until this
    signal avoids losing group-signalling authority after it exits in a sandbox.
    """
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--phase", required=True, choices=["setup", "admission", "analysis", "check", "diagnostic"])
    parser.add_argument("--timeout", required=True, type=float)
    parser.add_argument("--cwd", type=Path, default=Path.cwd())
    parser.add_argument("--env", action="append", default=[])
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command or not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("a command and finite positive timeout are required")
    args.output.mkdir(parents=True, exist_ok=False)
    environment = os.environ.copy()
    overrides = {}
    for item in args.env:
        key, value = item.split("=", 1)
        if key in {"HOME", "home", "CODEX_HOME"}:
            parser.error("do not repurpose user home variables")
        overrides[key] = value
    environment.update(overrides)
    record = {
        "command": command, "phase": args.phase,
        "cwd": str(args.cwd.resolve()), "environment_overrides": overrides,
        "timeout_seconds": args.timeout,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "status": "running", "proof_claim": False,
    }
    record_path = args.output / "run.json"
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    started = time.monotonic()
    interrupted = None

    def on_signal(number, _frame):
        nonlocal interrupted
        if interrupted is None:
            interrupted = number

    handlers = {number: signal.signal(number, on_signal)
                for number in [signal.SIGINT, signal.SIGTERM]}
    process = None
    with (args.output / "stdout.txt").open("wb") as stdout, (args.output / "stderr.txt").open("wb") as stderr:
        try:
            process = subprocess.Popen(command, cwd=args.cwd, env=environment,
                                       stdin=subprocess.DEVNULL, stdout=stdout,
                                       stderr=stderr, start_new_session=True)
            record["process_group"] = process.pid
            record_path.write_text(json.dumps(record, indent=2) + "\n")
            deadline = started + args.timeout
            while True:
                if interrupted is not None:
                    stop_group(process)
                    returncode = 128 + interrupted
                    record.update(status="interrupted", returncode=None,
                                  termination_signal=signal.SIGKILL,
                                  interrupt_signal=interrupted,
                                  child_returncode=process.returncode)
                    break
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    stop_group(process)
                    returncode = 124
                    record.update(status="timeout", returncode=None, termination_signal=signal.SIGKILL)
                    break
                try:
                    returncode = process.wait(timeout=min(remaining, 0.2))
                except subprocess.TimeoutExpired:
                    continue
                if interrupted is not None:
                    continue
                record.update(status="completed", returncode=returncode)
                break
        except OSError as error:
            returncode = 127
            record.update(status="launch_error" if process is None else "cleanup_error",
                          returncode=None, error=str(error))
    record["seconds"] = time.monotonic() - started
    record["finished_utc"] = datetime.now(timezone.utc).isoformat()
    record["streams"] = {
        name: {"bytes": (args.output / name).stat().st_size,
               "sha256": hashlib.sha256((args.output / name).read_bytes()).hexdigest()}
        for name in ["stdout.txt", "stderr.txt"]
    }
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    for number, handler in handlers.items():
        signal.signal(number, handler)
    print(json.dumps({"output": str(args.output), "status": record["status"],
                      "returncode": record["returncode"], "seconds": record["seconds"]}))
    return returncode


if __name__ == "__main__":
    raise SystemExit(main())

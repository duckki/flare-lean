#!/usr/bin/env python3
"""Check retained invocation/stream integrity; do not interpret mathematical claims."""

from collections import Counter
import hashlib
import json
from pathlib import Path


def audit(root):
    counts = Counter()
    failures = []
    records = sorted((root / "runs").glob("*/run.json"))
    for path in records:
        record = json.loads(path.read_text())
        status = record.get("status")
        counts[status] += 1
        if status not in {"completed", "timeout", "launch_error", "interrupted", "cleanup_error"}:
            failures.append(f"{path.parent.name}: unfinished/unknown status {status}")
        if record.get("proof_claim") is not False:
            failures.append(f"{path.parent.name}: runner must not infer proof success")
        if status == "completed" and type(record.get("returncode")) is not int:
            failures.append(f"{path.parent.name}: missing command status")
        for name in ["stdout.txt", "stderr.txt"]:
            source = path.parent / name
            expected = record.get("streams", {}).get(name, {})
            if not source.exists():
                failures.append(f"{path.parent.name}: missing stream {name}")
                continue
            content = source.read_bytes()
            if expected != {"bytes": len(content), "sha256": hashlib.sha256(content).hexdigest()}:
                failures.append(f"{path.parent.name}: changed/unrecorded stream {name}")
    return {"records": len(records), "statuses": dict(counts),
            "integrity_errors": failures, "mathematical_proof_claim": False}


if __name__ == "__main__":
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root',type=Path,help='Run directory containing runs/*/run.json')
    result = audit(parser.parse_args().root.resolve())
    print(json.dumps(result, indent=2))
    raise SystemExit(bool(result["integrity_errors"]))

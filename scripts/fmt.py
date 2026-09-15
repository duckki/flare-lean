#!/usr/bin/env python3
"""Format FLARE's Lean sources at width 100, or check them without rewriting.

Adapted from graphql-lean's changed-file workflow. Git paths are NUL-delimited;
untracked initial sources and repositories without origin/main are supported.
"""

import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT).decode().split("\0")


def selected_files(base=None):
    if base is None:
        files = git("ls-files", "--cached", "--others", "--exclude-standard", "-z", "--", "*.lean")
    else:
        # An invalid or unavailable base must fail, never silently select no files.
        files = git("diff", "--name-only", "--diff-filter=ACMR", "-z", f"{base}...HEAD", "--", "*.lean")
        files += git("diff", "--name-only", "--diff-filter=ACMR", "-z", "HEAD", "--", "*.lean")
        files += git("ls-files", "--others", "--exclude-standard", "-z", "--", "*.lean")
    return sorted({name for name in files if name and (ROOT / name).is_file()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check without rewriting")
    parser.add_argument("--base", help="select changes since a Git merge base, plus working changes")
    parser.add_argument("--jobs", type=int, default=4, help="formatter workers (default: 4)")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    files = selected_files(args.base)
    if not files:
        print("No Lean files to format.")
        return 0
    return format_files(files, check=args.check, jobs=args.jobs)


def format_files(files, *, check=False, jobs=4):
    originals = {name: (ROOT / name).read_bytes() for name in files} if not check else {}
    command = ["lake", "exe", "fmt", "--line-width", "100", "--jobs", str(jobs)]
    if check:
        command.append("--check")
    # Keep ordinary --check separate from leanfmt's diagnostic modes: those modes
    # deliberately do not fail merely because a file needs formatting.
    result = subprocess.call([*command, *files], cwd=ROOT)
    damaged = []
    for name, original in originals.items():
        path = ROOT / name
        # v0.4.1 can drop an unparsed proof tail after an indentation error.
        # Its own token check misses that tail, so verify the complete source.
        if "".join(original.decode().split()) != "".join(path.read_text().split()):
            path.write_bytes(original)
            damaged.append(name)
    if damaged:
        print("Restored files after leanfmt changed non-whitespace content:\n"
              + "\n".join(damaged), file=sys.stderr)
        return 1
    return result


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)

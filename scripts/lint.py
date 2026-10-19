#!/usr/bin/env python3
"""FLARE lint driver.

Check selection adapted from graphql-lean's Lint.lean and Lint/ImportClosure.lean
at 41f1c4a240c30419c4ba0ffcdfeae612ee4d5810. Use Lean's dependency reader, include
untracked files, and keep the tooling outside the single public Lean library.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LINE_WIDTH = 100
FILE_LINE_LIMIT = 1500
ENTRY_POINTS = {"Flare.lean", "Tests/ProofAudit.lean", "Tests/PublicAPI.lean", "Lint.lean"}


def run(args, *, capture=False):
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=capture, check=True)


def source_files():
    output = run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        capture=True,
    ).stdout
    return sorted({name for name in output.split("\0") if name and (ROOT / name).is_file()})


def mask_lean_literals(source):
    """Hide nested comments and literals while retaining line/column positions."""
    result = list(source)
    i = depth = 0
    quoted = None
    while i < len(source):
        end = i + 1
        if depth:
            if source.startswith("/-", i):
                depth += 1
                end += 1
            elif source.startswith("-/", i):
                depth -= 1
                end += 1
        elif quoted:
            if source[i] == "\\" and quoted != "»":
                end = min(i + 2, len(source))
            elif source[i] == quoted:
                quoted = None
        elif source.startswith("/-", i):
            depth = 1
            end += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end < 0:
                end = len(source)
        elif source[i] in {'"', '«'}:
            quoted = '»' if source[i] == '«' else '"'
        elif source[i] == "'" and (char := re.match(r"'(?:\\.|[^'\n])'", source[i:])):
            end += len(char[0]) - 1
        else:
            i += 1
            continue
        for position in range(i, end):
            if result[position] != "\n":
                result[position] = " "
        i = end
    return "".join(result)


def style_issues(name, source):
    lean = name.endswith(".lean")
    lines = source.splitlines()
    code = mask_lean_literals(source).splitlines() if lean else [""] * len(lines)
    issues = []
    if source and not source.endswith("\n"):
        issues.append(f"{name}: missing final newline")
    if lean and len(lines) > FILE_LINE_LIMIT:
        issues.append(f"{name}: {len(lines)} lines exceeds {FILE_LINE_LIMIT}")
    for number, (line, code_line) in enumerate(zip(lines, code), 1):
        prefix = f"{name}:{number}: "
        if line.endswith((" ", "\t")):
            issues.append(prefix + "trailing whitespace")
        if "\t" in line:
            issues.append(prefix + "tab character")
        if not lean:
            continue
        if len(line) > LINE_WIDTH and not re.search(r"https?://", line):
            issues.append(prefix + f"line has {len(line)} columns; limit is {LINE_WIDTH}")
        if "λ" in code_line:
            issues.append(prefix + "use `fun` instead of lambda syntax")
        if "$" in code_line:
            issues.append(prefix + "use `<|` instead of dollar syntax")
        diagnostic = re.match(
            r"\s*set_option\s+(?:trace(?:\.|\s)|pp\.|profiler\b|maxHeartbeats\b|maxRecDepth\b)",
            code_line,
        )
        if diagnostic and not re.search(r"\bin\b", code_line):
            issues.append(prefix + "scope diagnostic/resource `set_option` with `in`")
        if re.fullmatch(r"\s*open\s+(?:scoped\s+)?Classical\s*", code_line):
            issues.append(prefix + "scope `open Classical` to a declaration")
        declaration = re.match(
            r"\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
            r"(?:def|theorem|lemma|abbrev|structure|inductive|class|instance)\s+([^\s({\[:]+)",
            code_line,
        )
        if declaration and "__" in declaration[1]:
            issues.append(prefix + "declaration name contains double underscore")
    return issues


def reachable_files(graph, roots):
    seen = set()
    pending = list(roots)
    while pending:
        node = pending.pop()
        if node not in seen:
            seen.add(node)
            pending.extend(graph.get(node, ()))
    return seen


def check_imports(files, jobs):
    def dependencies(name):
        result = run(["lake", "env", "lean", "--src-deps", name], capture=True)
        own = set()
        for line in result.stdout.splitlines():
            path = Path(line).resolve()
            if path.is_relative_to(ROOT):
                relative = path.relative_to(ROOT).as_posix()
                if relative in files:
                    own.add(relative)
        return name, own

    missing = ENTRY_POINTS - set(files)
    if missing:
        raise RuntimeError(f"Missing lint entry points: {', '.join(sorted(missing))}")
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        graph = dict(pool.map(dependencies, files))
    unreachable = set(files) - reachable_files(graph, ENTRY_POINTS)
    if unreachable:
        raise RuntimeError("Lean files outside the import closure:\n" + "\n".join(sorted(unreachable)))
    print(f"import-closure: ok ({len(files)} Lean files, including untracked files)", flush=True)


def check_proof_audit():
    # Library modules and Lint.lean are already linted by Lake's incremental build.
    # The audit is outside those targets, so elaborate it once with the same options.
    run(["lake", "env", "lean", "-D", "warningAsError=true", "-D",
         "linter.extra=true", "-D", "linter.missingDocs=false", "Tests/ProofAudit.lean"])
    run(["lake", "env", "lean", "-D", "warningAsError=true", "-D",
         "linter.extra=true", "-D", "linter.missingDocs=false", "Tests/PublicAPI.lean"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4,
                        help="concurrent import-closure checks (default: 4)")
    parser.add_argument("--style-only", action="store_true", help="run only the fast text checks")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    files = source_files()
    lean_files = [name for name in files if name.endswith(".lean")]
    if not lean_files:
        raise RuntimeError("No Lean files found; refusing an empty lint run")
    issues = [issue for name in files if name.endswith((".lean", ".md"))
              for issue in style_issues(name, (ROOT / name).read_text())]
    if issues:
        raise RuntimeError(f"community-style: {len(issues)} issue(s)\n" + "\n".join(issues))
    print(f"community-style: ok (Lean code/comments ≤ {LINE_WIDTH} columns; URLs exempt)", flush=True)
    if not args.style_only:
        run(["lake", "build", "Flare", "+Lint"])
        run(["python3", "scripts/check_layout.py"])
        check_imports(lean_files, args.jobs)
        check_proof_audit()
        print(f"lean-lint: ok ({len(lean_files)} files; incremental build; warnings are errors)",
              flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        if error.stdout:
            print(error.stdout, file=sys.stderr)
        if error.stderr:
            print(error.stderr, file=sys.stderr)
        sys.exit(error.returncode)
    except RuntimeError as error:
        print(error, file=sys.stderr)
        sys.exit(1)

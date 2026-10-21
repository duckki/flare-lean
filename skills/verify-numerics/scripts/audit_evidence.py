#!/usr/bin/env python3
"""Audit evidence records and render budgets; this is not a proof checker."""

import argparse
from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re


STATUSES = {"success", "timeout", "error", "not_run", "prerequisites_missing"}
LEVELS = {"native_checked", "model_checked", "analyzer", "none"}
RELATIONS = {"proved", "tested", "unproved", "not_applicable"}
VALIDITIES = {"proved", "model_only", "assumed", "unproved"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(text):
    require(isinstance(text, str), "Quantities must be exact rational strings")
    try:
        number = Fraction(text)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError("Invalid exact rational") from error
    require(number >= 0, "Bounds and limits must be nonnegative")
    return number


def unique(items, field):
    result = {}
    for item in items:
        key = item[field]
        require(isinstance(key, str) and key and key not in result, f"Invalid/duplicate {field}: {key}")
        result[key] = item
    return result


def audit(record, root):
    root = Path(root).resolve()
    require(record["schema_version"] == 1, "Unsupported record schema")
    task = record["task"]
    for key in ["id", "domain", "reference"]:
        require(isinstance(task[key], str) and task[key].strip(), f"Missing task {key}")
    targets = unique(task["targets"], "id")
    require(targets, "No engineering targets")
    for target in targets.values():
        require(rational(target["limit"]) > 0, "Target limit must be positive")
        require(target["quantity"] and target["unit"], "Target needs quantity and units")
    artifacts = unique(record["artifacts"], "id")
    for artifact in artifacts.values():
        path = (root / artifact["path"]).resolve()
        require(path.is_relative_to(root), "Evidence path escapes the project root")
        require(path.is_file(), f"Evidence file missing: {artifact['path']}")
        expected = artifact["sha256"]
        require(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected), "Invalid SHA-256")
        require(hashlib.sha256(path.read_bytes()).hexdigest() == expected,
                f"Stale evidence: {artifact['path']}")
    results = unique(record["results"], "id")
    require(results, "No comparison results")
    rows = []
    for result in results.values():
        require(result["target"] in targets, "Unknown target/property")
        target = targets[result["target"]]
        require(result["workflow"] and result["case"], "Missing workflow or source case")
        require(result["status"] in STATUSES, "Unknown result status")
        require(result["level"] in LEVELS, "Unknown evidence level")
        require(result["source_relation"] in RELATIONS, "Unknown source relation")
        require(result["validity"] in VALIDITIES, "Unknown validity status")
        require(result["evidence"] and all(e in artifacts for e in result["evidence"]),
                "Missing/unknown evidence artifact")
        require(result["limitations"] and all(isinstance(x, str) and x.strip()
                                              for x in result["limitations"]),
                "State the assurance/trust limitations")
        if result["status"] == "success":
            require(result["level"] != "none", "A completed bound needs an evidence level")
            bound = rational(result["bound"])
            if result["level"] == "native_checked":
                require(result["source_relation"] == "proved" and result["validity"] == "proved",
                        "Native checked claim needs proved source relation and validity")
            budget = "meets" if bound <= rational(target["limit"]) else "exceeds"
        else:
            require(result["bound"] is None and result["level"] == "none",
                    "An incomplete result cannot supply a checked/analyzed bound")
            budget = "unavailable"
        rows.append({**result, "quantity": target["quantity"], "unit": target["unit"],
                     "limit": target["limit"], "budget_status": budget,
                     "application_claim": {"native_checked": "native", "model_checked": "model only",
                                           "analyzer": "analyzer only", "none": "no bound"}[result["level"]]})
    return {"kind": "evidence_record_audit", "task": task, "artifact_count": len(artifacts),
            "qualification": "Hashes and record consistency only; named proofs/checker outputs require review.",
            "results": rows}


def markdown(review):
    def cell(text):
        return str(text).replace("|", "\\|").replace("\n", " ")
    def display(text):
        number = Fraction(text)
        with localcontext() as context:
            context.prec = 4
            context.rounding = ROUND_CEILING
            return format(Decimal(number.numerator) / Decimal(number.denominator), ".3E")
    lines = [f"# {cell(review['task']['id'])}", "", review["qualification"], "",
             "| Workflow | Case | Quantity | Upper allowance (approx.) | Budget (approx.) | Evidence | Outcome |",
             "|---|---|---|---:|---:|---|---|"]
    for row in review["results"]:
        bound = "—" if row["bound"] is None else f"{display(row['bound'])} {row['unit']}"
        limit = f"{display(row['limit'])} {row['unit']}"
        outcome = row["status"] if row["status"] != "success" else row["budget_status"]
        lines.append("| " + " | ".join(map(cell, [row["workflow"], row["case"], row["quantity"],
                     bound, limit, row["application_claim"], outcome])) + " |")
    lines += ["", "An upper allowance exceeding a budget does not establish an attained-error failure.",
              "", "## Scope and limitations", ""]
    for row in review["results"]:
        lines.append(f"- {cell(row['id'])}: " + "; ".join(map(cell, row["limitations"])))
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--json", type=Path)
    parser.add_argument("--markdown", type=Path)
    args = parser.parse_args()
    try:
        review = audit(json.loads(args.record.read_text()), args.root)
        output = json.dumps(review, indent=2) + "\n"
        if args.json:
            args.json.write_text(output)
        else:
            print(output, end="")
        if args.markdown:
            args.markdown.write_text(markdown(review))
    except (KeyError, TypeError, ValueError, OSError) as error:
        parser.exit(1, f"Evidence record rejected: {error}\n")


if __name__ == "__main__":
    main()

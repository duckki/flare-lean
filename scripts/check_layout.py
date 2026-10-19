#!/usr/bin/env python3
"""Check FLARE's module boundaries without third-party Python dependencies."""
from pathlib import Path
import re
from collections import Counter
from lint import mask_lean_literals

ROOT = Path(__file__).resolve().parents[1]
modules = {
    ".".join(path.relative_to(ROOT).with_suffix("").parts): path
    for path in (ROOT / "Flare").rglob("*.lean")
}

allowed_layers = {
    "Analysis": {"Analysis"},
    "Binary64": {"Analysis", "Binary64"},
    "Matrix": {"Analysis", "Binary64", "Matrix"},
}
external_roots = {"Init", "Std", "Mathlib"}


def imports(path):
    lines = re.findall(
        r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([^\n]+)",
        path.read_text(), re.MULTILINE,
    )
    return [name for line in lines for name in line.split("--", 1)[0].split()]


errors = []
for module, path in sorted(modules.items()):
    if not re.match(r"\s*module\b", mask_lean_literals(path.read_text())):
        errors.append(f"{module}: missing module-system header")
    layer = module.split(".")[1]
    if layer not in allowed_layers:
        errors.append(f"{module}: unrecognized module tree")
    if module.count(".") < 2:
        errors.append(f"{module}: use a subject module, not a directory aggregator")
    for dependency in imports(path):
        if dependency == "Flare":
            errors.append(f"{module}: internal module imports the public entry point")
        elif dependency.startswith("Flare."):
            if dependency not in modules:
                errors.append(f"{module}: missing module {dependency}")
            if dependency.split(".")[1] not in allowed_layers.get(layer, set()):
                errors.append(f"{module}: {layer} cannot depend on {dependency}")
        elif dependency.split(".")[0] not in external_roots:
            errors.append(f"{module}: unsupported external dependency {dependency}")

# Numerical runtime modules must remain independent of all ghost interpretations.
runtime = {"Flare.Matrix.Error", "Flare.Matrix.Dense", "Flare.Matrix.Operations"}
for module in sorted(runtime):
    if module not in modules:
        errors.append(f"Missing runtime module {module}")
        continue
    for dependency in imports(modules[module]):
        if dependency.startswith("Flare.") and dependency not in runtime:
            errors.append(f"{module}: runtime imports reasoning module {dependency}")
        if not dependency.startswith("Flare.") and dependency.split(".")[0] not in {"Init", "Std"}:
            errors.append(f"{module}: runtime imports proof infrastructure {dependency}")

entry_imports = imports(ROOT / "Flare.lean")
entry_source = mask_lean_literals((ROOT / "Flare.lean").read_text())
if not re.match(r"\s*module\b", entry_source):
    errors.append("Flare.lean: missing module-system header")
if re.search(r"^[ \t]*import\b", entry_source, re.MULTILINE):
    errors.append("Flare.lean: entry-point imports must be public")
exported = set(entry_imports)
for module in sorted(modules.keys() - exported):
    errors.append(f"Flare.lean does not include {module}")
for module in sorted(exported - modules.keys()):
    errors.append(f"Flare.lean imports an unknown library module: {module}")
for module, count in sorted(Counter(entry_imports).items()):
    if count > 1:
        errors.append(f"Flare.lean imports {module} more than once")
audit_source = mask_lean_literals((ROOT / "Tests/ProofAudit.lean").read_text())
audited = set(re.findall(r"^[ \t]*import[ \t]+all[ \t]+(Flare\.[\w.]+)",
                         audit_source, re.MULTILINE))
for module in sorted(modules.keys() - audited):
    errors.append(f"ProofAudit.lean does not import private data for {module}")
for module in sorted(audited - modules.keys()):
    errors.append(f"ProofAudit.lean audits an unknown library module: {module}")
if errors:
    raise SystemExit("\n".join(errors))
print(f"Checked {len(modules)} modules: import closure and runtime/analysis boundaries pass.")

"""Repository-owned provider resources, independent of package nesting."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MANIFESTS = ROOT / "provider/manifests"
PATCHES = ROOT / "provider/patches"

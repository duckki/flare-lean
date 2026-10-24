"""Run the checked-out provider without an installation step."""
from pathlib import Path
import runpy
import sys


def run(module):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "provider"))
    runpy.run_module(module, run_name="__main__")

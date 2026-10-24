"""Pinned CBMC witness proposer; its verdict never discharges a Lean premise."""
import json
from pathlib import Path
from .integration import Adapter
from .counterexample_search import produce,validate


PINS=json.loads((Path(__file__).resolve().parents[2]/'tools/numerics/cbmc.json').read_text())
def applicable(program,request):
    validate(request,program)


ADAPTERS=[Adapter('cbmc','witness-proposer','cbmc-json-trace-v1',
    'Strict-positivity scalar witness search followed by ordinary Lean counterexample checking.',
    produce,applicable,{'version':'6.11.0','nodes':32,'inputs':8,'properties':['strict_positive'],
        'arithmetic':'separate nearest/even binary64; no-witness is unresolved, never a proof'},PINS['setup'])]

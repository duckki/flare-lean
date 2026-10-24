"""Pinned CBMC witness proposer; its verdict never discharges a Lean premise."""
import json
from pathlib import Path
from numerics.paths import MANIFESTS
from numerics.integrations.registry import Adapter
from numerics.workflow.search import produce, validate


PINS=json.loads((MANIFESTS/'cbmc.json').read_text())
def applicable(program,request):
    validate(request,program)


ADAPTERS=[Adapter('cbmc','witness-proposer','cbmc-json-trace-v1',
    'Strict-positivity scalar witness search followed by ordinary Lean counterexample checking.',
    produce,applicable,{'version':'6.11.0','nodes':32,'inputs':8,'properties':['strict_positive'],
        'arithmetic':'separate nearest/even binary64; no-witness is unresolved, never a proof'},PINS['setup'])]

"""Method specialization tests: operation order, defaults, mutation and rejection."""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from numerics.frontend import parse, execute, word, Unsupported
from numerics.python_method import load_method
from numerics.workflow import certify, replay_run, save

SOURCE = '''
import deliberately_unavailable_dependency
class Filter(object):
    def update(self, z, g=None, h=None):
        if g is None:
            g = self.g
        if h is None:
            h = self.h
        self.dx_prediction = self.dx
        self.x_prediction = self.x + (self.dx*self.dt)
        self.y = z - self.x_prediction
        self.dx = self.dx_prediction + h * self.y / self.dt
        self.x = self.x_prediction + g * self.y
        return (self.x, self.dx)
'''
BINDING = {'state': {'x': 'x0', 'dx': 'v0'},
           'constants': {'dt': 0.125, 'g': 0.5, 'h': 0.125},
           'sequence': ['z'+str(i) for i in range(8)]}

class MethodTests(unittest.TestCase):
    def test_order_and_all_eight_original_method_calls(self):
        p = parse('python', SOURCE, 'Filter.update', BINDING)
        fn = load_method(SOURCE, 'Filter.update', BINDING)
        self.assertEqual(p.inputs, ('x0','v0',*(f'z{i}' for i in range(8))))
        ops = [n.op for n in p.nodes if n.op != 'constant']
        self.assertEqual(ops, ['mul','add','sub','mul','div','add','mul','add']*8)
        for args in [(10.,2.,*([-10.,10.]*4)), (-0.,0.,*([-0.]*8)),
                     (1e-300,-1e-300,*([1e-310,-1e-310]*4))]:
            self.assertEqual(tuple(map(word, execute(p,args))), tuple(map(word,fn(*args))))
        # A source arithmetic mutation must affect the admitted graph.
        changed = SOURCE.replace('self.dx*self.dt', 'self.dx/self.dt')
        self.assertNotEqual(p, parse('python',changed,'Filter.update',BINDING))

    def test_unsupported_semantics_are_rejected_before_execution(self):
        for old,new in [('h * self.y / self.dt','h * (self.y / self.dt) + external()'),
                        ('g = self.g','g = self.missing'),
                        ('return (self.x, self.dx)','return (self.dx, self.x)'),
                        ('self.dx_prediction = self.dx','self.dx_prediction = self.dx\n        escape(self)'),
                        ('self.dx_prediction = self.dx','self.g = 0.25'),
                        ('if g is None:', 'if z > 0:'),
                        ('class Filter(object):', 'class Filter(CustomBase):'),
                        ('    def update', '    @property\n    def update'),
                        ('    def update', '    def __setattr__(self, name, value): pass\n    def update'),
                        ('self.x_prediction + g * self.y', 'self.nested.x + g * self.y')]:
            with self.subTest(new=new), self.assertRaises(Unsupported):
                parse('python',SOURCE.replace(old,new),'Filter.update',BINDING)
        for change in [{'sequence':['z']*8}, {'constants':{'dt':1}}, {'state':{'x':'q','dx':'q'}},
                       {'constants':{'dt':float('inf')}}, {'constants':{'dt':float('nan')}},
                       {'state':{'x':'for','dx':'v'}}]:
            b = copy.deepcopy(BINDING); b.update(change)
            with self.assertRaises(Unsupported):
                parse('python',SOURCE,'Filter.update',b)

    def test_invalid_original_signature_is_rejected_before_specialization(self):
        source = SOURCE.replace('self, z, g=None, h=None', 'self, z, z=None, h=None')
        with self.assertRaisesRegex(Unsupported, 'not valid Python'):
            parse('python',source,'Filter.update',BINDING)


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1',
                     'Run make numerics-check for fresh method certificates')
class MethodWorkflowTests(unittest.TestCase):
    def test_eight_updates_certify_and_replay_without_source_runtime(self):
        with tempfile.TemporaryDirectory(prefix='flare-method-') as directory:
            root = Path(directory)
            (root/'source.py').write_text(SOURCE)
            request = {'schema':'numerics-request-v1','language':'python',
                'source':'source.py','function':'Filter.update','python_method':BINDING,
                'domain':{'x0':['-10','10'],'v0':['-2','2'],
                          **{name:['-10','10'] for name in BINDING['sequence']}},
                'outputs':[{'name':name,'unit':unit,'limit':'1/1000000'}
                           for name,unit in [('position','m'),('velocity','m/s')]],
                'specification':{'kind':'fold','initial':['x0','v0'],
                    'state':['position','velocity'],'element':'observation',
                    'sequence':BINDING['sequence'],
                    'step':['position + velocity * 0.125 + 0.5 * (observation - (position + velocity * 0.125))',
                            'velocity + 0.125 * (observation - (position + velocity * 0.125)) / 0.125']}}
            save(root/'request.json',request)
            result = certify(root/'request.json',root/'run')
            self.assertEqual(result['status'],'certified',result.get('error'))
            self.assertIn('source_diagnostics_checked',result['completed_stages'])
            frozen = json.loads((root/'run/request.json').read_text())
            self.assertEqual(frozen['python_method'],BINDING)
            self.assertIn('Module initialization, construction and dynamic dispatch',
                          '\n'.join(result['assumptions']))
            with patch('numerics.runtimes.source_results',side_effect=AssertionError('runtime called')), \
                 patch('numerics.workflow.analyze',side_effect=AssertionError('producer called')):
                self.assertEqual(replay_run(root/'run',root/'replay')['status'],'replayed')

if __name__ == '__main__':
    unittest.main()

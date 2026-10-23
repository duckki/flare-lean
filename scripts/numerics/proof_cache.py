"""Explicit local reuse of compiled helper contracts, with frozen-source replay.

Keys include the source module, provider/library identities and compiler profile.
The cache is a build optimization like Lake's compiled artifacts. Replay always
compiles saved sources afresh and never depends on this cache.
"""
import hashlib
import json
from pathlib import Path
import re
import shutil


class ProofCache:
    def __init__(self, root, dependencies, source_root=None):
        self.root = Path(root).expanduser().resolve() if root else None
        self.dependencies = dependencies
        self.source_root = source_root
        self.records = []

    def entry(self, source):
        from .workflow import sha
        text = source.read_text()
        imports = {}
        for name in re.findall(r'^public import (Workflow\.Functions\.[A-Za-z_0-9]+)$', text, re.MULTILINE):
            imports[name] = sha(self.source_root/(name.replace('.','/')+'.lean'))
        identity = {'schema':'numerics-contract-cache-v1', 'source':text, 'imports':imports,
                    'dependencies':self.dependencies, 'profile':'lean-checked-autoImplicit-false-warningAsError'}
        key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
        return key, self.root/key if self.root else None

    def restore(self, source, target):
        from .workflow import sha
        key, entry = self.entry(source)
        record = {'module':str(source).split('/lean/')[-1], 'identity':key, 'reused':False}
        self.records.append(record)
        if entry is None:
            return False
        try:
            metadata = json.loads((entry/'manifest.json').read_text())
            artifacts = metadata['artifacts']
            if (metadata.get('identity') != key or set(artifacts) != {'', '.private', '.server'} or
                    any(sha(entry/('module.olean'+suffix)) != digest for suffix,digest in artifacts.items())):
                return False
            for suffix in artifacts:
                shutil.copyfile(entry/('module.olean'+suffix), Path(str(target)+suffix))
            record['reused'] = True
            return True
        except (OSError, ValueError, KeyError, TypeError):
            return False

    def save(self, source, target):
        from .workflow import save, sha
        key, entry = self.entry(source)
        if entry is None:
            return
        entry.mkdir(parents=True, exist_ok=True)
        artifacts = {}
        for suffix in ['', '.private', '.server']:
            shutil.copyfile(Path(str(target)+suffix), entry/('module.olean'+suffix))
            artifacts[suffix] = sha(entry/('module.olean'+suffix))
        save(entry/'manifest.json', {'identity':key, 'artifacts':artifacts})


def local_imports(text):
    """Read local imports for scheduling/cache identity; Lean remains authoritative."""
    from lint import mask_lean_literals
    lines = re.findall(r'^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([^\n]+)',
                       mask_lean_literals(text), re.M)
    return [name for line in lines for name in line.split() if name.startswith('Workflow.')]


class ApplicationCache(ProofCache):
    """A module key includes its entire local import closure and model identity."""
    def entry(self, source):
        from .workflow import sha
        imports = {}
        active = set()
        def visit(path):
            if path in active:
                raise ValueError('Cyclic application proof-cache imports')
            active.add(path)
            for module in local_imports(path.read_text()):
                relative = module.replace('.', '/')+'.lean'
                dependency = self.source_root/relative
                if not dependency.is_file():
                    raise ValueError('Missing local proof-cache dependency: '+module)
                if dependency in active:
                    raise ValueError('Cyclic application proof-cache imports')
                if relative not in imports:
                    imports[relative] = sha(dependency)
                    visit(dependency)
            active.remove(path)
        visit(source)
        identity = {'schema': 'numerics-application-cache-v1',
                    'module': str(source.relative_to(self.source_root)), 'source': source.read_text(),
                    'imports': imports, 'dependencies': self.dependencies,
                    'profile': 'lean-checked-autoImplicit-false-warningAsError-extra-linters'}
        key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
        return key, self.root/key if self.root else None

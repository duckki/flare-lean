#!/usr/bin/env python3
"""Build the admitted PRECiSA/Kodiak source with a versioned, relocatable launcher.

Requires GHC 9.6.7, Cabal >=3.6.2.1 and ordinary C/C++ build tools on Linux.
All build/install writes stay inside the selected tool source and prefix.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'scripts'))
from numerics.workflow import Runner, save, sha
from numerics.installation import unpack
from numerics.integration import ToolError

REVISION = '2626ba151a2915d7b148ff90ccfff5e1f764d948'
KODIAK = 'c054c3d5b86452182ce0aaf07bdacc83a92f2d95'
FILIB_URL = ('https://raw.githubusercontent.com/ibex-team/ibex-lib/'
             '65ed5877c166d9f7e516904f4ae228f9206118ba/'
             'interval_lib_wrapper/filib/3rd/filibsrc-3.0.2.2.tar.gz')
FILIB_SHA = '799d89cd0166c61d46bdd4e11db28f5650b5302f1190479765f8bcf01eb3db41'


def launcher():
    return '''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
root = Path(__file__).resolve().parents[1]
record = json.loads((root/'precisa-build.json').read_text())
if sys.argv[1:] == ['--version']:
    print('PRECiSA package '+record['version']+' source '+record['source_revision'])
else:
    os.environ['LD_LIBRARY_PATH'] = str(root/'lib')+os.pathsep+os.environ.get('LD_LIBRARY_PATH','')
    os.execv(str(root/'libexec/precisa'), ['precisa', *sys.argv[1:]])
'''


def build(source, prefix):
    source, prefix = Path(source).resolve(), Path(prefix).resolve()
    if sys.platform != 'linux':
        raise ToolError('unsupported_setup_platform', 'This maintained PRECiSA setup recipe is tested on Linux; use a Linux environment')
    prefix.mkdir(parents=True, exist_ok=False)
    work = source/'.flare-build'
    work.mkdir()
    runner = Runner(work, 1800)
    for tool in ('ghc', 'cabal', 'git', 'cmake', 'make', 'g++', 'curl'):
        if shutil.which(tool) is None:
            raise ToolError('missing_tool', 'PRECiSA setup requires '+tool)
    if runner.run('ghc-version', ['ghc', '--numeric-version'], cwd=source).strip() != '9.6.7':
        raise ToolError('unsupported_tool_version', 'PRECiSA setup requires GHC 9.6.7')
    cabal = runner.run('cabal-version', ['cabal', '--numeric-version'], cwd=source).strip()
    if tuple(map(int, cabal.split('.'))) < (3,6,2,1):
        raise ToolError('unsupported_tool_version', 'PRECiSA setup requires Cabal >=3.6.2.1')
    revision = runner.run('source-pin', ['git','rev-parse','HEAD'], cwd=source).strip()
    if revision != REVISION:
        raise ValueError('PRECiSA source revision mismatch')
    runner.run('submodules', ['git','submodule','update','--init','--recursive'], cwd=source, phase='setup')
    if runner.run('kodiak-pin', ['git','rev-parse','HEAD'], cwd=source/'Kodiak').strip() != KODIAK:
        raise ValueError('PRECiSA Kodiak submodule differs from the admitted pin')
    archive = work/'filib.tar.gz'
    runner.run('filib-download', ['curl','--fail','--location','--silent','--show-error',
        '--connect-timeout','20','--max-time','120',FILIB_URL,'--output',archive], phase='setup')
    if sha(archive) != FILIB_SHA:
        raise ValueError('filib++ archive identity mismatch')
    unpack(archive, work)
    filib = work/'filibsrc-3.0.2.2'
    runner.run('filib-configure', ['./configure','--prefix='+str(prefix),
        'CFLAGS=-fPIC -frounding-math', 'CPPFLAGS=-fPIC',
        'CXXFLAGS=-fPIC -std=c++14 -frounding-math -ffp-contract=off'], cwd=filib, phase='setup')
    runner.run('filib-build', ['make','-j2'], cwd=filib, phase='setup')
    runner.run('filib-install', ['make','install'], cwd=filib, phase='setup')
    kodiak = work/'kodiak'
    runner.run('kodiak-configure', ['cmake','-S',source/'Kodiak','-B',kodiak,'-DCMAKE_CXX_STANDARD=14'],
        env={'FILIB_ROOT':str(filib)}, phase='setup')
    runner.run('kodiak-build', ['cmake','--build',kodiak,'--target','KodiakDynamic','-j2'], phase='setup')
    config = source/'cabal.project.local'
    if config.exists():
        raise ValueError('Refusing to overwrite an existing cabal.project.local')
    config.write_text('optimization: False\njobs: 2\npackage precisa\n'
        '  extra-lib-dirs: '+str(kodiak)+' '+str(prefix/'lib')+'\n'
        '  extra-include-dirs: '+str(source/'Kodiak/src/Adapters')+'\n'
        '  ghc-options: -O0 -optl=-Wl,-rpath,'+str(kodiak)+'\npackage vector\n  ghc-options: -O0\n')
    runner.run('cabal-update', ['cabal','update'], cwd=source, phase='setup')
    runner.run('precisa-build', ['cabal','v2-build','exe:precisa','--disable-optimization','--jobs=2'], cwd=source, phase='setup')
    binary = Path(runner.run('precisa-binary', ['cabal','list-bin','exe:precisa'], cwd=source).strip())
    (prefix/'libexec').mkdir()
    shutil.copy2(binary, prefix/'libexec/precisa')
    shutil.copy2(kodiak/'libkodiak.so', prefix/'lib/libkodiak.so')
    (prefix/'bin').mkdir()
    (prefix/'bin/precisa').write_text(launcher())
    (prefix/'bin/precisa').chmod(0o755)
    record = {'schema':'numerics-precisa-build-v1','version':'4.0.4','source_revision':REVISION,
        'kodiak_revision':KODIAK,'filib_source':FILIB_URL,'filib_sha256':FILIB_SHA,
        'binary_sha256':sha(prefix/'libexec/precisa'), 'ghc':'9.6.7','cabal':cabal,
        'library_sha256':{p.name:sha(p) for p in sorted((prefix/'lib').glob('*.so*')) if p.is_file()},
        'qualification':'Analyzer build provenance; numerical conclusions still require independent Lean validation.'}
    save(prefix/'precisa-build.json', record)
    runner.run('launcher-version', [prefix/'bin/precisa','--version'], cwd=prefix)
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--prefix', required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(build(args.source, args.prefix), indent=2))

"""Shared bounded source setup driven by provider-owned adapter recipes."""
from pathlib import Path
import math
import os
import sys
import tarfile

from .integration import ToolError, adapters


def unpack(archive, destination):
    with tarfile.open(archive) as stream:
        members = stream.getmembers()
        for member in members:
            target = (destination/member.name).resolve()
            if not target.is_relative_to(destination.resolve()) or not (member.isfile() or member.isdir()):
                raise ValueError('Unsupported archive member: '+member.name)
        options = {'filter': 'data'} if hasattr(tarfile, 'data_filter') else {}
        stream.extractall(destination, members=members, **options)


def setup(name, directory, timeout=600, make_args=()):
    from .workflow import ROOT, Runner, save, sha
    adapter = adapters().get(name)
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError('Setup timeout must be finite and positive')
    if adapter is None or adapter.setup is None:
        raise ValueError('No maintained setup recipe for '+name)
    directory = Path(directory).expanduser().resolve()
    directory.mkdir(parents=True, exist_ok=False)
    runner = Runner(directory, timeout)
    recipe = adapter.setup
    record = {'schema': 'numerics-installation-v1', 'adapter': name, 'recipe': recipe,
              'status': 'unresolved', 'make_args': list(make_args),
              'build_environment': {key: os.environ[key] for key in [
                  'PATH', 'CC', 'CXX', 'CPPFLAGS', 'CFLAGS', 'CXXFLAGS', 'LDFLAGS',
                  'PKG_CONFIG_PATH', 'OCAMLPATH', 'DEVELOPER_DIR'] if key in os.environ}}
    try:
        source = recipe['source']
        if 'repository' in source:
            runner.run('download', ['git', 'clone', '--no-checkout', source['repository'], directory/'source'], phase='setup')
            runner.run('revision', ['git', 'checkout', '--detach', source['revision']], cwd=directory/'source', phase='setup')
            revision = runner.run('source-identity', ['git', 'rev-parse', 'HEAD'], cwd=directory/'source', phase='setup').strip()
            if revision != source['revision']:
                raise ValueError('Downloaded tool revision differs from the setup recipe')
            root = directory/'source'
        else:
            archive = directory/'source.tar.gz'
            runner.run('download', ['curl', '--fail', '--location', '--silent', '--show-error',
                                   source['url'], '--output', archive], phase='setup')
            if sha(archive) != source['sha256']:
                raise ValueError('Downloaded tool archive differs from the pinned SHA-256')
            # Extraction is bounded and logged like other setup commands.
            runner.run('unpack', [sys.executable, '-m', 'numerics.installation', archive, directory],
                       env={'PYTHONPATH': str(ROOT/'scripts')}, phase='setup')
            root = directory/source['directory']
        values = {'source': str(root), 'install': str(directory/'install')}
        for i, command in enumerate(recipe['commands']):
            expanded = [word.format(**values) for word in command]
            if expanded[0] == 'make':
                expanded += list(make_args)
            runner.run('build-'+str(i), expanded, cwd=root, phase='setup')
        executable = directory/recipe['executable']
        if not executable.is_file() or not os.access(executable, os.X_OK):
            raise ToolError('setup_failure', 'Setup did not produce '+str(executable))
        record.update(status='installed', executable=str(executable), sha256=sha(executable))
    except (RuntimeError, ValueError, OSError) as error:
        record.update(error=str(error), failure_stage=runner.last_stage)
        raise
    finally:
        save(directory/'installation.json', record)
    return record


if __name__ == '__main__':
    unpack(Path(sys.argv[1]), Path(sys.argv[2]))

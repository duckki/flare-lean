#!/usr/bin/env python3
"""Link the authoritative repository skill into an agent's skill directory."""
import argparse
import os
from pathlib import Path


def install(destination):
    source=Path(__file__).resolve().parents[1]/'skills/verify-numerics'
    target=Path(destination).expanduser().absolute()/'verify-numerics'
    if target.is_symlink() and target.resolve()==source:
        return target
    if target.exists() or target.is_symlink():
        raise ValueError('Existing skill was preserved: '+str(target))
    target.parent.mkdir(parents=True,exist_ok=True)
    target.symlink_to(source,target_is_directory=True)
    return target


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    default=Path(os.environ.get('CODEX_HOME',str(Path.home()/'.codex')))/'skills'
    parser.add_argument('--dest',type=Path,default=default,help='Agent skill parent directory')
    args=parser.parse_args()
    try:
        print(install(args.dest))
    except (OSError,ValueError) as error:
        parser.exit(2,str(error)+'\n')


if __name__=='__main__': main()

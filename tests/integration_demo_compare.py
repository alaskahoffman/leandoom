"""Pinned E1M1 integrations: real reference determinism and mutation detection.

An engine divergence is a recorded finding, not an integration failure. A bad
oracle, inconsistent trace, or failure to detect a deliberate mutation is a failure.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import demo_compare as dc


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fetch',action='store_true')
    args=parser.parse_args()
    findings={}
    for scenario in ['movement','combat','moving-combat','enemy-encounter','shotgun-secret','e1m1-exit']:
        out=ROOT/'artifacts'/f'compare-{scenario}'
        report=dc.run(argparse.Namespace(out=str(out),demo=None,scenario=scenario,ticks=2500,fetch=args.fetch))
        original=dc.read_records(out/'reference.jsonl')
        # Re-run the same built reference in a fresh process: no residual globals,
        # startup randomness, output path, or wall-clock dependence may leak in.
        binary=ROOT/'artifacts/tick-reference/build/src/chocolate-doom'
        env={**os.environ,'SDL_VIDEODRIVER':'dummy','SDL_AUDIODRIVER':'dummy',
             'LEANDOOM_TRACE':str(out/'reference-repeat.jsonl'),
             'LEANDOOM_TRACE_TICS':str(len(original)-1)}
        with (out/'reference-repeat.log').open('w') as log:
            subprocess.run([str(binary),'-iwad',str(ROOT/'artifacts/doom-shareware-1.9/doom1.wad'),
                            '-timedemo',str(out/'input.lmp'),'-gameversion','1.9','-nodraw','-nosound','-nojoy','-nomouse',
                            '-config',str(out/'default.cfg'),'-extraconfig',str(out/'chocolate.cfg')],
                           cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=120)
        assert (out/'reference.jsonl').read_bytes()==(out/'reference-repeat.jsonl').read_bytes(),'reference trace is nondeterministic'
        repeat=subprocess.run([str(ROOT/'.lake/build/bin/trace-probe'),'E1M1',
                               str(ROOT/'artifacts/doom-shareware-1.9/doom1.wad'),str(out/'commands.txt')],
                              check=True,capture_output=True,timeout=120)
        assert repeat.stdout==(out/'lean.jsonl').read_bytes(),'Lean trace is nondeterministic'
        assert dc.compare(original,copy.deepcopy(original))['status']=='match'
        changed=copy.deepcopy(original)
        changed[42]['state']['player']['x']^=1
        diff=dc.compare(original,changed)['first_divergence']
        assert diff['tick']==42 and diff['differences'][0]['field']=='state.player.x'
        assert diff['difference_count']==1
        findings[scenario]={'ticks':len(original)-1,'reference_repeatable':True,'lean_repeatable':True,
                            'injected_one_bit_difference_detected_at':42,
                            'engine_status':report['status'],'first_by_subsystem':report['first_by_subsystem']}
    path=ROOT/'artifacts/demo-comparison-integration.json'
    path.write_text(json.dumps(findings,indent=2)+'\n')
    print(f'Comparison harness integration checks passed; findings: {path}')


if __name__=='__main__': main()

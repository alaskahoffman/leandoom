"""Opt-in persistent engine validation, using ordinary E1M1 demo commands."""
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import live_compare as live


def main():
    binary,key=live.build_reference()
    out=ROOT/'artifacts/live-compare-validation';out.mkdir(exist_ok=True)
    session=live.Session(ROOT/'artifacts/doom-shareware-1.9/doom1.wad',binary,key,out)
    report={};start=time.monotonic()
    try:
        checkpoints={1,777,950,1100,1242,1450,1881}
        for scenario in ['e1m1-exit','sky-window']:
            if report:session.reset()
            captures={}
            for i,cmd in enumerate(live.dc.scenario(scenario),1):
                meta,a,b=session.step(cmd)
                assert meta['firstStateDifference'] is None,meta
                if (scenario=='e1m1-exit' and i in checkpoints) or (scenario=='sky-window' and i==183):
                    captures[i]=live.rc.compare_pixels(a,b)
                    print(scenario,i,captures[i]['full'],flush=True)
                    assert a==b,(scenario,i,captures[i])
            report[scenario]={'tics':len(session.commands),'captures':captures,'save':session.save()}
        sky=(a,b);session.reset()
        for cmd in live.dc.scenario('sky-window'):meta,a,b=session.step(cmd)
        assert (a,b)==sky,'fresh processes must repeat identical frame pairs'
        assert meta['firstStateDifference'] is None
        report['repeat_sky']='byte-identical'
        # A fresh render matches here even without history. Only the full
        # presentation sequence catches clearing the original's unpainted gap.
        for name in ['slime-edge','fireball-barrels','pixel-edges','door-projectile-hud','player-death','player-death-inputs','stray-memory']:
            fixture=json.loads((ROOT/f'tests/reference/{name}-commands.json').read_text())
            commands=[row[1:] for row in fixture['runs'] for _ in range(row[0])]
            encoded=''.join(' '.join(map(str,c))+'\n' for c in commands).encode()
            assert len(commands)==fixture['tics'] and live.dc.sha(encoded)==fixture['commands_sha256']
            exact=set(fixture.get('exact_frames',[len(commands)]))
            capture=exact|set(fixture.get('capture_frames',[]))
            session.reset();captures={}
            for i,cmd in enumerate(commands,1):
                meta,a,b=session.step(cmd)
                assert meta['firstStateDifference'] is None,meta
                if fixture.get('exact_hud_all_frames',False):
                    assert a[168*320*3:]==b[168*320*3:],(name,i,'status bar differs')
                if i in capture:
                    captures[i]=live.rc.compare_pixels(a,b)
                    print(name,i,captures[i]['full'],flush=True)
                if i in exact or fixture.get('exact_all_frames',False):
                    assert a==b,(name,i,live.rc.compare_pixels(a,b))
            if fixture.get('no_bounds_panics',False):
                assert 'PANIC' not in (session.directory/'lean.log').read_text(),name
            report[name]={'tics':len(commands),'captures':captures,'save':session.save()}
        report['elapsed_seconds']=time.monotonic()-start
        (out/'report.json').write_text(json.dumps(report,indent=2))
        print('Live input/state synchronization, saved replay and fresh-process repeatability verified.',flush=True)
    finally:session.close()

if __name__=='__main__':main()

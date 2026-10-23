"""Real DOS rendering, live input/state alignment, fresh-process repeatability.

Pixel discrepancies remain findings; exact frame assertions are limited to
known exact cases. No pixel tolerances or state-field omissions are applied.
"""
import argparse
import copy
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import original_live_compare as dos


def fixture(name):
    data=json.loads((ROOT/f'tests/reference/{name}-commands.json').read_text())
    cmds=[row[1:] for row in data['runs'] for _ in range(row[0])]
    encoded=''.join(' '.join(map(str,c))+'\n' for c in cmds).encode()
    assert len(cmds)==data['tics'] and dos.oc.sha(encoded)==data['commands_sha256']
    return cmds


def main():
    p=argparse.ArgumentParser();p.add_argument('--fetch',action='store_true');args=p.parse_args()
    binary,key=dos.build_reference(args.fetch)
    out=ROOT/'artifacts/original-live-integration';out.mkdir(exist_ok=True)
    session=dos.Session(ROOT/'artifacts/doom-shareware-1.9/doom1.wad',binary,key,out)
    report={};start=time.monotonic()
    cases={name:dos.oc.dc.scenario(name) for name in ['movement','combat','moving-combat','enemy-encounter','e1m1-exit']}
    cases.update({name:fixture(name) for name in ['door-projectile-hud','player-death-inputs','stray-memory','dos-video']})
    try:
        for name,commands in cases.items():
            session.reset();frames=[];states=[];captures={};hud=0
            for tick,cmd in enumerate(commands,1):
                meta,a,b=session.step(cmd)
                assert meta['firstStateDifference'] is None,(name,tick,meta)
                difference=dos.live.rc.compare_pixels(a,b)
                if difference['full']['different_pixels']:frames.append({'tick':tick,**difference})
                if a[168*320*3:]!=b[168*320*3:]:hud+=1
                if name=='movement':
                    assert a==b,(name,tick,difference)
                    states.append(copy.deepcopy(session.last[1][0][0]))
                    captures[tick]=dos.oc.sha(a)
            assert hud==0,(name,'HUD differences',hud)
            assert 'PANIC' not in (session.directory/'lean.log').read_text(),name
            report[name]={'tics':len(commands),'different_frames':frames,'hud_different_frames':hud,'capture':session.save()}
            if name=='dos-video':assert not frames,(name,'unexpected pixel differences',frames[:3])
            if name=='movement':
                session.reset()
                for tick,cmd in enumerate(commands,1):
                    meta,a,b=session.step(cmd)
                    assert dos.oc.sha(a)==captures[tick] and session.last[1][0][0]==states[tick-1],('fresh process differs',tick)
                changed=copy.deepcopy(states[41]);changed['state']['player']['x']^=1
                diffs=list(dos.oc.dc.differences(states[41]['state'],changed['state']))
                assert len(diffs)==1 and diffs[0]['field']=='state.player.x'
                altered=bytearray(a);altered[0]^=1
                assert dos.live.rc.compare_pixels(a,bytes(altered))['full']['different_pixels']==1
                report['repeat_movement']='byte-identical state and frames; state/pixel mutations detected'
            print(name,len(commands),'tics; state/HUD match;',len(frames),'differing frames',flush=True)
        report['elapsed_seconds']=time.monotonic()-start
        print('Original DOS live comparison checks passed.',flush=True)
    finally:
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');session.close()

if __name__=='__main__':main()

"""Execute original DOS DOOM, compare both candidates, verify repeatability.

Engine divergence is recorded as a finding. Failure to capture consistent
evidence, match the diagnostic reference, or detect a mutation fails this test.
"""
import argparse
import copy
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import original_demo_compare as oc


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fetch',action='store_true')
    args=parser.parse_args()
    findings={}
    for scenario in ['movement','combat','moving-combat','enemy-encounter','shotgun-secret','e1m1-exit']:
        out=ROOT/'artifacts'/f'original-{scenario}'
        report=oc.run(argparse.Namespace(out=out,demo=None,scenario=scenario,ticks=2500,
                                         fetch=args.fetch,rebuild=False))
        binary,_=oc.build_emulator()
        data=(out/'diagnostic/input.lmp').read_bytes()
        commands=oc.dc.decode_demo(data)
        original=oc.read_records(out/'original.jsonl',commands)
        repeat,_=oc.capture(binary,out/'repeat',data)
        assert (out/'original.jsonl').read_bytes()==(out/'repeat/original.jsonl').read_bytes(), 'original trace not repeatable'
        assert oc.compare(original,repeat,commands,'repeat')['status']=='match'
        changed=copy.deepcopy(original); changed[42]['state']['player']['x']^=1
        difference=oc.compare(original,changed,commands,'mutated')['first_divergence']
        assert difference['tick']==42 and len(difference['differences'])==1
        assert difference['differences'][0]['field']=='state.player.x'
        # This is an integration expectation for these pinned cases, never a
        # reason to silently prefer Chocolate if future original runs disagree.
        assert report['comparisons']['chocolate']['status']=='match', 'Chocolate diverged from original; investigate oracle disagreement'
        diagnostic=json.loads((out/'diagnostic/report.json').read_text())
        assert diagnostic['status']=='match', f'{scenario} regression against broad reference trace'
        assert report['comparisons']['lean']['status']=='match', f'{scenario} regression against original DOS executable'
        if scenario=='enemy-encounter':
            # Complete encounter, now including enemy movement in DOS memory.
            assert len(commands)==521
            for field in ['tics','x','momx','momz','health']:
                changed=copy.deepcopy(original); changed[42]['state']['enemyBrains']['87'][field]^=1
                difference=oc.compare(original,changed,commands,'enemy-mutated')['first_divergence']
                assert difference['tick']==42 and len(difference['differences'])==1
                assert difference['differences'][0]['field']==f'state.enemyBrains.87.{field}'
        if scenario=='shotgun-secret':
            assert len(commands)==1961
            # Player health, inventory and weapon milestones are now observed
            # directly in DOS memory as well as both candidates' traces.
            assert original[1248]['state']['player']['health']==25
            assert original[1249]['state']['player']['health']==20
            assert original[1881]['state']['player']['readyWeapon']==2
            assert original[1881]['state']['player']['ammo'][1]==28
            assert original[1886]['state']['player']['ammo'][1]==27
            assert original[-1]['state']['player']['ammo'][1]==25
            assert original[-1]['state']['player']['secrets']==1
            # Flight, spawn-tick explosion, damage, and removal are now
            # directly visible in DOS. Lists preserve live thinker order.
            assert sum(len(r['state']['projectiles']) for r in original)==414
            assert {p['source'] for r in original for p in r['state']['projectiles']}=={9,17}
            assert original[776]['state']['projectiles']==[]
            assert original[777]['state']['projectiles'][0]['missile']==1
            assert original[857]['state']['projectiles'][0]['state']==99
            assert original[874]['state']['projectiles']==[]
            assert original[1241]['state']['projectiles']==[]
            assert original[1242]['state']['projectiles'][0]['missile']==0
            assert original[1256]['state']['projectiles']==[]
            assert original[1633]['state']['projectiles'][0]['source']==17
            assert original[1633]['state']['player']['health']==2
            # Object presence and sector heights still use the wider profile.
            rows=oc.dc.read_records(out/'diagnostic/reference.jsonl')
            assert rows[1248]['state']['player']['health']==25
            assert rows[1249]['state']['player']['health']==20
            assert rows[1438]['state']['enemyBrains']['8']['health']==-5
            assert '99' in rows[1827]['state']['actors'] and '99' not in rows[1828]['state']['actors']
            assert rows[1881]['state']['player']['readyWeapon']==2
            assert rows[1881]['state']['player']['ammo'][1]==28
            assert rows[-1]['state']['player']['ammo'][1]==25
            assert rows[-1]['state']['player']['secrets']==1
            assert rows[-1]['state']['lineSpecials'][308]==0
            assert rows[-1]['state']['sectors'][59]['floor']==-40*65536
            for tick,field in [(1249,'play'),(1886,'misc')]:
                changed=copy.deepcopy(original); changed[tick]['state']['rng'][field]^=1
                difference=oc.compare(original,changed,commands,'rng-mutated')['first_divergence']
                assert difference['tick']==tick and difference['differences'][0]['field']==f'state.rng.{field}'
            mutations=[(1249,'player','health'),(1249,'player','armor'),
                       (1853,'player','pendingWeapon'),(1886,'weapon','state'),
                       (1886,'weapon','tics'),(1886,'weapon','flashState'),
                       (1886,'weapon','flashTics'),(1886,'weapon','refire'),
                       (1886,'weapon','extraLight')]
            for tick,group,field in mutations:
                changed=copy.deepcopy(original)
                changed[tick]['state'][group][field]^=1
                difference=oc.compare(original,changed,commands,'player-weapon-mutated')['first_divergence']
                assert difference['tick']==tick and len(difference['differences'])==1
                assert difference['differences'][0]['field']==f'state.{group}.{field}'
            changed=copy.deepcopy(original);changed[1886]['state']['player']['ammo'][1]^=1
            difference=oc.compare(original,changed,commands,'shell-mutated')['first_divergence']
            assert difference['tick']==1886 and difference['differences'][0]['field']=='state.player.ammo[1]'
            for field in ['x','y','z','momx','momy','momz','angle','floor','ceiling','tics','lastlook','missile']:
                changed=copy.deepcopy(original);changed[777]['state']['projectiles'][0][field]^=1
                difference=oc.compare(original,changed,commands,'projectile-mutated')['first_divergence']
                assert difference['tick']==777 and len(difference['differences'])==1
                assert difference['differences'][0]['field']==f'state.projectiles[0].{field}'
            changed=copy.deepcopy(original);changed[857]['state']['projectiles'][0]['state']=100
            difference=oc.compare(original,changed,commands,'explosion-mutated')['first_divergence']
            assert difference['tick']==857 and difference['differences'][0]['field']=='state.projectiles[0].state'
            changed=copy.deepcopy(original);changed[777]['state']['projectiles']=[]
            difference=oc.compare(original,changed,commands,'projectile-removed')['first_divergence']
            assert difference['tick']==777 and difference['differences'][0]['field']=='state.projectiles.length'
        if scenario=='e1m1-exit':
            assert len(commands)==2445
            assert commands[:1961]==oc.dc.scenario('shotgun-secret')
            assert original[2164]['state']['enemyBrains']['16']['health']==10
            assert original[2165]['state']['enemyBrains']['16']['health']==-5
            assert original[2242]['state']['enemyBrains']['16']['state']==461
            assert original[2243]['state']['enemyBrains']['16']['state']==895
            assert original[2243]['state']['enemyBrains']['16']['tics']==-1
            assert all(b['health']<=0 for b in original[-1]['state']['enemyBrains'].values())
            assert original[-1]['state']['player']['health']==21
            assert not any(r['state']['exitRequested'] for r in original[:-1])
            assert original[-1]['state']['exitRequested'] is True
            rows=oc.dc.read_records(out/'diagnostic/reference.jsonl')
            assert rows[-2]['state']['lineSpecials'][330]==11
            assert rows[-1]['state']['lineSpecials'][330]==0
            # Reintroduce the real corpse-state bug and suppress the exit:
            # each must identify its exact original-executable boundary.
            changed=copy.deepcopy(original);changed[2243]['state']['enemyBrains']['16']['state']=461
            difference=oc.compare(original,changed,commands,'gibs-mutated')['first_divergence']
            assert difference['tick']==2243 and difference['differences'][0]['field']=='state.enemyBrains.16.state'
            changed=copy.deepcopy(original);changed[-1]['state']['exitRequested']=False
            difference=oc.compare(original,changed,commands,'exit-mutated')['first_divergence']
            assert difference['tick']==2445 and difference['differences'][0]['field']=='state.exitRequested'
        findings[scenario]={'ticks':len(commands),'original_repeatable':True,
                            'single_bit_mutation_detected_at':42,'comparisons':report['comparisons'],
                            'diagnostic_status':diagnostic['status'],'diagnostic_first_divergence':diagnostic['first_divergence']}
        print(f"{scenario}: original repeatable; Chocolate matches selected fields; Lean {report['comparisons']['lean']['status']}",flush=True)
    path=ROOT/'artifacts/original-comparison-integration.json'
    path.write_text(json.dumps(findings,indent=2)+'\n')
    print(f'Original executable integration checks passed: {path}')


if __name__=='__main__': main()

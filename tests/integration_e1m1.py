"""Pinned E1M1 inventory, scrolling, and relocated-start mover/secret/exit checks."""
import collections
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import tempfile
from test_wad import wad

ROOT=Path(__file__).resolve().parents[1]

def main():
    spec=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    path=ROOT/spec['local_directory']/'doom1.wad'
    data=path.read_bytes()
    assert hashlib.sha256(data).hexdigest()==spec['wad_sha256'],'unexpected shareware WAD'
    count,offset=struct.unpack_from('<ii',data,4)
    lumps=[]
    for i in range(count):
        start,size,name=struct.unpack_from('<ii8s',data,offset+i*16)
        lumps.append((name.rstrip(b'\0').decode('ascii'),data[start:start+size]))
    start_index=next(i for i,(name,_) in enumerate(lumps) if name=='E1M1')
    level=dict(lumps[start_index+1:start_index+11])
    lines=list(struct.iter_unpack('<7H',level['LINEDEFS']))
    sides=list(struct.iter_unpack('<hh8s8s8sH',level['SIDEDEFS']))
    sectors=list(struct.iter_unpack('<hh8s8shhh',level['SECTORS']))
    things=list(struct.iter_unpack('<5h',level['THINGS']))
    line_counts=collections.Counter(line[3] for line in lines if line[3])
    sector_counts=collections.Counter(sector[5] for sector in sectors if sector[5])
    assert dict(line_counts)=={1:8,11:1,36:1,48:8,88:1}
    assert dict(sector_counts)=={1:1,7:4,8:2,9:3,12:1}
    expected_scrollers=[i for i,line in enumerate(lines) if line[3]==48]
    increments=collections.Counter(lines[i][5] for i in expected_scrollers)
    with tempfile.TemporaryDirectory(prefix='lean-doom-e1m1-') as temporary:
        output=Path(temporary)/'state.json'
        for script,ticks in [('0:0',0),('1:0',1),('35:0',35),('10:0,25:0',35),('35:0,1:1024',0)]:
            subprocess.run([str(ROOT/'.lake/build/bin/lean-doom'),'simulate','E1M1',script,str(output),str(path)],check=True,capture_output=True,timeout=30)
            state=json.loads(output.read_text())
            assert state['scrollers']==expected_scrollers
            expected=[(side[0]+ticks*increments[i]+32768)%65536-32768 for i,side in enumerate(sides)]
            assert state['sideOffsets']==expected,(script,'scroll offsets differ')
        # Keep the original geometry, BLOCKMAP and things, relocating only the
        # player-1 start near each trigger. These are focused map integrations,
        # not an end-to-end run from the normal spawn or a demo comparison.
        mover_checks=[]
        for trigger,start,target,low,finish in [(308,(3008,-4184,90),59,-40,-40),(195,(2908,-2978,135),70,-48,104)]:
            moved=bytearray(level['THINGS'])
            player=next(i for i,t in enumerate(things) if t[3]==1)
            struct.pack_into('<hhH',moved,player*10,*start)
            patch=Path(temporary)/'relocated-start.wad'
            patch.write_bytes(wad([('E1M1',b'')]+[(name,bytes(moved) if name=='THINGS' else payload) for name,payload in lumps[start_index+1:start_index+11]]))
            for script,complete in [('10:2',False),('10:2,200:0',True)]:
                subprocess.run([str(ROOT/'.lake/build/bin/lean-doom'),'simulate','E1M1',script,str(output),str(path),str(patch)],check=True,capture_output=True,timeout=30)
                state=json.loads(output.read_text())
                assert state['specials'][trigger]==(0 if trigger==308 else 88)
                if complete:
                    assert state['floors'][target]==finish
                    assert not any(m['sector']==target for m in state['floorMovers'])
                else:
                    mover=next(m for m in state['floorMovers'] if m['sector']==target)
                    assert mover['low']==low
                    assert state['floors'][target]==88
            mover_checks.append({'trigger':trigger,'target':target,'low':low,'finished_floor':finish,'relocated_start':start})
        def relocated_state(start,script,combat=False):
            moved=bytearray(level['THINGS'])
            player=next(i for i,t in enumerate(things) if t[3]==1)
            struct.pack_into('<hhH',moved,player*10,*start)
            patch=Path(temporary)/'relocated-special.wad'
            patch.write_bytes(wad([('E1M1',b'')]+[(name,bytes(moved) if name=='THINGS' else payload) for name,payload in lumps[start_index+1:start_index+11]]))
            subprocess.run([str(ROOT/'.lake/build/bin/lean-doom'),'combat' if combat else 'simulate','E1M1',script,str(output),str(path),str(patch)],check=True,capture_output=True,timeout=30)
            return json.loads(output.read_text())
        secret_checks=[]
        for sector,start in [(68,(2928,-3840,0)),(69,(3264,-3856,0)),(70,(3552,-3872,0))]:
            before=relocated_state(start,'0:0')
            assert (before['secrets'],before['totalSecrets'])==(0,3)
            for script in ['1:0','70:0']:
                state=relocated_state(start,script)
                assert (state['secrets'],state['totalSecrets'])==(1,3),(sector,script,state['secrets'])
                assert state['sectorSpecials'][sector]==0
            assert relocated_state(start,'1:0,1:1024')==before
            secret_checks.append({'sector':sector,'relocated_start':start})
        exit_start=(2944,-4768,180)
        assert lines[330][3]==11
        initial=relocated_state(exit_start,'0:0')
        exited=relocated_state(exit_start,'1:4096')
        assert exited['exitRequested'] and not exited['secretExit']
        assert exited['specials'][330]==0
        assert exited['textures'][lines[330][5]][1]=='SW2STRTN'
        assert exited['exitSwitchSound']=='swtchn'
        assert exited['ticks']==1
        assert relocated_state(exit_start,'1:4096,70:0')==exited
        assert relocated_state(exit_start,'1:4096,1:1024')==initial
        exit_check={'trigger':330,'relocated_start':exit_start,'completion_requested':True,'intermission_implemented':False}
        shotgun_start=(3264,-3936,270)
        equipped=relocated_state(shotgun_start,'1:2,31:0',combat=True)
        assert equipped['readyWeapon']==2 and equipped['ammo'][1]==8,equipped
        fired=relocated_state(shotgun_start,'1:2,31:0,4:8192',combat=True)
        assert fired['shots']==1 and fired['ammo'][1]==7,fired
        assert len([e for e in fired['shotEvents'] if e['source']==-1 and e['kind'] in ('puff','blood')])==7
        pistol=relocated_state(shotgun_start,'1:2,31:0,31:32768',combat=True)
        assert pistol['readyWeapon']==1 and pistol['pendingWeapon']==9,pistol
        shotgun_check={'relocated_start':shotgun_start,'pickup_equips_shotgun':True,'seven_pellets_one_shell':True,'pistol_selection':True}
        combat_checks=[]
        for target,start,effect in [(87,(2192,-2432,0),'blood'),(35,(1232,-3264,0),'puff')]:
            state=relocated_state(start,'5:8192',combat=True)
            hits=[e for e in state['shotEvents'] if e['source']==-1]
            assert any(e['kind']=='damage' and e['target']==target for e in hits),(target,hits)
            assert any(e['kind']==effect for e in hits),(target,hits)
            assert next(a['health'] for a in state['actors'] if a['thing']==target)<20
            combat_checks.append({'target':target,'relocated_start':start,'impact_request':effect,
                                  'damage_bridge':'prototype with original death/blast actions'})
        killed=relocated_state((2192,-2432,0),'60:8192',combat=True)
        corpse=next(a for a in killed['actors'] if a['thing']==87)
        assert corpse['death'] is not None and corpse['health']==0,corpse
        assert not corpse['death']['solid'] and corpse['death']['height']==14,corpse
        assert corpse['pose']=='POSSL' and corpse['death']['tics']==-1,corpse
        assert killed['kills']>=1 and killed['dropped']
        combat_checks.append({'target':87,'death_state':corpse['death']['state'],
                              'corpse_height':14,'solid':False,'drop_created':True})

        barrel=relocated_state((1232,-3264,0),'80:8192',combat=True)
        exploded=next(a for a in barrel['actors'] if a['thing']==35)
        assert exploded['health']==0 and exploded['removed'],exploded
        combat_checks.append({'target':35,'barrel_exploded_and_removed':True})
        # Melee distance keeps the now-active imp in this fixed pistol sightline.
        imp_start=(3392,-3472,0)
        wounded=relocated_state(imp_start,'5:8192',combat=True)
        imp=next(a for a in wounded['actors'] if a['thing']==8)
        assert 0<imp['health']<60,imp
        attacked=relocated_state((3440,-3344,0),'220:0',combat=True)
        assert any(p['source']==8 for p in attacked['projectiles']),attacked['projectiles']
        assert any(p['source']==8 and p['exploding'] for p in attacked['projectiles'])
        combat_checks.append({'target':8,'imp_fireball_spawned':True,'fireball_geometry_impact':True})
        defeated=relocated_state(imp_start,'140:8192',combat=True)
        imp=next(a for a in defeated['actors'] if a['thing']==8)
        assert imp['health']==0 and imp['death'] is not None,imp
        combat_checks.append({'target':8,'relocated_start':imp_start,'imp_damaged_and_killed':True})

    print(json.dumps({'map':'E1M1','wad_sha256':spec['wad_sha256'],
        'linedef_specials':dict(sorted(line_counts.items())),
        'sector_specials':dict(sorted(sector_counts.items())),
        'medium_single_player_types':dict(sorted(collections.Counter(t[3] for t in things if t[4]&2 and not t[4]&16).items())),
        'scrollers':expected_scrollers,'scrolling_checks':5,'mover_checks':mover_checks,'secret_checks':secret_checks,'exit_check':exit_check,'combat_checks':combat_checks,'shotgun_check':shotgun_check},indent=2))

if __name__=='__main__':main()

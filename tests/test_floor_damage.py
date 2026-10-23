"""Damaging-sector requests against original C, plus runtime phase boundaries."""
import json
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest
import fidelity_reference
import level_reference
from motion_reference import function
import test_assets
from test_assets import replace
from test_combat import arena
from test_render import two_rooms
from test_things import things, sectors

ROOT=Path(__file__).resolve().parents[1]


def oracle_source():
    upstream=fidelity_reference.sources()
    source=level_reference.oracle_source(upstream)
    random=upstream['src/doom/m_random.c'];start=random.index('const unsigned char rndtable')
    random=random[start:random.index('};',start)+2]+'\nstatic int prndindex;\n'+function(random,'int P_Random')
    source=source.replace('static int P_Random(void) { abort(); }',random)
    source=source.replace('static void P_DamageMobj(mobj_t *m,void *a,void *b,int damage) { (void)m;(void)a;(void)b;(void)damage;abort(); }',
        'static int requested;\nstatic void P_DamageMobj(mobj_t *m,void *a,void *b,int damage) { assert(m && !a && !b); requested=damage; }')
    anchor='if(!strcmp(op,"secret")||!strcmp(op,"visit")) {'
    replacement='''if(!strcmp(op,"damage")) {
            mo.z=next();sector.floorheight=next();sector.special=next();
            player.powers[pw_ironfeet]=next();leveltime=next();prndindex=next();requested=0;
            P_PlayerInSpecialSector(&player);
            printf("%d %d\\n",requested,prndindex);
        } else '''+anchor
    assert source.count(anchor)==1
    return source.replace(anchor,replacement)


class FloorDamageOracleTests(unittest.TestCase):
    def test_original_floor_damage_and_short_circuit_rng(self):
        commands=[f'damage {z} -65536 {special} {suit} {time} {seed}'
                  for seed in range(256) for special in [5,7,4,16] for suit in [0,1]
                  for z in [-65537,-65536,-65535]
                  for time in [0,1,31,32,33,2147483616,2147483647]]
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory);(p/'commands').write_text('\n'.join(commands)+'\n')
            (p/'oracle.c').write_text(oracle_source())
            lean=subprocess.check_output([str(ROOT/'.lake/build/bin/level-probe'),str(p/'commands')])
            self.assertEqual(len(lean.splitlines()),len(commands))
            for opt in ['-O0','-O2']:
                subprocess.run(['cc','-std=c11','-fwrapv',opt,str(p/'oracle.c'),'-o',str(p/'oracle')],check=True,capture_output=True)
                original=subprocess.check_output([str(p/'oracle'),str(p/'commands')])
                if original!=lean:
                    for command,a,b in zip(commands,original.splitlines(),lean.splitlines()):
                        if a!=b:self.fail(f'{opt} {command}: original {a!r}; Lean {b!r}')
                    self.fail('trace lengths differ')


def damaging(geometry,special=7,index=0):
    data=bytearray(dict(geometry)['SECTORS']);struct.pack_into('<H',data,index*26+22,special)
    return replace(geometry,'SECTORS',data)


class FloorDamageRuntimeTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geometry,script):
        output=self.directory/'damage.json'
        self.run_cli(['combat','E1M1',script,output],geometry)
        return json.loads(output.read_text())

    def test_global_clock_first_tick_and_armor(self):
        for tick,health in [(1,95),(32,95),(33,90),(65,85)]:
            self.assertEqual(self.state(damaging(arena()),f'{tick}:0')['health'],health)
        # The pickup follows the initial damage; green armor then saves 5/3.
        result=self.state(damaging(arena(extras=[(0,0,0,2018,7)])),'1:2,32:0')
        self.assertEqual((result['health'],result['armor']),(91,99))

    def test_suit_pickup_and_expiration(self):
        geometry=damaging(arena(extras=[(0,0,0,2025,7)]))
        for tick,health in [(1,95),(33,95),(2101,95),(2113,90)]:
            self.assertEqual(self.state(geometry,f'1:2,{tick-1}:0')['health'],health)
        # Pick up twelve ticks later: the last protected tick is itself a
        # damage tick. Special-sector effects precede the suit decrement.
        self.assertEqual(self.state(geometry,'12:0,1:2,2100:0')['health'],95)
        self.assertEqual(self.state(geometry,'12:0,1:2,2132:0')['health'],90)

    def test_invulnerability_blocks_damage(self):
        geometry=damaging(arena(extras=[(0,0,0,2022,7)]))
        self.assertEqual(self.state(geometry,'1:2,32:0')['health'],95)

    def test_entering_sector_on_damage_tick_waits_until_next_period(self):
        # The eighth moving tick crosses x=64; arrange it at leveltime 32.
        geometry=damaging(things(sectors(two_rooms(),first=(0,128),second=(0,128)),[(48,0,0,1,7)]),index=1)
        # Seven movement ticks cross in this fixture (see secret-sector tests).
        self.assertGreater(self.state(geometry,'26:0,7:2')['x'],64)
        self.assertEqual(self.state(geometry,'26:0,7:2')['health'],100)
        self.assertEqual(self.state(geometry,'26:0,7:2,31:0')['health'],100)
        self.assertEqual(self.state(geometry,'26:0,7:2,32:0')['health'],95)

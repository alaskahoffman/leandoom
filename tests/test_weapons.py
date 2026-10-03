"""Weapon switching, original shotgun cadence and live pellet integration."""
import hashlib,json,subprocess,unittest
import test_assets
import test_combat
from test_combat import arena,combat_art
from test_assets import rgb
import test_audio
import weapon_reference

class WeaponTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli
    sim=test_combat.CombatTests.sim
    frame=test_combat.CombatTests.frame
    pixel=staticmethod(test_assets.AssetTests.pixel)
    render=test_audio.AudioTests.render

    def shotgun(self,enemies=()):return arena(enemies,extras=[(0,0,0,2001,7)])

    def test_generated_states_and_original_c_sequences(self):
        subprocess.run(['python3',str(weapon_reference.ROOT/'scripts/generate-weapons.py')],check=True,capture_output=True)
        commands=weapon_reference.corpus();inp=self.directory/'commands';out=self.directory/'output'
        inp.write_text('\n'.join(commands)+'\n')
        subprocess.run([str(weapon_reference.PROBE),str(inp),str(out)],check=True,capture_output=True)
        spec=json.loads(weapon_reference.SPEC.read_text())
        self.assertEqual(hashlib.sha256(weapon_reference.source().encode()).hexdigest(),spec['harness_sha256'])
        self.assertEqual(len(commands),spec['commands'])
        self.assertEqual(hashlib.sha256(out.read_bytes()).hexdigest(),spec['sha256'])

    def test_unowned_selection_is_ignored(self):
        self.assertEqual(self.sim(arena(),'40:65536'),self.sim(arena(),'40:0'))

    def test_pickup_lowers_then_switches_then_raises(self):
        for tic,w,state,y,pending in [(1,1,11,38,2),(15,1,11,122,2),(16,2,20,122,9),(30,2,20,38,9),(31,2,18,32,9)]:
            with self.subTest(tic=tic):
                s=self.sim(self.shotgun(),f'1:2,{tic-1}:0')
                self.assertEqual((s['readyWeapon'],s['weaponState'],s['pendingWeapon']),(w,state,pending))
                self.assertAlmostEqual(s['weaponY'],y,delta=0.1)
                self.assertEqual(s['ammo'][:2],[50,8])

    def test_shotgun_windup_pellets_ammo_and_held_cadence(self):
        for ticks,shots in [(1,0),(3,0),(4,1),(40,1),(41,2),(78,3)]:
            s=self.sim(self.shotgun(),f'1:2,31:0,{ticks}:8192')
            self.assertEqual(s['shots'],shots)
            self.assertEqual(s['ammo'][:2],[50,8-shots])
        s=self.sim(self.shotgun(),'1:2,31:0,4:8192')
        self.assertEqual(len([e for e in s['shotEvents'] if e['source']==-1]),7)
        self.assertEqual(s['rng'],21)
        self.assertEqual(self.sim(self.shotgun(),'1:2,31:0,1:8192,60:0')['shots'],1)

    def test_switch_during_pump_finishes_attack_and_cancels_refire(self):
        geom=self.shotgun()
        s=self.sim(geom,'1:2,31:0,4:8192,1:40960,39:8192')
        self.assertEqual((s['readyWeapon'],s['pendingWeapon'],s['shots']),(2,1,1))
        s=self.sim(geom,'1:2,31:0,4:8192,1:40960,70:0')
        self.assertEqual((s['readyWeapon'],s['pendingWeapon'],s['weaponState']),(1,9,10))
        # Holding selection for the already readied weapon does not re-lower it.
        s=self.sim(geom,'1:2,31:0,100:65536')
        self.assertEqual((s['readyWeapon'],s['weaponState']),(2,18))

    def test_empty_shotgun_falls_back_to_pistol(self):
        s=self.sim(self.shotgun(),'1:2,31:0,263:8192,100:0')
        self.assertEqual((s['shots'],s['ammo'][1],s['readyWeapon']),(8,0,1))
        self.assertEqual(s['ammo'][0],50)

    def test_fist_selection_range_and_ammo_fallback(self):
        s=self.sim(arena(),'31:16384')
        self.assertEqual((s['readyWeapon'],s['weaponState']),(0,2))
        s=self.sim(arena(extras=[(48,0,0,2035,7)]),'31:16384,5:8192')
        self.assertEqual(s['ammo'][0],50)
        self.assertLess(s['actors'][0]['health'],20)
        far=self.sim(arena(extras=[(160,0,0,2035,7)]),'31:16384,5:8192')
        self.assertEqual(far['actors'][0]['health'],20)
        s=self.sim(arena(),'900:8192,50:0')
        self.assertEqual((s['readyWeapon'],s['ammo'][0],s['weaponState']),(0,0,2))

    def test_pellets_apply_damage_before_later_pellets(self):
        geom=self.shotgun([(96,0,180,3004,7),(160,0,180,3004,7)])
        s=self.sim(geom,'1:2,31:0,4:8192')
        damage=[e for e in s['shotEvents'] if e['source']==-1 and e['kind']=='damage']
        self.assertGreater(len({e['target'] for e in damage}),1)
        self.assertGreater(s['kills'],0)
        self.assertGreater(s['rng'],21) # Pain/death actions consumed draws between pellets.

    def test_shotgun_sprite_flash_and_sound_follow_state(self):
        geom=self.shotgun()+combat_art()
        for ticks,color in [(0,234),(3,234),(4,238),(7,239),(10,234),(11,235),(16,236),(21,237)]:
            with self.subTest(ticks=ticks):
                pixels=self.frame(geom,f'1:2,31:0,{ticks}:8192')
                self.assertEqual(self.pixel(pixels,156,164),rgb(color))
        _,trace=self.render(self.shotgun(),'1:2,31:0,4:8192')
        self.assertEqual(trace['trace'][-1]['sounds'],['shotgn'])

    def test_restart_and_partition_restore_weapon_state(self):
        geom=self.shotgun()
        self.assertEqual(self.sim(geom,'1:2,31:0,50:8192'),self.sim(geom,'1:2,31:0,20:8192,30:8192'))
        self.assertEqual(self.sim(geom,'1:2,31:0,50:8192,1:1024'),self.sim(geom,'0:0'))

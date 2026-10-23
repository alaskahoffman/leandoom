"""WAD-driven status pixels through the same combat renderer as SDL."""
import unittest
import json
import test_assets
from test_assets import patch, replace
from test_combat import arena, combat_art
from test_power_render import scene


def color(index,palette=0):
    return bytes(((index+palette)%256,255-index,index*3%256))


def face_names():
    names=[]
    for pain in range(5):
        names += [f'STFST{pain}{i}' for i in range(3)]
        names += [f'STFTR{pain}0',f'STFTL{pain}0',f'STFOUCH{pain}',f'STFEVL{pain}',f'STFKILL{pain}']
    return names+['STFGOD0','STFDEAD0']


def status_art():
    result=[('STBAR',patch([[10]*320 for _ in range(32)])),
            ('STARMS',patch([[11]*39 for _ in range(32)])),
            ('STTPRCNT',patch([[12]*2 for _ in range(5)])),
            ('STTMINUS',patch([[13]*2 for _ in range(5)])),
            ('PLAYPAL',b''.join(color(i,p) for p in range(14) for i in range(256)))]
    result += [(f'STTNUM{i}',patch([[20+i]*3 for _ in range(5)])) for i in range(10)]
    result += [(f'STYSNUM{i}',patch([[40+i]*2 for _ in range(3)])) for i in range(10)]
    result += [(f'STGNUM{i}',patch([[60+i]*2 for _ in range(3)])) for i in range(2,8)]
    result += [(f'STKEYS{i}',patch([[80+i]*3 for _ in range(3)])) for i in range(6)]
    # Offsets plus a transparent hole verify V_DrawPatch semantics, no lighting.
    result += [(name,patch([[100+i,None],[100+i,100+i]],-1,-1)) for i,name in enumerate(face_names())]
    return result


class StatusRenderTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli
    pixel=staticmethod(test_assets.AssetTests.pixel)

    def frame(self, geom=None, script='0:0', patches=()):
        if geom is None: geom=arena()+combat_art()+status_art()
        output=self.directory/'status.ppm'
        self.run_cli(['render-combat','E1M1',script,output],geom,patches)
        return output.read_bytes().split(b'\n',3)[3]

    def test_initial_bar_digits_percent_ammo_order_and_face_offsets(self):
        pixels=self.frame()
        for x,y,index in [(0,168,10),(319,199,10),(38,171,25),(41,171,20),
                          (81,171,21),(84,171,20),(87,171,20),(90,171,12),
                          (218,171,20),(221,171,12),(111,172,42),(123,172,63),
                          (104,199,11),(284,173,45),(286,173,40),(308,173,42),
                          (310,173,40),(312,173,40),(310,179,45),(312,179,40),
                          (308,191,43),(310,185,45),(144,169,100),(145,169,10)]:
            with self.subTest(x=x,y=y): self.assertEqual(self.pixel(pixels,x,y),color(index))
        # No card: backing is visible in each slot.
        for y in (171,181,191): self.assertEqual(self.pixel(pixels,239,y),color(10))

    def test_view_center_and_weapon_shift_up_sixteen_pixels(self):
        geom=arena()+combat_art()
        full=self.frame(geom,'15:0')
        bar=self.frame(geom+status_art(),'15:0')
        for x,y in [(0,0),(50,84),(200,100),(300,167)]:
            self.assertEqual(self.pixel(bar,x,y),self.pixel(full,x,y+16))
        self.assertEqual(self.pixel(bar,156,148),color(230))
        self.assertEqual(self.pixel(bar,156,168),color(10))

    def test_skull_overrides_card_for_all_three_slots(self):
        kinds=(5,6,13,40,39,38)
        prefixes=('BKEY','YKEY','RKEY','BSKU','YSKU','RSKU')
        sprites=[(prefix+f+'0',patch([[150]*4 for _ in range(8)],2,8)) for prefix in prefixes for f in 'AB']
        for mask in range(64):
            geom=arena(extras=[(0,0,0,k,7) for i,k in enumerate(kinds) if mask&(1<<i)])+combat_art()+status_art()+sprites
            pixels=self.frame(geom,'1:2,100:0')
            for i in range(3):
                key=i+3 if mask&(1<<(i+3)) else i if mask&(1<<i) else None
                self.assertEqual(self.pixel(pixels,239,171+i*10),color(10 if key is None else 80+key))

    def test_weapon_pickup_switches_ready_ammo_to_shells(self):
        geom=arena(extras=[(0,0,0,2001,7)])+combat_art()+status_art()
        pixels=self.frame(geom,'1:2,30:0')
        self.assertEqual(self.pixel(pixels,123,172),color(43))
        self.assertEqual(self.pixel(pixels,38,171),color(10))
        self.assertEqual(self.pixel(pixels,41,171),color(28))
        self.assertEqual(self.pixel(pixels,286,179),color(48))
        self.assertEqual(self.pixel(pixels,144,169),color(106)) # Grin persists 70 tics.

    def test_armor_pickup_and_wad_palette_apply_to_bar_and_world(self):
        geom=arena(extras=[(0,0,0,2019,7)])+combat_art()+status_art()
        geom += [(f'ARM2{f}0',patch([[150]*4 for _ in range(8)],2,8)) for f in 'AB']
        flash=self.frame(geom,'1:2')
        base=b''.join(color(i) for i in range(256))*14
        calm=self.frame(geom,'1:2',patches=[[('PLAYPAL',base)]])
        for x,y in [(0,0),(300,80),(0,168),(212,171)]:
            a=self.pixel(flash,x,y);b=self.pixel(calm,x,y)
            self.assertEqual(a,bytes(((b[0]+10)%256,b[1],b[2])))
        self.assertEqual(self.pixel(calm,212,171),color(22))
        self.assertEqual(self.pixel(calm,215,171),color(20))
        self.assertEqual(self.pixel(calm,218,171),color(20))

    def test_status_ignores_inverse_colormap_and_shows_invulnerable_face(self):
        geom=scene()+[(n,b) for n,b in combat_art() if n.startswith('PIS')]+status_art()
        pixels=self.frame(geom,'1:2,30:0')
        self.assertEqual(self.pixel(pixels,144,169),color(140))
        self.assertEqual(self.pixel(pixels,38,171),color(25))
        self.assertEqual(self.pixel(pixels,90,171),color(12))

    def test_fuzz_cannot_sample_status_bar_or_draw_bottom_view_row(self):
        geom=scene(2024)+[(n,b) for n,b in combat_art() if n.startswith('PIS')]+status_art()
        # After viewport shift this post extends from row 156 through the bar.
        weapons=[(n,patch([[231]*8 for _ in range(40)],-154,-140)) for n in ('PISGA0','PISGB0','PISGC0')]
        cols=bytes(range(256))*6+bytes([219])*256+bytes(range(256))*27
        pixels=self.frame(replace(geom,'COLORMAP',cols),'1:2,30:0',patches=[weapons])
        self.assertEqual(self.pixel(pixels,156,166),color(219))
        self.assertNotEqual(self.pixel(pixels,156,167),color(219))
        self.assertEqual(self.pixel(pixels,156,168),color(10))

    def test_dead_face_replaces_development_death_text(self):
        geom=arena([(160,0,180,3004,7)])+combat_art()+status_art()
        pixels=self.frame(geom,'2000:0')
        self.assertEqual(self.pixel(pixels,144,169),color(141))
        self.assertEqual(self.pixel(pixels,87,171),color(20))
        self.assertNotEqual(self.pixel(pixels,156,148),color(230))

    def test_patch_override_and_missing_resources_are_explicit(self):
        geom=arena()+combat_art()+status_art()
        pixels=self.frame(geom,patches=[[('STTNUM5',patch([[219]*3 for _ in range(5)]))]])
        self.assertEqual(self.pixel(pixels,38,171),color(219))
        output=self.directory/'missing.ppm'
        result=self.run_cli(['render-combat','E1M1','0:0',output],[(n,b) for n,b in geom if n!='STFDEAD0'],ok=False)
        self.assertIn('STFDEAD0',result.stderr)
        result=self.run_cli(['render-combat','E1M1','0:0',output],replace(geom,'PLAYPAL',b''.join(color(i) for i in range(256))),ok=False)
        self.assertIn('14 palettes',result.stderr)

    def test_face_tics_use_misc_rng_without_changing_pistol_rng(self):
        geom=arena()+combat_art()+status_art()
        for ticks,face in [(0,100),(1,102),(17,102),(18,102),(35,100),(52,101)]:
            pixels=self.frame(geom,f'{ticks}:0')
            self.assertEqual(self.pixel(pixels,144,169),color(face))
        output=self.directory/'state.json'
        self.run_cli(['combat','E1M1','19:8192',output],arena())
        state=json.loads(output.read_text())
        self.assertEqual(state['miscRng'],20)
        self.assertEqual(state['rng'],6) # Player spawn, damage, four puff draws.
        self.assertEqual(state['shots'],1)

    def test_first_enemy_damage_drives_actual_playpal_red_and_face(self):
        geom=arena([(160,0,180,3004,7)])+combat_art()+status_art()
        output=self.directory/'damage.json'
        for tic in range(1,251):
            self.run_cli(['combat','E1M1',f'{tic}:0',output],geom)
            state=json.loads(output.read_text())
            if state['health']<100: break
        else: self.fail('fixture enemy never attacks')
        pixels=self.frame(geom,f'{tic}:0')
        palette=1+min(7,(100-state['health']+7)//8)
        self.assertEqual(self.pixel(pixels,0,168),color(10,palette))
        pain=8*((100-state['health'])*5//101)
        self.assertEqual(self.pixel(pixels,144,169),color(100+pain+3,palette)) # Zombieman has circled to the right.

    def test_firing_face_uses_weapon_latch_until_ready_after_release(self):
        geom=arena()+combat_art()+status_art()
        held=self.frame(geom,'71:8192')
        released_during_animation=self.frame(geom,'71:8192,18:0')
        ready=self.frame(geom,'71:8192,19:0')
        self.assertEqual(self.pixel(held,144,169),color(107))
        self.assertEqual(self.pixel(released_during_animation,144,169),color(107))
        self.assertNotEqual(self.pixel(ready,144,169),color(107))

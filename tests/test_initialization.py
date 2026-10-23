"""Spawn order, psprite setup and silent sound calls are gameplay semantics."""
import subprocess
import unittest
from test_combat import arena
import test_demo_compare as trace_tests


class InitializationTests(unittest.TestCase):
    trace=trace_tests.LeanTraceTests.trace

    def test_generated_spawn_states_match_pinned_original_metadata(self):
        subprocess.run(['python3',str(trace_tests.ROOT/'scripts/generate-spawn.py')],check=True,capture_output=True)

    def test_every_spawn_draws_lastlook_and_only_timed_states_draw_duration(self):
        # Player 1; static stimpack 1; animated armor bonus 2; monster 2.
        for extra,expected in [([],1),([(96,0,0,2011,7)],2),
                               ([(96,0,0,2015,7)],3),([(96,0,0,3004,7)],3),
                               ([(96,0,0,2011,7),(128,0,0,2015,7),(192,0,0,3001,7)],6)]:
            with self.subTest(extra=extra):
                rows=self.trace([[0,0,0,0]],arena(extras=extra))
                self.assertEqual(rows[0]['state']['rng'],{'play':expected,'misc':0})

    def test_skill_multiplayer_and_other_player_starts_do_not_consume_rng(self):
        extra=[(96,0,0,3004,1),(128,0,0,3004,23),(160,0,0,2,7),(192,0,0,11,7)]
        self.assertEqual(self.trace([[0,0,0,0]],arena(extras=extra))[0]['state']['rng']['play'],1)

    def test_pistol_rises_before_first_fire_and_view_is_computed_on_first_tick(self):
        rows=self.trace([[0,0,0,1]]*19)
        self.assertEqual(rows[0]['state']['player']['viewZ'],0)
        self.assertNotEqual(rows[1]['state']['player']['viewZ'],0)
        for tick in range(15):
            w=rows[tick]['state']['weapon']
            self.assertEqual((w['state'],w['y']),(12,(122-6*tick)*65536))
        self.assertTrue(all(r['state']['player']['ammo'][0]==50 for r in rows[:19]))
        self.assertEqual(rows[19]['state']['player']['ammo'][0],49)

    def test_release_during_raising_does_not_queue_a_shot(self):
        rows=self.trace([[0,0,0,1]]+[[0,0,0,0]]*25)
        self.assertEqual(rows[-1]['state']['player']['ammo'][0],50)

    def test_silent_pistol_pitch_draw_precedes_status_randomness(self):
        rows=self.trace([[0,0,0,1]]*19)
        self.assertEqual(rows[18]['state']['rng']['misc'],18)
        self.assertEqual(rows[19]['state']['rng']['misc'],20)

    def test_landing_pitch_draw_survives_import_of_crossing_state(self):
        from test_things import sectors
        from test_render import two_rooms
        geom=sectors(two_rooms(),first=(64,192),second=(-16,128))
        rows=self.trace([[25,0,0,0]]*80,geom)
        landings=0
        for before,after in zip(rows,rows[1:]):
            a,b=before['state'],after['state']
            hard_landing=(a['player']['momz'] < -8*65536 and
                          b['player']['momz']==0 and
                          b['player']['z']==b['player']['floor'])
            landings+=hard_landing
            # ST_Ticker always draws once; an audible oof draws once first.
            self.assertEqual((b['rng']['misc']-a['rng']['misc'])%256,1+hard_landing)
        self.assertEqual(landings,1)


if __name__=='__main__': unittest.main()

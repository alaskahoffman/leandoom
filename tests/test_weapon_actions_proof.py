"""Kernel contracts for real firing ticks and the runtime event boundary."""
import re
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime

ROOT = Path(__file__).resolve().parents[1]
HEADER = '''import Doom.Proofs.E1M1WeaponDischarge
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs
'''
AMMO = HEADER + '''
attribute [local irreducible] Weapon.tick
example (gun : Fire.Gun) (c : Weapon.Context)
    (frame : c.state.weapon.frame = WeaponActions.windup gun)
    (timer : c.state.weapon.tics = 1) :
    (Weapon.tick c).player.ammo[gun.ammoIndex] = c.player.ammo[gun.ammoIndex] - 1 :=
  WeaponActions.tick_ammo gun c frame timer
'''
DISPATCH = HEADER + '''
attribute [local irreducible] Simulation.weaponTick Simulation.weaponEvent E1M1WeaponRuntime.install
example (gun : Fire.Gun) (s : Simulation) (keys : UInt32)
    (frame : s.weapon.weapon.frame = WeaponActions.windup gun)
    (timer : s.weapon.weapon.tics = 1) :
    ∃ age, s.weaponTick keys =
      (E1M1WeaponRuntime.install s (Weapon.tick (s.weaponContext keys)) age).weaponEvent
        (s.weaponContext keys).player.ammo (Weapon.tick (s.weaponContext keys)).player
        (WeaponActions.event gun s.weapon.refire) :=
  E1M1WeaponDischarge.firing_dispatch gun s keys frame timer
'''
NAMES = ['WeaponActions.' + n for n in [
    'terminal_entry', 'live_entry', 'live_tick', 'action_ammo', 'action_ammo_bits',
    'action_other_ammo', 'tick_outputs', 'tick_ammo', 'tick_other_ammo', 'tick_spends_one']]
NAMES += ['E1M1WeaponDischarge.' + n for n in [
    'single_event', 'firing_dispatch', 'pistol_event', 'shotgun_event', 'firing_handler']]


class WeaponActionsTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds
    rejects = runtime.WeaponRuntimeTests.rejects

    def test_real_tick_and_runtime_contracts(self):
        self.succeeds(AMMO)
        self.succeeds(DISPATCH)
        for source, old, new in [
            (AMMO, '(timer : c.state.weapon.tics = 1)', '(timer : True)'),
            (AMMO, '(frame : c.state.weapon.frame = WeaponActions.windup gun)', '(frame : True)'),
            (AMMO, 'c.player.ammo[gun.ammoIndex] - 1 :=', 'c.player.ammo[gun.ammoIndex] - 2 :='),
            (DISPATCH, '(timer : s.weapon.weapon.tics = 1)', '(timer : True)'),
            (DISPATCH, '(WeaponActions.event gun s.weapon.refire) :=', '(.noise) :=')]:
            with self.subTest(change=new):
                self.assertIn(old, source)
                self.rejects(source.replace(old, new))

    def test_joined_handler_uses_debit_and_accuracy(self):
        source = HEADER + '''
attribute [local irreducible] Simulation.weaponTick Simulation.fireGun E1M1WeaponRuntime.install Weapon.tick
example (gun : Fire.Gun) (s : Simulation) (keys : UInt32)
    (frame : s.weapon.weapon.frame = WeaponActions.windup gun)
    (timer : s.weapon.weapon.tics = 1) :
    ∃ age, s.weaponTick keys =
      let before := (s.weaponContext keys).player.ammo[gun.ammoIndex]
      let base := E1M1WeaponRuntime.install s (Weapon.tick (s.weaponContext keys)) age
      ({base with lastFire := some {
        gun, tic := s.ticks, ammoBefore := before, ammoAfter := before-1,
        pelletsExpected := gun.pellets}} : Simulation).fireGun
          (gun == .shotgun) (if gun == .pistol then s.weapon.refire == 0 else false) :=
  E1M1WeaponDischarge.firing_handler gun s keys frame timer
'''
        self.succeeds(source)
        self.rejects(source.replace('ammoAfter := before-1', 'ammoAfter := before-2'))
        self.rejects(source.replace('(gun == .shotgun)', '(gun == .pistol)'))

    def test_no_recursive_callback_is_assumed(self):
        self.succeeds(HEADER + '''
example (gun : Fire.Gun) (c : Weapon.Context)
    (again : Weapon.Context → Nat → Weapon.Context)
    (shoot : Weapon.Context → Weapon.Context)
    (check : Weapon.Context → Bool × Weapon.Context) :
    Weapon.enterWith again shoot check c (WeaponActions.firing gun) = WeaponActions.entered gun c :=
  WeaponActions.terminal_entry gun c again shoot check
''')

    def test_concrete_flash_accuracy_ammo_and_queue(self):
        source = HEADER + '''
namespace ActionChecks
def c (gun : Fire.Gun) (ammo refire : Int32) : Weapon.Context :=
  { state := { weapon := {frame := WeaponActions.windup gun, tics := 1}, refire },
    player := {ammo := #v[ammo,ammo,77,88]}, events := #[.noise,.punch] }
example : (Weapon.tick (c .pistol 50 0)).player.ammo[0] = 49 := by rfl
example : (Weapon.tick (c .shotgun 8 1)).player.ammo[1] = 7 := by rfl
example : (Weapon.tick (c .pistol 0 0)).player.ammo[0] = -1 := by rfl
example : (Weapon.tick (c .shotgun (-2147483648) 0)).player.ammo[1] = 2147483647 := by rfl
example : (Weapon.tick (c .pistol 50 0)).events = #[.pistol true] := by rfl
example : (Weapon.tick (c .pistol 50 1)).events = #[.pistol false] := by rfl
example : (Weapon.tick (c .shotgun 8 0)).events = #[.shotgun] := by rfl
example : (Weapon.tick (c .pistol 50 0)).state.flash.tics = 6 := by rfl
example : (Weapon.tick (c .shotgun 8 0)).state.flash.tics = 3 := by rfl
example : (Weapon.tick (c .shotgun 8 0)).state.weapon.tics = 7 := by rfl
example : (Weapon.tick (c .shotgun 8 0)).player.ammo[2] = 77 := by rfl
end ActionChecks
'''
        self.succeeds(source)
        self.rejects(source.replace('flash.tics = 3', 'flash.tics = 4'))
        self.rejects(source.replace('events = #[.pistol false]', 'events = #[.pistol true]'))

    def test_transitive_axioms(self):
        source = HEADER + '\n'.join('#print axioms Doom.Proofs.' + n for n in NAMES) + '\n'
        output = self.succeeds(source)
        entries = re.findall(r"'Doom.Proofs\.([\w.]+)'\s+"
                             r"(?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
        self.assertEqual([name for name, _ in entries], NAMES)
        for name, axioms in entries:
            self.assertLessEqual({a.strip() for a in axioms.split(',') if a.strip()},
                                 {'propext', 'Quot.sound', 'Classical.choice'}, name)
        self.assertNotIn('sorry', output)
        self.assertNotIn('_native', output)


if __name__ == '__main__':
    unittest.main()

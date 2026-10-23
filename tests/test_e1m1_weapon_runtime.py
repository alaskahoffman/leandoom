"""Original-byte weapon observations connected to the live Simulation adapter."""
import os
import re
import signal
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NAMES = ["no_events", "installed", "no_events_install", "flash_latches",
         "countdown_latches", "quiet_install", "quiet_effects", "supported_after",
         "live_correspondence"]
HEADER = '''import Doom.Proofs.E1M1WeaponRuntime
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
'''
BRIDGE = HEADER + '''
-- Keep the runtime and observations opaque when checking the public contract.
attribute [local irreducible] Simulation.weaponTick WeaponFlash.observe E1M1FlashUpdate.observe
example (machine : X86Memory.State) (flags : Option Flags) (p : Word)
    (s : Simulation) (keys : UInt32)
    (h : E1M1WeaponFlash.Inputs machine p s.weapon)
    (quiet : E1M1WeaponFlash.Quiet s.weapon)
    (supported : WeaponFlash.Supported s.weapon)
    (safe : E1M1WeaponFlash.Safe p (machine.regs 4))
    (expiry : ¬ E1M1FlashUpdate.NoTransition s.weapon →
      E1M1FlashExpiry.Tables machine.memory ∧ E1M1FlashExpiry.Separated p (machine.regs 4)) :
    ∃ n t, n ≤ 125 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n
      ⟨machine,flags,0x2dc6f⟩ t ∧
      E1M1FlashUpdate.observe t.core.memory p = WeaponFlash.observe (s.weaponTick keys).weapon :=
  E1M1WeaponRuntime.live_correspondence machine flags p s keys h quiet supported safe expiry
'''


class WeaponRuntimeTests(unittest.TestCase):
    def lean(self, source):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'Check.lean'
            path.write_text(source)
            process = subprocess.Popen([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                                       cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       text=True, start_new_session=True)
            try:
                out, err = process.communicate(timeout=60)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate()
                raise
            return subprocess.CompletedProcess(process.args, process.returncode, out, err)

    def succeeds(self, source):
        result = self.lean(source)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('error:', result.stdout)
        self.assertNotIn('maximum', result.stdout)
        self.assertNotIn('timeout', result.stdout.lower())

    def test_runtime_contract_and_transitive_axioms(self):
        output = self.succeeds(BRIDGE + '\n' + '\n'.join(
            '#print axioms Doom.Proofs.E1M1WeaponRuntime.' + n for n in NAMES))
        entries = re.findall(r"'Doom.Proofs.E1M1WeaponRuntime\.(\w+)'\s+"
                             r"(?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
        self.assertEqual([name for name, _ in entries], NAMES)
        for name, axioms in entries:
            self.assertLessEqual({a.strip() for a in axioms.split(',') if a.strip()},
                                 {'propext', 'Quot.sound', 'Classical.choice'}, name)
        self.assertNotIn('sorry', output)
        self.assertNotIn('_native', output)

    def test_cannot_drop_branch_or_representation_or_change_runtime_observation(self):
        for old, new in [
            ('(quiet : E1M1WeaponFlash.Quiet s.weapon)', '(quiet : True)'),
            ('(h : E1M1WeaponFlash.Inputs machine p s.weapon)', '(h : True)'),
            ('WeaponFlash.observe (s.weaponTick keys).weapon', 'WeaponFlash.observe s.weapon'),
            ('⟨machine,flags,0x2dc6f⟩', '⟨machine,flags,0x2dc60⟩')]:
            with self.subTest(change=new):
                self.assertIn(old, BRIDGE)
                self.rejects(BRIDGE.replace(old, new))

    def test_real_context_and_quiet_effects(self):
        source = HEADER + '''
example (s : Simulation) (keys : UInt32) : s.weaponContext keys =
    ({ state := s.weapon, player := s.inventory.toPickup, body := s.player.animation,
       attack := keyDown keys 8192, dead := s.inventory.health == 0,
       bob := s.player.view.bob, time := Int32.ofNat (s.ticks-1) } : Weapon.Context) := rfl
example (s : Simulation) (keys : UInt32) (quiet : E1M1WeaponFlash.Quiet s.weapon) :
    (s.weaponTick keys).rng = s.rng ∧ (s.weaponTick keys).audio = s.audio ∧
    (s.weaponTick keys).audioEvents = s.audioEvents ∧
    (s.weaponTick keys).soundTargets = s.soundTargets ∧
    (s.weaponTick keys).shots = s.shots ∧
    (s.weaponTick keys).physicsError = s.physicsError :=
  E1M1WeaponRuntime.quiet_effects s keys quiet
'''
        self.succeeds(source)
        self.rejects(source.replace('time := Int32.ofNat (s.ticks-1)', 'time := Int32.ofNat s.ticks'))
        self.rejects(source.replace('(quiet : E1M1WeaponFlash.Quiet s.weapon)', '(quiet : True)'))

    def test_nonvacuous_original_machine_to_live_adapter(self):
        # Reuse the independently checked unaligned-player/wrapping-stack fixture.
        fixture = (ROOT/'tests/reference/e1m1-weapon-flash.lean').read_text()
        fixture = fixture.replace('import Doom.Proofs.E1M1WeaponFlash',
                                  'import Doom.Proofs.E1M1WeaponRuntime')
        fixture += '''
open WeaponFlashChecks
example (s : Simulation) (keys : UInt32) : ∃ n t, n ≤ 125 ∧
    X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n
      ⟨weaponInitial 0x600101 5,none,0x2dc6f⟩ t ∧
    E1M1FlashUpdate.observe t.core.memory 0x600101 =
      WeaponFlash.observe (({s with weapon := context.state} : Simulation).weaponTick keys).weapon := by
  apply E1M1WeaponRuntime.live_correspondence
  all_goals try dsimp only
  · constructor
    · constructor <;> decide
    · decide
    · decide
  · unfold E1M1WeaponFlash.Quiet; decide
  · unfold WeaponFlash.Supported; decide
  · unfold E1M1WeaponFlash.Safe Apart; decide
  · intro _
    constructor
    · constructor <;> decide
    · unfold E1M1FlashExpiry.Separated Apart; decide

-- Held attack and release both follow this branch; the flash really expires.
example (s : Simulation) (keys : UInt32) :
    (({s with weapon := context.state} : Simulation).weaponTick keys).weapon.flash.frame = 31 ∧
    (({s with weapon := context.state} : Simulation).weaponTick keys).weapon.flash.tics = 3 := by
  have quiet : E1M1WeaponFlash.Quiet context.state := by
    unfold E1M1WeaponFlash.Quiet; decide
  let live := ({s with weapon := context.state} : Simulation)
  rw [E1M1WeaponRuntime.installed live keys quiet,
    E1M1WeaponFlash.live_tick (live.weaponContext keys) quiet]
  dsimp only [live, Simulation.weaponContext]
  change (Weapon.tickFlash (E1M1WeaponFlash.countdown context.state)).flash.frame = 31 ∧
    (Weapon.tickFlash (E1M1WeaponFlash.countdown context.state)).flash.tics = 3
  decide +kernel
'''
        self.succeeds(fixture)
        self.rejects(fixture.replace('weapon.flash.frame = 31', 'weapon.flash.frame = 30'))


if __name__ == '__main__':
    unittest.main()

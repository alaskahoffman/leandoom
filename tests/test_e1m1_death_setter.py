"""Pinned player death table, original setter RET, and composed contracts."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_death_setter as proof


class E1M1DeathSetterTests(unittest.TestCase):
    def setUp(self):
        self.spec = json.loads((ROOT/'tests/reference/original-death-setter.json').read_text())
        self.raw = {'setter': bytes.fromhex(self.spec['units']['setter']['hex'])}
        self.raw.update({k: bytes.fromhex(v['hex']) for k, v in self.spec['states'].items()})

    def lean(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'Check.lean'
            path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                                  cwd=ROOT, capture_output=True, text=True)

    def reject_contracts(self, replacements):
        source = proof.certificate(self.raw)
        for old, new in replacements:
            with self.subTest(change=new):
                self.assertIn(old, source)
                result = self.lean(source.replace(old, new))
                self.assertNotEqual(result.returncode, 0, result.stdout+result.stderr)
                self.assertIn('error:', result.stdout)

    def test_certificate_and_strict_audit(self):
        result = self.lean(proof.certificate(self.raw))
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound', 'sorryAx'),
                    result.stdout.replace('Quot.sound', 'bad._native.ax_1'),
                    result.stdout+'unexpected', result.stdout.replace('joined_checked', 'missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)

    def test_changed_instructions_and_state_data_rejected(self):
        for name, offset in [('setter', 28), ('setter', 38), ('setter', 61), ('setter', 90),
                             ('normal', 4), ('normal', 8), ('normal', 12), ('normal', 16),
                             ('extreme', 4), ('extreme', 8)]:
            with self.subTest(unit=name, offset=offset):
                changed = dict(self.raw)
                data = bytearray(changed[name]); data[offset] ^= 1; changed[name] = bytes(data)
                result = self.lean(proof.certificate(changed))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('decide', result.stdout)

    def test_setter_contract_and_return_required(self):
        self.reject_contracts([
            ('(h : DeathSetter.SetterInputs (E1M1DeathSetter.entry extreme) s)', '(h : True)'),
            ('[0x2a3f1] 24', '[0x2a3f1] 23'),
            ('[0x2a3f1] 24', '[0x2a3f2] 24')])

    def test_initial_table_and_separation_contracts_required(self):
        self.reject_contracts([
            ('(ins : E1M1DeathSetter.Inputs s)', '(ins : True)'),
            ('(h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)', '(h : True)'),
            ('(dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)', '(dead : True)'),
            ('(stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32)))', '(stackSafe : True)')])

    def test_wrong_joined_results_rejected(self):
        self.reject_contracts([
            ('[0x2a3f1] 263', '[0x2a3f1] 239'),
            ('t.core.regs 0=1', 't.core.regs 0=0'),
            ('t.core.regs 4=s.regs 4-52', 't.core.regs 4=s.regs 4-56'),
            ('(E1M1DeathSetter.entry extreme).tics,', '(E1M1DeathSetter.entry extreme).tics-1,'),
            ('load32 t.core.memory (0x12c5c#32)=0', 'load32 t.core.memory (0x12c5c#32)=1'),
            ('(PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo',
             'v.health E1M1Death.playerInfo')])

    def test_pinned_code_table_mapping_and_relocations(self):
        exe = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary = proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip', sw, exe)
        self.assertEqual(proof.extraction.extract(binary, exe, self.spec) | proof.table_data(binary, exe, self.spec), self.raw)
        for field, value in [('offset', '0x16b71'), ('index', 159), ('hex', '00'*28)]:
            bad = copy.deepcopy(self.spec); bad['states']['normal'][field] = value
            with self.assertRaises(ValueError): proof.table_data(binary, exe, bad)
        bad = copy.deepcopy(self.spec); bad['units']['setter']['relocations'][0]['object'] = 1
        with self.assertRaises(ValueError): proof.extraction.extract(binary, exe, bad)

    def test_compiled_live_entry_and_rng_preservation(self):
        rows = [(state, seed) for state in [158, 165] for seed in range(256)]
        with tempfile.TemporaryDirectory() as directory:
            inp, out = Path(directory)/'input', Path(directory)/'output'
            inp.write_text(''.join(f'{state} {seed}\n' for state, seed in rows))
            subprocess.run([str(ROOT/'.lake/build/bin/death-probe'), 'state-entry', str(inp), str(out)], check=True)
            expected = [f'{state} {10 if state == 158 else 5} PLAY {7 if state == 158 else 14} {state+1} {seed} 1'
                        for state, seed in rows]
            self.assertEqual(out.read_text().splitlines(), expected)


if __name__ == '__main__': unittest.main()

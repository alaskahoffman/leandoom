"""Death timing certificate, RNG/frame contracts, and executable probe checks."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_death_timing as proof


class E1M1DeathTimingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec = json.loads((ROOT/'tests/reference/original-death-timing.json').read_text())
        cls.exe = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
        cls.binary = proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip', sw, cls.exe)
        cls.raw = proof.extract(cls.binary, cls.exe, cls.spec)

    def lean(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'Check.lean'; path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                                  cwd=ROOT, capture_output=True, text=True)

    def reject(self, replacements):
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

    def test_changed_call_mask_clamp_rng_and_table_rejected(self):
        for name, offset in [('timing', 1), ('timing', 7), ('timing', 12), ('timing', 18),
                             ('timing', 20), ('timing', 24), ('rng', 7), ('rng', 27), ('table', 0), ('table', 255)]:
            with self.subTest(unit=name, offset=offset):
                raw = dict(self.raw); data = bytearray(raw[name]); data[offset] ^= 1; raw[name] = bytes(data)
                result = self.lean(proof.certificate(raw))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('decide', result.stdout)

    def test_local_contract_and_execution_bound_required(self):
        self.reject([('(h : DeathTiming.Inputs s i)', '(h : True)'),
                     ('[0x2a40d] 15', '[0x2a40d] 13'),
                     ('⟨s,f,0x2a3f1⟩', '⟨s,f,0x2a3f6⟩')])

    def test_joined_memory_and_rng_contracts_required(self):
        self.reject([('(ins : E1M1DeathTiming.Inputs s sim.rng)', '(ins : True)'),
                     ('(stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32)))', '(stackSafe : True)'),
                     ('(dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)', '(dead : True)')])

    def test_wrong_tics_rng_stream_and_preservation_rejected(self):
        self.reject([('DeathTiming.playerTicks extreme sim.rng.play,', '(E1M1DeathSetter.entry extreme).tics,'),
                     ('FloorDamage.nextIndex sim.rng.play ∧', 'BitVec.ofNat 32 sim.rng.play.toNat ∧'),
                     ('BitVec.ofNat 32 sim.rng.misc.toNat ∧', 'BitVec.ofNat 32 (sim.rng.misc+1).toNat ∧'),
                     ('[0x2a40d] 278', '[0x2a40d] 263'),
                     ('t.core.regs 4=s.regs 4-52', 't.core.regs 4=s.regs 4-56')])

    def test_code_and_rng_relocations_checked(self):
        for unit, field, value in [('timing', 'file_offset', '0x0'), ('timing', 'code_offset', '0x2a3f2')]:
            bad = copy.deepcopy(self.spec); bad['units'][unit][field] = value
            with self.assertRaises(ValueError): proof.extract(self.binary, self.exe, bad)
        bad = copy.deepcopy(self.spec); bad['units']['rng']['relocations'].clear()
        with self.assertRaises(ValueError): proof.extract(self.binary, self.exe, bad)

    def test_short_and_decoder_all_registers_and_immediates(self):
        result = self.lean((ROOT/'tests/reference/x86-and-immediate.lean').read_text())
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        self.assertEqual(result.stdout, '')

    def test_compiled_timing_wrap_clamp_and_both_rng_streams(self):
        corpus = proof.cases()
        with tempfile.TemporaryDirectory() as directory:
            inp, out = Path(directory)/'input', Path(directory)/'output'
            inp.write_text(''.join(f'{tics} {play} {misc}\n' for tics, play, misc, _ in corpus))
            subprocess.run([str(ROOT/'.lake/build/bin/death-probe'), 'death-timing', str(inp), str(out)], check=True)
            expected = []
            for tics, play, misc, _ in corpus:
                value = (tics-(self.raw['table'][(play+1)%256]&3))&0xffffffff
                if value >= 2**31: value -= 2**32
                expected.append(f'{max(1,value)} {(play+1)%256} {misc} 1')
            self.assertEqual(out.read_text().splitlines(), expected)


if __name__ == '__main__': unittest.main()

"""Allocation-derived memory guards, child restoration and byte-boundary failures."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_allocation as proof
class NoiseAllocationTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('restore_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_required_contracts(self):
        s=proof.certificate()
        for old,new in [('(allocation : Allocation table stack)','(allocation : True)'),
            ('(room : StackRoom stack s)','(room : True)'),
            ('(member : s.regs 0∈layout table)','(member : True)'),
            ('(count : s.regs 2=(0#32) ∨ s.regs 2=(1#32))','(count : True)'),
            ('(footprint : BelowFrame table s w)','(footprint : True)'),
            ('(low : 20 ≤ (s.regs 4).toNat)','(low : True)'),
            ('(trace : CheckedTrace (layout table) .sector s t w n)','(trace : True)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def fixture(self):
        return (ROOT/'tests/reference/original-noise-allocation.lean').read_text()
    def test_unaligned_allocation_and_actual_child_resume(self):
        r=self.lean(self.fixture());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_overlapping_layouts_rejected(self):
        # Only the static certificate is needed to expose these bad layouts.
        s=self.fixture().split('theorem initial_room')[0]+'end Doom.Verification.NoiseAllocationFixture\n'
        for old,new in [('0x700000,0x701000','0x600100,0x701000'),
            ('⟨origin,0x600b01,[wall,wall]⟩','⟨origin,origin+78,[wall,wall]⟩'),
            ('def other : Word := 0x600201','def other : Word := 0x600150')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_byte_overlap_wrap_and_saved_word_overwrite_rejected(self):
        prefix='''import Doom.Proofs.E1M1NoiseAllocation
open Doom.Proofs Doom.Verification X86 X86Memory E1M1NoiseAllocation
'''
        claims=[
            '(Region.mk 101 105).Disjoint (Region.mk 104 108)',
            '(Region.mk 4294967293 4294967297).Contains (4294967293#32)',
            '(Region.mk 100 104).Contains (101#32)',
        ]
        for claim in claims:
            with self.subTest(claim=claim):
                r=self.lean(prefix+'example : '+claim+' := by decide +kernel\n')
                self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
        # The first five writes are prologue stores; a later saved-word write
        # must not be discarded merely because it repeats a prologue address.
        s=prefix+'''
def entry : X86Memory.State := ⟨fun _ => 100, fun _ => 0⟩
example : BelowFrame [] entry [0,0,0,0,0,100] := by
  simp only [BelowFrame,List.drop,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq,exists_false,false_and] 
  decide +kernel
'''
        r=self.lean(s);self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
if __name__=='__main__':unittest.main()

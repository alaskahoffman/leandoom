"""Initializer memory relations, overlap consistency and sparse preservation."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_image as proof
class NoiseImageTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('completion_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_required_contracts(self):
        s=proof.certificate()
        for old,new in [('(consistent : Consistent p)','(consistent : True)'),
            ('(different : old≠generation)','(different : True)'),
            ('(consistent : Consistent (freshImage table base edges generation old))','(consistent : True)'),
            ('(allocation : Allocation (t.table a) stack)','(allocation : True)'),
            ('(storage : Storage (t.table a) stack base (t.edges a) regions)','(storage : True)'),
            ('(consistent : Consistent (freshImage (t.table a) base (t.edges a) generation old))','(consistent : True)'),
            ('(inside : index<t.sectors.length)','(inside : True)'),
            ('(count : s.core.regs 2=0 ∨ s.core.regs 2=1)','(count : True)'),
            ('56*t.sectors.length+20','28*t.sectors.length+20')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def fixture(self):
        return (ROOT/'tests/reference/original-noise-image.lean').read_text()
    def test_initialized_memory_and_completion(self):
        r=self.lean(self.fixture());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_conflicting_shared_side_or_aliased_array_rejected(self):
        s=self.fixture().split('theorem certified')[0]
        s+='example : Consistent plan := by decide +kernel\nend Doom.Verification.NoiseImageFixture\n'
        for old,new in [('⟨1,4,1,0,1,0⟩','⟨1,4,1,0,0,0⟩'),('0x600b01','0x60014f')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('false',r.stdout)
    def test_wrapping_little_endian_writes_duplicate_bytes_and_sentinel(self):
        s='''import Doom.Proofs.E1M1NoiseImage
open Doom Doom.Proofs Doom.Verification X86 X86Memory E1M1NoiseGraph E1M1NoiseImage
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
-- The same word can be repeated, and a matching high half may overlap it.
example : Consistent (word 0x1001 0x12345678 ++ word 0x1001 0x12345678 ++ half 0x1003 0x1234) := by decide +kernel
example : ¬Consistent (word 0x1001 0x12345678 ++ half 0x1003 0x1235) := by decide +kernel
example : applyPatch (word 0xffffffff 0x12345678) (fun _ => 0xaa) 0xffffffff=0x78 ∧
    applyPatch (word 0xffffffff 0x12345678) (fun _ => 0xaa) 0=0x56 ∧
    load32 (applyPatch (word 0xffffffff 0x12345678) (fun _ => 0xaa)) 0xffffffff=0x12345678 := by decide +kernel
example : load16 (applyPatch (half 0xffffffff 0x1234) (fun _ => 0xaa)) 0xffffffff=0x1234 := by decide +kernel
-- One-sided back index -1 is installed, but no back-sector pointer is written.
def edge : Edge := ⟨0x600001,0,0,65535,0x600101,0⟩
def plan := graphPatch 0x600801 [edge]
example : Consistent plan := by decide +kernel
example : load16 (applyPatch plan (fun _ => 0xaa)) (edge.line+24)=65535 := by decide +kernel
example : applyPatch plan (fun _ => 0xaa) (0x600801-4)=0xaa := by decide +kernel
example : GraphRep 0x600801 [edge] (applyPatch plan (fun _ => 0xaa)) :=
  graph_rep (realizes (by decide +kernel) _)
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

"""Original aim setup, explicit aliasing contracts, and actual traversal CALL."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_aim_setup as proof

class AimSetupTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    rejects=runtime.WeaponRuntimeTests.rejects

    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-aim-setup.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_axioms(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('first_traversal_correspondence','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_execution_contract_mutations(self):
        for offset in [1,20,37,40,56,61,67,90,94]:
            raw={'setup':bytearray(self.raw['setup'])};raw['setup'][offset]^=1
            with self.subTest(offset=offset):self.rejects(proof.certificate(raw))
        source=self.source.replace('namespace Doom.Verification.ExtractedAimSetup','set_option backward.isDefEq.respectTransparency true\nnamespace Doom.Verification.ExtractedAimSetup')
        source=source.replace('theorem execution_checked','attribute [local irreducible] traversal\ntheorem execution_checked')
        self.succeeds(source)
        for old,new in [('[] 25 ⟨s,f,0x2bba0⟩','[] 24 ⟨s,f,0x2bba0⟩'),('[] 25 ⟨s,f,0x2bba0⟩','[] 25 ⟨s,f,0x2bba5⟩')]:self.rejects(source.replace(old,new))

    def test_push_decode_sign_extension_and_stack(self):
        self.succeeds('''import Doom.Proofs.OriginalAimSetup
open Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
example (i : UInt8) : X86Routine.decode [0x6a,i,0x90]=
  some (.pushImmediate (i.toBitVec.signExtend 32),[0x90]) := rfl
example : X86Routine.decode [0x6a,0x80]=some (.pushImmediate 0xffffff80,[]) := by decide
example : X86Routine.decode [0x6a,0xff]=some (.pushImmediate 0xffffffff,[]) := by decide
example : X86Routine.decode [0x68,0,0,0,0x80,0x90]=some (.pushImmediate 0x80000000,[0x90]) := by decide
example : X86Routine.decode [0x68,0,0,0]=none := by decide
example : X86Routine.decode [0x6a]=none := by decide
example (s : X86Control.State) (v : Word) :
    (X86Routine.execute (.pushImmediate v) s).map (·.core.regs 4)=some (s.core.regs 4-4) := by
  simp [X86Routine.execute,X86Routine.pushWord,write]
example (s : X86Control.State) (v : Word) :
    (X86Routine.execute (.pushImmediate v) s).map (fun t => load32 t.core.memory (t.core.regs 4))=some v := by
  simp [X86Routine.execute,X86Routine.pushWord,write,load_store]
example (s : X86Control.State) (v : Word) :
    (X86Routine.execute (.pushImmediate v) s).map (·.flags)=some s.flags := rfl
''')

    def test_missing_representation_or_separation_rejected(self):
        source='''import Doom.Proofs.E1M1AimSetup
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control OriginalAimSetup
attribute [local irreducible] traversal
example (s : X86Memory.State) (t : Collision.SolidThing) (a : Angle) (d : Fixed)
    (h : Inputs s t a d) : Ready s (traversal s) t a d := ready s t a d h
example (s : X86Memory.State) (safe : Separated s) :
    load32 (traversal s).core.memory (s.regs 4-4)=0x2b760 := stored_callback s safe
example (s : X86Memory.State) (addr : Word)
    (safe : ∀ b, b ∈ (writes s).toList → BlockSummary.Apart addr b) :
    load32 (m9 s) addr=load32 s.memory addr := frame9 s addr safe
'''
        self.succeeds(source)
        for old,new in [('(h : Inputs s t a d)','(h : True)'),('(safe : Separated s)','(safe : True)'),
                        ('BlockSummary.Apart addr b','True')]:self.rejects(source.replace(old,new))

    def test_concrete_geometry_and_wrapping_call_frame(self):
        source=(ROOT/'tests/reference/original-aim-setup.lean').read_text()
        self.succeeds(source)
        for old,new in [('0x2b9a8=0x7fffd','0x2b9a8=0x7fffe'),('0xfffffff9=3','0xfffffff9=1'),('0xfffffffd=0x2b760','0xfffffffd=0x2bb80')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_joined_real_discharge_fixture(self):
        source=(ROOT/'tests/reference/e1m1-discharge-setters.lean').read_text().replace('import Doom.Proofs.E1M1DischargeSetters','import Doom.Proofs.E1M1AimSetup')
        source+='''
open DischargeSettersFixture
example (i : Fin 4) : ∃ n, n≤163 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1AimSetup.program [] n
    ⟨machine (gunOf i) (ammoOf i),none,OriginalWeaponDischarge.afterSound (gunOf i)⟩
    (E1M1AimSetup.firstTraversal (gunOf i) (machine (gunOf i) (ammoOf i))) :=
  E1M1AimSetup.first_traversal_execution _ _ _ _ (inputs i)
example : (E1M1AimSetup.firstTraversal .pistol (machine .pistol 8)).pc=0x2c8a0 := by decide +kernel
example : load32 (E1M1AimSetup.firstTraversal .shotgun (machine .shotgun 8)).core.memory 0x2b9f8=0 := by decide +kernel
'''
        self.succeeds(source)

    def test_extraction_and_code_pointer_relocation(self):
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec,allowed_objects=(1,3)),self.raw)
        with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,self.spec)
        for field,value in [('relocations',[]),('code_offset','0x2bba1'),('file_offset','0x6dbb5')]:
            spec=copy.deepcopy(self.spec);spec['units']['setup'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec,allowed_objects=(1,3))
        spec=copy.deepcopy(self.spec);spec['units']['setup']['relocations'][0]['object']=3
        with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec,allowed_objects=(1,3))

if __name__=='__main__':unittest.main()

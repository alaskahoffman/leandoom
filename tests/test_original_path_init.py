"""Pinned traversal initialization, production geometry, and firing joins."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_path_init as proof

class PathInitTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    rejects=runtime.WeaponRuntimeTests.rejects

    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-path-init.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_axioms(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('first_path_correspondence','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_execution_contract_mutations(self):
        for offset in [3,24,49,58,63,79,86,106,157,193]:
            raw={'init':bytearray(self.raw['init'])};raw['init'][offset]^=1
            with self.subTest(offset=offset):self.rejects(proof.certificate(raw))
        source=self.source.replace('namespace Doom.Verification.ExtractedPathInit','set_option backward.isDefEq.respectTransparency true\nnamespace Doom.Verification.ExtractedPathInit')
        source=source.replace('theorem execution_checked','attribute [local irreducible] result\ntheorem execution_checked')
        self.succeeds(source)
        for old,new in [('n≤60','n≤59'),('⟨s,f,0x2c8a0⟩','⟨s,f,0x2c8a1⟩')]:self.rejects(source.replace(old,new))

    def test_test_and_inc_decoding(self):
        self.succeeds('''import Doom.Proofs.OriginalPathInit
open Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
example : X86Routine.decode [0xa9,0xff,0xff,0x7f,0,0x90]=
    some (.testRegisterImmediate 0 0x7fffff,[0x90]) := by decide
example : X86Routine.decode [0xa9,0xff,0xff,0x7f]=none := by decide
example : X86Routine.decode [0x43,0x90]=some (.addImmediate 3 1,[0x90]) := by decide
example (s : X86Control.State) (mask : Word) :
    (X86Routine.execute (.testRegisterImmediate 0 mask) s).map (·.core)=some s.core := rfl
example (s : X86Control.State) (mask : Word) :
    (X86Routine.execute (.testRegisterImmediate 0 mask) s).map (·.flags)=
      some (some (logical32 (s.core.regs 0 &&& mask))) := rfl
example (s : X86Control.State) :
    (X86Routine.execute (.addImmediate 3 1) s).map (·.flags)=some none := rfl
''')

    def test_encoding_and_separation_required(self):
        source='''import Doom.Proofs.E1M1PathInit
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control OriginalPathInit
attribute [local irreducible] result
example (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (h : Inputs s ox oy sx sy ex ey) : Ready s (result s) (Collision.pathStart ox oy sx sy ex ey) :=
  ready s ox oy sx sy ex ey h
example (s : X86Memory.State) (safe : Separated s) :
    load32 (result s).core.memory 0x2c028=0x2ba20 := stored_4 s safe
example (s : X86Memory.State) (addr : Word)
    (safe : ∀ b, b ∈ (writes s).toList → BlockSummary.Apart addr b) :
    load32 (m15 s) addr=load32 s.memory addr := frame15 s addr safe
'''
        self.succeeds(source)
        for old,new in [('(h : Inputs s ox oy sx sy ex ey)','(h : True)'),('(safe : Separated s)','(safe : True)'),
                        ('BlockSummary.Apart addr b','True')]:self.rejects(source.replace(old,new))

    def test_prior_shot_geometry_is_reused(self):
        source='''import Doom.Proofs.E1M1PathInit
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] OriginalAimSetup.traversal
example (s : X86Memory.State) (thing : Collision.SolidThing) (angle : Angle)
    (distance ox oy : Fixed) (h : OriginalAimSetup.Inputs s thing angle distance)
    (originX : load32 (OriginalAimSetup.traversal s).core.memory 0x2c104=ox.raw.toBitVec)
    (originY : load32 (OriginalAimSetup.traversal s).core.memory 0x2c108=oy.raw.toBitVec)
    (reads : ∀ a, a ∈ OriginalPathInit.reads (OriginalAimSetup.traversal s).core →
      ∀ b, b ∈ (OriginalPathInit.writes (OriginalAimSetup.traversal s).core).toList → Apart a b)
    (separated : OriginalPathInit.Separated (OriginalAimSetup.traversal s).core) :
    OriginalPathInit.Inputs (OriginalAimSetup.traversal s).core ox oy thing.x thing.y
      (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2 :=
  E1M1PathInit.inputs_from_setup s thing angle distance ox oy h originX originY reads separated
'''
        self.succeeds(source)
        for old,new in [('(h : OriginalAimSetup.Inputs s thing angle distance)','(h : True)'),
                        ('0x2c104=ox.raw.toBitVec','0x2c104=oy.raw.toBitVec')]:self.rejects(source.replace(old,new))

    def test_quadrants_signed_blocks_and_wrapping_stack(self):
        source=(ROOT/'tests/reference/original-path-init.lean').read_text();self.succeeds(source)
        for old,new in [('0x2ba10=0xff810000','0x2ba10=0xff800000'),('0xffffffd1=0xffffffff','0xffffffd1=0'),('0xffffffcd=512','0xffffffcd=511'),('0x13580=0','0x13580=1')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_joined_real_discharge_fixture(self):
        source=(ROOT/'tests/reference/e1m1-discharge-setters.lean').read_text().replace('import Doom.Proofs.E1M1DischargeSetters','import Doom.Proofs.E1M1PathInit')
        source+='''
open DischargeSettersFixture
example (i : Fin 4) : ∃ n, n≤223 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PathInit.program [] n
    ⟨machine (gunOf i) (ammoOf i),none,OriginalWeaponDischarge.afterSound (gunOf i)⟩
    (E1M1PathInit.firstPath (gunOf i) (machine (gunOf i) (ammoOf i))) :=
  E1M1PathInit.first_path_execution _ _ _ _ (inputs i)
example : (E1M1PathInit.firstPath .pistol (machine .pistol 8)).pc=0x2c96c := by decide +kernel
'''
        self.succeeds(source)

    def test_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        for field,value in [('relocations',[]),('code_offset','0x2c8a1'),('file_offset','0x6e8b5')]:
            spec=copy.deepcopy(self.spec);spec['units']['init'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec)
        spec=copy.deepcopy(self.spec);spec['units']['init']['relocations'][0]['object']=1
        with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec,allowed_objects=(1,3))

if __name__=='__main__':unittest.main()

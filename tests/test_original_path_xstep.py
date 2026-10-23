"""Original X-axis setup: actual helper calls, live geometry and firing joins."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_path_xstep as proof

class PathXStepTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    rejects=runtime.WeaponRuntimeTests.rejects

    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-path-xstep.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_axioms(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('first_xstep_correspondence','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_all_three_byte_ranges_and_execution_contract(self):
        for name,offset in [('xstep',12),('xstep',17),('xstep',42),('xstep',93),('abs',3),('abs',5),('division',26),('division',61)]:
            raw={k:bytearray(v) for k,v in self.raw.items()};raw[name][offset]^=1
            with self.subTest(name=name,offset=offset):self.rejects(proof.certificate(raw))
        source=self.source.replace('namespace Doom.Verification.ExtractedPathXStep','set_option backward.isDefEq.respectTransparency true\nnamespace Doom.Verification.ExtractedPathXStep')
        source=source.replace('theorem execution_checked','attribute [local irreducible] result\ntheorem execution_checked')
        self.succeeds(source)
        for old,new in [('n≤45','n≤44'),('⟨s,f,0x2c96c⟩','⟨s,f,0x2c96e⟩'),('(safe : Safe s)','(safe : True)')]:self.rejects(source.replace(old,new))

    def test_live_success_and_encoding_required(self):
        source='''import Doom.Proofs.E1M1PathXStep
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control OriginalPathXStep
attribute [local irreducible] result Collision.PathStart.xStep
example (s : X86Memory.State) (p : Collision.PathStart) (out : Int32 × Fixed × Fixed)
    (h : Inputs s p) (ok : p.xStep=.ok out) :
    Safe s ∧ observe s (result s)=liveObserve out := live s p out h ok
'''
        self.succeeds(source)
        for old,new in [('(h : Inputs s p)','(h : True)'),('(ok : p.xStep=.ok out)','(ok : True)')]:self.rejects(source.replace(old,new))

    def test_kernel_direction_saturation_and_wrapping_fixtures(self):
        source=(ROOT/'tests/reference/original-path-xstep.lean').read_text();self.succeeds(source)
        for old,new in [('(1,⟨65280⟩,⟨32768⟩)','(1,⟨65281⟩,⟨32768⟩)'),('(-1,⟨256⟩,⟨32768⟩)','(1,⟨256⟩,⟨32768⟩)'),
                        ('(1,⟨1⟩,⟨2147483647⟩)','(1,⟨1⟩,⟨2147483646⟩)')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_previous_initialization_supplies_inputs(self):
        source=(ROOT/'tests/reference/original-path-init.lean').read_text().replace('import Doom.Proofs.E1M1PathInit','import Doom.Proofs.E1M1PathXStep')
        source+='''
open PathInitFixture
example : OriginalPathXStep.Inputs (OriginalPathInit.result machine).core
    (Collision.pathStart ox oy sx sy ex ey) := E1M1PathXStep.inputs_from_init _ _ _ _ _ _ _ inputs
'''
        self.succeeds(source)

    def test_joined_real_discharge_contract(self):
        source=(ROOT/'tests/reference/e1m1-discharge-setters.lean').read_text().replace('import Doom.Proofs.E1M1DischargeSetters','import Doom.Proofs.E1M1PathXStep')
        source+='''
open DischargeSettersFixture
example (i : Fin 4)
    (safe : OriginalPathXStep.Safe (E1M1PathInit.firstPath (gunOf i) (machine (gunOf i) (ammoOf i))).core) :
    ∃ n, n≤268 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PathXStep.program [] n
    ⟨machine (gunOf i) (ammoOf i),none,OriginalWeaponDischarge.afterSound (gunOf i)⟩
    (E1M1PathXStep.firstXStep (gunOf i) (machine (gunOf i) (ammoOf i))) :=
  E1M1PathXStep.first_xstep_execution _ _ _ _ (inputs i) safe
'''
        self.succeeds(source)
        self.rejects(source.replace('n≤268','n≤267'))

    def test_abs_register_memory_and_guarded_int_min(self):
        self.succeeds('''import Doom.Proofs.OriginalAbs
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
example : OriginalAbs.value 0xffffffff=1 := by decide +kernel
example : OriginalAbs.value 0x80000000=0x80000000 := by decide +kernel
example (s : X86Memory.State) : (OriginalAbs.result s).core.memory=s.memory := OriginalAbs.memory s
example (a b : Fixed) (ok : Collision.checkedPathAbs a=.ok b) :
    OriginalAbs.value a.raw.toBitVec=b.raw.toBitVec := OriginalAbs.checked a b ok
example : Collision.checkedPathAbs ⟨-2147483648⟩=.error "path: unverified abs(INT_MIN)" := rfl
''')

    def test_original_file_mappings_and_no_relocations(self):
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        for name in self.raw:
            for field in ['code_offset','file_offset']:
                spec=copy.deepcopy(self.spec);spec['units'][name][field]=hex(int(spec['units'][name][field],16)+1)
                with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec)
        spec=copy.deepcopy(self.spec);spec['units']['abs']['relocations']=[{'offset':0,'object':3,'target':'0'}]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec)

if __name__=='__main__':unittest.main()

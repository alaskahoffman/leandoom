"""DOS autoaim controller and the actual Lean three-query policy."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_bullet_slope as proof

class BulletSlopeTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    rejects=runtime.WeaponRuntimeTests.rejects

    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-bullet-slope.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_axioms(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('first_query_execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_branch_and_argument_mutations(self):
        for offset in [9,20,35,43,64,77,90,98]:
            raw={'slope':bytearray(self.raw['slope'])};raw['slope'][offset]^=1
            with self.subTest(offset=offset):self.rejects(proof.certificate(raw))

    def test_machine_bound_and_entry_contracts(self):
        source=self.source.replace('namespace Doom.Verification.ExtractedBulletSlope', 'set_option backward.isDefEq.respectTransparency true\nnamespace Doom.Verification.ExtractedBulletSlope')
        source=source.replace('theorem first_checked', 'attribute [local irreducible] firstCall decision retryState\ntheorem first_checked')
        self.succeeds(source)
        for old,new in [('[] 9 ⟨s,f,0x2d7c0⟩','[] 8 ⟨s,f,0x2d7c0⟩'),
                        ('if second then 4 else 5','if second then 5 else 4'),
                        ('if second then 0x2d7f8 else 0x2d7d5','if second then 0x2d7d5 else 0x2d7f8')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_production_selection_premises(self):
        source='''import Doom.Proofs.E1M1BulletAim
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Collision
attribute [local irreducible] Scene.bulletAim BulletAim.choose BulletAim.controllerSlope
example (scene : Scene) (shooter : Nat) (angle : Angle) (r : AimResult)
    (probe : BulletAim.query scene shooter angle 0=.ok r) (hit : r.target.isSome=true) :
    scene.bulletAim shooter angle=.ok (BulletAim.selection angle 0 r) :=
  BulletAim.live_center scene shooter angle r probe hit
example (angle : Angle) (a b c : AimResult)
    (zero : c.target.isSome=false → c.slope=⟨0⟩) :
    (BulletAim.choose angle a b c).slope=BulletAim.controllerSlope a b c :=
  BulletAim.selection_slope angle a b c zero
'''
        self.succeeds(source)
        for old,new in [('(hit : r.target.isSome=true)','(hit : True)'),
                        ('(probe : BulletAim.query scene shooter angle 0=.ok r)','(probe : True)'),
                        ('(zero : c.target.isSome=false → c.slope=⟨0⟩)','(zero : True)')]:
            self.rejects(source.replace(old,new))

    def test_concrete_controller_edges(self):
        source=(ROOT/'tests/reference/original-bullet-slope.lean').read_text()
        self.succeeds(source)
        for old,new in [(').pc=0x2d81e',').pc=0x2d7e4'),('regs 2=0xfc000000','regs 2=0x04000000'),
                        ('0x2c0c0=123','0x2c0c0=0')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_join_to_real_discharge_fixture(self):
        source=(ROOT/'tests/reference/e1m1-discharge-setters.lean').read_text().replace('import Doom.Proofs.E1M1DischargeSetters','import Doom.Proofs.E1M1BulletAim')
        source+='''
open DischargeSettersFixture
example (i : Fin 4) : ∃ n, n≤127 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1BulletAim.program [] n
    ⟨machine (gunOf i) (ammoOf i),none,OriginalWeaponDischarge.afterSound (gunOf i)⟩
    (E1M1BulletAim.firstQuery (gunOf i) (machine (gunOf i) (ammoOf i))) :=
  E1M1BulletAim.first_query_execution _ _ _ _ (inputs i)
example : (E1M1BulletAim.firstQuery .pistol (machine .pistol 8)).core.regs 0=obj := by decide +kernel
example : (E1M1BulletAim.firstQuery .shotgun (machine .shotgun 8)).core.regs 2=0 := by decide +kernel
example : (E1M1BulletAim.firstQuery .shotgun (machine .shotgun 8)).core.regs 3=0x04000000 := by decide +kernel
'''
        self.succeeds(source)

    def test_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        for field,value in [('relocations',[]),('code_offset','0x2d7c1'),('file_offset','0x6f7d5')]:
            spec=copy.deepcopy(self.spec);spec['units']['slope'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec)

if __name__=='__main__':unittest.main()

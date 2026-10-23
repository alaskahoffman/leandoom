"""DOS ray arithmetic, real return branches, and joins to the firing prefix."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_aim_query as proof

class AimQueryTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    rejects=runtime.WeaponRuntimeTests.rejects

    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-aim-query.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_axioms(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('first_ray_execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_execution_contract_mutations(self):
        for name,offset in [('ray',14),('ray',17),('ray',23),('ray',28),('ret',8),('ret',20),('ret',25)]:
            raw=dict(self.raw);raw[name]=bytearray(raw[name]);raw[name][offset]^=1
            with self.subTest(unit=name,offset=offset):self.rejects(proof.certificate(raw))
        source=self.source.replace('namespace Doom.Verification.ExtractedAimQuery','set_option backward.isDefEq.respectTransparency true\nnamespace Doom.Verification.ExtractedAimQuery')
        source=source.replace('theorem ray_checked','attribute [local irreducible] ray returned\ntheorem ray_checked')
        self.succeeds(source)
        for old,new in [('[] 11 ⟨s,f,0x2bb80⟩','[] 10 ⟨s,f,0x2bb80⟩'),('[] 8 ⟨s,f,0x2bbff⟩','[] 8 ⟨s,f,0x2bc08⟩')]:self.rejects(source.replace(old,new))

    def test_imul_decode_and_flags(self):
        self.succeeds('''import Doom.Proofs.OriginalAimQuery
open Doom.Verification X86 X86Memory X86Control
example : ∀ dst src : Fin 8,
    X86Routine.decode [0x0f,0xaf,UInt8.ofNat (192+dst.val*8+src.val)]=
    some (.multiplyRegister dst src,[]) := by decide
example : X86Routine.decode [0x0f,0xaf,0xce,0x90]=some (.multiplyRegister 1 6,[0x90]) := by decide
example : X86Routine.decode [0x0f,0xaf,0x34,0x95,0x84,0x5a,0,0,0x90]=
  some (.multiplyLoaded 6 ⟨none,some 2,2,0x5a84⟩,[0x90]) := by decide
example : X86Routine.decode [0x0f,0xaf]=none := by decide
example : X86Routine.decode [0x0f,0xaf,0x34,0x95,0x84,0x5a,0]=none := by decide
example (s : X86Control.State) :
    (X86Routine.execute (.multiplyRegister 1 6) s).map (·.core.regs 1)=
    some (s.core.regs 1*s.core.regs 6) := by simp [X86Routine.execute,put,write]
example (s : X86Control.State) :
    (X86Routine.execute (.multiplyLoaded 6 ⟨none,some 2,2,0x5a84⟩) s).map (·.flags)=some none := rfl
''')

    def test_production_and_return_premises(self):
        source='''import Doom.Proofs.E1M1AimQuery
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control OriginalAimQuery
attribute [local irreducible] returned ray Collision.SolidThing.attackEndpoint
example (s : X86Memory.State) (a : Angle) (d : Fixed) (t : Collision.SolidThing)
    (h : RayInputs s a d) :
    (t.x.raw.toBitVec+(ray s).core.regs 1,t.y.raw.toBitVec+(ray s).core.regs 6)=
    ((t.attackEndpoint a d).1.raw.toBitVec,(t.attackEndpoint a d).2.raw.toBitVec) :=
  live_endpoint s t a d h
example (s : X86Memory.State) (miss : target s=0) : (returned s).core.regs 0=0 := return_miss s miss
example (s : X86Memory.State) (f : Option Flags) (hit : target s≠0)
    (resume : (load32 s.memory (s.regs 4+16)).toNat=0x2d7d5) :
    X86CodeMemory.Prefix FloorCaller.cm E1M1AimQuery.program [] 17 ⟨s,f,0x2bbff⟩
    (E1M1BulletAim.accepted false (returned s).core) := E1M1AimQuery.return_to_accept false s f resume hit
'''
        self.succeeds(source)
        for old,new in [('(h : RayInputs s a d)','(h : True)'),('(miss : target s=0)','(miss : True)'),
                        ('(hit : target s≠0)','(hit : True)'),(').toNat=0x2d7d5',').toNat=0x2d7f8')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_real_discharge_and_wrapping_return(self):
        source=(ROOT/'tests/reference/e1m1-discharge-setters.lean').read_text().replace('import Doom.Proofs.E1M1DischargeSetters','import Doom.Proofs.E1M1AimQuery')
        source+='''
open DischargeSettersFixture OriginalAimQuery
example (i : Fin 4) : ∃ n, n≤138 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1AimQuery.program [] n
    ⟨machine (gunOf i) (ammoOf i),none,OriginalWeaponDischarge.afterSound (gunOf i)⟩
    (E1M1AimQuery.firstRay (gunOf i) (machine (gunOf i) (ammoOf i))) :=
  E1M1AimQuery.first_ray_execution _ _ _ _ (inputs i)
def returnFixture (hit : Bool) : X86Memory.State :=
  ⟨fun r => if r=4 then 0xfffffff1 else 123,
    store32 (store32 (store32 (store32 (store32 (store32 (store32 (fun _ => 0)
      0xfffffff1 55) 0xfffffff5 77) 0xfffffff9 66) 0xfffffffd 11) 1 0x2d7d5)
      0x2b9f8 (if hit then 1 else 0)) 0x2b9b4 0x80000000⟩
example : (returned (returnFixture false)).core.regs 0=0 := by decide +kernel
example : (returned (returnFixture true)).core.regs 0=0x80000000 := by decide +kernel
example : (returned (returnFixture true)).pc=0x2d7d5 := by decide +kernel
example : (returned (returnFixture true)).core.regs 4=5 := by decide +kernel
example : (returned (returnFixture true)).core.regs 1=11 := by decide +kernel
'''
        self.succeeds(source)

    def test_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        for field,value in [('relocations',[]),('code_offset','0x2bb81'),('file_offset','0x6db95')]:
            spec=copy.deepcopy(self.spec);spec['units']['ray'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec)

if __name__=='__main__':unittest.main()

"""Pinned first grid crossing, preserved coordinates and continuous firing proof."""
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_path_intercept as proof

HEADER='''import Doom.Proofs.E1M1PathIntercept
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
'''

class PathInterceptTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    rejects=runtime.WeaponRuntimeTests.rejects

    def setUp(self):
        spec=json.loads((ROOT/'tests/reference/original-path-intercept.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_axioms(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('first_intercept_correspondence','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_original_bytes_and_instruction_contract(self):
        # Shift count, multiply, SHRD count, fraction mask, store slot, comparison.
        for offset in [8,22,26,39,46,60]:
            raw={k:bytearray(v) for k,v in self.raw.items()};raw['intercept'][offset]^=1
            with self.subTest(offset=offset):self.rejects(proof.certificate(raw))
        source=self.source.replace('namespace Doom.Verification.ExtractedPathIntercept',
            'set_option backward.isDefEq.respectTransparency true\nnamespace Doom.Verification.ExtractedPathIntercept')
        source=source.replace('theorem execution_checked','attribute [local irreducible] result\ntheorem execution_checked')
        self.succeeds(source)
        for old,new in [('[] 19','[] 18'),('⟨s,f,0x2c9d3⟩','⟨s,f,0x2c9d7⟩')]:self.rejects(source.replace(old,new))

    def test_live_contract_requires_encoding(self):
        source=HEADER+'''open OriginalPathIntercept
attribute [local irreducible] result Collision.pathFirstIntercept
example (s : X86Memory.State) (p : Collision.PathStart) (portion stride : Fixed)
    (h : Inputs s p portion stride) : Ready s (result s) p portion stride := live s p portion stride h
'''
        self.succeeds(source)
        self.rejects(source.replace('(h : Inputs s p portion stride)','(h : True)'))
        self.rejects(source.replace('Ready s (result s) p portion stride :=','Ready s (result s) p stride portion :='))

    def test_kernel_rounding_overflow_and_wrapping_stack(self):
        source=(ROOT/'tests/reference/original-path-intercept.lean').read_text();self.succeeds(source)
        self.rejects(source.replace('def answers : Array Word := #[32767','def answers : Array Word := #[32768'))
        self.rejects(source.replace('.core.memory 41=','.core.memory 42='))

    def test_preservation_and_separation_contracts(self):
        source=HEADER+'''open PathXStepFrame BlockSummary
attribute [local irreducible] OriginalPathXStep.result
example (s : X86Memory.State) (r : Reg) (h : r∈[1,5,6,7]) :
    (OriginalPathXStep.result s).core.regs r=s.regs r := registers s r h
example (s : X86Memory.State) (a : Word) (safe : ∀ b, b∈writes s → Apart a b) :
    load32 (OriginalPathXStep.result s).core.memory a=load32 s.memory a := frame s a safe
example (s : X86Memory.State) (off : Word) (h : off∈[12,16,20,24]) :
    load32 (OriginalPathXStep.result s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) :=
  local_preserved s off h
'''
        self.succeeds(source)
        for old,new in [('r∈[1,5,6,7]','r∈[0,5,6,7]'),
                        ('safe : ∀ b, b∈writes s → Apart a b','safe : True'),
                        ('off∈[12,16,20,24]','off∈[0,16,20,24]')]:self.rejects(source.replace(old,new))

    def test_initialization_supplies_intercept_inputs(self):
        source=(ROOT/'tests/reference/original-path-init.lean').read_text().replace(
            'import Doom.Proofs.E1M1PathInit','import Doom.Proofs.E1M1PathIntercept')
        source+='''
open PathInitFixture
example (out : Int32 × Fixed × Fixed)
    (ok : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok out) :
    OriginalPathIntercept.Inputs (OriginalPathXStep.result (OriginalPathInit.result machine).core).core
      (Collision.pathStart ox oy sx sy ex ey) out.2.1 out.2.2 :=
  E1M1PathIntercept.inputs_from_xstep _ _ _ _ _ _ _ inputs out ok
'''
        self.succeeds(source)
        self.rejects(source.replace('(ok : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok out)','(ok : True)'))

    def test_real_discharge_prefix(self):
        source=(ROOT/'tests/reference/e1m1-discharge-setters.lean').read_text().replace(
            'import Doom.Proofs.E1M1DischargeSetters','import Doom.Proofs.E1M1PathIntercept')
        source+='''
open DischargeSettersFixture
example (i : Fin 4)
    (safe : OriginalPathXStep.Safe (E1M1PathInit.firstPath (gunOf i) (machine (gunOf i) (ammoOf i))).core) :
    ∃ n, n≤287 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PathIntercept.program [] n
      ⟨machine (gunOf i) (ammoOf i),none,OriginalWeaponDischarge.afterSound (gunOf i)⟩
      (E1M1PathIntercept.firstIntercept (gunOf i) (machine (gunOf i) (ammoOf i))) :=
  E1M1PathIntercept.first_intercept_execution _ _ _ _ (inputs i) safe
'''
        self.succeeds(source)
        self.rejects(source.replace('n≤287','n≤286'))
        self.rejects(source.replace('OriginalWeaponDischarge.afterSound (gunOf i)⟩','0x2c9d3⟩'))

    def test_joined_observation_requires_geometry_and_live_success(self):
        source=HEADER+'''attribute [local irreducible] E1M1PathIntercept.firstIntercept Collision.PathStart.xStep
example (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (out : Int32 × Fixed × Fixed) (ok : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok out) :
    ∃ n, n≤287 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PathIntercept.program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (E1M1PathIntercept.firstIntercept gun s) ∧
    OriginalPathIntercept.Ready (E1M1PathXStep.firstXStep gun s).core (E1M1PathIntercept.firstIntercept gun s)
      (Collision.pathStart ox oy sx sy ex ey) out.2.1 out.2.2 :=
  E1M1PathIntercept.first_intercept_correspondence gun s f c h ox oy sx sy ex ey geometry out ok
'''
        self.succeeds(source)
        self.rejects(source.replace('(geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)', '(geometry : True)'))
        self.rejects(source.replace('(ok : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok out)', '(ok : True)'))

if __name__=='__main__':unittest.main()

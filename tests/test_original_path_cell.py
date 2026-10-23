"""Real original cell gates, signed map bounds and first firing composition."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_path_cell as proof
HEADER='''import Doom.Proofs.E1M1PathCell
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''

class PathCellTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    rejects=runtime.WeaponRuntimeTests.rejects

    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-path-cell.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('first_bounds_execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_execution_contracts(self):
        for name,offset in [('dispatch',4),('dispatch',8),('dispatch',37),('lineEntry',9),('lineEntry',27),('lineReturn',9)]:
            raw={k:bytearray(v) for k,v in self.raw.items()};raw[name][offset]^=1
            with self.subTest(name=name,offset=offset):self.rejects(proof.certificate(raw))
        for old,new in [('n≤6','n≤5'),('n≤16','n≤15'),('⟨s,f,0x2c520⟩','⟨s,f,0x2c521⟩')]:
            self.rejects(self.source.replace(old,new))

    def test_boundary_ordering_and_wrapping_fixtures(self):
        source=(ROOT/'tests/reference/original-path-cell.lean').read_text();self.succeeds(source)
        for old,new in [('(dispatch 3 0)).pc=0x2c520','(dispatch 3 0)).pc=0x2c5a0'),
                        ('(dispatch 3 0)).pc=0x2cb0b','(dispatch 3 0)).pc=0x2c5a0'),
                        ('(bounds 17 10 17 11)).pc=0x2ca94','(bounds 17 10 17 11)).pc=0x2c541'),
                        ('(bounds (-1) 0 17 11 1)).core.regs 4=(5#32)','(bounds (-1) 0 17 11 1)).core.regs 4=(4#32)')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_live_bounds_need_representation_and_nonnegative_dimension(self):
        source=HEADER+'''open OriginalLineBounds
attribute [local irreducible] entry Inside Collision.pathCellInside
example (s : X86Memory.State) (x y : Int32) (w h : Nat) (encoding : Inputs s x y w h) :
    Inside (entry s) ↔ Collision.pathCellInside x y w h=true := live_bounds s x y w h encoding
example (n : Nat) (bounded : n<2147483648) :
    (BitVec.ofNat 32 n).toInt=(n : Int) := dimension_int n bounded
'''
        self.succeeds(source)
        self.rejects(source.replace('(encoding : Inputs s x y w h)','(encoding : True)'))
        self.rejects(source.replace('n<2147483648','n<4294967296'))

    def test_return_and_frame_requirements(self):
        source=HEADER+'''open OriginalLineBounds
attribute [local irreducible] entry result
example (s : X86Memory.State) (a : Word)
    (saved : Apart a (s.regs 4-4)) (local_ : Apart a (s.regs 4-8)) :
    load32 (entry s).memory a=load32 s.memory a := entry_frame s a saved local_
example (s : X86Memory.State) (outside : ¬Inside (entry s)) :
    (result s).core.regs 0=1 ∧ (result s).core.regs 4=s.regs 4+4 ∧
    (result s).pc=(load32 s.memory (s.regs 4)).toNat := outside_return s outside
'''
        self.succeeds(source)
        for old,new in [('saved : Apart a (s.regs 4-4)','saved : True'),
                        ('local_ : Apart a (s.regs 4-8)','local_ : True'),
                        ('outside : ¬Inside (entry s)','outside : True')]:self.rejects(source.replace(old,new))

    def test_firing_join_carries_flags_from_caller(self):
        source=HEADER+'''open E1M1PathCell
attribute [local irreducible] firstBounds firstCall OriginalPathCell.enabled
example (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤360 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstBounds gun s) ∧
    (firstCall gun s).core.regs 0=(Collision.pathStart ox oy sx sy ex ey).startBlockX.toBitVec ∧
    (firstCall gun s).core.regs 2=(Collision.pathStart ox oy sx sy ex ey).startBlockY.toBitVec :=
  first_bounds_execution gun s f c h ox oy sx sy ex ey geometry layout xout yout okX okY
'''
        self.succeeds(source)
        for old,new in [('n≤360','n≤359'),('layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core','layout : True'),
                        ('okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout','okY : True')]:
            self.rejects(source.replace(old,new))

    def test_original_mapping_and_relocation_checks(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec,allowed_objects=(1,3)),self.raw)
        variants=[]
        for name in self.spec['units']:
            bad=copy.deepcopy(self.spec);bad['units'][name]['file_offset']='0x0';variants.append(bad)
        bad=copy.deepcopy(self.spec);bad['units']['dispatch']['relocations'][0]['object']=3;variants.append(bad)
        bad=copy.deepcopy(self.spec);bad['units']['lineEntry']['relocations']=[];variants.append(bad)
        for bad in variants:
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,bad,allowed_objects=(1,3))
        with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,self.spec,allowed_objects=(3,))
if __name__=='__main__':unittest.main()

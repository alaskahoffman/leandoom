"""BLOCKMAP signed loads, line-list item control, and the original firing join."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_cell as proof
HEADER='''import Doom.Proofs.E1M1LineCell
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''
class LineCellTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    def rejects(self, source):
        result=self.lean(source)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('error:',result.stdout)
        for failure in ['maximum','timeout','object file','unknown module prefix']:
            self.assertNotIn(failure,result.stdout.lower())

    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-line-cell.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('first_cell_execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_byte_and_execution_contract_mutations(self):
        for offset in [13,14,19,29,44,53,58,69]:
            raw={'cell':bytearray(self.raw['cell'])};raw['cell'][offset]^=1
            with self.subTest(offset=offset):self.rejects(proof.certificate(raw))
        for old,new in [('[] 8','[] 7'),('n≤11','n≤10'),('n≤19','n≤18'),('⟨s,f,0x2c541⟩','⟨s,f,0x2c544⟩')]:
            self.rejects(self.source.replace(old,new))

    def test_signed_decoder_leading_zero_order_and_stamp_alias(self):
        source=(ROOT/'tests/reference/original-line-cell.lean').read_text();self.succeeds(source)
        for old,new in [('(0x601000#32)','(0x6011b2#32)'),('(0x6008ca#32)','(0x6008cc#32)'),
                        ('callback aliasState none).pc=0x2c600','callback aliasState none).pc=0x2c5f0'),
                        ('(0xffff8000#32)','(0x00008000#32)')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_live_lookup_encoding_and_signed_offset_bound(self):
        source=HEADER+'''open OriginalLineCell
attribute [local irreducible] lookup
example (s : X86Memory.State) (x y : Int32) (w off : Nat) (table lists : Word)
    (h : Inputs s x y w off table lists) :
    (lookup s).core.regs 2=lists+BitVec.ofNat 32 (off*2) := live_lookup s x y w off table lists h
example (n : Nat) (bound : n<32768) :
    (BitVec.ofNat 16 n).signExtend 32=BitVec.ofNat 32 n := short_nonnegative n bound
'''
        self.succeeds(source)
        self.rejects(source.replace('(h : Inputs s x y w off table lists)','(h : True)'))
        self.rejects(source.replace('n<32768','n<65536'))

    def test_callback_frame_requires_separation(self):
        source=HEADER+'''open OriginalLineCell
attribute [local irreducible] callback
example (s : X86Memory.State) (f : Option Flags)
    (targetSafe : Apart (s.regs 4) (s.regs 0+(54#32)))
    (markSafe : Apart (s.regs 0+(54#32)) (s.regs 4-(4#32))) :
    (callback s f).core.regs 0=s.regs 0 ∧
    (callback s f).core.regs 2=s.regs 2 ∧
    (callback s f).core.regs 4=s.regs 4-(4#32) ∧
    load32 (callback s f).core.memory (s.regs 4-(4#32))=0x2c578 ∧
    load32 (callback s f).core.memory (s.regs 0+(54#32))=s.regs 7 ∧
    (callback s f).pc=(load32 s.memory (s.regs 4)).toNat := callback_observe s f targetSafe markSafe
'''
        self.succeeds(source)
        for old in ['Apart (s.regs 4) (s.regs 0+(54#32))','Apart (s.regs 0+(54#32)) (s.regs 4-(4#32))']:
            self.rejects(source.replace(old,'True'))

    def test_map_data_and_coordinates_are_transported_from_bounds(self):
        source=HEADER+'''open E1M1LineCell
attribute [local irreducible] OriginalLineBounds.result
example (s : X86Memory.State) (x y : Int32) (w h off : Nat) (table lists : Word)
    (bounds : OriginalLineBounds.Inputs s x y w h)
    (inside : Collision.pathCellInside x y w h=true)
    (map : MapData s x y w off table lists) :
    OriginalLineCell.Inputs (OriginalLineBounds.result s).core x y w off table lists :=
  bounds_to_lookup s x y w h off table lists bounds inside map
'''
        self.succeeds(source)
        for old in ['OriginalLineBounds.Inputs s x y w h','Collision.pathCellInside x y w h=true','MapData s x y w off table lists']:
            self.rejects(source.replace(old,'True',1))

    def test_actual_firing_join(self):
        source=HEADER+'''open E1M1LineCell
attribute [local irreducible] firstCell
example (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤379 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstCell gun s) :=
  first_cell_execution gun s f c h ox oy sx sy ex ey geometry layout xout yout okX okY
'''
        self.succeeds(source)
        for old,new in [('n≤379','n≤378'),('layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core','layout : True'),
                        ('okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout','okY : True')]:
            self.rejects(source.replace(old,new))

    def test_original_mapping_and_relocation_checks(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec,allowed_objects=(3,)),self.raw)
        variants=[]
        bad=copy.deepcopy(self.spec);bad['units']['cell']['file_offset']='0x0';variants.append(bad)
        bad=copy.deepcopy(self.spec);bad['units']['cell']['relocations'][0]['object']=1;variants.append(bad)
        bad=copy.deepcopy(self.spec);bad['units']['cell']['relocations']=[];variants.append(bad)
        for bad in variants:
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,bad,allowed_objects=(3,))
if __name__=='__main__':unittest.main()

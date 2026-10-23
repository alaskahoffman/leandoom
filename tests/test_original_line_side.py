"""Complete linedef side helper, real callback transport, and firing join."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_side as proof
HEADER='''import Doom.Proofs.E1M1LineSide
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''
class LineSideTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    def rejects(self, source):
        result=self.lean(source)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('error:',result.stdout)
        for failure in ['maximum','timeout','object file','unknown module prefix']:
            self.assertNotIn(failure,result.stdout.lower())

    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-line-side.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('first_side_execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_execution_contract_mutations(self):
        for offset in [0,10,23,26,69,112,127,141,144,162]:
            raw={'side':bytearray(self.raw['side'])};raw['side'][offset]^=1
            with self.subTest(offset=offset):self.rejects(proof.certificate(raw))
        for old,new in [('n≤34','n≤33'),('⟨s,f,0x2c010⟩','⟨s,f,0x2c014⟩')]:
            self.rejects(self.source.replace(old,new))

    def test_axes_ties_truncation_and_real_return(self):
        source=(ROOT/'tests/reference/original-line-side.lean').read_text();self.succeeds(source)
        for old,new in [('answer 0 65536 0 0=(1#32)','answer 0 65536 0 0=(0#32)'),
                        ('answer 65536 65536 65536 65536=(1#32)','answer 65536 65536 65536 65536=(0#32)'),
                        ('some (.setGreater 7,3)','some (.setGreater 3,3)'),
                        ('(0x600104#32)','(0x600100#32)'),('(77#32)','(0#32)')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new,1))

    def test_live_result_requires_input_representation(self):
        source=HEADER+'''open OriginalLineSide
attribute [local irreducible] result
example (s : X86Memory.State) (line : Collision.Line) (x y : Fixed)
    (p v : Word) (h : Inputs s line x y p v) :
    (result s).core.regs 0=bit (line.pointSide x y) := live s line x y p v h
'''
        self.succeeds(source);self.rejects(source.replace('h : Inputs s line x y p v','h : True'))

    def test_memory_frame_requires_separation(self):
        source=HEADER+'''open OriginalLineSide
attribute [local irreducible] result
example (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16], Apart a (s.regs 4-off)) :
    load32 (result s).core.memory a=load32 s.memory a := frame s a safe
'''
        self.succeeds(source);self.rejects(source.replace('Apart a (s.regs 4-off)','True'))

    def test_caller_transports_input_data_and_gets_side_at_return(self):
        source=HEADER+'''open E1M1LineSide
attribute [local irreducible] continueSide OriginalLineInterceptEntry.first
example (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v)
    (short : trace.usesDivlineTest=false) (data : LineData s line p v) :
    OriginalLineSide.Inputs (OriginalLineInterceptEntry.first s).core line trace.x trace.y p v :=
  entry_inputs s trace line p v h short data
example (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v)
    (short : trace.usesDivlineTest=false) (data : LineData s line p v) :
    let t := continueSide (OriginalLineInterceptEntry.first s)
    t.core.regs 0=OriginalLineSide.bit (line.pointSide trace.x trace.y) ∧ t.pc=0x2c65f :=
  short_result s trace line p v h short data
'''
        self.succeeds(source)
        for old in ['OriginalLineInterceptEntry.Inputs s trace line p v','trace.usesDivlineTest=false','LineData s line p v']:
            self.rejects(source.replace(old,'True'))
        self.rejects(source.replace('t.pc=0x2c65f','t.pc=0x2c637'))

    def test_actual_firing_join(self):
        source=HEADER+'''open E1M1LineSide
attribute [local irreducible] firstSide
example (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤435 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstSide gun s) :=
  first_side_execution gun s f c h ox oy sx sy ex ey geometry layout xout yout okX okY
'''
        self.succeeds(source)
        for old,new in [('n≤435','n≤434'),('layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core','layout : True'),
                        ('okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout','okY : True')]:
            self.rejects(source.replace(old,new))

    def test_original_mapping_and_relocation_checks(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec,allowed_objects=(3,)),self.raw)
        variants=[]
        bad=copy.deepcopy(self.spec);bad['units']['side']['file_offset']='0x0';variants.append(bad)
        bad=copy.deepcopy(self.spec);bad['units']['side']['relocations']=[{'offset':0,'object':1,'target':'0x0'}];variants.append(bad)
        bad=copy.deepcopy(self.spec);bad['units']['side']['hex']='00'+bad['units']['side']['hex'][2:];variants.append(bad)
        for bad in variants:
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,bad,allowed_objects=(3,))
if __name__=='__main__':unittest.main()

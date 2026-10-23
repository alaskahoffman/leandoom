"""Real second-side calls, same-side callback return, production and firing join."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_second_point as proof
HEADER='''import Doom.Proofs.E1M1LineSecondPoint
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''
class LineSecondPointTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    def rejects(self, source):
        result=self.lean(source)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('error:',result.stdout)
        for failure in ['maximum','timeout','object file','unknown module prefix']:
            self.assertNotIn(failure,result.stdout.lower())

    def setUp(self):
        self.spec,self.profile,self.raw=proof.extracted()
        self.source=proof.certificate(self.raw)

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('callback_rejection','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_execution_contract_mutations(self):
        for name,offset in [('wide',0),('wide',5),('wide',16),('wide',20),('short',2),('short',32),('short',36),('short',40),('short',45),('return',0),('return',8),('line',141),('divline',129)]:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[name]);code[offset]^=1;raw[name]=code
            with self.subTest(name=name,offset=offset):self.rejects(proof.certificate(raw))
        for old,new in [('n≤62','n≤61'),('⟨s,f,startPc wide⟩','⟨s,f,0x2c683⟩')]:
            self.rejects(self.source.replace(old,new))

    def test_both_branches_and_saved_caller_frame(self):
        source=(ROOT/'tests/reference/original-line-second-point.lean').read_text();self.succeeds(source)
        for old,new in [('(result false (fixture false true)).pc=0x4f000','(result false (fixture false true)).pc=0x2c691'),
                        ('(result true (fixture true false)).pc=0x2c691','(result true (fixture true false)).pc=0x4f000'),
                        ('(0x600128#32)','(0x600100#32)'),('(555#32)','(0#32)'),
                        ('(0x12345678#32)','(0#32)')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new,1))

    def test_production_rejection_requires_both_sides_equal(self):
        source=HEADER+'''open OriginalLineSecondPoint
attribute [local irreducible] result load32 Collision.lineIntercept
example (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : Inputs s trace line p v w) (same : firstSide trace line=lastSide trace line) :
    (result trace.usesDivlineTest s).core.regs 0=(1#32) ∧
    (result trace.usesDivlineTest s).pc=(load32 s.memory (s.regs 4+36)).toNat ∧
    Collision.lineIntercept trace line=.ok none := rejection s trace line p v w h same
'''
        self.succeeds(source)
        for old in ['Inputs s trace line p v w','firstSide trace line=lastSide trace line']:
            self.rejects(source.replace(old,'True'))
        self.rejects(source.replace('s.regs 4+36','s.regs 4+32'))

    def test_memory_frame_requires_separation(self):
        source=HEADER+'''open OriginalLineSecondPoint
attribute [local irreducible] result
example (wide : Bool) (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)) :
    load32 (result wide s).core.memory a=load32 s.memory a := frame wide s a safe
'''
        self.succeeds(source);self.rejects(source.replace('Apart a (s.regs 4-off)','True'))

    def test_callback_input_transport_and_real_return(self):
        source=HEADER+'''open E1M1LineSecondPoint
attribute [local irreducible] continueTest firstReturn
example (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v) (data : LineData s line p v w) :
    OriginalLineSecondPoint.Inputs (firstReturn s).core trace line p v w := entry_inputs s trace line p v w h data
example (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : OriginalLineInterceptEntry.Inputs s trace line p v) (data : LineData s line p v w)
    (same : OriginalLineSecondPoint.firstSide trace line=OriginalLineSecondPoint.lastSide trace line) :
    (continueTest (firstReturn s)).core.regs 0=(1#32) ∧
    (continueTest (firstReturn s)).pc=(load32 s.memory (s.regs 4)).toNat ∧
    Collision.lineIntercept trace line=.ok none := callback_rejection s trace line p v w h data same
'''
        self.succeeds(source)
        for old in ['OriginalLineInterceptEntry.Inputs s trace line p v','LineData s line p v w']:
            self.rejects(source.replace(old,'True'))
        self.rejects(source.replace('(load32 s.memory (s.regs 4)).toNat','0x2c691'))

    def test_actual_firing_join(self):
        source=HEADER+'''open E1M1LineSecondPoint
attribute [local irreducible] lineTest
example (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤541 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (lineTest gun s) :=
  line_test_execution gun s f c h ox oy sx sy ex ey geometry layout xout yout okX okY
'''
        self.succeeds(source)
        for old,new in [('n≤541','n≤540'),('layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core','layout : True')]:
            self.rejects(source.replace(old,new))

    def test_original_mapping_and_relocation_checks(self):
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        expected={k:self.raw[k] for k in self.spec['units']}
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),expected)
        variants=[]
        bad=copy.deepcopy(self.spec);bad['units']['wide']['file_offset']='0x0';variants.append(bad)
        bad=copy.deepcopy(self.spec);bad['units']['short']['relocations']=[];variants.append(bad)
        bad=copy.deepcopy(self.spec);bad['units']['return']['hex']='00'+bad['units']['return']['hex'][2:];variants.append(bad)
        for bad in variants:
            with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)
if __name__=='__main__':unittest.main()

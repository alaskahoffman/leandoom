"""Original fixed-point fraction, real call/return, input transport and firing join."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_intercept_vector as proof
HEADER='''import Doom.Proofs.E1M1LineFraction
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''
class InterceptVectorTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    def rejects(self,source):
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
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('crossed_live','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_byte_and_execution_contract_mutations(self):
        for name,offset in [('helper',0),('helper',15),('helper',41),('helper',43),('helper',47),('helper',89),('helper',99),('setup',4),('setup',33),('setup',38),('division',58)]:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[name]);code[offset]^=1;raw[name]=code
            with self.subTest(name=name,offset=offset):self.rejects(proof.certificate(raw))
        for old,new in [('n≤80','n≤79'),('⟨s,f,0x2c691⟩','⟨s,f,0x2c692⟩')]:self.rejects(self.source.replace(old,new))
    def test_live_equality_requires_encoding_and_success(self):
        source=HEADER+'''open OriginalInterceptVector
attribute [local irreducible] result Collision.interceptVector
example (s : X86Memory.State) (v2 v1 : Collision.Divline) (p q : Word)
    (h : Inputs s v2 v1 p q) (ok : (Collision.interceptVector v2 v1).isOk=true) :
    (Collision.interceptVector v2 v1).toOption.map (fun v => v.raw.toBitVec)=some ((result s).core.regs 0) :=
  live s v2 v1 p q h ok
'''
        self.succeeds(source)
        for old in ['Inputs s v2 v1 p q','(Collision.interceptVector v2 v1).isOk=true']:
            self.rejects(source.replace(old,'True'))
        self.rejects(source.replace('(result s).core.regs 0','(result s).core.regs 2'))
    def test_setup_derives_encoded_local_divline(self):
        source=HEADER+'''open OriginalLineFraction
attribute [local irreducible] setup
example (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line) (p v : Word)
    (h : Inputs s trace line p v) : Encoded s trace line := encoded s trace line p v h
'''
        self.succeeds(source);self.rejects(source.replace('Inputs s trace line p v','True'))
    def test_frame_requires_separation(self):
        source=HEADER+'''open OriginalInterceptVector
attribute [local irreducible] OriginalDivMemory.result num
example (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16], Apart a (s.regs 4-off)) :
    load32 (OriginalDivMemory.result (num s)).core.memory a=load32 s.memory a := inner_frame s a safe
'''
        self.succeeds(source);self.rejects(source.replace('Apart a (s.regs 4-off)','True'))
    def test_complete_helper_frame(self):
        source=HEADER+'''open OriginalInterceptVector
attribute [local irreducible] result
example (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20,24,28,32,36], Apart a (s.regs 4-off)) :
    load32 (result s).core.memory a=load32 s.memory a := frame s a safe
'''
        self.succeeds(source);self.rejects(source.replace('Apart a (s.regs 4-off)','True'))
    def test_numeric_fixtures_and_sub_flags(self):
        source=(ROOT/'tests/reference/original-intercept-vector.lean').read_text();self.succeeds(source)
        for old,new in [('regs 0=(32768#32)','regs 0=(32769#32)'),('regs 4=(4#32)','regs 4=(0#32)'),
                        ('regs 5=(555#32)','regs 5=(0#32)'),('.pc=0x4f000','.pc=0x2c6bb'),
                        (').isOk=false',').isOk=true'),('⟨false,false,true,some false⟩','⟨false,false,false,some false⟩'),
                        ('some (.subRegistersWithFlags 7 0,2)','some (.subRegistersWithFlags 0 7,2)')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new,1))
    def test_real_firing_join(self):
        source=HEADER+'''open E1M1LineFraction
attribute [local irreducible] fraction
example (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (safe : Ready (E1M1LineSecondPoint.lineTest gun s)) :
    ∃ n≤621, X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (fraction gun s) :=
  line_fraction_execution gun s f c h ox oy sx sy ex ey geometry layout xout yout okX okY safe
'''
        self.succeeds(source)
        for old,new in [('n≤621','n≤620'),('Ready (E1M1LineSecondPoint.lineTest gun s)','True')]:self.rejects(source.replace(old,new))
    def test_original_mapping_and_relocations(self):
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),{k:self.raw[k] for k in self.spec['units']})
        for name in ['helper','setup']:
            bad=copy.deepcopy(self.spec);bad['units'][name]['file_offset']='0x0'
            with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)
        bad=copy.deepcopy(self.spec);bad['units']['setup']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)
if __name__=='__main__':unittest.main()

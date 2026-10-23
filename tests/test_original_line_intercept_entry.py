"""Original line callback selection, helper-call ABI, and firing join."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_intercept_entry as proof
HEADER='''import Doom.Proofs.E1M1LineInterceptEntry
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''
class LineInterceptEntryTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    def rejects(self, source):
        result=self.lean(source)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('error:',result.stdout)
        for failure in ['maximum','timeout','object file','unknown module prefix']:
            self.assertNotIn(failure,result.stdout.lower())

    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-line-intercept-entry.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('first_point_execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_byte_and_execution_contract_mutations(self):
        for name,offset in [('entry',5),('entry',20),('entry',22),('entry',44),('entry',52),('entry',66),('short',8),('short',13)]:
            raw={k:bytearray(v) for k,v in self.raw.items()};raw[name][offset]^=1
            with self.subTest(name=name,offset=offset):self.rejects(proof.certificate(raw))
        for old,new in [('n≤22','n≤21'),('⟨s,f,0x2c5f0⟩','⟨s,f,0x2c600⟩')]:
            self.rejects(self.source.replace(old,new))

    def test_threshold_coordinates_pointer_and_return(self):
        source=(ROOT/'tests/reference/original-line-intercept-entry.lean').read_text();self.succeeds(source)
        for old,new in [('usesDivlineTest=false','usesDivlineTest=true'),('(789#32)','(123#32)'),
                        ('(0x2ba10#32)','(0x600200#32)'),('(0x2c637#32)','(0x2c65f#32)')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new,1))

    def test_live_contract_requires_representation_and_stack_separation(self):
        source=HEADER+'''open OriginalLineInterceptEntry
attribute [local irreducible] first prepared gate called
example (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (linePtr vertexPtr : Word) (h : Inputs s trace line linePtr vertexPtr) :
    Ready s (first s) trace line linePtr := live s trace line linePtr vertexPtr h
example (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)) :
    load32 (prepared s).memory a=load32 s.memory a := frame s a safe
'''
        self.succeeds(source)
        self.rejects(source.replace('(h : Inputs s trace line linePtr vertexPtr)','(h : True)'))
        self.rejects(source.replace('Apart a (s.regs 4-off)','True'))

    def test_full_frame_requires_return_word_separation(self):
        source=HEADER+'''open OriginalLineInterceptEntry
attribute [local irreducible] first
example (s : X86Memory.State) (a : Word)
    (saves : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off))
    (ret : Apart a (s.regs 4-(40#32))) :
    load32 (first s).core.memory a=load32 s.memory a := first_frame s a saves ret
'''
        self.succeeds(source)
        self.rejects(source.replace('ret : Apart a (s.regs 4-(40#32))','ret : True'))

    def test_callback_requires_actual_entry(self):
        source=HEADER+'''open E1M1LineInterceptEntry
attribute [local irreducible] continueCallback
example (s : X86Control.State) (trace : Collision.Divline) (line : Collision.Line)
    (linePtr vertexPtr : Word) (entry : s.pc=0x2c5f0)
    (h : OriginalLineInterceptEntry.Inputs s.core trace line linePtr vertexPtr) :
    OriginalLineInterceptEntry.Ready s.core (continueCallback s) trace line linePtr :=
  callback_live s trace line linePtr vertexPtr entry h
'''
        self.succeeds(source);self.rejects(source.replace('entry : s.pc=0x2c5f0','entry : True'))

    def test_actual_firing_join(self):
        source=HEADER+'''open E1M1LineInterceptEntry
attribute [local irreducible] firstPoint
example (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤401 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstPoint gun s) :=
  first_point_execution gun s f c h ox oy sx sy ex ey geometry layout xout yout okX okY
'''
        self.succeeds(source)
        for old,new in [('n≤401','n≤400'),('layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core','layout : True'),
                        ('okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout','okY : True')]:
            self.rejects(source.replace(old,new))

    def test_original_mapping_and_relocation_checks(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec,allowed_objects=(3,)),self.raw)
        variants=[]
        bad=copy.deepcopy(self.spec);bad['units']['entry']['file_offset']='0x0';variants.append(bad)
        bad=copy.deepcopy(self.spec);bad['units']['entry']['relocations'][0]['object']=1;variants.append(bad)
        bad=copy.deepcopy(self.spec);bad['units']['entry']['relocations']=[];variants.append(bad)
        for bad in variants:
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,bad,allowed_objects=(3,))
if __name__=='__main__':unittest.main()

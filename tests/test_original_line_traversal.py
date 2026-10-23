"""All callback outcomes compose; early stop requires no suffix traversal."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_traversal as proof
HEADER='''import Doom.Proofs.OriginalLineTraversal
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''
REJECT='''variable (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
  (p v w : Word) (ready : Ready s trace line p v w)
include ready
'''
STOP='''variable (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
  (frac : Fixed) (flags : Nat) (p v w : Word)
  (h : OriginalLineDispatch.Ready s trace line frac flags p v w) (stop : Stops frac flags line)
include h stop
'''
class LineTraversalTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix']:
            self.assertNotIn(bad,out.stdout.lower())

    def setUp(self):
        self.spec,self.profile,self.raw=proof.extracted()
        self.source=proof.certificate(self.raw)

    def declaration(self,module,name,args,context=''):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        decl=text[text.index('theorem '+name):].split(' :=',1)[0]
        return HEADER+'open '+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self,source,pairs):
        self.succeeds(source)
        for old,new in pairs:
            self.assertIn(old,source)
            with self.subTest(old=old):self.rejects(source.replace(old,new))

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('parent_return','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_extracted_bytes_and_execution_contract(self):
        for key in ['cell','entry','secondShort','secondReturn','lineSide','divlineSide','finish','lineReturn']:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[key]);code[-1]^=1;raw[key]=code
            with self.subTest(key=key):self.rejects(proof.certificate(raw))
        self.mutations(self.source,[('steps≤281*n+7','steps≤281*n+6'),('OriginalLineTraversal.Runs s out n','True')])

    def test_rejection_continues_without_an_intercept(self):
        self.mutations(self.declaration('OriginalLineReject','continued','s trace line p v w ready',REJECT),
            [('s.regs 2+(2#32)','s.regs 2+(4#32)'),('Collision.lineIntercept trace line=.ok none','Collision.lineIntercept trace line=.ok (some ⟨0⟩)')])
        self.mutations(self.declaration('OriginalLineReject','frame','s trace line p v w ready a dispatch safe',REJECT),
            [('OriginalLineDispatch.Safe s a','True'),('OriginalLineCrossing.SideSafe (OriginalLineDispatch.view s) a','True')])

    def test_early_stop_and_parent_return_require_their_contracts(self):
        args='s trace line frac flags p v w h stop'
        self.mutations(self.declaration('OriginalLineStop','observed',args,STOP),
            [('Stops frac flags line','True'),('core.regs 0=(0#32)','core.regs 0=(1#32)'),('s.regs 4+(12#32)','s.regs 4+(8#32)')])
        self.mutations(self.declaration('OriginalLineStop','parent_return',args+' dispatch safe',STOP),
            [('OriginalLineDispatch.Safe s a','True'),('OriginalLineCrossing.Protected (OriginalLineDispatch.view s) a','True')])

    def test_terminal_stop_constructor_needs_no_suffix_contract(self):
        source=HEADER+'''example (s : X86Control.State) (pc : s.pc=0x2c57f)
    (trace : Collision.Divline) (line : Collision.Line) (frac : Fixed) (flags : Nat) (p v w : Word)
    (h : OriginalLineDispatch.Ready s.core trace line frac flags p v w)
    (stop : OriginalLineStop.Stops frac flags line) :
    OriginalLineTraversal.Runs s (OriginalLineDispatch.result s.core) 1 :=
  .stopped s pc trace line frac flags p v w h stop
'''
        self.mutations(source,[('s.pc=0x2c57f','True'),('OriginalLineStop.Stops frac flags line','True'),('result s.core) 1','result s.core) 2')])

    def test_combined_return_and_stack(self):
        self.mutations(self.declaration('OriginalLineTraversal','stack','s out n h'),
            [('Runs s out n','True'),('s.core.regs 4+(12#32)','s.core.regs 4+(8#32)')])
        self.mutations(self.declaration('OriginalLineTraversal','return_value','s out n h'),
            [('out.core.regs 0=(0#32) ∨ out.core.regs 0=(1#32)','out.core.regs 0=(1#32)')])

    def test_previous_mixed_traversal_embeds(self):
        self.mutations(self.declaration('OriginalLineTraversal','of_mixed','n s pc h last'),
            [('OriginalLineMixed.Admitted n s','True'),('=(0xffff#16)','=(0xfffe#16)')])

    def test_both_branch_rejection_and_stop_fixtures(self):
        source=(ROOT/'tests/reference/original-line-traversal.lean').read_text()
        self.mutations(source,[('regs 2=(0x600902#32)','regs 2=(0x600904#32)'),('=(0x600800#32)','=(0x60080c#32)'),('regs 7=(777#32)','regs 7=(0#32)')])

    def test_original_mapping_and_relocations(self):
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),self.raw)
        for key in ['cell','secondReturn','finish','lineReturn']:
            bad=copy.deepcopy(self.spec);bad['units'][key]['file_offset']='0x0'
            with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)
        bad=copy.deepcopy(self.spec);bad['units']['cell']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)

if __name__=='__main__':unittest.main()

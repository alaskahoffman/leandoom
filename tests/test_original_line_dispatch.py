"""Pre-stamp geometry, generated CALL frames and current-memory mixed traversal."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_dispatch as proof
HEADER='''import Doom.Proofs.OriginalLineMixed
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''
CONTEXT='''variable (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
  (frac : Fixed) (flags : Nat) (p v w : Word) (h : Ready s trace line frac flags p v w)
include h
'''
class LineDispatchTests(unittest.TestCase):
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

    def declaration(self,module,name,args,context=False):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        decl=text[text.index('theorem '+name):].split(' :=',1)[0]
        return HEADER+'open '+module+'\n'+(CONTEXT if context else '')+decl.replace('theorem '+name,'example',1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self,source,pairs):
        self.succeeds(source)
        for old,new in pairs:
            self.assertIn(old,source)
            with self.subTest(old=old):self.rejects(source.replace(old,new))

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('marked_seen','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_extracted_bytes_and_execution_contract(self):
        for key in ['cell','entry','firstShort','secondWide','secondShort','lineSide','divlineSide','setup','helper','division','finish','lineReturn']:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[key]);code[-1]^=1;raw[key]=code
            with self.subTest(key=key):self.rejects(proof.certificate(raw))
        self.mutations(self.source,[('n≤281','n≤280'),('⟨s,f,0x2c57f⟩','⟨s,f,0x2c580⟩'),('OriginalLineDispatch.Ready s trace line frac flags p v w','True')])

    def test_generated_return_and_dispatch_target(self):
        self.mutations(self.declaration('OriginalLineDispatch','entry_observe','s h'),
            [('Fresh s','True'),('(0x2c578#32)','(0x2c57a#32)')])
        self.mutations(self.declaration('OriginalLineDispatch','entry_frame','s a safe'),[('Safe s a','True')])

    def test_geometry_is_transported_from_pre_stamp_memory(self):
        self.mutations(self.declaration('OriginalLineDispatch','crossing_inputs','s trace line p v w h safe'),
            [('Safe s a','True'),('OriginalLineCrossing.Inputs (view s) trace line p v w','True')])

    def test_stamp_survives_callback_and_pointer_advances_once(self):
        args='s trace line frac flags p v w h'
        self.mutations(self.declaration('OriginalLineDispatch','marked_seen',args+' dispatch safe',True),
            [('Safe s a','True'),('OriginalLineCrossing.Protected (view s) a','True')])
        self.mutations(self.declaration('OriginalLineDispatch','continued',args+' saved keep',True),
            [('s.regs 2+(2#32)','s.regs 2+(4#32)'),('OriginalLineTail.RecordSafe (view s) ((view s).regs 4-(12#32))','True')])

    def test_mixed_run_keeps_dynamic_domain_and_sentinel(self):
        self.mutations(self.declaration('OriginalLineMixed','execution','n s atHeader h'),
            [('Admitted n s','True'),('steps≤281*n','steps≤280*n'),('s.pc=0x2c57f','True')])
        self.mutations(self.declaration('OriginalLineMixed','through_sentinel','n s atHeader h last'),
            [('=(0xffff#16)','=(0xfffe#16)'),('steps≤281*n+7','steps≤281*n+6')])

    def test_fresh_line_zero_then_duplicate_and_sentinel_fixture(self):
        source=(ROOT/'tests/reference/original-line-dispatch.lean').read_text()
        self.mutations(source,[('=(0x60080c#32)','=(0x600818#32)'),('regs 2=(0x600904#32)','regs 2=(0x600906#32)'),('=(99#32)','=(98#32)')])

    def test_original_mapping_and_relocations(self):
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),self.raw)
        for key in ['cell','entry','lineSide','finish']:
            bad=copy.deepcopy(self.spec);bad['units'][key]['file_offset']='0x0'
            with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)
        bad=copy.deepcopy(self.spec);bad['units']['cell']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)

if __name__=='__main__':unittest.main()

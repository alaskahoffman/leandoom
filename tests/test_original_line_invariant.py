"""One initial list contract derives every rejection/duplicate iteration."""
import copy
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_invariant as proof
HEADER='''import Doom.Proofs.OriginalLineInvariant
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary OriginalLineInvariant
'''

class LineInvariantTests(unittest.TestCase):
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

    def declaration(self,name,args):
        text=(ROOT/'Doom/Proofs/OriginalLineInvariant.lean').read_text()
        decl=text[text.index('theorem '+name):].split(' :=',1)[0]
        return HEADER+decl.replace('theorem '+name,'example',1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self,source,pairs):
        self.succeeds(source)
        for old,new in pairs:
            self.assertIn(old,source)
            with self.subTest(old=old):self.rejects(source.replace(old,new))

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('parent_return','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_initial_execution_contract(self):
        for key in ['cell','entry','secondReturn','lineReturn']:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[key]);code[-1]^=1;raw[key]=code
            with self.subTest(key=key):self.rejects(proof.certificate(raw))
        self.mutations(self.source,[('steps≤178*n+7','steps≤178*n+6'),('Initial s n','Initial s (n+1)')])

    def test_geometry_transport_keeps_memory_argument_and_stack(self):
        self.mutations(self.declaration('reject_inputs','s t trace line p v w h arg sp memory'),[
            ('t.regs 0=s.regs 0','True'),('t.regs 4=s.regs 4','True'),
            ('load32 t.memory a=load32 s.memory a','True')])

    def test_fresh_readiness_is_derived_only_within_the_initial_list(self):
        self.mutations(self.declaration('ready','initial n h i s inv hi unseen'),[
            ('(inv : Stable initial h i s)','(inv : True)'),('(hi : i<n)','(hi : i≤n)'),
            ('¬OriginalLineCell.already (OriginalLineCell.header s.core).core','True')])

    def test_advance_and_walk_preserve_the_exact_cursor_index(self):
        self.mutations(self.declaration('advance','initial n h i s inv hi'),[
            ('Stable initial h (i+1)','Stable initial h (i+2)'),('(hi : i<n)','(hi : i≤n)')])
        self.mutations(self.declaration('walk','initial n h k i s inv hi'),[
            ('Stable initial h (i+k)','Stable initial h i'),('(hi : i+k≤n)','(hi : True)')])

    def test_parent_return_and_word_protection_are_not_assumed(self):
        self.mutations(self.declaration('parent_return','s n h f saved ret'),[
            ('s.regs 4+(4#32)∈h.words','True'),('s.regs 4+(8#32)∈h.words','True'),
            ('core.regs 0=(1#32)','core.regs 0=(0#32)')])
        self.mutations(self.declaration('frame','s n h f a ha'),[('(ha : a∈h.words)','(ha : True)')])

    def test_initial_contract_fixture_in_both_geometry_branches(self):
        source=(ROOT/'tests/reference/original-line-invariant.lean').read_text()
        self.mutations(source,[('regs 2=(0x600904#32)','regs 2=(0x600906#32)'),(').pc=0x4f000',').pc=0x4f004')])

    def test_original_mapping_and_relocations(self):
        import json
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),self.raw)
        bad=copy.deepcopy(self.spec);bad['units']['cell']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)

if __name__=='__main__':unittest.main()

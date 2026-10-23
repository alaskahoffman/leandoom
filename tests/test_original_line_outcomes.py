"""All original line-callback outcomes close under an initial prefix invariant."""
import copy
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_outcomes as proof
HEADER='''import Doom.Proofs.OriginalLineScan
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineCollection (Tracks Layout)
open OriginalLineMixedInvariant OriginalLineScan
'''
CONTEXT='''variable (initial : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word)
  (h : Initial initial n base resolve) (i : Nat) (s : X86Control.State) (r : Collision.PathResult)
'''
STABLE='''variable (inv : Stable initial h i s r)
include inv
'''
NOINSERT='''open OriginalLineNoInsert
variable (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
  (frac : Fixed) (flags : Nat) (p v w : Word)
  (h : OriginalLineDispatch.Ready s trace line frac flags p v w)
  (no : NoInsert frac flags line)
include h no
'''
ARGS='initial n base resolve h i s r inv'
NOARGS='s trace line frac flags p v w h no'

class LineScanTests(unittest.TestCase):
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

    def declaration(self,module,name,args,context=CONTEXT+STABLE):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        decl=re.split(r' :=(?: by|\n)',text[text.index('theorem '+name):],maxsplit=1)[0]
        return HEADER+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\n'

    def mutations(self,source,pairs):
        self.succeeds(source)
        for old,new in pairs:
            self.assertIn(old,source)
            with self.subTest(old=old):self.rejects(source.replace(old,new))

    def test_certificate_and_complete_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('stopped_step','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        names=[]
        for module in ['OriginalLineNoInsert','OriginalLineMixedInvariant','OriginalLineScan']:
            text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
            names += [module+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
        self.assertEqual(proof.PROOFS,names)

    def test_bytes_and_completed_execution_contract(self):
        for key in ['cell','finish','division']:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[key]);code[-1]^=1;raw[key]=code
            with self.subTest(key=key):self.rejects(proof.certificate(raw))
        self.mutations(self.source,[('steps≤281*n+7','steps≤281*n+6'),
            ('load16 initial.memory (address initial n)=(0xffff#16)','True')])

    def test_no_insert_requires_the_actual_branch(self):
        self.mutations(self.declaration('OriginalLineNoInsert','disabled',NOARGS,NOINSERT),[
            ('(no : NoInsert frac flags line)','(no : True)')])
        self.mutations(self.declaration('OriginalLineNoInsert','negative_live','s trace line frac flags p v w h neg',NOINSERT.replace('include h no','include h')), [
            ('(neg : frac.raw<0)','(neg : True)')])

    def test_no_insert_preserves_records_but_still_needs_scratch_separation(self):
        self.mutations(self.declaration('OriginalLineNoInsert','frame',NOARGS+' a dispatch side scratch',NOINSERT),[
            ('(dispatch : OriginalLineDispatch.Safe s a)','(dispatch : True)'),
            ('(scratch : OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view s) a)','(scratch : True)')])
        self.mutations(self.declaration('OriginalLineNoInsert','collection',NOARGS+' base resolve hits reserve tracked layout',NOINSERT),[
            ('(layout : Layout s base)','(layout : True)'),
            ('base resolve hits reserve :=','base resolve hits (reserve+2) :=')])

    def test_terminal_transition_needs_unseen_crossing_and_stop(self):
        self.mutations(self.declaration('OriginalLineScan','stopped_step',ARGS+' hi halt'),[
            ('(halt : Halts (h.candidates i) s.core)','(halt : True)'),
            ('Terminal initial h (i+1)','Terminal initial h i')])

    def test_full_scan_derives_all_reached_conditions(self):
        self.mutations(self.declaration('OriginalLineScan','scan_correct',ARGS+' k hi'),[
            ('(inv : Stable initial h i s r)','(inv : True)'),
            ('(hi : i+k≤n)','(hi : True)'),
            ('out.visits≤k','out.visits<k')])
        self.mutations(self.declaration('OriginalLineScan','through_scan','initial n base resolve h r f collected sentinel',CONTEXT),[
            ('r.collected n)','r.collected 0)'),
            ('(n-out.visits)','(n+out.visits)')])

    def test_stopping_prefix_has_no_sentinel_or_suffix_requirement(self):
        source=self.declaration('OriginalLineScan','stopping_prefix','initial n base resolve h r f collected halt',CONTEXT)
        self.assertNotIn('sentinel',source)
        self.mutations(source,[
            ('(scan h.candidates n 0 ⟨initial,f,0x2c57f⟩ r).stopped=true','True')])
        self.mutations(self.declaration('OriginalLineScan','stopped_parent','initial n base resolve h out path visits term saved ret',CONTEXT),[
            ('(ret : initial.regs 4+(8#32)∈h.words)','(ret : True)')])

    def test_negative_and_both_stop_branches_with_nonempty_collection(self):
        source=(ROOT/'tests/reference/original-line-outcomes.lean').read_text()
        self.mutations(source,[
            ('(out .negative).path.collected.size=1','(out .negative).path.collected.size=2'),
            ('(out .wideStop).machine.core.regs 0=(0#32)','(out .wideStop).machine.core.regs 0=(1#32)'),
            ('=(0x70080c#32)','=(0x700818#32)')])

    def test_original_mapping_and_relocations(self):
        import json
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),self.raw)
        bad=copy.deepcopy(self.spec);bad['units']['finish']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)

if __name__=='__main__':unittest.main()

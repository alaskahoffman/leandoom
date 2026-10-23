"""Initial-memory closure of a bounded append/duplicate/rejection scan."""
import copy
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_mixed_invariant as proof
HEADER='''import Doom.Proofs.OriginalLineMixedInvariant
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineCollection (Tracks)
open OriginalLineMixedInvariant
'''
CONTEXT='''variable (initial : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word)
  (h : Initial initial n base resolve) (i : Nat) (s : X86Control.State) (r : Collision.PathResult)
'''
STABLE='''variable (inv : Stable initial h i s r)
include inv
'''
ARGS='initial n base resolve h i s r inv'

class LineMixedInvariantTests(unittest.TestCase):
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

    def declaration(self,name,args,context=CONTEXT+STABLE):
        text=(ROOT/'Doom/Proofs/OriginalLineMixedInvariant.lean').read_text()
        decl=re.split(r' :=(?: by|\n)',text[text.index('theorem '+name):],maxsplit=1)[0]
        return HEADER+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self,source,pairs):
        self.succeeds(source)
        for old,new in pairs:
            self.assertIn(old,source)
            with self.subTest(old=old):self.rejects(source.replace(old,new))

    def test_certificate_and_complete_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('through_sentinel','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        text=(ROOT/'Doom/Proofs/OriginalLineMixedInvariant.lean').read_text()
        names=['OriginalLineMixedInvariant.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
        self.assertEqual(proof.PROOFS,names)

    def test_bytes_and_complete_scan_execution_contract(self):
        for key in ['cell','entry','finish','setup']:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[key]);code[-1]^=1;raw[key]=code
            with self.subTest(key=key):self.rejects(proof.certificate(raw))
        self.mutations(self.source,[('steps≤281*n+7','steps≤281*n+6'),
            ('(h : Initial initial n base resolve)','(h : True)'),
            ('r.collected n)','r.collected 0)')])

    def test_crossing_transport_requires_memory_argument_and_stack(self):
        self.mutations(self.declaration('crossing_inputs','s t trace line p v w h arg sp memory',''),[
            ('(arg : t.regs 0=s.regs 0)','(arg : True)'),
            ('(sp : t.regs 4=s.regs 4)','(sp : True)'),
            ('load32 t.memory a=load32 s.memory a','True')])

    def test_readiness_is_derived_but_needs_invariant_and_outcome(self):
        self.mutations(self.declaration('crossing_ready',ARGS+' hi unseen append'),[
            ('(inv : Stable initial h i s r)','(inv : True)'),
            ('(hi : i<n)','(hi : True)'),
            ('(append : (h.candidates i).crosses=true)','(append : True)')])
        self.mutations(self.declaration('reject_ready',ARGS+' hi unseen reject'),[
            ('(reject : (h.candidates i).crosses=false)','(reject : True)'),
            ('(unseen : ¬OriginalLineCell.already (OriginalLineCell.header s.core).core)','(unseen : True)')])

    def test_storage_and_record_separation_come_from_initial_contract(self):
        self.mutations(self.declaration('storage',ARGS+' hi'),[
            ('(inv : Stable initial h i s r)','(inv : True)')])
        self.mutations(self.declaration('record_safe',ARGS+' hi a safe'),[
            ('(hi : i<n)','(hi : i≤n)'),
            ('(safe : ArraySafe base a)','(safe : True)')])

    def test_every_branch_reestablishes_invariant_and_exact_index(self):
        self.mutations(self.declaration('advance',ARGS+' hi keep'),[
            ('Stable initial h (i+1) next.1 next.2','Stable initial h i next.1 next.2'),
            ('steps≤281','steps≤280')])
        self.mutations(self.declaration('walk',ARGS+' k hi keep'),[
            ('(hi : i+k≤n)','(hi : True)'),
            ('Stable initial h (i+k) final.1 final.2','Stable initial h i final.1 final.2')])

    def test_sentinel_collection_and_parent_return(self):
        self.mutations(self.declaration('through_sentinel','initial n base resolve h r f collected keep sentinel',CONTEXT),[
            ('r.collected n)','r.collected 0)'),
            ('out.2.collected 0','r.collected 0')])
        self.mutations(self.declaration('parent_return','initial n base resolve h r f collected keep saved ret',CONTEXT),[
            ('(ret : initial.regs 4+(8#32)∈h.words)','(ret : True)'),
            ('out.core.regs 4=initial.regs 4+(12#32)','out.core.regs 4=initial.regs 4+(8#32)')])

    def test_nonempty_append_duplicate_fresh_rejection_both_branches(self):
        source=(ROOT/'tests/reference/original-line-mixed-invariant.lean').read_text()
        self.mutations(source,[('collected.size=2','collected.size=3'),
            ('collected[1]!.id=0','collected[1]!.id=17'),
            ('=(0x700818#32)','=(0x70080c#32)')])

    def test_original_mapping_and_relocations(self):
        import json
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),self.raw)
        bad=copy.deepcopy(self.spec);bad['units']['finish']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)

if __name__=='__main__':unittest.main()

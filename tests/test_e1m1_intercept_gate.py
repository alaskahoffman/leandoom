"""Keep the original cutoff, callback argument and stop/continue contracts honest."""
import re
import unittest
from pathlib import Path
import test_e1m1_minimum_scan as prior
import verify_e1m1_intercept_gate as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1InterceptGate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1InterceptMinimum (Best minimum selectFrom update)
open E1M1MinimumScan (address Represents Fractions)
open OriginalInterceptGate (gate called saved resumed resumeSteps)
attribute [local irreducible] load32 store32
'''
class InterceptGateTests(unittest.TestCase):
    lean=prior.MinimumScanTests.lean
    succeeds=prior.MinimumScanTests.succeeds
    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout+out.stderr)
        diagnostic=(out.stdout+out.stderr).lower()
        for bad in ['unknown identifier','unknown constant','maximum recursion','maximum heartbeats','timeout']:
            self.assertNotIn(bad,diagnostic)
        self.assertRegex(diagnostic,r'type mismatch|unsolved goals|tactic.*failed|tactic.*proved that the proposition|failed to synthesize')
    mutations=prior.MinimumScanTests.mutations

    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_bytes_and_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),31)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out+'extra',out.replace('InterceptGate.callback','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        altered=dict(raw);b=bytearray(raw['interceptGate']);b[8]=0x7d;altered['interceptGate']=bytes(b)
        self.rejects(proof.certificate(data,altered))

    def test_continuous_gate_requires_encoded_bounds_and_maximum(self):
        self.mutations(self.contract('E1M1InterceptGate','execution','s f hits bounded limit encoded maximum'),[
            ('(bounded : hits.size≤128)','(bounded : True)'),
            ('(limit : s.regs 1=address hits.size)','(limit : True)'),
            ('(encoded : Fractions s.memory hits)','(encoded : True)'),
            ('(maximum : s.regs 7=65536)','(maximum : True)'),
            ('best.1>65536','best.1≥65536'),
            ('⟨s,f,0x2c841⟩','⟨s,f,0x2c84f⟩')])

    def test_callback_requires_real_selection_and_cutoff(self):
        self.mutations(self.contract('E1M1InterceptGate','callback','s f hits best selected within state maximum'),[
            ('(selected : minimum hits=.ok best)','(selected : True)'),
            ('(within : ¬best.1>65536)','(within : True)'),
            ('(state : Represents s hits hits.size best)','(state : True)'),
            ('core.regs 0=address j','core.regs 0=address (j+1)')])

    def test_no_choice_and_in_bounds_claims_need_selection(self):
        self.mutations(self.contract('E1M1InterceptGate','no_choice','s hits distance selected state maximum'),[
            ('(selected : minimum hits=.ok (distance,none))','(selected : True)'),
            ('(gate s).pc=0x2c887','(gate s).pc=0x2c868')])
        self.mutations(self.contract('E1M1InterceptGate','admitted','hits best selected within'),[
            ('(within : ¬best.1>65536)','(within : True)'),
            ('j<hits.size','j+1<hits.size')])

    def test_original_stop_and_continue_are_not_interchangeable(self):
        self.mutations(self.contract('OriginalInterceptGate','resume_execution','s f'),[
            ('(resumed s)','(resumed (put s 0 0))'),
            ('⟨s,f,0x2c86d⟩','⟨s,f,0x2c86f⟩')])
        self.mutations(self.contract('OriginalInterceptGate','call_execution','s f'),[
            ('(called s f)','(called (put s 3 0) f)'),
            ('⟨s,f,0x2c868⟩','⟨s,f,0x2c86a⟩')])

    def test_signed_cutoff_and_resume_edges(self):
        self.succeeds(HEADER+'''
def machine (distance answer : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then answer else if r=2 then distance else if r=7 then 65536 else 0,fun _ => 0⟩
example : (gate (machine 65536 0)).pc=0x2c868 := by decide +kernel
example : (gate (machine 65537 0)).pc=0x2c887 := by decide +kernel
example : (gate (machine 0x80000000 0)).pc=0x2c868 := by decide +kernel
example : (gate (machine 0x7fffffff 0)).pc=0x2c887 := by decide +kernel
example : (resumed (machine 0 0)).pc=0x2c88c ∧ resumeSteps (machine 0 0)=4 := by decide +kernel
example : (resumed (machine 0 0x80000000)).pc=0x2c83a ∧ resumeSteps (machine 0 0x80000000)=5 := by decide +kernel
''')

    def test_resume_memory_and_call_return_address(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (h : s.regs 0=0) : (resumed s).core.memory=s.memory := by
  simp [resumed,h,OriginalInterceptGate.restored,put]
example (s : X86Memory.State) (h : s.regs 0≠0) :
    (resumed s).core.memory=store32 s.memory (s.regs 3) 0x7fffffff := by
  simp only [resumed,if_neg h]
  rfl
example (s : X86Memory.State) (f : Option Flags) :
    (called s f).core.memory=store32 s.memory (s.regs 4-4) 0x2c86d := by
  rfl
''')

if __name__=='__main__':unittest.main()

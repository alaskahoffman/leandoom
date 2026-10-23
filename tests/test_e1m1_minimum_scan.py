"""The original minimum scan must preserve strict ordering and encoded bounds."""
import re
import unittest
from pathlib import Path
import test_e1m1_query_collection as prior
import verify_e1m1_minimum_scan as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1MinimumScan
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1InterceptMinimum (Best minimum selectFrom update)
open OriginalInterceptMinimum (advanced)
open Doom.Collision
attribute [local irreducible] load32
'''

class MinimumScanTests(unittest.TestCase):
    lean=prior.QueryCollectionTests.lean
    succeeds=prior.QueryCollectionTests.succeeds
    rejects=prior.QueryCollectionTests.rejects
    mutations=prior.QueryCollectionTests.mutations

    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',s[a:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_bytes_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),30);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out+'extra',out.replace('MinimumScan.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        altered=dict(raw);b=bytearray(raw['interceptMinimum']);b[14]=0x7c;altered['interceptMinimum']=bytes(b)
        self.rejects(proof.certificate(data,altered))

    def test_live_selector_rejects_tie_and_sentinel_drift(self):
        s=(ROOT/'Doom/Proofs/E1M1InterceptMinimum.lean').read_text().split('attribute [local semireducible]')[0]
        s=s.replace('namespace Doom.Proofs.E1M1InterceptMinimum','namespace Doom.Proofs.ScratchMinimum')
        s+='\nend Doom.Proofs.ScratchMinimum\n'
        self.mutations(s,[('hits[i]!.frac.raw < best.1','hits[i]!.frac.raw ≤ best.1'),
                          ('((2147483647 : Int32),none)','((65536 : Int32),none)')])

    def test_full_scan_requires_real_limit_and_encoded_fractions(self):
        self.mutations(self.contract('E1M1MinimumScan','execution','s f hits bounded limit encoded'),[
            ('(limit : s.regs 1=address hits.size)','(limit : True)'),
            ('(encoded : Fractions s.memory hits)','(encoded : True)'),
            ('(bounded : hits.size≤128)','(bounded : True)')])

    def test_full_scan_keeps_entry_exit_and_selected_state(self):
        self.mutations(self.contract('E1M1MinimumScan','execution','s f hits bounded limit encoded'),[
            ('⟨s,f,0x2c841⟩','⟨s,f,0x2c84f⟩'),
            ('out.pc=0x2c85e','out.pc=0x2c86a'),
            ('Represents out.core hits hits.size best','Represents out.core hits 0 best'),
            ('out.core.memory=s.memory','out.core.memory=store32 s.memory 0 0')])

    def test_iteration_bridge_requires_a_real_in_bounds_record(self):
        self.mutations(self.contract('E1M1MinimumScan','next','s hits i best state inside'),[
            ('(inside : i<hits.size)','(inside : i≤hits.size)'),
            ('(state : Represents s hits i best)','(state : True)')])

    def test_signed_minimum_ties_and_sentinels(self):
        self.succeeds(HEADER+'''
def hit (frac : Int32) : Collision.Intercept := ⟨⟨frac⟩,true,0⟩
example : (minimum #[hit 65536,hit 1,hit 1,hit 2147483647]).toOption = some (1,some 1) := by decide +kernel
example : (minimum #[hit 0,hit (-2147483648),hit (-2147483648)]).toOption = some (-2147483648,some 1) := by decide +kernel
example : (minimum #[hit 2147483647,hit 2147483647]).toOption = some (2147483647,none) := by decide +kernel
example : (minimum #[]).toOption = some (2147483647,none) := by decide +kernel
''')

    def test_no_choice_requires_sentinel_distance(self):
        self.mutations(self.contract('E1M1InterceptMinimum','minimum_none','hits distance noneSelected'),[
            ('(noneSelected : minimum hits=.ok (distance,none))','(noneSelected : True)'),
            ('distance=2147483647','distance=65536')])

    def test_actual_machine_empty_scan_keeps_stale_pointer_and_memory(self):
        self.succeeds(HEADER+'''
def emptyState : X86Memory.State := ⟨fun r => if r=1 then 0x2ba20 else if r=3 then 0xdeadbeef else 7,fun _ => 0⟩
example : (OriginalInterceptMinimum.entry emptyState).pc=0x2c85e ∧
    (OriginalInterceptMinimum.entry emptyState).core.regs 3=0xdeadbeef ∧
    (OriginalInterceptMinimum.entry emptyState).core.regs 2=0x7fffffff := by decide +kernel
''')

if __name__=='__main__':unittest.main()

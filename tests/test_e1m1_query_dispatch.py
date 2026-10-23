"""Continuous first dispatch must retain real entry, selection and cutoff evidence."""
import re, unittest
from pathlib import Path
import test_e1m1_traversal_entry as prior
import verify_e1m1_query_dispatch as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1QueryDispatch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1TraversalEntry (Protected)
open E1M1FirstIntercept (program Boundary)
open E1M1MinimumScan (address Fractions Represents)
open E1M1InterceptMinimum (Best minimum)
attribute [local irreducible] load32 store32
'''

class QueryDispatchTests(unittest.TestCase):
    lean=prior.TraversalEntryTests.lean
    succeeds=prior.TraversalEntryTests.succeeds
    rejects=prior.TraversalEntryTests.rejects
    mutations=prior.TraversalEntryTests.mutations

    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_bytes_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),33)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('QueryDispatch.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        # Change strict minimum ordering, then the inclusive range endpoint.
        for unit,index,value in [('interceptMinimum',14,0x7c),('interceptGate',8,0x7d)]:
            altered=dict(raw);b=bytearray(raw[unit]);self.assertNotEqual(b[index],value)
            b[index]=value;altered[unit]=bytes(b);self.rejects(proof.certificate(data,altered))

    def test_dispatch_requires_actual_setup_and_encoded_collection(self):
        self.mutations(self.contract('E1M1FirstIntercept','dispatch','s hits bounded limit encoded maximum pc'),[
            ('(bounded : hits.size≤128)','(bounded : True)'),
            ('(limit : s.core.regs 1=address hits.size)','(limit : True)'),
            ('(encoded : Fractions s.core.memory hits)','(encoded : True)'),
            ('(maximum : s.core.regs 7=65536)','(maximum : True)'),
            ('(pc : s.pc=(if hits.size=0 then 0x2c887 else 0x2c841))','(pc : True)')])

    def test_dispatch_retains_bound_and_actual_output(self):
        self.mutations(self.contract('E1M1FirstIntercept','dispatch','s hits bounded limit encoded maximum pc'),[
            ('∃ n≤9+7*hits.size','∃ n≤8+7*hits.size'),
            ('Boundary hits out','Boundary hits {out with pc:=0}')])

    def test_query_composition_keeps_entry_and_reachable_layout_contracts(self):
        args='q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads separated room'
        self.mutations(self.contract('E1M1QueryDispatch','execution',args),[
            ('(entry : Entry q s sx sy ex ey)','(entry : True)'),
            ('(separated : Protected q)','(separated : True)'),
            ('⟨s,f,0x2c8a0⟩','⟨s,f,0x2cafd⟩'),
            ('Boundary after.collected out','Boundary after.visited out')])

    def test_no_hit_claims_require_real_empty_or_rejected_minimum(self):
        self.mutations(self.contract('E1M1FirstIntercept','empty_tail','r visit empty'),[
            ('(empty : r.collected.size=0)','(empty : True)')])
        self.mutations(self.contract('E1M1FirstIntercept','rejected_tail','r visit best selected far'),[
            ('(selected : minimum r.collected=.ok best)','(selected : True)'),
            ('(far : best.1>65536)','(far : best.1≥65536)')])

    def test_live_tail_empty_rejection_endpoint_and_first_tie(self):
        self.succeeds(HEADER+'''
open Collision
def hit (d : Int32) (i : Nat) : Intercept := ⟨⟨d⟩,true,i⟩
def seed (hits : Array Intercept) : PathResult :=
  {trace:=⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩,collected:=hits,visited:=#[hit 0 99]}
def result (hits : Array Intercept) : Option (Bool × List Nat) :=
  (E1M1QuerySource.visitHits (seed hits) (fun _ _ => false)).toOption.map
    (fun r => (r.completed,r.visited.toList.map (·.id)))
example : result #[]=some (true,[99]) := by decide +kernel
example : result #[hit 65537 1,hit 2147483647 2]=some (true,[99]) := by decide +kernel
example : result #[hit 65536 1,hit 65536 2]=some (false,[99,1]) := by decide +kernel
example : result #[hit 65536 1,hit (-1) 2]=some (false,[99,2]) := by decide +kernel
example : result #[hit 2147483647 1]=some (true,[99]) := by decide +kernel
''')

if __name__=='__main__':unittest.main()

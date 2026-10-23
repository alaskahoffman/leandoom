"""Check live-loop extraction, history induction and repeat-counter contracts."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_repeat as prior
import verify_e1m1_ordered_history as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1TraversalBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1SelectionHistory E1M1InterceptMinimum E1M1OrderedVisit
open E1M1InterceptMark (consume)
open E1M1AimNextSelection (head)
'''
class OrderedHistoryTests(unittest.TestCase):
    lean=prior.AimRepeatTests.lean
    succeeds=prior.AimRepeatTests.succeeds
    rejects=prior.AimRepeatTests.rejects
    mutations=prior.AimRepeatTests.mutations
    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),42)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out+'extra',out.replace('OrderedTraversal.live_history','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_extraction_preserves_iteration_count_and_callback(self):
        self.mutations(self.contract('E1M1OrderedVisit','live_walk','result visit'),[
            ('walk result.collected.size result result.collected visit','walk (result.collected.size-1) result result.collected visit'),
            ('E1M1QuerySource.visitHits result visit','E1M1QuerySource.visitHits result (fun _ _ => true)')])
    def test_consumed_record_cannot_pass_range_again(self):
        self.mutations(self.contract('E1M1SelectionHistory','fresh','initial work seen image distance j chosen within'),[
            ('(within : ¬distance>65536)','(within : True)'),
            ('(image : Image initial work seen)','(image : True)'),
            ('(chosen : minimum work=.ok (distance,some j))','(chosen : True)')])
    def test_history_alignment_requires_equal_selection_count(self):
        self.mutations(self.contract('E1M1SelectionHistory','same_count','first second length'),[
            ('(length : seen₁.length=seen₂.length)','(length : True)')])
        self.mutations(self.contract('E1M1SelectionHistory','original_log','history'),[
            ('seen.reverse.map (fun i => initial[i]!)','seen.map (fun i => initial[i]!)'),
            ('seen.reverse.map (fun i => initial[i]!)','seen.reverse.map (fun i => work[i]!)')])
    def test_source_steps_include_rejected_hit_and_exact_visit_index(self):
        self.mutations(self.contract('E1M1OrderedTraversal','stop_step','fuel result work visit distance j selected within reject'),[
            ('visit work[j]! result.visited.size=false','visit work[j]! j=false'),
            ('.ok {appended result work[j]! with completed:=false}','.ok result')])
    def test_repeat_counter_matches_remaining_budget_and_wraps_only_at_exit(self):
        self.mutations(self.contract('E1M1TraversalBudget','head_budget','s f initial work seen visits history bounded counter'),[
            ('(counter : s.regs 6=BitVec.ofNat 32 (initial.size-seen.length))','(counter : True)'),
            ('then (head s).core.regs 6=0xffffffff','then (head s).core.regs 6=0'),
            ('BitVec.ofNat 32 (initial.size-seen.length-1)','BitVec.ofNat 32 (initial.size-seen.length)'),
            ('then 0x2c887 else 0x2c841','then 0x2c841 else 0x2c887')])
    def test_live_signed_ties_cutoff_stop_and_preexisting_visit_log(self):
        # Execute the real visitor for concrete cases; the general correspondence
        # and history properties above are separately checked kernel proofs.
        out=self.succeeds(HEADER+'''
def hit (fraction : Int32) (id : Nat) : Intercept := ⟨⟨fraction⟩,true,id⟩
def sample : PathResult := {trace:=⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩,collected:=#[hit 65536 10,hit (-1) 20,hit 65536 30,hit 65537 40,hit 2147483647 50]}
def ids (r : Except String PathResult) : List Nat := match r with
  | .error _ => [999]
  | .ok r => r.visited.toList.map (fun h => h.id)
#eval ids (E1M1QuerySource.visitHits sample (fun _ _ => true))
#eval ids (E1M1QuerySource.visitHits sample (fun _ i => i<1))
#eval (match E1M1QuerySource.visitHits sample (fun _ _ => false) with
  | .ok r => r.completed | .error _ => true)
#eval ids (E1M1QuerySource.visitHits {sample with visited:=#[hit 0 99]} (fun _ i => i<1))
#eval ids (E1M1QuerySource.visitHits {trace:=⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩,collected:=#[]} (fun _ _ => false))
#eval ids (E1M1QuerySource.visitHits {trace:=⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩,collected:=#[hit 65537 1,hit 2147483647 2]} (fun _ _ => true))
''')
        self.assertEqual(out.strip().splitlines(),['[20, 10, 30]','[20, 10]','false','[99, 20]','[]','[]'])
if __name__=='__main__':unittest.main()

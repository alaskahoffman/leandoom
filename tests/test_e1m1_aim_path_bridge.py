"""Guard exact history replay, precomputed hit alignment and source aim exits."""
import re
import unittest
from pathlib import Path
import test_e1m1_aim_traversal_invariant as prior
import verify_e1m1_aim_path_bridge as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimPathBridge
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory Collision
open E1M1SelectionHistory E1M1InterceptMinimum E1M1OrderedVisit E1M1OrderedTraversal
open E1M1InterceptMark (consume)
open E1M1HistoryDispatch (Selection)
open E1M1AimIteration E1M1AimSource
'''
class AimPathBridgeTests(unittest.TestCase):
    lean=prior.AimTraversalInvariantTests.lean
    succeeds=prior.AimTraversalInvariantTests.succeeds
    rejects=prior.AimTraversalInvariantTests.rejects
    mutations=prior.AimTraversalInvariantTests.mutations
    def contract(self,module,name,args):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r' ',text,re.M).start()
        decl=text[start:text.index(' := by',start)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_complete_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),42)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimPathOrder.next_hit','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_history_replay_keeps_budget_and_original_log(self):
        self.mutations(self.contract('E1M1AimPathOrder','replay','initial work seen visits history result'),[
            ('(history : History initial work seen visits)','(history : True)'),
            ('walk (initial.size-seen.length)','walk initial.size'),
            ('visited:=result.visited++visits','visited:=visits')])
    def test_next_hit_requires_reached_history_and_admitted_minimum(self):
        self.mutations(self.contract('E1M1AimPathOrder','next_hit','result out work seen visits history distance j chosen within run'),[
            ('(history : History result.collected work seen visits)','(history : True)'),
            ('(within : ¬distance>65536)','(within : True)'),
            ('(chosen : minimum work=.ok (distance,some j))','(chosen : True)'),
            ('out.visited[result.visited.size+seen.length]!','out.visited[result.visited.size+seen.length+1]!')])
    def test_terminal_requires_actual_exhaustion_or_range_exit(self):
        self.mutations(self.contract('E1M1AimPathOrder','terminal','result out work seen visits history done run'),[
            ('seen.length=result.collected.size ∨','True ∨'),
            ('best.1>65536','True'),
            ('out.visited=result.visited++visits','out.visited=visits')])
    def test_dos_selection_uses_chronological_index_and_original_hit(self):
        self.mutations(self.contract('E1M1AimPathBridge','selected',proof.SELECT_ARGS),[
            ('(selection : Selection result.collected work seen resolve target sp s fraction j)','(selection : True)'),
            ('(empty : result.visited=#[])','(empty : True)'),
            ('path.visited[seen.length]!','path.visited[j]!'),
            ('result.collected[j]!','result.collected[j+1]!')])
    def test_source_step_uses_reached_selection_and_updated_window(self):
        self.mutations(self.contract('E1M1AimPathBridge','next_line',proof.LINE_ARGS),[
            ('(run : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)','(run : True)'),
            ('(seen.length::rest)','(j::rest)'),
            ('(portals.push (portal scene.lines[(work[j]!).id]!.front back distance work[j]!))','portals'),
            ('stopped path (seen.length+1)','stopped path seen.length')])
    def test_finished_suffix_excludes_unprocessed_source_hits(self):
        self.mutations(self.contract('E1M1AimPathBridge','finished',proof.FINISH_ARGS),[
            ('(empty : result.visited=#[])','(empty : True)'),
            ('seen.length=result.collected.size ∨','True ∨'),
            ('path.visited.size=seen.length ∧','path.visited.size=seen.length+1 ∧')])
    def test_live_visitor_ties_limits_negative_fractions_and_prior_log(self):
        self.succeeds(HEADER+'''
def checkOrder (fractions : Array Int32) (expected : Array Nat) : IO Unit := do
  let hits := fractions.mapIdx fun i f => (⟨⟨f⟩,i % 2 == 0,i⟩ : Intercept)
  let initial : PathResult := {
    trace := ⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩
    collected := hits
    visited := #[⟨⟨0⟩,true,999⟩] }
  match E1M1QuerySource.visitHits initial (fun _ _ => true) with
  | .error e => throw (IO.userError e)
  | .ok path =>
    if path.visited.map (·.id) != #[999]++expected then
      throw (IO.userError "wrong strict-min order")
    if path.visited.size != expected.size+1 then throw (IO.userError "wrong count")
    for i in [:expected.size] do
      let hit := path.visited[i+1]!
      let original := hits[expected[i]!]!
      if hit.frac.raw != original.frac.raw || hit.isLine != original.isLine then
        throw (IO.userError "original record was marked or altered")
#eval do
  checkOrder #[] #[]
  checkOrder #[65537,2147483647] #[]
  checkOrder #[65536,0,65536,-1,2147483647,65537] #[3,1,0,2]
  checkOrder #[7,7,7,7] #[0,1,2,3]
  checkOrder #[-2147483648,2147483647,-2147483648,65536] #[0,2,3]
  checkOrder (Array.replicate 128 42) (List.range 128).toArray
''')
if __name__=='__main__':unittest.main()

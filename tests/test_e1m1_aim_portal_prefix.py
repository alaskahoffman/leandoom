"""Guard genuine multi-hit induction, history progress and both traversal exits."""
import re
import unittest
from pathlib import Path
import test_e1m1_aim_synchronized_cycle as prior
import verify_e1m1_aim_portal_prefix as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimPortalPrefixExit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimSourceCatalog (Represents front back)
open E1M1AimIteration
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimPortalPrefix (Position advance Sequence)
open E1M1AimRepeatProgram (program)
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimPortalPrefixTests(unittest.TestCase):
    lean=prior.AimSynchronizedCycleTests.lean
    succeeds=prior.AimSynchronizedCycleTests.succeeds
    rejects=prior.AimSynchronizedCycleTests.rejects
    mutations=prior.AimSynchronizedCycleTests.mutations
    def contract(self,module,name,args):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r' ',text,re.M).start()
        decl=text[start:text.index(' := by',start)]
        decl=re.sub(r'\bprogram\b','E1M1AimRepeatProgram.program',decl)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_complete_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),42)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimPortalPrefix.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_seed_uses_actual_first_selection_and_persistent_state(self):
        self.mutations(self.contract('E1M1AimPortalPrefix','seed',
            'scene shooter thing path result distance a seen visits resolve portals s sp fraction j history selection before empty query'),[
            ('(selection : Selection result.collected a.work seen resolve 0x2b760 sp s fraction j)','(selection : True)'),
            ('(before : Persistent s.core result.collected a.work resolve portals distance thing.shootHeight)','(before : True)'),
            ('(empty : result.visited=#[])','(empty : True)')])
    def test_induction_requires_source_sequence_and_initial_boundary_only(self):
        self.mutations(self.contract('E1M1AimPortalPrefix','execution',proof.EXEC_ARGS),[
            ('(sequence : Sequence portals distance thing.shootHeight a final count)','(sequence : True)'),
            ('(history : History result.collected a.work seen visits)','(history : True)'),
            ('(aligned : AlignedNext origin scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s)','(aligned : True)'),
            ('n≤count*(157+7*result.collected.size)','n≤count*(157+6*result.collected.size)'),
            ('finalSeen.length=seen.length+count','finalSeen.length=seen.length')])
    def test_induction_preserves_final_invariant_bounds_and_actual_suffix(self):
        self.mutations(self.contract('E1M1AimPortalPrefix','execution',proof.EXEC_ARGS),[
            ('History result.collected final.work finalSeen finalVisits','History result.collected a.work finalSeen finalVisits'),
            ('load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec','load32 out.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec'),
            ('load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec','load32 out.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec'),
            ("List.range' finalSeen.length (path.visited.size-finalSeen.length)","List.range' seen.length (path.visited.size-seen.length)")])
    def test_capacity_counts_distinct_consumed_records(self):
        self.mutations(self.contract('E1M1AimPortalPrefix','capacity',proof.EXEC_ARGS),[
            ('(sequence : Sequence portals distance thing.shootHeight a final count)','(sequence : True)'),
            ('count≤result.collected.size-seen.length','count+1≤result.collected.size-seen.length')])
    def test_normal_exit_requires_exhaustion_or_range_rejection(self):
        self.mutations(self.contract('E1M1AimPortalPrefixExit','completed',proof.COMPLETE_ARGS),[
            ('seen.length+count=result.collected.size ∨','True ∨'),
            ('best.1>65536','True'),
            ('out.pc=0x2c887','out.pc=0x2c88c'),
            ('.ok {path:=path}', '.ok {path:=E1M1AimSource.stopped path seen.length}')])
    def test_later_stop_includes_last_visit_without_consuming_it(self):
        self.mutations(self.contract('E1M1AimPortalPrefixExit','stopped',proof.STOP_ARGS),[
            ('(closed : ¬(advance final j p distance floorSlope ceilingSlope).lower.raw <\n      (advance final j p distance floorSlope ceilingSlope).upper.raw)','(closed : True)'),
            ('out.pc=0x2c88c','out.pc=0x2c887'),
            ('History result.collected final.work finalSeen finalVisits','History result.collected (E1M1InterceptMark.consume final.work j) finalSeen finalVisits'),
            ('E1M1AimSource.stopped path (seen.length+count+1)','E1M1AimSource.stopped path (seen.length+count)'),
            ('n≤(count+1)*(157+7*result.collected.size)','n≤count*(157+7*result.collected.size)')])
    def test_two_tied_portals_have_a_kernel_checked_source_sequence(self):
        source=HEADER+'''
open E1M1InterceptMinimum (minimum_replay)
def p : Portal := ⟨0,0,0,8388608,0,8388608⟩
def portals : Nat → Option Portal := fun _ => some p
def a : Position := ⟨#[⟨⟨32768⟩,true,0⟩,⟨⟨32768⟩,true,1⟩],⟨-40960⟩,⟨40960⟩,#[]⟩
def b := advance a 0 p ⟨65536⟩ ⟨0⟩ ⟨0⟩
def c := advance b 1 p ⟨65536⟩ ⟨0⟩ ⟨0⟩
example : Sequence portals ⟨65536⟩ ⟨0⟩ a c 2 := by
  apply Sequence.cons 32768 0 p ⟨0⟩ ⟨0⟩
  · exact (minimum_replay a.work).trans (congrArg Except.ok (by decide))
  · decide
  · rfl
  · decide
  · intro h; exact False.elim (h rfl)
  · intro h; exact False.elim (h rfl)
  · decide
  · apply Sequence.cons 32768 1 p ⟨0⟩ ⟨0⟩
    · exact (minimum_replay b.work).trans (congrArg Except.ok (by decide))
    · decide
    · rfl
    · decide
    · intro h; exact False.elim (h rfl)
    · intro h; exact False.elim (h rfl)
    · decide
    · exact Sequence.nil c
'''
        self.mutations(source,[
            ('apply Sequence.cons 32768 1 p','apply Sequence.cons 32768 0 p'),
            ('⟨-40960⟩,⟨40960⟩','⟨40960⟩,⟨40960⟩')])
if __name__=='__main__':unittest.main()

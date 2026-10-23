"""Outside cells must execute real returns without appending hits or resetting history."""
import re
import unittest
from pathlib import Path
import test_e1m1_cell_walk as prior
import verify_e1m1_mixed_cell_walk as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1CellWalkLimit','import Doom.Proofs.E1M1MixedCellWalk')
HEADER+='open E1M1CellWalk (grid)\n'
HEADER+='attribute [local irreducible] E1M1OutsideLine.result E1M1OutsideCell.result E1M1MixedCellWalk.next E1M1MixedCellWalk.history\n'
WALK='q cells s r seen common statics state images entry follows room'

class MixedCellWalkTests(unittest.TestCase):
    lean=prior.CellWalkTests.lean
    succeeds=prior.CellWalkTests.succeeds
    rejects=prior.CellWalkTests.rejects
    mutations=prior.CellWalkTests.mutations

    def contract(self,module,name,args):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r'(?: | :)',source,re.M).start()
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('OutsideLine.memory','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_outside_line_reads_and_saved_counter_require_real_frame(self):
        self.mutations(self.contract('E1M1OutsideLine','read_word','s sp a stack safe'),[
            ('(safe : CallerSafe sp a)','(safe : True)'),
            ('(stack : s.core.regs 4=sp-(112#32))','(stack : True)')])
        self.mutations(self.contract('E1M1OutsideLine','register','s outside reg member'),[
            ('(outside : ¬OriginalLineBounds.Inside (OriginalLineBounds.entry (E1M1PathMapCaller.call s.core).core))','(outside : True)'),
            ('([1,5,6,7] : List (Fin 8))','([0,1,5,6,7] : List (Fin 8))')])

    def test_line_bounds_return_requires_outside_coordinate_and_actual_map(self):
        self.mutations(self.contract('E1M1OutsideLine','execution','q s x y common stack maps pc mapX mapY outMap'),[
            ('(outMap : Collision.pathCellInside x y q.width q.height=false)','(outMap : True)'),
            ('(maps : E1M1CellMapInvariant.Image s.core.memory q.sp q.base q.lines q.words q.width q.height)','(maps : True)'),
            ('out.pc=0x2ca94','out.pc=0x2ca9c'),
            ('n≤22','n≤21')])

    def test_state_preservation_needs_all_stack_reads_and_original_state(self):
        self.mutations(self.contract('E1M1OutsideCell','state_reads','q s t r seen common state stack reads'),[
            ('(state : E1M1CellWalkInvariant.State q s r seen)','(state : True)'),
            ('(reads : ∀ a, CallerSafe q.sp a → load32 t.core.memory a=load32 s.core.memory a)','(reads : True)'),
            ('(stack : t.core.regs 4=q.sp-(112#32))','(stack : True)')])

    def test_objects_return_to_the_real_caller_without_a_head_premise(self):
        self.mutations(self.contract('E1M1OutsideCell','objects','q s r seen common state pc success x y mapX mapY outMap'),[
            ('(success : s.core.regs 0=(1#32))','(success : True)'),
            ('(outMap : Collision.pathCellInside x y q.width q.height=false)','(outMap : True)'),
            ('out.pc=0x2cab1','out.pc=0x2ca94'),
            ('n≤28','n≤27')])

    def test_outside_cell_still_steps_and_tests_the_original_exit(self):
        self.mutations(self.contract('E1M1OutsideCell','execution','q s r seen common state pc x y mapX mapY outMap'),[
            ('E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core)',
             'E1M1PathAdvance.observe out.core=E1M1PathAdvance.observe s.core'),
            ('out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core)','out.pc=0x2ca7f'),
            ('n≤71','n≤70')])

    def test_mixed_walk_keeps_initial_images_and_one_budget(self):
        self.mutations(self.contract('E1M1MixedCellWalk','execution',WALK),[
            ('(images : Images q cells s.core.memory)','(images : True)'),
            ('(statics : ∀ c∈cells, Admitted q c)','(statics : True)'),
            ('(room : r.collected.size+budget q cells≤128)','(room : r.collected.size≤128)')])

    def test_mixed_walk_still_requires_original_control_and_history(self):
        self.mutations(self.contract('E1M1MixedCellWalk','execution',WALK),[
            ('(follows : Follows (E1M1PathAdvance.observe s.core) cells)','(follows : True)'),
            ('(entry : cells≠[] → s.pc=0x2ca7f)','(entry : True)'),
            ('State q out after (history q seen cells)','State q out after seen'),
            ('out.pc=stopPc s.pc (E1M1PathAdvance.observe s.core) cells','out.pc=0x2ca7f')])

    def test_outside_branch_does_not_require_payload_or_budget_or_update_visits(self):
        self.succeeds('''import Doom.Proofs.E1M1MixedCellWalk
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1CellWalkInvariant (Context Cell)
open E1M1MixedCellWalk
example (q : Context) (c : Cell) (seen : Array Bool) (m : Memory)
    (outside : inside q c=false) :
    Admitted q c ∧ Images q [c] m ∧ cost q c=0 ∧ visits q c seen=seen := by
  simp [Admitted,Images,cost,visits,outside]
example (q : Context) (c : Cell) (s : X86Control.State) (r after : Collision.PathResult)
    (outside : inside q c=false) : CellResult q c s r after ↔ after=r := by
  simp [CellResult,outside]
''')

    def test_signed_and_upper_bound_rejections_restore_real_callers(self):
        self.succeeds('''import Doom.Proofs.E1M1MixedCellWalk
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
example : Collision.pathCellInside (-1) 0 23 36=false ∧
    Collision.pathCellInside 0 (-1) 23 36=false ∧
    Collision.pathCellInside 23 0 23 36=false ∧
    Collision.pathCellInside 0 36 23 36=false ∧
    Collision.pathCellInside 22 35 23 36=true := by decide +kernel
-- Rejected bounds never require a valid object table or line list.
def fixture (ret : Word) : X86Memory.State :=
  ⟨(fun i => if i=4 then 0x1000 else if i=0 then 0xffffffff else if i=7 then 37 else 0),
    store32 (fun _ => 0) 0x1000 ret⟩
example : (OriginalLineBounds.result (fixture 0x2ca94)).pc=0x2ca94 ∧
    (OriginalLineBounds.result (fixture 0x2ca94)).core.regs 4=0x1004 ∧
    (OriginalLineBounds.result (fixture 0x2ca94)).core.regs 7=37 ∧
    (OriginalLineBounds.result (fixture 0x2ca94)).core.regs 0=1 := by decide +kernel
example : (OriginalThingEntry.result (fixture 0x2cab1)).pc=0x2cab1 ∧
    (OriginalThingEntry.result (fixture 0x2cab1)).core.regs 4=0x1004 ∧
    (OriginalThingEntry.result (fixture 0x2cab1)).core.regs 0=1 := by decide +kernel
''')

if __name__=='__main__':unittest.main()

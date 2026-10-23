"""Guard the counter, authentic callback state and ordered-history seam."""
import re
import unittest
from pathlib import Path
import test_e1m1_ordered_history as prior
import verify_e1m1_history_dispatch as proof

ROOT = Path(__file__).resolve().parents[1]
HEADER = '''import Doom.Proofs.E1M1HistoryDispatch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1SelectionHistory E1M1InterceptMinimum
open E1M1MinimumScan (address Represents Fractions)
open E1M1InterceptMark (consume)
open E1M1AimNextSelection (head)
open E1M1AimRepeatProgram (ReadFrame)
open E1M1OrderedTraversal (appended)
open E1M1OrderedVisit (walk)
attribute [local irreducible] load32 store32
'''


class HistoryDispatchTests(unittest.TestCase):
    lean = prior.OrderedHistoryTests.lean
    succeeds = prior.OrderedHistoryTests.succeeds
    rejects = prior.OrderedHistoryTests.rejects
    mutations = prior.OrderedHistoryTests.mutations

    def contract(self, module, name, args):
        source = (ROOT / f'Doom/Proofs/{module}.lean').read_text()
        start = re.search(r'^theorem ' + name + r'(?: | :)', source, re.M).start()
        decl = source[start:source.index(' := by', start)]
        program = ('E1M1InterceptGate.program' if module == 'E1M1SelectionRegisters'
                   else 'E1M1AimRepeatProgram.program')
        decl = re.sub(r'\bprogram\b', program, decl)
        decl = re.sub(r'\bgate\b', 'OriginalInterceptGate.gate', decl)
        return (HEADER + 'namespace Doom.Proofs.' + module + '\n' +
                decl.replace('theorem ' + name, 'example', 1) + ' :=\n  ' +
                module + '.' + name + ' ' + args + '\nend Doom.Proofs.' + module + '\n')

    def test_certificate_and_complete_transitive_audit(self):
        data, _ = proof.pinned_data()
        spec, _, raw = proof.extracted()
        self.assertEqual(len(spec['units']), 42)
        output = self.succeeds(proof.certificate(data, raw))
        proof.audit(output)
        for bad in [output.replace('Quot.sound', 'sorryAx'), output + 'extra',
                    output.replace('NextCallbackState.dispatch', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)
        for module, names in proof.GROUPS.items():
            self.assertEqual(names, re.findall(r'^theorem (\w+)(?: | :)',
                (ROOT / f'Doom/Proofs/{module}.lean').read_text(), re.M))

    def test_full_scan_preserves_counter_and_stack(self):
        self.mutations(self.contract('E1M1SelectionRegisters', 'execution',
            's f hits bounded limit encoded maximum'), [
            ('selected.core.regs 6=s.regs 6', 'selected.core.regs 6=s.regs 6-1'),
            ('selected.core.regs 4=s.regs 4', 'selected.core.regs 4=s.regs 4-4'),
            ('(encoded : Fractions s.memory hits)', '(encoded : True)')])

    def test_call_derives_cursor_and_keeps_counter(self):
        self.mutations(self.contract('E1M1NextCallbackState', 'dispatch',
            's hits resolve bounded limit encoded maximum pc targetSafe cursorSafe recordSafe'), [
            ('(cursorSafe : Apart 0x2c028 (s.core.regs 4-4))', '(cursorSafe : True)'),
            ('out.core.regs 6=s.core.regs 6', 'out.core.regs 6=s.core.regs 6-1'),
            ('(maximum : s.core.regs 7=65536)', '(maximum : True)')])

    def test_callback_slot_uses_frame_and_cursor_separation(self):
        self.mutations(self.contract('E1M1NextCallbackState', 'callback_slot',
            's out frame safe'), [
            ('(frame : ReadFrame s out)', '(frame : True)'),
            ('(safe : Apart (s.regs 4) 0x2c028)', '(safe : True)')])

    def test_repeat_entry_requires_actual_history_and_remaining_count(self):
        self.mutations(self.contract('E1M1HistoryDispatch', 'execution', proof.ENTRY_ARGS), [
            ('(history : History initial work seen visits)', '(history : True)'),
            ('(counter : s.regs 6=BitVec.ofNat 32 (initial.size-seen.length))', '(counter : True)'),
            ('⟨s,f,0x2c83a⟩ out', '⟨s,f,0x2c841⟩ out'),
            ('(targetSafe : Apart (s.regs 4) 0x2c028)', '(targetSafe : True)')])

    def test_reached_state_has_both_pointers_and_next_budget(self):
        source = HEADER + '''
example (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (target sp : Word) (out : X86Control.State)
    (distance : Int32) (j : Nat)
    (h : E1M1HistoryDispatch.Selection initial work seen resolve target sp out distance j) :
    out.core.regs 3=address j ∧
    out.core.regs 6=BitVec.ofNat 32 (initial.size-(j::seen).length) ∧
    work[j]! = initial[j]! ∧ j∉seen :=
  ⟨h.ready.pointer.trans h.argument,h.counter,h.original,h.fresh⟩
'''
        self.mutations(source, [
            ('out.core.regs 3=address j', 'out.core.regs 3=address (j+1)'),
            ('BitVec.ofNat 32 (initial.size-(j::seen).length)', 'BitVec.ofNat 32 (initial.size-seen.length)'),
            ('∧ j∉seen', '∧ j∈seen')])

    def test_source_continue_uses_original_hit_visit_index_and_next_fuel(self):
        self.mutations(self.contract('E1M1HistoryDispatch', 'source_continue', proof.SOURCE_ARGS), [
            ('visit initial[j]! (priorVisits.size+seen.length)=true', 'visit initial[j]! j=true'),
            ('walk (initial.size-(j::seen).length)', 'walk (initial.size-seen.length)'),
            ('(log : result.visited=priorVisits++visits)', '(log : True)')])

    def test_source_stop_includes_selected_hit_and_marks_incomplete(self):
        self.mutations(self.contract('E1M1HistoryDispatch', 'source_stop',
            proof.SOURCE_ARGS.replace('accept', 'reject')), [
            ('.ok {appended result initial[j]! with completed:=false}', '.ok result'),
            ('visit initial[j]! (priorVisits.size+seen.length)=false', 'visit initial[j]! (priorVisits.size+seen.length)=true')])


if __name__ == '__main__':
    unittest.main()

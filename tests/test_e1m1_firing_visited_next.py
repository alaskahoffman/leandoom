"""The next cell must inherit the actual visited history and incremented epoch."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_things as previous
import verify_e1m1_firing_visited_next as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=previous.HEADER.replace('import Doom.Proofs.E1M1FiringThings','import Doom.Proofs.E1M1FiringVisitedNext')
HEADER+='open OriginalLineMixedInvariant\nopen OriginalLineVisits (Represents markPrefix stamp)\nopen E1M1ScanContracts (candidates)\nopen E1M1FiringGridState (initial)\nopen E1M1FiringLineVisits (seenAfter)\n'
FULL=previous.ARGS+previous.HEAD+previous.DATA
VIS=' stamps epochBefore epochAfter stampSetup fresh epochTail stampTail'
REST=' room world dimension ids scene'
NEXT=FULL+VIS+REST+' locals f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell'

class FiringVisitedNextTests(unittest.TestCase):
    lean=previous.FiringThingsTests.lean
    succeeds=previous.FiringThingsTests.succeeds
    rejects=previous.FiringThingsTests.rejects
    mutations=previous.FiringThingsTests.mutations

    def contract(self,module,name,args,section=False):
        return previous.FiringThingsTests.contract(self,module,name,args,section).replace(previous.HEADER,HEADER,1)

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('FiringVisitedNext.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_marked_bits_survive_and_first_candidate_is_marked(self):
        self.mutations(self.contract('OriginalLineVisitedRun','mark_keeps','cs k i seen j bound marked'),[
            ('(marked : seen[j]! =true)','(marked : True)'),
            ('(markPrefix cs k i seen)[j]! =true','(markPrefix cs k i seen)[j]! =false')])
        self.mutations(self.contract('OriginalLineVisitedRun','first_marked','cs k i seen bound'),[
            ('(bound : (cs i).id<seen.size)','(bound : True)'),
            ('markPrefix cs (k+1) i seen','markPrefix cs k i seen')])

    def test_continuing_scan_requires_layout_and_representation(self):
        self.mutations(self.contract('OriginalLineVisitedRun','run_represents',
            'initial n base resolve h lines count layout i s r inv k bound keep epoch seen size represented'),[
            ('(layout : OriginalLineVisits.Layout initial h lines count)','(layout : True)'),
            ('(keep : ∀ j, i≤j → j<i+k → (h.candidates j).crosses=true → (h.candidates j).Continues)','(keep : True)'),
            ('(represented : Represents s.core.memory lines epoch seen)','(represented : True)')])

    def test_freshness_uses_incremented_epoch(self):
        self.mutations(self.contract('E1M1FiringLineVisits','fresh_scan',
            previous.ARGS+' stamps epochBefore epochAfter stampSetup fresh',True),[
            ('(fresh : ∀ j<475, load32 s.memory (stamp lines j)≠load32 s.memory 0x13580+1)','(fresh : True)'),
            ('load32 s.memory 0x13580+1','load32 s.memory 0x13580'),
            ('(stampSetup : ∀ j<475, E1M1PathMapFiring.Safe gun s (stamp lines j))','(stampSetup : True)')])

    def test_scan_layout_and_leading_zero_are_required(self):
        self.mutations(self.contract('E1M1FiringLineVisits','visit_layout',previous.ARGS+' stamps',True),[
            ('(stamps : E1M1ScanContracts.Stamps (s.regs 4) lines)','(stamps : True)')])
        self.mutations(self.contract('E1M1FiringLineVisits','seen_zero','trace lines c data words valid'),[
            ('(valid : c.Valid words)','(valid : True)')])

    def test_updated_stamps_need_only_postline_protection(self):
        self.mutations(self.contract('E1M1FiringVisitedNext','before_seen',FULL+VIS+' room',True),[
            ('(epochTail : TailSafe (s.regs 4) (0x13580#32))','(epochTail : True)'),
            ('(stampTail : ∀ j<475, TailSafe (s.regs 4) (stamp lines j))','(stampTail : True)'),
            ('(seenAfter (path thing angle ox oy).trace lines c data)','(Array.replicate 475 false)')])

    def test_next_lookup_rebases_protection_to_proved_stack(self):
        self.mutations(self.contract('E1M1FiringVisitedNext','next_safe','s sp a stack safe'),[
            ('(stack : s.regs 4=sp-(112#32))','(stack : s.regs 4=sp-(124#32))'),
            ('(safe : TailSafe sp a)','(safe : True)')])

    def test_leading_duplicate_needs_mark_and_actual_memory(self):
        self.mutations(self.contract('E1M1FiringVisitedNext','leading_duplicate',
            's lines epoch words c valid items seen size represented marked'),[
            ('(marked : seen[0]! =true)','(marked : True)'),
            ('(represented : Represents s.memory lines epoch seen)','(represented : True)'),
            ('(valid : c.Valid words)','(valid : True)')])

    def test_firing_prefix_joins_history_without_new_reserve(self):
        self.mutations(self.contract('E1M1FiringVisitedNext','execution',NEXT,True),[
            ('(fresh : ∀ j<475, load32 s.memory (stamp lines j)≠load32 s.memory 0x13580+1)','(fresh : True)'),
            ('after.collected 0','after.collected 1'),
            ('OriginalLineCell.already (OriginalLineCell.header out.core).core',
             '¬OriginalLineCell.already (OriginalLineCell.header out.core).core')])

if __name__=='__main__':unittest.main()

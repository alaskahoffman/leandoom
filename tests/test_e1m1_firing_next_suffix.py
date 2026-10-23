"""The duplicate must advance exactly one entry and preserve the justified reserve."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_visited_next as prior
import verify_e1m1_firing_next_suffix as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringVisitedNext','import Doom.Proofs.E1M1FiringNextSuffix')
HEADER+='open E1M1FiringVisitedNext (TailSafe)\n'

class FiringNextSuffixTests(unittest.TestCase):
    lean=prior.FiringVisitedNextTests.lean
    succeeds=prior.FiringVisitedNextTests.succeeds
    rejects=prior.FiringVisitedNextTests.rejects
    mutations=prior.FiringVisitedNextTests.mutations

    def contract(self,module,name,args,section=False):
        return prior.FiringVisitedNextTests.contract(self,module,name,args,section).replace(prior.HEADER,HEADER,1)

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('FiringNextSuffix.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_duplicate_execution_needs_actual_branch_and_entry(self):
        self.mutations(self.contract('E1M1DuplicateSuffix','skip','s pc nonlast seen'),[
            ('(pc : s.pc=0x2c57f)','(pc : s.pc=0x2c580)'),
            ('(nonlast : OriginalLineCell.itemWord s.core≠(0xffffffff#32))','(nonlast : True)'),
            ('(seen : OriginalLineCell.already (OriginalLineCell.header s.core).core)','(seen : True)'),
            ('n≤10','n≤9'),
            ('out.core.regs 2=s.core.regs 2+(2#32)','out.core.regs 2=s.core.regs 2')])

    def test_suffix_requires_same_memory_and_advanced_cursor(self):
        self.mutations(self.contract('E1M1DuplicateSuffix','scan_tail','s t lines c nonempty items memory cursor'),[
            ('(nonempty : c.ids≠[])','(nonempty : True)'),
            ('(memory : t.memory=s.memory)','(memory : True)'),
            ('(cursor : t.regs 2=s.regs 2+(2#32))','(cursor : t.regs 2=s.regs 2)'),
            ('ScanWords t lines (tailCell c)','ScanWords t lines c')])

    def test_object_count_bound_requires_success(self):
        self.mutations(self.contract('E1M1CellCapacity','collect_bound','trace nodes r after ok'),[
            ('(ok : E1M1ThingList.collect trace nodes r=.ok after)','(ok : True)'),
            ('r.collected.size+nodes.length','r.collected.size')])

    def test_scene_bound_uses_the_actual_ordered_scene(self):
        self.mutations(self.contract('E1M1CellCapacity','scene_bound',
            'trace world x y width nodes r after dimension ids scene ok'),[
            ('(dimension : world.grid.width=width)','(dimension : True)'),
            ('(scene : ∀ node∈nodes, world.things[node.id]?=some node.target)','(scene : True)'),
            ('Collision.pathCellIndex x y width','Collision.pathCellIndex y x width')])

    def test_reserve_cannot_be_created_without_count_and_budget(self):
        self.mutations(self.contract('E1M1CellCapacity','reserve','s base resolve hits limit tracked bound room'),[
            ('(bound : hits.size≤limit)','(bound : True)'),
            ('(room : limit≤128)','(room : True)'),
            ('hits (128-limit)','hits (129-limit)')])
        self.mutations(self.contract('E1M1CellCapacity','suffix_reserve','s base resolve hits limit remaining tracked budget'),[
            ('(budget : limit+remaining≤128)','(budget : remaining≤128)'),
            ('hits remaining','hits (remaining+1)')])

    def test_joined_firing_prefix_preserves_hits_and_exact_suffix(self):
        self.mutations(self.contract('E1M1FiringNextSuffix','execution',prior.NEXT,True),[
            ('steps≤467+281*c.ids.length+230*nodes.length','steps≤466+281*c.ids.length+230*nodes.length'),
            ('ScanWords out.core lines (E1M1DuplicateSuffix.tailCell nextCell)','ScanWords out.core lines nextCell'),
            ('after.collected (128-(c.ids.length+nodes.length))','after.collected 128'),
            ('out.core.regs 2=entry.core.regs 2+(2#32)','out.core.regs 2=entry.core.regs 2'),
            ('(seenAfter (path thing angle ox oy).trace lines c data)','(Array.replicate 475 false)')])

if __name__=='__main__':unittest.main()

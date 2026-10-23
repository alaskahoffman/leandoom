"""Next-cell lookup must preserve prior mutable state, not reset its history."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_things as previous
import verify_e1m1_next_cell_scan as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=previous.HEADER.replace('import Doom.Proofs.E1M1FiringThings','import Doom.Proofs.E1M1NextCellScan')
HEADER+='open E1M1NextCellMemory (advanced scan Safe)\nopen E1M1PathAdvance (Cell observe step nextPc)\n'

class NextCellScanTests(unittest.TestCase):
    lean=previous.FiringThingsTests.lean
    succeeds=previous.FiringThingsTests.succeeds
    rejects=previous.FiringThingsTests.rejects
    mutations=previous.FiringThingsTests.mutations

    def contract(self,module,name,args):
        return previous.FiringThingsTests.contract(self,module,name,args).replace(previous.HEADER,HEADER,1)

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('scan_invariants','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_frame_protects_both_step_and_caller_stores(self):
        self.mutations(self.contract('E1M1NextCellMemory','frame','s a safe'),[
            ('(safe : Safe s a)','(safe : E1M1PathMapCaller.Safe s a)'),
            ('(safe : Safe s a)','(safe : Apart a (s.regs 4+(44#32)))')])

    def test_visited_history_and_epoch_are_preserved_not_reset(self):
        self.mutations(self.contract('E1M1NextCellMemory','visits',
            's lines epoch seen represented epochSafe stampsSafe'),[
            ('(epochSafe : Safe s (0x13580#32))','(epochSafe : True)'),
            ('(stampsSafe : ∀ j<seen.size, Safe s (OriginalLineVisits.stamp lines j))','(stampsSafe : True)'),
            ('(scan s).core.memory lines epoch seen','(scan s).core.memory lines epoch (Array.replicate seen.size false)')])

    def test_map_image_and_globals_need_protection(self):
        self.mutations(self.contract('E1M1NextCellMemory','image','s base words encoded safe'),[
            ('(safe : ∀ i<words.size, Safe s (base+BitVec.ofNat 32 (2*i)))','(safe : True)')])
        self.mutations(self.contract('E1M1NextCellMemory','map',
            's base lines words w h dims globals encoded globalsSafe imageSafe'),[
            ('(globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Apart a (s.regs 4+(44#32)))','(globalsSafe : True)')])

    def test_collection_cannot_manufacture_next_scan_reserve(self):
        self.mutations(self.contract('E1M1NextCellMemory','collection',
            's base resolve hits reserve tracked advanceSafe cursorSafe recordsSafe'),[
            ('(advanceSafe : OriginalLineMixedInvariant.ArraySafe base (s.regs 4+(44#32)))','(advanceSafe : True)'),
            ('(cursorSafe : E1M1PathMapCaller.Safe s (0x2c028#32))','(cursorSafe : True)'),
            ('(scan s).core base resolve hits reserve','(scan s).core base resolve hits (reserve+1)')])

    def test_inside_requires_actual_next_cell_and_continuation(self):
        self.mutations(self.contract('E1M1NextCellScan','inside',
            's f g observed next x y mapX mapY base lines words c w h enabled dims globals encoded globalsSafe imageSafe inMap valid selected'),[
            ('(next : nextPc g=0x2ca7f)','(next : True)'),
            ('(mapX : (step g).mapX=x.toBitVec)','(mapX : g.mapX=x.toBitVec)'),
            ('(enabled : OriginalPathCell.enabled true s=true)','(enabled : True)'),
            ('(selected : words[4+Collision.pathCellIndex x y w]?=some c.offset)','(selected : True)'),
            ('⟨s,f,0x2cab5⟩','⟨s,f,0x2ca7f⟩')])

    def test_outside_returns_success_to_thing_gate(self):
        self.mutations(self.contract('E1M1NextCellScan','outside',
            's f g observed next x y mapX mapY w h enabled dims safe outMap'),[
            ('(outMap : Collision.pathCellInside x y w h=false)','(outMap : True)'),
            ('out.pc=0x2ca9c','out.pc=0x2cab5'),
            ('out.core.regs 0=1','out.core.regs 0=0')])

    def test_scan_inputs_keep_both_history_and_hits(self):
        self.mutations(self.contract('E1M1NextCellScan','scan_invariants',
            's lines epoch seen represented epochSafe stampsSafe base resolve hits reserve tracked advanceSafe cursorSafe recordsSafe'),[
            ('(represented : OriginalLineVisits.Represents s.memory lines epoch seen)','(represented : True)'),
            ('(tracked : OriginalLineCollection.Tracks s base resolve hits reserve)','(tracked : True)')])

if __name__=='__main__':unittest.main()

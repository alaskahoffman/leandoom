"""Retained ordered hits and a legal next iteration at the real grid gate."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_things as previous
import verify_e1m1_firing_collection_advance as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=previous.HEADER.replace('import Doom.Proofs.E1M1FiringThings','import Doom.Proofs.E1M1FiringCollectionAdvance')
HEADER+='open OriginalLineCollection (Tracks slot)\nopen E1M1PathAdvance (Cell observe step nextPc ended)\nopen E1M1FiringGridState (initial)\n'
FULL=previous.ARGS+previous.HEAD+previous.DATA+' locals'

class FiringCollectionAdvanceTests(unittest.TestCase):
    lean=previous.FiringThingsTests.lean
    succeeds=previous.FiringThingsTests.succeeds
    rejects=previous.FiringThingsTests.rejects
    mutations=previous.FiringThingsTests.mutations

    def contract(self,module,name,args,section=False):
        source=previous.FiringThingsTests.contract(self,module,name,args,section)
        return source.replace(previous.HEADER,HEADER,1)

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('continuing_index','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_memory_frame_needs_separation_from_actual_store(self):
        self.mutations(self.contract('E1M1AdvanceCollection','frame','s a safe'),[
            ('(safe : Apart a (s.regs 4+(44#32)))','(safe : True)'),
            ('(safe : Apart a (s.regs 4+(44#32)))','(safe : Apart a (s.regs 4+(40#32)))')])

    def test_ordered_records_cursor_and_reserve_survive_together(self):
        self.mutations(self.contract('E1M1AdvanceCollection','collection','s base resolve hits reserve tracked safe'),[
            ('(safe : OriginalLineMixedInvariant.ArraySafe base (s.regs 4+(44#32)))','(safe : True)'),
            ('Tracks (OriginalPathAdvance.result s).core base resolve hits reserve',
             'Tracks (OriginalPathAdvance.result s).core base resolve hits (reserve+1)')])

    def test_legal_index_and_termination_order(self):
        self.mutations(self.contract('E1M1AdvanceCollection','counter','g n bound count'),[
            ('if ended g then n else n+1','if ended g then n+1 else n'),
            ('else if n+1<64 then 0x2ca7f','else if n+1≤64 then 0x2ca7f')])
        self.mutations(self.contract('E1M1AdvanceCollection','next_gate_iff','g n bound count'),[
            ('ended g=false ∧ n+1<64','ended g=false ∨ n+1<64')])
        self.mutations(self.contract('E1M1AdvanceCollection','continuing_index','g n bound count next'),[
            ('(next : nextPc g=0x2ca7f)','(next : True)')])

    def test_reusable_iteration_requires_observation_and_collection(self):
        self.mutations(self.contract('E1M1AdvanceCollection','iteration',
            's f g observed n bound count base resolve hits reserve tracked safe'),[
            ('(observed : observe s=g)','(observed : True)'),
            ('(tracked : Tracks s base resolve hits reserve)','(tracked : True)'),
            ('steps≤19','steps≤18')])

    def test_firing_join_keeps_the_same_scene_collection(self):
        self.mutations(self.contract('E1M1FiringCollectionAdvance','execution',FULL+' room world dimension ids scene f',True),[
            ('(locals : E1M1GridLocals.Safe (s.regs 4) lines)','(locals : True)'),
            ('after.collected 0','after.collected 1'),
            ('steps≤427+','steps≤426+')])

    def test_next_cell_needs_nonendpoint_and_has_count_one(self):
        self.mutations(self.contract('E1M1FiringCollectionAdvance','next_cell',FULL+' room world dimension ids scene f notEnd',True),[
            ('(notEnd : E1M1PathAdvance.ended (initial (path thing angle ox oy) xout yout)=false)','(notEnd : True)'),
            ('out.core.regs 7=(1#32)','out.core.regs 7=(0#32)'),
            ('out.pc=0x2ca7f','out.pc=0x2cafd')])

if __name__=='__main__':unittest.main()

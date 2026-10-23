"""Repeated cells require initial images, one shared budget and real continuation."""
import re
import unittest
from pathlib import Path
import test_e1m1_cell_advance as prior
import verify_e1m1_cell_walk as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1CellAdvance','import Doom.Proofs.E1M1CellWalkLimit')
HEADER=HEADER.replace('open E1M1PathAdvance (Cell observe step nextPc)','open E1M1PathAdvance (observe step nextPc)')
HEADER+='open E1M1CellWalkInvariant\nopen E1M1CellWalk (Follows stopPc)\n'
HEADER+='open E1M1PathAdvance (step nextPc ended)\n'
HEADER+='attribute [local irreducible] E1M1CellWalk.grid E1M1CellWalk.history E1M1CellWalk.stopPc E1M1CellWalk.next E1M1PathAdvance.nextPc\n'
WALK='q cells s r seen common statics state images entry follows room'

class CellWalkTests(unittest.TestCase):
    lean=prior.CellAdvanceTests.lean
    succeeds=prior.CellAdvanceTests.succeeds
    rejects=prior.CellAdvanceTests.rejects
    mutations=prior.CellAdvanceTests.mutations

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
                    out+'extra',out.replace('CellWalkInvariant.caller_safe','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_future_images_require_initial_memory_and_static_protection(self):
        self.mutations(self.contract('E1M1CellWalkInvariant','images_transport','q cells m n statics images frame'),[
            ('(statics : ∀ c∈cells, Static q c)','(statics : True)'),
            ('(images : Images q cells m)','(images : True)'),
            ('(frame : E1M1CellMapInvariant.Frame q.sp q.lines m n)','(frame : True)')])

    def test_candidate_budget_is_consumed_across_cells(self):
        self.mutations(self.contract('E1M1CellWalkInvariant','budget_tail','c rest before after room used'),[
            ('(room : before+budget (c::rest)≤128)','(room : before+budget rest≤128)'),
            ('(used : after≤before+cost c)','(used : True)'),
            ('after+budget rest≤128 :=','after+budget rest≤127 :=')])

    def test_walk_cannot_assume_reached_images_or_ignore_later_capacity(self):
        self.mutations(self.contract('E1M1CellWalk','execution',WALK),[
            ('(images : Images q cells s.core.memory)','(images : True)'),
            ('(statics : ∀ c∈cells, Static q c)','(statics : True)'),
            ('(room : r.collected.size+budget cells≤128)','(room : r.collected.size≤128)')])

    def test_walk_requires_the_original_route_and_intermediate_control(self):
        self.mutations(self.contract('E1M1CellWalk','execution',WALK),[
            ('(entry : cells≠[] → s.pc=0x2ca7f)','(entry : True)'),
            ('(follows : Follows (E1M1PathAdvance.observe s.core) cells)','(follows : True)'),
            ('out.pc=stopPc s.pc (E1M1PathAdvance.observe s.core) cells','out.pc=0x2ca7f')])

    def test_walk_preserves_updated_history_numeric_state_and_bound(self):
        self.mutations(self.contract('E1M1CellWalk','execution',WALK),[
            ('State q out after (history q seen cells)','State q out after seen'),
            ('E1M1PathAdvance.observe out.core=grid (E1M1PathAdvance.observe s.core) cells',
             'E1M1PathAdvance.observe out.core=E1M1PathAdvance.observe s.core'),
            ('n≤bound cells','n≤bound cells-1')])

    def test_limit_requires_legal_counter_and_actual_continuation(self):
        self.mutations(self.contract('E1M1CellWalkLimit','continuation','g n legal counter go'),[
            ('(legal : n<64)','(legal : True)'),
            ('(counter : g.count=BitVec.ofNat 32 n)','(counter : True)'),
            ('(go : nextPc g=0x2ca7f)','(go : True)')])
        self.mutations(self.contract('E1M1CellWalkLimit','length_bound','g n cells legal counter follows'),[
            ('(follows : Follows g cells)','(follows : True)'),
            ('cells.length≤64-n :=','cells.length≤63-n :=')])

    def test_exhaustion_is_an_exit_only_with_the_full_legal_budget(self):
        self.mutations(self.contract('E1M1CellWalkLimit','exhausted','pc g n cells legal counter follows full'),[
            ('(full : cells.length=64-n)','(full : True)'),
            ('(legal : n<64)','(legal : True)'),
            ('stopPc pc g cells=0x2cafd :=','stopPc pc g cells=0x2ca7f :=')])

    def test_counter_edge_cases_stall_endpoint_and_signed_wrap(self):
        self.succeeds('''import Doom.Proofs.E1M1CellWalkLimit
open Doom Doom.Proofs Doom.Verification X86
open E1M1PathAdvance
-- Neither axis matches: the original still spends one iteration.
def stalled : Cell := ⟨2,3,9,9,0,0,1,1,0,0,62⟩
example : (step stalled).mapX=2 ∧ (step stalled).mapY=3 ∧
    (step stalled).count=63 ∧ nextPc stalled=0x2ca7f := by decide +kernel
example : nextPc (step stalled)=0x2cafd := by decide +kernel
example : nextPc {stalled with mapX:=9,mapY:=9}=0x2cafd := by decide +kernel
-- A negative signed counter can continue, so legality cannot be dropped.
example : nextPc {stalled with count:=0xffffffff}=0x2ca7f := by decide +kernel
''')

if __name__=='__main__':unittest.main()

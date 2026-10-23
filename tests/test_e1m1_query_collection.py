"""Entry images and the original setup must feed the actual collection theorem."""
import re
import unittest
from pathlib import Path
import test_e1m1_query_init as prior
import verify_e1m1_query_collection as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1QueryCollection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1PathMapSetup (grid Safe StackSafe)
attribute [local irreducible] load32
'''
FIXTURE=prior.FIXTURE.replace('import Doom.Proofs.E1M1QuerySource','import Doom.Proofs.E1M1QueryCollection')
EXECUTION='q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads room'

class QueryCollectionTests(unittest.TestCase):
    lean=prior.QueryInitTests.lean
    succeeds=prior.QueryInitTests.succeeds
    rejects=prior.QueryInitTests.rejects
    mutations=prior.QueryInitTests.mutations

    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',s[a:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('QueryImages.globals','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_trace_and_active_globals_come_from_actual_initialization(self):
        self.mutations(self.contract('E1M1QueryImages','globals','s ox oy sx sy ex ey geometry options traceSafe activeSafe'),[
            ('(options : load32 s.memory (s.regs 4+4)=3)','(options : load32 s.memory (s.regs 4+4)=7)'),
            ('(activeSafe : StackSafe (s.regs 4-60) 0x2c024)','(activeSafe : True)'),
            ('(geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)','(geometry : True)')])

    def test_map_join_requires_actual_options_and_protection(self):
        self.mutations(self.contract('E1M1QueryImages','map','s q ox oy sx sy ex ey geometry stack options flagSafe input'),[
            ('(stack : s.regs 4=q.sp-52)','(stack : s.regs 4=q.sp-48)'),
            ('(flagSafe : Safe s (E1M1ThingGate.flagWord q.sp))','(flagSafe : True)')])

    def test_cell_images_need_initial_payload_and_matching_trace(self):
        self.mutations(self.contract('E1M1QueryImages','cell','s q c ox oy sx sy ex ey geometry trace options traceSafe activeSafe payload safe'),[
            ('(payload : Payload s.memory q c)','(payload : True)'),
            ('(safe : Protected s q c)','(safe : True)'),
            ('(trace : q.trace=(Collision.pathStart ox oy sx sy ex ey).trace)','(trace : True)')])

    def test_prefix_keeps_real_entry_exit_and_axis_success(self):
        self.mutations(self.contract('E1M1QueryPrefix','execution','s f ox oy sx sy ex ey geometry xout yout okX okY'),[
            ('⟨s,f,0x2c8a0⟩','⟨s,f,0x2ca7f⟩'),
            ('(okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)','(okY : True)')])

    def test_complete_join_requires_entry_memory_and_one_total_budget(self):
        self.mutations(self.contract('E1M1QueryCollection','execution',EXECUTION),[
            ('(entry : Entry q s sx sy ex ey)','(entry : True)'),
            ('(room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤128)',
             '(room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤129)')])

    def test_complete_join_preserves_history_final_state_and_exit(self):
        self.mutations(self.contract('E1M1QueryCollection','execution',EXECUTION),[
            ('State q out after (history q seen cells)','State q out after seen'),
            ('E1M1PathAdvance.observe out.core=E1M1CellWalk.grid g cells','E1M1PathAdvance.observe out.core=g'),
            ('out.pc=0x2cafd','out.pc=0x2ca7f')])

    def test_live_remainder_requires_success_and_same_result(self):
        self.mutations(self.contract('E1M1QueryCollection','query_tail',
            'q sx sy ex ey profile trace xout yout okX okY g seen after collected visit'),[
            ('.ok (E1M1LoopReplay.pack g seen after)', '.error "collection failed"'),
            ('E1M1QuerySource.visitHits after visit','E1M1QuerySource.visitHits {after with completed:=false} visit')])

    def test_ordered_tail_keeps_equal_fraction_order_range_and_visitor_stop(self):
        self.succeeds(FIXTURE+'''
def hits : Collision.PathResult := {r with collected:=#[⟨⟨32768⟩,true,4⟩,⟨⟨32768⟩,false,5⟩,⟨⟨65537⟩,true,6⟩]}
example : (visitHits hits (fun _ _ => true)).toOption.map
    (fun r => (r.visited.toList.map (fun hit => hit.id),r.completed)) = some ([4,5],true) := by decide +kernel
example : (visitHits hits (fun _ _ => false)).toOption.map
    (fun r => (r.visited.toList.map (fun hit => hit.id),r.completed)) = some ([4],false) := by decide +kernel
''')

if __name__=='__main__':unittest.main()

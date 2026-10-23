"""Guard the joined clipping cycle and reusable callback-entry conditions."""
import re
import unittest
from pathlib import Path
import test_e1m1_history_dispatch as prior
import verify_e1m1_aim_history_cycle as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimCycleInvariant
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1SelectionHistory (History)
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimRepeatProgram (ReadFrame)
open E1M1AimHistoryCycle (Frame Next)
open E1M1AimCycleInvariant (Layout QuerySafe)
attribute [local irreducible] load32 store32
'''
NEXT_ARGS='s f initial hits seen visits resolve target sp fraction j history selection line front back ff fc bf bc h bounded safe returnSafe go stable cursorSafe targetSafe cursorStore recordSafe'
class AimHistoryCycleTests(unittest.TestCase):
    lean=prior.HistoryDispatchTests.lean
    succeeds=prior.HistoryDispatchTests.succeeds
    rejects=prior.HistoryDispatchTests.rejects
    mutations=prior.HistoryDispatchTests.mutations
    def contract(self,module,name,args):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r'(?: | :)',source,re.M).start()
        decl=source[start:source.index(' := by',start)]
        decl=re.sub(r'\bprogram\b','E1M1AimRepeatProgram.program',decl)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_complete_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),42)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimHistoryCycle.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_resume_uses_selected_entry_and_real_continue_branch(self):
        self.mutations(self.contract('E1M1AimHistoryCycle','next',NEXT_ARGS),[
            ('(selection : Selection initial hits seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)','(selection : True)'),
            ('(go : (E1M1AimWindow.result s).core.regs 0≠0)','(go : True)'),
            ('(cursorStore : Apart 0x2c028 (s.regs 4))','(cursorStore : True)'),
            ('initial (consume hits j) (j::seen) resolve out','initial hits seen resolve out')])
    def test_cycle_preserves_computed_bounds_and_actual_stop_exit(self):
        self.mutations(self.contract('E1M1AimHistoryCycle','execution',proof.CYCLE_ARGS),[
            ('out.pc=0x2c88c','out.pc=0x2c887'),
            ('load32 out.core.memory (0x2c1e4#32)=(if bf=ff then lower.raw else max lower.raw floorSlope.raw).toBitVec','load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec'),
            ('load32 out.core.memory (0x2c1e8#32)=(if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toBitVec','load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec'),
            ('⟨s,f,0x2b760⟩ out','⟨s,f,0x2c83a⟩ out')])
    def test_layout_transport_requires_same_actual_stack(self):
        self.mutations(self.contract('E1M1AimCycleInvariant','layout','s t hits j sameStack safe'),[
            ('(sameStack : t.regs 4=s.regs 4)','(sameStack : True)'),
            ('(safe : Layout s hits)','(safe : True)')])
        self.mutations(self.contract('E1M1AimCycleInvariant','stack','s initial work seen resolve target out distance j selection'),[
            ('out.core.regs 4=s.regs 4','out.core.regs 4=s.regs 4+4')])
    def test_next_record_is_the_original_selected_record(self):
        self.mutations(self.contract('E1M1AimCycleInvariant','record',
            'initial work seen visits resolve target sp out distance j history selection'),[
            ('(history : History initial work seen visits)','(history : True)'),
            ('initial[j]! (resolve initial[j]!)','initial[j+1]! (resolve initial[j+1]!)'),
            ('out.core.memory (out.core.regs 0)','out.core.memory (out.core.regs 0+4)')])
    def test_query_words_require_protection_and_cycle_frame(self):
        self.mutations(self.contract('E1M1AimCycleInvariant','query_words','s out frame safe'),[
            ('(frame : Frame s out)','(frame : True)'),
            ('(safe : QuerySafe s)','(safe : True)'),
            ('load32 s.memory (0x2b9a8#32)','load32 s.memory (0x2b9b8#32)')])
    def test_query_protection_handles_new_selected_pointer(self):
        self.mutations(self.contract('E1M1AimCycleInvariant','query_safe',
            's initial work seen resolve target out distance j selection bounded safe'),[
            ('(bounded : initial.size≤128)','(bounded : True)'),
            ('(safe : QuerySafe s)','(safe : True)'),
            ('(selection : Selection initial work seen resolve target (s.regs 4+4) out distance j)','(selection : True)')])
    def test_next_entry_uses_pre_cycle_conditions_and_real_memory_frame(self):
        self.mutations(self.contract('E1M1AimCycleInvariant','entry',proof.ENTRY_ARGS),[
            ('(safe : Layout s hits)','(safe : True)'),
            ('(querySafe : QuerySafe s)','(querySafe : True)'),
            ('(frame : Frame s out)','(frame : True)'),
            ('load32 out.core.memory (0x2b9b8#32)=load32 s.memory (0x2b9b8#32)','load32 out.core.memory (0x2b9b8#32)=0')])
if __name__=='__main__':unittest.main()

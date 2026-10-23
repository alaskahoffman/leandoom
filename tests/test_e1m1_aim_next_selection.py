"""Check the consumed buffer, preserved fields and authentic repeat edge."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_line_join as prior
import verify_e1m1_aim_next_selection as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimNextSelection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1FirstIntercept (program)
attribute [local irreducible] load32 store32
'''
AFTER_ARGS='s hit line front back ff fc bf bc h hits resolve j inside bounded image safe returnSafe pointer go stable cursorSafe cursor maximum targetSafe recordSafe'
class AimNextSelectionTests(unittest.TestCase):
    lean=prior.AimLineJoinTests.lean
    succeeds=prior.AimLineJoinTests.succeeds
    rejects=prior.AimLineJoinTests.rejects
    mutations=prior.AimLineJoinTests.mutations
    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_pins_loop_and_scan_and_audits_every_theorem(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),42)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out+'extra',out.replace('AimNextSelection.after_callback','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        for name,index,old,new in [('interceptSetup',44,0x4e,0x46),('interceptMinimum',16,0x7e,0x7c)]:
            changed=dict(raw);b=bytearray(raw[name]);self.assertEqual(b[index],old);b[index]=new;changed[name]=bytes(b)
            self.rejects(proof.certificate(data,changed))
    def test_mark_requires_in_bounds_and_stable_resolved_pointer(self):
        self.mutations(self.contract('E1M1InterceptMark','encoded','m hits resolve j inside bounded image stable'),[
            ('(inside : j<hits.size)','(inside : True)'),
            ('(stable : resolve {hits[j]! with frac := ⟨2147483647⟩}=resolve hits[j]!)','(stable : True)'),
            ('(store32 m (address j) 0x7fffffff)','(store32 m (address j) 0)'),
            ('resolve (consume hits j)','resolve hits')])
    def test_record_frame_requires_all_callback_writes_separated(self):
        self.mutations(self.contract('E1M1AimRecordFrame','records','s hit line front back ff fc bf bc h hits resolve image safe'),[
            ('(safe : RecordsSafe s hits)','(safe : True)'),
            ('(image : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)','(image : True)')])
    def test_next_selection_uses_updated_buffer_and_initial_cursor(self):
        self.mutations(self.contract('E1M1AimNextSelection','after_callback',AFTER_ARGS),[
            ('(pointer : s.regs 3=address j)','(pointer : True)'),
            ('(go : (E1M1AimWindow.result s).core.regs 0≠0)','(go : True)'),
            ('(cursor : load32 s.memory 0x2c028=address hits.size)','(cursor : True)'),
            ('Outcome (E1M1AimResume.result s).core (E1M1InterceptMark.consume hits j) resolve out','Outcome (E1M1AimResume.result s).core hits resolve out')])
    def test_callback_target_is_preserved_not_assumed_after_the_call(self):
        self.mutations(self.contract('E1M1AimNextSelection','carried_outcome','s hit line front back ff fc bf bc h returnSafe cursorSafe slotSafe markSafe hits resolve out done'),[
            ('(slotSafe : E1M1AimRecordFrame.ReadSafe s (s.regs 4+4))','(slotSafe : True)'),
            ('(markSafe : Apart (s.regs 4+4) (s.regs 3))','(markSafe : True)'),
            ('(load32 s.memory (s.regs 4+4)) (s.regs 4+4) out','(load32 s.memory (s.regs 4)) (s.regs 4+4) out')])
    def test_zero_counter_exits_but_still_wraps_decrement(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (zero : s.regs 6=(0#32)) :
    (E1M1AimNextSelection.head s).pc=0x2c887 ∧
    (E1M1AimNextSelection.head s).core.regs 6=0xffffffff := by
  simp [E1M1AimNextSelection.head,put,write,zero]
example (s : X86Memory.State) (one : s.regs 6=(1#32)) :
    (E1M1AimNextSelection.head s).pc=0x2c841 ∧
    (E1M1AimNextSelection.head s).core.regs 6=0 := by
  simp [E1M1AimNextSelection.head,put,write,one]
''')
if __name__=='__main__':unittest.main()

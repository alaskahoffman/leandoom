"""Guard terminal stack recovery and the real callback push across scans."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_saved_caller as prior
import verify_e1m1_aim_scan_stack as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimScanCaller\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimCompletedReturn.result E1M1AimTraversalReturn.result
attribute [local irreducible] E1M1AimActorSkip.result E1M1AimActorReject.result E1M1AimActorBottomReject.result E1M1AimResume.result
'''
class AimScanStackTests(unittest.TestCase):
    lean=prior.AimSavedCallerTests.lean
    succeeds=prior.AimSavedCallerTests.succeeds
    rejects=prior.AimSavedCallerTests.rejects
    mutations=prior.AimSavedCallerTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimScanStack.terminal','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_terminal_needs_distinct_callback_destination(self):
        self.mutations(self.contract('E1M1AimScanStack','terminal','target base out position distinct exit'),[
            ('(distinct : target.toNat≠0x2c887)','(distinct : True)'),
            ('out.core.regs 4=base :=','out.core.regs 4=base-4 :=')])
        # A deliberately colliding indirect destination really can have the
        # pushed stack at the exit PC: distinctness is a necessary premise.
        self.succeeds(HEADER+'''
example : ∃ out : X86Control.State,
    E1M1AimScanStack.Position 0x2c887 0 out ∧ out.pc=0x2c887 ∧ out.core.regs 4≠0 := by
  let out : X86Control.State := ⟨⟨fun _ => 0xfffffffc,fun _ => 0⟩,none,0x2c887⟩
  exact ⟨out,Or.inr ⟨rfl,rfl⟩,rfl,by decide⟩
''')
    def test_callback_push_and_wraparound_are_exact(self):
        self.mutations(self.contract('E1M1AimScanStack','callback','target base out position live'),[
            ('out.core.regs 4=base-4','out.core.regs 4=base'),
            ('(live : out.pc≠0x2c887)','(live : True)')])
        self.succeeds(HEADER+'''
example (out : X86Control.State)
    (position : E1M1AimScanStack.Position 0x2b760 0 out) (live : out.pc≠0x2c887) :
    out.core.regs 4=0xfffffffc := (E1M1AimScanStack.callback _ _ _ position live).2
example (out : X86Control.State)
    (position : E1M1AimScanStack.Position 0x2b760 (0xfffffffc+4) out)
    (exit : out.pc=0x2c887) : out.core.regs 4=0 :=
  E1M1AimScanStack.terminal _ _ _ position (by decide) exit
''')
    def test_dispatch_keeps_parent_base_and_real_entry_pc(self):
        self.mutations(self.contract('E1M1AimScanStack','dispatch',proof.DISPATCH_ARGS),[
            ('(pc : s.pc=(if hits.size=0 then 0x2c887 else 0x2c841))','(pc : True)'),
            ('Doom.Proofs.E1M1AimScanStack.Position (load32 s.core.memory (s.core.regs 4)) (s.core.regs 4) out',
             'Doom.Proofs.E1M1AimScanStack.Position (load32 s.core.memory (s.core.regs 4)) (s.core.regs 4+4) out')])
    def test_history_dispatch_requires_remaining_counter_and_authentic_buffer(self):
        self.mutations(self.contract('E1M1AimScanStack','execution',proof.HISTORY_ARGS),[
            ('(counter : s.regs 6=BitVec.ofNat 32 (initial.size-seen.length))','(counter : True)'),
            ('(encoded : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve work)','(encoded : True)')])
    def test_ignored_actor_scan_uses_returned_stack_base(self):
        self.mutations(self.contract('E1M1AimActorScanStack','skipped',proof.SKIP_ARGS),[
            ('(s.regs 4+4) out :=','(s.regs 4) out :='),
            ('(layout : E1M1AimCycleInvariant.Layout s work)','(layout : True)')])
    def test_both_rejection_scans_preserve_stack_and_require_resolver_stability(self):
        for name in ['top_rejected','bottom_rejected']:
            self.mutations(self.contract('E1M1AimActorScanStack',name,proof.REJECT_ARGS),[
                ('(stable : resolve {work[j]! with frac:=⟨2147483647⟩}=resolve work[j]!)','(stable : True)'),
                ('(s.regs 4+4) out :=','(s.regs 4) out :=')])
    def test_actor_destinations_are_derived_from_entry_invariant(self):
        for name in ['skipped_position','top_rejected_position','bottom_rejected_position']:
            self.mutations(self.contract('E1M1AimActorScanStack',name,proof.ACTOR_POSITION_ARGS),[
                ('(pointer : s.regs 3=Doom.Proofs.E1M1MinimumScan.address marked)','(pointer : True)'),
                ('(inside : marked<initial.size)','(inside : True)')])
    def test_line_scan_needs_continue_and_slot_write_protection(self):
        self.mutations(self.contract('E1M1AimLineScanStack','execution',proof.LINE_ARGS),[
            ('(go : (E1M1AimWindow.result s).core.regs 0≠0)','(go : True)'),
            ('(s.regs 4+4) out :=','(s.regs 4) out :=')])
        self.mutations(self.contract('E1M1AimLineScanStack','position',proof.LINE_POSITION_ARGS),[
            ('(slotMark : Apart (s.regs 4+4) (s.regs 3))','(slotMark : True)'),
            ('(target : load32 s.memory (s.regs 4+4)=0x2b760)','(target : True)')])
    def test_scan_return_uses_proved_position_not_an_esp_premise(self):
        source=self.contract('E1M1AimScanCaller','execution',proof.RETURN_ARGS)
        self.assertNotIn('(stack :',source)
        self.mutations(source,[
            ('(position : E1M1AimScanStack.Position 0x2b760 base finish)','(position : True)'),
            ('(image : E1M1AimSavedCaller.Image start finish base)','(image : True)'),
            ('(exit : E1M1AimHitMemory.Exit initial resolve finish answer)','(exit : True)')])
if __name__=='__main__':unittest.main()

"""Guard RET imm16 semantics and the complete, conditional DOS aiming return."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_traversal_return as prior
import verify_e1m1_aim_completed_return as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimCompletedReturn\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimTraversalReturn.result E1M1AimCompletedReturn.result X86ReturnCleanup.returned
'''
class AimCompletedReturnTests(unittest.TestCase):
    lean=prior.AimTraversalReturnTests.lean
    succeeds=prior.AimTraversalReturnTests.succeeds
    rejects=prior.AimTraversalReturnTests.rejects
    mutations=prior.AimTraversalReturnTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  '+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('X86ReturnCleanup.lift','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem ([\w.]+)(?: |\s*:)',(ROOT/(module.replace('.','/')+'.lean')).read_text(),re.M))
    def test_decoder_reads_unsigned_little_endian_and_rejects_truncation(self):
        self.succeeds(HEADER+'''
example : X86ReturnCleanup.decodeAt [0xc2,8,0] 0=some (.retCleanup 8,3) := by decide
example : X86ReturnCleanup.decodeAt [0xc2,0,0x80] 0=some (.retCleanup 0x8000,3) := by decide
example : X86ReturnCleanup.decodeAt [0x90,0xc2,0xff,0xff] 1=some (.retCleanup 0xffff,3) := by decide
example : X86ReturnCleanup.decodeAt [0xc2] 0=none := by decide
example : X86ReturnCleanup.decodeAt [0xc2,8] 0=none := by decide
example : X86ReturnCleanup.decodeAt [0xc3] 0=some (.prior .ret,1) := by decide
-- The original decoder is unchanged; support is opt-in.
example : X86Routine.decodeAt [0xc2,8,0] 0=none := by decide
''')
    def test_cleanup_uses_old_stack_unsigned_immediate_and_preserves_flags(self):
        self.mutations(self.contract('Doom.Verification.X86ReturnCleanup','layout','bytes s'),[
            ('s.core.regs 4+4+bytes.zeroExtend 32','s.core.regs 4+bytes.zeroExtend 32'),
            ('bytes.zeroExtend 32','bytes.signExtend 32'),
            ('(load32 s.core.memory (s.core.regs 4)).toNat','(load32 s.core.memory (s.core.regs 4+4)).toNat'),
            ('.flags=s.flags','.flags=none')])
    def test_prior_prefix_lifts_without_state_changes(self):
        source=HEADER+'''
example {cm p exits n s t} (path : X86CodeMemory.Prefix cm p exits n s t) :
    X86ReturnCleanup.Prefix cm (X86ReturnCleanup.embed p) exits n s t :=
  X86ReturnCleanup.lift path
'''
        self.mutations(source,[('exits n s t :=','exits n s s :='),('exits n s t :=','exits (n+1) s t :=')])
        self.mutations(self.contract('Doom.Verification.X86ReturnCleanup','zero_cleanup','cm s'),[
            ('(.retCleanup 0)','(.retCleanup 8)')])
    def test_actual_execution_needs_both_saved_return_addresses(self):
        self.mutations(self.contract('Doom.Proofs.E1M1AimCompletedReturn','execution','s exit safe20 address20 safe84 address84'),[
            ('(address20 : load32 s.core.memory (s.core.regs 4+20)=0x2cb0b)','(address20 : True)'),
            ('(address84 : load32 s.core.memory (s.core.regs 4+84)=0x2bbff)','(address84 : True)'),
            ('(safe84 : Apart (s.core.regs 4+84) 0x2c028)','(safe84 : True)')])
    def test_caller_frame_requires_separation_from_final_cursor_write(self):
        self.mutations(self.contract('Doom.Proofs.E1M1AimCompletedReturn','saved_caller','s safe'),[
            ('(safe : ∀ off∈[(96#32),100,104,108,112], Apart (s.core.regs 4+off) 0x2c028)','(safe : True)'),
            ('regs 5=load32 s.core.memory (s.core.regs 4+96)','regs 5=load32 s.core.memory (s.core.regs 4+100)')])
    def test_final_eax_requires_exit_correspondence_and_nonnull_resolver(self):
        self.mutations(self.contract('Doom.Proofs.E1M1AimCompletedReturn','value','initial resolve s answer exit nonnull'),[
            ('(exit : E1M1AimHitMemory.Exit initial resolve s answer)','(exit : True)'),
            ('(nonnull : ∀ j<initial.size, resolve initial[j]!≠0)','(nonnull : True)'),
            ('answer.slope.raw.toBitVec','(0#32)')])
    def test_final_stack_and_return_address_offsets(self):
        self.mutations(self.contract('Doom.Proofs.E1M1AimCompletedReturn','layout','s'),[
            ('regs 4=s.core.regs 4+116','regs 4=s.core.regs 4+108'),
            ('(s.core.regs 4+112)).toNat','(s.core.regs 4+104)).toNat')])
    def test_appended_chain_keeps_endpoint_obligations(self):
        self.mutations(self.contract('Doom.Proofs.E1M1AimCompletedReturn','append','start finish steps run exit safe20 address20 safe84 address84'),[
            ('(address84 : load32 finish.core.memory (finish.core.regs 4+84)=0x2bbff)','(address84 : True)'),
            ('(safe20 : Apart (finish.core.regs 4+20) 0x2c028)','(safe20 : True)'),
            ('n start (Doom.Proofs.E1M1AimCompletedReturn.result finish)','n start (Doom.Proofs.E1M1AimCompletedReturn.result start)')])
    def test_pinned_ret8_immediate_and_aim_target_bytes_cannot_change(self):
        data,_=proof.pinned_data();_,_,raw=proof.extracted()
        # Check byte equalities directly; the complete authenticated certificate
        # is independently checked above.
        for key,definition,offset in [('pathRet8','OriginalPathReturn.code',1),('aimReturn','OriginalAimQuery.retBytes',2)]:
            code=list(raw[key]);literal=lambda:'['+','.join(map(str,code))+']'
            self.succeeds(HEADER+'example : ('+literal()+' : List UInt8)='+definition+' := by decide\n')
            code[offset]^=1
            self.rejects(HEADER+'example : ('+literal()+' : List UInt8)='+definition+' := by decide\n')
if __name__=='__main__':unittest.main()

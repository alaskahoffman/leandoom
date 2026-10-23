"""Check the authentic final branch, return-frame provenance and decoder extension."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_ceiling as prior
import verify_e1m1_aim_window as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimWindow
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32
'''
class AimWindowTests(unittest.TestCase):
    lean=prior.AimCeilingTests.lean
    succeeds=prior.AimCeilingTests.succeeds
    rejects=prior.AimCeilingTests.rejects
    mutations=prior.AimCeilingTests.mutations
    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_bytes_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),42)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimWindow.restored','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        for name,index,value in [('aimWindow',12,0x8d),('aimWindow',13,0x8d),('aimWindow',19,0x5f),('aimContinue',1,0),('aimContinue',11,0x90)]:
            changed=dict(raw);b=bytearray(raw[name]);self.assertNotEqual(b[index],value);b[index]=value
            changed[name]=bytes(b);self.rejects(proof.certificate(data,changed))
    def test_near_jg_decoder_lengths_signed_offsets_and_faults(self):
        source=HEADER+'''
example : X86Routine.decode [0x0f,0x8f,0xff,0xff,0xff,0xff,0x90] = some (.jumpSigned 2 (-1),[0x90]) := by decide
example : X86Routine.decodeAt [0x0f,0x8f,0,0,0,0x80,0x90] 0 = some (.jumpSigned 2 (-2147483648),6) := by decide
example : X86Routine.decode [0x0f,0x8f,0,0,0] = none := by decide
example : X86Routine.decode [0x0f,0x8d,1,0,0,0] = some (.jumpSigned 0 1,[]) := by decide
example : X86Routine.decode [0x0f,0x8e,1,0,0,0] = some (.jumpSigned 1 1,[]) := by decide
example : X86Routine.decode [0x7f,0xff] = some (.jumpSigned 2 (-1),[]) := by decide
example (s : X86Memory.State) : X86Routine.execute (.jumpSigned 2 140) ⟨s,none,6⟩ = none := rfl
example (s : X86Memory.State) : X86Routine.execute (.jumpSigned 2 (-1)) ⟨s,some (compare32 1 0),0⟩ = none := by rfl
example (s : X86Memory.State) : X86Routine.execute (.jumpSigned 2 1) ⟨s,some (compare32 1 0),4294967295⟩ = none := by rfl
'''
        self.succeeds(source)
    def test_signed_window_edges_and_equality_stop(self):
        source=HEADER
        pairs=[(0,0),(1,0),(0,1),(-1,-1),(-2147483648,2147483647),(2147483647,-2147483648),(-1,0),(0,-1)]
        for upper,lower in pairs:
            target=146 if upper>lower else 6
            source+=f'''example : (X86Routine.execute (.jumpSigned 2 140)
  ⟨⟨fun _=>0,fun _=>0⟩,some (compare32 (BitVec.ofInt 32 ({upper})) (BitVec.ofInt 32 ({lower}))),6⟩).map (·.pc)=some {target} := by decide
'''
        self.succeeds(source)
    def test_frame_requires_global_and_helper_stack_separation(self):
        self.mutations(self.contract('E1M1AimReturnFrame','frame','s hit line front back ff fc bf bc a h safe'),[
            ('(safe : ∀ b∈writes (s.regs 4), Apart a b)','(safe : True)')])
        self.mutations(self.contract('E1M1AimReturnFrame','saved_slot','s hit line front back ff fc bf bc off h safe member'),[
            ('(safe : Safe s)','(safe : True)'),('(member : off∈slots)','(member : True)')])
    def test_restoration_is_from_initial_frame_and_original_return(self):
        self.mutations(self.contract('E1M1AimWindow','restored','s hit line front back ff fc bf bc h safe'),[
            ('(safe : E1M1AimReturnFrame.Safe s)','(safe : True)'),
            ('(result s).core.regs 4=s.regs 4+(4#32)','(result s).core.regs 4=s.regs 4'),
            ('(load32 s.memory (s.regs 4)).toNat','(load32 s.memory (s.regs 4+(4#32))).toNat'),
            ('(result s).core.regs 6=s.regs 6','(result s).core.regs 6=s.regs 7')])
    def test_complete_callback_requires_real_clipping_and_return_contract(self):
        args='s f hit line front back ff fc bf bc distance z lower upper floorSlope ceilingSlope h distanceReads floorReads reads clip range eye bottom top pass floorOk ceilingOk returnSafe'
        self.mutations(self.contract('E1M1AimWindow','execution',args),[
            ('(returnSafe : E1M1AimReturnFrame.Safe s)','(returnSafe : True)'),
            ('(clip : E1M1AimCeilingEntry.ClipSafe s line front back)','(clip : True)'),
            ('max lower.raw floorSlope.raw','min lower.raw floorSlope.raw'),
            ('then 1 else 0','then 0 else 1'),
            ('⟨s,f,0x2b760⟩','⟨s,f,0x2b800⟩')])
    def test_return_values_and_stack_offsets_are_not_interchangeable(self):
        self.mutations(self.contract('OriginalAimWindow','result_fields','s'),[
            ('then 1 else 0','then 0 else 1'),
            ('s.regs 4+(28#32)','s.regs 4+(24#32)'),
            ('s.regs 4+(24#32)','s.regs 4+(20#32)')])
if __name__=='__main__':unittest.main()

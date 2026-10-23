"""Ceiling clipping must preserve the floor result and use authentic entry operands."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_floor as prior
import verify_e1m1_aim_ceiling as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimCeilingEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32
'''
class AimCeilingTests(unittest.TestCase):
    lean=prior.AimFloorTests.lean
    succeeds=prior.AimFloorTests.succeeds
    rejects=prior.AimFloorTests.rejects
    mutations=prior.AimFloorTests.mutations
    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_bytes_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),40)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimCeilingEntry.inputs','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        for name,index,value in [('aimCeiling',12,0x75),('aimCeiling',40,0x7e),('aimCeiling',26,0xd2),('division',0,0x52)]:
            changed=dict(raw);b=bytearray(raw[name]);self.assertNotEqual(b[index],value);b[index]=value
            changed[name]=bytes(b);self.rejects(proof.certificate(data,changed))
    def test_floor_and_ceiling_frames_require_write_separation(self):
        for module,name in [('E1M1AimClipFrame','floor_frame'),('E1M1AimCeiling','frame')]:
            self.mutations(self.contract(module,name,'s a safe'),[
                ('(safe : ∀ b∈writes (s.regs 4), Apart a b)','(safe : True)')])
        self.mutations(self.contract('E1M1AimClipFrame','floor_regs','s'),[
            ('(E1M1AimFloor.result s).core.regs 3=s.regs 0','(E1M1AimFloor.result s).core.regs 3=s.regs 3')])
    def test_ceiling_division_uses_saved_distance_and_success(self):
        self.mutations(self.contract('E1M1AimCeiling','division_success','s top z distance slope b z0 d ok'),[
            ('(b : OriginalAimCeiling.high s=top.raw.toBitVec)','(b : True)'),
            ('(z0 : OriginalAimCeiling.shootZ s=z.raw.toBitVec)','(z0 : True)'),
            ('(d : s.regs 3=distance.raw.toBitVec)','(d : s.regs 2=distance.raw.toBitVec)'),
            ('(ok : checkedPathDiv (top-z) distance=.ok slope)','(ok : True)')])
    def test_ceiling_entry_operands_need_initial_images_and_protection(self):
        self.mutations(self.contract('E1M1AimCeilingEntry','inputs','s hit line front back ff fc bf bc h clip reads'),[
            ('(h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)','(h : True)'),
            ('(clip : ClipSafe s line front back)','(clip : True)'),
            ('(reads : ReadSafe s)','(reads : True)'),
            ('OriginalAimCeiling.high (reached s)=(if bc.toInt≤fc.toInt then bc else fc)','OriginalAimCeiling.high (reached s)=(if bc.toInt≤fc.toInt then fc else bc)')])
    def test_joined_bounds_need_both_divisions_and_entry_values(self):
        args='s f hit line front back ff fc bf bc distance z lower upper floorSlope ceilingSlope h distanceReads floorReads reads clip range eye bottom top pass floorOk ceilingOk'
        self.mutations(self.contract('E1M1AimCeilingEntry','execution',args),[
            ('(floorReads : E1M1AimFloorEntry.ReadSafe s)','(floorReads : True)'),
            ('(clip : ClipSafe s line front back)','(clip : True)'),
            ('(top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)','(top : True)'),
            ('(ceilingOk : fc≠bc → checkedPathDiv (⟨Int32.ofBitVec (if bc.toInt≤fc.toInt then bc else fc)⟩-z)\n      (distance*hit.frac)=.ok ceilingSlope)','(ceilingOk : True)'),
            ('min upper.raw ceilingSlope.raw','max upper.raw ceilingSlope.raw'),
            ('max lower.raw floorSlope.raw','min lower.raw floorSlope.raw'),
            ('(result s).pc=0x2b800','(result s).pc=0x2b89d')])
    def test_actual_helper_and_upper_store_contracts(self):
        self.mutations(self.contract('E1M1AimCeiling','execution','s f safe'),[
            ('(safe : Safe s)','(safe : True)'),('⟨s,f,0x2b7d1⟩','⟨s,f,0x2b7df⟩')])
        self.mutations(self.contract('E1M1AimCeiling','upper_update','s slope safe value'),[
            ('(safe : UpperSafe s)','(safe : True)'),
            ('(value : OriginalAimCeiling.fc s≠OriginalAimCeiling.bc s →\n      (divided s).core.regs 0=slope.raw.toBitVec)','(value : True)')])
if __name__=='__main__':unittest.main()

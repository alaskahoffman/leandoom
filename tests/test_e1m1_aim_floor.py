"""Reject incorrect floor branches, lost entry premises, and altered machine bytes."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_distance as prior
import verify_e1m1_aim_floor as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimFloorEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32
'''
class AimFloorTests(unittest.TestCase):
    lean=prior.AimDistanceTests.lean
    succeeds=prior.AimDistanceTests.succeeds
    rejects=prior.AimDistanceTests.rejects
    mutations=prior.AimDistanceTests.mutations
    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_bytes_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),39)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimFloorEntry.inputs','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        for name,index,value in [('aimFloor',12,0x75),('aimFloor',36,0x7f),('aimFloor',26,0xbd),('division',0,0x52)]:
            changed=dict(raw);b=bytearray(raw[name]);self.assertNotEqual(b[index],value);b[index]=value
            changed[name]=bytes(b);self.rejects(proof.certificate(data,changed))
    def test_actual_division_requires_successful_source_arithmetic(self):
        self.mutations(self.contract('E1M1AimFloor','division_success','s bottom z distance slope b z0 d ok'),[
            ('(b : OriginalAimFloor.low s=bottom.raw.toBitVec)','(b : True)'),
            ('(z0 : OriginalAimFloor.shootZ s=z.raw.toBitVec)','(z0 : True)'),
            ('(d : s.regs 2=distance.raw.toBitVec)','(d : True)'),
            ('(ok : checkedPathDiv (bottom-z) distance=.ok slope)','(ok : True)')])
    def test_lower_update_requires_real_value_and_memory_separation(self):
        self.mutations(self.contract('E1M1AimFloor','lower_update','s slope safe value'),[
            ('(safe : LowerSafe s)','(safe : True)'),
            ('(value : OriginalAimFloor.bf s≠OriginalAimFloor.ff s →\n      (divided s).core.regs 0=slope.raw.toBitVec)','(value : True)'),
            ('slope.raw.toInt≤(OriginalAimFloor.old s).toInt','slope.raw.toInt<(OriginalAimFloor.old s).toInt')])
    def test_entry_map_and_global_transport(self):
        self.mutations(self.contract('E1M1AimFloorEntry','inputs','s hit line front back ff fc bf bc h'),[
            ('(h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)','(h : True)'),
            ('OriginalAimFloor.ff (reached s)=ff','OriginalAimFloor.ff (reached s)=bf')])
        self.mutations(self.contract('E1M1AimFloorEntry','preserved','s safe'),[
            ('(safe : ReadSafe s)','(safe : True)')])
    def test_complete_prefix_requires_entry_operands_and_success(self):
        args='s f hit line front back ff fc bf bc distance z lower slope h distanceReads reads range eye bound pass ok'
        self.mutations(self.contract('E1M1AimFloorEntry','execution',args),[
            ('(reads : ReadSafe s)','(reads : True)'),
            ('(eye : load32 s.memory (0x2b9a8#32)=z.raw.toBitVec)','(eye : True)'),
            ('(bound : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)','(bound : True)'),
            ('(ok : bf≠ff → checkedPathDiv (⟨Int32.ofBitVec (if ff.toInt≤bf.toInt then bf else ff)⟩-z)\n      (distance*hit.frac)=.ok slope)','(ok : True)'),
            ('max lower.raw slope.raw','min lower.raw slope.raw'),
            ('(result s).pc=0x2b7d1','(result s).pc=0x2b8d2')])
    def test_path_requires_division_safety_and_correct_start(self):
        self.mutations(self.contract('E1M1AimFloor','execution','s f safe'),[
            ('(safe : Safe s)','(safe : True)'),
            ('⟨s,f,0x2b7a6⟩','⟨s,f,0x2b7b4⟩')])
if __name__=='__main__':unittest.main()

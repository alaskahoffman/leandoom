"""Guard bottom slope, two-division entry continuity and the original rejection return."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_actor_reject as prior
import verify_e1m1_aim_actor_bottom as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimActorBottomReject\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimActorBottomEntry.result E1M1AimActorBottomEntry.input
attribute [local irreducible] E1M1AimActorBottom.result E1M1AimActorBottom.divided
attribute [local irreducible] E1M1AimActorBottomReject.bottom E1M1AimActorBottomReject.result E1M1AimActorBottomReject.returned
'''
class AimActorBottomTests(unittest.TestCase):
    lean=prior.AimActorRejectTests.lean
    succeeds=prior.AimActorRejectTests.succeeds
    rejects=prior.AimActorRejectTests.rejects
    mutations=prior.AimActorRejectTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),46)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorBottomReject.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_authentic_bytes_mapping_and_relocations(self):
        spec,profile,raw=proof.extracted();part={'units':{'aimActorBottom':spec['units']['aimActorBottom']}}
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        for field,value in [('hex','90'+part['units']['aimActorBottom']['hex'][2:]),('file_offset','0x0'),('relocations',[])]:
            bad=copy.deepcopy(part);bad['units']['aimActorBottom'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,bad)
        data,_=proof.pinned_data();bad=dict(raw);bad['aimActorBottom']=bytes([0x90])+raw['aimActorBottom'][1:]
        self.rejects(proof.certificate(data,bad))
    def test_bottom_operand_uses_saved_distance_and_actor_z_without_height(self):
        self.mutations(self.contract('OriginalAimActorBottom','operands','s distance targetZ shootZ dist z0 eye0'),[
            ('(dist : s.regs 3=distance.raw.toBitVec)','(dist : True)'),
            ('(z0 : z s=targetZ.raw.toBitVec)','(z0 : True)'),
            ('(targetZ-shootZ).raw.toBitVec','(targetZ+shootZ).raw.toBitVec')])
    def test_second_division_and_exact_gate(self):
        args='s f distance targetZ shootZ upper slope dist z0 eye0 bound safe ok'
        self.mutations(self.contract('E1M1AimActorBottom','execution',args),[
            ('(ok : checkedPathDiv (targetZ-shootZ) distance=.ok slope)','(ok : True)'),
            ('if upper.raw<slope.raw then','if upper.raw≤slope.raw then'),
            ('core.regs 3=upper.raw.toBitVec','core.regs 3=distance.raw.toBitVec'),
            ('core.regs 6=s.regs 6','core.regs 6=s.regs 0'),
            ('n≤33','n≤32')])
    def test_complete_entry_requires_top_admission_and_preserves_both_slopes(self):
        self.mutations(self.contract('E1M1AimActorBottomEntry','execution',proof.EXEC_ARGS),[
            ('(admitted : ¬topSlope.raw<lower.raw)','(admitted : True)'),
            ('(safe : Doom.Proofs.E1M1AimActorBottomEntry.ReadSafe s pointer)','(safe : True)'),
            ('core.regs 0=bottomSlope.raw.toBitVec','core.regs 0=topSlope.raw.toBitVec'),
            ('core.regs 7=topSlope.raw.toBitVec','core.regs 7=bottomSlope.raw.toBitVec'),
            ('n≤89','n≤88')])
    def test_source_join_requires_strict_bottom_rejection_and_real_return(self):
        self.mutations(self.contract('E1M1AimActorBottomReject','execution',proof.REJECT_ARGS),[
            ('(above : upper.raw<bottomSlope.raw)','(above : upper.raw≤bottomSlope.raw)'),
            ('(admitted : ¬topSlope.raw<lower.raw)','(admitted : True)'),
            ('(identity : pointer=who ↔ hit.id=shooterId)','(identity : True)'),
            ('(returnWord : load32 s.memory (s.regs 4)=0x2c86d)','(returnWord : True)'),
            ('n≤102','n≤101'),
            ('range rest lower upper log','range rest upper lower log')])
    def test_return_restores_original_saves_and_parent_marks_original_hit(self):
        self.mutations(self.contract('E1M1AimActorBottomReject','returned_fields','s'),[
            ('core.regs 3=s.regs 3','core.regs 3=s.regs 0'),
            ('core.regs 6=s.regs 6','core.regs 6=s.regs 7'),
            ('core.regs 4=s.regs 4+4','core.regs 4=s.regs 4')])
        self.mutations(self.contract('E1M1AimActorBottomReject','frame','s a safe mark'),[
            ('(safe : Doom.Proofs.E1M1AimActorBottomReject.ReadSafe s a)','(safe : True)'),
            ('(mark : Apart a (s.regs 3))','(mark : True)')])
    def test_signed_gate_boundary_and_equality(self):
        self.succeeds('import Doom.Proofs.E1M1AimActorBottomReject\n'+proof.HEADER+'''
def sample (slope upper : BitVec 32) : X86Memory.State :=
  { regs:=fun _ => slope, memory:=store32 (fun _ => 0) 0x2c1e8 upper }
example : (OriginalAimActorBottom.gate (sample 0 0)).pc=0x2b8a9 := by decide
example : (OriginalAimActorBottom.gate (sample 1 0)).pc=0x2b89d := by decide
example : (OriginalAimActorBottom.gate (sample 0xffffffff 0)).pc=0x2b8a9 := by decide
example : (OriginalAimActorBottom.gate (sample 0x80000000 0x7fffffff)).pc=0x2b8a9 := by decide
example : (OriginalAimActorBottom.gate (sample 0x7fffffff 0x80000000)).pc=0x2b89d := by decide
example : (OriginalAimActorBottom.gate (sample 0x80000000 0x80000000)).pc=0x2b8a9 := by decide
''')
if __name__=='__main__':unittest.main()

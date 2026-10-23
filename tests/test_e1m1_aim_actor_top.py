"""Actor eligibility, bit-exact top-slope computation and source rejection contracts."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_actor_cycle as prior
import verify_e1m1_aim_actor_top as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimActorTopEntry\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimActorTopEntry.result E1M1AimActorTop.result E1M1AimActorTop.divided
'''
class AimActorTopTests(unittest.TestCase):
    lean=prior.AimActorCycleTests.lean
    succeeds=prior.AimActorCycleTests.succeeds
    rejects=prior.AimActorCycleTests.rejects
    mutations=prior.AimActorCycleTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),44)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorTopEntry.reject','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_authentic_new_range_and_relocations(self):
        spec,profile,raw=proof.extracted();part={'units':{'aimActorTop':spec['units']['aimActorTop']}}
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        for field,value in [('hex','90'+part['units']['aimActorTop']['hex'][2:]),('file_offset','0x0'),('relocations',[])]:
            bad=copy.deepcopy(part);bad['units']['aimActorTop'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,bad)
        data,_=proof.pinned_data();bad=dict(raw);bad['aimActorTop']=bytes([0x90])+raw['aimActorTop'][1:]
        self.rejects(proof.certificate(data,bad))
    def test_eligibility_requires_actor_identity_shootability_and_read_protection(self):
        args='s f hit pointer who record isThing tagSafe pointerSafe shooterSafe flagsSafe shooter different shootable'
        self.mutations(self.contract('E1M1AimActorTopEntry','entry',args),[
            ('(different : pointer≠who)','(different : True)'),
            ('(shootable : s.memory (pointer+104) &&& (4#8)≠0)','(shootable : True)'),
            ('(pointerSafe : Safe (s.regs 4) (s.regs 0+8))','(pointerSafe : True)'),
            ('(flagsSafe : Safe (s.regs 4) (pointer+104))','(flagsSafe : True)'),
            ('program [] 15','program [] 14')])
    def test_exact_height_and_distance_operands(self):
        self.mutations(self.contract('OriginalAimActorTop','operands','s range frac targetZ targetHeight shootZ r f z0 ht eye0'),[
            ('(ht : height s=targetHeight.raw.toBitVec)','(ht : True)'),
            ('(f : OriginalAimDistance.fraction s=frac.raw.toBitVec)','(f : True)'),
            ('(targetZ+targetHeight-shootZ).raw.toBitVec','(targetZ-shootZ).raw.toBitVec'),
            ('(range*frac).raw.toBitVec','range.raw.toBitVec')])
    def test_division_success_requires_actual_source_numerator_and_denominator(self):
        self.mutations(self.contract('E1M1AimActorTop','division_success','s range frac targetZ targetHeight shootZ slope r f z0 ht eye0 ok'),[
            ('(ok : checkedPathDiv (targetZ+targetHeight-shootZ) (range*frac)=.ok slope)','(ok : True)'),
            ('(eye0 : OriginalAimActorTop.eye s=shootZ.raw.toBitVec)','(eye0 : True)'),
            ('(r : OriginalAimDistance.range s=range.raw.toBitVec)','(r : True)')])
    def test_full_entry_preserves_exact_signed_decision_and_distance(self):
        self.mutations(self.contract('E1M1AimActorTopEntry','execution',proof.EXEC_ARGS),[
            ('(safe : Doom.Proofs.E1M1AimActorTopEntry.ReadSafe s pointer)','(safe : True)'),
            ('n≤56','n≤55'),
            ('if slope.raw<lower.raw then 0x2b875 else 0x2b881','if slope.raw≤lower.raw then 0x2b875 else 0x2b881'),
            ('core.regs 3=(range*hit.frac).raw.toBitVec','core.regs 3=range.raw.toBitVec'),
            ('core.regs 4=s.regs 4-24','core.regs 4=s.regs 4')])
    def test_source_join_requires_representation_and_strict_rejection(self):
        self.mutations(self.contract('E1M1AimActorTopEntry','reject',proof.REJECT_ARGS),[
            ('(identity : pointer=who ↔ hit.id=shooterId)','(identity : True)'),
            ('(flags : (s.memory (pointer+104) &&& (4#8) != 0)=scene.things[hit.id]!.shootable)','(flags : True)'),
            ('(below : slope.raw<lower.raw)','(below : slope.raw≤lower.raw)'),
            ('(selected : path.visited[i]! = hit)','(selected : True)'),
            ('range rest lower upper log','range rest upper lower log')])
    def test_frame_accounts_for_call_and_helper_stack_writes(self):
        self.mutations(self.contract('E1M1AimActorTop','frame','s a safe'),[
            ('(safe : Doom.Proofs.E1M1AimActorTop.ReadSafe s a)','(safe : True)')])
    def test_signed_comparison_edges_and_equality(self):
        self.succeeds('import Doom.Proofs.E1M1AimActorTopEntry\n'+proof.HEADER+'''
def sample (slope lower : BitVec 32) : X86Memory.State :=
  { regs:=fun _ => slope, memory:=store32 (fun _ => 0) 0x2c1e4 lower }
example : (OriginalAimActorTop.gate (sample 0 0)).pc=0x2b881 := by decide
example : (OriginalAimActorTop.gate (sample 0xffffffff 0)).pc=0x2b875 := by decide
example : (OriginalAimActorTop.gate (sample 0x80000000 0x7fffffff)).pc=0x2b875 := by decide
example : (OriginalAimActorTop.gate (sample 0x7fffffff 0x80000000)).pc=0x2b881 := by decide
example : (OriginalAimActorTop.gate (sample 0x80000000 0x80000000)).pc=0x2b881 := by decide
''')
if __name__=='__main__':unittest.main()

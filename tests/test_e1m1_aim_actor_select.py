"""Guard original actor clipping, exact selected result and rejection-scan composition."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_actor_bottom as prior
import verify_e1m1_aim_actor_select as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimActorSelectEntry\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimActorBottomEntry.result E1M1AimActorBottomEntry.input
attribute [local irreducible] E1M1AimActorBottomReject.result E1M1AimActorBottomReject.bottom
attribute [local irreducible] E1M1AimActorSelectEntry.result E1M1AimActorSelectEntry.input
attribute [local irreducible] OriginalAimActorSelect.result OriginalAimActorSelect.clipped
'''
class AimActorSelectTests(unittest.TestCase):
    lean=prior.AimActorBottomTests.lean
    succeeds=prior.AimActorBottomTests.succeeds
    rejects=prior.AimActorBottomTests.rejects
    mutations=prior.AimActorBottomTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),47)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorSelectEntry.selected','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_authentic_bytes_mapping_and_relocations(self):
        spec,profile,raw=proof.extracted();part={'units':{'aimActorSelect':spec['units']['aimActorSelect']}}
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        for field,value in [('hex','90'+part['units']['aimActorSelect']['hex'][2:]),('file_offset','0x0'),('relocations',[])]:
            bad=copy.deepcopy(part);bad['units']['aimActorSelect'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,bad)
        data,_=proof.pinned_data();bad=dict(raw);bad['aimActorSelect']=bytes([0x90])+raw['aimActorSelect'][1:]
        self.rejects(proof.certificate(data,bad))
    def test_clipping_requires_both_top_copies_and_signed_bounds(self):
        self.mutations(self.contract('E1M1AimActorSelect','clipping','s lower upper targetBottom targetTop low up bot top1 top2'),[
            ('(top1 : s.regs 6=targetTop.toBitVec)','(top1 : True)'),
            ('(top2 : s.regs 7=targetTop.toBitVec)','(top2 : True)'),
            ('max targetBottom lower','min targetBottom lower'),
            ('min targetTop upper','max targetTop upper')])
    def test_midpoint_uses_both_clipped_operands(self):
        self.mutations(self.contract('E1M1AimActorSelect','center','s bottom top bot hi'),[
            ('(bot : s.regs 0=bottom.toBitVec)','(bot : True)'),
            ('(hi : s.regs 7=top.toBitVec)','(hi : True)'),
            ('AutoAim.center bottom top','AutoAim.center bottom bottom')])
    def test_entry_requires_admission_and_stores_correct_globals(self):
        self.mutations(self.contract('E1M1AimActorSelectEntry','execution',proof.EXEC_ARGS),[
            ('(bottomAdmitted : ¬upper.raw<bottomSlope.raw)','(bottomAdmitted : True)'),
            ('(admitted : ¬topSlope.raw<lower.raw)','(admitted : True)'),
            ('(0x2b9f8#32)=pointer','(0x2b9b4#32)=pointer'),
            ('n≤103','n≤102'),
            ('.pc=0x2b8d2','.pc=0x2c887')])
    def test_source_selection_requires_identity_and_both_divisions(self):
        self.mutations(self.contract('E1M1AimActorSelectEntry','selected',proof.SELECT_ARGS),[
            ('(identity : pointer=who ↔ hit.id=shooterId)','(identity : True)'),
            ('(bottomAdmitted : ¬upper.raw<bottomSlope.raw)','(bottomAdmitted : True)'),
            ('(range*hit.frac)=.ok bottomSlope','(range*hit.frac)=.ok topSlope'),
            ('log i hit) :=','log (i+1) hit) :=')])
    def test_bottom_rejection_preserves_next_scan_and_source_progress(self):
        self.mutations(self.contract('E1M1AimActorBottomCycle','execution',proof.CYCLE_ARGS),[
            ('(above : upper.raw<bottomSlope.raw)','(above : upper.raw≤bottomSlope.raw)'),
            ('(history : History original.collected work seen visits)','(history : True)'),
            ('(before : Persistent s original.collected work resolve portals distance thing.shootHeight)','(before : True)'),
            ('n≤115+7*work.size','n≤114+7*work.size'),
            ("List.range' (seen.length+1) (path.visited.size-(seen.length+1))","List.range' (seen.length+2) (path.visited.size-(seen.length+2))")])
    def test_midpoint_negative_odd_and_wrapped_sum_examples(self):
        self.succeeds('import Doom.Proofs.E1M1AimActorSelectEntry\n'+proof.HEADER+'''
def sample (bottom top : BitVec 32) : X86Memory.State :=
  {regs:=fun r => if r=0 then bottom else top, memory:=fun _ => 0}
example : OriginalAimActorSelect.half (sample 0xffffffff 0xfffffffe)=0xffffffff := by decide
example : OriginalAimActorSelect.half (sample 0 0xffffffff)=0 := by decide
example : OriginalAimActorSelect.half (sample 0x7fffffff 0x7fffffff)=0xffffffff := by decide
example : OriginalAimActorSelect.half (sample 0x80000000 0x80000000)=0 := by decide
example : OriginalAimActorSelect.half (sample 0x80000000 0x7fffffff)=0 := by decide
example : OriginalAimActorSelect.half (sample 1 2)=1 := by decide
''')
if __name__=='__main__':unittest.main()

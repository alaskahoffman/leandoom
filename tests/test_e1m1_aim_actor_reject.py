"""Guard actor top rejection return, exact parent mark and reusable scan composition."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_actor_top as prior
import verify_e1m1_aim_actor_reject as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimActorRejectCycle\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimActorReject.top E1M1AimActorReject.result E1M1AimActorReject.returned
'''
class AimActorRejectTests(unittest.TestCase):
    lean=prior.AimActorTopTests.lean
    succeeds=prior.AimActorTopTests.succeeds
    rejects=prior.AimActorTopTests.rejects
    mutations=prior.AimActorTopTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),45)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorRejectCycle.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_authentic_return_bytes_and_mapping(self):
        spec,profile,raw=proof.extracted();part={'units':{'aimActorReject':spec['units']['aimActorReject']}}
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        for field,value in [('hex','90'+part['units']['aimActorReject']['hex'][2:]),('file_offset','0x0'),
                            ('relocations',[{'offset':1,'object':3,'target':'0x2b9b8'}])]:
            bad=copy.deepcopy(part);bad['units']['aimActorReject'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,bad)
        data,_=proof.pinned_data();bad=dict(raw);bad['aimActorReject']=bytes([0x90])+raw['aimActorReject'][1:]
        self.rejects(proof.certificate(data,bad))
    def test_return_restores_saved_registers_and_stack(self):
        self.mutations(self.contract('E1M1AimActorReject','returned_fields','s'),[
            ('core.regs 0=1','core.regs 0=0'),
            ('core.regs 4=s.regs 4+4','core.regs 4=s.regs 4'),
            ('core.regs 6=s.regs 6','core.regs 6=s.regs 7'),
            ('core.regs 3=s.regs 3','core.regs 3=s.regs 0')])
    def test_continuation_requires_rejection_pc_and_real_return_word(self):
        self.mutations(self.contract('E1M1AimActorReject','continuation','s atReject returnWord'),[
            ('(atReject : (Doom.Proofs.E1M1AimActorReject.top s).pc=0x2b875)','(atReject : True)'),
            ('(returnWord : load32 s.memory (s.regs 4)=0x2c86d)','(returnWord : True)'),
            ('program [] 13','program [] 12')])
    def test_parent_frame_and_mark_are_exact(self):
        self.mutations(self.contract('E1M1AimActorReject','registers','s'),[
            ('.pc=0x2c83a','.pc=0x2c88c'),
            ('(s.regs 3) 0x7fffffff','(s.regs 0) 0x7fffffff')])
        self.mutations(self.contract('E1M1AimActorReject','frame','s a safe mark'),[
            ('(safe : Doom.Proofs.E1M1AimActorReject.ReadSafe s a)','(safe : True)'),
            ('(mark : Apart a (s.regs 3))','(mark : True)')])
    def test_source_rejection_stays_strict_and_reaches_parent(self):
        self.mutations(self.contract('E1M1AimActorReject','execution',proof.EXEC_ARGS),[
            ('(below : slope.raw<lower.raw)','(below : slope.raw≤lower.raw)'),
            ('(returnWord : load32 s.memory (s.regs 4)=0x2c86d)','(returnWord : True)'),
            ('n≤69','n≤68'),
            ('range rest lower upper log','range rest upper lower log')])
    def test_next_scan_derives_consumed_image_from_incoming_history(self):
        self.mutations(self.contract('E1M1AimActorRejectCycle','scan',proof.SCAN_ARGS),[
            ('(history : History initial work seen visits)','(history : True)'),
            ('(layout : E1M1AimCycleInvariant.Layout s work)','(layout : True)'),
            ('(bounded : initial.size≤128)','(bounded : True)'),
            ('(stable : resolve {work[j]! with frac:=⟨2147483647⟩}=resolve work[j]!)','(stable : True)'),
            ('History initial (consume work j) (j::seen)','History initial work (j::seen)')])
    def test_complete_cycle_preserves_source_progress_and_bounds(self):
        self.mutations(self.contract('E1M1AimActorRejectCycle','execution',proof.CYCLE_ARGS),[
            ('(different : (work[j]!).id≠shooter)','(different : True)'),
            ('(below : slope.raw<lower.raw)','(below : slope.raw≤lower.raw)'),
            ('(safe : E1M1AimActorTopEntry.ReadSafe s (resolve original.collected[j]!))','(safe : True)'),
            ('(z0 : load32 s.memory (resolve original.collected[j]!+20)=scene.things[work[j]!.id]!.z.raw.toBitVec)','(z0 : True)'),
            ('n≤82+7*work.size','n≤81+7*work.size'),
            ('=lower.raw.toBitVec ∧\n      load32 out.core.memory','=upper.raw.toBitVec ∧\n      load32 out.core.memory'),
            ("List.range' (seen.length+1) (path.visited.size-(seen.length+1))","List.range' (seen.length+2) (path.visited.size-(seen.length+2))")])
if __name__=='__main__':unittest.main()

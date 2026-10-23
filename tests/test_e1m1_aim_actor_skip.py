"""Guard authentic actor skip bytes, return/mark effects, and source progress."""
import copy,json,re
import unittest
from pathlib import Path
import test_e1m1_aim_line_cycle as prior
import verify_e1m1_aim_actor_skip as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1AimLineCycle','import Doom.Proofs.E1M1AimActorSkipJoin')
class AimActorSkipTests(unittest.TestCase):
    lean=prior.AimLineCycleTests.lean
    succeeds=prior.AimLineCycleTests.succeeds
    rejects=prior.AimLineCycleTests.rejects
    mutations=prior.AimLineCycleTests.mutations
    def contract(self,module,name,args):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r' ',text,re.M).start()
        decl=text[start:text.index(' := by',start)]
        decl=re.sub(r'\bprogram\b','Doom.Proofs.E1M1AimActorSkip.program',decl)
        decl=decl.replace('(result s)','(Doom.Proofs.E1M1AimActorSkip.result s)').replace('(returned s)','(Doom.Proofs.E1M1AimActorSkip.returned s)')
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),43)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorSkip.callback','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_new_bytes_and_relocation_are_authenticated(self):
        spec,profile,raw=proof.extracted();part={'units':{'aimActorGuard':spec['units']['aimActorGuard']}}
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,part)['aimActorGuard'],raw['aimActorGuard'])
        for field,value in [('hex','90'+part['units']['aimActorGuard']['hex'][2:]),('file_offset','0x0'),('relocations',[])]:
            bad=copy.deepcopy(part);bad['units']['aimActorGuard'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,bad)
        data,_=proof.pinned_data();bad=dict(raw);bad['aimActorGuard']=bytes([0x90])+raw['aimActorGuard'][1:]
        self.rejects(proof.certificate(data,bad))
    def test_callback_requires_real_actor_reads_and_rejection(self):
        self.mutations(self.contract('E1M1AimActorSkip','callback',proof.CALLBACK_ARGS),[
            ('(isThing : hit.isLine=false)','(isThing : True)'),
            ('(shooterSafe : Safe (s.regs 4) 0x2b9ac)','(shooterSafe : True)'),
            ('(flagsSafe : Safe (s.regs 4) (pointer+104))','(flagsSafe : True)'),
            ('(shooter : load32 s.memory 0x2b9ac=who)','(shooter : True)'),
            ('(reject : pointer=who ∨ s.memory (pointer+104) &&& (4#8)=0)','(reject : True)'),
            ('n≤23','n≤22')])
    def test_real_parent_continues_and_marks_selected_fraction(self):
        self.mutations(self.contract('E1M1AimActorSkip','execution',proof.CALLBACK_ARGS+' returnWord'),[
            ('(returnWord : load32 s.memory (s.regs 4)=0x2c86d)','(returnWord : True)'),
            ('n≤28','n≤27'),
            ('(Doom.Proofs.E1M1AimActorSkip.result s).pc=0x2c83a','(Doom.Proofs.E1M1AimActorSkip.result s).pc=0x2c88c'),
            ('store32 (OriginalAimGuard.saved s).memory (s.regs 3) 0x7fffffff','store32 (OriginalAimGuard.saved s).memory (s.regs 0) 0x7fffffff'),
            ('(Doom.Proofs.E1M1AimActorSkip.result s).core.regs 4=s.regs 4+4','(Doom.Proofs.E1M1AimActorSkip.result s).core.regs 4=s.regs 4')])
    def test_join_requires_actor_representation_and_resolver_stability(self):
        self.mutations(self.contract('E1M1AimActorSkipJoin','execution',proof.EXEC_ARGS),[
            ('(identity : resolve original.collected[j]! = who ↔ (work[j]!).id=shooter)','(identity : True)'),
            ('(flags : (s.memory (resolve original.collected[j]!+104) &&& (4#8) != 0)=scene.things[work[j]!.id]!.shootable)','(flags : True)'),
            ('(ignored : (work[j]!).id=shooter ∨ scene.things[work[j]!.id]!.shootable=false)','(ignored : True)'),
            ('(stable : resolve {work[j]! with frac:=⟨2147483647⟩}=resolve work[j]!)','(stable : True)'),
            ('(bounded : original.collected.size≤128)','(bounded : True)')])
    def test_join_consumes_same_record_without_clipping_or_stopping(self):
        self.mutations(self.contract('E1M1AimActorSkipJoin','execution',proof.EXEC_ARGS),[
            ('0x2ba20 resolve (consume work j)','0x2ba20 resolve work'),
            ('History original.collected (consume work j) (j::seen) (visits.push work[j]!)','History original.collected work (j::seen) (visits.push work[j]!)'),
            ('=lower.raw.toBitVec','=upper.raw.toBitVec'),
            ("List.range' (seen.length+1) (path.visited.size-(seen.length+1))","List.range' (seen.length+2) (path.visited.size-(seen.length+2))")])
    def test_source_skip_requires_actor_kind_and_skip_condition(self):
        self.mutations(self.contract('E1M1AimActorSkipJoin','source',
            'scene shooter thing path distance lower upper log i rest hit selected isThing ignored'),[
            ('(isThing : hit.isLine=false)','(isThing : True)'),
            ('(ignored : hit.id=shooter ∨ scene.things[hit.id]!.shootable=false)','(ignored : True)'),
            ('distance rest lower upper log','distance rest upper lower log')])
    def test_saved_buffer_requires_prologue_separation(self):
        self.mutations(self.contract('E1M1AimActorSkipJoin','saved_records','s work resolve records safe'),[
            ('(safe : E1M1AimRecordFrame.RecordsSafe s work)','(safe : True)'),
            ('(records : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve work)','(records : True)')])
if __name__=='__main__':unittest.main()

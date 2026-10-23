"""Guard the real selected-target return, preserved records and aligned source stop."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_actor_select as prior
import verify_e1m1_aim_actor_return as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimActorStop\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimActorSelectEntry.result E1M1AimActorSelectEntry.input
attribute [local irreducible] E1M1AimActorReturn.selected E1M1AimActorReturn.returned E1M1AimActorReturn.result
'''
class AimActorReturnTests(unittest.TestCase):
    lean=prior.AimActorSelectTests.lean
    succeeds=prior.AimActorSelectTests.succeeds
    rejects=prior.AimActorSelectTests.rejects
    mutations=prior.AimActorSelectTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),47)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorStop.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_reused_false_return_is_authenticated(self):
        spec,profile,raw=proof.extracted();part={'units':{'aimStop':spec['units']['aimStop']}}
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        extraction=proof.previous.extraction
        binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        for field,value in [('hex','90'+part['units']['aimStop']['hex'][2:]),('file_offset','0x0'),
                            ('relocations',[{'offset':1,'object':3,'target':'0x2b9f8'}])]:
            bad=copy.deepcopy(part);bad['units']['aimStop'][field]=value
            with self.assertRaises(ValueError):extraction.extract(binary,profile,bad)
        data,_=proof.pinned_data();bad=dict(raw);bad['aimStop']=bytes([0x90])+raw['aimStop'][1:]
        self.rejects(proof.certificate(data,bad))
    def test_selection_stores_must_preserve_saved_slots(self):
        self.mutations(self.contract('E1M1AimActorReturn','saved_slot','s safe off member'),[
            ('(safe : Doom.Proofs.E1M1AimActorReturn.Safe s)','(safe : True)'),
            ('(member : off∈E1M1AimReturnFrame.slots)','(member : True)')])
        self.mutations(self.contract('E1M1AimActorReturn','selected_frame','s a target slope'),[
            ('(target : Apart a 0x2b9f8)','(target : True)'),
            ('(slope : Apart a 0x2b9b4)','(slope : True)')])
    def test_false_return_restores_registers_and_true_stack(self):
        self.mutations(self.contract('E1M1AimActorReturn','returned_fields','s safe'),[
            ('core.regs 0=0','core.regs 0=1'),
            ('core.regs 4=s.regs 4+4','core.regs 4=s.regs 4'),
            ('core.regs 3=s.regs 3','core.regs 3=s.regs 0'),
            ('core.regs 7=s.regs 7','core.regs 7=s.regs 6')])
    def test_continuation_requires_original_return_and_twelve_instructions(self):
        self.mutations(self.contract('E1M1AimActorReturn','continuation','s safe returnWord'),[
            ('(returnWord : load32 s.memory (s.regs 4)=0x2c86d)','(returnWord : True)'),
            ('(safe : Doom.Proofs.E1M1AimActorReturn.Safe s)','(safe : True)'),
            ('program [] 12','program [] 11')])
    def test_selected_source_result_survives_machine_return(self):
        self.mutations(self.contract('E1M1AimActorReturn','execution',proof.EXEC_ARGS),[
            ('(saveSafe : Doom.Proofs.E1M1AimActorReturn.Safe s)','(saveSafe : True)'),
            ('.pc=0x2c88c','.pc=0x2c83a'),
            ('(0x2b9f8#32)=pointer','(0x2b9b4#32)=pointer'),
            ('n≤115','n≤114'),
            ('log i hit) :=','log (i+1) hit) :=')])
    def test_aligned_stop_requires_real_history_and_preserves_source_index(self):
        self.mutations(self.contract('E1M1AimActorStop','execution',proof.STOP_ARGS),[
            ('(history : History original.collected work seen visits)','(history : True)'),
            ('(empty : original.visited=#[])','(empty : True)'),
            ('(bottomAdmitted : ¬upper.raw<bottomSlope.raw)','(bottomAdmitted : True)'),
            ('(saveSafe : E1M1AimActorReturn.Safe s)','(saveSafe : True)'),
            ('log seen.length work[j]!) :=','log (seen.length+1) work[j]!) :=')])
    def test_stopping_preserves_whole_buffer_instead_of_consuming_target(self):
        self.mutations(self.contract('E1M1AimActorStop','records','s work resolve saveSafe bounded image safe'),[
            ('(bounded : work.size≤128)','(bounded : True)'),
            ('(safe : E1M1AimRecordFrame.RecordsSafe s work)','(safe : True)'),
            ('(saveSafe : E1M1AimActorReturn.Safe s)','(saveSafe : True)'),
            ('0x2ba20 resolve work :=','0x2ba20 resolve (consume work 0) :=')])
if __name__=='__main__':unittest.main()

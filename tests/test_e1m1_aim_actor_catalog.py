"""Guard catalog transport, derived actor inputs, and prefix-to-hit composition."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_actor_dispatch as prior
import verify_e1m1_aim_actor_catalog as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimActorPortalPrefix\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimActorCycle.Outcome
'''
class AimActorCatalogTests(unittest.TestCase):
    lean=prior.AimActorDispatchTests.lean
    succeeds=prior.AimActorDispatchTests.succeeds
    rejects=prior.AimActorDispatchTests.rejects
    mutations=prior.AimActorDispatchTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),47)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorCatalog.inputs','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_preservation_requires_frame_stack_and_actual_mark(self):
        self.mutations(self.contract('E1M1AimActorCatalog','preserved',proof.PRESERVE_ARGS),[
            ('(frame : Frame s out)','(frame : True)'),
            ('(stack : out.core.regs 4=s.regs 4)','(stack : True)'),
            ('(pointer : s.regs 3=Doom.Proofs.E1M1MinimumScan.address marked)','(pointer : True)'),
            ('(bounded : marked<128)','(bounded : True)')])
    def test_catalog_entries_retain_real_actor_fields(self):
        self.mutations(self.contract('E1M1AimActorCatalog','entry_preserved','s out marked pointer actor frame stack selected bounded entry'),[
            ('(entry : Doom.Proofs.E1M1AimActorCatalog.Entry s pointer actor)','(entry : True)'),
            ('Entry out.core pointer actor','Entry out.core (pointer+4) actor')])
    def test_reached_inputs_require_history_catalog_and_selection(self):
        self.mutations(self.contract('E1M1AimActorCatalog','inputs',proof.INPUT_ARGS),[
            ('(history : History initial work seen visits)','(history : True)'),
            ('(catalog : Doom.Proofs.E1M1AimActorCatalog.Catalog s.core scene shooter initial resolve who)','(catalog : True)'),
            ('(selection : Selection initial work seen resolve target sp s fraction j)','(selection : True)'),
            ('(isThing : (work[j]!).isLine=false)','(isThing : True)')])
    def test_unified_cycle_uses_catalog_and_reached_division_equations(self):
        self.mutations(self.contract('E1M1AimActorCatalogCycle','execution',proof.EXEC_ARGS),[
            ('(catalog : Doom.Proofs.E1M1AimActorCatalog.Catalog s scene shooter original.collected resolve who)','(catalog : True)'),
            ('(distance*(work[j]!).frac)=.ok topSlope','(distance*(work[j]!).frac)=.ok bottomSlope'),
            ('n≤115+7*work.size','n≤114+7*work.size')])
    def test_prefix_requires_initial_catalog_and_real_sequence(self):
        self.mutations(self.contract('E1M1AimActorPortalPrefix','selected',proof.PREFIX_ARGS),[
            ('(catalog : Doom.Proofs.E1M1AimActorCatalog.Catalog s.core scene shooter original.collected resolve who)','(catalog : True)'),
            ('(sequence : Doom.Proofs.E1M1AimPortalPrefix.Sequence portals distance thing.shootHeight a final count)','(sequence : True)'),
            ('(within : ¬fraction>65536)','(within : True)')])
    def test_prefix_preserves_source_index_and_selected_stores(self):
        self.mutations(self.contract('E1M1AimActorPortalPrefix','selected',proof.PREFIX_ARGS),[
            ('finalSeen.length=seen.length+count','finalSeen.length=seen.length+count+1'),
            ('resolve original.collected[j]!','resolve original.collected[j+1]!'),
            ('load32 out.core.memory (0x2b9b4#32)','load32 out.core.memory (0x2b9b8#32)'),
            ('n≤count*(157+7*original.collected.size)+115','n≤count*(157+7*original.collected.size)+114')])
    def test_prefix_requires_successful_actor_admission(self):
        self.mutations(self.contract('E1M1AimActorPortalPrefix','selected',proof.PREFIX_ARGS),[
            ('(different : (final.work[j]!).id≠shooter)','(different : True)'),
            ('(shootable : scene.things[final.work[j]!.id]!.shootable=true)','(shootable : True)'),
            ('(admitted : ¬topSlope.raw<final.lower.raw)','(admitted : True)'),
            ('(bottomAdmitted : ¬final.upper.raw<bottomSlope.raw)','(bottomAdmitted : True)')])
if __name__=='__main__':unittest.main()

"""Guard catalog transport, generic carry induction, and whole-prefix stops."""
import re
import unittest
from pathlib import Path
import test_e1m1_aim_blocking_cycle as prior
import verify_e1m1_aim_blocking_prefix as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1AimBlockingCycle','import Doom.Proofs.E1M1AimBlockingPrefix')+'\nopen E1M1MinimumScan (address)\nopen E1M1AimHistoryCycle (Frame)\n'
class AimBlockingPrefixTests(unittest.TestCase):
    lean=prior.AimBlockingCycleTests.lean
    succeeds=prior.AimBlockingCycleTests.succeeds
    rejects=prior.AimBlockingCycleTests.rejects
    mutations=prior.AimBlockingCycleTests.mutations
    def contract(self,module,name,args):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r' ',text,re.M).start()
        decl=text[start:text.index(' := by',start)]
        decl=re.sub(r'\bprogram\b','E1M1AimRepeatProgram.program',decl)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),42)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimPortalCarry.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_catalog_requires_frame_stack_pointer_and_original_flags(self):
        self.mutations(self.contract('E1M1AimWallCatalog','preserved',proof.PRESERVE_ARGS),[
            ('(frame : Frame s out)','(frame : True)'),
            ('(stack : out.core.regs 4=s.regs 4)','(stack : True)'),
            ('(pointer : s.regs 3=address marked)','(pointer : True)'),
            ('(bounded : marked<128)','(bounded : True)'),
            ('(catalog : Catalog s initial resolve walls)','(catalog : True)')])
    def test_catalog_inputs_use_actual_selected_wall(self):
        self.mutations(self.contract('E1M1AimWallCatalog','inputs',
            'scene initial work seen resolve walls target sp s fraction j selection catalog represented listed'),[
            ('(selection : Selection initial work seen resolve target sp s fraction j)','(selection : True)'),
            ('(catalog : Catalog s.core initial resolve walls)','(catalog : True)'),
            ('(represented : Represents scene initial walls)','(represented : True)'),
            ('(listed : walls j)','(listed : True)')])
    def test_carry_requires_preservation_initial_property_and_admitted_endpoint(self):
        self.mutations(self.contract('E1M1AimPortalCarry','execution',proof.CARRY_ARGS),[
            ('(carried : Carry s.core)','(carried : True)'),
            ('(preserve : ∀ before out marked, E1M1AimHistoryCycle.Frame before out →\n      out.core.regs 4=before.regs 4 → before.regs 3=E1M1MinimumScan.address marked →\n      marked<128 → Carry before → Carry out.core)','(preserve : True)'),
            ('(chosen : minimum final.work=.ok (fraction,some j))','(chosen : True)'),
            ('(within : ¬fraction>65536)','(within : True)'),
            ('(sequence : Sequence portals distance thing.shootHeight a final count)','(sequence : True)')])
    def test_carry_reaches_same_final_selection_bounds_and_count(self):
        self.mutations(self.contract('E1M1AimPortalCarry','execution',proof.CARRY_ARGS),[
            ('finalSeen.length=seen.length+count','finalSeen.length=seen.length+count+1'),
            ('out fraction j ∧','out fraction (j+1) ∧'),
            ('load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec','load32 out.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec'),
            ('n≤count*(157+7*result.collected.size)','n≤count*(157+6*result.collected.size)')])
    def test_wall_ending_requires_only_initial_catalog_and_source_endpoint(self):
        self.mutations(self.contract('E1M1AimBlockingPrefix','wall',proof.WALL_ARGS),[
            ('(catalog : E1M1AimWallCatalog.Catalog s.core result.collected resolve walls)','(catalog : True)'),
            ('(wallMap : E1M1AimWallCatalog.Represents scene result.collected walls)','(wallMap : True)'),
            ('(listed : walls j)','(listed : True)'),
            ('(chosen : minimum final.work=.ok (fraction,some j))','(chosen : True)'),
            ('(within : ¬fraction>65536)','(within : True)')])
    def test_wall_ending_includes_last_visit_and_real_instructions(self):
        self.mutations(self.contract('E1M1AimBlockingPrefix','wall',proof.WALL_ARGS),[
            ('+24, ∃ out','+23, ∃ out'),
            ('out.pc=0x2c88c','out.pc=0x2c887'),
            ('finalSeen.length=seen.length+count','finalSeen.length=seen.length+count+1'),
            ('History result.collected final.work finalSeen finalVisits','History result.collected (E1M1InterceptMark.consume final.work j) finalSeen finalVisits'),
            ('E1M1AimSource.stopped path (seen.length+count+1)','E1M1AimSource.stopped path (seen.length+count)'),
            ('load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec','load32 out.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec')])
    def test_closed_ending_keeps_closed_gap_bounds_and_last_visit(self):
        self.mutations(self.contract('E1M1AimBlockingPrefix','closed',proof.CLOSED_ARGS),[
            ('(blocked : min (front p).ceiling.raw (back p).ceiling.raw ≤ max (front p).floor.raw (back p).floor.raw)','(blocked : True)'),
            ('(listed : portals j=some p)','(listed : True)'),
            ('+60, ∃ out','+59, ∃ out'),
            ('out.pc=0x2c88c','out.pc=0x2c887'),
            ('E1M1AimSource.stopped path (seen.length+count+1)','E1M1AimSource.stopped path (seen.length+count)'),
            ('load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec','load32 out.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec')])
if __name__=='__main__':unittest.main()

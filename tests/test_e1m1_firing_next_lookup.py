"""Next object lookup must derive coordinates and reads from the firing entry."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_next_things as prior
import verify_e1m1_firing_next_lookup as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringNextThings','import Doom.Proofs.E1M1FiringNextLookup')
SCAN=prior.SCAN
FRAME=prior.FRAME
NEXT=prior.NEXT+' nextHead headValue nextSetup nextSafe'
LOOKUP='s sp lines epoch objects hits seen x y w h links object pc stack callback returnWord encoding inMap global selected globalSafe headSafe tracked represented array epochSafe stampSafe'

class FiringNextLookupTests(unittest.TestCase):
    lean=prior.FiringNextThingsTests.lean
    succeeds=prior.FiringNextThingsTests.succeeds
    rejects=prior.FiringNextThingsTests.rejects
    mutations=prior.FiringNextThingsTests.mutations

    def contract(self,module,name,args,section=False):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=source.index('theorem '+name+' ')
        context=''
        if section:
            label='Scan' if name=='scan_coordinate' else 'Firing'
            earlier=source[source.index('section '+label):start]
            context=''.join(re.findall(r'^variable .*?(?=^include)',earlier,re.M|re.S))
            context+='\n'.join(re.findall(r'^include .+$',earlier,re.M))+'\n'
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('FiringNextLookup.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_scan_coordinate_needs_capacity_and_callback_readiness(self):
        self.mutations(self.contract('E1M1NextCoordinates','scan_coordinate',SCAN+' f r tracked axis',True),[
            ('r.collected c.ids.length)','r.collected 0)'),
            ('(ready : Ready s lines trace c data)','(ready : True)'),
            ('s.regs (OriginalLineCoordinates.register axis) :=','s.regs 0 :=')])

    def test_next_coordinates_come_from_grid_step(self):
        self.mutations(self.contract('E1M1NextCoordinates','suffix_coordinates',FRAME+' locals x y mapX mapY',True),[
            ('(mapX : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapX=x.toBitVec)','(mapX : True)'),
            ('(mapY : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapY=y.toBitVec)','(mapY : True)'),
            ('start.core.regs 6=x.toBitVec','start.core.regs 6=y.toBitVec')])

    def test_lookup_needs_actual_table_encoding_and_bounds(self):
        self.mutations(self.contract('E1M1NextThingLookup','execution',LOOKUP),[
            ('(encoding : OriginalThingEntry.Inputs s.core x y w h)','(encoding : True)'),
            ('(inMap : Collision.pathCellInside x y w h=true)','(inMap : True)'),
            ('(global : load32 s.core.memory (0x2c0f8#32)=links)','(global : True)'),
            ('(selected : load32 s.core.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2))=object)','(selected : True)')])

    def test_empty_and_nonempty_paths_have_distinct_real_returns(self):
        self.mutations(self.contract('E1M1NextThingLookup','execution',LOOKUP),[
            ('out.pc=0x2cab1','out.pc=0x2ca94'),
            ('out.pc=0x2c5d2','out.pc=0x2c720'),
            ('out.core.regs 2=object','out.core.regs 2=links'),
            ('out.core.regs 4=sp-(112#32)','out.core.regs 4=sp-(116#32)'),
            ('n≤20','n≤19')])

    def test_prologue_store_preserves_hits_and_history_only_when_separate(self):
        self.mutations(self.contract('E1M1NextThingLookup','execution',LOOKUP),[
            ('(array : OriginalLineMixedInvariant.ArraySafe 0x2ba20 (sp-(120#32)))','(array : True)'),
            ('(epochSafe : Apart (0x13580#32) (sp-(120#32)))','(epochSafe : True)'),
            ('(stampSafe : ∀ j<seen.size, Apart (stamp lines j) (sp-(120#32)))','(stampSafe : True)'),
            ('(globalSafe : Apart (0x2c0f8#32) (sp-(120#32)))','(globalSafe : True)')])

    def test_joined_lookup_requires_initial_read_value_and_separation(self):
        self.mutations(self.contract('E1M1FiringNextLookup','execution',NEXT,True),[
            ('(headValue : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2))=nextHead)','(headValue : True)'),
            ('E1M1PathMapFiring.Safe gun s a)\n    (nextSafe', 'True)\n    (nextSafe'),
            ('E1M1FiringMapState.Safe (s.regs 4) lines a) :','True) :')])

    def test_joined_lookup_has_exact_cell_head_and_continuous_bound(self):
        self.mutations(self.contract('E1M1FiringNextLookup','execution',NEXT,True),[
            ('steps≤502+281*(c.ids.length+nextCell.ids.tail.length)+230*nodes.length','steps≤501+281*(c.ids.length+nextCell.ids.tail.length)+230*nodes.length'),
            ('call.core.regs 0=x.toBitVec','call.core.regs 0=y.toBitVec'),
            ('out.core.regs 2=nextHead','out.core.regs 2=links')])

if __name__=='__main__':unittest.main()

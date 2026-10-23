"""Coordinate restoration and intended-cell arguments at the original thing CALL."""
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_thing_coordinates as proof
HEADER='''import Doom.Proofs.E1M1ThingCoordinates
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant
open OriginalLineCoordinates
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage
attribute [local irreducible] load32
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'

class ThingCoordinatesTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,name,args,generic=False,section=False):
        module='OriginalLineCoordinates' if generic else 'E1M1ThingCoordinates'
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        context=''
        if section:
            start=source.index('variable (',source.index('section Scan' if generic else 'section Firing'))
            context=source[start:source.index('include inv' if generic else 'include input',start)]
        decl=re.split(r' :=(?: by)?\n',source[source.index('theorem '+name+' '):],maxsplit=1)[0]
        decl=decl.replace('theorem '+name,'example',1)
        return HEADER+context+decl+' :=\n  '+module+'.'+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old): self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data(); _,_,raw=proof.extracted()
        out=self.succeeds(proof.certificate(data,raw)); proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('saved_safe','missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)
        for module,names in [('OriginalLineCoordinates',proof.GENERIC),('E1M1ThingCoordinates',proof.PROOFS)]:
            text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',text,re.M))

    def test_actual_save_and_restore_slots(self):
        self.mutations(self.contract('saved_prologue','s x',True),[
            ('s.regs (register x) :=','s.regs (register (!x)) :=')])
        self.mutations(self.contract('unwind_coordinate','s x',True),[
            ('s.regs 4+popOffset x','s.regs 4+savedOffset x')])
        self.succeeds(self.contract('finish_coordinate','s x',True))
        self.succeeds(self.contract('resume_coordinate','s x',True))

    def test_point_helpers_keep_prologue_values(self):
        self.mutations(self.contract('tested_saved','s trace line p v entry x',True),[
            ('(entry : OriginalLineInterceptEntry.Inputs s trace line p v)','(entry : True)'),
            ('s.regs (register x) :=','s.regs (register (!x)) :=')])

    def test_crossing_requires_record_and_scratch_protection(self):
        self.mutations(self.contract('crossing_coordinate','s trace line p v w h x cursor savedSafe',True),[
            ('(savedSafe : OriginalLineTail.RecordSafe s (s.regs 4-savedOffset x))','(savedSafe : True)'),
            ('(cursor : OriginalLineCrossing.SideSafe s (0x2c028#32) ∧ OriginalLineCrossing.ScratchSafe s (0x2c028#32))','(cursor : True)')])
        self.mutations(self.contract('rejected_coordinate','s trace line p v w h x',True),[
            ('(h : OriginalLineReject.Inputs s trace line p v w)','(h : True)')])

    def test_scan_reuses_layout_and_capacity(self):
        self.succeeds(self.contract('saved_safe','initial n base resolve h i s r inv hi x',True,True))
        self.succeeds(self.contract('step_coordinate','initial n base resolve h i s r inv hi x',True,True))
        self.mutations(self.contract('finished_coordinate','initial n base resolve h r f collected keep x',True),[
            ('(collected : OriginalLineCollection.Tracks initial base resolve r.collected n)','(collected : True)'),
            ('(keep : ∀ j<n, (h.candidates j).crosses=true → (h.candidates j).Continues)','(keep : True)'),
            ('=initial.regs (register x) :=','=initial.regs (register (!x)) :=')])

    def test_firing_supplies_intended_coordinates(self):
        self.succeeds(self.contract('caller_coordinate','s x'))
        self.succeeds(self.contract('scan_coordinate',ARGS+' x',section=True))
        self.mutations(self.contract('first_coordinates',ARGS,section=True),[
            ('startBlockX.toBitVec','startBlockY.toBitVec')])
        self.mutations(self.contract('call_coordinates',ARGS,section=True),[
            ('out.core.regs 2=','out.core.regs 0=')])

    def test_joined_call_requires_real_gate_and_return(self):
        self.mutations(self.contract('firing_call',ARGS+' returns safe f',section=True),[
            ('(safe : E1M1ThingGate.FlagSafe (s.regs 4) lines)','(safe : True)'),
            ('(returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)','(returns : True)'),
            ('out.pc=0x2c5a0','out.pc=0x2c720'),
            ('startBlockX.toBitVec','startBlockY.toBitVec')])

    def test_nonzero_coordinates_survive_wrapping_stack_scan(self):
        source=(ROOT/'tests/reference/e1m1-scan-contracts.lean').read_text()
        source=source.replace('import Doom.Proofs.E1M1ScanContracts','import Doom.Proofs.E1M1ThingCoordinates')
        source=source.replace('else if r=4 then (1#32)-124 else 0,memory same',
            'else if r=4 then (1#32)-124 else if r=1 then 0xdeadbeef else if r=6 then 0x12345678 else 0,memory same')
        source+='''
namespace ScanContractsFixture
open OriginalLineCoordinates

theorem coordinates (same : Bool) :
    (result same).1.core.regs 6=(0x12345678#32) ∧
    (result same).1.core.regs 1=(0xdeadbeef#32) := by
  have keep (x : Bool) := finished_coordinate (scan same) 2 0x2ba20 (E1M1PathMap.resolve 0x600200)
    (checked same) {trace:=ray same} none (collected same)
    (fun i _ _ => E1M1ScanContracts.candidate_continues (ray same) 0x600200 cell.ids[i]! (data i)) x
  exact ⟨keep true,keep false⟩

example : (result false).1.core.regs 6=(0x12345678#32) := (coordinates false).1
example : (result true).1.core.regs 1=(0xdeadbeef#32) := (coordinates true).2
#print axioms coordinates
end ScanContractsFixture
'''
        out=self.succeeds(source)
        self.assertNotIn('sorryAx',out)
        self.rejects(source.replace('example : (result false).1.core.regs 6=(0x12345678#32)',
            'example : (result false).1.core.regs 6=(0xdeadbeef#32)'))

if __name__=='__main__': unittest.main()

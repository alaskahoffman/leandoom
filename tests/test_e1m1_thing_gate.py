"""Derived thing traversal flag, actual CALL, and retained line intercepts."""
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_thing_gate as proof
HEADER='''import Doom.Proofs.E1M1ThingGate
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (Initial ArraySafe)
open E1M1ThingGate
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'


class ThingGateTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,name,args,joined=False):
        source=(ROOT/'Doom/Proofs/E1M1ThingGate.lean').read_text()
        context=''
        if joined:
            context=source[source.index('variable (',source.index('section Firing')):source.index('/-- First grid SP')]
        kind='def' if name=='flagged' else 'theorem'
        decl=re.split(r' :=(?: by)?\n| := rfl',source[source.index(kind+' '+name+' '):],maxsplit=1)[0]
        decl=decl.replace(kind+' '+name,'def contractCheck' if kind=='def' else 'example',1)
        return HEADER+context+decl+' :=\n  E1M1ThingGate.'+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old): self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data(); _,_,raw=proof.extracted()
        out=self.succeeds(proof.certificate(data,raw)); proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('firing_call','missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)
        text=(ROOT/'Doom/Proofs/E1M1ThingGate.lean').read_text()
        self.assertEqual(proof.PROOFS,[a or b for a,b in re.findall(r'^(?:theorem (\w+)|def (flagged|gate|called)) ',text,re.M)])

    def test_flag_is_generated_at_firing_entry(self):
        self.succeeds(self.contract('caller_flag','s'))
        self.mutations(self.contract('first_flag',ARGS,True),[
            ('=(3#32)', '=(1#32)')])
        self.mutations(self.contract('grid_stack',ARGS,True),[
            ('s.regs 4-(112#32)','s.regs 4-(108#32)')])

    def test_scan_preservation_needs_heap_separation(self):
        self.mutations(self.contract('scan_flag',ARGS+' safe',True),[
            ('(safe : FlagSafe (s.regs 4) lines)','(safe : True)'),
            ('=(3#32)','=(2#32)')])
        self.succeeds(self.contract('flagged_finished',ARGS+' safe',True))
        self.succeeds(self.contract('flagged',ARGS+' safe',True))

    def test_gate_requires_flag_and_restored_stack(self):
        self.mutations(self.contract('enabled',ARGS+' returns safe',True),[
            ('(returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)','(returns : True)'),
            ('(safe : FlagSafe (s.regs 4) lines)','(safe : True)')])

    def test_call_preserves_collection_with_same_capacity(self):
        self.mutations(self.contract('call_collection','s f base resolve hits reserve tracked safe'),[
            ('(safe : ArraySafe base (s.regs 4-(4#32)))','(safe : True)'),
            ('base resolve hits reserve :=','base resolve hits (reserve+1) :=')])

    def test_continuous_call_has_actual_abi_and_target(self):
        self.mutations(self.contract('firing_call',ARGS+' returns safe f',True),[
            ('out.pc=0x2c5a0','out.pc=0x2c720'),
            ('(0x2cab1#32)','(0x2ca94#32)'),
            ('out.core.regs 0=prior.core.regs 6','out.core.regs 0=prior.core.regs 1'),
            ('steps≤383+281*c.ids.length','steps≤382+281*c.ids.length')])

    def test_overlapping_flag_word_is_rejected(self):
        self.succeeds(HEADER+'''
example : ¬FlagSafe (1#32) (0xffffff9b#32) := by
  intro h
  exact h.stamps 0 (by decide) ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide)
example : ¬FlagSafe (0x2ba50#32) (0x600200#32) := by
  intro h
  exact h.array.1 0 (by decide) 0 (by simp) ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide)
''')

    def test_wrapping_stack_flag_survives_crossing_and_rejection(self):
        source=(ROOT/'tests/reference/e1m1-scan-contracts.lean').read_text()
        source=source.replace('import Doom.Proofs.E1M1ScanContracts','import Doom.Proofs.E1M1ThingGate')
        source=source.replace('(0xffffff85,0x2c5f0),','(0xffffff85,0x2c5f0),(0xffffffd1,3),')
        a=source.index('theorem word_stamp_safe'); b=source.index('\ndef reads',a)
        helper=source[a:b].replace('word_stamp_safe','flag_stamp_safe').replace('0x2c028,0xffffff81])','0x2c028,0xffffff81,0xffffffd1])')
        marker='  rcases ha with '+ '|'.join(['rfl']*22)
        self.assertIn(marker,helper)
        helper=helper.replace(marker,marker+'|rfl')
        source=source[:b]+'\n'+helper+source[b:]
        source+='''
namespace ScanContractsFixture
open E1M1ThingGate

theorem flag_safe : FlagSafe 1 0x600200 := by
  constructor
  · intro id hi
    exact flag_stamp_safe _ (by simp [flagWord]) id hi
  · constructor
    · intro k hk off ho
      exact FloorCaller.apart_symm (record_apart k hk off ho _ (by decide) (by decide))
    · unfold Apart; decide

def flag_contract (same : Bool) := E1M1ScanReturn.protect (scan same) 2 0x2ba20 (E1M1PathMap.resolve 0x600200)
  (checked same) [flagWord 1] (by
    intro i hi a ha
    have eq : a=flagWord 1 := by simpa using ha
    subst a
    exact E1M1ScanContracts.protection (scan same) 1 0x600200 rfl i _ (ids ⟨i,hi⟩)
      ((items same).pointers ⟨i,hi⟩ (Fixed.ofInt 0)) _ (flag_protected _ _ flag_safe.stamps))
  (by
    intro a ha
    have eq : a=flagWord 1 := by simpa using ha
    subst a
    exact flag_safe.array)

theorem options_survive (same : Bool) :
    load32 (result same).1.core.memory (flagWord 1)=(3#32) ∧
    OriginalPathCell.enabled false (result same).1.core=true := by
  have run := OriginalLineMixedInvariant.through_sentinel (scan same) 2 0x2ba20 (E1M1PathMap.resolve 0x600200)
    (flag_contract same) {trace:=ray same} none (collected same)
    (fun i _ _ => E1M1ScanContracts.candidate_continues (ray same) 0x600200 cell.ids[i]! (data i))
    (items same).sentinel
  have kept := run.2.2.2 (flagWord 1) (List.mem_append_right _ (by simp))
  have initial : load32 (scan same).memory (flagWord 1)=(3#32) := by cases same <;> decide
  have value : load32 (result same).1.core.memory (flagWord 1)=(3#32) := kept.trans initial
  have sp := OriginalLineTraversal.stack _ _ _ run.2.1
  change (result same).1.core.regs 4=(0xffffff91#32) at sp
  have byte := congrArg (fun v : Word => v.extractLsb' 0 8) value
  rw [E1M1PathCell.low_byte] at byte
  refine ⟨value,?_⟩
  change ((result same).1.core.memory ((result same).1.core.regs 4+(64#32)) &&& (2#8) != 0)=true
  rw [sp]
  change ((result same).1.core.memory (flagWord 1) &&& (2#8) != 0)=true
  rw [byte]; decide

example : OriginalPathCell.enabled false (result false).1.core=true := (options_survive false).2
example : OriginalPathCell.enabled false (result true).1.core=true := (options_survive true).2
#print axioms options_survive
end ScanContractsFixture
'''
        out=self.succeeds(source)
        self.assertNotIn('sorryAx',out)
        self.rejects(source.replace('false (result false).1.core=true :=','false (result false).1.core=false :='))


if __name__=='__main__': unittest.main()

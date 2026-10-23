"""Saved scan frame, actual return address, and caller success-test connection."""
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_scan_return as proof
HEADER='''import Doom.Proofs.E1M1ScanReturn
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path linePointer)
open E1M1ScanContracts (LineData candidates)
open OriginalLineMixedInvariant (Initial ArraySafe atIndex)
open E1M1ScanReturn
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'


class ScanReturnTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,name,args,joined=False):
        source=(ROOT/'Doom/Proofs/E1M1ScanReturn.lean').read_text()
        context=''
        if joined:
            context=source[source.index('variable (',source.index('section Firing')):source.index('/-- Actual saved-frame')]
        kind='def' if name in ['protect','framed','finished'] else 'theorem'
        decl=re.split(r' :=(?: by)?\n| := rfl',source[source.index(kind+' '+name+' '):],maxsplit=1)[0]
        decl=decl.replace(kind+' '+name,'def contractCheck' if kind=='def' else 'example',1)
        return HEADER+context+decl+' :=\n  E1M1ScanReturn.'+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old): self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data(); _,_,raw=proof.extracted()
        out=self.succeeds(proof.certificate(data,raw)); proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('firing_to_things','missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)
        text=(ROOT/'Doom/Proofs/E1M1ScanReturn.lean').read_text()
        self.assertEqual(proof.PROOFS,[a or b for a,b in re.findall(r'^(?:theorem (\w+)|def (protect|framed|finished)) ',text,re.M)])

    def test_extension_requires_write_separation(self):
        args='s n base resolve h extra separated array'
        self.mutations(self.contract('protect',args),[
            ('(array : ∀ a∈extra, ArraySafe base a)','(array : True)')])
        self.succeeds(self.contract('protect_finished',args+' f r'))

    def test_saved_words_and_exact_callback_return(self):
        self.mutations(self.contract('caller_words','s'),[
            ('(0x2ca94#32)','(0x2ca9c#32)'),
            ('=s.regs 7 ∧','=s.regs 6 ∧')])
        self.succeeds(self.contract('prologue_words','s'))
        self.succeeds(self.contract('firing_frame',ARGS,True))

    def test_frame_extension_preserves_execution(self):
        self.succeeds(self.contract('framed_finished',ARGS+' safe',True))
        self.mutations(self.contract('framed',ARGS+' safe',True),[
            ('(safe : ReturnSafe (s.regs 4) lines)','(safe : True)')])

    def test_restored_parent_frame_requires_protection(self):
        self.mutations(self.contract('parent_return',ARGS+' safe',True),[
            ('(safe : ReturnSafe (s.regs 4) lines)','(safe : True)'),
            ('out.pc=0x2ca94','out.pc=0x2ca9c'),
            ('out.core.regs 4=s.regs 4-(112#32)','out.core.regs 4=s.regs 4-(108#32)')])

    def test_joined_prefix_stops_at_thing_gate(self):
        self.mutations(self.contract('firing_to_things',ARGS+' safe f',True),[
            ('steps≤377+281*c.ids.length','steps≤376+281*c.ids.length'),
            ('out.pc=0x2ca9c','out.pc=0x2c5a0'),
            ('⟨s,f,OriginalWeaponDischarge.afterSound gun⟩','⟨s,f,0⟩')])

    def test_aliasing_return_words_is_rejected(self):
        self.succeeds(HEADER+'''
example : ¬ReturnSafe (1#32) (0xffffff53#32) := by
  intro h
  exact h.stamps ((1#32)-120) (by simp [returnWords]) 0 (by decide)
    ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide)
example : ¬ReturnSafe (0x2ba98#32) (0x600200#32) := by
  intro h
  exact (h.array ((0x2ba98#32)-120) (by simp [returnWords])).1 0 (by decide) 0 (by simp)
    ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide)
''')

    def test_concrete_wrapping_frame_survives_both_scan_outcomes(self):
        # Reuse the established two-item scan fixture, adding actual saved words.
        source=(ROOT/'tests/reference/e1m1-scan-contracts.lean').read_text()
        source=source.replace('import Doom.Proofs.E1M1ScanContracts','import Doom.Proofs.E1M1ScanReturn')
        source=source.replace('(0xffffff85,0x2c5f0),','(0xffffff85,0x2c5f0),(0xffffff89,0xdeadbeef),(0xffffff8d,0x2ca94),')
        # Extend the existing finite-address separation lemma to the two new slots.
        a=source.index('theorem word_stamp_safe'); b=source.index('\ndef reads',a)
        helper=source[a:b].replace('word_stamp_safe','return_stamp_safe').replace('0x2c028,0xffffff81])','0x2c028,0xffffff81,0xffffff89,0xffffff8d])')
        marker='  rcases ha with '+ '|'.join(['rfl']*22)
        self.assertIn(marker,helper)
        helper=helper.replace(marker,marker+'|rfl|rfl')
        source=source[:b]+'\n'+helper+source[b:]
        source+='''
namespace ScanContractsFixture
open E1M1ScanReturn

theorem return_safe : ReturnSafe 1 0x600200 := by
  constructor
  · intro a ha id hi
    apply return_stamp_safe a _ id hi
    simp only [returnWords,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> simp
  · intro a ha
    simp only [returnWords,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl
    all_goals
      constructor
      · intro k hk off ho
        exact FloorCaller.apart_symm (record_apart k hk off ho _ (by decide) (by decide))
      · unfold Apart; decide

def framed_scan (same : Bool) := E1M1ScanReturn.protect (scan same) 2 0x2ba20 (E1M1PathMap.resolve 0x600200)
  (checked same) (returnWords 1) (by
    intro i hi a ha
    exact E1M1ScanContracts.protection (scan same) 1 0x600200 rfl i _ (ids ⟨i,hi⟩)
      ((items same).pointers ⟨i,hi⟩ (Fixed.ofInt 0)) a (stack_protected _ _ _ ha (return_safe.stamps a ha)))
  return_safe.array

theorem exact_return (same : Bool) :
    (result same).1.core.regs 0=1 ∧ (result same).1.core.regs 4=0xffffff91 ∧
    (result same).1.core.regs 7=0xdeadbeef ∧ (result same).1.pc=0x2ca94 := by
  have ret := OriginalLineMixedInvariant.parent_return (scan same) 2 0x2ba20 (E1M1PathMap.resolve 0x600200)
    (framed_scan same) {trace:=ray same} none (collected same)
    (fun i _ _ => E1M1ScanContracts.candidate_continues (ray same) 0x600200 cell.ids[i]! (data i))
    (by apply List.mem_append_right; cases same <;> decide)
    (by apply List.mem_append_right; cases same <;> decide)
  have saved : load32 (scan same).memory ((scan same).regs 4+(4#32))=(0xdeadbeef#32) := by cases same <;> decide
  have pc : load32 (scan same).memory ((scan same).regs 4+(8#32))=(0x2ca94#32) := by cases same <;> decide
  change _ ∧ _ ∧ _ ∧ _ at ret
  rw [saved,pc] at ret
  exact ret

example : (result false).1.pc=0x2ca94 := (exact_return false).2.2.2
example : (result true).1.core.regs 7=0xdeadbeef := (exact_return true).2.2.1
#print axioms exact_return
end ScanContractsFixture
'''
        out=self.succeeds(source)
        self.assertNotIn('sorryAx',out)
        self.rejects(source.replace('(result false).1.pc=0x2ca94 :=','(result false).1.pc=0x2ca9c :='))


if __name__=='__main__': unittest.main()

"""DOS valid-count stamps track the production visited array through a scan."""
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_visits as proof
HEADER='''import Doom.Proofs.OriginalLineVisits
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineMixedInvariant OriginalLineVisits
attribute [local irreducible] OriginalLineVisits.Represents Collision.SolidThing.attackEndpoint
'''
CONTEXT='''variable (initial : X86Memory.State) (n : Nat) (base : Word) (resolve : Collision.Intercept → Word)
  (h : Initial initial n base resolve) (lines : Word) (count : Nat)
  (layout : OriginalLineVisits.Layout initial h lines count)
'''
STEP='''variable (i : Nat) (s : X86Control.State) (r : Collision.PathResult)
  (inv : Stable initial h i s r) (hi : i<n)
'''
ARGS='initial n base resolve h lines count layout i s r inv hi'


class LineVisitsTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,name,args,context=''):
        source=(ROOT/'Doom/Proofs/OriginalLineVisits.lean').read_text()
        decl=re.split(r' :=(?: by)?\n',source[source.index('theorem '+name):],maxsplit=1)[0]
        return HEADER+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old): self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.previous.previous.previous.previous.setup.setup.caller.bounds.lookup.maps.pinned_data()
        _,_,raw=proof.extracted()
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('scan_execution','missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)
        text=(ROOT/'Doom/Proofs/OriginalLineVisits.lean').read_text()
        self.assertEqual(proof.PROOFS,re.findall(r'^theorem (\w+)',text,re.M))

    def test_stride_and_duplicate_bit(self):
        self.mutations(self.contract('stamps_apart','lines i j hi hj ne'),[
            ('(ne : i≠j)','(ne : True)'),('(hi : i<32768)','(hi : True)')])
        self.mutations(self.contract('set_already','seen id bound yes'),[
            ('(yes : seen[id]! = true)','(yes : True)'),('seen.set! id true=seen','seen.set! id false=seen')])

    def test_freshness_is_not_inferred_from_wraparound(self):
        self.mutations(self.contract('fresh_represents','memory lines epoch count counter fresh'),[
            ('(fresh : ∀ j<count, load32 memory (stamp lines j)≠epoch)','(fresh : True)'),
            ('(counter : load32 memory 0x13580=epoch)','(counter : True)')])
        self.succeeds('''import Doom.Proofs.OriginalLineVisits
open Doom Doom.Proofs Doom.Verification X86Memory OriginalLineVisits
example : ¬Represents (fun _ => 0) 0x600200 0 #[false] := by
  intro h
  have bad := (h.2 0 (by decide)).mp (by decide)
  contradiction
example : Represents (fun _ => 0) 0x600200 0 #[true] := by
  constructor
  · decide
  · intro j hj
    have eq : j=0 := by change j<1 at hj; omega
    subst j; decide
''')

    def test_step_preserves_mutable_stamp_relation(self):
        for name in ['duplicate_iff','step_represents']:
            self.mutations(self.contract(name,ARGS+' epoch seen size represented',CONTEXT+STEP),[
                ('(layout : OriginalLineVisits.Layout initial h lines count)','(layout : True)'),
                ('(represented : Represents s.core.memory lines epoch seen)','(represented : True)'),
                ('(inv : Stable initial h i s r)','(inv : True)')])

    def test_complete_scanned_prefix(self):
        self.mutations(self.contract('scan_execution','initial n base resolve h lines count layout f r collected epoch seen size represented',CONTEXT),[
            ('(layout : OriginalLineVisits.Layout initial h lines count)','(layout : True)'),
            ('(collected : OriginalLineCollection.Tracks initial base resolve r.collected n)','(collected : True)'),
            ('(represented : Represents initial.memory lines epoch seen)','(represented : True)'),
            ('⟨initial,f,0x2c57f⟩ out.machine','⟨initial,f,0x2c580⟩ out.machine')])
        self.mutations(self.contract('scan_represents','initial n base resolve h lines count layout i s r inv k bound epoch seen size represented',CONTEXT+STEP),[
            ('(bound : i+k≤n)','(bound : True)')])

    def test_firing_entry_connection(self):
        self.mutations(self.contract('firing_represents','gun s actor thing angle ox oy geometry before after lines seen safe bits'),[
            ('(before : E1M1ScanMemory.BeforeInit gun s (0x13580#32))','(before : True)'),
            ('(safe : ∀ j<seen.size, E1M1PathMapFiring.Safe gun s (stamp lines j))','(safe : True)'),
            ('(bits : ∀ j<seen.size, (load32 s.memory (stamp lines j)=load32 s.memory 0x13580+1 ↔ seen[j]! = true))','(bits : True)')])

    def test_mixed_and_early_stop_fixtures(self):
        for name,old,new in [
            ('original-line-visits','#[true,true]','#[true,false]'),
            ('original-line-visits-outcomes','#[true,false]','#[true,true]')]:
            source=(ROOT/'tests/reference'/f'{name}.lean').read_text()
            out=self.succeeds(source)
            self.assertNotIn('sorryAx',out);self.assertNotIn('_native',out)
            self.rejects(source.replace(old,new))


if __name__=='__main__': unittest.main()

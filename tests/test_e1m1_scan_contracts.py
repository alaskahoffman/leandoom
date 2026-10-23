"""Assembled aiming scan inputs, original execution and sentinel return."""
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_scan_contracts as proof
HEADER='''import Doom.Proofs.E1M1ScanContracts
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (linePointer SideSafe ScratchSafe Geometry)
open OriginalLineMixedInvariant (atIndex Candidate ArraySafe)
open E1M1ScanContracts
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage
'''
ARGS='s sp cursor lines trace c data stack list items ids target active geometry computed back layout'


class ScanContractsTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,name,args,joined=False):
        source=(ROOT/'Doom/Proofs/E1M1ScanContracts.lean').read_text()
        context=''
        if joined:
            context=source[source.index('variable (',source.index('section Joined')):source.index('/-- The same assembled')]
        kind='def' if name=='initial' else 'theorem'
        decl=re.split(r' :=(?: by)?\n',source[source.index(kind+' '+name+' '):],maxsplit=1)[0]
        decl=decl.replace(kind+' '+name,'def contractCheck' if name=='initial' else 'example',1)
        return HEADER+context+decl+' :=\n  E1M1ScanContracts.'+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old): self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data(); _,_,raw=proof.extracted()
        out=self.succeeds(proof.certificate(data,raw)); proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('through_sentinel','missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)
        text=(ROOT/'Doom/Proofs/E1M1ScanContracts.lean').read_text()
        self.assertEqual(proof.PROOFS,[a or b for a,b in re.findall(r'^(?:theorem (\w+)|def (initial)) ',text,re.M)])

    def test_firing_flag_and_back_encoding(self):
        self.mutations(self.contract('firing_active','gun s actor thing angle ox oy geometry safe'),[
            ('(safe : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x2c024#32))','(safe : True)'),
            ('memory 0x2c024=0','memory 0x2c024=4')])
        self.mutations(self.contract('firing_back','gun s actor thing angle ox oy geometry line p back safe'),[
            ('(back : load32 s.memory (p+50)=0 ↔ line.back.isNone=true)','(back : True)'),
            ('(safe : E1M1PathMapFiring.Safe gun s (p+50))','(safe : True)')])

    def test_read_set_covers_sentinel_and_candidates(self):
        self.mutations(self.contract('list_member','sp cursor n cs i hi'),[
            ('(hi : i≤n)','(hi : i≤n+1)')])
        self.mutations(self.contract('read_member','sp cursor n cs i hi a ha'),[
            ('(hi : i<n)','(hi : i≤n)'),('(ha : a∈(cs i).reads)','(ha : True)')])

    def test_protection_requires_static_separation(self):
        self.mutations(self.contract('protection','s sp lines stack i id bound pointer a safe'),[
            ('(safe : Protected sp lines a)','(safe : True)'),
            ('(bound : id<475)','(bound : id<476)'),
            ('s.regs 4=sp-(124#32)','s.regs 4=sp-(120#32)')])

    def test_initial_contract_keeps_data_obligations(self):
        source=self.contract('initial',ARGS)
        self.mutations(source,[
            ('(active : load32 s.memory 0x2c024=0)','(active : True)'),
            ('(target : load32 s.memory (s.regs 4)=(0x2c5f0#32))','(target : True)'),
            ('(layout : Layout sp cursor lines c.ids.length (candidates trace lines c.ids data))','(layout : True)'),
            ('=.ok (data i.val).frac)', '=.ok (Fixed.ofInt 0))')])

    def test_visited_layout_and_execution(self):
        self.mutations(self.contract('visit_layout',ARGS+' stamps',joined=True),[
            ('(stamps : Stamps sp lines)','(stamps : True)')])
        self.mutations(self.contract('scan_execution',ARGS+' stamps f r collected epoch seen size represented',joined=True),[
            ('(represented : OriginalLineVisits.Represents s.memory lines epoch seen)','(represented : True)'),
            ('(size : seen.size=475)','(size : seen.size=474)')])

    def test_sentinel_requires_capacity(self):
        source=self.contract('through_sentinel',ARGS+' f r collected',joined=True)
        self.mutations(source,[
            ('(collected : OriginalLineCollection.Tracks s 0x2ba20 (E1M1PathMap.resolve lines) r.collected c.ids.length)','(collected : True)'),
            ('steps≤281*c.ids.length+7','steps≤281*c.ids.length')])

    def test_concrete_duplicate_and_rejected_scans(self):
        source=(ROOT/'tests/reference/e1m1-scan-contracts.lean').read_text()
        out=self.succeeds(source)
        self.assertNotIn('sorryAx',out); self.assertNotIn('_native',out)
        self.rejects(source.replace('#[((43690:Int),true,0)]','#[((43690:Int),true,1)]'))


if __name__=='__main__': unittest.main()

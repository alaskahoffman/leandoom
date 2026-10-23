"""Initial-state geometry transport, second endpoint, and DOS skip/crossing branch."""
import copy
import json
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_thing_crossing as proof
import verify_original_inline_thrust as extraction
HEADER='''import Doom.Proofs.E1M1ThingCrossing
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanMemory (firstScan)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (ArraySafe)
open OriginalThingDiagonal (points)
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage load32
attribute [local irreducible] Collision.thingIntercept Collision.interceptVector Collision.Divline.pointSide OriginalThingDiagonal.points
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'
HEAD=' returns flag links object lookupSafe global selected present stack'

class ThingCrossingTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,module,name,args,section=False,head=False):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        context=''
        if section:
            start=source.index('variable (',source.index('section Firing'))
            context=source[start:source.index('include input',start)]
        if head:
            start=source.index('variable (returns')
            context+=source[start:source.index('include returns',start)]
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[source.index('theorem '+name+' '):],maxsplit=1)[0]
        return HEADER+'open '+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old):self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),26)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('second_inputs','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_pinned_code_and_relocations_fail_closed(self):
        spec=json.loads((ROOT/'tests/reference/original-thing-second.json').read_text())
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        extraction.extract(binary,profile,spec)
        for kind in ['bytes','file','relocation']:
            bad=copy.deepcopy(spec);unit=bad['units']['thingSecond']
            if kind=='bytes':unit['hex']='90'+unit['hex'][2:]
            elif kind=='file':unit['file_offset']='0x1'
            else:unit['relocations'][0]['target']='0x2ba14'
            with self.subTest(kind=kind),self.assertRaises(ValueError):extraction.extract(binary,profile,bad)

    def test_initial_object_and_initialized_trace_transport(self):
        self.mutations(self.contract('E1M1ThingGeometry','object_read',ARGS+HEAD+' a safe callback',True,True),[
            ('(safe : E1M1ThingEntry.ReadSafe gun s lines a)','(safe : True)'),
            ('(callback : ∀ off∈[(4#32),8,12,16,20,24,28], Apart a (s.regs 4-(120#32)-off))','(callback : True)')])
        self.mutations(self.contract('E1M1ThingGeometry','trace_read',ARGS+HEAD+' a scan entry',True,True),[
            ('load32 (firstScan gun s).core.memory a','load32 s.memory a'),
            ('(scan : ScanSafe (s.regs 4) lines a)','(scan : True)'),
            ('(entry : EntrySafe (s.regs 4) a)','(entry : True)')])

    def test_inputs_are_derived_from_entry_contract(self):
        self.mutations(self.contract('E1M1ThingGeometry','callback_inputs',ARGS+HEAD+' target d',True,True),[
            ('(d : Data gun s lines object target)','(d : True)'),
            ('(path thing angle ox oy).trace target object','(path thing angle ox oy).trace thing object')])

    def test_second_endpoint_call_and_saved_first_side(self):
        self.mutations(self.contract('OriginalThingSecondSide','call_observe','s f'),[
            ('load32 s.memory (s.regs 4+(20#32))','load32 s.memory (s.regs 4+(16#32))'),
            ('(0x2c7a1#32)','(0x2c78d#32)'),
            ('(s.regs 4+(16#32))=s.regs 0','(s.regs 4+(20#32))=s.regs 0')])
        self.mutations(self.contract('OriginalThingSecondSide','second_inputs','s trace thing object h scratch'),[
            ('(h : OriginalThingFirstSide.Inputs s trace thing object)','(h : True)'),
            ('(points trace thing).2.2.1 (points trace thing).2.2.2','(points trace thing).1 (points trace thing).2.1'),
            ('Apart a (s.regs 4+(16#32))','Apart a (s.regs 4+(20#32))')])

    def test_execution_bound_and_preservation(self):
        self.mutations(self.contract('OriginalThingSecondSide','execution','s f'),[
            ('∃ n≤53','∃ n≤52'),('⟨s,f,0x2c78d⟩','⟨s,f,0x2c7a1⟩')])
        self.mutations(self.contract('OriginalThingSecondSide','frame','s a safe'),[
            ('(safe : Safe (s.regs 4) a)','(safe : True)')])
        self.mutations(self.contract('E1M1ThingCrossing','collection','s base resolve hits reserve tracked safe'),[
            ('(safe : StackSafe (s.regs 4) base)','(safe : True)')])

    def test_live_branch_and_production_no_hit(self):
        self.mutations(self.contract('OriginalThingSecondSide','live','s trace thing object h scratch'),[
            ('then 0x2c805 else 0x2c7ae','then 0x2c7ae else 0x2c805'),
            ('(crossing s).core.regs 0=(1#32)','(crossing s).core.regs 0=(0#32)'),
            ('Collision.thingIntercept trace thing=.ok none','Collision.thingIntercept trace thing=.ok (some (Fixed.ofInt 0))')])

    def test_continuous_firing_join(self):
        self.mutations(self.contract('E1M1ThingCrossing','firing_crossing',ARGS+HEAD+' target d sideStack secondStack traceScratch f',True,True),[
            ('steps≤533+281*c.ids.length','steps≤532+281*c.ids.length'),
            ('(d : E1M1ThingGeometry.Data gun s lines object target)','(d : True)'),
            ('(secondStack : StackSafe (s.regs 4-(172#32)) 0x2ba20)','(secondStack : True)'),
            ('then 0x2c805 else 0x2c7ae','then 0x2c7ae else 0x2c805')])

    def test_same_opposite_axes_zero_xor_and_wrapping_fixture(self):
        source=(ROOT/'tests/reference/original-thing-crossing.lean').read_text()
        self.assertNotIn('sorryAx',self.succeeds(source))
        self.rejects(source.replace('out.pc=0x2c805 ∧','out.pc=0x2c7ae ∧'))

if __name__=='__main__':unittest.main()

"""DOS object fraction, exact negative filter, and common firing-entry composition."""
import copy
import json
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_thing_fraction as proof
import verify_original_inline_thrust as extraction
HEADER='''import Doom.Proofs.E1M1ThingFraction
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanMemory (firstScan)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (ArraySafe)
open OriginalThingDiagonal (points)
open OriginalThingSecondSide (firstSide lastSide)
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage load32
attribute [local irreducible] Collision.thingIntercept Collision.interceptVector Collision.Divline.pointSide OriginalThingDiagonal.points
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'
HEAD=' returns flag links object lookupSafe global selected present stack'

class ThingFractionTests(unittest.TestCase):
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
        self.assertEqual(len(spec['units']),27)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('decision_live','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_pinned_code_and_relocations_fail_closed(self):
        spec=json.loads((ROOT/'tests/reference/original-thing-fraction.json').read_text())
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        extraction.extract(binary,profile,spec)
        for kind in ['bytes','file','relocation']:
            bad=copy.deepcopy(spec);unit=bad['units']['thingFraction']
            if kind=='bytes':unit['hex']='90'+unit['hex'][2:]
            elif kind=='file':unit['file_offset']='0x1'
            else:unit['relocations'][0]['target']='0x2ba14'
            with self.subTest(kind=kind),self.assertRaises(ValueError):extraction.extract(binary,profile,bad)

    def test_setup_encodes_actual_diagonal_and_return(self):
        self.mutations(self.contract('OriginalThingFraction','setup_return','s'),[
            ('(0x2c7d1#32)','(0x2c6bb#32)')])
        self.mutations(self.contract('OriginalThingFraction','encoded','s trace thing h'),[
            ('(h : Inputs s trace thing)','(h : True)'),
            ('0x2ba10 (s.regs 4)','0x2ba10 (s.regs 4+4)')])
        self.mutations(self.contract('OriginalThingFraction','setup_memory','s trace thing h'),[
            ('(h : Inputs s trace thing)','(h : True)')])

    def test_endpoints_and_trace_derived_through_both_side_tests(self):
        self.mutations(self.contract('OriginalThingFractionInputs','endpoints','s trace thing object h'),[
            ('(s.regs 4+(20#32))','(s.regs 4+(16#32))'),
            ('core.regs 7=(points trace thing).1','core.regs 7=(points trace thing).2.2.1')])
        self.mutations(self.contract('OriginalThingFractionInputs','inputs','s trace thing object h scratch safe'),[
            ('(h : OriginalThingFirstSide.Inputs s trace thing object)','(h : True)'),
            ('Apart a (s.regs 4+(16#32))','Apart a (s.regs 4+(20#32))'),
            ('(safe : ∀ a∈OriginalThingFraction.traceReads, OriginalThingFraction.Safe (s.regs 4) a)','(safe : True)')])

    def test_fraction_exact_and_production_negative_filter(self):
        self.mutations(self.contract('OriginalThingFraction','live','s trace thing h frac ok'),[
            ('(fraction s).core.regs 0=frac.raw.toBitVec','(fraction s).core.regs 0=frac.raw.toBitVec+1'),
            ('(ok : Collision.interceptVector trace (diagonal trace thing)=.ok frac)','(ok : True)')])
        self.mutations(self.contract('OriginalThingFraction','production','trace thing frac crossed ok'),[
            ('if frac.raw<0 then none else some frac','if frac.raw≤0 then none else some frac'),
            ('(crossed : OriginalThingSecondSide.firstSide trace thing≠OriginalThingSecondSide.lastSide trace thing)','(crossed : True)')])
        self.mutations(self.contract('OriginalThingFraction','decision_live','s trace thing h frac ok'),[
            ('then 0x2c7da else 0x2c7e4','then 0x2c7e4 else 0x2c7da')])

    def test_bounded_execution_and_all_writes_protected(self):
        self.mutations(self.contract('OriginalThingFraction','execution','s f safe'),[
            ('∃ n≤80','∃ n≤79'),
            ('(safe : OriginalInterceptVector.Safe (setup s))','(safe : True)')])
        self.mutations(self.contract('OriginalThingFraction','frame','s a safe'),[
            ('(safe : Safe (s.regs 4) a)','(safe : True)')])
        self.mutations(self.contract('E1M1ThingFraction','collection','s base resolve hits reserve tracked safe'),[
            ('(safe : StackSafe (s.core.regs 4) base)','(safe : True)')])

    def test_firing_entry_join_needs_arithmetic_and_memory_contracts(self):
        self.mutations(self.contract('E1M1ThingFraction','firing_fraction',ARGS+HEAD+' target d sideStack secondStack traceScratch fractionStack traceSafe computed f',True,True),[
            ('steps≤613+281*c.ids.length','steps≤612+281*c.ids.length'),
            ('(d : E1M1ThingGeometry.Data gun s lines object target)','(d : True)'),
            ('(fractionStack : StackSafe (s.regs 4-(172#32)) 0x2ba20)','(fractionStack : True)'),
            ('(traceSafe : ∀ a∈OriginalThingFraction.traceReads, OriginalThingFraction.Safe (s.regs 4-(172#32)) a)','(traceSafe : True)'),
            ('∃ frac, Collision.interceptVector (path thing angle ox oy).trace (OriginalThingFraction.diagonal (path thing angle ox oy).trace target)=.ok frac','True')])

    def test_positive_negative_zero_parallel_axes_and_wrapping_fixture(self):
        source=(ROOT/'tests/reference/original-thing-fraction.lean').read_text()
        self.assertNotIn('sorryAx',self.succeeds(source))
        self.rejects(source.replace('out.core.regs 0=65536','out.core.regs 0=65535'))

if __name__=='__main__':unittest.main()

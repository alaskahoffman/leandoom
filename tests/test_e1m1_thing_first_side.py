"""DOS object diagonal, actual production endpoints, first-side helper and firing join."""
import copy
import json
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_thing_first_side as proof
import verify_original_inline_thrust as extraction
HEADER='''import Doom.Proofs.E1M1ThingFirstSide
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (ArraySafe)
open OriginalThingDiagonal (points)
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage load32
attribute [local irreducible] Collision.thingIntercept Collision.interceptVector Collision.Divline.pointSide OriginalThingDiagonal.points
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'

class ThingFirstSideTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,module,name,args,section=False):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        context=''
        if section:
            start=source.index('variable (',source.index('section Firing'))
            context=source[start:source.index('include input',start)]
            context+='variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines) (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)\n'
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[source.index('theorem '+name+' '):],maxsplit=1)[0]
        return HEADER+'open '+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old):self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),25)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('live_diagonal','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_pinned_code_and_relocations_fail_closed(self):
        spec=json.loads((ROOT/'tests/reference/original-thing-diagonal.json').read_text())
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        extraction.extract(binary,profile,spec)
        for kind in ['bytes','file','relocation']:
            bad=copy.deepcopy(spec);unit=bad['units']['thingDiagonal']
            if kind=='bytes':unit['hex']='90'+unit['hex'][2:]
            elif kind=='file':unit['file_offset']='0x1'
            else:unit['relocations'][0]['target']='0x2ba14'
            with self.subTest(kind=kind),self.assertRaises(ValueError):extraction.extract(binary,profile,bad)

    def test_actual_runtime_expression_and_diagonal_inputs(self):
        self.mutations(self.contract('OriginalThingDiagonal','production','trace thing'),[
            ('if frac.raw<0 then none else some frac','if frac.raw≤0 then none else some frac'),
            ('⟨x1,y1,x2-x1,y2-y1⟩','⟨x1,y1,x2-x1,y1-y2⟩')])
        self.mutations(self.contract('OriginalThingDiagonal','live_diagonal','s trace thing object h'),[
            ('(h : Inputs s trace thing object)','(h : True)'),
            ('s.regs 4+(20#32)','s.regs 4+(16#32)'),
            ('(points trace thing).2.1.raw','(points trace thing).2.2.2.raw')])

    def test_exact_execution_and_call_return_word(self):
        self.mutations(self.contract('OriginalThingDiagonal','first_execution','s f'),[
            ('∃ n≤23','∃ n≤22'),('⟨s,f,0x2c72b⟩','⟨s,f,0x2c720⟩')])
        self.mutations(self.contract('OriginalThingDiagonal','first_observe','s'),[
            ('(0x2c78d#32)','(0x2c7a1#32)'),
            ('core.regs 0=x s-radius s','core.regs 0=x s+radius s')])

    def test_helper_inputs_require_trace_and_stack_separation(self):
        self.mutations(self.contract('OriginalThingFirstSide','helper_inputs','s trace thing object h'),[
            ('(h : Inputs s trace thing object)','(h : True)'),
            ('(points trace thing).1 (points trace thing).2.1','(points trace thing).2.2.1 (points trace thing).2.2.2')])
        self.mutations(self.contract('OriginalThingFirstSide','frame','s a safe'),[
            ('(safe : Safe s a)','(safe : True)')])
        self.mutations(self.contract('E1M1ThingFirstSide','collection','s base resolve hits reserve tracked safe'),[
            ('(safe : StackSafe (s.regs 4) base)','(safe : True)')])

    def test_first_side_is_live_boolean_and_returns_to_caller(self):
        self.mutations(self.contract('OriginalThingFirstSide','live','s trace thing object h'),[
            ('pc=0x2c78d','pc=0x2c7a1'),
            ('OriginalDivlineSide.bit (trace.pointSide (points trace thing).1 (points trace thing).2.1)',
             'OriginalDivlineSide.bit (!(trace.pointSide (points trace thing).1 (points trace thing).2.1))')])

    def test_second_endpoint_survives_helper_stack_writes(self):
        self.mutations(self.contract('OriginalThingFirstSide','second_endpoint','s'),[
            ('s.regs 4+(20#32)','s.regs 4+(16#32)'),
            ('OriginalThingDiagonal.y2 s','OriginalThingDiagonal.y1 s')])

    def test_continuous_firing_execution_and_collection(self):
        self.mutations(self.contract('E1M1ThingFirstSide','firing_first_side',ARGS+' returns flag links object safe global selected present stack sideStack f',True),[
            ('(sideStack : StackSafe (s.regs 4-(172#32)) 0x2ba20)','(sideStack : True)'),
            ('steps≤480+281*c.ids.length','steps≤479+281*c.ids.length'),
            ('out.pc=0x2c78d','out.pc=0x2c7a1')])

    def test_signed_xor_zero_axes_and_wrapping_fixture(self):
        source=(ROOT/'tests/reference/original-thing-first-side.lean').read_text()
        self.assertNotIn('sorryAx',self.succeeds(source))
        self.rejects(source.replace(')).regs 6=65536 :=',')).regs 6=196608 :='))

if __name__=='__main__':unittest.main()

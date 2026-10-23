"""DOS object record insertion, epilogue, mixed pointers, and traversal continuation."""
import copy
import json
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_thing_finish as proof
import verify_original_inline_thrust as extraction
HEADER='''import Doom.Proofs.E1M1ThingFinish
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanMemory (firstScan)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (ArraySafe)
open OriginalThingDiagonal (points)
open OriginalThingSecondSide (firstSide lastSide)
open OriginalLineFinish (Encodes RecordAt)
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage load32
attribute [local irreducible] OriginalDivlineSide.result OriginalThingSecondSide.result OriginalThingFraction.result
attribute [local irreducible] Collision.thingIntercept Collision.interceptVector Collision.Divline.pointSide OriginalThingDiagonal.points
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'
HEAD=' returns flag links object lookupSafe global selected present stack'

class ThingFinishTests(unittest.TestCase):
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
        self.assertEqual(len(spec['units']),28)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('firing_finish','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_pinned_code_and_relocations_fail_closed(self):
        spec=json.loads((ROOT/'tests/reference/original-thing-finish.json').read_text())
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        extraction.extract(binary,profile,spec)
        for kind in ['bytes','file','relocation']:
            bad=copy.deepcopy(spec);unit=bad['units']['thingFinish']
            if kind=='bytes':unit['hex']='90'+unit['hex'][2:]
            elif kind=='file':unit['file_offset']='0x1'
            else:unit['relocations'][0]['target']='0x2c024'
            with self.subTest(kind=kind),self.assertRaises(ValueError):extraction.extract(binary,profile,bad)

    def test_exact_epilogue_and_record_words(self):
        self.mutations(self.contract('OriginalThingFinish','unwind_observe','s'),[
            ('(s.regs 4+(36#32))','(s.regs 4+(40#32))'),
            ('s.regs 4+(52#32)','s.regs 4+(48#32)'),
            ('(s.regs 4+(48#32))','(s.regs 4+(44#32))')])
        self.mutations(self.contract('OriginalThingFinish','written_record','s safe'),[
            ('(cursor s+(4#32))=(0#32)','(cursor s+(4#32))=(1#32)'),
            ('(cursor s+(8#32))=s.regs 1','(cursor s+(8#32))=s.regs 2')])
        self.mutations(self.contract('OriginalThingFinish','written_cursor','s'),[
            ('cursor s+(12#32)','cursor s+(8#32)')])

    def test_ordered_append_requires_kind_pointer_capacity_and_separation(self):
        self.mutations(self.contract('OriginalThingFinish','append_encoded','s base resolve hits hit enabled encoded atEnd fraction kind pointer newSafe oldSafe'),[
            ('(kind : hit.isLine=false)','(kind : hit.isLine=true)'),
            ('(pointer : s.core.regs 1=resolve hit)','(pointer : True)'),
            ('(newSafe : ∀ off∈[(0#32),4,8], Apart (cursor s.core+off) (0x2c028#32))','(newSafe : True)')])
        self.mutations(self.contract('OriginalThingFinish','append_tracks','s base resolve r frac id enabled tracked capacity fraction pointer metadata'),[
            ('(capacity : r.collected.size<128)','(capacity : r.collected.size≤128)')])

    def test_saved_frame_survives_geometry_and_return(self):
        self.mutations(self.contract('E1M1ThingReturn','view_saved','s off ho'),[
            ('off∈[(24#32),28,32,36,40,44,48]','off∈[(20#32),28,32,36,40,44,48]')])
        self.mutations(self.contract('E1M1ThingReturn','returned','s safe'),[
            ('(safe : ReturnSafe s)','(safe : True)'),
            ('(s.regs 4+(48#32))','(s.regs 4+(44#32))')])

    def test_returned_traversal_reads_post_callback_link(self):
        self.mutations(self.contract('E1M1ThingReturn','execution','s trace target h safe ret'),[
            ('∃ n≤20','∃ n≤19'),
            ('load32 (finished s).core.memory','load32 s.memory'),
            ('(ret : load32 s.memory (s.regs 4+(48#32))=(0x2c5d7#32))','(ret : True)')])

    def test_mixed_pointer_mapping_requires_line_only_prefix(self):
        self.mutations(self.contract('E1M1ThingFinish','relabel','s base lines objects r h tracked'),[
            ('(h : AllLines r)','(h : True)')])
        self.mutations(self.contract('E1M1ThingFinish','metadata','i hi off ho'),[
            ('(hi : i<128)','(hi : i≤128)')])

    def test_continuous_firing_return_and_production_collection(self):
        self.mutations(self.contract('E1M1ThingFinish','firing_finish',ARGS+HEAD+' target d sideStack secondStack traceScratch fractionStack traceSafe computed id objects objectId capacity returnStack f',True,True),[
            ('steps≤633+281*c.ids.length','steps≤632+281*c.ids.length'),
            ('(objectId : objects id=object)','(objectId : True)'),
            ('(returnStack : ∀ off∈[(36#32),48], ArraySafe 0x2ba20 (s.regs 4-(172#32)+off))','(returnStack : True)'),
            ('load32 out.core.memory (object+(44#32))','load32 s.memory (object+(44#32))')])

    def test_record_return_rejections_and_alias_fixture(self):
        source=(ROOT/'tests/reference/original-thing-finish.lean').read_text()
        self.assertNotIn('sorryAx',self.succeeds(source))
        self.rejects(source.replace('load32 out.core.memory 0x2ba30=0','load32 out.core.memory 0x2ba30=1'))

if __name__=='__main__':unittest.main()

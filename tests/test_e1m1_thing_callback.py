"""Original object callback ABI, initial-memory contracts and resume semantics."""
import copy
import json
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_thing_callback as proof
import verify_original_inline_thrust as extraction
HEADER='''import Doom.Proofs.E1M1ThingCallback
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (ArraySafe)
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage load32
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'

class ThingCallbackTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,name,args,joined=False,section=False):
        module='E1M1ThingCallback' if joined else 'OriginalThingCallback'
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        context=''
        if section:
            start=source.index('variable (',source.index('section Firing'))
            context=source[start:source.index('include input',start)]
            context+='variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines) (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)\n'
        decl=re.split(r' :=(?: by)?\n',source[source.index('theorem '+name+' '):],maxsplit=1)[0]
        return HEADER+'open '+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old):self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),24)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('saved_cursor','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in [('OriginalThingCallback',proof.GENERIC),('E1M1ThingCallback',proof.PROOFS)]:
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_pinned_units_fail_closed(self):
        spec=json.loads((ROOT/'tests/reference/original-thing-callback.json').read_text())
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        extraction.extract(binary,profile,spec)
        for kind in ['bytes','file','relocation']:
            bad=copy.deepcopy(spec)
            if kind=='bytes':bad['units']['thingCall']['hex']='90'+bad['units']['thingCall']['hex'][2:]
            elif kind=='file':bad['units']['thingPrepare']['file_offset']='0x1'
            else:bad['units']['thingCall']['relocations']=[dict(offset=0,object=3,target='0x2c720')]
            with self.subTest(kind=kind),self.assertRaises(ValueError):extraction.extract(binary,profile,bad)

    def test_real_call_requires_target_and_exact_entry(self):
        self.mutations(self.contract('enter_execution','s f target'),[
            ('(target : load32 s.memory (s.regs 4)=(0x2c720#32))','(target : True)'),
            ('[] 10 ⟨s,f,0x2c5d2⟩','[] 9 ⟨s,f,0x2c5d2⟩'),
            ('⟨s,f,0x2c5d2⟩','⟨s,f,0x2c5d7⟩')])
        self.mutations(self.contract('call_observe','s f'),[
            ('core.regs 0=s.regs 2','core.regs 0=s.regs 0'),
            ('(0x2c5d7#32)','(0x2cab1#32)')])

    def test_prologue_saves_object_and_return_at_exact_offsets(self):
        self.mutations(self.contract('enter_observe','s f'),[
            ('-(52#32)','-(48#32)'),('-(16#32)','-(12#32)'),
            ('(0x2c5d7#32)','(0x2c5d4#32)')])
        self.mutations(self.contract('saved_cursor','s'),[('-(12#32)','-(8#32)')])
        self.succeeds(self.contract('saved_return','s'))

    def test_frame_and_collection_require_all_stack_stores_disjoint(self):
        self.mutations(self.contract('enter_frame','s f a safe'),[
            ('(safe : ∀ off∈[(4#32),8,12,16,20,24,28], Apart a (s.regs 4-off))','(safe : True)'),
            ('[(4#32),8,12,16,20,24,28]','[(4#32),8,12,16,20,24]')])
        self.mutations(self.contract('collection','s f base resolve hits reserve tracked safe',True),[
            ('(safe : StackSafe (s.regs 4) base)','(safe : True)'),
            ('base resolve hits reserve :=','base resolve hits (reserve+1) :=')])

    def test_resume_reads_correct_link_and_branches_in_order(self):
        self.mutations(self.contract('resume_execution','s f'),[('∃ n≤5','∃ n≤4')])
        self.mutations(self.contract('resumed_observe','s'),[
            ('s.regs 2+(44#32)','s.regs 2+(40#32)'),
            ('then 0x2c5e2 else 0x2c5d2','then 0x2c5d2 else 0x2c5e2'),
            ('pc=0x2c5e7','pc=0x2c5e2')])

    def test_continuous_firing_join(self):
        self.mutations(self.contract('firing_enter',ARGS+' returns flag links object safe global selected present stack f',True,True),[
            ('(present : object≠(0#32))','(present : True)'),
            ('(stack : StackSafe (s.regs 4-(120#32)) 0x2ba20)','(stack : True)'),
            ('steps≤413+281*c.ids.length','steps≤412+281*c.ids.length'),
            ('out.pc=0x2c72b','out.pc=0x2c720'),
            ('-(136#32)','-(132#32)')])

    def test_wrapping_stack_and_post_callback_link_fixture(self):
        source=(ROOT/'tests/reference/original-thing-callback.lean').read_text()
        self.assertNotIn('sorryAx',self.succeeds(source))
        self.rejects(source.replace('core.regs 2=0x700c00','core.regs 2=0x700800'))

if __name__=='__main__':unittest.main()

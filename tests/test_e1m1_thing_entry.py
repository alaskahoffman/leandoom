"""Pinned thing iterator bounds, pointer selection and firing-entry transport."""
import copy
import json
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_thing_entry as proof
import verify_original_inline_thrust as extraction
HEADER='''import Doom.Proofs.E1M1ThingEntry
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (Initial ArraySafe)
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage load32
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'

class ThingEntryTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,name,args,generic=False,section=False):
        module='OriginalThingEntry' if generic else 'E1M1ThingEntry'
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        context=''
        if section:
            start=source.index('variable (',source.index('section Firing'))
            context=source[start:source.index('include input',start)]
            context+='variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines) (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)\n'
        decl=re.split(r' :=(?: by)?\n',source[source.index('theorem '+name+' '):],maxsplit=1)[0]
        decl=decl.replace('theorem '+name,'example',1)
        return HEADER+'open '+module+'\n'+context+decl+' :=\n  '+module+'.'+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old): self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),22)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('live_head','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        original=(ROOT/'Doom/Proofs/OriginalThingEntry.lean').read_text()
        joined=(ROOT/'Doom/Proofs/E1M1ThingEntry.lean').read_text()
        self.assertEqual(proof.GENERIC,re.findall(r'^theorem (\w+) ',original,re.M))
        self.assertEqual(proof.PROOFS,[a or b for a,b in re.findall(r'^(?:theorem (\w+)|def (extended|result|reads))',joined,re.M)])

    def test_pinned_bytes_and_relocations_fail_closed(self):
        spec=json.loads((ROOT/'tests/reference/original-thing-entry.json').read_text())
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        extraction.extract(binary,profile,spec)
        for kind in ['bytes','file','relocation']:
            bad=copy.deepcopy(spec)
            if kind=='bytes':bad['units']['thingLookup']['hex']='90'+bad['units']['thingLookup']['hex'][2:]
            elif kind=='file':bad['units']['thingEntry']['file_offset']='0x6e5b5'
            else:bad['units']['thingLookup']['relocations'][0]['target']='0x2c100'
            with self.subTest(kind=kind), self.assertRaises(ValueError):extraction.extract(binary,profile,bad)

    def test_original_prefix_and_true_returns(self):
        self.mutations(self.contract('execution','s f',True),[
            ('∃ n≤20','∃ n≤19'),('⟨s,f,0x2c5a0⟩','⟨s,f,0x2c520⟩')])
        self.mutations(self.contract('outside_return','s outside',True),[
            ('(outside : ¬Inside (entry s))','(outside : True)'),
            ('core.regs 0=(1#32)','core.regs 0=(0#32)')])
        self.mutations(self.contract('empty_return','s inside empty',True),[
            ('(empty : head (guarded (entry s)).core=(0#32))','(empty : True)')])

    def test_bounds_and_pointer_read_require_representation(self):
        self.mutations(self.contract('live_bounds','s x y w h encoding',True),[
            ('(encoding : Inputs s x y w h)','(encoding : True)')])
        self.mutations(self.contract('live_head','s x y w h encoding inside links object global selected globalSafe headSafe',True),[
            ('(globalSafe : Apart (0x2c0f8#32) (s.regs 4-(4#32)))','(globalSafe : True)'),
            ('(headSafe : Apart (links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2)) (s.regs 4-(4#32)))','(headSafe : True)'),
            ('<<< 2','<<< 1')])

    def test_collection_keeps_capacity_and_requires_separation(self):
        self.mutations(self.contract('collection','s base resolve hits reserve tracked safe'),[
            ('(safe : ArraySafe base (s.regs 4-(4#32)))','(safe : True)'),
            ('base resolve hits reserve :=','base resolve hits (reserve+1) :=')])

    def test_firing_transports_reads_from_initial_memory(self):
        self.mutations(self.contract('scan_read',ARGS+' a safe',section=True),[
            ('(safe : ReadSafe gun s lines a)','(safe : True)')])
        self.succeeds(self.contract('call_read',ARGS+' returns a safe',section=True))
        self.succeeds(self.contract('bounds_inputs',ARGS+' returns links safe',section=True))
        self.mutations(self.contract('first_head',ARGS+' returns links object safe global selected',section=True),[
            ('(safe : ∀ a∈reads thing angle ox oy w links, ReadSafe gun s lines a)','(safe : True)'),
            ('=object :=','=links :=')])

    def test_continuous_lookup_has_correct_branch_outputs(self):
        self.mutations(self.contract('firing_lookup',ARGS+' returns flag links object safe global selected f',section=True),[
            ('then 0x2cab1 else 0x2c5d2','then 0x2c5d2 else 0x2cab1'),
            ('else s.regs 4-(120#32)','else s.regs 4-(116#32)'),
            ('(0x2c720#32)','(0x2c5f0#32)'),
            ('steps≤403+281*c.ids.length','steps≤402+281*c.ids.length')])

    def test_signed_edges_null_heads_and_wrapping_addresses(self):
        source=(ROOT/'tests/reference/original-thing-entry.lean').read_text()
        out=self.succeeds(source)
        self.assertNotIn('sorryAx',out)
        self.rejects(source.replace('theorem empty_true : (OriginalThingEntry.result (machine 0 0 36 23 1 0x800900 0)).core.regs 0=1',
            'theorem empty_true : (OriginalThingEntry.result (machine 0 0 36 23 1 0x800900 0)).core.regs 0=0'))

if __name__=='__main__':unittest.main()

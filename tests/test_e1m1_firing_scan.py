"""Post-sound firing to complete first-cell line scan, including proof boundaries."""
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_firing_scan as proof
HEADER='''import Doom.Proofs.E1M1FiringScan
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path linePointer)
open E1M1ScanContracts (LineData candidates)
open E1M1FiringScan
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.WordImage
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'


class FiringScanTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,name,args,joined=False):
        source=(ROOT/'Doom/Proofs/E1M1FiringScan.lean').read_text()
        context=''
        if joined:
            context=source[source.index('variable (',source.index('section Firing')):source.index('theorem boundary')]
        kind='def' if name=='initial' else 'theorem'
        decl=re.split(r' :=(?: by)?\n',source[source.index(kind+' '+name+' '):],maxsplit=1)[0]
        decl=decl.replace(kind+' '+name,'def contractCheck' if name=='initial' else 'example',1)
        return HEADER+context+decl+' :=\n  E1M1FiringScan.'+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old): self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data(); _,_,raw=proof.extracted()
        out=self.succeeds(proof.certificate(data,raw)); proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('firing_through_sentinel','missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)
        text=(ROOT/'Doom/Proofs/E1M1FiringScan.lean').read_text()
        self.assertEqual(proof.PROOFS,[a or b for a,b in re.findall(r'^(?:theorem (\w+)|def (initial)) ',text,re.M)])

    def test_saved_callback_is_derived(self):
        self.mutations(self.contract('caller_target','s x y w h dims mapX mapY inside'),[
            ('(0x2c5f0#32)','(0x2c5f1#32)'),
            ('(inside : Collision.pathCellInside x y w h=true)','(inside : True)')])

    def test_cursor_requires_image_and_selection(self):
        self.mutations(self.contract('caller_cursor','s base lines words c x y w h dims mapX mapY globals inside valid image safe selected'),[
            ('(image : E1M1PathMap.WordImage s.memory base words)','(image : True)'),
            ('(selected : words[4+Collision.pathCellIndex x y w]?=some c.offset)','(selected : True)'),
            ('2*c.offset) :=','2*c.offset+2) :=')])

    def test_shared_program_and_firing_boundary(self):
        self.succeeds(self.contract('firing_program','pc'))
        self.mutations(self.contract('boundary',ARGS,True),[
            ('(firstScan gun s).pc=0x2c57f','(firstScan gun s).pc=0x2c580')])

    def test_initial_contract_needs_firing_inputs(self):
        self.mutations(self.contract('initial',ARGS,True),[
            ('(input : Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)',
             '(input : True)')])

    def test_continuous_prefix_and_ordered_output(self):
        source=self.contract('firing_through_sentinel',ARGS+' f',True)
        self.mutations(source,[
            ('steps≤375+281*c.ids.length','steps≤374+281*c.ids.length'),
            ('⟨s,f,OriginalWeaponDischarge.afterSound gun⟩','⟨s,f,0⟩')])
        self.succeeds(self.contract('scan_return',ARGS+' f',True))

    def test_wrapping_map_cursor_and_saved_callback_fixture(self):
        source=(ROOT/'tests/reference/e1m1-path-map-caller.lean').read_text()
        source=source.replace('import Doom.Proofs.E1M1PathMapCaller','import Doom.Proofs.E1M1FiringScan')
        source+='\nnamespace PathMapCallerFixture\n' + r"""
theorem derived_target : load32 (scan state).core.memory ((scan state).core.regs 4)=(0x2c5f0#32) :=
  E1M1FiringScan.caller_target state 0 0 36 23 dims (by decide) (by decide) (by decide)
theorem derived_cursor : (scan state).core.regs 2=base+BitVec.ofNat 32 (2*cell.offset) :=
  E1M1FiringScan.caller_cursor state base lines words cell 0 0 36 23 dims (by decide) (by decide)
    globals (by decide) valid image image_safe (by decide)
example : (scan state).core.regs 2=(5#32) := derived_cursor
#print axioms derived_target
#print axioms derived_cursor
end PathMapCallerFixture
"""
        out=self.succeeds(source)
        self.assertNotIn('sorryAx',out)
        self.rejects(source.replace('(5#32) := derived_cursor','(6#32) := derived_cursor'))


if __name__=='__main__': unittest.main()

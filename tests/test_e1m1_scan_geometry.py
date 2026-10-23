"""Firing-entry geometry supplies the callback contracts without reached inputs."""
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_scan_geometry as proof
HEADER='''import Doom.Proofs.E1M1ScanGeometry
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry E1M1ScanMemory OriginalLineMixedInvariant
attribute [local irreducible] E1M1PathMap.WordImage Collision.SolidThing.attackEndpoint
'''


class ScanGeometryTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,name,args):
        source=(ROOT/'Doom/Proofs/E1M1ScanGeometry.lean').read_text()
        decl=re.split(r' :=\s*',source[source.index('theorem '+name):],maxsplit=1)[0]
        return HEADER+decl.replace('theorem '+name,'example',1)+' :=\n  E1M1ScanGeometry.'+name+' '+args+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old): self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data()
        _,_,raw=proof.extracted()
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('first_line_geometry','missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)
        text=(ROOT/'Doom/Proofs/E1M1ScanGeometry.lean').read_text()
        self.assertEqual(proof.PROOFS,re.findall(r'^theorem (\w+)',text,re.M))

    def test_stack_requires_successful_axis_and_inside_cell(self):
        self.mutations(self.contract('firing_stack','gun s actor thing angle ox oy geometry xout yout okX okY base lines words w h map inside'),[
            ('(okX : (path thing angle ox oy).xStep=.ok xout)','(okX : True)'),
            ('(inside : Collision.pathCellInside (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w h=true)','(inside : True)'),
            ('s.regs 4-(124#32)','s.regs 4-(120#32)')])

    def test_geometry_needs_line_trace_and_protection(self):
        self.mutations(self.contract('callback_geometry','s sp stack i trace line p v w pointer traceWords encoded safe'),[
            ('(encoded : LineWords s.memory line p v w)','(encoded : True)'),
            ('(safe : ∀ a∈OriginalLineSecondPoint.reads p v w, SideSafe sp a)','(safe : True)'),
            ('(trace.x.raw.toBitVec,trace.y.raw.toBitVec,trace.dx.raw.toBitVec,trace.dy.raw.toBitVec)',
             '(trace.y.raw.toBitVec,trace.x.raw.toBitVec,trace.dx.raw.toBitVec,trace.dy.raw.toBitVec)'),
            ('s.regs 4=sp-(124#32)','s.regs 4=sp-(120#32)')])

    def test_both_side_outcomes(self):
        for name,arg,op in [('rejection_inputs','same','='),('crossing_inputs','crosses','≠')]:
            self.mutations(self.contract(name,'s trace line p v w geometry '+arg),[
                (f'({arg} : OriginalLineSecondPoint.firstSide trace line{op}OriginalLineSecondPoint.lastSide trace line)',f'({arg} : True)')])

    def test_storage_requires_all_line_ids_and_stack_separation(self):
        self.mutations(self.contract('storage_layout','s sp lines stack i id bound pointer storage'),[
            ('(storage : Storage sp lines)','(storage : True)'),
            ('(bound : id<475)','(bound : id<476)'),
            ('s.regs 4=sp-(124#32)','s.regs 4=sp-(120#32)')])

    def test_firing_connection_requires_initial_inputs(self):
        args='gun s f weapon input actor thing angle ox oy geometry xout yout okX okY base lines words c w h map cursorSafe inside valid selected i line v1 v2 encoded lineSafe traceSafe callbackSafe storage'
        self.mutations(self.contract('first_line_geometry',args),[
            ('(encoded : LineWords s.memory line (linePointer lines c.ids[i.val]) v1 v2)','(encoded : True)'),
            ('(callbackSafe : ∀ a∈OriginalLineSecondPoint.reads (linePointer lines c.ids[i.val]) v1 v2, SideSafe (s.regs 4) a)','(callbackSafe : True)'),
            ('(storage : Storage (s.regs 4) lines)','(storage : True)'),
            ('OriginalWeaponDischarge.afterSound gun','OriginalWeaponDischarge.afterSound gun+1')])

    def test_concrete_wrapping_stack_and_geometry(self):
        source=(ROOT/'tests/reference/e1m1-scan-geometry.lean').read_text()
        out=self.succeeds(source)
        self.assertNotIn('sorryAx',out);self.assertNotIn('_native',out)
        self.rejects(source.replace('regs 4=0xffffff81','regs 4=0xffffff85'))
        self.rejects(source.replace('ray false) wall 0x600200 0x600400 0x600410 :=','ray false) wall 0x600200 0x600410 0x600400 :='))


if __name__=='__main__': unittest.main()

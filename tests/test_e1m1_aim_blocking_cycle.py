"""Guard selected wall/closed-sector stops and the real binary return path."""
import re
import unittest
from pathlib import Path
import test_e1m1_aim_portal_prefix as prior
import verify_e1m1_aim_blocking_cycle as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1AimPortalPrefixExit','import Doom.Proofs.E1M1AimBlockingCycle')+'\nopen E1M1AimWall (Safe)\n'
class AimBlockingCycleTests(unittest.TestCase):
    lean=prior.AimPortalPrefixTests.lean
    succeeds=prior.AimPortalPrefixTests.succeeds
    rejects=prior.AimPortalPrefixTests.rejects
    mutations=prior.AimPortalPrefixTests.mutations
    def contract(self,module,name,args):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r' ',text,re.M).start()
        decl=text[start:text.index(' := by',start)]
        decl=re.sub(r'\bprogram\b','E1M1AimRepeatProgram.program',decl)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),42)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimBlockingCycle.closed','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_closed_return_requires_real_stack_and_closed_gap(self):
        self.mutations(self.contract('E1M1AimClosedReturn','execution',proof.RETURN_ARGS),[
            ('(safe : E1M1AimReturnFrame.Safe s)','(safe : True)'),
            ('(returnWord : load32 s.memory (s.regs 4)=0x2c86d)','(returnWord : True)'),
            ('(closed : (if bc.toInt≤fc.toInt then bc else fc).toInt ≤\n      (if ff.toInt≤bf.toInt then bf else ff).toInt)','(closed : True)'),
            ('(result s).pc=0x2c88c','(result s).pc=0x2c887'),
            ('(result s).core.regs 4=s.regs 4+4','(result s).core.regs 4=s.regs 4'),
            ('n≤60','n≤59')])
    def test_closed_join_uses_reached_selection_and_catalog(self):
        self.mutations(self.contract('E1M1AimBlockingCycle','closed',proof.CLOSED_ARGS),[
            ('(history : History result.collected work seen visits)','(history : True)'),
            ('(selection : Selection result.collected work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)','(selection : True)'),
            ('(represented : Represents scene result.collected portals)','(represented : True)'),
            ('(listed : portals j=some p)','(listed : True)'),
            ('(blocked : min (front p).ceiling.raw (back p).ceiling.raw ≤ max (front p).floor.raw (back p).floor.raw)','(blocked : True)')])
    def test_closed_join_preserves_bounds_and_counts_stopping_visit(self):
        self.mutations(self.contract('E1M1AimBlockingCycle','closed',proof.CLOSED_ARGS),[
            ('out.pc=0x2c88c','out.pc=0x2c887'),
            ('out.core.regs 0=0','out.core.regs 0=1'),
            ('load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec','load32 out.core.memory (0x2c1e4#32)=upper.raw.toBitVec'),
            ('load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec','load32 out.core.memory (0x2c1e8#32)=lower.raw.toBitVec'),
            ('E1M1AimSource.stopped path (seen.length+1)','E1M1AimSource.stopped path seen.length')])
    def test_wall_join_keeps_map_flag_obligations_explicit(self):
        self.mutations(self.contract('E1M1AimBlockingCycle','wall',proof.WALL_ARGS),[
            ('(layout : E1M1AimCycleInvariant.Layout s work)','(layout : True)'),
            ('(flagsSafe : Safe (s.regs 4) (resolve result.collected[j]!+16))','(flagsSafe : True)'),
            ('(flags : (s.memory (resolve result.collected[j]!+16) &&& (4#8) != 0)=scene.lines[work[j]!.id]!.twoSided)','(flags : True)'),
            ('(solid : scene.lines[work[j]!.id]!.twoSided=false)','(solid : True)'),
            ('(isLine : (work[j]!).isLine=true)','(isLine : True)')])
    def test_wall_join_uses_exact_hit_suffix_and_return(self):
        self.mutations(self.contract('E1M1AimBlockingCycle','wall',proof.WALL_ARGS),[
            ('program [] 24','program [] 23'),
            ('out.pc=0x2c88c','out.pc=0x2c887'),
            ('out.core.regs 4=s.regs 4+4','out.core.regs 4=s.regs 4'),
            ('E1M1AimSource.stopped path (seen.length+1)','E1M1AimSource.stopped path seen.length'),
            ('load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec','load32 out.core.memory (0x2c1e4#32)=upper.raw.toBitVec')])
    def test_equal_heights_are_closed_signed_boundary(self):
        source=HEADER+'''
example (height : Fixed) :
    (if height.raw.toBitVec.toInt≤height.raw.toBitVec.toInt then height.raw.toBitVec else height.raw.toBitVec).toInt ≤
    (if height.raw.toBitVec.toInt≤height.raw.toBitVec.toInt then height.raw.toBitVec else height.raw.toBitVec).toInt :=
  (E1M1AimPortalSource.signed_bounds height height height height).mpr (by simp [min,max,Int32.le_iff_toInt_le])
'''
        self.mutations(source,[(').toInt ≤',').toInt <')])
if __name__=='__main__':unittest.main()

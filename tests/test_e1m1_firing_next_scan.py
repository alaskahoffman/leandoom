"""Firing must derive next-cell lookup inputs through both actual scans."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_things as previous
import verify_e1m1_firing_next_scan as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=previous.HEADER.replace('import Doom.Proofs.E1M1FiringThings','import Doom.Proofs.E1M1FiringNextScan')
HEADER+='open E1M1FiringGridState (initial)\n'
FULL=previous.ARGS+previous.HEAD+previous.DATA
MAP=FULL+' room world dimension ids scene'
NEXT=FULL+' locals room world dimension ids scene f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell'

class FiringNextScanTests(unittest.TestCase):
    lean=previous.FiringThingsTests.lean
    succeeds=previous.FiringThingsTests.succeeds
    rejects=previous.FiringThingsTests.rejects
    mutations=previous.FiringThingsTests.mutations

    def contract(self,module,name,args,section=False):
        return previous.FiringThingsTests.contract(self,module,name,args,section).replace(previous.HEADER,HEADER,1)

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('FiringNextScan.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_full_scan_frame_needs_both_parts_of_layout(self):
        self.mutations(self.contract('E1M1FiringCellMemory','firing_frame',FULL+' room a entrySafe objectSafe',True),[
            ('(entrySafe : E1M1ThingEntry.ReadSafe gun s lines a)','(entrySafe : True)'),
            ('(objectSafe : E1M1ThingVisit.ReadSafe (s.regs 4-(120#32)) a)','(objectSafe : True)')])

    def test_postline_frame_keeps_updated_memory_not_old_memory(self):
        self.mutations(self.contract('E1M1FiringCellMemory','after_lines_frame',FULL+' room a callSafe entrySafe objectSafe',True),[
            ('(callSafe : Apart a (s.regs 4-(116#32)))','(callSafe : True)'),
            ('(entrySafe : Apart a (s.regs 4-(120#32)))','(entrySafe : True)'),
            ('load32 (E1M1ScanReturn.finished '+previous.ARGS+').1.core.memory a','load32 s.memory a')])

    def test_flag_layout_needs_heap_separation(self):
        self.mutations(self.contract('E1M1FiringMapState','flag_safe','sp lines flag'),[
            ('(flag : E1M1ThingGate.FlagSafe sp lines)','(flag : True)')])
        self.mutations(self.contract('E1M1FiringMapState','flag_word',FULL+' room',True),[
            ('=(3#32)','=(1#32)'),
            ('(flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)','(flag : True)')])

    def test_reached_map_requires_initial_read_separation(self):
        self.mutations(self.contract('E1M1FiringMapState','map',MAP+' globalsSafe imageSafe',True),[
            ('(globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Safe (s.regs 4) lines a)','(globalsSafe : True)'),
            ('(imageSafe : ∀ i<words.size, Safe (s.regs 4) lines (base+BitVec.ofNat 32 (2*i)))','(imageSafe : True)')])

    def test_next_caller_reuses_only_protected_slots(self):
        self.mutations(self.contract('E1M1FiringNextScan','caller_array','sp cursor lines n cs layout returns off member'),[
            ('(member : off∈[(116#32),120,124])','(member : off∈[(116#32),120,44])'),
            ('(returns : E1M1ScanReturn.ReturnSafe sp lines)','(returns : True)')])

    def test_prefix_reaches_selected_next_cell_not_current_cell(self):
        self.mutations(self.contract('E1M1FiringNextScan','execution',NEXT,True),[
            ('(notEnd : E1M1PathAdvance.ended (initial (path thing angle ox oy) xout yout)=false)','(notEnd : True)'),
            ('(selectedCell : words[4+Collision.pathCellIndex x y w]?=some nextCell.offset)','(selectedCell : True)'),
            ('E1M1PathMapLookup.ScanWords out.core lines nextCell','E1M1PathMapLookup.ScanWords out.core lines c'),
            ('out.pc=0x2c57f','out.pc=0x2cab5')])

    def test_prefix_retains_hits_but_does_not_allocate_capacity(self):
        self.mutations(self.contract('E1M1FiringNextScan','execution',NEXT,True),[
            ('after.collected 0','after.collected nextCell.ids.length'),
            ('out.core.regs 4=s.regs 4-(124#32)','out.core.regs 4=s.regs 4-(112#32)'),
            ('steps≤457+','steps≤456+')])

if __name__=='__main__':unittest.main()

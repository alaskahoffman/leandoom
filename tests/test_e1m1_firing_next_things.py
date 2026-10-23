"""The return and object CALL must use actual saved words and preserve history."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_next_lines as prior
import verify_e1m1_firing_next_things as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringNextLines','import Doom.Proofs.E1M1FiringNextThings')
SCAN=prior.SCAN
FRAME=prior.prior.FRAME
NEXT=prior.NEXT
ENTER='s sp lines epoch objects hits seen pc success stack flag tracked represented array epochSafe stampSafe'

class FiringNextThingsTests(unittest.TestCase):
    lean=prior.FiringNextLinesTests.lean
    succeeds=prior.FiringNextLinesTests.succeeds
    rejects=prior.FiringNextLinesTests.rejects
    mutations=prior.FiringNextLinesTests.mutations

    def contract(self,module,name,args,section=False):
        if module!='E1M1NextLineReturn' or not section:
            return prior.FiringNextLinesTests.contract(self,module,name,args,section).replace(prior.HEADER,HEADER,1)
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=source.index('theorem '+name+' ')
        earlier=source[source.index('section Scan'):start]
        context=''.join(re.findall(r'^variable .*?(?=^include)',earlier,re.M|re.S))
        context+='\n'.join(re.findall(r'^include .+$',earlier,re.M))+'\n'
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('FiringNextThings.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_extra_read_requires_scan_and_array_protection(self):
        self.mutations(self.contract('E1M1NextLineReturn','read_word',SCAN+' f r tracked a safe',True),[
            ('(safe : E1M1ThingGeometry.ScanSafe sp lines a)','(safe : True)'),
            ('r.collected c.ids.length)','r.collected 0)')])

    def test_parent_return_restores_exact_words_and_stack(self):
        self.mutations(self.contract('E1M1NextLineReturn','parent_return',SCAN+' returns f r tracked',True),[
            ('(returns : E1M1ScanReturn.ReturnSafe sp lines)','(returns : True)'),
            ('out.core.regs 4=sp-(112#32)','out.core.regs 4=sp-(116#32)'),
            ('out.pc=(load32 s.memory (sp-(116#32))).toNat','out.pc=(load32 s.memory (sp-(120#32))).toNat')])

    def test_flag_needs_original_value_and_heap_separation(self):
        self.mutations(self.contract('E1M1NextLineReturn','flag_word',SCAN+' flag f r tracked value',True),[
            ('(flag : E1M1ThingGate.FlagSafe sp lines)','(flag : True)'),
            ('(value : load32 s.memory (E1M1ThingGate.flagWord sp)=(3#32))','(value : True)')])
        self.mutations(self.contract('E1M1NextSavedFrame','flag_safe','sp lines flag'),[
            ('(flag : E1M1ThingGate.FlagSafe sp lines)','(flag : True)')])

    def test_saved_return_word_comes_from_actual_call(self):
        self.mutations(self.contract('E1M1NextSavedFrame','saved_words',FRAME,True),[
            ('(s.regs 4-(116#32))=(0x2ca94#32)','(s.regs 4-(116#32))=(0x2cab1#32)'),
            ('load32 m (s.regs 4-(120#32))','load32 m (s.regs 4-(124#32))')])

    def test_enter_requires_success_enabled_and_real_return_pc(self):
        self.mutations(self.contract('E1M1FiringNextThings','enter',ENTER),[
            ('(pc : s.pc=0x2ca94)','(pc : s.pc=0x2cab1)'),
            ('(success : s.core.regs 0=(1#32))','(success : True)'),
            ('(flag : load32 s.core.memory (E1M1ThingGate.flagWord sp)=(3#32))','(flag : True)'),
            ('n≤8','n≤7')])

    def test_call_write_must_preserve_collection_epoch_and_stamps(self):
        self.mutations(self.contract('E1M1FiringNextThings','enter',ENTER),[
            ('(array : OriginalLineMixedInvariant.ArraySafe 0x2ba20 (sp-(116#32)))','(array : True)'),
            ('(epochSafe : Apart (0x13580#32) (sp-(116#32)))','(epochSafe : True)'),
            ('(stampSafe : ∀ j<seen.size, Apart (stamp lines j) (sp-(116#32)))','(stampSafe : True)'),
            ('hits 0 ∧','hits 1 ∧')])

    def test_joined_call_has_correct_destination_arguments_and_bound(self):
        self.mutations(self.contract('E1M1FiringNextThings','execution',NEXT,True),[
            ('steps≤482+281*(c.ids.length+nextCell.ids.tail.length)+230*nodes.length','steps≤481+281*(c.ids.length+nextCell.ids.tail.length)+230*nodes.length'),
            ('out.pc=0x2c5a0','out.pc=0x2c720'),
            ('out.core.regs 4=s.regs 4-(116#32)','out.core.regs 4=s.regs 4-(120#32)'),
            ('out.core.regs 3=(0x2c720#32)','out.core.regs 3=(0x2c5f0#32)')])

if __name__=='__main__':unittest.main()

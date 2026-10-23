"""Whole-loop composition, pinned counts, and required initial/layout premises."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_group_count_scan as proof
class GroupCountScanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw={'count':bytes.fromhex(json.loads((ROOT/'tests/reference/original-group-count.json').read_text())['units']['count']['hex'])}
        cls.data,_=proof.topology.pinned_data()
        cls.fixture=(ROOT/'tests/reference/original-group-count-scan.lean').read_text()
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_strict_audit(self):
        s=proof.certificate(self.raw,self.data)
        # The final counts and total allocation are conclusions, not inputs.
        premises=s.split('theorem scan_checked')[1].split(' :\n    ∃ out')[0]
        self.assertNotIn('2568',premises);self.assertNotIn('642',premises)
        self.assertNotIn('Ready',premises);self.assertNotIn('X86Routine.run',premises)
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('scan_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_initial_relations_are_required(self):
        s=proof.certificate(self.raw,self.data)
        for old,new in [
          ('(layout : Layout (topology.lines.map (E1M1GroupOutput.physical a)))','(layout : True)'),
          ('(inputs : OriginalGroupOutput.Inputs (topology.lines.map (E1M1GroupOutput.physical a)) s.memory)','(inputs : True)'),
          ('(linked : OriginalGroupOutput.Linked (topology.lines.map (E1M1GroupOutput.physical a)) (load32 s.memory 0x2c120))','(linked : True)'),
          ('(count : (load32 s.memory 0x2c134).toNat=475)','(count : (load32 s.memory 0x2c134).toNat=474)'),
          ('(zeros : ∀ i : Fin topology.sectors.length, load32 s.memory (a.sector i.val+78)=0)','(zeros : True)'),
          ('CounterSafe (a.sector i.val) (topology.lines.map (E1M1GroupOutput.physical a)))','True)')]:
            with self.subTest(premise=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_concrete_complete_loop_and_empty_entry(self):
        r=self.lean(self.fixture);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        self.assertNotIn('sorryAx',r.stdout);self.assertNotIn('_native',r.stdout)
    def test_wrong_count_allocation_and_aliased_global_rejected(self):
        for old,new in [('memory 0xa04e=3','memory 0xa04e=4'),
                        ('core.regs 0=16','core.regs 0=20'),
                        ('0xa000','0x2c0e6')]:
            with self.subTest(change=old):
                self.assertIn(old,self.fixture);r=self.lean(self.fixture.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_wrong_wad_row_and_missing_line_rejected(self):
        for mode in ['row','line']:
            data=copy.deepcopy(self.data)
            if mode=='row':data['rows'][0]=data['rows'][0][:-1]
            else:data['lines'].pop()
            r=self.lean(proof.certificate(self.raw,data));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
if __name__=='__main__':unittest.main()

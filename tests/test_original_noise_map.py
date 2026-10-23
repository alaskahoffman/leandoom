"""Stable DOS line arrays, derived cursors and automatic numeric loop guards."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_map as proof
class NoiseMapTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('budget_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_required_contracts(self):
        s=proof.certificate()
        for old,new in [('(safe : Protect (mapReads table) w)','(safe : True)'),
            ('(rep : E1M1NoiseMap.Rep e s.memory)','(rep : True)'),
            ('(small : e.lines.length≤2147483647)','(small : True)'),
            ('(guards : MemoryGuards table h)','(guards : True)'),
            ('(bounds : Bounded table limit)','(bounds : True)'),
            ('(rep : MapRep table s.core.memory)','(rep : True)'),
            ('(entry : Entry table phase s)','(entry : True)'),
            ('(map : MapRep table s.core.memory)','(map : True)'),
            ('2*table.length*(limit+1)+1','table.length*(limit+1)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_entry_selection_skip_child_resume_and_derived_fuel(self):
        r=self.lean((ROOT/'tests/reference/original-noise-map.lean').read_text())
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def prefix(self):
        s=(ROOT/'tests/reference/original-noise-map.lean').read_text()
        return s.split('theorem initial_safe')[0]+'open E1M1NoiseMap\n'+s.split('open E1M1NoiseMap\n')[1].split('theorem represented')[0]
    def test_count_pointer_and_array_corruption_rejected(self):
        for address,value in [('origin+78','2'),('origin+82','0'),('0x600b01','0')]:
            with self.subTest(address=address):
                s=self.prefix()+f'example : E1M1NoiseMap.Rep mainSector (store32 initial.core.memory ({address}) ({value})) := by\n  constructor <;> decide +kernel\nend Doom.Verification.NoiseMapFixture\n'
                r=self.lean(s);self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
    def test_out_of_bounds_or_misaligned_cursor_rejected(self):
        for register,value in [(6,1),(5,4)]:
            with self.subTest(register=register):
                s=self.prefix()+f'example : Cursor mainSector {{ parent.core with regs := write parent.core.regs {register} ({value}#32) }} := by\n  constructor <;> decide +kernel\nend Doom.Verification.NoiseMapFixture\n'
                r=self.lean(s);self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
if __name__=='__main__':unittest.main()

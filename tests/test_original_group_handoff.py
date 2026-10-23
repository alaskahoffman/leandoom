"""Executable binding, allocator/caller composition and nonvacuous memory contracts."""
import copy
import json
import os
import signal
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_group_handoff as proof


class GroupHandoffTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec = json.loads((ROOT/'tests/reference/original-group-handoff.json').read_text())
        cls.raw = {n:bytes.fromhex(v['hex']) for n,v in cls.spec['units'].items()}
        cls.fixture = (ROOT/'tests/reference/original-group-handoff.lean').read_text()

    def lean(self, source):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'Check.lean'; p.write_text(source)
            process = subprocess.Popen([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,
                                       stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True)
            try:
                stdout,stderr = process.communicate(timeout=60)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid,signal.SIGKILL)
                process.communicate()
                raise
            return subprocess.CompletedProcess(process.args,process.returncode,stdout,stderr)

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('error', result.stdout)

    def test_certificate_and_strict_audit(self):
        result = self.lean(proof.certificate(self.raw))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout+'extra',result.stdout.replace('handoff_checked','missing'),
                    result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','bad._native.ax_1')]:
            with self.assertRaises(ValueError): proof.audit(bad)

    def test_every_byte_interval_is_bound(self):
        for name in self.raw:
            with self.subTest(interval=name):
                raw = dict(self.raw); changed = bytearray(raw[name]); changed[0] ^= 1; raw[name] = bytes(changed)
                self.rejects(proof.certificate(raw))

    def test_initial_contracts_are_required(self):
        source = proof.certificate(self.raw)
        for old,new in [
            ('(user : s.regs 7=(0#32))','(user : True)'),
            ('(tag : s.regs 5=(50#32))','(tag : True)'),
            ('(safe : OriginalGroupAllocation.SafeWord (s.regs 4+16) s)','(safe : True)'),
            ('(ret : load32 s.memory (s.regs 4+16)=0x2e63e)','(ret : True)')]:
            with self.subTest(premise=old):
                self.assertIn(old,source); self.rejects(source.replace(old,new))

    def test_concrete_join_and_preservation(self):
        result = self.lean(self.fixture)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertNotIn('sorryAx',result.stdout); self.assertNotIn('_native',result.stdout)

    def test_wrong_results_rejected(self):
        for old,new in [('memory 0x63004e=3','memory 0x63004e=4'),
                        ('core.regs 6=0x620018','core.regs 6=0x62001c'),
                        ('core.regs 4=0x680014','core.regs 4=0x680010'),
                        (').pc=0x2e661',').pc=0x2e791')]:
            with self.subTest(change=old):
                self.assertIn(old,self.fixture); self.rejects(self.fixture.replace(old,new))

    def test_changed_saved_return_and_overlapping_counter_rejected(self):
        for old,new in [('store32 m 0x680010 0x2e63e','store32 m 0x680010 0x2e63f'),
                        ('0x63004e','0x620004')]:
            with self.subTest(change=old):
                self.rejects(self.fixture.replace(old,new))

    def test_extraction_mapping_and_relocations(self):
        profile = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary = proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        for mode in ['byte','mapping','relocation']:
            bad = copy.deepcopy(self.spec)
            unit = bad['units']['allocation']
            if mode=='byte': unit['hex']='90'+unit['hex'][2:]
            elif mode=='mapping': unit['file_offset']='0x7b746'
            else: unit['relocations'].pop()
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                proof.extraction.extract(binary,profile,bad)

if __name__ == '__main__': unittest.main()

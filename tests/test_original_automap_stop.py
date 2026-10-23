"""Byte binding, original notification, precondition and instruction regressions."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_automap_stop as proof
class AutomapStopTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-automap-stop.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.tables={k:bytes.fromhex(v['hex']) for k,v in self.spec['tables'].items()}
    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'Check.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw,self.tables,'test'));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'unexpected',r.stdout.replace('dos_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_changed_instructions_rejected(self):
        for name,offset in [('tag',37),('tag',52),('unload',49),('stop',25),('responder',21),('responderReturn',10),('choice',10),('guard',53)]:
            with self.subTest(unit=name,offset=offset):
                raw=dict(self.raw);b=bytearray(raw[name]);b[offset]^=1;raw[name]=bytes(b)
                r=self.lean(proof.certificate(raw,self.tables,'test'));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_original_event_is_not_exit_event_contract(self):
        self.assertEqual(self.tables['event'],bytes.fromhex('000000000100000000786d61'))
        changed=dict(self.tables);changed['event']=bytes.fromhex('0100000000786d6100000000')
        r=self.lean(proof.certificate(self.raw,changed,'test'));self.assertNotEqual(r.returncode,0);self.assertIn('event_checked',r.stdout)
    def test_required_contracts_and_bounds(self):
        source=proof.certificate(self.raw,self.tables,'test')
        for old,new in [
            ('(cache : AutomapStop.UnloadInputs (AutomapStop.stopUnload s))','(cache : True)'),
            ('(kind : load32 s.memory (0x12c98#32)=0)','(kind : True)'),
            ('(safe : ∀ b, b ∈ AutomapStop.dosWrites s → Apart (0x12c98#32) b)','(safe : True)'),
            ('[0x39af8] 226','[0x39af8] 1'),('[0x2a3c8] 250','[0x2a3c8] 1'),
            ('(h : AutomapStop.StopInputs s)','(h : AutomapStop.UnloadInputs (AutomapStop.stopUnload s))')]:
            with self.subTest(change=new):
                self.assertIn(old,source);r=self.lean(source.replace(old,new));self.assertNotEqual(r.returncode,0)
    def test_decoder_flags_halfword_and_unsigned_branches(self):
        r=self.lean((ROOT/'tests/reference/x86-automap.lean').read_text())
        self.assertEqual(r.returncode,0,r.stdout+r.stderr);self.assertEqual(r.stdout.split(),['true'])
    def test_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        self.assertEqual(proof.drop.table_data(binary,profile,self.spec),self.tables)
        for change in ['object','target','missing','file_offset']:
            spec=copy.deepcopy(self.spec);unit=spec['units']['stop'];rel=unit['relocations']
            if change=='object':rel[0]['object']=1
            elif change=='target':rel[0]['target']='0x12c9c'
            elif change=='missing':rel.clear()
            else:unit['file_offset']='0x0'
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec)
if __name__=='__main__':unittest.main()

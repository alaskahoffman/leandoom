"""Pinned WAD topology, symbolic address lifting and retained physical premises."""
import copy,struct,subprocess,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_topology as proof

class NoiseTopologyTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def small(self):
        # Ordinary edge, missing back side, and a self-edge included only once.
        return dict(rows=[[0,1,2],[0]],sides=[0,1,0],
            lines=[[0,4,0,1,0,1],[1,0,2,65535,0,0],[2,68,2,0,0,0]],limit=3)
    def test_kernel_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.small()));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('completion_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_actual_pinned_e1m1_profile(self):
        data,profile=proof.pinned_data()
        self.assertEqual((len(data['rows']),len(data['lines']),len(data['sides']),data['limit']),(85,475,648,32))
        self.assertEqual(sum(map(len,data['rows'])),642)
        self.assertEqual(profile['wad_sha256'],'1d7d43be501e67d927e415e0b8f3e29c3bf33075e859721816f652a526cac771')
        with patch.object(Path,'read_bytes',return_value=b'altered WAD'):
            with self.assertRaisesRegex(ValueError,'hash mismatch'):proof.pinned_data()
        generated=proof.certificate(data)
        self.assertIn('eval 5611 .sector',generated);self.assertIn('stack.lo+4780',generated)
    def test_kernel_rejects_bad_topology(self):
        variants=[]
        def variant(change):
            d=copy.deepcopy(self.small());change(d);variants.append(d)
        variant(lambda d:d['rows'][0].append(99))
        variant(lambda d:d['lines'][0].__setitem__(5,7))
        variant(lambda d:d['lines'][0].__setitem__(2,65535))
        variant(lambda d:d['lines'][1].__setitem__(1,4))
        variant(lambda d:d['rows'][0].reverse())
        variant(lambda d:d['rows'][0].append(2))
        variant(lambda d:d.__setitem__('limit',2))
        variant(lambda d:d['lines'].reverse())
        for i,data in enumerate(variants):
            with self.subTest(variant=i):
                r=self.lean(proof.certificate(data));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_memory_and_entry_contracts_remain_required(self):
        s=proof.certificate(self.small())
        for old,new in [('(allocation : Allocation (topology.table a) stack)','(allocation : True)'),
            ('(storage : Storage (topology.table a) stack base (topology.edges a) regions)','(storage : True)'),
            ('(ledger : Represents generation s.core.memory xs)','(ledger : True)'),
            ('(map : MapRep (topology.table a) s.core.memory)','(map : True)'),
            ('(graph : GraphRep base (topology.edges a) s.core.memory)','(graph : True)'),
            ('(inside : index<2)','(inside : True)'),
            ('(count : s.core.regs 2=0 ∨ s.core.regs 2=1)','(count : True)'),
            ('stack.lo+132','stack.lo+131'),('eval 17 .sector','eval 16 .sector')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def wad(self, *, front=0,back=1,flags=4,side_sector=1):
        sides=b''.join(struct.pack('<hh8s8s8sH',0,0,b'-',b'-',b'-',x) for x in [0,side_sector])
        contents={name:b'' for name in proof.MAP_LABELS}
        contents.update(SECTORS=bytes(52),SIDEDEFS=sides,LINEDEFS=struct.pack('<7H',0,1,flags,0,0,front,back))
        entries=[('E1M1',b'')]+[(n,contents[n]) for n in proof.MAP_LABELS]
        payload=bytearray(b'IWAD'+bytes(8));directory=[]
        for name,data in entries:
            directory.append(struct.pack('<II8s',len(payload),len(data),name.encode()));payload.extend(data)
        struct.pack_into('<II',payload,4,len(entries),len(payload))
        return bytes(payload)+b''.join(directory)
    def test_decoder_and_record_validation(self):
        data=proof.decode_wad(self.wad());self.assertEqual(data['rows'],[[0],[0]])
        self.assertEqual(proof.decode_wad(self.wad(back=65535,flags=0))['rows'],[[0],[]])
        for blob in [b'bad',self.wad()[:-1],self.wad(front=32768),self.wad(back=3),self.wad(back=65535),self.wad(side_sector=2)]:
            with self.assertRaises(ValueError):proof.decode_wad(blob)
        damaged=bytearray(self.wad());struct.pack_into('<I',damaged,8,len(damaged)+1)
        with self.assertRaises(ValueError):proof.decode_wad(bytes(damaged))
if __name__=='__main__':unittest.main()

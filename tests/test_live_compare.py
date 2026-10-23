"""Live lockstep framing, controls, and saved evidence (no SDL requirement)."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import live_compare as live

class LiveCompareTests(unittest.TestCase):
    def test_shared_keyboard_commands_are_demo_encodable(self):
        s=live.Session.__new__(live.Session);s.held=0
        self.assertEqual(s.command(2|16|8192|4096),[25,24,0,3])
        self.assertEqual(s.command(4|8|512),[-50,-40,0,0])
        self.assertEqual([s.command(32)[2] for _ in range(6)],[256]*5+[768])
        self.assertEqual(s.command(64|512)[2],-1280)
        self.assertEqual(s.command(0),[0,0,0,0])
        self.assertEqual(s.held,0)
        for bit,button in [(16384,4),(32768,12),(65536,20)]:self.assertEqual(s.command(bit)[3],button)
        for keys in [32,64,32|512,64|512,2|4|8|16|32|64]:
            for _ in range(12):self.assertEqual(s.command(keys)[2]%256,0)

    def test_packet_reader_keeps_binary_boundaries_and_next_record(self):
        r,w=os.pipe()
        try:
            packet=live.PacketReader(r)
            # Preload fragments rather than filling an OS pipe before reading.
            record={'tick':1,'command':[0,0,0,0]};frame=bytes(range(256))*750
            packet.buffer.extend(json.dumps(record).encode()+b'\n'+frame+json.dumps({'tick':2}).encode()+b'\n'+frame)
            self.assertEqual(packet.packet(),(record,frame))
            self.assertEqual(packet.packet(),({'tick':2},frame))
            os.close(w);w=None
            with self.assertRaisesRegex(RuntimeError,'engine stopped'):packet.packet()
        finally:
            os.close(r)
            if w is not None:os.close(w)

    def test_packet_timeout_is_bounded(self):
        r,w=os.pipe()
        try:
            with self.assertRaises(TimeoutError):live.PacketReader(r).packet(timeout=.01)
        finally:os.close(r);os.close(w)

    def test_saved_replay_and_pixels_are_lossless(self):
        s=live.Session.__new__(live.Session)
        with tempfile.TemporaryDirectory() as d:
            s.directory=Path(d);s.provenance={'oracle':'fixture'}
            s.commands=[[25,-24,-256,1],[0,0,32512,20]]
            a=bytes(live.FRAME_SIZE);b=bytearray(a);b[3*57+2]=1
            meta={'tick':2,'gameplayMatch':True,'firstStateDifference':None}
            s.last=(meta,[({'tick':2},a),({'tick':2},bytes(b))])
            out=Path(s.save());report=json.loads((out/'report.json').read_text())
            self.assertEqual(report['full']['different_pixels'],1)
            self.assertEqual(report['first_difference']['x'],57)
            self.assertEqual(live.dc.decode_demo((out/'input.lmp').read_bytes()),s.commands)
            self.assertEqual((out/'commands.txt').read_text(),'25 -24 -256 1\n0 0 32512 20\n')
            self.assertEqual(live.rc.read_ppm(out/'lean.ppm'),bytes(b))

    def test_failed_worker_cannot_advance_or_create_misleading_evidence(self):
        s=live.Session.__new__(live.Session);s.failed=True
        with self.assertRaisesRegex(ValueError,'Worker failed'):s.step([0,0,0,0])

    def test_http_requires_capability_and_rejects_stale_tick(self):
        import re
        import threading
        import urllib.request
        import urllib.error
        class Fake:
            lock=threading.Lock();generation=1;commands=[];last=None
            def command(self,keys):return [0,0,0,0]
            def step(self,cmd):
                self.commands.append(cmd)
                return {'tick':1},bytes(live.FRAME_SIZE),bytes(live.FRAME_SIZE)
        httpd=live.server(Fake());thread=threading.Thread(target=httpd.serve_forever,daemon=True);thread.start()
        url=f'http://127.0.0.1:{httpd.server_port}'
        try:
            page=urllib.request.urlopen(url).read().decode()
            token=re.search("const token='([^']+)'",page)[1]
            def post(body,cap=token):
                req=urllib.request.Request(url+'/step',json.dumps(body).encode(),{'X-Compare-Token':cap,'Content-Type':'application/json'})
                return urllib.request.urlopen(req)
            for body,cap,code in [({'tick':0,'generation':1},'',403),({'tick':8,'generation':1},token,400)]:
                with self.assertRaises(urllib.error.HTTPError) as e:post(body,cap)
                self.assertEqual(e.exception.code,code)
                e.exception.close()
            import struct
            body=post({'tick':0,'generation':1,'keys':0}).read();size=struct.unpack_from('<I',body)[0]
            self.assertEqual(len(body),4+size+2*live.FRAME_SIZE)
            self.assertEqual(json.loads(body[4:4+size]),{'tick':1})
        finally:httpd.shutdown();httpd.server_close();thread.join()

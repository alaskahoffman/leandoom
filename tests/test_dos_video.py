"""Regression of a real DOS slime-trail seam, comparing complete frame hashes."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from live_compare import PacketReader


class DosVideoTests(unittest.TestCase):
    def test_unpainted_seams_retain_original_vga_page_history(self):
        wad=ROOT/'artifacts/doom-shareware-1.9/doom1.wad'
        if not wad.exists():self.skipTest('shareware WAD not installed')
        spec=json.loads((ROOT/'tests/reference/dos-video-commands.json').read_text())
        sha=lambda b:hashlib.sha256(b).hexdigest()
        self.assertEqual(sha(wad.read_bytes()),spec['wad_sha256'])
        commands=[row[1:] for row in spec['runs'] for _ in range(row[0])]
        encoded=''.join(' '.join(map(str,c))+'\n' for c in commands).encode()
        self.assertEqual(sha(encoded),spec['commands_sha256'])
        self.assertEqual(len(commands),spec['tics'])
        with tempfile.TemporaryDirectory() as directory:
            error=Path(directory)/'stderr'
            with error.open('wb') as log:
                p=subprocess.Popen([str(ROOT/'.lake/build/bin/live-render-probe'),str(wad),'--dos-presentation'],
                    stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=log)
                reader=PacketReader(p.stdout.fileno())
                try:
                    for tic,command in enumerate(commands,1):
                        p.stdin.write((' '.join(map(str,command))+'\n').encode());p.stdin.flush()
                        _,frame=reader.packet(timeout=60)
                        if str(tic) in spec['frames']:
                            self.assertEqual(sha(frame),spec['frames'][str(tic)],f'frame {tic}')
                    p.stdin.close()
                    self.assertEqual(p.wait(timeout=10),0)
                finally:
                    if p.poll() is None:p.terminate();p.wait(timeout=10)
                    if not p.stdin.closed:p.stdin.close()
                    p.stdout.close()
            self.assertEqual(error.read_text(),'')


if __name__=='__main__':unittest.main()

"""Compare all reachable renderer tangent reads with original DOS image bytes."""
import re
import struct
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import original_demo_compare as oc


class OriginalRenderTableTests(unittest.TestCase):
    def test_entire_tangent_address_range_including_adjacent_sine_bytes(self):
        if not (ROOT/'artifacts/doom-shareware-1.9/doom19s.zip').exists():self.skipTest('shareware archive not installed')
        image=oc.original_image();le=int(oc.PROFILE['le_offset'],16)
        u32=lambda p:struct.unpack_from('<I',image,p)[0]
        objects=le+u32(le+0x40);data=struct.unpack_from('<6I',image,objects+48)
        self.assertEqual(data[:5],(0x85e10,0x70000,0x2043,71,38))
        page_map=le+u32(le+0x48);file_start=int(oc.PROFILE['data_pages_offset'],16)
        start,end=0x1a84,0x9a84
        raw=bytearray()
        for offset in range(start,end):
            page=data[3]-1+offset//4096
            entry=image[page_map+4*page:page_map+4*page+4]
            self.assertEqual(entry[3],0)
            physical=int.from_bytes(entry[:3],'big')
            raw.append(image[file_start+(physical-1)*4096+offset%4096])
        # Relocation must not modify any of these static table bytes at load.
        for offset,_,_ in oc.fixups(image,range(70+start//4096,70+(end-1)//4096+1)):
            self.assertFalse(max(offset-70*4096,start)<min(offset-70*4096+4,end))
        expected=list(struct.unpack('<8192i',raw))
        source=(ROOT/'Doom/Tables.lean').read_text()
        def vector(name):
            chunks=re.findall(r'private def '+name+r'(\d+)\s.*?#\[(.*?)\]',source,re.S)
            return [int(v) for _,body in sorted(chunks,key=lambda c:int(c[0])) for v in body.replace('\n','').replace(' ','').strip(',').split(',')]
        self.assertEqual(expected,vector('fineTangent')+vector('fineSine')[:4096])
        with tempfile.TemporaryDirectory() as directory:
            commands=Path(directory)/'commands.txt'
            commands.write_text(''.join(f'render-tangent {i}\n' for i in range(8192)))
            result=subprocess.run([str(ROOT/'.lake/build/bin/fidelity-probe'),str(commands)],
                                  text=True,capture_output=True,check=True)
        self.assertEqual(list(map(int,result.stdout.splitlines())),expected)
        self.assertNotIn('PANIC',result.stderr)

if __name__=='__main__':unittest.main()

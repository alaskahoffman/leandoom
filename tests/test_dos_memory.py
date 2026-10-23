"""Guest-memory and renderer integration, independent of an installed emulator."""
from pathlib import Path
import hashlib
import json
import struct
import subprocess
import tempfile
import unittest

from test_assets import patch

ROOT=Path(__file__).resolve().parents[1]
EXE=ROOT/'.lake/build/bin/dos-memory-probe'
HEAP=0x400000
OWNERS=0x300000


class DosMemoryTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.path=Path(self.temp.name)
        self.initial=self.file('initial',bytes(16384))
        self.owners=self.file('owners',bytes(256))

    def tearDown(self):self.temp.cleanup()

    def file(self,name,data):
        p=self.path/name;p.write_bytes(data);return p

    def run_commands(self,commands):
        p=self.path/'commands'
        p.write_text('\n'.join(commands)+'\n')
        result=subprocess.run([str(EXE),str(p)],capture_output=True,text=True,check=True)
        self.assertEqual(result.stderr,'')
        return result.stdout.splitlines()

    def setup_commands(self):
        return [f'map {HEAP} {self.initial}',f'map {OWNERS} {self.owners}',f'zone {HEAP} 16384']

    def test_neighbor_header_is_generated_by_allocator_not_a_fixed_color(self):
        for payload,expected in [(8192,24),(8200,32),(8400,232)]:
            result=self.run_commands(self.setup_commands()+[
                f'alloc 512 101 {OWNERS}',f'alloc {payload} 101 {OWNERS+4}',
                f'sample {HEAP+56} 496 16'])
            self.assertEqual(result[-1],f'ok {expected}')
        # The same sample depends on the neighboring allocation's size.

    def test_unmapped_bytes_are_errors_and_word_access_wraps_like_x86(self):
        high=self.file('high',b'\x11\x22');low=self.file('low',b'\x33\x44')
        result=self.run_commands([f'map 4294967294 {high}',f'map 0 {low}',
            'read 4294967294','sample 4294967294 2 0','sample 8 0 0'])
        self.assertEqual(result[2:],['ok 1144201745','ok 51','error unmapped guest sample'])

    def test_lump_cache_owns_blocks_and_reload_preserves_stale_memory(self):
        first=self.file('lump1',bytes([191])*128)
        different=self.file('lump2',bytes([23])*128)
        # The original owner array is outside the zone, so it consumes no zone
        # block. First payload follows just the zone header and block header.
        ptr=HEAP+56
        dump=self.path/'dump'
        result=self.run_commands(self.setup_commands()+[
            f'cache {OWNERS} 4',f'lump 0 101 {first}',f'lump 0 50 {different}',
            f'read {OWNERS}',f'sample {ptr} 0 2',
            'tags 50 50',f'read {OWNERS}',f'sample {ptr} 0 2',
            f'lump 0 101 {different}',f'sample {ptr} 0 2',f'dump {dump}'])
        self.assertEqual(result[3:13],[f'ok {OWNERS}',f'ok {ptr}',f'ok {ptr}',f'ok {ptr}',
            'ok 191','ok 0','ok 0','ok 191',f'ok {ptr}','ok 23'])
        self.assertEqual(struct.unpack_from('<I',dump.read_bytes(),ptr-HEAP-16)[0],101)

    def test_invalid_owner_and_duplicate_free_fail_explicitly(self):
        result=self.run_commands(self.setup_commands()+[
            'alloc 16 101 0','alloc 16 1 0',f'tag {HEAP+56} 101',
            f'free {HEAP+56}',f'free {HEAP+56}'])
        self.assertTrue(result[3].startswith('error '))
        self.assertTrue(result[5].startswith('error '))
        self.assertEqual(result[6],'ok 0')
        self.assertTrue(result[7].startswith('error '))

    def test_unknown_ram_stays_unknown_until_written(self):
        result=self.run_commands([f'unknown {HEAP} 256',f'zone {HEAP} 256',
            'alloc 32 1 0',f'sample {HEAP+56} 0 0',
            f'write {HEAP+56} 201',f'sample {HEAP+56} 0 0',
            f'free {HEAP+56}',f'sample {HEAP+56} 0 0'])
        self.assertEqual(result[3],'error unmapped guest sample')
        self.assertEqual(result[5:],["ok 201","ok 0","ok 201"])

    def test_unmodeled_writes_cannot_expose_old_known_payload(self):
        result=self.run_commands(self.setup_commands()+[
            'alloc 32 1 0',f'write {HEAP+56} 201',
            f'forget {HEAP+56} 4',f'sample {HEAP+56} 0 0',
            f'sample {HEAP+56} 4 0',f'write {HEAP+56} 88',f'sample {HEAP+56} 0 0'])
        self.assertEqual(result[-4:],['error unmapped guest sample','ok 0','ok 0','ok 88'])

    def test_real_sprite_drawer_reads_guest_bytes_beyond_patch(self):
        # Exact problematic arithmetic: fraction -4 -> row 127. Build a small
        # 11-high patch; the known guest byte lies past its complete lump.
        raw=patch([[12] for _ in range(11)])
        p=self.file('sprite',raw)
        source=struct.unpack_from('<I',raw,8)[0]+3
        backing=bytearray([99]*256)
        backing[:len(raw)]=raw
        backing[source+127]=201
        guest=self.file('guest',backing)
        dest=self.path/'frame'
        self.run_commands([f'map {HEAP} {guest}',
            f'drawpatch {HEAP} {p} 0 125484 {(-4-55*34227)&0xffffffff} 34227 {dest}'])
        pixels=dest.read_bytes()
        self.assertEqual(pixels[139*320],201)
        self.assertEqual(pixels[140*320],12)
        self.assertEqual(pixels[138*320],77)
        self.assertTrue(all(pixels[y*320+x]==77 for y in range(200) for x in range(1,320)))
        # Changing only the adjacent guest byte changes the actual renderer.
        backing[source+127]=88
        guest.write_bytes(backing)
        self.run_commands([f'map {HEAP} {guest}',
            f'drawpatch {HEAP} {p} 0 125484 {(-4-55*34227)&0xffffffff} 34227 {dest}'])
        self.assertEqual(dest.read_bytes()[139*320],88)

    def test_recorded_overreads_follow_from_allocations_and_wad_neighbors(self):
        # Addresses/adjacency are fixture assumptions, not a live heap model.
        # Generate headers with the allocator and payloads from WAD resources;
        # never inject the observed stray colors into the modeled memory.
        path=ROOT/'artifacts/doom-shareware-1.9/doom1.wad'
        if not path.exists():self.skipTest('shareware WAD not installed')
        wad=path.read_bytes()
        spec=json.loads((ROOT/'tests/reference/dos-texture-overreads.json').read_text())
        self.assertEqual(hashlib.sha256(wad).hexdigest(),spec['wad_sha256'])
        _,n,d=struct.unpack_from('<4sII',wad)
        lumps={}
        for i in range(n):
            p,size,name=struct.unpack_from('<II8s',wad,d+16*i)
            lumps[name.rstrip(b'\0').decode()]=wad[p:p+size]
        count=0
        for case in spec['cases']:
            ptr=case['source_address'];base=ptr-56
            commands=[f'map {base} {self.initial}',f'map {OWNERS} {self.owners}',
                f'zone {base} 16384',f'alloc {case["source_bytes"]} 101 {OWNERS}']
            if case['source'] in lumps:
                self.assertEqual(len(lumps[case['source']]),case['source_bytes'])
                source=self.file('source-lump',lumps[case['source']])
                commands.append(f'load {ptr} {source}')
            commands.append(f'alloc {case["neighbor_payload_bytes"]} 101 {OWNERS+4}')
            if case['neighbor'] is not None:
                neighbor=self.file('next-lump',lumps[case['neighbor']])
                commands.append(f'load {ptr+case["source_bytes"]+24} {neighbor}')
            for p in case['samples']:
                commands.append(f'sample {ptr} {p["source_offset"]} {p["row"]}')
            results=self.run_commands(commands)[-len(case['samples']):]
            self.assertEqual(results,[f'ok {p["byte"]}' for p in case['samples']],case['tic'])
            count+=len(results)
        self.assertEqual(count,37)


if __name__=='__main__':unittest.main()

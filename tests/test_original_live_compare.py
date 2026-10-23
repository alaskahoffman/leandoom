"""Original-executable live adapter: writes only input, reads actual planar pixels."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import original_live_compare as original
import live_compare as live


def fixture_source():
    setup=[]
    for item in original.SPEC['evidence'].values():
        p=int(item['offset'],16)
        setup.extend(f'ram[code+{p+i}]={v};' for i,v in enumerate(bytes.fromhex(item['hex'])))
    for p,t in {**original.oc.SPEC['data_operands'],**original.SPEC['data_operands']}.items():
        setup.append(f'put(code+{p},data+{t});')
    header=(ROOT/'tests/reference/dosbox_live_frame.h').read_text().replace('#include "vga.h"','')
    return r'''
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
using PhysPt=uint32_t;
static unsigned char ram[32*1024*1024], pixels[262144];
static struct {bool pmode=true;struct {bool big=true;} code;} cpu;
static struct {bool enabled=false;} paging;
static struct {struct {unsigned char *linear=pixels;unsigned memmask=262143;} mem;} vga;
static unsigned reg_eax=0, writes=0;
enum {ds};
static unsigned SegBase(int) {return 0;}
static uint8_t mem_readb(PhysPt p) {if(p>=sizeof(ram))std::exit(3);return ram[p];}
static uint32_t mem_readd(PhysPt p) {return mem_readb(p)|(mem_readb(p+1)<<8)|(mem_readb(p+2)<<16)|(uint32_t(mem_readb(p+3))<<24);}
static void mem_writeb(PhysPt p,uint8_t v) {if(p<0x300000 || p>=0x300004)std::exit(4);ram[p]=v;++writes;}
static void put(PhysPt p,uint32_t v) {for(unsigned i=0;i<4;++i)ram[p+i]=v>>(8*i);}
''' + header + r'''
int main(int argc,char **argv) {
 const unsigned code=0x100000,data=0x200000;
''' + '\n'.join(setup) + r'''
 const char *mode=argc>1?argv[1]:"good";
 if(!std::strcmp(mode,"relocation"))put(code+0x19fcb,data+0x29150);
 put(data+0x2b378,0x300000);
 LDLiveObserve(code+0x20607);
 if(writes!=4 || ram[0x300000]!=25 || ram[0x300001]!=232 || ram[0x300002]!=255 || ram[0x300003]!=1)return 5;
 if(!std::strcmp(mode,"duplicate"))LDLiveObserve(code+0x20607);
 FILE *trace=std::tmpfile();
 std::fputs("{\"tick\":0}\n",trace);std::fflush(trace);LDLiveState(trace,0);
 std::fputs("{\"tick\":1}\n",trace);std::fflush(trace);LDLiveState(trace,1);
 reg_eax=0x310000;
 for(unsigned i=0;i<768;++i)ram[reg_eax+i]=uint8_t(i);
 if(!std::strcmp(mode,"gamma"))put(data+0x74fc0,1);
 if(std::strcmp(mode,"palette"))LDLiveObserve(code+0x19ca0);
 put(data+0x2914c,!std::strcmp(mode,"page")?0xa1000:0xa8000);
 for(unsigned i=0;i<64000;++i)pixels[0x20000+i]=uint8_t(i/320+i%320);
 if(!std::strcmp(mode,"paging"))paging.enabled=true;
 LDLiveObserve(code+0x1d4a2);
 if(writes!=4)return 6;
 return 0;
}
'''


class DOSLiveAdapterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp=tempfile.TemporaryDirectory();p=Path(cls.tmp.name)
        (p/'fixture.cpp').write_text(fixture_source());cls.binary=p/'fixture'
        subprocess.run(['c++','-std=c++14','-O2',str(p/'fixture.cpp'),'-o',str(cls.binary)],check=True,capture_output=True)
    @classmethod
    def tearDownClass(cls):cls.tmp.cleanup()
    def run_fixture(self,mode='good',command='25 -24 -256 1\n'):
        with tempfile.TemporaryFile() as reply:
            proc=subprocess.run([str(self.binary),mode],input=command.encode(),capture_output=True,
                   env={**os.environ,'LEANDOOM_REPLY_FD':str(reply.fileno())},pass_fds=(reply.fileno(),))
            reply.seek(0);return proc,reply.read()
    def test_only_four_input_bytes_written_and_vga_planes_preserved(self):
        proc,data=self.run_fixture();self.assertEqual(proc.returncode,0,proc.stderr)
        line,rgb=data.split(b'\n',1);self.assertEqual(json.loads(line),{'tick':1})
        expected=bytes((3*((i//320+i%320)%256)+c)%256 for i in range(64000) for c in range(3))
        self.assertEqual(rgb,expected)
    def test_invalid_binding_mapping_palette_and_sequence_fail_closed(self):
        for mode in ['relocation','duplicate','gamma','palette','page','paging']:
            with self.subTest(mode=mode):
                proc,data=self.run_fixture(mode);self.assertEqual(proc.returncode,2,proc.stderr);self.assertEqual(data,b'')
    def test_special_commands_and_non_demo_turns_rejected(self):
        for command in ['25 -24 -255 1\n','25 -24 -256 128\n','-128 0 0 0\n','25 999 0 0\n']:
            with self.subTest(command=command):
                proc,data=self.run_fixture(command=command);self.assertEqual(proc.returncode,2);self.assertEqual(data,b'')
    def test_profile_matches_original_executable_when_present(self):
        if not (ROOT/'artifacts/doom-shareware-1.9/doom19s.zip').exists():self.skipTest('shareware archive not installed')
        original.verify_profile()

if __name__=='__main__':unittest.main()

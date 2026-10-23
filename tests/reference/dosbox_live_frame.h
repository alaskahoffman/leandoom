/* Original DOOM live adapter, hosted outside the DOS executable.
 * Only four pending demo-input bytes are written. CPU registers, instructions,
 * gameplay state, allocator and rendering routines are never replaced.
 * SPDX-License-Identifier: GPL-2.0-or-later */
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <string>
#include "vga.h"

static PhysPt ld_live_code=0, ld_live_data=0, ld_live_ds=0;
static unsigned ld_live_inputs=0, ld_live_frames=0, ld_live_state_tick=0;
static uint32_t ld_live_demo_start=0;
static std::string ld_live_record;
static unsigned char ld_live_palette[768];
static bool ld_live_has_palette=false;
static FILE *ld_live_reply=nullptr;
static void LDLiveFail(const char *s) {
    std::fprintf(stderr,"original DOOM live: %s\n",s); std::exit(2);
}
static void LDLiveState(FILE *trace,unsigned tick) {
    static long cursor=0;
    long end=std::ftell(trace);
    if(end<cursor || end-cursor>2000000) LDLiveFail("invalid state record length");
    if(std::fseek(trace,cursor,SEEK_SET)) LDLiveFail("cannot seek state trace");
    std::string row((size_t)(end-cursor),'\0');
    if(std::fread(&row[0],1,row.size(),trace)!=row.size()) LDLiveFail("cannot read state trace");
    if(std::fseek(trace,end,SEEK_SET)) LDLiveFail("cannot restore state trace cursor");
    cursor=end;
    if(!tick) return;
    if(tick!=ld_live_inputs || tick!=ld_live_frames+1) LDLiveFail("state/input/frame ordering mismatch");
    ld_live_record=row; ld_live_state_tick=tick;
}
static void LDLiveObserve(PhysPt ip) {
    if(!cpu.pmode || !cpu.code.big) return;
    auto rd=[](PhysPt p){return (uint32_t)mem_readd(p);};
    if(!ld_live_code) {
        // Unique relocation-free G_Ticker inlined demo-reader sequence.
        static const uint8_t sig[]={0x8a,0x22,0x80,0xfc,0x80,0x75,0x07,0xe8,0x27,0x16,0x00,0x00,0xeb,0x38};
        if(mem_readb(ip)!=0x8b || mem_readb(ip+1)!=0x15) return;
        for(unsigned i=0;i<sizeof(sig);++i) if(mem_readb(ip+6+i)!=sig[i]) return;
        ld_live_code=ip-0x20607; ld_live_ds=SegBase(ds);
        uint32_t offset=rd(ip+2)-0x2b378;
        if(rd(ld_live_code+0x24161)-0x12720!=offset ||
           rd(ld_live_code+0x24181)-0x1271c!=offset ||
           rd(ld_live_code+0x19fcb)-0x2914c!=offset ||
           rd(ld_live_code+0x19ccc)-0x74fc0!=offset ||
           rd(ld_live_code+0x19cd9)-0x13588!=offset) LDLiveFail("data relocations disagree");
        ld_live_data=ld_live_ds+offset;
        const char *fd=std::getenv("LEANDOOM_REPLY_FD");
        ld_live_reply=fd?fdopen(std::atoi(fd),"wb"):nullptr;
        if(!ld_live_reply) LDLiveFail("missing reply descriptor");
        std::fprintf(stderr,"DOS live binding: code=%x data=%x ds=%x\n",ld_live_code,ld_live_data,ld_live_ds);
    }
    if(ip!=ld_live_code+0x20607 && ip!=ld_live_code+0x19ca0 && ip!=ld_live_code+0x1d4a2) return;
    if(paging.enabled || SegBase(ds)!=ld_live_ds) LDLiveFail("unsupported memory mapping");
    if(ip==ld_live_code+0x20607) {
        if(ld_live_inputs!=ld_live_frames || ld_live_inputs>=10000) LDLiveFail("input outside frame/capacity boundary");
        int f,s,a,b;
        int n=std::scanf("%d %d %d %d",&f,&s,&a,&b);
        if(n==EOF) std::exit(0);
        if(n!=4 || f< -127 || f>127 || s< -128 || s>127 || a< -32768 || a>32512 || a%256 || b<0 || b>127)
            LDLiveFail("invalid live demo command");
        uint32_t p=rd(ld_live_data+0x2b378);
        if(!ld_live_inputs) ld_live_demo_start=p;
        if(p!=ld_live_demo_start+4*ld_live_inputs || p+ld_live_ds<0x100000 || p+ld_live_ds>32*1024*1024-4)
            LDLiveFail("demo input pointer outside declared buffer");
        // The original code reads, decodes and advances these four bytes itself.
        const uint8_t bytes[]={(uint8_t)f,(uint8_t)s,(uint8_t)(a>>8),(uint8_t)b};
        for(unsigned i=0;i<4;++i) mem_writeb(ld_live_ds+p+i,bytes[i]);
        ++ld_live_inputs;
    } else if(ip==ld_live_code+0x19ca0) {
        PhysPt p=ld_live_ds+reg_eax;
        if(p<0x100000 || p>32*1024*1024-768 || rd(ld_live_data+0x74fc0)!=0)
            LDLiveFail("palette outside RAM or nonzero gamma");
        for(unsigned i=0;i<768;++i) ld_live_palette[i]=mem_readb(p+i);
        ld_live_has_palette=true;
    } else {
        if(ld_live_state_tick!=ld_live_frames+1 || ld_live_inputs!=ld_live_state_tick || !ld_live_has_palette)
            LDLiveFail("missing state or palette at completed render");
        uint32_t page=rd(ld_live_data+0x2914c);
        if(page!=0xa0000 && page!=0xa4000 && page!=0xa8000) LDLiveFail("unexpected Mode X page");
        if(!vga.mem.linear || vga.mem.memmask<262143) LDLiveFail("invalid VGA storage");
        unsigned char rgb[64000*3];
        // DOSBox stores the four VGA planes interleaved; adjacent source pixels
        // select successive planes, then advance one byte in each plane.
        for(unsigned i=0;i<64000;++i) {
            unsigned index=vga.mem.linear[(page-0xa0000)*4+i];
            for(unsigned c=0;c<3;++c) rgb[3*i+c]=ld_live_palette[3*index+c];
        }
        if(std::fwrite(ld_live_record.data(),1,ld_live_record.size(),ld_live_reply)!=ld_live_record.size() ||
           std::fwrite(rgb,1,sizeof(rgb),ld_live_reply)!=sizeof(rgb) || std::fflush(ld_live_reply))
            LDLiveFail("reply write failed");
        ++ld_live_frames;
    }
}

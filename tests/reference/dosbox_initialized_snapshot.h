/* Opt-in host-only capture at the existing authenticated pre-P_Ticker boundary.
 * No guest/device reads for the RAM/VRAM backing dump, no guest writes.
 * Not a serialized emulator save-state; device control/scheduler state omitted.
 */
#include "vga.h"
static void LDInitialSnapshot(PhysPt code, PhysPt data, PhysPt dsbase, unsigned tick) {
    static bool captured=false;
    const char *directory=std::getenv("LEANDOOM_INITIAL_DIR");
    if (!directory || tick || captured) return;
    auto fail=[](const char *s) { std::fprintf(stderr,"initial snapshot: %s\n",s); std::exit(2); };
    if (paging.enabled || MEM_TotalPages()!=8192 || !MemBase) fail("unsupported RAM/paging");
    auto save=[&](const char *name, const void *bytes, size_t size) {
        std::string path=std::string(directory)+"/"+name;
        FILE *out=std::fopen(path.c_str(),"wb");
        if (!out || std::fwrite(bytes,1,size,out)!=size || std::fclose(out)) fail("dump write failed");
    };
    save("ram.bin",MemBase,32u*1024u*1024u);
    if (!vga.mem.linear || !vga.mem.memsize) fail("missing VGA backing");
    save("vram.bin",vga.mem.linear,vga.mem.memsize);
    std::string path=std::string(directory)+"/initial.json";
    FILE *out=std::fopen(path.c_str(),"w");
    if (!out) fail("metadata open failed");
    std::fprintf(out,"{\"pc\":%u,\"tick\":0,\"leveltime\":%u,\"paging\":false,\"code_linear\":%u,\"data_linear\":%u,\"ds_base\":%u,\"ss_base\":%u,\"cs_base\":%u,\"eip\":%u,\"eflags\":%u,\"registers\":[%u,%u,%u,%u,%u,%u,%u,%u],\"vram_bytes\":%u}\n",
        0x2081a,(unsigned)mem_readd(data+0x2cf80),(unsigned)code,(unsigned)data,(unsigned)dsbase,
        (unsigned)SegBase(ss),(unsigned)SegBase(cs),(unsigned)reg_eip,(unsigned)reg_flags,
        (unsigned)reg_eax,(unsigned)reg_ecx,(unsigned)reg_edx,(unsigned)reg_ebx,
        (unsigned)reg_esp,(unsigned)reg_ebp,(unsigned)reg_esi,(unsigned)reg_edi,(unsigned)vga.mem.memsize);
    if (std::fclose(out)) fail("metadata close failed");
    captured=true;
}

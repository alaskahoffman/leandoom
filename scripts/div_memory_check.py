"""Independent native FixedDiv diagnostics, including physical stack writes."""
def cross_check(raw):
    import random
    import unicorn as u
    from unicorn import x86_const as x
    from verify_original_inline_thrust import require
    rng=random.Random(0x1d180);mask=0xffffffff;CODE=0x100000;RETURN=CODE+0x2e312
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000);em.mem_write(CODE+0x1d180,raw)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    pages=set();writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    edges=[0,1,2,16383,16384,65535,65536,0x7fffffff,0x80000000,0x80000001,0xffff0000,0xfffffffe,0xffffffff]
    pairs=[(a,b) for a in edges for b in edges]+[(rng.getrandbits(32),rng.getrandbits(32)) for _ in range(256)]
    counts=dict(saturated=0,divided=0,divide_by_zero=0,quotient_overflow=0)
    for case,(a,b,sp) in enumerate((a,b,sp) for a,b in pairs for sp in [0x710100,0x710101,0,2]):
        # Start a fresh CPU after each case: Unicorn retains exception state
        # after #DE, which can otherwise contaminate a later faulting case.
        em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000);em.mem_write(CODE+0x1d180,raw)
        em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
        em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
        pages.clear();memory={}
        for offset in range(-12,4):
            p=((sp+offset)&mask)&~4095
            if p not in memory:memory[p]=bytearray(rng.randbytes(4096))
        def put(addr,v):
            for k,byte in enumerate((v&mask).to_bytes(4,'little')):
                z=(addr+k)&mask;memory[z&~4095][z&4095]=byte
        put(sp,RETURN)
        for p,data in memory.items():em.mem_map(p,4096);pages.add(p);em.mem_write(p,bytes(data))
        initial=[rng.getrandbits(32) for _ in regs];initial[0]=a;initial[2]=b;initial[4]=sp
        expected=[((sp-4)&mask,4,initial[3]),((sp-8)&mask,4,initial[1]),((sp-12)&mask,4,initial[6])]
        for addr,_,v in expected:put(addr,v)
        for r,v in zip(regs,initial):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
        aa=signed((-a)&mask) if signed(a)<0 else a;bb=signed((-b)&mask) if signed(b)<0 else b
        fault=None;rr=initial.copy()
        if (aa>>14)>=bb:
            counts['saturated']+=1;rr[0]=0x80000000 if signed(a^b)<0 else 0x7fffffff;rr[2]=mask if signed(b)<0 else 0
        else:
            dividend=signed(a)*65536;divisor=signed(b)
            q=(abs(dividend)//abs(divisor))*(-1 if (dividend<0)!=(divisor<0) else 1) if divisor else 0
            if divisor==0:fault='divide_by_zero'
            elif not -2147483648<=q<=2147483647:fault='quotient_overflow'
            if fault:
                counts[fault]+=1;rr[0]=dividend&mask;rr[2]=(dividend>>32)&mask
                rr[1]=a;rr[3]=b;rr[6]=(aa>>14)&mask;rr[4]=(sp-12)&mask
            else:counts['divided']+=1;rr[0]=q&mask;rr[2]=(dividend-q*divisor)&mask
        if not fault:rr[4]=(sp+4)&mask
        error=None
        try:em.emu_start(CODE+0x1d180,RETURN,count=26)
        except u.UcError as e:error=e
        require((error is not None)==(fault is not None),f'fault/{case}: {error}')
        if error:require(error.errno==u.UC_ERR_EXCEPTION,f'wrong fault/{case}')
        require(writes==expected,f'stack writes/{case}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{case}')
        require(all(bytes(em.mem_read(p,4096))==data for p,data in memory.items()),f'memory/{case}')
        require(em.reg_read(x.UC_X86_REG_EIP)==(CODE+0x1d1bb if fault else RETURN),f'PC/{case}')
        require(len(visits)==(21 if fault else 25),f'instruction count/{case}')
    return dict(cases=4*len(pairs),branches=counts,all_registers=True,ordered_writes=True,stack_memory_frame=True,unaligned_and_wrapping=True,
        scope='Original routine, real stack and return address; native fault checks are diagnostics. Formal return theorem requires arithmetic success.')

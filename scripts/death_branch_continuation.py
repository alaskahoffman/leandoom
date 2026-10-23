"""Resume the checked lethal floor execution without replacing machine state."""
import json
import struct
import subprocess
import tempfile
from pathlib import Path
import verify_original_kill_bookkeeping as book
import verify_original_weapon_drop as drop
ROOT,require=drop.ROOT,drop.require
MASK=0xffffffff

def check(binary,profile,branch_raw,branch_spec):
    spec=json.loads((ROOT/'tests/reference/original-weapon-drop.json').read_text())
    raw=drop.extraction.extract(binary,profile,spec);tables=drop.table_data(binary,profile,spec)
    book_spec=json.loads((ROOT/'tests/reference/original-kill-bookkeeping.json').read_text())
    book_raw=drop.extraction.extract(binary,profile,book_spec)
    continuation=Continuation(raw,tables,spec,branch_raw,branch_spec)
    prefix=book.cross_check(book_raw,book_spec,continuation)
    return {'prefix':prefix,**continuation.check_live()}

class Continuation:
    def __init__(self,raw,tables,spec,branch_raw,branch_spec):
        self.raw={**raw,**branch_raw};self.units={**spec['units'],**branch_spec['units']}
        self.tables=tables;self.table_spec=spec['tables'];self.base=None;self.mapped=False
        self.rows=[];self.branches=set();self.slots=set();self.sites=set()
    def prepare(self,em,code,base,obj,player,sp,i):
        if not self.mapped:
            em.mem_map(code+0x30000,0x10000);self.mapped=True
        if self.base!=base:
            for name,unit in self.units.items():
                data=bytearray(self.raw[name])
                for rel in unit['relocations']:
                    target=(base if rel['object']==3 else code)+int(rel['target'],16)
                    struct.pack_into('<I',data,rel['offset'],target)
                at=code+int(unit['code_offset'],16);em.mem_write(at,bytes(data));em.ctl_remove_cache(at,at+len(data))
            for name,unit in self.table_spec.items():
                data=bytearray(self.tables[name])
                for rel in unit['relocations']:struct.pack_into('<I',data,rel['offset'],code+int(rel['target'],16))
                em.mem_write(base+int(unit['offset'],16),bytes(data))
            self.base=base
        put=lambda a,v:em.mem_write(a&MASK,struct.pack('<I',v&MASK))
        # All setup occurs before the original floor CALL, not at the seam.
        info=0x600000+1100+i%4;spawn=[100,0,0x80000000,1][(i//16)%4]
        extreme=[0,20,0xffffffff][(i//64)%3];normal=10
        height=[0,0x79ffff,0x7a0000,0x7fffffff,0x80000000,0xffffffff][(i//4)%6]
        active=[0,1,0x80000000,0xffffffff][(i//3)%4]
        put(obj+92,info);put(info+8,spawn);put(info+48,normal);put(info+52,extreme)
        put(player+112,i%3);put(player+256,height);put(base+0x12c5c,active)
        self.current=(spawn,normal,extreme,height,active)
    def finish(self,em,code,base,obj,player,sp,i,health,registers,writes):
        import unicorn as uc
        from unicorn import x86_const as x
        signed=lambda v:v if v<2**31 else v-2**32
        spawn,normal,extreme,height,active=self.current
        victim=i%4;console=(i//4)%4;stop=console==victim and active!=0
        target=0x24f90 if stop else 0x30ea0;ret=0x2a3c8 if stop else 0x2a3f1
        rr=[em.reg_read(r) for r in registers];entry_sp=sp-56;w=i%3;down=3+8*w
        state=base+0x15a28+28*down;psp=player+244;ya=player+256
        pages={0,0xfffff000,0x600000,player&~4095,(player+279)&~4095,(base+0x2af44)&~4095,(base+0x2b400)&~4095}
        before={a:bytearray(em.mem_read(a,4096)) for a in pages};write_start=len(writes);visits=[]
        def visit(e,a,_size,_user):
            visits.append(a-code)
            if a==code+target:e.emu_stop()
        hook=em.hook_add(uc.UC_HOOK_CODE,visit)
        try:em.emu_start(code+0x2d2c0,code+0x40000,count=82)
        finally:em.hook_del(hook)
        require(em.reg_read(x.UC_X86_REG_EIP)==code+target,f'continuous death boundary {i}')
        advanced=(height+0x60000)&MASK;clamp=signed(advanced)>=0x800000
        lowered=0x800000 if clamp else advanced
        expected=[(entry_sp-4,4,rr[3]),(entry_sp-8,4,rr[2]),(entry_sp-12,4,code+0x2d2e0),
                  (entry_sp-16,4,rr[1]),(entry_sp-20,4,rr[6]),(psp,4,state),(psp+4,4,1),
                  (entry_sp-24,4,code+0x2d095),(entry_sp-28,4,psp),(ya+2,2,((height>>16)+6)&65535)]
        if clamp:expected.append((ya,4,0x800000))
        expected.append((sp-56,4,code+ret))
        require(writes[write_start:]==expected,f'continuous suffix writes {i}')
        for addr,size,value in expected:
            for offset,byte in enumerate(value.to_bytes(size,'little')):
                at=(addr+offset)&MASK;before[at&~4095][at&4095]=byte
        require(all(em.mem_read(a,4096)==v for a,v in before.items()),f'continuous retained memory {i}')
        rr[0]=base+0x2ae78+280*console;rr[2]=player
        over=health<signed((-spawn)&MASK)
        choice=extreme if over and extreme else normal
        if not stop:
            rr[0]=obj;rr[2]=choice;rr[6]=health&MASK
            if over:rr[7]=extreme
        require([em.reg_read(r) for r in registers]==rr,f'continuous registers {i}')
        require(all(visits.count(pc)==1 for pc in [0x2d490,0x2d095,0x2d2e0,0x2a38c]),f'missing callback or return {i}')
        self.rows.append((w,height,down,lowered,health,signed(spawn),normal,extreme,choice,stop))
        self.branches.add('automap' if stop else ('extreme' if over and extreme else 'normal'))
        self.slots.add(victim);self.sites.add(i%3)
    def check_live(self):
        signed=lambda v:v if v<2**31 else v-2**32
        with tempfile.TemporaryDirectory() as directory:
            inp=Path(directory)/'input';out=Path(directory)/'output'
            inp.write_text(''.join(f'reset {w} 50 8 1 0 0\nheight {signed(y)}\ndie\n' for w,y,*_ in self.rows))
            subprocess.run([str(ROOT/'.lake/build/bin/weapon-probe'),str(inp),str(out)],check=True)
            answers=out.read_text().splitlines();require(len(answers)==3*len(self.rows),'weapon rows')
            for row,line in zip(self.rows,answers[2::3]):
                values=list(map(int,line.split('|')[0].split()))
                require(values[4]==row[2] and values[5]==1 and values[7]&MASK==row[3],'compiled Weapon.drop mismatch')
            inp.write_text(''.join(f'{hp} {spawn} {normal} {extreme}\n' for _,_,_,_,hp,spawn,normal,extreme,_,_ in self.rows))
            subprocess.run([str(ROOT/'.lake/build/bin/death-probe'),'choice',str(inp),str(out)],check=True)
            choices=list(map(int,out.read_text().splitlines()));require(len(choices)==len(self.rows),'choice rows')
            for row,choice in zip(self.rows,choices):require(row[8]==choice,'compiled deathState mismatch')
        require(self.branches=={'automap','normal','extreme'},'missing terminal branch')
        require(self.slots==set(range(4)) and self.sites==set(range(3)),'missing slot/call coverage')
        return {'continuous_lethal_cases':len(self.rows),'terminal_branches':sorted(self.branches),
                'machine_state_not_reset_at_seam':True,'compiled_weapon_and_death_helpers':True,
                'all_suffix_registers_ordered_writes_and_retained_memory':True}

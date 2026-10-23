#!/usr/bin/env python3
"""Differentially execute DOS zone routines and Lean on the same synthetic RAM.

The oracle is original x86 from the hash-pinned DOOM.EXE, not a C transcription.
Compare every byte of the zone and owner cells after each successful operation.
Error exits are terminal in DOS; only error detection is compared in that case.
This is finite differential testing, not a formal x86 equivalence proof.
"""
import argparse
import json
from pathlib import Path
import random
import struct
import subprocess
import tempfile

import original_demo_compare as oc

ROOT = oc.ROOT
SPEC = json.loads((ROOT/'tests/reference/original-zone.json').read_text())
CODE, DATA, HEAP, OWNERS, STACK = 0x100000, 0x200000, 0x400000, 0x300000, 0x900000
STOP = CODE + 0x80000


def verified_code():
    image = oc.original_image()
    oc.require(oc.sha(image) == SPEC['exe_sha256'], 'zone EXE identity mismatch')
    code, _, _, _ = oc.mul.inspect_image(image, oc.PROFILE)
    for name, r in SPEC['routines'].items():
        start = int(r['offset'], 16)
        oc.require(oc.sha(code[start:start+r['length']]) == r['sha256'], f'zone routine changed: {name}')
    # The loader's data relocations must identify this same global, not merely
    # happen to contain an integer matching the expected offset.
    global_offset = int(SPEC['mainzone_offset'], 16)
    fixes = oc.fixups(image, range((len(code)+4095)//4096))
    for operand in [0x3965a, 0x39680, 0x3969c, 0x3975a, 0x39789, 0x397b3]:
        oc.require((operand, 3, global_offset) in fixes, f'mainzone fixup mismatch: {operand:x}')
    result = bytearray(code)
    for offset, obj, target in fixes:
        struct.pack_into('<I', result, offset, {1:CODE, 2:0x800000, 3:DATA}[obj]+target)
    return bytes(result)


class Oracle:
    def __init__(self, code, initial, owners):
        import unicorn as uc
        from unicorn import x86_const as x
        self.uc, self.x = uc, x
        self.em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
        for base, length in [(CODE,0x100000),(DATA,0x100000),(HEAP,(len(initial)+4095)//4096*4096),(OWNERS,4096),(STACK,4096)]:
            self.em.mem_map(base, length)
        self.em.mem_write(CODE, code)
        self.em.mem_write(HEAP, initial)
        self.em.mem_write(OWNERS, owners)
        self.em.mem_write(DATA+int(SPEC['mainzone_offset'],16), struct.pack('<I',HEAP))
        self.length, self.owner_length = len(initial), len(owners)
        self.failure = False
        self.em.hook_add(uc.UC_HOOK_CODE, self.hook)

    def hook(self, em, address, size, _):
        if address == CODE+int(SPEC['error_offset'],16):
            self.failure = True
            em.emu_stop()
            return
        if not any(CODE+int(r['offset'],16) <= address < CODE+int(r['offset'],16)+r['length'] for r in SPEC['routines'].values()):
            raise AssertionError(f'allocator left audited routines: {address:x}')

    def call(self, name, a=0, d=0, b=0):
        x, em = self.x, self.em
        self.failure = False
        for reg, value in [(x.UC_X86_REG_EAX,a),(x.UC_X86_REG_EDX,d),(x.UC_X86_REG_EBX,b),
                           (x.UC_X86_REG_ECX,0xdeadbeef),(x.UC_X86_REG_ESI,0x12345678),
                           (x.UC_X86_REG_EDI,0x76543210),(x.UC_X86_REG_EBP,0x2468ace0),
                           (x.UC_X86_REG_ESP,STACK+4000)]:
            em.reg_write(reg, value)
        em.mem_write(STACK+4000, struct.pack('<I',STOP))
        em.emu_start(CODE+int(SPEC['routines'][name]['offset'],16),STOP,count=100000)
        if self.failure:
            return None
        assert em.reg_read(x.UC_X86_REG_EIP) == STOP, 'instruction budget exhausted'
        return em.reg_read(x.UC_X86_REG_EAX)

    def snapshot(self):
        return bytes(self.em.mem_read(HEAP,self.length)) + bytes(self.em.mem_read(OWNERS,self.owner_length))

    def blocks(self):
        rd = lambda a: struct.unpack('<I',self.em.mem_read(a,4))[0]
        p = rd(HEAP+20)
        out=[]
        while p != HEAP+4:
            assert len(out) < self.length//24
            out.append((p+24,rd(p),rd(p+4),rd(p+8)))
            p=rd(p+16)
        return out


class Case:
    def __init__(self, path, code, length=4096, seed=0):
        self.path=path
        path.mkdir(exist_ok=True)
        rng=random.Random(seed)
        initial=rng.randbytes(length)
        owners=rng.randbytes(256)
        (path/'initial.bin').write_bytes(initial)
        (path/'owners.bin').write_bytes(owners)
        self.oracle=Oracle(code,initial,owners)
        self.commands=[f'map {HEAP} {path}/initial.bin',f'map {OWNERS} {path}/owners.bin']
        self.expected=['ok 0','ok 0']
        self.snapshots=[]
        self.operations=0
        self.oracle.em.mem_write(HEAP,struct.pack('<I',length))
        assert self.oracle.call('clear',HEAP) is not None
        self.commands.append(f'zone {HEAP} {length}')
        self.expected.append('ok 0')
        self.capture()

    def capture(self):
        path=self.path/f'{len(self.snapshots)}.bin'
        self.commands.append(f'dump {path}')
        self.expected.append('ok 0')
        self.snapshots.append((path,self.oracle.snapshot()))

    def call(self, command, *args):
        routine={'alloc':'alloc','free':'free','tag':'change_tag','tags':'free_tags','clear':'clear'}[command]
        original_args=(HEAP,) if command=='clear' else args
        value=self.oracle.call(routine,*original_args)
        self.commands.append(' '.join(map(str,[command,*args])))
        self.operations+=1
        self.expected.append('error' if value is None else f'ok {value if command == "alloc" else 0}')
        if value is not None:
            self.capture()
        return value

    def write(self, address, value):
        self.oracle.em.mem_write(address,struct.pack('<I',value))
        self.commands.append(f'write {address} {value}')
        self.expected.append('ok 0')

    def check(self):
        path=self.path/'commands.txt'
        path.write_text('\n'.join(self.commands)+'\n')
        proc=subprocess.run([str(ROOT/'.lake/build/bin/dos-memory-probe'),str(path)],capture_output=True,text=True,check=True)
        assert not proc.stderr, proc.stderr
        actual=proc.stdout.splitlines()
        assert len(actual)==len(self.expected)
        for i,(got,want) in enumerate(zip(actual,self.expected)):
            assert (got.startswith('error ') if want=='error' else got==want), (self.path.name,i,self.commands[i],got,want)
        for path,want in self.snapshots:
            got=path.read_bytes()
            if got != want:
                i=next(i for i,(a,b) in enumerate(zip(got,want)) if a!=b)
                raise AssertionError((self.path.name,path.name,'RAM differs',hex(HEAP+i),got[i:i+24].hex(),want[i:i+24].hex()))


def verify(out):
    (out/'report.json').unlink(missing_ok=True)
    code=verified_code()
    cases=[]
    def case(name,**kw):
        c=Case(out/name,code,**kw);cases.append(c);return c

    # Request alignment, tiny/zero allocations, and retained payload/header bytes.
    for seed in [0,1,0x5a5a]:
        c=case(f'alignment-{seed}',length=16384,seed=seed)
        for n in range(130):
            p=c.call('alloc',n,1,0)
            if n>=4:c.write(p,0xabcd0000+n)
        c.call('tags',1,99)
        c.call('clear')
    for extra in [0,4,60,64,68,72]:
        c=case(f'fragment-{extra}',length=256)
        p=c.call('alloc',200-extra,1,0)
        c.call('free',p)
    # Backward/forward coalescing, rover repair, and owner clearing.
    for order in [(0,1,2),(2,1,0),(0,2,1),(1,0,2),(1,2,0),(2,0,1)]:
        c=case('merge-'+''.join(map(str,order)))
        pointers=[c.call('alloc',n,50,OWNERS+4*i) for i,n in enumerate([100,200,300])]
        for i in order:c.call('free',pointers[i])
        c.call('alloc',400,1,0)
    # Explicit wraparound/purge: the tail is too small; cached owners must clear.
    c=case('purge',length=1024)
    a=c.call('alloc',180,1,0)
    b=c.call('alloc',240,101,OWNERS)
    c.call('alloc',240,100,OWNERS+4)
    c.call('alloc',160,50,0)
    c.call('alloc',400,50,0)
    c.call('free',a)
    c.call('tags',50,101)
    # The strict pointer threshold differs between free (>256) and tag (>=256).
    c=case('small-owner')
    p=c.call('alloc',20,1,0)
    c.write(p-20,256)
    c.call('tag',p,100)
    c.call('free',p)
    # A zero/negative tag still owns a block: DOS tests user, not tag, for free.
    c=case('signed-tags')
    c.call('alloc',32,0,0)
    c.call('alloc',32,0xffffffff,0)
    c.call('alloc',32,0x80000000,0)
    c.call('tags',0x80000000,0xffffffff)
    c.call('tags',0,0)
    for name,action in [('oom',lambda c:c.call('alloc',8192,1,0)),
                        ('missing-owner',lambda c:c.call('alloc',16,101,0)),
                        ('invalid-id',lambda c:c.call('free',HEAP+56)),
                        ('bad-tag',lambda c:c.call('tag',c.call('alloc',16,1,0),101))]:
        c=case(name);action(c)
    # Random realistic operation sequences with known live allocations.
    for seed in range(8):
        c=case(f'random-{seed}',length=8192,seed=seed)
        rng=random.Random(seed+0xd005)
        for _ in range(180):
            blocks=c.oracle.blocks()
            live=[b for b in blocks if b[2]!=0]
            operation=rng.randrange(5)
            if operation==0 and live:
                c.call('free',rng.choice(live)[0])
            elif operation==1 and live:
                p,_,owner,_=rng.choice(live)
                c.call('tag',p,rng.choice([1,50,51,100,101]) if owner>256 else rng.choice([1,50,51]))
            elif operation==2:
                c.call('tags',50,51)
            else:
                used={b[2] for b in live}
                slots=[OWNERS+4*i for i in range(64) if OWNERS+4*i not in used]
                tag=rng.choice([1,50,51,100,101]) if slots else 1
                owner=rng.choice(slots) if tag>=100 else 0
                p=c.call('alloc',rng.randrange(0,301),tag,owner)
                if p is None:break  # A DOS I_Error terminates this scenario.
        # Compare earlier successful states even when the sequence ends in OOM.
    for c in cases:c.check()
    import unicorn
    report={'oracle':'hash-pinned original DOS x86 under Unicorn','exe_sha256':SPEC['exe_sha256'],
            'unicorn_version':unicorn.__version__,
            'lean_executable_sha256':oc.sha((ROOT/'.lake/build/bin/dos-memory-probe').read_bytes()),
            'lean_source_sha256':oc.sha((ROOT/'Doom/DosMemory.lean').read_bytes()),
            'driver_sha256':oc.sha(Path(__file__).read_bytes()),
            'profile_sha256':oc.sha((ROOT/'tests/reference/original-zone.json').read_bytes()),
            'scenarios':len(cases),'operations':sum(c.operations for c in cases),
            'full_memory_snapshots':sum(len(c.snapshots) for c in cases),
            'status':'match','scope':SPEC['scope']}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    if args.out:
        args.out.mkdir(parents=True,exist_ok=True)
        verify(args.out.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='leandoom-zone-') as path:verify(Path(path))


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Certify the original grid-advance block and join it to the first-cell firing prefix."""
import argparse
import json
import re
import subprocess
import verify_e1m1_firing_cell_return as previous
import verify_original_inline_thrust as extraction
ROOT, require = previous.ROOT, previous.require
GROUPS = {'OriginalPathAdvance': ['decoded', 'xcheck_execution', 'ycheck_execution', 'xadvanced_execution', 'yadvanced_execution', 'counted_execution', 'gate_execution', 'selected_execution', 'execution'], 'E1M1PathAdvance': ['slot_frame', 'slot20', 'slot24', 'slot28', 'slot32', 'slot36', 'slot40', 'selected_observe', 'result_observe', 'production_axis', 'counter_limit', 'execution'], 'E1M1ThingListFrame': ['run_frame', 'traversal_frame'], 'E1M1FiringAdvance': ['contains_prior', 'contains_advance', 'execution']}


def extracted():
    spec, profile, raw = previous.extracted()
    part = json.loads((ROOT/'tests/reference/original-path-advance.json').read_text())
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip', share, profile)
    require(not (set(part['units']) & set(spec['units'])), 'duplicate grid-advance range')
    raw.update(extraction.extract(binary, profile, part))
    return dict(units={**spec['units'], **part['units']}), profile, raw


def pinned_data():
    return previous.pinned_data()


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringAdvance\n'+previous.certificate(data, raw)
    literal = '['+','.join(hex(b) for b in raw['gridAdvance'])+']'
    source += f'''\nnamespace Doom.Verification.ExtractedPathAdvance
open Doom.Proofs X86 X86Memory X86Control
 def bytes : List UInt8 := {literal}
 theorem bytes_checked : bytes=OriginalPathAdvance.code := by decide
 theorem execution_checked (s : X86Memory.State) (f : Option Flags) :
     ∃ n≤19, X86Routine.Prefix (OriginalPathAdvance.bytesProgram bytes) [] n
       ⟨s,f,0x2cab5⟩ (OriginalPathAdvance.result s) := by
   rw [bytes_checked]; exact OriginalPathAdvance.execution s f
 #print axioms bytes_checked
 #print axioms execution_checked
end Doom.Verification.ExtractedPathAdvance
'''
    for module, names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+n for n in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Verification.ExtractedPathAdvance.bytes_checked'"
    require(marker in output, 'missing firing-advance certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedPathAdvance.bytes_checked','Doom.Verification.ExtractedPathAdvance.execution_checked']+['Doom.Proofs.'+module+'.'+n for module,names in GROUPS.items() for n in names]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def cross_check(raw, spec, count=1024):
    """Diagnostic execution of pinned bytes in Unicorn; no callbacks/stubs."""
    import random
    import struct
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    require(count >= 64, 'too few branch cases')
    code = raw['gridAdvance']
    unit = spec['units']['gridAdvance']
    start = int(unit['code_offset'], 16)
    listing = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(code, start))
    require(b''.join(bytes(i.bytes) for i in listing) == code, 'decoder mismatch')
    require(len(listing) == 26, 'unexpected instruction count')
    CODE, HEAP, MASK = 0x100000, 0x600000, 0xffffffff
    em = u.Uc(u.UC_ARCH_X86, u.UC_MODE_32)
    em.mem_map(CODE, 0x50000)
    em.mem_write(CODE+start, code)
    pages_at = [0, HEAP, 0xfffff000]
    for a in pages_at:
        em.mem_map(a, 4096)
    regs = [x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes, visits = [], []
    em.hook_add(u.UC_HOOK_MEM_WRITE, lambda _, access, a, size, v, data: writes.append((a&MASK,size,v&MASK)))
    def instruction(emu, a, size, data):
        if a-CODE in [0x2ca7f, 0x2cafd]:
            emu.emu_stop()
        else:
            visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE, instruction)
    signed = lambda v: v if v < 2**31 else v-2**32
    rng = random.Random(0x2cab5)
    groups = dict(endpoint=0, x=0, y=0, stall=0, both_match=0, budget_exit=0,
                  continue_loop=0, negative_intercept=0, wrapping_stack=0, counter_extreme=0)
    for i in range(count):
        pages = {a: bytearray(rng.randbytes(4096)) for a in pages_at}
        def put(a, v):
            for k,b in enumerate(struct.pack('<I',v&MASK)):
                q=(a+k)&MASK; pages[q&~4095][q&4095]=b
        rr = [rng.getrandbits(32) for _ in regs]
        sp = [HEAP+512, HEAP+515, 0xffffffe1, 0xfffffff1][(i//4)%4]
        rr[4] = sp
        # Signed intercept integer parts; no artificial positive-only geometry.
        rr[5] = rng.getrandbits(32)
        yi = rng.getrandbits(32)
        mode = ['endpoint','x','y','stall'][i%4]
        rr[6], rr[1] = rng.getrandbits(32), rng.getrandbits(32)
        if mode == 'x':
            rr[1] = (signed(yi)>>16)&MASK
            if i%8 == 1:
                rr[6] = (signed(rr[5])>>16)&MASK
                groups['both_match'] += 1
        elif mode == 'y':
            rr[6] = (signed(rr[5])>>16)&MASK
        endx, endy = rng.getrandbits(32), rng.getrandbits(32)
        if mode == 'endpoint':
            endx, endy = rr[6], rr[1]
        elif i%3 == 0:
            endx = rr[6]  # exercise the second endpoint comparison without exiting
        dx, dy, xs, ys = [rng.getrandbits(32) for _ in range(4)]
        rr[7] = [0, 1, 62, 63, 0x7fffffff, 0xffffffff, 0x80000000][(i//4)%7]
        vals = {20:endx,24:endy,28:dy,32:dx,36:xs,40:ys,44:yi}
        for off,v in vals.items(): put(sp+off,v)
        for a,page in pages.items(): em.mem_write(a,bytes(page))
        for reg,v in zip(regs,rr): em.reg_write(reg,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2)
        expected = rr.copy(); expected_writes = []
        n = 4 if rr[6] == endx else 2
        if rr[6] == endx and rr[1] == endy:
            stop = 0x2cafd
            groups['endpoint'] += 1
            lhs,rhs = rr[1],endy
        else:
            n += 4
            expected[0] = (signed(yi)>>16)&MASK
            if expected[0] == rr[1]:
                groups['x'] += 1; n += 7
                expected[0],expected[3] = ys,dx
                expected[2] = (yi+ys)&MASK
                expected[6] = (rr[6]+dx)&MASK
                expected_writes.append(((sp+44)&MASK,4,expected[2])); put(sp+44,expected[2])
            else:
                n += 4; expected[0] = (signed(rr[5])>>16)&MASK
                if expected[0] == rr[6]:
                    groups['y'] += 1; n += 4
                    expected[0],expected[3] = dy,xs
                    expected[5],expected[1] = (rr[5]+xs)&MASK,(rr[1]+dy)&MASK
                else:
                    groups['stall'] += 1
            n += 3; expected[7] = (rr[7]+1)&MASK
            stop = 0x2ca7f if signed(expected[7]) < 64 else 0x2cafd
            groups['continue_loop' if stop == 0x2ca7f else 'budget_exit'] += 1
            lhs,rhs = expected[7],64
        groups['negative_intercept'] += signed(yi)<0 or signed(rr[5])<0
        groups['wrapping_stack'] += sp>=0xffffffe1
        groups['counter_extreme'] += rr[7]>=0x7fffffff
        writes.clear(); visits.clear()
        em.emu_start(CODE+start,CODE+stop,count=20)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+stop,f'case {i}: stop')
        require(len(visits)==n,f'case {i}: instruction count')
        require([em.reg_read(r) for r in regs]==expected,f'case {i}: registers')
        require(writes==expected_writes,f'case {i}: ordered writes')
        for a,page in pages.items(): require(em.mem_read(a,4096)==page,f'case {i}: memory')
        difference=(lhs-rhs)&MASK
        bits=(int(difference==0)<<6)|(int(difference>=2**31)<<7)|int(lhs<rhs)|(
            int(((lhs^rhs)&(lhs^difference)&0x80000000)!=0)<<11)
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==bits,f'case {i}: comparison flags')
    require(all(groups.values()), 'missing branch coverage')
    return dict(total_cases=count,groups=groups,
                checks='All eight registers, mapped data memory, ordered writes, PC, exact instruction count and final ZF/SF/OF/CF.',
                scope='Pinned grid-advance bytes only; includes wrapping/unaligned stack and arbitrary counter diagnostics. This is testing, not a proof of the emulator or reachable game states.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cross-check",action="store_true")
    args=parser.parse_args()
    data, map_profile = pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-firing-advance'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1FiringAdvance'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Adds an authenticated 72-byte DOS grid-advance range (29 ranges total). '
                        'All endpoint/X-priority/Y/stall/counter branches execute in at most 19 modeled '
                        'instructions and agree with a numeric cell-step model. Axis operations match '
                        'an Int32/Fixed expression reproducing the Path.pathTraverse fragment; the '
                        'outer production loop is not yet connected. The signed counter limit agrees '
                        'with the 64-iteration budget for indices 0..63. Protected reads survive the '
                        'complete object list and iterator return. The firing prefix now executes the '
                        'first advancement within 427+281*line_count+230*object_count instructions. '
                        'Its numeric step is relative to the reached observation; remaining intercept, '
                        'stride, endpoint and counter initialization/frame links remain open. No '
                        'post-advance intercept-array preservation claim is added. Initial memory, '
                        'geometry, layout, finite list/scene, arithmetic and capacity contracts remain; '
                        'later cells, clipping/damage, full query/tic and audiovisual parity are open. '
                        'No production runtime code changed.')
    report['cross_check']=cross_check(raw,spec) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: original grid advancement and firing prefix; strict axiom audit.')


if __name__ == '__main__':
    main()

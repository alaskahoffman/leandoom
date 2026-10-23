#!/usr/bin/env python3
"""Verify original DOOM arithmetic/RNG bytes and their Lean equivalence proofs.

Offline. The optional x86 emulator runs only the extracted routines and compares
them with the compiled Lean engine. It is independent evidence, not a proof.
"""
import argparse
import json
from pathlib import Path
import random
import re
import struct
import subprocess
import sys
import tempfile

import verify_original_mul as mul

ROOT = mul.ROOT
require = mul.require


def fixups(binary, pages):
    """Internal absolute dword fixups, in object-page order, for selected pages."""
    le = 0x27acc  # the hash-pinned profile; inspect_image verifies the header
    u32 = lambda off: struct.unpack_from('<I', binary, off)[0]
    fp, fr, end = (le+u32(le+off) for off in (0x68, 0x6c, 0x70))
    result = []
    for page in pages:
        pos, stop = fr+u32(fp+4*page), fr+u32(fp+4*(page+1))
        require(fr <= pos <= stop <= end, 'bad fixup page bounds')
        while pos < stop:
            require(pos+5 <= stop, 'truncated fixup')
            src, flags, offset, obj = struct.unpack_from('<BBhB', binary, pos)
            require(src == 7 and flags in (0, 16), 'unsupported arithmetic/RNG fixup')
            width = 4 if flags == 16 else 2
            require(pos+5+width <= stop, 'truncated fixup target')
            target = int.from_bytes(binary[pos+5:pos+5+width], 'little')
            result.append((page*4096+offset, obj, target))
            pos += 5+width
    return result


def verify_units(binary, profile, spec):
    code, offsets, _, _ = mul.inspect_image(binary, profile)
    code_start = offsets[0]
    code_fixups = fixups(binary, range(69))
    # Validate the table's actual mapping through object 3 and the LE page map.
    le = int(profile['le_offset'], 16)
    objtab = le+struct.unpack_from('<I', binary, le+0x40)[0]
    data = struct.unpack_from('<6I', binary, objtab+48)
    require(spec['data_object'] == 3 and data[:5] == (0x85e10, 0x70000, 0x2043, 71, 38),
            'unexpected data object')
    page_map = le+struct.unpack_from('<I', binary, le+0x48)[0]
    table_offset = int(spec['rng_table_offset'], 16)
    table_page = data[3]-1 + table_offset//4096
    entry = binary[page_map+4*table_page:page_map+4*table_page+4]
    require(entry == bytes([0,0,89,0]), 'unexpected RNG table physical page')
    table_file = int(profile['data_pages_offset'], 16)+(89-1)*4096+table_offset%4096
    require(table_file == int(spec['units']['randomTableBytes']['file_offset'], 16), 'RNG table mapping mismatch')
    require(int(spec['data_page_start'], 16) == code_start+70*4096, 'data page start mismatch')
    data_fixups = fixups(binary, [table_page])
    require(not any(max(table_offset, off-70*4096) < min(table_offset+256, off-70*4096+4)
                    for off, _, _ in data_fixups), 'RNG table is altered by relocation')

    extracted = {}
    for name, unit in spec['units'].items():
        start, size = int(unit['file_offset'], 16), unit['bytes']
        raw = binary[start:start+size]
        require(raw == bytes.fromhex(unit['hex']), f'{name}: original bytes changed')
        if name != 'randomTableBytes':
            offset = start-code_start
            require(offset >= 0 and offset+size <= len(code) and code[offset:offset+size] == raw,
                    f'{name}: outside mapped executable code')
            actual = [(off-offset, obj, target) for off, obj, target in code_fixups
                      if max(offset, off) < min(offset+size, off+4)]
            expected = [(p['offset'], 3, int(p['target'], 16)) for p in unit['data_relocations']]
            require(sorted(actual) == sorted(expected), f'{name}: relocation identity mismatch')
            for rel, obj, target in expected:
                require(int.from_bytes(raw[rel:rel+4], 'little') == target,
                        f'{name}: data offset differs from relocation target')
        extracted[name] = raw
    return extracted


def certificate(extracted, digest):
    text = f'''-- Extracted from DOOM.EXE SHA-256 {digest}; external file/loader checks documented separately.
import Doom.Proofs.OriginalAddSub
import Doom.Proofs.OriginalRandom
set_option maxRecDepth 4096
namespace Doom.Verification.ExtractedArithmetic
open X86 X86ValueRoutine Doom.Proofs
'''
    for name, data in extracted.items():
        text += f'def {name} : List UInt8 := [{", ".join(hex(b) for b in data)}]\n'
        text += f'theorem {name}_checked : {name} = Doom19.{name} := by decide\n'
    text += '''theorem extracted_add (a b : Fixed) :
    (X86.run 1 addBytes (originalMulInputs a b)).map (fun r => r eax) = some (a+b).raw.toBitVec := by
  rw [addBytes_checked]; exact fixed_add_matches_doom19 a b
theorem extracted_sub (a b : Fixed) :
    (X86.run 1 subBytes (originalMulInputs a b)).map (fun r => r eax) = some (a-b).raw.toBitVec := by
  rw [subBytes_checked]; exact fixed_sub_matches_doom19 a b
theorem extracted_div (a b : Fixed) :
    resultWord (X86ValueRoutine.run fixedDivBytes 40 (divisionInputs a b)) =
      some (divisionAnswer (Fixed.divChecked a b)) := by
  rw [fixedDivBytes_checked]; exact fixed_div_matches_doom19 a b
def extractedCode : RandomCall → List UInt8
  | .play => playRandomBytes
  | .misc => miscRandomBytes
  | .clear => clearRandomBytes
theorem extracted_random_trace (calls : List RandomCall) (r : DoomRandom) :
    binaryRandomTrace extractedCode randomTableBytes calls r = some (engineRandomTrace calls r) := by
  have hc : extractedCode = randomCode := by
    funext call; cases call <;> simp [extractedCode, randomCode,
      playRandomBytes_checked, miscRandomBytes_checked, clearRandomBytes_checked]
  rw [hc, randomTableBytes_checked]
  exact random_trace_matches_doom19 calls r
#print axioms extracted_add
#print axioms extracted_sub
#print axioms extracted_div
#print axioms extracted_random_trace
end Doom.Verification.ExtractedArithmetic
'''
    return text


def audit(output):
    remaining = output.strip()
    for name in ['add','sub','div','random_trace']:
        prefix = re.escape(f"'Doom.Verification.ExtractedArithmetic.extracted_{name}'")
        match = re.match(prefix + r'\s+depends on axioms: \[([^\[\]]*)\]', remaining)
        require(match is not None, 'missing audited theorem or unexpected arithmetic audit output')
        require({axiom.strip() for axiom in match[1].split(',')} <=
                {'propext','Classical.choice','Quot.sound'}, 'unexpected arithmetic proof axiom')
        remaining = remaining[match.end():].strip()
    require(not remaining, 'unexpected arithmetic audit output')


def probe(commands):
    with tempfile.TemporaryDirectory(prefix='leandoom-binary-probe-') as folder:
        path = Path(folder)/'input.txt'
        path.write_text('\n'.join(commands)+'\n')
        result = subprocess.run([str(ROOT/'.lake/build/bin/fidelity-probe'),str(path)],
                                text=True,capture_output=True,check=True)
    return result.stdout.splitlines()


def cross_check(extracted, spec):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    CODE, DATA, STACK, STOP = 0x100000, 0x200000, 0x300000, 0x100800
    dis = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32)
    for name, raw in extracted.items():
        if name != 'randomTableBytes':
            ins = list(dis.disasm(raw, 0))
            require(b''.join(bytes(i.bytes) for i in ins) == raw, f'{name}: incomplete independent disassembly')

    def machine(name):
        em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
        em.mem_map(CODE, 4096)
        em.mem_map(DATA, 0x20000)
        em.mem_map(STACK, 4096)
        raw = bytearray(extracted[name])
        for rel in spec['units'][name]['data_relocations']:
            struct.pack_into('<I', raw, rel['offset'], DATA+int(rel['target'], 16))
        em.mem_write(CODE, bytes(raw))
        return em

    rng = random.Random(0xD0019A)
    edges = [-2147483648, -2147483647, -65537, -65536, -65535, -16385, -1, 0,
             1, 2, 16383, 16384, 16385, 65535, 65536, 65537, 2147483647]
    pairs = [(a,b) for a in edges for b in edges]
    pairs += [(rng.randrange(-2**31,2**31),rng.randrange(-2**31,2**31)) for _ in range(10000)]
    # Explicitly exercise both sides of the conservative guard and INT_MIN's IDIV boundaries.
    for a in edges:
        for b in [abs(a)//16384-1,abs(a)//16384,abs(a)//16384+1]:
            pairs.extend([(a,b),(a,-b)])
    commands = [f'{op} {a} {b}' for op in ['add','sub','div'] for a,b in pairs]
    lean = probe(commands)
    require(len(lean) == len(commands), 'Lean probe output count mismatch')
    faults = 0
    for oi, (op,name) in enumerate([('add','addBytes'),('sub','subBytes'),('div','fixedDivBytes')]):
        em = machine(name)
        pristine = em.context_save()
        for i,(a,b) in enumerate(pairs):
            # Restore hidden exception state as well as registers after an IDIV fault.
            em.context_restore(pristine)
            keep = {x.UC_X86_REG_EBX:rng.getrandbits(32), x.UC_X86_REG_ECX:rng.getrandbits(32),
                    x.UC_X86_REG_ESI:rng.getrandbits(32), x.UC_X86_REG_EDI:rng.getrandbits(32),
                    x.UC_X86_REG_EBP:rng.getrandbits(32)}
            for reg,value in keep.items(): em.reg_write(reg,value)
            em.reg_write(x.UC_X86_REG_EAX,a&0xffffffff)
            em.reg_write(x.UC_X86_REG_EDX,b&0xffffffff)
            if op != 'div': em.reg_write(x.UC_X86_REG_EBX,b&0xffffffff)
            em.reg_write(x.UC_X86_REG_ESP,STACK+0x800)
            em.mem_write(STACK+0x800, STOP.to_bytes(4,'little'))
            expected = lean[oi*len(pairs)+i]
            try:
                finish = STOP if op == 'div' else CODE+2
                em.emu_start(CODE,finish,count=100)
                require(em.reg_read(x.UC_X86_REG_EIP) == finish, 'routine did not return')
                value = em.reg_read(x.UC_X86_REG_EAX)
                value = value if value < 2**31 else value-2**32
                require(expected == str(value), f'{op}({a},{b}): x86={value}, Lean={expected}')
                if op == 'div':
                    require(all(em.reg_read(reg)==v for reg,v in keep.items()), 'division register preservation')
                    require(em.reg_read(x.UC_X86_REG_ESP)==STACK+0x804, 'division stack balance')
            except uc.UcError as error:
                require(op == 'div' and error.errno == uc.UC_ERR_EXCEPTION, f'unexpected emulator error: {error}')
                require(em.reg_read(x.UC_X86_REG_EIP) == CODE+59, 'exception outside IDIV')
                reason = 'divide-by-zero' if b == 0 else 'quotient-overflow'
                require(expected == reason, f'IDIV fault differs from Lean: {a}, {b}, {expected}')
                faults += 1

    # Load all three RNG routines into one machine, preserving memory between calls.
    em = machine('playRandomBytes')
    locations = {'play':CODE, 'misc':CODE+0x100, 'clear':CODE+0x200}
    for call,name in [('play','playRandomBytes'),('misc','miscRandomBytes'),('clear','clearRandomBytes')]:
        raw = bytearray(extracted[name])
        for rel in spec['units'][name]['data_relocations']:
            struct.pack_into('<I',raw,rel['offset'],DATA+int(rel['target'],16))
        em.mem_write(locations[call],bytes(raw))
    em.mem_write(DATA+0x1261c,extracted['randomTableBytes'])
    calls = ['clear']+['play']*513+['misc']*513
    calls += [rng.choice(['play','misc','play','misc','clear']) for _ in range(10000)]
    expected = probe(calls)
    require(len(expected) == len(calls), 'Lean RNG output count mismatch')
    for call,answer in zip(calls,expected):
        em.reg_write(x.UC_X86_REG_ESP,STACK+0x800)
        em.mem_write(STACK+0x800,STOP.to_bytes(4,'little'))
        em.emu_start(locations[call],STOP,count=100)
        require(em.reg_read(x.UC_X86_REG_EIP)==STOP, 'RNG did not return')
        play,misc = (int.from_bytes(em.mem_read(DATA+addr,4),'little') for addr in [0x12720,0x1271c])
        # FidelityProbe returns the observed value and both indices for each operation.
        value = em.reg_read(x.UC_X86_REG_EAX)
        actual = f'0 {play} {misc}' if call == 'clear' else f'{value} {play} {misc}'
        require(answer == actual, f'RNG {call}: x86={actual}, Lean={answer}')
    return dict(capstone=capstone.__version__,unicorn=uc.__version__,arithmetic_cases=3*len(pairs),
                division_faults=faults,rng_calls=len(calls),seed='0xD0019A')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check',action='store_true')
    args = parser.parse_args()
    shareware = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    profile = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
    spec = json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())
    binary = mul.extract(ROOT/shareware['local_directory']/'doom19s.zip',shareware,profile)
    extracted = verify_units(binary,profile,spec)
    out = ROOT/'artifacts/original-arithmetic'
    out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    source = out/'Extracted.lean'
    source.write_text(certificate(extracted,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalAddSub',
                    'Doom.Proofs.OriginalRandom','fidelity-probe'],cwd=ROOT,check=True)
    result = subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                            text=True,capture_output=True,check=True)
    audit(result.stdout)
    print(result.stdout,end='',flush=True)
    report = dict(exe_sha256=profile['exe_sha256'],units=list(extracted),
                  certificate=str(source.relative_to(ROOT)),axiom_audit=result.stdout.splitlines(),cross_check=None)
    if args.cross_check: report['cross_check'] = cross_check(extracted,spec)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report['cross_check']),flush=True)
    print('PASS: original add/sub/division and arbitrary RNG call traces match under the documented x86 model.')


if __name__ == '__main__':
    try:
        main()
    except (OSError,ValueError,KeyError,struct.error,subprocess.CalledProcessError) as error:
        if isinstance(error,subprocess.CalledProcessError):
            print(error.stdout or '',file=sys.stderr)
            print(error.stderr or '',file=sys.stderr)
        sys.exit(f'original-arithmetic: {error}')

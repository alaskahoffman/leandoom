#!/usr/bin/env python3
"""Check original DOOM bytes, generate a Lean certificate, optionally emulate x86.

Offline; reads the original shareware archive without executing any DOS program.
LE layout/fixup definitions: Open Watcom bld/watcom/h/exeflat.h.
This deliberately accepts only the pinned image's simple page/fixup formats.
Unknown layouts are errors, never guessed or silently skipped.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import random
import re
import struct
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checked_hash(data, expected, label):
    require(hashlib.sha256(data).hexdigest() == expected, f'{label}: SHA-256 mismatch')


def extract(archive, shareware, spec):
    data = archive.read_bytes()
    checked_hash(data, shareware['archive_sha256'], 'shareware archive')
    with zipfile.ZipFile(io.BytesIO(data)) as outer:
        payload = outer.read('DOOMS_19.1') + outer.read('DOOMS_19.2')
    with zipfile.ZipFile(io.BytesIO(payload)) as inner:
        binary = inner.read(spec['exe_member'])
    checked_hash(binary, spec['exe_sha256'], 'DOOM.EXE')
    require(len(binary) == spec['exe_bytes'], 'unexpected executable size')
    return binary


def inspect_image(binary, spec):
    """Return bytes mapped from executable object 1 and all relocation ranges.

    The embedded MZ header is pinned, not found by scanning accidental signatures.
    All LE offsets are relative to LE except data pages (embedded-MZ-relative).
    """
    mz, le = int(spec['mz_offset'], 16), int(spec['le_offset'], 16)

    def u32(offset):
        return struct.unpack_from('<I', binary, offset)[0]

    require(binary[mz:mz+2] == b'MZ', 'embedded MZ signature')
    require(mz + u32(mz+0x3c) == le, 'embedded MZ → LE header mismatch')
    require(binary[le:le+4] == b'LE\0\0', 'little-endian LE signature')
    require(u32(le+4) == 0 and u32(le+8) == 0x10002, 'LE version/CPU/OS mismatch')
    require(u32(le+0x28) == 4096, 'unexpected LE page size')
    require(u32(le+0x44) == 3, 'unexpected object count')
    obj = le + u32(le+0x40)
    size, base, flags, first_page, page_count, reserved = struct.unpack_from('<6I', binary, obj)
    require(spec['code_object'] == 1, 'unsupported code object')
    require(size == int(spec['code_size'], 16) and flags == int(spec['code_flags'], 16),
            'code object size/flags mismatch')
    require(flags & 0x2004 == 0x2004, 'code object is not executable with 32-bit default operands')
    require(first_page == 1 and page_count == (size+4095)//4096 and reserved == 0,
            'unexpected code page mapping')
    page_map = le + u32(le+0x48)
    data_start = mz + u32(le+0x80)
    require(data_start == int(spec['data_pages_offset'], 16), 'data page offset mismatch')
    pages = []
    file_offsets = []
    for page in range(page_count):
        entry = binary[page_map+4*page:page_map+4*page+4]
        require(len(entry) == 4 and entry[3] == 0, 'unsupported/invalid code page')
        number = int.from_bytes(entry[:3], 'big')
        require(number == page+1, 'unexpected/non-contiguous physical code page')
        start = data_start + (number-1)*4096
        require(start+4096 <= len(binary), 'truncated code page')
        pages.append(binary[start:start+4096])
        file_offsets.extend(range(start, start+4096))
    code = b''.join(pages)[:size]
    file_offsets = file_offsets[:size]

    fix_pages, fix_records = le+u32(le+0x68), le+u32(le+0x6c)
    fix_end = le+u32(le+0x70)
    require(fix_pages + 4*(page_count+1) <= fix_records <= fix_end <= len(binary),
            'invalid fixup table bounds')
    relocations = []
    for page in range(page_count):
        pos, end = fix_records+u32(fix_pages+4*page), fix_records+u32(fix_pages+4*(page+1))
        require(fix_records <= pos <= end <= fix_end, 'invalid fixup page bounds')
        while pos < end:
            require(pos+5 <= end, 'truncated fixup record')
            src, target, offset, objnum = struct.unpack_from('<BBhB', binary, pos)
            # Only 32-bit absolute internal relocations occur in this code object.
            require(src == 7 and target in (0, 0x10) and 1 <= objnum <= 3,
                    'unsupported code relocation')
            width = 4 if target & 0x10 else 2
            pos += 5 + width
            require(pos <= end, 'truncated fixup target')
            relocations.append((page*4096+offset, 4))
    return code, file_offsets, relocations, base


def check_sites(code, file_offsets, relocations, spec):
    pattern = bytes.fromhex(spec['instruction_hex'])
    require(len(pattern) == 6, 'unexpected snippet size')
    positions = [i for i in range(len(code)) if code.startswith(pattern, i)]
    actual = [file_offsets[i] for i in positions]
    require(actual == [int(o, 16) for o in spec['site_file_offsets']], 'multiplication site inventory mismatch')
    sites = []
    for offset in positions:
        require(not any(max(offset, r) < min(offset+6, r+w) for r, w in relocations),
                f'loader relocation modifies instruction bytes at {offset:#x}')
        sites.append((file_offsets[offset], code[offset:offset+6]))
    return sites


def certificate(sites, spec):
    # Literal bytes come from the EXE slices, not the manifest's expected pattern.
    rows = ',\n'.join(f'  ({offset}, [{", ".join(hex(b) for b in data)}])' for offset, data in sites)
    return f'''-- Generated from DOOM.EXE SHA-256 {spec['exe_sha256']}.
-- File identity and extraction are external checks; the theorems below are kernel checked.
import Doom.Proofs.OriginalMul
namespace Doom.Verification.Extracted
open X86
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
def sites : Array (Nat × List UInt8) := #[
{rows}]
theorem all_extracted_bytes_match :
    ∀ i : Fin {len(sites)}, (sites[i.val]!).2 = Doom19.fixedMulBytes := by decide
theorem all_extracted_sites_match_engine (i : Fin {len(sites)}) (regs : Registers) :
    (run 2 (sites[i.val]!).2 regs).map (fun final => final eax) =
      some (Fixed.mul ⟨Int32.ofBitVec (regs eax)⟩
        ⟨Int32.ofBitVec (regs ebx)⟩).raw.toBitVec := by
  rw [all_extracted_bytes_match i]
  exact Doom.Proofs.original_mul_result regs
#print axioms all_extracted_bytes_match
#print axioms all_extracted_sites_match_engine
end Doom.Verification.Extracted
'''


def audit_axioms(output):
    lines = output.strip().splitlines()
    require(len(lines) == 2, 'unexpected certificate audit output')
    expected = ['all_extracted_bytes_match', 'all_extracted_sites_match_engine']
    for name, line in zip(expected, lines):
        require(line.startswith(f"'Doom.Verification.Extracted.{name}' "), 'missing audited theorem')
        if line.endswith('does not depend on any axioms'):
            continue
        match = re.search(r'depends on axioms: \[(.*)\]$', line)
        require(match is not None, 'unrecognized axiom audit')
        require(set(match[1].split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'},
                'unexpected proof axiom/trust extension')


def cross_check(code, file_offsets, sites):
    """Independent checks, not part of the universal proof or its trusted base."""
    import capstone
    import unicorn
    from unicorn import x86_const as x86

    disassembler = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32)
    disassembler.skipdata = True
    instructions = {i.address: i for i in disassembler.disasm(code, 0)}
    index = {offset: i for i, offset in enumerate(file_offsets)}
    for file_offset, data in sites:
        offset = index[file_offset]
        require(offset in instructions and offset+2 in instructions,
                'site not on linear-disassembly instruction boundaries')
        pair = [instructions[offset], instructions[offset+2]]
        require([(i.mnemonic, i.op_str) for i in pair] ==
                [('imul', 'ebx'), ('shrd', 'eax, edx, 0x10')], 'independent disassembly mismatch')
        require(b''.join(bytes(i.bytes) for i in pair) == data, 'independent instruction lengths mismatch')

    emulator = unicorn.Uc(unicorn.UC_ARCH_X86, unicorn.UC_MODE_32)
    address = 0x10000
    emulator.mem_map(address, 4096)
    emulator.mem_write(address, sites[0][1])
    rng = random.Random(0xD0019)
    edges = [0, 1, 2, 0x7fff, 0x8000, 0xffff, 0x10000, 0x10001,
             0x7fffffff, 0x80000000, 0x80000001, 0xffff0000, 0xfffffffe, 0xffffffff]
    pairs = [(a, b) for a in edges for b in edges]
    pairs += [(rng.getrandbits(32), rng.getrandbits(32)) for _ in range(10000)]
    names = ['EAX', 'ECX', 'EDX', 'EBX', 'ESP', 'EBP', 'ESI', 'EDI']
    registers = [getattr(x86, 'UC_X86_REG_'+name) for name in names]

    def signed(n):
        return n if n < 0x80000000 else n-0x100000000

    for a, b in pairs:
        before = [rng.getrandbits(32) for _ in names]
        before[0], before[3] = a, b
        for register, value in zip(registers, before):
            emulator.reg_write(register, value)
        # Vary arithmetic input flags; neither instruction consumes them.
        emulator.reg_write(x86.UC_X86_REG_EFLAGS, 2 | (rng.getrandbits(12) & 0x8d5))
        emulator.emu_start(address, address+6, count=2)
        product = signed(a)*signed(b)
        expected = before.copy()
        expected[0] = (product >> 16) & 0xffffffff
        expected[2] = (product >> 32) & 0xffffffff
        require([emulator.reg_read(r) for r in registers] == expected, 'x86 emulation mismatch')
        require(emulator.reg_read(x86.UC_X86_REG_EIP) == address+6, 'x86 instruction length mismatch')
    return dict(capstone=capstone.__version__, unicorn=unicorn.__version__, cases=len(pairs),
                instruction_boundary_sites=len(sites), seed='0xD0019')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, help='local doom19s.zip (same pinned SHA-256 required)')
    parser.add_argument('--cross-check', action='store_true', help='also run optional Capstone/Unicorn checks')
    args = parser.parse_args()
    shareware = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
    archive = args.archive or ROOT/shareware['local_directory']/'doom19s.zip'
    require(archive.exists(), f'{archive} missing; run ./scripts/fetch-shareware first')
    binary = extract(archive, shareware, spec)
    code, offsets, relocations, base = inspect_image(binary, spec)
    sites = check_sites(code, offsets, relocations, spec)
    out = ROOT/'artifacts/original-mul'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Extracted.lean'
    source.write_text(certificate(sites, spec))
    print(f'Verified DOOM.EXE SHA-256 {spec["exe_sha256"]}', flush=True)
    print(f'{len(sites)} byte-identical multiplication sites; {len(relocations):,} code relocations checked.', flush=True)
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.OriginalMul'], cwd=ROOT, check=True)
    result = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                            cwd=ROOT, check=True, text=True, capture_output=True)
    print(result.stdout, end='')
    audit_axioms(result.stdout)
    report = dict(exe_sha256=spec['exe_sha256'], sites=len(sites), relocations=len(relocations),
                  first_file_offset=hex(sites[0][0]), last_file_offset=hex(sites[-1][0]),
                  preferred_code_base=hex(base), kernel_certificate=str(source.relative_to(ROOT)),
                  axiom_audit=result.stdout.strip().splitlines(), cross_check=None)
    if args.cross_check:
        report['cross_check'] = cross_check(code, offsets, sites)
        print(f'Independent x86 checks: {report["cross_check"]}', flush=True)
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: all extracted snippets match Fixed.mul for all register inputs under the documented x86 model.')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, struct.error, zipfile.BadZipFile, subprocess.CalledProcessError) as error:
        if isinstance(error, subprocess.CalledProcessError):
            print(error.stdout or '', file=sys.stderr)
            print(error.stderr or '', file=sys.stderr)
        sys.exit(f'original-mul: {error}')

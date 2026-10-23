#!/usr/bin/env python3
"""Kernel-check every pinned E1M1 BLOCKMAP cell and its scan-entry adapters.

Python parsing and the WAD SHA256 are the explicit extraction boundary. The
certificate checks the supplied words, offsets, ordered IDs and sentinels; it
does not certify the DOS allocator, loader, or a whole multi-cell query.
"""
import hashlib
import json
import re
import struct
import subprocess
import verify_original_noise_topology as topology
ROOT, require = topology.ROOT, topology.require
PROOFS = ['sequence_valid', 'live_visits', 'address_from_list', 'item_from_image', 'nonlast_from_image',
          'sentinel_from_image', 'pointer_from_image', 'initialized_collection', 'reserve_cell']
NAMES = ['shape_checked', 'sequence_checked', 'payload_checked', 'offsets_checked', 'cells_checked', 'scan_inputs_checked']


def decode_blockmap(raw):
    require(len(raw) >= 8 and len(raw) % 2 == 0, 'invalid BLOCKMAP length')
    words = list(struct.unpack('<' + 'H' * (len(raw)//2), raw))
    width, height = words[2:4]
    require((width, height) == (36, 23), 'unexpected pinned map dimensions')
    end = 4 + width*height
    require(end <= len(words), 'truncated offset table')
    cells = []
    for offset in words[4:end]:
        require(end <= offset < min(len(words), 32768), 'invalid signed list offset')
        ids = []
        for value in words[offset:]:
            if value == 65535:
                break
            require(value < 475, 'invalid line ID')
            ids.append(value)
        else:
            raise ValueError('unterminated cell')
        require(ids and ids[0] == 0, 'missing leading linedef zero')
        require(len(ids) <= 13, 'cell exceeds pinned visit bound')
        cells.append((offset, ids))
    return dict(words=words, cells=cells, width=width, height=height,
                blockmap_sha256=hashlib.sha256(raw).hexdigest())


def pinned_data():
    _, profile = topology.pinned_data()  # validates the complete WAD hash and map structure
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    wad = (ROOT/share['local_directory']/'doom1.wad').read_bytes()
    require(hashlib.sha256(wad).hexdigest() == profile['wad_sha256'], 'pinned WAD hash mismatch')
    count, directory = struct.unpack_from('<II', wad, 4)
    lumps = []
    for i in range(count):
        start, size, name = struct.unpack_from('<II8s', wad, directory+16*i)
        lumps.append((name.rstrip(b'\0').decode('ascii'), wad[start:start+size]))
    start = next(i for i, (name, _) in enumerate(lumps) if name == 'E1M1')
    source = dict(lumps[start+1:start+11])
    require(len(source['LINEDEFS'])//14 == 475, 'unexpected linedef count')
    return decode_blockmap(source['BLOCKMAP']), profile


def certificate(data):
    words = '#['+','.join(map(str, data['words']))+']'
    cells = '#['+','.join('⟨'+str(off)+',['+','.join(map(str, ids))+']⟩' for off, ids in data['cells'])+']'
    source = f'''import Doom.Proofs.E1M1PathMap
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
namespace Doom.Verification.ExtractedPathMap
open Doom Doom.Proofs E1M1PathMap
-- Generated from hash-checked shareware data; includes leading zero and repeats.
def words : Array Nat := {words}
def cells : Array Cell := {cells}
theorem shape_checked : words.size=3461 ∧ words[2]?=some 36 ∧ words[3]?=some 23 ∧
    cells.size=36*23 := by decide +kernel
theorem sequence_checked : checkSequence 832 cells.toList=true := by decide +kernel
theorem payload_checked : words.toList.drop 832=payload cells.toList := by decide +kernel
theorem offsets_checked : (words.toList.drop 4).take cells.size=cells.toList.map Cell.offset := by decide +kernel
theorem cells_checked : ∀ i : Fin cells.size,
    words[4+i.val]?=some cells[i.val].offset ∧ cells[i.val].Valid words := by
  intro i
  have valid := sequence_valid words 832 cells.toList payload_checked sequence_checked
    cells[i.val] (by simp)
  have off := congrArg (fun xs : List Nat => xs[i.val]?) offsets_checked
  simp only [List.getElem?_take,if_pos i.isLt,List.getElem?_drop,List.getElem?_map,
    Array.getElem?_toList,Array.getElem?_eq_getElem i.isLt,Option.map_some] at off
  exact ⟨off,valid⟩
'''
    source += """
open Doom.Verification X86 X86Memory
/-- Every concrete map cell specializes the same scan-entry contract. -/
theorem scan_inputs_checked (j : Fin cells.size) (s : X86Memory.State) (base lines : Word)
    (image : WordImage s.memory base words)
    (cursor : s.regs 2=base+BitVec.ofNat 32 (2*cells[j.val].offset))
    (lineBase : load32 s.memory 0x2c120=lines) :
    (∀ i : Fin cells[j.val].ids.length,
      OriginalLineCell.itemWord (OriginalLineInvariant.atIndex s i.val)≠(0xffffffff#32) ∧
      ∀ frac : Fixed, OriginalLineDispatch.pointer (OriginalLineInvariant.atIndex s i.val)=
        resolve lines ⟨frac,true,cells[j.val].ids[i.val]⟩) ∧
    load16 s.memory (OriginalLineInvariant.address s cells[j.val].ids.length)=(0xffff#16) := by
  have valid := (cells_checked j).2
  refine ⟨?_,sentinel_from_image s base words _ valid image cursor⟩
  intro i
  exact ⟨nonlast_from_image s base words _ valid image cursor i,
    fun frac => pointer_from_image s base lines words _ valid image cursor lineBase i frac⟩
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1PathMap.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathMap\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedPathMap.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1PathMap.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, profile = pinned_data()
    out = ROOT/'artifacts/e1m1-path-map'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1PathMap'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=profile['wad_sha256'], blockmap_sha256=data['blockmap_sha256'],
                  cells=len(data['cells']), words=len(data['words']),
                  max_visits=max(len(ids) for _, ids in data['cells']),
                  total_visits=sum(len(ids) for _, ids in data['cells']),
                  axioms=checked.stdout.splitlines(),
                  scope='Every E1M1 BLOCKMAP cell, ordered signed-safe line IDs, leading zero and terminator. '
                        'Memory adapters derive scan nonlast/sentinel and line-pointer resolution from a word image. '
                        'Original query initialization establishes empty collection capacity for one cell. '
                        'Loader memory image, geometry, grid-write preservation, seen stamps, later-cell capacity '
                        'and whole-game equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: all 828 E1M1 cells; line-index/pointer and initial capacity adapters; strict axiom audit.')


if __name__ == '__main__':
    main()

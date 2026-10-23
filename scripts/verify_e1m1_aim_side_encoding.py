#!/usr/bin/env python3
"""Join authenticated side-pointer emissions to the E1M1 aiming byte image."""
import argparse,json,re,subprocess
import verify_e1m1_aim_encoded_portal as previous
import verify_original_side_loader as side
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
evidence=previous.evidence
HEADER=previous.HEADER
MODULE='E1M1AimSideEncoding'
GROUPS={MODULE:['word_of_load','preserved','publish_encoding','link_encoding','link_retains','row_encoding','row_source','initial_encoding']}
CONTRACTS=[(MODULE,n,a) for n,a in [
 ('word_of_load','m a v value'),('preserved','p before after image kept'),
 ('publish_encoding','s f'),('link_encoding','s f side index sideBase sectorBase input'),
 ('link_retains','s p outside'),
 ('row_encoding','r sideBase sectorBase frontState backState ff bf m frontInput backInput frontKept backKept'),
 ('row_source','r raw sideBase sectorBase frontState backState ff bf m frontInput backInput frontKept backKept present global rawImage'),
 ('initial_encoding','total rows raw vertexBase sideBase sectorBase m frontState backState frontInput backInput frontKept backKept globals rawImage vertices sectors')]]
NAMESPACE='Doom.Verification.ExtractedAimSideEncoding'
PINNED=['rows_sector_indices','records_sector_indices','front_input','back_input']
REUSED=['Doom.Proofs.OriginalSideLoader.graph_pointer','Doom.Proofs.OriginalSideLoader.nonnegative_offset','Doom.Proofs.OriginalSideLoader.untouched','Doom.Proofs.E1M1AimEncodedPortal.side_source']

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Row':'E1M1AimEncodedPortal','sideBytes':'E1M1AimEncodedPortal','rawBytes':'E1M1AimEncodedPortal',
      'Input':MODULE,'Kept':MODULE,'sectorAddress':MODULE,'Realizes':'E1M1NoiseImage','word':'E1M1NoiseImage','half':'E1M1NoiseImage'}
    for word,owner in owners.items():decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def side_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-side-loader.json').read_text())
    binary=side.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    return side.extraction.extract(binary,profile,spec),spec['units'],profile

def combined_units(aim_units,scan_units,side_units):
    units=evidence.combined_units(aim_units,scan_units)
    by_offset={u['code_offset']:u for u in units.values()}
    for name,unit in side_units.items():
        old=by_offset.get(unit['code_offset'])
        if old is not None:require(old==unit,'inconsistent side-loader byte range')
        else:units['side_'+name]=unit;by_offset[unit['code_offset']]=unit
    return units

def names():
    return ([NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+
      ['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]+REUSED+
      [NAMESPACE+'.'+n for n in PINNED])

def certificate(data,raw,scan_inputs=None,side_inputs=None):
    if side_inputs is None:side_inputs=side_data()
    source='import Doom.Proofs.E1M1AimSideEncoding\n'+previous.certificate(data,raw,scan_inputs)
    source+='\n'+side.certificate(side_inputs[0]).split('\n',1)[1]
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        uses_code='OriginalSideLoader.program' in decl
        decl=decl.replace('OriginalSideLoader.program','(OriginalSideLoader.bytesProgram Doom.Verification.ExtractedSideLoader.publish Doom.Verification.ExtractedSideLoader.link)')
        source+='namespace '+module+'\n'+decl+' := by\n'
        if uses_code:source+='  rw [Doom.Verification.ExtractedSideLoader.publish_checked,Doom.Verification.ExtractedSideLoader.link_checked]\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='''
open E1M1AimSideEncoding
open Doom.Verification.ExtractedAimEncodedPortal (rows records row_count)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
theorem rows_sector_indices : rows.all (fun r => decide (r.frontSector<32768) &&
    (r.backIndex==65535 || decide (r.backSector<32768)))=true := by decide +kernel
theorem records_sector_indices (i : Fin 475) :
    (records i).frontSector<32768 ∧ ((records i).backIndex≠65535 → (records i).backSector<32768) := by
  have h := List.all_eq_true.mp rows_sector_indices _ (List.get_mem rows ⟨i.val,by simpa only [row_count] using i.isLt⟩)
  change (decide ((records i).frontSector<32768) &&
    ((records i).backIndex==65535 || decide ((records i).backSector<32768)))=true at h
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  exact ⟨h.1,fun present => h.2.elim (fun eq => False.elim (present eq)) id⟩
theorem front_input (i : Fin 475) (s : X86Memory.State) (sideBase sectorBase : Word)
    (record : s.regs 2=sideBase+(records i).frontIndex.signExtend 32*18)
    (source : E1M1NoiseImage.Realizes (E1M1NoiseImage.half (s.regs 3+28)
      (BitVec.ofNat 16 (records i).frontSector)) s.memory)
    (sectors : load32 s.memory 0x2c148=sectorBase) (safe : Apart 0x2c148 (s.regs 4)) :
    Input s (records i).frontIndex (records i).frontSector sideBase sectorBase := by
  exact ⟨record,source,sectors,safe,(records_sector_indices i).1⟩
theorem back_input (i : Fin 475) (s : X86Memory.State) (sideBase sectorBase : Word)
    (present : (records i).backIndex≠65535)
    (record : s.regs 2=sideBase+(records i).backIndex.signExtend 32*18)
    (source : E1M1NoiseImage.Realizes (E1M1NoiseImage.half (s.regs 3+28)
      (BitVec.ofNat 16 (records i).backSector)) s.memory)
    (sectors : load32 s.memory 0x2c148=sectorBase) (safe : Apart 0x2c148 (s.regs 4)) :
    Input s (records i).backIndex (records i).backSector sideBase sectorBase := by
  exact ⟨record,source,sectors,safe,(records_sector_indices i).2 present⟩
'''
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'Doom.Verification.ExtractedSideLoader.publish_checked'"
    require(marker in output,'missing side-loader audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=marker+rest
    marker="'"+names()[0]+"'";require(marker in rest,'missing side-encoding audit')
    side_part,rest=rest.split(marker,1);side.audit(side_part);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();scan_inputs=evidence.scan_data();side_inputs=side_data()
    require(mp['exe_sha256']==profile['exe_sha256']==scan_inputs[3]['exe_sha256']==side_inputs[2]['exe_sha256'],'executable mismatch')
    require(mp['wad_sha256']==scan_inputs[3]['wad_sha256'],'WAD mismatch')
    out=ROOT/'artifacts/e1m1-aim-side-encoding';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan_inputs,side_inputs))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimSideEncoding'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    require(not checked.stderr.strip(),'unexpected stderr')
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],
      units=combined_units(spec['units'],scan_inputs[1],side_inputs[1]),cells=len(data['cells']),pinned_rows=475,
      reused_declarations=REUSED,new_binary_ranges_in_chain=2,
      scope='Authenticated side publication and pointer-emission suffixes establish aiming byte representations. Consumed-byte preservation connects per-side endpoints to a common line-loader entry. E1M1 sector-index bounds are kernel checked. Enclosing side-loader execution, allocation, raw-byte loading and intervening startup preservation remain unproved. No runtime or instruction-semantics changes.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: authenticated side-loader outputs joined to aiming byte encoding; inherited and new strict audits.')
if __name__=='__main__':main()

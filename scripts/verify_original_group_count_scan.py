#!/usr/bin/env python3
"""Whole original counting loop establishes the pinned E1M1 sector counts."""
import argparse,json,re,subprocess
import verify_original_group_count as count
import verify_original_noise_topology as topology
ROOT,require=count.ROOT,count.require
NAMES=[n if '.' in n else 'Doom.Verification.ExtractedGroupCount.'+n for n in count.NAMES]
NAMES+=['Doom.Proofs.OriginalGroupCountScan.'+n for n in [
    'safe_tail','layout_tail','head_reads','protected_head','inputs_step','linked_step',
    'after_frame','after_inputs','head_sector','after_sector','after_total','result_pc',
    'ready_step','scan_path','entry_ready','complete','after_stack','final_stack','final_frame','final_sector','final_inputs',
    'final_arguments','final_global','topology_counts','physical_references']]
NAMES+=['Doom.Verification.ExtractedGroupCountScan.'+n for n in [
    'line_count','sector_count','ranges_checked','grouped_checked','references_checked','scan_checked']]
def certificate(raw,data):
    s=count.certificate(raw).replace('import Doom.Proofs.OriginalGroupCount','import Doom.Proofs.OriginalGroupCountScan')
    s+='''set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.ExtractedGroupCountScan
open X86 X86Memory X86Control Doom.Proofs
open OriginalGroupCountScan E1M1NoiseTopology
'''
    emitted=topology.certificate(data)
    s+='def topology : Topology := '+emitted.split('def topology : Topology := ',1)[1].split('theorem topology_checked',1)[0]
    s+='''theorem line_count : topology.lines.length=475 := by decide +kernel
theorem sector_count : topology.sectors.length=85 := by decide +kernel
theorem ranges_checked : ∀ e∈topology.lines, OriginalGroupLines.InRange e topology.sectors.length := by decide +kernel
theorem grouped_checked : topology.Grouped := by decide +kernel
theorem references_checked : logicalReferences topology.lines=642 := by decide +kernel

theorem scan_checked (a : Addresses) (s : X86Memory.State) (f : Option Flags)
    (addresses : OriginalGroupLines.SectorAddresses a topology.sectors.length)
    (layout : Layout (topology.lines.map (E1M1GroupOutput.physical a)))
    (inputs : OriginalGroupOutput.Inputs (topology.lines.map (E1M1GroupOutput.physical a)) s.memory)
    (linked : OriginalGroupOutput.Linked (topology.lines.map (E1M1GroupOutput.physical a)) (load32 s.memory 0x2c120))
    (count : (load32 s.memory 0x2c134).toNat=475)
    (zeros : ∀ i : Fin topology.sectors.length, load32 s.memory (a.sector i.val+78)=0)
    (counters : ∀ i : Fin topology.sectors.length,
      CounterSafe (a.sector i.val) (topology.lines.map (E1M1GroupOutput.physical a))) :
    ∃ out, X86Routine.run (OriginalGroupCount.bytesProgram ExtractedGroupCount.count) [0x2e639] 8084
      ⟨s,f,0x2e5ef⟩=some out ∧ out.pc=0x2e639 ∧
      out.core.regs 0=2568 ∧ out.core.regs 2=50 ∧ out.core.regs 3=0 ∧
      OriginalGroupOutput.Inputs (topology.lines.map (E1M1GroupOutput.physical a)) out.core.memory ∧
      load32 out.core.memory 0x2c134=load32 s.memory 0x2c134 ∧
      ∀ i : Fin topology.sectors.length, load32 out.core.memory (a.sector i.val+78)=
        BitVec.ofNat 32 (topology.sectors[i.val]).length := by
  let es := topology.lines.map (E1M1GroupOutput.physical a)
  have size : es.length=475 := by simp [es,line_count]
  have run := complete es s f (by rw [size]; decide) layout inputs linked (by rw [size]; exact count)
  have args := final_arguments es s layout inputs linked
  have refs : references es=642 := by
    exact (physical_references topology.lines a topology.sectors.length addresses ranges_checked).trans references_checked
  rw [size] at run
  rw [refs] at args
  refine ⟨final es s,?_,args.2.2.2,?_,args.2.1,args.2.2.1,
    final_inputs es s layout inputs linked,final_global es s layout inputs linked,?_⟩
  · rw [ExtractedGroupCount.bytes_checked]; exact run
  · exact args.1
  · exact topology_counts topology a s addresses ranges_checked grouped_checked layout inputs linked zeros counters
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES[len(count.NAMES):])+'\nend Doom.Verification.ExtractedGroupCountScan\n'
def audit(output):
    rest=output.strip()
    for name in NAMES:
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    ex=count.extraction;profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=ex.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=ex.extract(binary,profile,json.loads((ROOT/'tests/reference/original-group-count.json').read_text()))
    data,wp=topology.pinned_data();require(profile['exe_sha256']==wp['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/original-group-count-scan';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupCountScan'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,data))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=count.cross_check(raw,data) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],wad_sha256=wp['wad_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,
      scope='Whole original counting loop and allocation arguments, at most 8084 instructions for 475 pinned lines. Derives all 85 sector counts, 642 references and 2568 requested bytes. Initial cached pointers, zero counters, global count and physical separation remain explicit; startup reachability and allocator execution are not proved.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: whole original counting pass establishes every pinned sector count.')
if __name__=='__main__':main()

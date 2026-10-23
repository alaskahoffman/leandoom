#!/usr/bin/env python3
"""Full original linedef loader establishes the existing grouping input relation."""
import argparse,json,re,subprocess
import verify_original_line_source as source
ROOT,require=source.ROOT,source.require
NAMES=source.NAMES+['Doom.Proofs.E1M1LineOutput.'+n for n in [
    'target_transport','transport','copy_reg','copy_frame','copy_source','iteration_output',
    'image_preserved','final_record','grouping_inputs','physical_lines','scan_to_grouping']]
NAMES+=['Doom.Verification.ExtractedLineOutput.'+n for n in ['topology_count','physical_list','scan_checked']]
def certificate(raw,data):
    s=source.certificate(raw,data).replace('import Doom.Proofs.E1M1LineSource','import Doom.Proofs.E1M1LineOutput')
    s+="""set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineOutput
open Doom.Proofs X86 X86Memory X86Control E1M1LineOutput
"""
    s+='def topology : List E1M1NoiseTopology.Line := ['+','.join('⟨'+','.join(str(v) for v in g)+'⟩' for g in data['lines'])+']\n'
    s+="""theorem topology_count : topology.length=475 := by decide +kernel
def sides (a : E1M1NoiseTopology.Addresses) (i : Fin 475) : Sides :=
  physicalSides a (topology.get ⟨i.val,by simpa only [topology_count] using i.isLt⟩)
theorem physical_list (a : E1M1NoiseTopology.Addresses) (output : Word)
    (addresses : ∀ i : Fin topology.length,
      a.line (topology.get i).index=E1M1LineScan.cursor output 62 i.val) :
    lines (sides a) output=topology.map (E1M1GroupOutput.physical a) := by
  exact physical_lines topology a output addresses

theorem scan_checked {raw vertexBase sideBase output sp s f}
    (a : E1M1NoiseTopology.Addresses)
    (addresses : ∀ i : Fin topology.length,
      a.line (topology.get i).index=E1M1LineScan.cursor output 62 i.val)
    (layout : E1M1LineScan.Layout 475 output sp)
    (ready : E1M1LineScan.Ready 475 raw output sp 0 s)
    (verticesSafe : E1M1LineSource.ImageLayout ExtractedLineSource.records raw vertexBase output sp)
    (vertices : E1M1LineSource.Image ExtractedLineSource.records raw vertexBase s.memory)
    (sidesSafe : ImageLayout (sides a) raw sideBase output sp)
    (sideImage : Image (sides a) raw sideBase s.memory)
    (storage : OutputLayout 475 output sp) :
    X86Routine.run ExtractedLineIteration.program [0x2e3c1] 49400 ⟨s,f,0x2e29a⟩=
      some (E1M1LineScan.states s f 475) ∧
    (E1M1LineScan.states s f 475).pc=0x2e3c1 ∧
    OriginalGroupOutput.Inputs (topology.map (E1M1GroupOutput.physical a))
      (E1M1LineScan.states s f 475).core.memory := by
  unfold ExtractedLineIteration.program
"""
    s+='  rw ['+','.join('ExtractedLineIteration.'+n+'_checked' for n in source.scan.iteration.UNITS)+']\n'
    s+="""  rw [←physical_list a output addresses]
  exact scan_to_grouping (total:=475) (geometry:=ExtractedLineSource.records) (records:=sides a)
    (raw:=raw) (vertexBase:=vertexBase) (sideBase:=sideBase) (output:=output) (sp:=sp) (s:=s) (f:=f)
    layout ready verticesSafe vertices ExtractedLineSource.records_good sidesSafe sideImage storage (by decide)
"""
    s+='\n'.join('#print axioms '+n for n in NAMES[len(source.NAMES):])
    return s+'\nend Doom.Verification.ExtractedLineOutput\n'
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
    extraction=source.scan.iteration.extraction
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw={}
    for name in ['original-div-memory','original-line-setup','original-line-geometry','original-line-load','original-line-cache']:
        raw.update(extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())))
    data,wp=source.scan.iteration.setup.geometry.geometry_data();require(profile['exe_sha256']==wp['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/original-line-output';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineOutput'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,data))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=source.scan.cross_check(raw,data) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],wad_sha256=wp['wad_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,
        scope='Complete pinned linedef loop establishes the relocated topology Inputs required by sector grouping. Initial geometry/side images, storage separation and address relation remain explicit. Startup image construction and intervening grouping instructions are not joined.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: whole linedef loader establishes pinned sector-grouping inputs.')
if __name__=='__main__':main()

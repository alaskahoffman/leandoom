#!/usr/bin/env python3
"""Pinned WAD geometry discharges the original linedef loop's division safety."""
import argparse,json,re,subprocess
import verify_original_line_scan as scan
ROOT,require=scan.ROOT,scan.require
NAMES=scan.NAMES+['Doom.Proofs.E1M1LineSource.'+n for n in [
    'half_of_word','transport','vertices_frame','prepared_deltas','safe_of_source',
    'image_preserved','iteration_deltas','arithmetic_of_image','scan_from_image']]
NAMES+=['Doom.Verification.ExtractedLineSource.'+n for n in ['row_count','rows_good','records_good','scan_checked']]
def certificate(raw,data):
    s=scan.certificate(raw,data).replace('import Doom.Proofs.E1M1LineScan','import Doom.Proofs.E1M1LineSource')
    s+='''namespace Doom.Verification.ExtractedLineSource
open Doom.Proofs X86 X86Memory X86Control E1M1LineSource
'''
    s+='def rows : List Record := ['+','.join('⟨'+','.join(str(v) for v in g)+'⟩' for g in data['geometry'])+']\n'
    s+='''theorem row_count : rows.length=475 := by decide +kernel
theorem rows_good : rows.all good=true := by decide +kernel
def records (i : Fin 475) : Record := rows.get ⟨i.val,by simpa only [row_count] using i.isLt⟩
theorem records_good (i : Fin 475) : good (records i)=true :=
  List.all_eq_true.mp rows_good _ (List.get_mem rows ⟨i.val,by simpa only [row_count] using i.isLt⟩)

/-- No assumed per-iteration arithmetic success remains in this theorem.
The initial raw/decoded-vertex memory image and storage separation are explicit. -/
theorem scan_checked {raw base line sp s f} (layout : E1M1LineScan.Layout 475 line sp)
    (ready : E1M1LineScan.Ready 475 raw line sp 0 s)
    (separate : ImageLayout records raw base line sp)
    (image : Image records raw base s.memory) :
    X86Routine.run ExtractedLineIteration.program [0x2e3c1] 49400 ⟨s,f,0x2e29a⟩=
      some (E1M1LineScan.states s f 475) ∧
    (E1M1LineScan.states s f 475).pc=0x2e3c1 ∧
    E1M1LineScan.Ready 475 raw line sp 475 (E1M1LineScan.states s f 475).core := by
  unfold ExtractedLineIteration.program
'''
    s+='  rw ['+','.join('ExtractedLineIteration.'+n+'_checked' for n in scan.iteration.UNITS)+']\n'
    s+='''  exact scan_from_image (total:=475) (records:=records) (raw:=raw) (base:=base)
    (line:=line) (sp:=sp) (s:=s) (f:=f) layout ready separate image records_good (by decide)
'''
    s+='\n'.join('#print axioms '+n for n in NAMES[len(scan.NAMES):])
    return s+'\nend Doom.Verification.ExtractedLineSource\n'
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
    extraction=scan.iteration.extraction
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw={}
    for name in ['original-div-memory','original-line-setup','original-line-geometry','original-line-load','original-line-cache']:
        raw.update(extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())))
    data,wp=scan.iteration.setup.geometry.geometry_data();require(profile['exe_sha256']==wp['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/original-line-source';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineSource'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,data))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=scan.cross_check(raw,data) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],wad_sha256=wp['wad_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,
        scope='Complete 475-record linedef loop from initial WAD-index/decoded-vertex memory relation and static separation. Per-iteration division safety derived. Actual startup allocation and construction of that initial memory remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: pinned WAD source relation discharges whole-loop division safety.')
if __name__=='__main__':main()

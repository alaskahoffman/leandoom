#!/usr/bin/env python3
"""Certify pinned WAD topology and specialize conditional original noise completion.

The Python byte decoder and SHA256 bind the generated finite data to the WAD;
Lean checks its topology and the address-independent lifting theorem. This does
not certify DOS loader execution or supply physical memory representations.
"""
import hashlib,json,re,struct,subprocess
from pathlib import Path
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['topology_checked','ordered_lines_checked','side_range_checked','world_checked','completion_checked']
NAMES+=['Doom.Proofs.E1M1NoiseTopology.'+n for n in ['table_length','covered','sector_member','closed','bounded','world','completes']]
MAP_LABELS=['THINGS','LINEDEFS','SIDEDEFS','VERTEXES','SEGS','SSECTORS','NODES','SECTORS','REJECT','BLOCKMAP']

def decode_wad(data):
    require(len(data)>=12 and data[:4]==b'IWAD','not an IWAD')
    count,directory=struct.unpack_from('<II',data,4)
    require(directory>=12 and directory+16*count<=len(data),'WAD directory out of bounds')
    lumps=[]
    for i in range(count):
        start,size,name=struct.unpack_from('<II8s',data,directory+16*i)
        require(start+size<=len(data),'lump out of bounds')
        lumps.append((name.rstrip(b'\0').decode('ascii'),data[start:start+size]))
    maps=[i for i,(name,_) in enumerate(lumps) if name=='E1M1']
    require(len(maps)==1,'expected one E1M1 marker')
    selected=lumps[maps[0]+1:maps[0]+11]
    require([n for n,_ in selected]==MAP_LABELS,'unexpected E1M1 lump order')
    source=dict(selected)
    for name,size in [('SECTORS',26),('SIDEDEFS',30),('LINEDEFS',14)]:
        require(len(source[name])>0 and len(source[name])%size==0,name+': invalid record size')
    sectors=len(source['SECTORS'])//26
    sides=[x[-1] for x in struct.iter_unpack('<hh8s8s8sH',source['SIDEDEFS'])]
    require(all(i<sectors for i in sides),'side sector outside map')
    rows=[[] for _ in range(sectors)];lines=[]
    for i,(_,_,flags,_,_,front,back) in enumerate(struct.iter_unpack('<7H',source['LINEDEFS'])):
        require(front<len(sides) and front<32768,'invalid signed front side')
        require(back==65535 or (back<len(sides) and back<32768),'invalid signed back side')
        require(not flags&4 or back!=65535,'two-sided line has no back side')
        f=sides[front];b=0 if back==65535 else sides[back]
        lines.append([i,flags&255,front,back,f,b])
        rows[f].append(i)
        if back!=65535 and b!=f:rows[b].append(i)
    return dict(rows=rows,sides=sides,lines=lines,limit=max(map(len,rows)),
        lump_sha256={n:hashlib.sha256(source[n]).hexdigest() for n in ['SECTORS','SIDEDEFS','LINEDEFS']})

def pinned_data():
    profile=json.loads((ROOT/'tests/reference/e1m1-proof-profile.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    data=(ROOT/share['local_directory']/'doom1.wad').read_bytes()
    require(hashlib.sha256(data).hexdigest()==profile['wad_sha256']==share['wad_sha256'],'pinned WAD hash mismatch')
    return decode_wad(data),profile

def certificate(data):
    n=len(data['rows']);limit=data['limit'];fuel=2*n*(limit+1)+1;space=56*n+20
    rows='['+','.join('['+','.join(map(str,row))+']' for row in data['rows'])+']'
    sides='['+','.join(map(str,data['sides']))+']'
    lines='['+',\n'.join('⟨'+','.join(map(str,e))+'⟩' for e in data['lines'])+']'
    s=f'''import Doom.Proofs.E1M1NoiseTopology
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.ExtractedNoiseTopology
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoisePreservation
open E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger E1M1NoiseRecursive
open E1M1NoiseGraph E1M1NoiseGraphAllocation E1M1NoiseTermination E1M1NoiseTopology
-- Generated only in artifacts, from the hash-checked local shareware WAD.
def topology : Topology := ⟨{rows},{sides},{lines}⟩
theorem topology_checked : Certified topology {limit} := by
  constructor <;> decide +kernel
theorem ordered_lines_checked : topology.lines.map Line.index=List.range {len(data['lines'])} := by decide +kernel
theorem side_range_checked : ∀ i∈topology.sides, i<{n} := by decide +kernel

theorem world_checked (a : Addresses) (stack : Region) (base : Word) (regions : List Region)
    (allocation : Allocation (topology.table a) stack)
    (storage : Storage (topology.table a) stack base (topology.edges a) regions) :
    World (topology.table a) stack base (topology.edges a) regions {limit} :=
  world topology_checked a allocation storage

theorem completion_checked (a : Addresses) (stack : Region) (base : Word) (regions : List Region)
    (generation : Word) (s : X86Control.State) (xs : Ledger)
    (allocation : Allocation (topology.table a) stack)
    (storage : Storage (topology.table a) stack base (topology.edges a) regions)
    (shape : addresses xs=layout (topology.table a)) (ledger : Represents generation s.core.memory xs)
    (map : MapRep (topology.table a) s.core.memory) (graph : GraphRep base (topology.edges a) s.core.memory)
    (index : Nat) (inside : index<{n}) (sector : s.core.regs 0=a.sector index)
    (count : s.core.regs 2=0 ∨ s.core.regs 2=1)
    (low : stack.lo+{space}≤(s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4≤stack.hi) (bound : stack.hi≤2^32) :
    ∃ out, eval {fuel} .sector s=some out ∧ Restored s.core out ∧
      MapRep (topology.table a) out.core.memory ∧ GraphRep base (topology.edges a) out.core.memory :=
  completes topology_checked a allocation storage shape ledger map graph index inside sector count low high bound
'''
    return s+'\n'.join('#print axioms '+name for name in NAMES)+'\nend Doom.Verification.ExtractedNoiseTopology\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseTopology.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def main():
    out=ROOT/'artifacts/original-noise-topology';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    data,profile=pinned_data()
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-termination')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseTopology'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    p=out/'Checked.lean';p.write_text(certificate(data))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-termination/report.json').read_text())
    require(dep['exe_sha256']==profile['exe_sha256'],'executable profile mismatch')
    n=len(data['rows']);limit=data['limit']
    report=dict(exe_sha256=dep['exe_sha256'],wad_sha256=profile['wad_sha256'],lump_sha256=data['lump_sha256'],
        sectors=n,lines=len(data['lines']),sides=len(data['sides']),line_entries=sum(map(len,data['rows'])),
        max_lines=limit,evaluator_fuel=2*n*(limit+1)+1,stack_below_esp=56*n+20,
        audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),
        scope='Pinned WAD finite topology is kernel-checked for coverage, closure, side references, original grouping order and line bounds. Generic Lean proofs lift it through arbitrary address functions to the original traversal World and conditional bounded completion. Physical allocation/storage, map/graph memory relations and ledger/entry conditions remain explicit. Python parsing plus SHA256 binds the finite literals to WAD bytes; DOS loader execution and live Lean sound-worklist correspondence are not proved.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(r.stdout,end='');print(f'PASS: E1M1 topology: {n} sectors, {len(data["lines"])} lines, limit {limit}; fuel {report["evaluator_fuel"]}, stack reserve {report["stack_below_esp"]}.')
if __name__=='__main__':main()

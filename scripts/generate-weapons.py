#!/usr/bin/env python3
"""Extract the original fist, pistol and shotgun psprite tables."""
import importlib.util,argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('death_data',ROOT/'scripts/generate-death.py')
data=importlib.util.module_from_spec(spec);spec.loader.exec_module(data)
def generate():
    rows,ids,_,_=data.data()
    out='''/- Generated from pinned Chocolate Doom 3.1.1 info.c by scripts/generate-weapons.py.
Copyright 1993-1996 id Software; 2005-2014 Simon Howard. GPL-2.0-or-later.
Lean adaptation 2026-10-03. See COPYING.md. -/
namespace Doom.WeaponData
structure Frame where
  name : String
  sprite : String
  frame : Nat
  tics : Int32
  next : Nat
  action : String
  deriving Inhabited

def frames : Array Frame := #[
'''
    chosen=rows[:ids['S_SGUNFLASH2']+1]
    out+=',\n'.join(f'  ⟨"{name}","{spr[4:]}",{frame},{tics},{ids[nxt]},"{action}"⟩' for spr,frame,tics,action,nxt,name in chosen)
    out+='\n]\n'
    for row in chosen:out+=f'def {row[-1][2:]} : Nat := {ids[row[-1]]}\n'
    return out+'end Doom.WeaponData\n'
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');a=p.parse_args()
    path=ROOT/'Doom/WeaponData.lean';content=generate()
    if a.write:path.write_text(content)
    else:assert path.read_text()==content,'WeaponData differs from reference'

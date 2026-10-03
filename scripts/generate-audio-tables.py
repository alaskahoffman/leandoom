#!/usr/bin/env python3
"""Reproduce audio tables from the pinned GPL Chocolate Doom/Nuked sources."""
from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[1]
cache=root/'artifacts/reference/chocolate-doom-3.1.1'
out='/- Generated from Chocolate Doom 3.1.1 / Nuked OPL3 1.8.\nCopyright id Software, Simon Howard, Alexey Khokholov. GPL-2.0-or-later. -/\nnamespace Doom.Audio.Tables\n'
for file,names in [('opl/opl3.c',['logsinrom','exprom','mt','kslrom','kslshift','eg_incstep','ad_slot','ch_slot']),('src/i_oplmusic.c',['frequency_curve','volume_mapping_table'])]:
 s=(cache/file).read_text()
 for name in names:
  body=re.search(r'\b'+name+r'\s*\[[^;=]*=\s*\{(.*?)\};',s,re.S).group(1)
  body=re.sub(r'//[^\n]*|/\*.*?\*/','',body,flags=re.S)
  values=[int(n,0) for n in re.findall(r'-?0x[0-9a-fA-F]+|-?\d+',body)]
  typ='Int' if min(values)<0 else 'Nat'
  out+=f'def {name} : Array {typ} := #[\n'
  out+=',\n'.join('  '+','.join(map(str,values[i:i+16])) for i in range(0,len(values),16))+'\n]\n'
s=(cache/'src/doom/sounds.c').read_text()
out+='def sfx : Array (String × Nat) := #[\n'
out+=',\n'.join(f'  ("{n}",{p})' for n,p in re.findall(r'\bSOUND\("(\w+)",\s*(\d+)\)',s))+'\n]\nend Doom.Audio.Tables\n'
p=root/'Doom/Audio/Tables.lean'
if '--write' in sys.argv:p.write_text(out)
elif p.read_text()!=out:raise SystemExit('audio tables differ from pinned sources')

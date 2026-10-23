import Doom.Verification.X86Routine
open Doom.Verification X86 X86Memory X86Control
#eval Id.run do
  for (bytes,op,len) in ([
    ([0x66,0x31,0xc0],.xorHalf 0 0,3),([0x3d,0,0,0x6d,0x61],.compareRegister 0 0x616d0000,5),
    ([0x73,0x80],.jumpUnsigned 2 (-128),2),([0x76,0x7f],.jumpUnsigned 1 127,2),
    ([0x0f,0x82,0,0xff,0xff,0xff],.jumpUnsigned 0 (-256),6)] : List (List UInt8 × X86Routine.Op × Nat)) do
    if X86Routine.decodeAt bytes 0 != some (op,len) then return false
  for bytes in ([[0x66,0x31],[0x66,0x31,0x00],[0x3d,1,2,3],[0x73],[0x76],
      [0x0f,0x82,0,0,0],[0x66,0x31,0x40,0]] : List (List UInt8)) do
    if (X86Routine.decodeAt bytes 0).isSome then return false
  for a in ([0,1,255,256,0x7fffffff,0x80000000,0xffffffff] : List Word) do
    for b in ([0,1,255,256,0x7fffffff,0x80000000,0xffffffff] : List Word) do
      let s : X86Control.State := ⟨⟨fun _ => a,fun _ => 0xa5⟩,some (compare32 a b),0x100⟩
      if (compare32 a b).carry != some (decide (a.toNat < b.toNat)) then return false
      for c in [:3] do
        let take := if c=0 then a.toNat < b.toNat else if c=1 then a.toNat ≤ b.toNat else a.toNat ≥ b.toNat
        let some t := X86Routine.execute (.jumpUnsigned c (-128)) s | return false
        if t.pc != (if take then 0x80 else 0x100) then return false
        if t.core.regs 0 != a || t.core.memory 0 != 0xa5 || t.flags != s.flags then return false
      let some t := X86Routine.execute (.xorHalf 0 0) s | return false
      if t.core.regs 0 != a &&& 0xffff0000 || t.flags != some ⟨true,false,false,some false⟩ then return false
      if t.core.regs 1 != a || t.core.memory 0 != 0xa5 then return false
  let s : X86Control.State := ⟨⟨fun _ => 0,fun _ => 0⟩,some ⟨false,false,false,none⟩,0⟩
  if (X86Routine.execute (.jumpUnsigned 0 1) s).isSome then return false
  if (X86Routine.execute (.jumpUnsigned 0 (-1)) {s with flags := some (compare32 0 1)}).isSome then return false
  if (X86Routine.execute (.jumpUnsigned 2 1) {s with flags := some (compare32 1 0),pc := 4294967295}).isSome then return false
  if (X86Routine.execute (.jumpUnsigned 3 1) {s with flags := some (compare32 1 0)}).isSome then return false
  if (logical32 0).carry != some false || (logical8 255).carry != some false then return false
  return true

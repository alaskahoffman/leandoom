import Doom.Proofs.OriginalKillBookkeeping
open Doom Doom.Verification X86 X86Memory X86Control Doom.Proofs KillBookkeeping

-- Execute the actual decoded suffix, including signed player-slot division and
-- wrapping counters, then compare with the live engine's bookkeeping function.
#eval Id.run do
  for slot in [:4] do
    if hi : slot < 4 then
      let i : Fin 4 := ⟨slot,hi⟩
      for multiplayer in [false,true] do
        for flags in ([0,2,0x400000,0x400002,0xffffffff] : List UInt32) do
          for counter in ([-2147483648,-1,0,1,2147483647] : List Int32) do
            for sp in ([0,1,0x8000,0xffffffff] : List Word) do
              let obj : Word := 0x1001
              let body : Death.Body := {flags,player := some i}
              let world : Death.World := {netgame := multiplayer,players := Vector.replicate 4 {kills := counter,frags := Vector.replicate 4 counter}}
              let mut m : Memory := fun _ => 0xa5
              m := store32 m (obj+132) (player i)
              m := store32 m (obj+104) flags.toBitVec
              m := store32 m 0x2b400 (if multiplayer then 1 else 0)
              m := store32 m 0x2af44 counter.toBitVec
              m := store32 m (fragAddress i) counter.toBitVec
              m := store32 m (player i+4) 0
              let s : X86Memory.State := ⟨fun r => if r=1 then 0 else if r=3 then obj else if r=4 then sp else 0x12345678,m⟩
              let some t := X86Routine.run program [0x2d2c0] 27 ⟨s,none,0x2a2e6⟩ | return false
              if observation obj i t != liveObservation i body world then return false
              if t.pc != 0x2d2c0 || t.core.regs 0 != player i || t.core.regs 4 != sp-4 then return false
              if load32 t.core.memory (sp-4) != 0x2a38c then return false
              if load32 t.core.memory 0x9000 != load32 m 0x9000 then return false
  return true

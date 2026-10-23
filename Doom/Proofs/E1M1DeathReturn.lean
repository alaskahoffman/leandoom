import Doom.Proofs.E1M1DeathTiming
import Doom.Proofs.OriginalDeathReturn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1DeathReturn
open Verification X86 X86Memory X86Control BlockSummary

/-- The original post-setter segment, through P_KillMobj's RET. -/
def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match DeathTiming.program pc with
  | some op => some op
  | none => DeathReturn.program pc

theorem contains_timing (pc : Nat) (h : DeathTiming.program pc≠none) :
    program pc=DeathTiming.program pc := by
  unfold program
  cases eq : DeathTiming.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_return (pc : Nat) (h : DeathReturn.program pc≠none) :
    program pc=DeathReturn.program pc := by
  have bound : 0x2a40d ≤ pc ∧ pc < 0x2a457 := by
    by_cases yes : 0x2a40d ≤ pc ∧ pc < 0x2a457
    · exact yes
    · simp [DeathReturn.program,DeathReturn.bytesProgram,yes] at h
  have h1 : ¬(0x2a3f1 ≤ pc ∧ pc < 0x2a40d) := by omega
  have h2 : ¬(0x24160 ≤ pc ∧ pc < 0x2417c) := by omega
  simp [program,DeathTiming.program,DeathTiming.bytesProgram,h1,h2]

/-- All new contracts are at the start of the timing call, not at an assumed
post-RNG state. E1M1FloorReturn separately transports the saved return address
from the actual floor CALL and kill prologue. -/
structure Inputs (s : X86Memory.State) (rng : DoomRandom) : Prop where
  timing : DeathTiming.Inputs s rng.play
  kind : load32 s.memory (s.regs 3+88)=0
  ret : load32 s.memory (s.regs 4+20)=0x2a6b1
  readsSafe : ∀ a, a ∈ [s.regs 3+88,s.regs 4,s.regs 4+4,s.regs 4+8,s.regs 4+12,
    s.regs 4+16,s.regs 4+20,(0x1271c#32)] → ∀ b, b ∈ DeathTiming.writes s → Apart a b

def result (s : X86Memory.State) (rng : DoomRandom) := DeathReturn.result (DeathTiming.result s rng.play).core

theorem timing_registers (s : X86Memory.State) (i : UInt8) :
    (DeathTiming.result s i).core.regs 3=s.regs 3 ∧
    (DeathTiming.result s i).core.regs 4=s.regs 4 := by
  simp [DeathTiming.result,DeathTiming.tailEnd,DeathTiming.rolled_regs,write]

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (rng : DoomRandom)
    (h : Inputs s rng) :
    X86Routine.run program [0x2a6b1] 26 ⟨s,f,0x2a3f1⟩=some (result s rng) ∧
    (result s rng).pc=0x2a6b1 ∧
    (result s rng).core.memory=(DeathTiming.result s rng.play).core.memory ∧
    (result s rng).core.regs 4=s.regs 4+24 ∧
    (result s rng).core.regs 0=0 ∧
    (result s rng).core.regs 2=s.regs 2 ∧
    (result s rng).core.regs 5=load32 s.memory (s.regs 4) ∧
    (result s rng).core.regs 7=load32 s.memory (s.regs 4+4) ∧
    (result s rng).core.regs 6=load32 s.memory (s.regs 4+8) ∧
    (result s rng).core.regs 1=load32 s.memory (s.regs 4+12) ∧
    (result s rng).core.regs 3=load32 s.memory (s.regs 4+16) ∧
    (result s rng).flags=some (compare32 0 1) ∧
    load32 (result s rng).core.memory (0x1271c#32)=load32 s.memory (0x1271c#32) ∧
    PlayerHeight.Frame s.memory (result s rng).core.memory (DeathTiming.writes s) := by
  let g := DeathTiming.result s rng.play
  have obj : g.core.regs 3=s.regs 3 := (timing_registers s rng.play).1
  have sp : g.core.regs 4=s.regs 4 := (timing_registers s rng.play).2
  have keep (a : Word) (ha : a ∈ [s.regs 3+88,s.regs 4,s.regs 4+4,s.regs 4+8,s.regs 4+12,
      s.regs 4+16,s.regs 4+20,(0x1271c#32)]) : load32 g.core.memory a=load32 s.memory a :=
    DeathTiming.memory_frame s rng.play a (h.readsSafe a ha)
  have kind : load32 g.core.memory (g.core.regs 3+88)=0 := by rw [obj,keep _ (by simp),h.kind]
  have ret : (DeathReturn.result g.core).pc=0x2a6b1 := by
    simp only [DeathReturn.result,sp]; rw [keep _ (by simp),h.ret]; rfl
  have tail := DeathReturn.original_execution g.core g.flags kind (by rw [ret]; omega)
  rw [ret] at tail
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path tail
  have p := p.transfer program [0x2a6b1] contains_return (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  have tail : X86Routine.run program [0x2a6b1] 11 g=some (result s rng) := by
    exact p.finish (fuel := 0) (by simp [X86Routine.run,ret]; rfl) 11 (by omega)
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path (DeathTiming.original_execution s f rng.play h.timing)
  have p := p.transfer program [0x2a6b1] contains_timing (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  refine ⟨p.finish tail 26 (by omega),ret,rfl,?_,?_,?_,?_,?_,?_,?_,?_,rfl,?_,?_⟩
  · change g.core.regs 4+24=s.regs 4+24
    rw [sp]
  · rfl
  · change g.core.regs 2=s.regs 2
    simp only [g,DeathTiming.result,DeathTiming.tailEnd,DeathTiming.rolled_regs]
    rfl
  · change load32 g.core.memory (g.core.regs 4)=load32 s.memory (s.regs 4)
    rw [sp,keep _ (by simp)]
  · change load32 g.core.memory (g.core.regs 4+4)=load32 s.memory (s.regs 4+4)
    rw [sp,keep _ (by simp)]
  · change load32 g.core.memory (g.core.regs 4+8)=load32 s.memory (s.regs 4+8)
    rw [sp,keep _ (by simp)]
  · change load32 g.core.memory (g.core.regs 4+12)=load32 s.memory (s.regs 4+12)
    rw [sp,keep _ (by simp)]
  · change load32 g.core.memory (g.core.regs 4+16)=load32 s.memory (s.regs 4+16)
    rw [sp,keep _ (by simp)]
  · exact keep _ (by simp)
  · exact DeathTiming.memory_frame s rng.play

/-- The concrete player state and RNG projection agree with the two production
helpers executed in order; item dispatch adds no event or second random draw. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (extreme : Bool)
    (body : Death.Body) (world : Death.World) (h : Inputs s world.rng)
    (kind : body.kind=0) (tics : body.tics=Int32.ofBitVec (E1M1DeathSetter.entry extreme).tics)
    (encoded : load32 s.memory (s.regs 3+96)=(E1M1DeathSetter.entry extreme).tics) :
    (X86Routine.run program [0x2a6b1] 26 ⟨s,f,0x2a3f1⟩).map
      (fun t => (load32 t.core.memory (s.regs 3+96),load32 t.core.memory (0x12720#32))) =
    some (let out := Death.randomizeTics body world
      let out := Death.dropItem out.1 out.2
      (out.1.tics.toBitVec,BitVec.ofNat 32 out.2.rng.play.toNat)) := by
  rw [(joined_execution s f world.rng h).1]
  have nodrop := DeathReturn.live_no_drop (Death.randomizeTics body world).1
    (Death.randomizeTics body world).2 (by simpa [Death.randomizeTics] using kind)
  simp only [nodrop,Option.map_some,result,DeathReturn.result]
  have prior := DeathTiming.live_correspondence s f body world extreme h.timing encoded tics
  rw [DeathTiming.original_execution s f world.rng.play h.timing] at prior
  exact prior

end Doom.Proofs.E1M1DeathReturn

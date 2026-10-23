import Doom.Proofs.OriginalKillBookkeeping
import Doom.Proofs.OriginalWeaponDrop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.KillWeaponDrop
open Verification X86 X86Memory X86Control BlockSummary

def program : X86Routine.Program := fun pc =>
  match KillBookkeeping.joined pc with
  | some op => some op
  | none => WeaponDrop.program pc

theorem contains_previous (pc : Nat) (h : KillBookkeeping.joined pc≠none) :
    program pc=KillBookkeeping.joined pc := by
  unfold program
  cases eq : KillBookkeeping.joined pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_drop (pc : Nat) (h : WeaponDrop.program pc≠none) :
    program pc=WeaponDrop.program pc := by
  have bound : 0x2d040 ≤ pc ∧ pc < 0x2d4cc := by
    by_cases yes : 0x2d040 ≤ pc ∧ pc < 0x2d4cc
    · exact yes
    · have b1 : ¬(0x2d2c0 ≤ pc ∧ pc < 0x2d2e3) := by omega
      have b2 : ¬(0x2d040 ≤ pc ∧ pc < 0x2d0af) := by omega
      have b3 : ¬(0x2d490 ≤ pc ∧ pc < 0x2d4cc) := by omega
      simp [WeaponDrop.program,WeaponDrop.bytesProgram,WeaponLower.bytesProgram,b1,b2,b3] at h
  have b0 : ¬(0x2a2e6 ≤ pc ∧ pc < 0x2a38c) := by omega
  have b1 : ¬(0x2a6a6 ≤ pc ∧ pc < 0x2a6b1) := by omega
  have b2 : ¬(0x2a2b0 ≤ pc ∧ pc < 0x2a2e6) := by omega
  have b3 : ¬(0x2a650 ≤ pc ∧ pc < 0x2a6a6) := by omega
  have b4 : ¬(0x1bb50 ≤ pc ∧ pc < 0x1bb66) := by omega
  have b5 : ¬(0x1bc41 ≤ pc ∧ pc < 0x1bc45) := by omega
  have b6 : ¬(0x2a616 ≤ pc ∧ pc < 0x2a650) := by omega
  have b7 : ¬(0x2a460 ≤ pc ∧ pc < 0x2a5d5) := by omega
  have b8 : ¬(0x2a5d5 ≤ pc ∧ pc < 0x2a616) := by omega
  simp [program,KillBookkeeping.joined,KillEntry.joined,ActorHealth.joined,PlayerHealth.joined,
    PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega]

theorem previous_active (pc : Nat) (h : KillBookkeeping.joined pc≠none) : pc ∉ [0x2a38c] := by
  simp only [List.mem_singleton]; intro eq; subst pc; exact h (by decide)
theorem drop_active (pc : Nat) (h : WeaponDrop.program pc≠none) : pc ∉ [0x2a38c] := by
  simp only [List.mem_singleton]; intro eq; subst pc; exact h (by decide)

/-- Initial-memory view of the known call-entry registers; it is not an
assumed intermediate execution state. -/
def dropView (s : X86Memory.State) (i : Fin 4) : X86Memory.State :=
  ⟨write (write s.regs 0 (KillBookkeeping.player i)) 4 (s.regs 4-56),s.memory⟩
def priorWrites (s : X86Memory.State) (i : Fin 4) :=
  KillBookkeeping.priorWrites s ++ KillBookkeeping.writes (KillBookkeeping.entryView s) i

def retained (s : X86Memory.State) (i : Fin 4) :=
  KillBookkeeping.retained s ++ [s.regs 0+104,0x2af44,KillBookkeeping.fragAddress i,KillBookkeeping.player i+4]

structure Inputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (i : Fin 4) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed) : Prop where
  prior : KillBookkeeping.JoinedInputs s v d baby i body world
  ready : load32 s.memory (WeaponDrop.location (dropView s i) w 1)=BitVec.ofNat 32 w.val
  height : load32 s.memory (WeaponDrop.location (dropView s i) w 2)=y.raw.toBitVec
  down : load32 s.memory (WeaponDrop.location (dropView s i) w 5)=WeaponDrop.down w
  tics : load32 s.memory (WeaponDrop.location (dropView s i) w 6)=1
  misc : load32 s.memory (WeaponDrop.location (dropView s i) w 7)=0
  callback : load32 s.memory (WeaponDrop.location (dropView s i) w 8)=0x2d490
  next : load32 s.memory (WeaponDrop.location (dropView s i) w 9)=WeaponDrop.down w
  separate : ∀ a b : Fin 18, a≠b → Apart (WeaponDrop.location (dropView s i) w a) (WeaponDrop.location (dropView s i) w b)
  readsSafe : ∀ n : Fin 18, n ∈ [1,2,5,6,7,8,9] → ∀ b, b ∈ priorWrites s i →
    Apart (WeaponDrop.location (dropView s i) w n) b
  retainedSafe : ∀ a, a ∈ retained s i → ∀ b, b ∈ WeaponDrop.writes (dropView s i) → Apart a b

/-- Continuous lethal floor damage, through the weapon callback and back
into P_KillMobj. Earlier damage/death observations survive the callback. -/
def stackWrites (s : X86Memory.State) (i : Fin 4) := KillBookkeeping.stackWrites s i ++ WeaponDrop.writes (dropView s i)
def returnWrites (s : X86Memory.State) (i : Fin 4) := KillBookkeeping.returnWrites s i ++ WeaponDrop.writes (dropView s i)

theorem joined_execution_detailed_tracked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (i : Fin 4) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed)
    (h : Inputs s v d baby i body world w y)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t,
      DeathStack.Saved s pc t.core.memory (stackWrites s i) (returnWrites s i) ∧ X86Routine.run program [0x2a38c] 213 ⟨s,f,pc⟩=some t ∧
      KillBookkeeping.joinedObservation s i t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false baby rng) i body world ∧
      load32 t.core.memory (KillBookkeeping.player i+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player i+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player i+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=0x2a38c ∧ t.core.regs 4=s.regs 4-52 ∧
      t.core.regs 3=s.regs 0 ∧
      PlayerHeight.Frame s.memory t.core.memory (priorWrites s i ++ WeaponDrop.writes (dropView s i)) := by
  obtain ⟨g,gsaved,grun,gobs,gpc,gplayer,gsp,gret,gobj,gframe⟩ :=
    KillBookkeeping.joined_execution_detailed_tracked s f pc site v d baby rng i body world h.prior dead
  have loc (n : Fin 18) : WeaponDrop.location g.core w n=WeaponDrop.location (dropView s i) w n := by
    simp [WeaponDrop.location,WeaponDrop.psp,dropView,write,gplayer,gsp]
  have keep (n : Fin 18) (hn : n ∈ [1,2,5,6,7,8,9]) :
      load32 g.core.memory (WeaponDrop.location g.core w n)=load32 s.memory (WeaponDrop.location (dropView s i) w n) := by
    rw [loc]
    exact gframe _ (h.readsSafe n hn)
  have liveDead := (KillBookkeeping.live_fields (Death.corpse body) world i h.prior.book.environmental
    (by simpa [Death.corpse,h.prior.player] using h.prior.book.victim)).2.2.2.1
  have deadWord : load32 g.core.memory (KillBookkeeping.player i+4)=1 := by
    have eq := congrArg (fun x => x.2.2.2.2.2) gobs
    simp only [KillBookkeeping.joinedObservation,KillBookkeeping.joinedLiveObservation,
      KillBookkeeping.observation,KillBookkeeping.liveObservation,liveDead,ite_true] at eq
    exact eq
  have ins : WeaponDrop.Inputs g.core w y := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [gplayer] using deadWord
    · exact (keep 1 (by simp)).trans h.ready
    · exact (keep 2 (by simp)).trans h.height
    · exact (keep 5 (by simp)).trans h.down
    · exact (keep 6 (by simp)).trans h.tics
    · exact (keep 7 (by simp)).trans h.misc
    · exact (keep 8 (by simp)).trans h.callback
    · exact (keep 9 (by simp)).trans h.next
    · simpa [gsp] using gret
    · intro a b ne; rw [loc,loc]; exact h.separate a b ne
  obtain ⟨t,trun,tstate,ttics,ty,tpc,tregs,tframe⟩ := WeaponDrop.live_correspondence g.core g.flags w y ins
  have wr : WeaponDrop.writes g.core=WeaponDrop.writes (dropView s i) := by
    simp [WeaponDrop.writes,WeaponDrop.psp,dropView,write,gplayer,gsp]
  have stable (a : Word) (ha : a ∈ retained s i) : load32 t.core.memory a=load32 g.core.memory a := by
    apply tframe
    intro b hb; rw [wr] at hb; exact h.retainedSafe a ha b hb
  have obs : KillBookkeeping.joinedObservation s i t=KillBookkeeping.joinedObservation s i g := by
    unfold KillBookkeeping.joinedObservation KillEntry.damageFields KillBookkeeping.observation
    dsimp only
    repeat rw [stable _ (by simp [retained,KillBookkeeping.retained,KillEntry.retained,ActorHealth.fields])]
  obtain ⟨n,hn,first,_⟩ := X86Routine.run_path grun
  have first := first.transfer program [0x2a38c] contains_previous previous_active
  obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path trun
  have tail := tail.transfer program [0x2a38c] contains_drop drop_active
  have tailRun : X86Routine.run program [0x2a38c] 55 g=some t := by
    have geq : g=⟨g.core,g.flags,0x2d2c0⟩ := by rw [← gpc]
    rw [geq]
    exact tail.finish (fuel := 0) (by simp [X86Routine.run,tpc]) 55 (by omega)
  have tracked : DeathStack.Saved s pc t.core.memory (stackWrites s i) (returnWrites s i) := by
    rw [wr] at tframe
    exact gsaved.then_frame _ _ _ _ _ _ _ tframe
  refine ⟨t,tracked,first.finish tailRun 213 (by omega),obs.trans gobs,?_,?_,?_,tpc,?_,?_,?_⟩
  · simpa [WeaponDrop.psp,gplayer] using tstate
  · simpa [WeaponDrop.psp,gplayer,BitVec.add_assoc] using ttics
  · simpa [WeaponDrop.psp,gplayer,BitVec.add_assoc] using ty
  · rw [tregs]; simp [write,gsp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · rw [tregs]; simp [write,gobj]
  · intro a safe
    rw [tframe a (fun b hb => safe b (List.mem_append.mpr (Or.inr (by simpa [wr] using hb))))]
    exact gframe a (fun b hb => safe b (List.mem_append.mpr (Or.inl hb)))

theorem joined_execution_detailed (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (i : Fin 4) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed)
    (h : Inputs s v d baby i body world w y)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t, X86Routine.run program [0x2a38c] 213 ⟨s,f,pc⟩=some t ∧
      KillBookkeeping.joinedObservation s i t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false baby rng) i body world ∧
      load32 t.core.memory (KillBookkeeping.player i+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player i+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player i+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=0x2a38c ∧ t.core.regs 4=s.regs 4-52 ∧
      t.core.regs 3=s.regs 0 ∧
      PlayerHeight.Frame s.memory t.core.memory (priorWrites s i ++ WeaponDrop.writes (dropView s i)) := by
  obtain ⟨t,_,rest⟩ :=
    joined_execution_detailed_tracked s f pc site v d baby rng i body world w y h dead
  exact ⟨t,rest⟩

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (i : Fin 4) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed)
    (h : Inputs s v d baby i body world w y)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t, X86Routine.run program [0x2a38c] 213 ⟨s,f,pc⟩=some t ∧
      KillBookkeeping.joinedObservation s i t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false baby rng) i body world ∧
      load32 t.core.memory (KillBookkeeping.player i+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player i+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player i+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=0x2a38c ∧ t.core.regs 4=s.regs 4-52 ∧
      PlayerHeight.Frame s.memory t.core.memory (priorWrites s i ++ WeaponDrop.writes (dropView s i)) := by
  obtain ⟨t,run,obs,state,tics,height,pc,sp,_,frame⟩ :=
    joined_execution_detailed s f pc site v d baby rng i body world w y h dead
  exact ⟨t,run,obs,state,tics,height,pc,sp,frame⟩

end Doom.Proofs.KillWeaponDrop

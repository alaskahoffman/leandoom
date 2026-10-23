import Doom.Proofs.E1M1FloorReturn
import Doom.Proofs.OriginalFloorReturn
import Doom.Verification.X86CodeBridge
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1SectorReturn
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1FloorReturn.program pc with
  | some op => some op
  | none => FloorReturn.program pc

theorem contains_damage (pc : Nat) (h : E1M1FloorReturn.program pc≠none) :
    program pc=E1M1FloorReturn.program pc := by
  unfold program
  cases eq : E1M1FloorReturn.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_floor (pc : Nat) (h : FloorReturn.program pc≠none) :
    program pc=FloorReturn.program pc := by
  have bounds : (0x2fb7b ≤ pc ∧ pc < 0x2fb80) ∨ (0x2fba5 ≤ pc ∧ pc < 0x2fbaa) ∨
      (0x2fbd7 ≤ pc ∧ pc < 0x2fbdc) ∨ (0x2fc39 ≤ pc ∧ pc < 0x2fc3e) := by
    by_cases yes : (0x2fb7b ≤ pc ∧ pc < 0x2fb80) ∨ (0x2fba5 ≤ pc ∧ pc < 0x2fbaa) ∨
      (0x2fbd7 ≤ pc ∧ pc < 0x2fbdc) ∨ (0x2fc39 ≤ pc ∧ pc < 0x2fc3e)
    · exact yes
    have a : ¬(0x2fb7b ≤ pc ∧ pc < 0x2fb80) := by omega
    have b : ¬(0x2fba5 ≤ pc ∧ pc < 0x2fbaa) := by omega
    have c : ¬(0x2fbd7 ≤ pc ∧ pc < 0x2fbdc) := by omega
    have d : ¬(0x2fc39 ≤ pc ∧ pc < 0x2fc3e) := by omega
    simp [FloorReturn.program,FloorReturn.bytesProgram,a,b,c,d] at h
  have cases : pc=0x2fb7b ∨ pc=0x2fb7c ∨ pc=0x2fb7d ∨ pc=0x2fb7e ∨ pc=0x2fb7f ∨ pc=0x2fba5 ∨ pc=0x2fba6 ∨ pc=0x2fba7 ∨ pc=0x2fba8 ∨ pc=0x2fba9 ∨ pc=0x2fbd7 ∨ pc=0x2fbd8 ∨ pc=0x2fbd9 ∨ pc=0x2fbda ∨ pc=0x2fbdb ∨ pc=0x2fc39 ∨ pc=0x2fc3a ∨ pc=0x2fc3b ∨ pc=0x2fc3c ∨ pc=0x2fc3d := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- A continuous lethal-floor execution through the outer sector RET. The
saved outer frame is an explicit entry contract; `FloorReturn.caller_saved`
derives it from the earlier actual caller. No mid-execution state is reset. -/
theorem joined_execution (caller s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (map : sim.map.name="E1M1") (skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32)))
    (timing : E1M1DeathTiming.Inputs s sim.rng) (ins : E1M1FloorReturn.Inputs s)
    (saved : FloorReturn.Saved caller s)
    (safe : ∀ a, a ∈ SectorCaller.slots caller → ∀ b, b ∈ E1M1FloorReturn.allWrites s → Apart a b) :
    ∃ (extreme : Bool) (t : X86Control.State),
      E1M1DeathSetter.stateId extreme=Death.deathState
        (PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo ∧
      X86Routine.run program [0x333e5] 300 ⟨s,f,pc⟩=some t ∧
      t.pc=0x333e5 ∧ t.core.regs 4=caller.regs 4 ∧
      t.core.regs 6=caller.regs 6 ∧ t.core.regs 2=caller.regs 2 ∧
      t.core.regs 1=caller.regs 1 ∧ t.core.regs 3=caller.regs 3 ∧
      t.core.regs 5=s.regs 5 ∧ t.core.regs 7=s.regs 7 ∧
      DeathSetter.observeFields t.core.memory (s.regs 0)=
        ((E1M1DeathSetter.entry extreme).pointer,DeathTiming.playerTicks extreme sim.rng.play,
         (E1M1DeathSetter.entry extreme).sprite,(E1M1DeathSetter.entry extreme).frame) ∧
      load32 t.core.memory (0x12720#32)=FloorDamage.nextIndex sim.rng.play ∧
      load32 t.core.memory (0x1271c#32)=BitVec.ofNat 32 sim.rng.misc.toNat ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false sim.rng) 0 body sim.deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      PlayerHeight.Frame s.memory t.core.memory (E1M1FloorReturn.allWrites s) := by
  obtain ⟨extreme,k,u,choice,_,_,_,run,upc,usp,bp,di,_,_,fields,index,misc,off,obs,weapon,tics,height,frame⟩ :=
    E1M1FloorReturn.joined_execution s f pc site v d sim map skill body info w y h dead stackSafe timing ins
  have saved := saved.then_frame usp _ frame safe
  let t := FloorReturn.result u.core u.flags
  obtain ⟨tpc,tsp,si,dx,cx,bx,ax,bp',di',mem,flags⟩ := FloorReturn.restores caller u.core u.flags saved
  have returnWord : load32 u.core.memory (u.core.regs 4+16)=0x333e5 := by
    have ret := congrArg Prod.fst (SectorCaller.saved_words caller)
    rw [saved.sp,show caller.regs 4-20+16=caller.regs 4-4 by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]]
    rw [saved.words _ (by simp [SectorCaller.slots])]
    exact ret
  have exitSite : pc+5 ∈ FloorReturn.sites := by
    simp only [PlayerDamageEntry.sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at site
    rcases site with rfl|rfl|rfl <;> decide
  have tail := FloorReturn.original_execution u.core u.flags (pc+5) exitSite returnWord
  rw [←upc] at tail
  obtain ⟨j,hj,q,_⟩ := X86Routine.run_path tail
  have q := q.transfer program [0x333e5] contains_floor (by
    intro addr hp; simp only [List.mem_singleton]; intro eq; subst addr; exact hp (by decide))
  have tail : X86Routine.run program [0x333e5] 5 u=some t :=
    q.finish (fuel := 0) (by simp [X86Routine.run,t,tpc]) 5 (by omega)
  obtain ⟨n,hn,p,_⟩ := X86Routine.run_path run
  have p := p.transfer program [0x333e5] contains_damage (by
    intro addr hp; simp only [List.mem_singleton]; intro eq; subst addr; exact hp (by decide))
  exact ⟨extreme,t,choice,p.finish tail 300 (by omega),tpc,tsp,si,dx,cx,bx,
    bp'.trans bp,di'.trans di,fields,index,misc,off,obs,weapon,tics,height,frame⟩

end Doom.Proofs.E1M1SectorReturn

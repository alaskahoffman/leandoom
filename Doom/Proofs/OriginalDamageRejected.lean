import Doom.Proofs.OriginalDamageReturn

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.DamageRejected
open Verification X86 X86Memory X86Control BlockSummary

/-- Rejection enters the common epilogue without resetting reaction time. -/
def freed (s : X86Memory.State) := put s 4 (s.regs 4+(12#32))
def result (s : X86Memory.State) := DamageReturn.restored (freed s) none

theorem execution (s : X86Memory.State) (f : Option Flags)
    (outside : 0x2a74e ≤ (result s).pc) :
    X86Routine.run DamageReturn.listed [(result s).pc] 5 ⟨s,f,0x2a747⟩ = some (result s) := by
  have start : X86Routine.Prefix DamageReturn.listed [(result s).pc] 1
      ⟨s,f,0x2a747⟩ ⟨freed s,none,0x2a74a⟩ := by
    apply X86Routine.Prefix.step (by simp only [List.mem_singleton]; omega) (by rfl) (by rfl)
    exact X86Routine.Prefix.nil _
  exact start.finish (DamageReturn.epilogue (freed s) none outside) 5 (by decide)

theorem original_execution (s : X86Memory.State) (f : Option Flags)
    (outside : 0x2a74e ≤ (result s).pc) :
    X86Routine.run DamageReturn.program [(result s).pc] 5 ⟨s,f,0x2a747⟩ = some (result s) := by
  rw [X86Routine.run_sound DamageReturn.program DamageReturn.listed DamageReturn.decoded _ _ _
    (by rw [execution s f outside]; simp)]
  exact execution s f outside

theorem memory_unchanged (s : X86Memory.State) : (result s).core.memory = s.memory := rfl

/-- Derive the machine's rejection decision from the actual live function. -/
theorem rejected_live (v : PlayerDamage.State) (d : Int32) (baby : Bool) (rng : DoomRandom)
    (skull : v.skullFly=false) (ordinary : v.sectorSpecial ≠ 11)
    (rejected : (PlayerDamage.apply v d none false baby rng).applied=false) :
    PlayerDamageEntry.accepted v d baby = false ∧
    PlayerDamage.apply v d none false baby rng = ⟨v,rng,false,false,false⟩ := by
  have entry := PlayerDamageEntry.live_entry v d baby false rng skull ordinary
  by_cases accepted : PlayerDamageEntry.accepted v d baby = true
  · rw [entry] at rejected
    simp only [accepted,if_true] at rejected
    unfold PlayerDamage.finish at rejected
    simp only [Id.run,pure,bind] at rejected
    split at rejected <;> simp_all
  · have no : PlayerDamageEntry.accepted v d baby = false := by simpa using accepted
    exact ⟨no,by simpa [no] using entry⟩

/-- Guards do not write memory. The only rejected-call writes are the actual
CALL/prologue saves, including both null source slots. -/
theorem rejected_prefix (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (h : PlayerDamageEntry.Inputs s v d baby) (no : PlayerDamageEntry.accepted v d baby=false) :
    ∃ g, X86Routine.run PlayerDamageEntry.program [0x2a616,0x2a747] 35 ⟨s,f,pc⟩ = some g ∧
      g.pc=0x2a747 ∧ g.core.regs 4=s.regs 4-(28#32) ∧ g.core.memory=PlayerDamageEntry.saved s pc := by
  have guards := PlayerDamageEntry.guards (PlayerDamageEntry.entered s pc) none v d baby
    (PlayerDamageEntry.transport s pc v d baby h)
  cases run : X86Routine.run PlayerDamageEntry.guardListed [0x2a5d5,0x2a747] 26
      ⟨PlayerDamageEntry.entered s pc,none,0x2a471⟩ with
  | none => simp [run] at guards
  | some g =>
    obtain ⟨n,hn,path,_⟩ := X86Routine.run_path run
    have path := path.transfer PlayerDamageEntry.program [0x2a616,0x2a747]
      PlayerDamageEntry.guards_decoded PlayerDamageEntry.guards_active
    simp only [run,Option.map_some,Option.some.injEq,PlayerDamageEntry.guardObservation,
      PlayerDamageEntry.expected,no,Bool.false_eq_true,if_false,Prod.mk.injEq] at guards
    obtain ⟨gp,_,_,_,sp,mem⟩ := guards
    have rest : X86Routine.run PlayerDamageEntry.program [0x2a616,0x2a747] 26
        ⟨PlayerDamageEntry.entered s pc,none,0x2a471⟩ = some g :=
      path.finish (fuel := 0) (by simp [X86Routine.run,gp]) 26 (by omega)
    refine ⟨g,(PlayerDamageEntry.prologue s f pc site).finish rest 35 (by decide),gp,?_,mem⟩
    simpa [PlayerDamageEntry.entered,write] using sp

theorem contains_entry (pc : Nat) (h : PlayerDamageEntry.program pc ≠ none) :
    DamageReturn.joined pc = PlayerDamageEntry.program pc := by
  have a := PlayerHealth.contains_entry pc h
  have b := ActorHealth.contains_health pc (by rw [a]; exact h)
  have c := PlayerPain.contains_actor pc (by rw [b,a]; exact h)
  have d := PainHandoff.contains_pain pc (by rw [c,b,a]; exact h)
  have e := PainSetter.contains_handoff pc (by rw [d,c,b,a]; exact h)
  have f := DamageReturn.contains_previous pc (by rw [e,d,c,b,a]; exact h)
  exact f.trans (e.trans (d.trans (c.trans (b.trans a))))

theorem entry_active (pc : Nat) (h : PlayerDamageEntry.program pc ≠ none) : pc ∉ DamageReturn.exits := by
  intro hm
  simp only [DamageReturn.exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> contradiction

/-- Rejected calls return with precisely the prologue's saved memory. This
component needs no pain-state, RNG-table or tactile-device assumptions. -/
theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (h : PlayerDamageEntry.Inputs s v d baby) (no : PlayerDamageEntry.accepted v d baby=false) :
    ∃ t, X86Routine.run DamageReturn.joined DamageReturn.exits 40 ⟨s,f,pc⟩ = some t ∧
      t.pc=pc+5 ∧ t.core.regs 4=s.regs 4 ∧ t.core.regs 5=s.regs 5 ∧
      t.core.regs 6=s.regs 6 ∧ t.core.regs 7=s.regs 7 ∧
      t.core.memory=PlayerDamageEntry.saved s pc := by
  obtain ⟨g,grun,gp,gsp,gm⟩ := rejected_prefix s f pc site v d baby h no
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path grun
  have path := path.transfer DamageReturn.joined DamageReturn.exits contains_entry entry_active
  have slots := DamageReturn.saved_slots s pc
  have a12 : g.core.regs 4+(12#32)=s.regs 4-(16#32) := by rw [gsp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a16 : g.core.regs 4+(16#32)=s.regs 4-(12#32) := by rw [gsp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a20 : g.core.regs 4+(20#32)=s.regs 4-(8#32) := by rw [gsp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a24 : g.core.regs 4+(24#32)=s.regs 4-(4#32) := by rw [gsp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have retpc : (result g.core).pc=pc+5 := by
    have view : (result g.core).pc=(load32 g.core.memory (g.core.regs 4+(24#32))).toNat := by
      simp [result,DamageReturn.restored,freed,put,write,BitVec.add_assoc]
    rw [view,a24,gm,slots.1]
    simp only [PlayerDamageEntry.sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at site
    rcases site with rfl | rfl | rfl <;> decide
  have outside : 0x2a74e ≤ (result g.core).pc := by
    rw [retpc]; simp only [PlayerDamageEntry.sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at site; omega
  have tailrun := original_execution g.core g.flags outside
  rw [← gp] at tailrun
  obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path tailrun
  have tail := tail.transfer DamageReturn.joined DamageReturn.exits DamageReturn.contains_tail DamageReturn.tail_active
  have done : (result g.core).pc ∈ DamageReturn.exits := by
    rw [retpc]; simp only [PlayerDamageEntry.sites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at site
    rcases site with rfl | rfl | rfl <;> decide
  have rest : X86Routine.run DamageReturn.joined DamageReturn.exits 5 g = some (result g.core) :=
    tail.finish (fuel := 0) (by simp [X86Routine.run,done]) 5 (by omega)
  refine ⟨result g.core,path.finish rest 40 (by omega),retpc,?_,?_,?_,?_,gm⟩
  · simp [result,DamageReturn.restored,freed,put,write,gsp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · simpa [result,DamageReturn.restored,freed,put,write,a12,gm] using slots.2.2.2.1
  · simpa [result,DamageReturn.restored,freed,put,write,BitVec.add_assoc,a20,gm] using slots.2.1
  · simpa [result,DamageReturn.restored,freed,put,write,BitVec.add_assoc,a16,gm] using slots.2.2.1

/-- Fields observed after a returned call, plus target and threshold metadata. -/
def reads (s : X86Memory.State) := DamageReturn.retained s ++ [s.regs 0+(124#32)]
structure Inputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool) (i : UInt8)
    extends toReturn : DamageReturn.JoinedInputs s v d baby i where
  rejectedSafe : ∀ a, a ∈ reads s → ∀ b, b ∈ PlayerDamageEntry.slots s → Apart a b

abbrev observation := DamageReturn.observation

/-- Rejected damage preserves the previous attacker pointer. Accepted damage
with a null source writes zero, as in the existing surviving-call relation. -/
def liveFields (s : X86Memory.State) (out : PlayerDamage.Result) :=
  ((out.state.armor.toBitVec,out.state.armorType.toBitVec,out.state.playerHealth.toBitVec,
    out.state.damageCount.toBitVec,
    if out.applied then (0#32) else load32 s.memory (PlayerDamageEntry.inputPlayer s+(228#32))),
    out.state.health.toBitVec,BitVec.ofNat 32 out.rng.play.toNat,
    load32 s.memory (s.regs 0+(104#32)) ||| (if out.pain then (64#32) else (0#32)),
    if out.pain then PainSetter.painFields else PainSetter.observeFields s.memory (s.regs 0))
def liveObservation (s : X86Memory.State) (out : PlayerDamage.Result) :=
  (liveFields s out,(out.reactionTime (Int32.ofBitVec (load32 s.memory (s.regs 0+(124#32))))).toBitVec)

theorem accepted_observation (s : X86Memory.State) (out : PlayerDamage.Result) (yes : out.applied=true) :
    liveObservation s out = DamageReturn.liveObservation s out := by
  simp [liveObservation,liveFields,DamageReturn.liveObservation,DamageReturn.liveFields,yes]

theorem initial_observation (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32)
    (baby : Bool) (rng : DoomRandom) (h : Inputs s v d baby rng.play)
    (no : (PlayerDamage.apply v d none false baby rng).applied=false) :
    (DamageReturn.memoryFields s s.memory,load32 s.memory (s.regs 0+(124#32))) =
      liveObservation s (PlayerDamage.apply v d none false baby rng) := by
  rw [(rejected_live v d baby rng h.liveSkull h.liveOrdinary no).2]
  simp [DamageReturn.memoryFields,liveObservation,liveFields,PlayerDamage.Result.reactionTime,
    h.armor,h.armorType,h.playerHealth,h.damageCount,h.health,h.index]

/-- All nonlethal results now return through the same original CALL boundary.
Rejected calls have only the prologue footprint; accepted surviving calls use
the earlier damage/pain/reaction proof. -/
theorem nonlethal_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (h : Inputs s v d baby rng.play)
    (alive : (PlayerDamage.apply v d none false baby rng).killed=false) :
    ∃ t, X86Routine.run DamageReturn.joined DamageReturn.exits 166 ⟨s,f,pc⟩ = some t ∧
      observation s t = liveObservation s (PlayerDamage.apply v d none false baby rng) ∧
      t.pc=pc+5 ∧ t.core.regs 4=s.regs 4 ∧ t.core.regs 5=s.regs 5 ∧
      t.core.regs 6=s.regs 6 ∧ t.core.regs 7=s.regs 7 ∧
      PlayerHeight.Frame s.memory t.core.memory
        (if (PlayerDamage.apply v d none false baby rng).applied then DamageReturn.joinedWrites s else PlayerDamageEntry.slots s) := by
  by_cases yes : (PlayerDamage.apply v d none false baby rng).applied=true
  · obtain ⟨_,t,_,_,run,ret,sp,bp,si,di,_,_,frame⟩ :=
      DamageReturn.joined_execution s f pc site v d baby rng h.toReturn yes alive
    have obs := DamageReturn.live_correspondence s f pc site v d baby rng h.toReturn yes alive
    rw [run,Option.map_some,Option.some.injEq] at obs
    refine ⟨t,run,?_,ret,sp,bp,si,di,?_⟩
    · rw [accepted_observation s _ yes]; exact obs
    · simpa [yes] using frame
  · have no : (PlayerDamage.apply v d none false baby rng).applied=false := by simpa using yes
    have reject := (rejected_live v d baby rng h.liveSkull h.liveOrdinary no).1
    obtain ⟨t,run,ret,sp,bp,si,di,mem⟩ := joined_execution s f pc site v d baby h.toInputs reject
    obtain ⟨n,hn,path,done⟩ := X86Routine.run_path run
    have run : X86Routine.run DamageReturn.joined DamageReturn.exits 166 ⟨s,f,pc⟩ = some t :=
      path.finish (fuel := 0) (by simp [X86Routine.run,done]) 166 (by omega)
    have keep (a : Word) (ha : a ∈ reads s) : load32 t.core.memory a = load32 s.memory a := by
      rw [mem]; exact PlayerDamageEntry.saved_frame s pc a (h.rejectedSafe a ha)
    refine ⟨t,run,?_,ret,sp,bp,si,di,?_⟩
    · rw [← initial_observation s v d baby rng h no]
      unfold observation DamageReturn.observation DamageReturn.memoryFields PainSetter.observeFields
      dsimp only
      repeat rw [keep _ (by simp [reads,DamageReturn.retained,PainSetter.retained,PainHandoff.retained,ActorHealth.fields,PainSetter.fields])]
    · simp only [no,Bool.false_eq_true,if_false]
      rw [mem]; exact PlayerDamageEntry.saved_frame s pc

theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (h : Inputs s v d baby rng.play)
    (alive : (PlayerDamage.apply v d none false baby rng).killed=false) :
    (X86Routine.run DamageReturn.joined DamageReturn.exits 166 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation s (PlayerDamage.apply v d none false baby rng)) := by
  obtain ⟨t,run,obs,_⟩ := nonlethal_execution s f pc site v d baby rng h alive
  simp [run,obs]

end Doom.Proofs.DamageRejected

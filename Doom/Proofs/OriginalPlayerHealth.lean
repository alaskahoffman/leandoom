import Doom.Proofs.OriginalPlayerDamageEntry

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.PlayerHealth
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0x8b,0x5d,0x20,0x29,0xfb,0x89,0x5d,0x20,0x85,0xdb,0x7d,0x7,0xc7,0x45,0x20,0x0,0x0,0x0,0x0,0x8b,0x44,0x24,0x4,0x89,0x85,0xe4,0x0,0x0,0x0,0x8b,0x85,0xdc,0x0,0x0,0x0,0x1,0xf8,0x89,0x85,0xdc,0x0,0x0,0x0,0x83,0xf8,0x64,0x7e,0xa,0xc7,0x85,0xdc,0x0,0x0,0x0,0x64,0x0,0x0,0x0]
def program (pc : Nat) := if 0x2a616 ≤ pc ∧ pc < 0x2a650 then X86Routine.decodeAt code (pc-0x2a616) else none

def listed : X86Routine.Program
  | 0x2a616 => some (.control (.block (.legacy (.load 3 5 32))),3)
  | 0x2a619 => some (.control (.block (.arithmetic (.sub 3 7))),2)
  | 0x2a61b => some (.control (.block (.store ⟨some 5,none,0,32⟩ 3)),3)
  | 0x2a61e => some (.control (.testWord 3 3),2)
  | 0x2a620 => some (.jumpSigned 0 7,2)
  | 0x2a622 => some (.storeImmediate ⟨some 5,none,0,32⟩ 0,7)
  | 0x2a629 => some (.control (.block (.load 0 ⟨some 4,none,0,4⟩)),4)
  | 0x2a62d => some (.control (.block (.store ⟨some 5,none,0,228⟩ 0)),6)
  | 0x2a633 => some (.control (.block (.load 0 ⟨some 5,none,0,220⟩)),6)
  | 0x2a639 => some (.control (.block (.arithmetic (.add 0 7))),2)
  | 0x2a63b => some (.control (.block (.store ⟨some 5,none,0,220⟩ 0)),6)
  | 0x2a641 => some (.compareRegister 0 100,3)
  | 0x2a644 => some (.jumpSigned 1 10,2)
  | 0x2a646 => some (.storeImmediate ⟨some 5,none,0,220⟩ 100,10)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

@[simp] theorem step_0x2a616 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a616⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 5 32)))) ⟨s,f,0x2a619⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a619 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a619⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.sub 3 7)))) ⟨s,f,0x2a61b⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a61b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a61b⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 5,none,0,32⟩ 3))) ⟨s,f,0x2a61e⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a61e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a61e⟩ =
      (X86Routine.execute (.control (.testWord 3 3)) ⟨s,f,0x2a620⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a620 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a620⟩ =
      (X86Routine.execute (.jumpSigned 0 7) ⟨s,f,0x2a622⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a622 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a622⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 5,none,0,32⟩ 0) ⟨s,f,0x2a629⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a629 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a629⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨some 4,none,0,4⟩))) ⟨s,f,0x2a62d⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a62d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a62d⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 5,none,0,228⟩ 0))) ⟨s,f,0x2a633⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a633 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a633⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨some 5,none,0,220⟩))) ⟨s,f,0x2a639⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a639 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a639⟩ =
      (X86Routine.execute (.control (.block (.arithmetic (.add 0 7)))) ⟨s,f,0x2a63b⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a63b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a63b⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 5,none,0,220⟩ 0))) ⟨s,f,0x2a641⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a641 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a641⟩ =
      (X86Routine.execute (.compareRegister 0 100) ⟨s,f,0x2a644⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a644 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a644⟩ =
      (X86Routine.execute (.jumpSigned 1 10) ⟨s,f,0x2a646⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem step_0x2a646 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] (n+1) ⟨s,f,0x2a646⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 5,none,0,220⟩ 100) ⟨s,f,0x2a650⟩).bind (X86Routine.run listed [0x2a650] n) := by rfl

@[simp] theorem stop (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2a650] n ⟨s,f,0x2a650⟩ = some ⟨s,f,0x2a650⟩ := by
  cases n <;> rfl

def pointer (s : X86Memory.State) := s.regs 5
def delta (s : X86Memory.State) := load32 s.memory (pointer s+(32#32)) - s.regs 7
def health (s : X86Memory.State) := if 0 ≤ (delta s).toInt then delta s else (0#32)
def healthMemory (s : X86Memory.State) :=
  let m := store32 s.memory (pointer s+(32#32)) (delta s)
  if 0 ≤ (delta s).toInt then m else store32 m (pointer s+(32#32)) (0#32)
def source (s : X86Memory.State) := load32 (healthMemory s) (s.regs 4+(4#32))
def attackerMemory (s : X86Memory.State) := store32 (healthMemory s) (pointer s+(228#32)) (source s)
def countSum (s : X86Memory.State) := load32 (attackerMemory s) (pointer s+(220#32)) + s.regs 7
def count (s : X86Memory.State) := if (countSum s).toInt ≤ 100 then countSum s else (100#32)
def resultMemory (s : X86Memory.State) :=
  let m := store32 (attackerMemory s) (pointer s+(220#32)) (countSum s)
  if (countSum s).toInt ≤ 100 then m else store32 m (pointer s+(220#32)) (100#32)

theorem logical_ge (v : Word) : (logical32 v).sign = (logical32 v).overflow ↔ 0 ≤ v.toInt := by
  have h : logical32 v = compare32 v 0 := by simp [logical32,compare32,BitVec.ult_eq_decide]
  rw [h,PlayerHeight.cmp_ge_prop]; rfl

theorem execution (s : X86Memory.State) (f : Option Flags) :
    (X86Routine.run listed [0x2a650] 14 ⟨s,f,0x2a616⟩).map
      (fun t => (t.core.memory,t.core.regs 5,t.core.regs 4,t.core.regs 6,t.core.regs 7,t.pc)) =
      some (resultMemory s,s.regs 5,s.regs 4,s.regs 6,s.regs 7,0x2a650) := by
  by_cases hp : 0 ≤ (delta s).toInt <;> by_cases hc : (countSum s).toInt ≤ 100
  all_goals
    have hp' := hp
    have hc' := hc
    simp only [delta,pointer] at hp'
    simp only [countSum,attackerMemory,source,healthMemory,delta,pointer,hp',if_true,if_false] at hc'
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      put,write,blockPreservesFlags,X86Block.Address.eval,logical_ge,cmp32_signed_le,
      hp',hc',← Int.not_le,resultMemory,countSum,attackerMemory,source,healthMemory,delta,pointer,hp,
      -BitVec.toInt_sub,-BitVec.toInt_add]

/-- Same-object fields remain disjoint even when the base is unaligned or wraps. -/
theorem offsets_apart (p : Word) (a b : Fin 256)
    (gap : a.val+4 ≤ b.val ∨ b.val+4 ≤ a.val) :
    Apart (p+BitVec.ofNat 32 a.val) (p+BitVec.ofNat 32 b.val) := by
  intro i j eq
  have cancel : BitVec.ofNat 32 (a.val+i.val) = BitVec.ofNat 32 (b.val+j.val) := by
    simpa [BitVec.ofNat_add,BitVec.add_assoc] using congrArg (fun x => x-p) eq
  have h := congrArg BitVec.toNat cancel
  have := a.isLt; have := b.isLt; have := i.isLt; have := j.isLt
  simp only [BitVec.toNat_ofNat] at h
  omega

theorem health_frame (s : X86Memory.State) (a : Word) (safe : Apart a (pointer s+(32#32))) :
    load32 (healthMemory s) a = load32 s.memory a := by
  unfold healthMemory
  split <;> simp only [load_store_apart _ _ _ _ safe]

theorem memory_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (resultMemory s) [pointer s+(32#32),pointer s+(228#32),pointer s+(220#32)] := by
  intro a safe
  have h32 := safe (pointer s+(32#32)) (by simp)
  have h228 := safe (pointer s+(228#32)) (by simp)
  have h220 := safe (pointer s+(220#32)) (by simp)
  unfold resultMemory
  split <;> simp only [load_store_apart _ _ _ _ h220,attackerMemory,
    load_store_apart _ _ _ _ h228,health_frame s a h32]

theorem values (s : X86Memory.State) :
    (load32 (resultMemory s) (pointer s+(32#32)),load32 (resultMemory s) (pointer s+(228#32)),
     load32 (resultMemory s) (pointer s+(220#32))) = (health s,source s,count s) := by
  have a : Apart (pointer s+(32#32)) (pointer s+(220#32)) := offsets_apart _ 32 220 (by decide)
  have b : Apart (pointer s+(32#32)) (pointer s+(228#32)) := offsets_apart _ 32 228 (by decide)
  have c : Apart (pointer s+(228#32)) (pointer s+(220#32)) := offsets_apart _ 228 220 (by decide)
  by_cases hp : 0 ≤ (delta s).toInt <;> by_cases hc : (countSum s).toInt ≤ 100 <;>
    simp [resultMemory,hc,load_store_apart _ _ _ _ a,load_store_apart _ _ _ _ c,
      attackerMemory,load_store_apart _ _ _ _ b,load_store,healthMemory,hp,health,count]

/-- All memory effects are retained, without an aliasing premise. -/
theorem original_execution (s : X86Memory.State) (f : Option Flags) :
    (X86Routine.run program [0x2a650] 14 ⟨s,f,0x2a616⟩).map
      (fun t => (t.core.memory,t.core.regs 5,t.core.regs 4,t.core.regs 6,t.core.regs 7,t.pc)) =
      some (resultMemory s,s.regs 5,s.regs 4,s.regs 6,s.regs 7,0x2a650) := by
  have h := execution s f
  have valid : X86Routine.run listed [0x2a650] 14 ⟨s,f,0x2a616⟩ ≠ none := by
    intro hn; rw [hn] at h; contradiction
  rw [X86Routine.run_sound program listed decoded _ _ _ valid]
  exact h

theorem live_values (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32)
    (damage : s.regs 7 = d.toBitVec)
    (hp : load32 s.memory (pointer s+(32#32)) = v.playerHealth.toBitVec)
    (hc : load32 s.memory (pointer s+(220#32)) = v.damageCount.toBitVec)
    (safe : Apart (s.regs 4+(4#32)) (pointer s+(32#32))) :
    (health s,source s,count s) =
      ((PlayerDamage.bookkeep v d).playerHealth.toBitVec,load32 s.memory (s.regs 4+(4#32)),
       (PlayerDamage.bookkeep v d).damageCount.toBitVec) := by
  have a : Apart (pointer s+(220#32)) (pointer s+(228#32)) := offsets_apart _ 220 228 (by decide)
  have b : Apart (pointer s+(220#32)) (pointer s+(32#32)) := offsets_apart _ 220 32 (by decide)
  have sum : countSum s = (v.damageCount+d).toBitVec := by
    simp only [countSum,attackerMemory,load_store_apart _ _ _ _ a,health_frame s _ b,hc,damage]
    rfl
  have sub : delta s = (v.playerHealth-d).toBitVec := by
    simp only [delta,hp,damage]; rfl
  have maximum (a b : Int32) : max a b = if a ≤ b then b else a := rfl
  have minimum (a b : Int32) : min a b = if a ≤ b then a else b := rfl
  rw [health,sub,source,health_frame s _ safe,count,sum]
  have maxword (v : Int32) :
      (if 0 ≤ v.toBitVec.toInt then v.toBitVec else (0#32)) = (max 0 v).toBitVec := by
    rw [maximum]
    by_cases h : 0 ≤ v.toInt
    · have h' : (0:Int32) ≤ v := Int32.le_iff_toInt_le.mpr h
      simp only [Int32.toInt_toBitVec,if_pos h,if_pos h']
    · have h' : ¬(0:Int32) ≤ v := by rw [Int32.le_iff_toInt_le]; exact h
      simp only [Int32.toInt_toBitVec,if_neg h,if_neg h']; rfl
  have minword (v : Int32) :
      (if v.toBitVec.toInt ≤ 100 then v.toBitVec else (100#32)) = (min 100 v).toBitVec := by
    rw [minimum]
    by_cases h : v ≤ 100 <;> by_cases q : 100 ≤ v
    · have eq : v = 100 := Int32.le_antisymm h q
      subst v; decide
    · have h' := Int32.le_iff_toInt_le.mp h
      change v.toInt ≤ 100 at h'
      simp only [Int32.toInt_toBitVec,if_pos h',if_neg q]
    · have h' := h
      simp only [Int32.le_iff_toInt_le] at h'
      change ¬ v.toInt ≤ 100 at h'
      simp only [Int32.toInt_toBitVec,if_neg h',if_pos q]; rfl
    · have h' := h; have q' := q
      simp only [Int32.le_iff_toInt_le] at h' q'
      change ¬ v.toInt ≤ 100 at h'
      change ¬ 100 ≤ v.toInt at q'
      omega
  change (_,_,_) = ((max 0 (v.playerHealth-d)).toBitVec,_,(min 100 (v.damageCount+d)).toBitVec)
  rw [maxword,minword]

/-- Extra initial fields needed after entry and armor. No seam-state assumptions. -/
structure Inputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    extends PlayerDamageEntry.Inputs s v d baby where
  playerHealth : load32 s.memory (PlayerDamageEntry.inputPlayer s+(32#32)) = v.playerHealth.toBitVec
  damageCount : load32 s.memory (PlayerDamageEntry.inputPlayer s+(220#32)) = v.damageCount.toBitVec
  extraStack : ∀ a, a ∈ [PlayerDamageEntry.inputPlayer s+(32#32),PlayerDamageEntry.inputPlayer s+(220#32)] →
    ∀ b, b ∈ PlayerDamageEntry.slots s → Apart a b

def joined (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2a616 ≤ pc ∧ pc < 0x2a650 then program pc else PlayerDamageEntry.program pc

theorem contains_entry (pc : Nat) (h : PlayerDamageEntry.program pc ≠ none) :
    joined pc = PlayerDamageEntry.program pc := by
  unfold joined
  split
  next bound =>
    simp [PlayerDamageEntry.program,PlayerDamageEntry.bytesProgram,
      show ¬(0x2a460 ≤ pc ∧ pc < 0x2a5d5) by omega,
      show ¬(0x2a5d5 ≤ pc ∧ pc < 0x2a616) by omega,
      show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega] at h
  next => rfl

theorem entry_active (pc : Nat) (h : PlayerDamageEntry.program pc ≠ none) :
    pc ∉ [0x2a650,0x2a747] := by
  intro mem
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl <;> contradiction

theorem contains_health (pc : Nat) (h : program pc ≠ none) : joined pc = program pc := by
  unfold program at h
  split at h
  next bound => simp [joined,bound]
  next bound => simp_all

theorem health_active (pc : Nat) (h : program pc ≠ none) : pc ∉ [0x2a650,0x2a747] := by
  unfold program at h
  split at h
  next bound => simp; omega
  next bound => simp_all

def observation (s : X86Memory.State) (t : X86Control.State) : Option (Word × Word × Word × Word × Word × Word) :=
  if t.pc = 0x2a747 then none else
    let p := PlayerDamageEntry.inputPlayer s
    some (t.core.regs 7,load32 t.core.memory (p+(36#32)),load32 t.core.memory (p+(40#32)),
      load32 t.core.memory (p+(32#32)),load32 t.core.memory (p+(220#32)),load32 t.core.memory (p+(228#32)))

def answer (v : PlayerDamage.State) (d : Int32) (baby : Bool) : Option (Word × Word × Word × Word × Word × Word) :=
  if PlayerDamageEntry.accepted v d baby then
    let a := PlayerDamage.absorbArmor v (PlayerDamageEntry.skillDamage d baby)
    let b := PlayerDamage.bookkeep a.1 a.2
    some (a.2.toBitVec,b.armor.toBitVec,b.armorType.toBitVec,b.playerHealth.toBitVec,b.damageCount.toBitVec,0)
  else none

def writes (s : X86Memory.State) := PlayerDamageEntry.writes s ++
  [PlayerDamageEntry.inputPlayer s+(32#32),PlayerDamageEntry.inputPlayer s+(228#32),PlayerDamageEntry.inputPlayer s+(220#32)]

def afterWrites (s : X86Memory.State) :=
  [PlayerDamageEntry.inputPlayer s+36,PlayerDamageEntry.inputPlayer s+40,
   PlayerDamageEntry.inputPlayer s+32,PlayerDamageEntry.inputPlayer s+228,PlayerDamageEntry.inputPlayer s+220]

/-- Real floor CALL through entry, armor, and player bookkeeping; rejection
stops at the epilogue. The memory relation is transported from the initial call. -/
theorem joined_execution_detailed (s : X86Memory.State) (f : Option Flags) (pc : Nat) (site : pc ∈ PlayerDamageEntry.sites)
    (v : PlayerDamage.State) (d : Int32) (baby : Bool) (h : Inputs s v d baby) :
    ∃ t, X86Routine.run joined [0x2a650,0x2a747] 73 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer v d baby ∧
      t.pc = (if PlayerDamageEntry.accepted v d baby then 0x2a650 else 0x2a747) ∧
      t.core.regs 4 = s.regs 4-(28#32) ∧ t.core.regs 6 = s.regs 0 ∧
      PlayerHeight.Frame s.memory t.core.memory (writes s) ∧
      (PlayerDamageEntry.accepted v d baby = true → t.core.regs 5 = PlayerDamageEntry.inputPlayer s) ∧
      PlayerHeight.Frame (PlayerDamageEntry.saved s pc) t.core.memory (afterWrites s) := by
  obtain ⟨g,grun,gobs,gpc,gsp,gobj,gframe,gplayer,gsaved⟩ :=
    PlayerDamageEntry.execution_detailed s f pc site v d baby h.toInputs
  obtain ⟨n,hn,gpath,_⟩ := X86Routine.run_path grun
  have gpath := gpath.transfer joined [0x2a650,0x2a747] contains_entry entry_active
  by_cases accept : PlayerDamageEntry.accepted v d baby = true
  · have gp := gplayer accept
    simp only [accept,if_true] at gpc
    simp only [PlayerDamageEntry.observation,PlayerDamageEntry.answer,gpc,accept,if_true,
      show (0x2a616:Nat) ≠ 0x2a747 by decide,if_false,Option.some.injEq,Prod.mk.injEq] at gobs
    simp only [show (36:Word) = (36#32) from rfl,show (40:Word) = (40#32) from rfl] at gobs
    let a := PlayerDamage.absorbArmor v (PlayerDamageEntry.skillDamage d baby)
    have keep (offset : Fin 256) (which : offset.val = 32 ∨ offset.val = 220) :
        load32 g.core.memory (PlayerDamageEntry.inputPlayer s+BitVec.ofNat 32 offset.val) =
          load32 s.memory (PlayerDamageEntry.inputPlayer s+BitVec.ofNat 32 offset.val) := by
      apply gframe
      intro b hb
      simp only [PlayerDamageEntry.writes,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
      rcases hb with stack | rfl | rfl
      · apply h.extraStack _ _ b stack
        rcases which with e | e <;> simp [e]
      · apply offsets_apart _ offset 36
        change offset.val+4 ≤ 36 ∨ 36+4 ≤ offset.val
        omega
      · apply offsets_apart _ offset 40
        change offset.val+4 ≤ 40 ∨ 40+4 ≤ offset.val
        omega
    have ah : a.1.playerHealth = v.playerHealth := by unfold a PlayerDamage.absorbArmor; split <;> rfl
    have ac : a.1.damageCount = v.damageCount := by unfold a PlayerDamage.absorbArmor; split <;> rfl
    have hp : load32 g.core.memory (pointer g.core+(32#32)) = a.1.playerHealth.toBitVec := by
      rw [pointer,gp,ah]
      exact (keep 32 (by decide)).trans h.playerHealth
    have hc : load32 g.core.memory (pointer g.core+(220#32)) = a.1.damageCount.toBitVec := by
      rw [pointer,gp,ac]
      exact (keep 220 (by decide)).trans h.damageCount
    have stackAddress : g.core.regs 4+(4#32) = s.regs 4-(24#32) := by
      rw [gsp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    have safe : Apart (g.core.regs 4+(4#32)) (pointer g.core+(32#32)) := by
      rw [stackAddress,pointer,gp]
      intro i j eq
      exact h.extraStack _ (by simp) _ (by simp [PlayerDamageEntry.slots]) j i eq.symm
    have src : load32 g.core.memory (g.core.regs 4+(4#32)) = (0#32) := by
      rw [stackAddress,gsaved]
      · simp only [PlayerDamageEntry.saved,load_store]
        exact h.source
      · intro b hb
        simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
        rcases hb with rfl | rfl
        all_goals
          intro i j eq
          exact h.stackSafe _ (by simp [PlayerDamageEntry.reads]) _
            (by simp [PlayerDamageEntry.slots]) j i eq.symm
    have correct := live_values g.core a.1 a.2 gobs.1 hp hc safe
    rw [src] at correct
    have erun := original_execution g.core g.flags
    rw [← gpc] at erun
    cases hr : X86Routine.run program [0x2a650] 14 g with
    | none => simp [hr] at erun
    | some t =>
      obtain ⟨k,hk,hpath,_⟩ := X86Routine.run_path hr
      have hpath := hpath.transfer joined [0x2a650,0x2a747] contains_health health_active
      simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at erun
      rcases erun with ⟨tm,tp,ts,to,td,tpc⟩
      have tail : X86Routine.run joined [0x2a650,0x2a747] 14 g = some t :=
        hpath.finish (fuel := 0) (by simp [X86Routine.run,tpc]) 14 (by omega)
      refine ⟨t,gpath.finish tail 73 (by omega),?_,by simp [accept,tpc],ts.trans gsp,to.trans gobj,?_,(fun _ => tp.trans gp),?_⟩
      · have vals := values g.core
        rw [correct] at vals
        simp only [Prod.mk.injEq] at vals
        have armorKeep : load32 (resultMemory g.core) (pointer g.core+(36#32)) =
            load32 g.core.memory (pointer g.core+(36#32)) := by
          apply memory_frame
          intro b hb
          simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
          rcases hb with rfl | rfl | rfl
          · exact offsets_apart _ 36 32 (by decide)
          · exact offsets_apart _ 36 228 (by decide)
          · exact offsets_apart _ 36 220 (by decide)
        have typeKeep : load32 (resultMemory g.core) (pointer g.core+(40#32)) =
            load32 g.core.memory (pointer g.core+(40#32)) := by
          apply memory_frame
          intro b hb
          simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
          rcases hb with rfl | rfl | rfl
          · exact offsets_apart _ 40 32 (by decide)
          · exact offsets_apart _ 40 228 (by decide)
          · exact offsets_apart _ 40 220 (by decide)
        simp only [pointer,gp] at vals armorKeep typeKeep
        simp [observation,answer,accept,tpc,tm,td,armorKeep,typeKeep,gobs.1,gobs.2.1,gobs.2.2,
          vals.1,vals.2.1,vals.2.2,a,PlayerDamage.bookkeep]
      · intro addr safe
        rw [tm,memory_frame g.core addr]
        · exact gframe addr (fun b hb => safe b (by simp [writes,hb]))
        · intro b hb
          apply safe
          simpa [writes,pointer,gp] using Or.inr hb
      · intro addr safe
        rw [tm,memory_frame g.core addr]
        · exact gsaved addr (fun b hb => safe b (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb; rcases hb with rfl | rfl <;> simp [afterWrites]))
        · intro b hb
          apply safe
          simpa [afterWrites,pointer,gp] using Or.inr (Or.inr hb)
  · have reject : PlayerDamageEntry.accepted v d baby = false := by simpa using accept
    simp only [reject,Bool.false_eq_true,if_false] at gpc
    refine ⟨g,gpath.finish (fuel := 0) (by simp [X86Routine.run,gpc]) 73 (by omega),
      by simp [observation,answer,reject,gpc],by simp [reject,gpc],gsp,gobj,?_,(by simp [reject]),?_⟩
    · intro a safe
      exact gframe a (fun b hb => safe b (by simp [writes,hb]))
    · intro a safe
      exact gsaved a (fun b hb => safe b (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb; rcases hb with rfl | rfl <;> simp [afterWrites]))

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat) (site : pc ∈ PlayerDamageEntry.sites)
    (v : PlayerDamage.State) (d : Int32) (baby : Bool) (h : Inputs s v d baby) :
    ∃ t, X86Routine.run joined [0x2a650,0x2a747] 73 ⟨s,f,pc⟩ = some t ∧
      observation s t = answer v d baby ∧
      t.pc = (if PlayerDamageEntry.accepted v d baby then 0x2a650 else 0x2a747) ∧
      t.core.regs 4 = s.regs 4-(28#32) ∧ t.core.regs 6 = s.regs 0 ∧
      PlayerHeight.Frame s.memory t.core.memory (writes s) := by
  obtain ⟨t,run,obs,pc',sp,obj,frame,_⟩ := joined_execution_detailed s f pc site v d baby h
  exact ⟨t,run,obs,pc',sp,obj,frame⟩


/-- The final component is the DOS null attacker pointer for environmental
damage. Live attacker identity belongs to Combat and is not modeled here. -/
def liveObservation (v : PlayerDamage.State) (out : PlayerDamage.Result) : Option (Word × Word × Word × Word × Word × Word) :=
  if out.applied then some ((v.health-out.state.health).toBitVec,out.state.armor.toBitVec,
    out.state.armorType.toBitVec,out.state.playerHealth.toBitVec,out.state.damageCount.toBitVec,0)
  else none

theorem finish_observation (v : PlayerDamage.State) (d : Int32) (rng : DoomRandom) :
    liveObservation v (PlayerDamage.finish v d rng) =
      let a := PlayerDamage.absorbArmor v d
      let b := PlayerDamage.bookkeep a.1 a.2
      some (a.2.toBitVec,b.armor.toBitVec,b.armorType.toBitVec,b.playerHealth.toBitVec,b.damageCount.toBitVec,0) := by
  have health : (PlayerDamage.absorbArmor v d).1.health = v.health := by
    unfold PlayerDamage.absorbArmor
    split <;> rfl
  have cancel (a b : Int32) : (a-(a-b)).toBitVec = b.toBitVec := by
    simp only [Int32.toBitVec_sub]
    rw [BitVec.sub_eq_iff_eq_add,BitVec.add_comm,BitVec.sub_add_cancel]
  unfold PlayerDamage.finish
  simp only [Id.run,pure,bind]
  split <;> simp [liveObservation,PlayerDamage.bookkeep,health,cancel]

theorem live_answer (v : PlayerDamage.State) (d : Int32) (baby : Bool) (rng : DoomRandom)
    (skull : v.skullFly = false) (ordinary : v.sectorSpecial ≠ 11) :
    liveObservation v (PlayerDamage.apply v d none false baby rng) = answer v d baby := by
  rw [PlayerDamageEntry.live_entry v d baby false rng skull ordinary]
  by_cases h : PlayerDamageEntry.accepted v d baby = true
  · simp [h,answer,finish_observation]
  · simp [h,answer,liveObservation]

/-- Continuous original bytes agree with the actual live damage function's
armor, remaining damage, player health and counter, and store null attacker. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (baby : Bool) (rng : DoomRandom) (h : Inputs s v d baby) :
    (X86Routine.run joined [0x2a650,0x2a747] 73 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation v (PlayerDamage.apply v d none false baby rng)) := by
  obtain ⟨t,run,obs,_⟩ := joined_execution s f pc site v d baby h
  rw [live_answer v d baby rng h.liveSkull h.liveOrdinary]
  simp [run,obs]

end Doom.Proofs.PlayerHealth

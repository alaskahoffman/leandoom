import Doom.Proofs.OriginalLineCollection
import Doom.Proofs.OriginalThingCallback
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalThingFinish
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineFinish (Encodes RecordAt)
def thingFinish : List UInt8 := [0x83,0xc4,0x18,0x5d,0x5f,0x5e,0x5a,0x59,0x5b,0xc3,0x8b,0x35,0x28,0xc0,0x2,0x0,0x83,0xc6,0xc,0xc7,0x46,0xf8,0x0,0x0,0x0,0x0,0x89,0x46,0xf4,0x89,0x4e,0xfc,0xb8,0x1,0x0,0x0,0x0,0x89,0x35,0x28,0xc0,0x2,0x0,0x83,0xc4,0x18,0x5d,0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c7da≤pc ∧ pc<0x2c80f then X86Routine.decodeAt bytes (pc-0x2c7da) else none
def program := bytesProgram thingFinish
def listed : X86Routine.Program
  | 0x2c7e4 => some (.control (.block (.load 6 ⟨none,none,0,0x2c028⟩)),6)
  | 0x2c7ea => some (.addImmediate 6 12,3)
  | 0x2c7ed => some (.storeImmediate ⟨some 6,none,0,-8⟩ 0,7)
  | 0x2c7f4 => some (.control (.block (.store ⟨some 6,none,0,-12⟩ 0)),3)
  | 0x2c7f7 => some (.control (.block (.store ⟨some 6,none,0,-4⟩ 1)),3)
  | 0x2c7fa => some (.immediate 0 1,5)
  | 0x2c7ff => some (.control (.block (.store ⟨none,none,0,0x2c028⟩ 6)),6)
  | 0x2c7da => some (.addImmediate 4 24,3)
  | 0x2c7dd => some (.pop 5,1)
  | 0x2c7de => some (.pop 7,1)
  | 0x2c7df => some (.pop 6,1)
  | 0x2c7e0 => some (.pop 2,1)
  | 0x2c7e1 => some (.pop 1,1)
  | 0x2c7e2 => some (.pop 3,1)
  | 0x2c7e3 => some (.ret,1)
  | 0x2c805 => some (.addImmediate 4 24,3)
  | 0x2c808 => some (.pop 5,1)
  | 0x2c809 => some (.pop 7,1)
  | 0x2c80a => some (.pop 6,1)
  | 0x2c80b => some (.pop 2,1)
  | 0x2c80c => some (.pop 1,1)
  | 0x2c80d => some (.pop 3,1)
  | 0x2c80e => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def u0 (s : X86Memory.State) := put s 4 (s.regs 4+(24#32))
def u1 (s : X86Memory.State) := put (put (u0 s) 4 (s.regs 4+(28#32))) 5 (load32 s.memory (s.regs 4+(24#32)))
def u2 (s : X86Memory.State) := put (put (u1 s) 4 (s.regs 4+(32#32))) 7 (load32 s.memory (s.regs 4+(28#32)))
def u3 (s : X86Memory.State) := put (put (u2 s) 4 (s.regs 4+(36#32))) 6 (load32 s.memory (s.regs 4+(32#32)))
def u4 (s : X86Memory.State) := put (put (u3 s) 4 (s.regs 4+(40#32))) 2 (load32 s.memory (s.regs 4+(36#32)))
def u5 (s : X86Memory.State) := put (put (u4 s) 4 (s.regs 4+(44#32))) 1 (load32 s.memory (s.regs 4+(40#32)))
def u6 (s : X86Memory.State) := put (put (u5 s) 4 (s.regs 4+(48#32))) 3 (load32 s.memory (s.regs 4+(44#32)))
def unwind (s : X86Memory.State) : X86Control.State :=
  ⟨put (u6 s) 4 (s.regs 4+(52#32)),none,(load32 s.memory (s.regs 4+(48#32))).toNat⟩

theorem unwind_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (atReturn : pc∈[0x2c7da,0x2c805]) :
    X86Routine.Prefix program [] 8 ⟨s,f,pc⟩ (unwind s) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at atReturn
  rcases atReturn with rfl|rfl
  · have path : X86Routine.Prefix listed [] 8 ⟨s,f,0x2c7da⟩ (unwind s) := by
      apply X86Routine.Prefix.step (middle:=⟨u0 s,none,0x2c7dd⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u1 s,none,0x2c7de⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u2 s,none,0x2c7df⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u3 s,none,0x2c7e0⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u4 s,none,0x2c7e1⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u5 s,none,0x2c7e2⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u6 s,none,0x2c7e3⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=unwind s) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      exact .nil _
    exact path.transfer program [] decoded (by simp)
  · have path : X86Routine.Prefix listed [] 8 ⟨s,f,0x2c805⟩ (unwind s) := by
      apply X86Routine.Prefix.step (middle:=⟨u0 s,none,0x2c808⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u1 s,none,0x2c809⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u2 s,none,0x2c80a⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u3 s,none,0x2c80b⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u4 s,none,0x2c80c⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u5 s,none,0x2c80d⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=⟨u6 s,none,0x2c80e⟩) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle:=unwind s) (by simp) (by rfl) (by simp [unwind,u0,u1,u2,u3,u4,u5,u6,X86Routine.execute,put,write,BitVec.add_assoc])
      exact .nil _
    exact path.transfer program [] decoded (by simp)
def ins1 (s : X86Memory.State) := put s 6 (load32 s.memory (0x2c028#32))
def ins2 (s : X86Memory.State) := put (ins1 s) 6 ((ins1 s).regs 6+(12#32))
def ins3 (s : X86Memory.State) := {(ins2 s) with memory:=store32 (ins2 s).memory ((ins2 s).regs 6-(8#32)) (0#32)}
def ins4 (s : X86Memory.State) := {(ins3 s) with memory:=store32 (ins3 s).memory ((ins3 s).regs 6-(12#32)) ((ins3 s).regs 0)}
def ins5 (s : X86Memory.State) := {(ins4 s) with memory:=store32 (ins4 s).memory ((ins4 s).regs 6-(4#32)) ((ins4 s).regs 1)}
def ins6 (s : X86Memory.State) := put (ins5 s) 0 1
def ins7 (s : X86Memory.State) := {(ins6 s) with memory:=store32 (ins6 s).memory (0x2c028#32) ((ins6 s).regs 6)}
def inserted := ins7

theorem insert_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 15 ⟨s,f,0x2c7e4⟩ (unwind (inserted s)) := by
  have head : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c7e4⟩ ⟨inserted s,none,0x2c805⟩ := by
    apply X86Routine.Prefix.step (middle:=⟨ins1 s,f,0x2c7ea⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1])
    apply X86Routine.Prefix.step (middle:=⟨ins2 s,none,0x2c7ed⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2])
    apply X86Routine.Prefix.step (middle:=⟨ins3 s,none,0x2c7f4⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2,ins3])
    apply X86Routine.Prefix.step (middle:=⟨ins4 s,none,0x2c7f7⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2,ins3,ins4])
    apply X86Routine.Prefix.step (middle:=⟨ins5 s,none,0x2c7fa⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2,ins3,ins4,ins5])
    apply X86Routine.Prefix.step (middle:=⟨ins6 s,none,0x2c7ff⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2,ins3,ins4,ins5,ins6])
    apply X86Routine.Prefix.step (middle:=⟨ins7 s,none,0x2c805⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2,ins3,ins4,ins5,ins6,ins7])
    exact .nil _
  exact OriginalGroupBounds.prefix_join (head.transfer program [] decoded (by simp)) (unwind_execution _ _ _ (by simp))

theorem unwind_observe (s : X86Memory.State) :
    (unwind s).core.memory=s.memory ∧ (unwind s).core.regs 0=s.regs 0 ∧
    (unwind s).core.regs 4=s.regs 4+(52#32) ∧
    (unwind s).core.regs 5=load32 s.memory (s.regs 4+(24#32)) ∧
    (unwind s).core.regs 7=load32 s.memory (s.regs 4+(28#32)) ∧
    (unwind s).core.regs 6=load32 s.memory (s.regs 4+(32#32)) ∧
    (unwind s).core.regs 2=load32 s.memory (s.regs 4+(36#32)) ∧
    (unwind s).core.regs 1=load32 s.memory (s.regs 4+(40#32)) ∧
    (unwind s).core.regs 3=load32 s.memory (s.regs 4+(44#32)) ∧
    (unwind s).pc=(load32 s.memory (s.regs 4+(48#32))).toNat := by
  simp [unwind,u0,u1,u2,u3,u4,u5,u6,put,write]

abbrev cursor := OriginalLineFinish.cursor
def written (s : X86Memory.State) :=
  store32 (store32 (store32 (store32 s.memory (cursor s+(4#32)) (0#32))
    (cursor s) (s.regs 0)) (cursor s+(8#32)) (s.regs 1)) (0x2c028#32) (cursor s+(12#32))

theorem inserted_memory (s : X86Memory.State) : (inserted s).memory=written s := by
  simp [inserted,ins1,ins2,ins3,ins4,ins5,ins6,ins7,written,OriginalLineFinish.cursor,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem inserted_regs (s : X86Memory.State) :
    (inserted s).regs 0=(1#32) ∧ (inserted s).regs 4=s.regs 4 := by
  simp [inserted,ins1,ins2,ins3,ins4,ins5,ins6,ins7,put,write]

/-- The incoming PC distinguishes the actual insertion and both rejection exits. -/
def result (s : X86Control.State) := if s.pc=0x2c7e4 then unwind (inserted s.core) else unwind s.core

theorem execution (s : X86Control.State) (atFinish : s.pc∈[0x2c7da,0x2c7e4,0x2c805]) :
    ∃ n≤15, X86Routine.Prefix program [] n s (result s) := by
  by_cases atInsert : s.pc=0x2c7e4
  · have run := insert_execution s.core s.flags
    rw [OriginalPathXStep.at_pc _ _ atInsert] at run
    exact ⟨15,by omega,by simpa only [result,if_pos atInsert] using run⟩
  · have r : s.pc∈[0x2c7da,0x2c805] := by simpa [atInsert] using atFinish
    have run := unwind_execution s.core s.flags s.pc r
    exact ⟨8,by omega,by simpa only [result,if_neg atInsert] using run⟩

theorem result_memory (s : X86Control.State) :
    (result s).core.memory=if s.pc=0x2c7e4 then written s.core else s.core.memory := by
  unfold result
  split <;> simp only [(unwind_observe _).1,inserted_memory]
theorem result_value (s : X86Control.State) :
    (result s).core.regs 0=if s.pc=0x2c7e4 then (1#32) else s.core.regs 0 := by
  unfold result
  split <;> simp only [(unwind_observe _).2.1,(inserted_regs _).1]
theorem result_sp (s : X86Control.State) : (result s).core.regs 4=s.core.regs 4+(52#32) := by
  unfold result
  split <;> simp only [(unwind_observe _).2.2.1,(inserted_regs _).2]
theorem result_cursor (s : X86Control.State) :
    (result s).core.regs 2=load32 (result s).core.memory (s.core.regs 4+(36#32)) := by
  unfold result
  split <;> simp only [(unwind_observe _).2.2.2.2.2.2.1,(unwind_observe _).1,(inserted_regs _).2]
theorem result_pc (s : X86Control.State) :
    (result s).pc=(load32 (result s).core.memory (s.core.regs 4+(48#32))).toNat := by
  unfold result
  split <;> simp only [(unwind_observe _).2.2.2.2.2.2.2.2.2,(unwind_observe _).1,(inserted_regs _).2]
theorem written_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ w∈[cursor s,cursor s+(4#32),cursor s+(8#32),(0x2c028#32)], Apart a w) :
    load32 (written s) a=load32 s.memory a := by
  unfold written
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp))]
theorem frame (s : X86Control.State) (a : Word)
    (safe : ∀ w∈[cursor s.core,cursor s.core+(4#32),cursor s.core+(8#32),(0x2c028#32)], Apart a w) :
    load32 (result s).core.memory a=load32 s.core.memory a := by
  rw [result_memory]; split
  · exact written_frame s.core a safe
  · rfl
theorem written_cursor (s : X86Memory.State) : load32 (written s) (0x2c028#32)=cursor s+(12#32) := by
  unfold written; rw [load_store]
theorem written_record (s : X86Memory.State)
    (safe : ∀ off∈[(0#32),4,8], Apart (cursor s+off) (0x2c028#32)) :
    load32 (written s) (cursor s)=s.regs 0 ∧
    load32 (written s) (cursor s+(4#32))=(0#32) ∧
    load32 (written s) (cursor s+(8#32))=s.regs 1 := by
  have apart (a b : Word) (h : Apart a b) := OriginalPathXStep.apart_translate (cursor s) a b h
  unfold written
  constructor
  · rw [load_store_apart _ _ _ _ (by simpa only [BitVec.add_zero] using safe (0#32) (by simp)),
      load_store_apart _ _ _ _ (by simpa only [BitVec.add_zero] using apart (0#32) (8#32) (by unfold Apart; decide)),load_store]
  constructor
  · rw [load_store_apart _ _ _ _ (safe (4#32) (by simp)),load_store_apart _ _ _ _ (apart (4#32) (8#32) (by unfold Apart; decide)),
      load_store_apart _ _ _ _ (by simpa only [BitVec.add_zero] using apart (4#32) (0#32) (by unfold Apart; decide)),load_store]
  · rw [load_store_apart _ _ _ _ (safe (8#32) (by simp)),load_store]
theorem append_encoded (s : X86Control.State) (base : Word)
    (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept) (hit : Collision.Intercept)
    (enabled : s.pc=0x2c7e4) (encoded : Encodes s.core.memory base resolve hits)
    (atEnd : cursor s.core=base+BitVec.ofNat 32 (12*hits.size))
    (fraction : s.core.regs 0=hit.frac.raw.toBitVec) (kind : hit.isLine=false)
    (pointer : s.core.regs 1=resolve hit)
    (newSafe : ∀ off∈[(0#32),4,8], Apart (cursor s.core+off) (0x2c028#32))
    (oldSafe : ∀ (i : Nat), i<hits.size → ∀ off∈[(0#32),4,8],
      ∀ w∈[cursor s.core,cursor s.core+(4#32),cursor s.core+(8#32),(0x2c028#32)],
        Apart (base+BitVec.ofNat 32 (12*i)+off) w) :
    Encodes (result s).core.memory base resolve (hits.push hit) := by
  rw [result_memory,if_pos enabled]
  intro i hi
  have bound : i≤hits.size := by simp only [Array.size_push] at hi; omega
  by_cases old : i<hits.size
  · rw [Array.getElem_push_lt old]
    have keep (off : Word) (ho : off∈[(0#32),4,8]) :=
      written_frame s.core (base+BitVec.ofNat 32 (12*i)+off) (oldSafe i old off ho)
    have previous := encoded i old
    unfold RecordAt at previous ⊢
    rw [show load32 (written s.core) (base+BitVec.ofNat 32 (12*i))=
        load32 s.core.memory (base+BitVec.ofNat 32 (12*i)) by simpa using keep 0 (by simp),
      keep (4#32) (by simp), keep (8#32) (by simp)]
    exact previous
  · have eq : i=hits.size := by omega
    subst i
    rw [Array.getElem_push_eq,←atEnd]
    have record := written_record s.core newSafe
    simpa only [RecordAt,fraction,pointer,kind,Bool.false_eq_true,if_false] using record


theorem append_tracks (s : X86Control.State) (base : Word)
    (resolve : Collision.Intercept → Word) (r : Collision.PathResult) (frac : Fixed) (id : Nat)
    (enabled : s.pc=0x2c7e4)
    (tracked : OriginalLineCollection.Tracks s.core base resolve r.collected 0)
    (capacity : r.collected.size<128)
    (fraction : s.core.regs 0=frac.raw.toBitVec) (pointer : s.core.regs 1=resolve ⟨frac,false,id⟩)
    (metadata : ∀ i<128, ∀ off∈[(0#32),4,8], Apart (OriginalLineCollection.slot base i off) (0x2c028#32)) :
    Collision.appendIntercept r ⟨frac,false,id⟩=.ok {r with collected:=r.collected.push ⟨frac,false,id⟩} ∧
    OriginalLineCollection.Tracks (result s).core base resolve (r.collected.push ⟨frac,false,id⟩) 0 := by
  have newer : ∀ off∈[(0#32),4,8], Apart (cursor s.core+off) (0x2c028#32) := by
    change ∀ off∈[(0#32),4,8], Apart (OriginalLineFinish.cursor s.core+off) (0x2c028#32)
    rw [tracked.cursor]
    exact metadata r.collected.size capacity
  have older (i : Nat) (hi : i<r.collected.size) (off : Word) (ho : off∈[(0#32),4,8])
      (w : Word) (hw : w∈[cursor s.core,cursor s.core+(4#32),cursor s.core+(8#32),(0x2c028#32)]) :
      Apart (OriginalLineCollection.slot base i off) w := by
    change w∈[OriginalLineFinish.cursor s.core,OriginalLineFinish.cursor s.core+(4#32),OriginalLineFinish.cursor s.core+(8#32),(0x2c028#32)] at hw
    rw [tracked.cursor] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl
    · simpa only [OriginalLineCollection.slot,BitVec.add_zero] using OriginalLineCollection.slots_apart base i r.collected.size (by omega) capacity (by omega) off (0#32) ho (by simp)
    · exact OriginalLineCollection.slots_apart base i r.collected.size (by omega) capacity (by omega) off (4#32) ho (by simp)
    · exact OriginalLineCollection.slots_apart base i r.collected.size (by omega) capacity (by omega) off (8#32) ho (by simp)
    · exact metadata i (by omega) off ho
  refine ⟨OriginalLineFinish.append_live r _ capacity,
    append_encoded s base resolve r.collected _ enabled tracked.encoded tracked.cursor fraction rfl pointer newer older,?_,?_⟩
  · change load32 (result s).core.memory (0x2c028#32)=_
    rw [result_memory,if_pos enabled,written_cursor]
    change OriginalLineFinish.cursor s.core+(12#32)=_
    rw [tracked.cursor]
    simp [Array.size_push,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
  · simp only [Array.size_push]; omega
end Doom.Proofs.OriginalThingFinish

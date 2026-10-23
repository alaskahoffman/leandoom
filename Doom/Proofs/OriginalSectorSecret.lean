import Doom.Proofs.BlockSummary
import Doom.Verification.X86Routine
import Doom.LevelSpecials

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.SectorSecret
open Verification X86 X86Memory X86Control BlockSummary X86Routine

/-- Original P_PlayerInSpecialSector case 9, including POPs and RET.
Entering this case (floor equality and switch dispatch) is a separate obligation. -/
def code : List UInt8 := [0xff,0x86,0xd4,0x00,0x00,0x00,
  0x66,0xc7,0x41,0x0e,0x00,0x00,0x5e,0x5a,0x59,0x5b,0xc3]
def program := X86Routine.decodeAt code

def countAddress (s : X86Memory.State) := s.regs 6+(212#32)
def specialAddress (s : X86Memory.State) := s.regs 1+(14#32)
def count (s : X86Memory.State) := load32 s.memory (countAddress s)
def updated (s : X86Memory.State) : X86Memory.State :=
  {s with memory := store16 (store32 s.memory (countAddress s) (count s+1)) (specialAddress s) 0}

theorem load_store16 (m : Memory) (a : Word) (v : BitVec 16) : load16 (store16 m a v) a = v := by
  simp only [load16,store16]
  bv_decide

/-- A word read disjoint from the two-byte write is unchanged. -/
theorem load32_store16 (m : Memory) (a b : Word) (v : BitVec 16)
    (safe : ∀ i : Fin 4, b+BitVec.ofNat 32 i.val ≠ a ∧ b+BitVec.ofNat 32 i.val ≠ a+1) :
    load32 (store16 m a v) b = load32 m b := by
  have h0 := safe 0
  have h1 := safe 1
  have h2 := safe 2
  have h3 : b+3 ≠ a ∧ b+3 ≠ a+1 := safe 3
  simp_all [load32,store16]

def Separate (s : X86Memory.State) : Prop :=
  ∀ i : Fin 4, countAddress s+BitVec.ofNat 32 i.val ≠ specialAddress s ∧
    countAddress s+BitVec.ofNat 32 i.val ≠ specialAddress s+1

theorem updated_count (s : X86Memory.State) (safe : Separate s) :
    load32 (updated s).memory (countAddress s) = count s+1 := by
  rw [updated,load32_store16 _ _ _ _ safe,load_store]

theorem updated_special (s : X86Memory.State) : load16 (updated s).memory (specialAddress s) = 0 :=
  load_store16 _ _ _

/-- Exactly six byte addresses may change; the two bytes following the sector
special are preserved, unlike a four-byte clear. -/
def Written (s : X86Memory.State) (a : Word) : Prop :=
  (∃ i : Fin 4, a = countAddress s+BitVec.ofNat 32 i.val) ∨
    a = specialAddress s ∨ a = specialAddress s+1

theorem updated_frame (s : X86Memory.State) (a : Word) (safe : ¬ Written s a) :
    (updated s).memory a = s.memory a := by
  have hc (i : Fin 4) : a ≠ countAddress s+BitVec.ofNat 32 i.val := fun h => safe (Or.inl ⟨i,h⟩)
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 : a ≠ countAddress s+3 := hc 3
  have hs : a ≠ specialAddress s := fun h => safe (Or.inr (Or.inl h))
  have hs1 : a ≠ specialAddress s+1 := fun h => safe (Or.inr (Or.inr h))
  simp_all [updated,store16,store32]

/-- The exact two original writes. INC's flags are invalidated by the limited
model, and no subsequent instruction in this region consumes them. -/
theorem body (s : X86Memory.State) (flags : Option Flags) :
    X86Routine.run program [12] 2 ⟨s,flags,0⟩ = some ⟨updated s,none,12⟩ := by
  have d0 : program 0 = some (.incrementMemory ⟨some 6,none,0,212⟩,6) := by decide
  have d6 : program 6 = some (.storeHalfImmediate ⟨some 1,none,0,14⟩ 0,6) := by decide
  simp [X86Routine.run,d0,d6,X86Routine.execute,X86Block.Address.eval,updated,count,countAddress,specialAddress]

def restored (s : X86Memory.State) : X86Memory.State :=
  {regs := write (write (write (write (write s.regs
    6 (load32 s.memory (s.regs 4)))
    2 (load32 s.memory (s.regs 4+4)))
    1 (load32 s.memory (s.regs 4+8)))
    3 (load32 s.memory (s.regs 4+12))) 4 (s.regs 4+20)
   memory := s.memory}

def returnPc (s : X86Memory.State) := (load32 s.memory (s.regs 4+16)).toNat

theorem epilogue (s : X86Memory.State) (flags : Option Flags) (outside : 17 ≤ returnPc s) :
    X86Routine.run program [returnPc s] 5 ⟨s,flags,12⟩ =
      some ⟨restored s,flags,returnPc s⟩ := by
  have d12 : program 12 = some (.pop 6,1) := by decide
  have d13 : program 13 = some (.pop 2,1) := by decide
  have d14 : program 14 = some (.pop 1,1) := by decide
  have d15 : program 15 = some (.pop 3,1) := by decide
  have d16 : program 16 = some (.ret,1) := by decide
  generalize hr : returnPc s = ret at outside ⊢
  have hret : (load32 s.memory (s.regs 4+(16#32))).toNat = ret := hr
  have a12 : 12 ≠ ret := by omega
  have a13 : 13 ≠ ret := by omega
  have a14 : 14 ≠ ret := by omega
  have a15 : 15 ≠ ret := by omega
  have a16 : 16 ≠ ret := by omega
  simp [X86Routine.run,a12,a13,a14,a15,a16,d12,d13,d14,d15,d16,X86Routine.execute,
    restored,put,write,BitVec.add_assoc,hret]
  funext r
  simp [write]
  split <;> simp_all

/-- The caller-supplied five stack words survive both secret writes. -/
def StackSafe (s : X86Memory.State) : Prop :=
  ∀ j : Fin 5, ∀ i : Fin 4, ¬ Written s (s.regs 4+BitVec.ofNat 32 (j.val*4)+BitVec.ofNat 32 i.val)

theorem saved (s : X86Memory.State) (safe : StackSafe s) (j : Fin 5) :
    load32 (updated s).memory (s.regs 4+BitVec.ofNat 32 (j.val*4)) =
      load32 s.memory (s.regs 4+BitVec.ofNat 32 (j.val*4)) := by
  let a := s.regs 4+BitVec.ofNat 32 (j.val*4)
  have h0 : (updated s).memory a = s.memory a := by
    have h : (updated s).memory (a+0) = s.memory (a+0) := updated_frame s _ (safe j 0)
    simpa using h
  have h1 : (updated s).memory (a+1) = s.memory (a+1) := updated_frame s _ (safe j 1)
  have h2 : (updated s).memory (a+2) = s.memory (a+2) := updated_frame s _ (safe j 2)
  have h3 : (updated s).memory (a+3) = s.memory (a+3) := updated_frame s _ (safe j 3)
  change load32 (updated s).memory a = load32 s.memory a
  simp only [load32,h0,h1,h2,h3]

/-- Restore the caller's four saved registers and consume its return word. -/
def final (s : X86Memory.State) : X86Memory.State :=
  {restored s with memory := (updated s).memory}

theorem updated_return (s : X86Memory.State) (safe : StackSafe s) : returnPc (updated s) = returnPc s := by
  have keep : load32 (updated s).memory (s.regs 4+16) = load32 s.memory (s.regs 4+16) := saved s safe 4
  exact congrArg BitVec.toNat keep

theorem updated_restored (s : X86Memory.State) (safe : StackSafe s) : restored (updated s) = final s := by
  have k0 : load32 (updated s).memory (s.regs 4) = load32 s.memory (s.regs 4) := by
    have h : load32 (updated s).memory (s.regs 4+0) = load32 s.memory (s.regs 4+0) := saved s safe 0
    simpa using h
  have k1 : load32 (updated s).memory (s.regs 4+4) = load32 s.memory (s.regs 4+4) := saved s safe 1
  have k2 : load32 (updated s).memory (s.regs 4+8) = load32 s.memory (s.regs 4+8) := saved s safe 2
  have k3 : load32 (updated s).memory (s.regs 4+12) = load32 s.memory (s.regs 4+12) := saved s safe 3
  simp only [restored,final,updated] at k0 k1 k2 k3 ⊢
  rw [k0,k1,k2,k3]

theorem execution (s : X86Memory.State) (flags : Option Flags)
    (safe : StackSafe s) (outside : 17 ≤ returnPc s) :
    X86Routine.run program [returnPc s] 7 ⟨s,flags,0⟩ = some ⟨final s,none,returnPc s⟩ := by
  have d0 : program 0 = some (.incrementMemory ⟨some 6,none,0,212⟩,6) := by decide
  have d6 : program 6 = some (.storeHalfImmediate ⟨some 1,none,0,14⟩ 0,6) := by decide
  have first : X86Routine.Prefix program [returnPc s] 2 ⟨s,flags,0⟩ ⟨updated s,none,12⟩ := by
    apply X86Routine.Prefix.step (by simp only [List.mem_singleton]; omega) d0 (by rfl)
    apply X86Routine.Prefix.step (by simp only [List.mem_singleton]; omega) d6 (by rfl)
    simpa [updated,count,countAddress,specialAddress,X86Block.Address.eval] using
      (X86Routine.Prefix.nil (program := program) (exits := [returnPc s]) (⟨updated s,none,12⟩ : X86Control.State))
  have tail := epilogue (updated s) none (by rw [updated_return s safe]; exact outside)
  rw [updated_return s safe,updated_restored s safe] at tail
  exact first.finish tail 7 (by decide)

/-- The live secret helper's successful case, with signed 32-bit wraparound. -/
theorem secret_fields (s : X86Memory.State) (n : Int32) (z floor : Fixed)
    (onFloor : z = floor) (isSecret : load16 s.memory (specialAddress s) = 9)
    (encoded : count s = n.toBitVec) (separate : Separate s) :
    (load16 (final s).memory (specialAddress s),load32 (final s).memory (countAddress s)) =
      (BitVec.ofNat 16 (LevelSpecials.secret (load16 s.memory (specialAddress s)).toNat z floor n).1,(LevelSpecials.secret (load16 s.memory (specialAddress s)).toNat z floor n).2.toBitVec) := by
  subst floor
  change (load16 (updated s).memory (specialAddress s),load32 (updated s).memory (countAddress s)) = _
  rw [updated_special,updated_count s separate,encoded]
  have self : (z == z) = true := by change (z.raw == z.raw) = true; simp
  simp [LevelSpecials.secret,self,isSecret]

/-- Original case-9 bytes agree with the live helper and return using the
untouched caller stack. Reaching this case is not assumed to be proved here. -/
theorem observation (s : X86Memory.State) (flags : Option Flags) (n : Int32) (z floor : Fixed)
    (onFloor : z = floor) (isSecret : load16 s.memory (specialAddress s) = 9)
    (encoded : count s = n.toBitVec) (separate : Separate s)
    (safe : StackSafe s) (outside : 17 ≤ returnPc s) :
    (X86Routine.run program [returnPc s] 7 ⟨s,flags,0⟩).map (fun t =>
      (t.pc,load16 t.core.memory (specialAddress s),load32 t.core.memory (countAddress s),t.core.regs 4)) =
      some (returnPc s,BitVec.ofNat 16 (LevelSpecials.secret (load16 s.memory (specialAddress s)).toNat z floor n).1,
        (LevelSpecials.secret (load16 s.memory (specialAddress s)).toNat z floor n).2.toBitVec,s.regs 4+20) := by
  rw [execution s flags safe outside]
  have fields := secret_fields s n z floor onFloor isSecret encoded separate
  simp only [Prod.mk.injEq] at fields
  change some (returnPc s,load16 (final s).memory (specialAddress s),load32 (final s).memory (countAddress s),_) = _
  rw [fields.1,fields.2]
  rfl

end Doom.Proofs.SectorSecret

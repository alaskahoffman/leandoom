import Doom.Proofs.OriginalSectorEntry
import Doom.Proofs.OriginalMoveGuards
import Doom.Proofs.OriginalPlayerHeight
import Doom.Random

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.FloorDamage
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0x8b,0x56,0x38,0x85,0xd2,0xf,0x85,0xd7,0x0,0x0,0x0,0xf6,0x5,0x80,0xcf,0x2,0x0,0x1f,0xf,0x85,0xca,0x0,0x0,0x0,0xb9,0xa,0x0,0x0,0x0,0x31,0xdb,0xe8,0xe5,0xa8,0xff,0xff,0x5e,0x5a,0x59,0x5b,0xc3,0x83,0x7e,0x38,0x0,0xf,0x85,0xaf,0x0,0x0,0x0,0xf6,0x5,0x80,0xcf,0x2,0x0,0x1f,0xf,0x85,0xa2,0x0,0x0,0x0,0xb9,0x5,0x0,0x0,0x0,0x31,0xd2,0x31,0xdb,0xe8,0xbb,0xa8,0xff,0xff,0x5e,0x5a,0x59,0x5b,0xc3,0x83,0x7e,0x38,0x0,0x74,0xe,0xe8,0xab,0x45,0xff,0xff,0x83,0xf8,0x5,0xf,0x8d,0x7b,0x0,0x0,0x0,0xf6,0x5,0x80,0xcf,0x2,0x0,0x1f,0x75,0x72,0xb9,0x14,0x0,0x0,0x0,0x8b,0x6,0x31,0xd2,0x31,0xdb,0xe8,0x89,0xa8,0xff,0xff,0x5e,0x5a,0x59,0x5b,0xc3]

def bytesProgram (cases rng : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2fb57 ≤ pc ∧ pc < 0x2fb57+cases.length then X86Routine.decodeAt cases (pc-0x2fb57)
  else if 0x24160 ≤ pc ∧ pc < 0x24160+rng.length then X86Routine.decodeAt rng (pc-0x24160)
  else none

def program := bytesProgram code Doom19.playRandomBytes

def exits : List Nat := [0x2fc39,0x2fb76,0x2fba0,0x2fbd2]

def player (s : X86Memory.State) : Word := s.regs 6
def suitWord (s : X86Memory.State) : Word := load32 s.memory (player s+(56#32))
def due (s : X86Memory.State) : Bool := (s.memory (0x2cf80#32) &&& (31#8)) == 0

def listed : X86Routine.Program
  | 0x2fb57 => some (.control (.block (.legacy (.load 2 6 56))),3)
  | 0x2fb5a => some (.control (.testWord 2 2),2)
  | 0x2fb5c => some (.control (.jumpZero false 215),6)
  | 0x2fb62 => some (.testMemoryByte ⟨none,none,0,0x2cf80⟩ 31,7)
  | 0x2fb69 => some (.control (.jumpZero false 202),6)
  | 0x2fb6f => some (.immediate 1 10,5)
  | 0x2fb74 => some (.xorRegister 3 3,2)
  | 0x2fb80 => some (.control (.cmpImmediate ⟨some 6,none,0,56⟩ 0),4)
  | 0x2fb84 => some (.control (.jumpZero false 175),6)
  | 0x2fb8a => some (.testMemoryByte ⟨none,none,0,0x2cf80⟩ 31,7)
  | 0x2fb91 => some (.control (.jumpZero false 162),6)
  | 0x2fb97 => some (.immediate 1 5,5)
  | 0x2fb9c => some (.xorRegister 2 2,2)
  | 0x2fb9e => some (.xorRegister 3 3,2)
  | 0x2fbaa => some (.control (.cmpImmediate ⟨some 6,none,0,56⟩ 0),4)
  | 0x2fbae => some (.control (.jumpZero true 14),2)
  | 0x2fbb0 => some (.call (-47701),5)
  | 0x2fbb5 => some (.compareRegister 0 5,3)
  | 0x2fbb8 => some (.jumpSigned 0 123,6)
  | 0x2fbbe => some (.testMemoryByte ⟨none,none,0,0x2cf80⟩ 31,7)
  | 0x2fbc5 => some (.control (.jumpZero false 114),2)
  | 0x2fbc7 => some (.immediate 1 20,5)
  | 0x2fbcc => some (.control (.block (.legacy (.load 0 6 0))),2)
  | 0x2fbce => some (.xorRegister 2 2,2)
  | 0x2fbd0 => some (.xorRegister 3 3,2)
  | 0x24160 => some (.control (.block (.load 0 ⟨none,none,0,0x12720⟩)),5)
  | 0x24165 => some (.addImmediate 0 1,1)
  | 0x24166 => some (.control (.andEax 255),5)
  | 0x2416b => some (.control (.storeEax 0x12720),5)
  | 0x24170 => some (.control (.loadByte 0 ⟨some 0,none,0,0x1261c⟩),6)
  | 0x24176 => some (.control (.andEax 255),5)
  | 0x2417b => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- The byte timing test is exactly the 32-tic gate, including large clocks. -/
theorem clock_mask (time : Nat) :
    ((BitVec.ofNat 8 time &&& (31#8)) == 0) = decide (time % 32 = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq,← BitVec.toNat_inj,BitVec.toNat_and,
    BitVec.toNat_ofNat,BitVec.toNat_zero]
  change (time % 256) &&& (2^5-1) = 0 ↔ _
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 256)]

/-- An individual byte outside a word store survives, including address wrap. -/
theorem byte_store (m : Memory) (a b v : Word)
    (safe : ∀ j : Fin 4, a ≠ b+BitVec.ofNat 32 j.val) : (store32 m b v) a = m a := by
  have h0 : a ≠ b := by simpa using safe 0
  have h1 : a ≠ b+(1#32) := safe 1
  have h2 : a ≠ b+(2#32) := safe 2
  have h3 : a ≠ b+(3#32) := safe 3
  simp [store32] <;> split <;> simp_all

def nextIndex (i : UInt8) : Word := BitVec.ofNat 32 (i+1).toNat

theorem increment_index (i : UInt8) :
    ((BitVec.ofNat 32 i.toNat + (1#32)) &&& (255#32)) = nextIndex i := by
  apply BitVec.eq_of_toNat_eq
  simp only [nextIndex,BitVec.toNat_and,BitVec.toNat_add,BitVec.toNat_ofNat,UInt8.toNat_add,UInt8.toNat_one]
  change ((i.toNat % 4294967296+1%4294967296)%4294967296) &&& (2^8-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := i.toNat_lt
  omega

theorem mask_byte (old : Word) (b : BitVec 8) :
    ((old &&& (0xffffff00#32)) ||| b.zeroExtend 32) &&& (255#32) = b.zeroExtend 32 := by
  change ((old &&& (4294967040#32)) ||| b.zeroExtend 32) &&& (255#32) = b.zeroExtend 32
  dsimp only [Word] at *
  simp only [BitVec.and_or_distrib_right, BitVec.and_assoc]
  simp only [show (4294967040#32) &&& (255#32) = (0#32) from by decide,BitVec.and_zero,BitVec.zero_or]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  change (b.toNat % 4294967296) &&& (2^8-1) = b.toNat % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := b.isLt
  omega

/-- The original immutable table and engine table agree at every index. -/
theorem table_matches : ∀ i : Fin 256,
    (Doom19.randomTableBytes.toArray[i.val]!).toNat = randomAt (UInt8.ofNat i.val) := by decide

def randomMemory (s : X86Memory.State) (i : UInt8) : Memory := store32 s.memory (0x12720#32) (nextIndex i)
def randomEnd (s : X86Memory.State) (i : UInt8) (b : BitVec 8) : X86Control.State :=
  ⟨⟨write (write s.regs 0 (b.zeroExtend 32)) 4 (s.regs 4+(4#32)),randomMemory s i⟩,
    some (logical32 (b.zeroExtend 32)),0x2fbb5⟩

/-- Real P_Random instructions and RET in the shared byte-addressed memory.
Table/return reads are from memory after the index write, so aliasing is never
silently discarded by the instruction proof. -/
theorem random_execution (s : X86Memory.State) (f : Option Flags) (i : UInt8) (b : BitVec 8)
    (index : load32 s.memory (0x12720#32) = BitVec.ofNat 32 i.toNat)
    (table : randomMemory s i ((0x1261c#32)+nextIndex i) = b)
    (ret : load32 (randomMemory s i) (s.regs 4) = (0x2fbb5#32)) :
    X86Routine.run listed [0x2fbb5] 7 ⟨s,f,0x24160⟩ = some (randomEnd s i b) := by
  let c1 := put s 0 (BitVec.ofNat 32 i.toNat)
  let c2 := put c1 0 (BitVec.ofNat 32 i.toNat+1)
  let c3 := put c2 0 (nextIndex i)
  let c4 : X86Memory.State := { c3 with memory := randomMemory s i }
  let c5 := putByte c4 0 b
  let c6 := put c5 0 (b.zeroExtend 32)
  have path : X86Routine.Prefix listed [0x2fbb5] 7 ⟨s,f,0x24160⟩
      ⟨put c6 4 (s.regs 4+4),some (logical32 (b.zeroExtend 32)),0x2fbb5⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x24165⟩) (by simp) (show listed 0x24160 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,c1,index])
    apply X86Routine.Prefix.step (middle := ⟨c2,none,0x24166⟩) (by simp) (show listed 0x24165 = _ from rfl) (by
      simp [X86Routine.execute,c2,c1,put,write])
    apply X86Routine.Prefix.step (middle := ⟨c3,some (logical32 (nextIndex i)),0x2416b⟩) (by simp) (show listed 0x24166 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,c3,c2,c1,put,write,increment_index])
    apply X86Routine.Prefix.step (middle := ⟨c4,some (logical32 (nextIndex i)),0x24170⟩) (by simp) (show listed 0x2416b = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,c4,c3,c2,c1,put,write,randomMemory])
    apply X86Routine.Prefix.step (middle := ⟨c5,some (logical32 (nextIndex i)),0x24176⟩) (by simp) (show listed 0x24170 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,c5,c4,c3,c2,c1,put,write,BitVec.add_comm,table,eax])
    apply X86Routine.Prefix.step (middle := ⟨c6,some (logical32 (b.zeroExtend 32)),0x2417b⟩) (by simp) (show listed 0x24176 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,c6,c5,putByte,byteReg,put,write,mask_byte,eax])
    apply X86Routine.Prefix.step (middle := ⟨put c6 4 (s.regs 4+4),some (logical32 (b.zeroExtend 32)),0x2fbb5⟩)
      (by simp) (show listed 0x2417b = _ from rfl) (by
        simp [X86Routine.execute,c6,c5,c4,c3,c2,c1,putByte,byteReg,put,write,ret])
    exact X86Routine.Prefix.nil _
  rw [show 7 = 7+0 from rfl,path.run 0]
  simp [X86Routine.run,randomEnd,c6,c5,c4,c3,c2,c1,putByte,byteReg,put,write]
  funext r
  by_cases h0 : r=0 <;> by_cases h4 : r=4 <;> simp_all [write]


def zeroFlags : Flags := { (logical32 0) with carry := some false }
def clockFlags (s : X86Memory.State) := logical8 (s.memory (0x2cf80#32) &&& (31#8))
def skip (s : X86Memory.State) (f : Flags) : X86Control.State := ⟨s,some f,0x2fc39⟩
def damage (s : X86Memory.State) (amount pc : Nat) : X86Control.State :=
  ⟨put (put (put s 1 (BitVec.ofNat 32 amount)) 2 0) 3 0,some zeroFlags,pc⟩
def lightEnd (s : X86Memory.State) (kind : Bool) : X86Control.State :=
  let s := if kind then put s 2 (suitWord s) else s
  if suitWord s != (0#32) then skip s (if kind then logical32 (suitWord s) else compare32 (suitWord s) 0)
  else if due s then damage s (if kind then 10 else 5) (if kind then 0x2fb76 else 0x2fba0)
  else skip s (clockFlags s)

def heavyEnd (s : X86Memory.State) : X86Control.State :=
  if due s then damage (put s 0 (load32 s.memory (player s))) 20 0x2fbd2
  else skip s (clockFlags s)

theorem five_clock (s : X86Memory.State) (f : Option Flags) (zero : s.regs 2 = 0) :
    X86Routine.run listed exits 4 ⟨s,f,0x2fb62⟩ = some (if due s then damage s 10 0x2fb76 else skip s (clockFlags s)) := by
  cases hc : due s
  · have hc : (clockFlags s).zero = false := hc
    simp [clockFlags,logical8] at hc
    have path : X86Routine.Prefix listed exits 2 ⟨s,f,0x2fb62⟩ (skip s (clockFlags s)) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fb69⟩)
        (by simp [exits]) (show listed 0x2fb62 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fc39⟩)
        (by simp [exits]) (show listed 0x2fb69 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      exact X86Routine.Prefix.nil _
    have tail : X86Routine.run listed exits 0 (skip s (clockFlags s)) = some (skip s (clockFlags s)) := by rfl
    simpa [heavyEnd,due,clockFlags,logical8,hc] using path.finish tail 4 (by decide)
  · have hc : (clockFlags s).zero = true := hc
    simp [clockFlags,logical8] at hc
    have path : X86Routine.Prefix listed exits 4 ⟨s,f,0x2fb62⟩
        ⟨put (put s 1 10) 3 0,some zeroFlags,0x2fb76⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fb69⟩)
        (by simp [exits]) (show listed 0x2fb62 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fb6f⟩)
        (by simp [exits]) (show listed 0x2fb69 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨put s 1 10,some (clockFlags s),0x2fb74⟩)
        (by simp [exits]) (show listed 0x2fb6f = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨put (put s 1 10) 3 0,some zeroFlags,0x2fb76⟩)
        (by simp [exits]) (show listed 0x2fb74 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      exact X86Routine.Prefix.nil _
    have tail : X86Routine.run listed exits 0 ⟨put (put s 1 10) 3 0,some zeroFlags,0x2fb76⟩ = some ⟨put (put s 1 10) 3 0,some zeroFlags,0x2fb76⟩ := by rfl
    have result := path.finish tail 4 (by decide)
    simp only [heavyEnd,due,clockFlags,logical8] at hc ⊢
    simp only [beq_iff_eq,Bool.true_eq,decide_eq_true_eq,hc,↓reduceIte]
    rw [result]
    congr 2
    simp only [damage,put]
    congr 1
    · funext r
      by_cases h : r = 2 <;> simp_all [damage,put,write]

theorem seven_clock (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed exits 5 ⟨s,f,0x2fb8a⟩ = some (if due s then damage s 5 0x2fba0 else skip s (clockFlags s)) := by
  cases hc : due s
  · have hc : (clockFlags s).zero = false := hc
    simp [clockFlags,logical8] at hc
    have path : X86Routine.Prefix listed exits 2 ⟨s,f,0x2fb8a⟩ (skip s (clockFlags s)) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fb91⟩)
        (by simp [exits]) (show listed 0x2fb8a = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fc39⟩)
        (by simp [exits]) (show listed 0x2fb91 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      exact X86Routine.Prefix.nil _
    have tail : X86Routine.run listed exits 0 (skip s (clockFlags s)) = some (skip s (clockFlags s)) := by rfl
    simpa [heavyEnd,due,clockFlags,logical8,hc] using path.finish tail 5 (by decide)
  · have hc : (clockFlags s).zero = true := hc
    simp [clockFlags,logical8] at hc
    have path : X86Routine.Prefix listed exits 5 ⟨s,f,0x2fb8a⟩
        ⟨put (put (put s 1 5) 2 0) 3 0,some zeroFlags,0x2fba0⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fb91⟩)
        (by simp [exits]) (show listed 0x2fb8a = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fb97⟩)
        (by simp [exits]) (show listed 0x2fb91 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨put s 1 5,some (clockFlags s),0x2fb9c⟩)
        (by simp [exits]) (show listed 0x2fb97 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨put (put s 1 5) 2 0,some zeroFlags,0x2fb9e⟩)
        (by simp [exits]) (show listed 0x2fb9c = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨put (put (put s 1 5) 2 0) 3 0,some zeroFlags,0x2fba0⟩)
        (by simp [exits]) (show listed 0x2fb9e = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      exact X86Routine.Prefix.nil _
    have tail : X86Routine.run listed exits 0 ⟨put (put (put s 1 5) 2 0) 3 0,some zeroFlags,0x2fba0⟩ = some ⟨put (put (put s 1 5) 2 0) 3 0,some zeroFlags,0x2fba0⟩ := by rfl
    have result := path.finish tail 5 (by decide)
    simp only [heavyEnd,due,clockFlags,logical8] at hc ⊢
    simp only [beq_iff_eq,Bool.true_eq,decide_eq_true_eq,hc,↓reduceIte]
    rw [result]
    rfl
theorem heavy_clock (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed exits 6 ⟨s,f,0x2fbbe⟩ = some (heavyEnd s) := by
  cases hc : due s
  · have hc : (clockFlags s).zero = false := hc
    simp [clockFlags,logical8] at hc
    have path : X86Routine.Prefix listed exits 2 ⟨s,f,0x2fbbe⟩ (skip s (clockFlags s)) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fbc5⟩)
        (by simp [exits]) (show listed 0x2fbbe = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fc39⟩)
        (by simp [exits]) (show listed 0x2fbc5 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      exact X86Routine.Prefix.nil _
    have tail : X86Routine.run listed exits 0 (skip s (clockFlags s)) = some (skip s (clockFlags s)) := by rfl
    simpa [heavyEnd,due,clockFlags,logical8,hc] using path.finish tail 6 (by decide)
  · have hc : (clockFlags s).zero = true := hc
    simp [clockFlags,logical8] at hc
    have path : X86Routine.Prefix listed exits 6 ⟨s,f,0x2fbbe⟩
        ⟨put (put (put (put s 1 20) 0 (load32 s.memory (player s))) 2 0) 3 0,some zeroFlags,0x2fbd2⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fbc5⟩)
        (by simp [exits]) (show listed 0x2fbbe = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨s,some (clockFlags s),0x2fbc7⟩)
        (by simp [exits]) (show listed 0x2fbc5 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨put s 1 20,some (clockFlags s),0x2fbcc⟩)
        (by simp [exits]) (show listed 0x2fbc7 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨put (put s 1 20) 0 (load32 s.memory (player s)),some (clockFlags s),0x2fbce⟩)
        (by simp [exits]) (show listed 0x2fbcc = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨put (put (put s 1 20) 0 (load32 s.memory (player s))) 2 0,some zeroFlags,0x2fbd0⟩)
        (by simp [exits]) (show listed 0x2fbce = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put s 1 20) 0 (load32 s.memory (player s))) 2 0) 3 0,some zeroFlags,0x2fbd2⟩)
        (by simp [exits]) (show listed 0x2fbd0 = _ from rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,clockFlags,logical8,logical32,zeroFlags,player,suitWord,hc])
      exact X86Routine.Prefix.nil _
    have tail : X86Routine.run listed exits 0 ⟨put (put (put (put s 1 20) 0 (load32 s.memory (player s))) 2 0) 3 0,some zeroFlags,0x2fbd2⟩ = some ⟨put (put (put (put s 1 20) 0 (load32 s.memory (player s))) 2 0) 3 0,some zeroFlags,0x2fbd2⟩ := by rfl
    have result := path.finish tail 6 (by decide)
    simp only [heavyEnd,due,clockFlags,logical8] at hc ⊢
    simp only [beq_iff_eq,Bool.true_eq,decide_eq_true_eq,hc,↓reduceIte]
    rw [result]
    congr 2
    simp only [damage,put]
    congr 1
    · funext r
      by_cases h : r = 0 <;> by_cases h1 : r = 1 <;> simp_all [damage,put,write]



def lightCore (s : X86Memory.State) (kind : Bool) := if kind then put s 2 (suitWord s) else s
def suitFlags (s : X86Memory.State) := compare32 (suitWord s) 0

theorem light_guard (s : X86Memory.State) (f : Option Flags) (kind : Bool) :
    X86Routine.Prefix listed exits (if kind then 3 else 2)
      ⟨s,f,if kind then 0x2fb57 else 0x2fb80⟩
      ⟨lightCore s kind,some (suitFlags s),
        if suitWord s = (0#32) then (if kind then 0x2fb62 else 0x2fb8a) else 0x2fc39⟩ := by
  cases kind
  · apply X86Routine.Prefix.step (middle := ⟨s,some (suitFlags s),0x2fb84⟩)
      (by simp [exits]) (show listed 0x2fb80 = _ from rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,suitFlags,suitWord,player])
    apply X86Routine.Prefix.step (by simp [exits]) (show listed 0x2fb84 = _ from rfl)
      (show X86Routine.execute _ _ = some _ from ?_) (X86Routine.Prefix.nil _)
    by_cases hs : suitWord s = (0#32) <;>
      simp [X86Routine.execute,X86Control.execute,suitFlags,compare32,hs,lightCore]
  · apply X86Routine.Prefix.step (middle := ⟨put s 2 (suitWord s),f,0x2fb5a⟩)
      (by simp [exits]) (show listed 0x2fb57 = _ from rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
          blockPreservesFlags,suitWord,player])
    apply X86Routine.Prefix.step (middle := ⟨put s 2 (suitWord s),some (suitFlags s),0x2fb5c⟩)
      (by simp [exits]) (show listed 0x2fb5a = _ from rfl) (by
        simp [X86Routine.execute,X86Control.execute,suitFlags,compare32,logical32,put,write,BitVec.ult_eq_decide])
    apply X86Routine.Prefix.step (by simp [exits]) (show listed 0x2fb5c = _ from rfl)
      (show X86Routine.execute _ _ = some _ from ?_) (X86Routine.Prefix.nil _)
    by_cases hs : suitWord s = (0#32) <;>
      simp [X86Routine.execute,X86Control.execute,suitFlags,compare32,hs,lightCore]

theorem light_execution (s : X86Memory.State) (f : Option Flags) (kind : Bool) :
    X86Routine.run listed exits 7 ⟨s,f,if kind then 0x2fb57 else 0x2fb80⟩ = some (lightEnd s kind) := by
  have guard := light_guard s f kind
  by_cases hs : suitWord s = (0#32)
  · simp only [hs,↓reduceIte] at guard
    cases kind
    · have result := guard.finish (seven_clock s (some (suitFlags s))) 7 (by decide)
      simpa [lightEnd,hs] using result
    · have result := guard.finish (five_clock (lightCore s true) (some (suitFlags s))
        (by simp [lightCore,put,write,hs])) 7 (by decide)
      simpa [lightEnd,lightCore,suitWord,player,put,write,show load32 s.memory (s.regs 6+(56#32)) = (0#32) from hs] using result
  · simp only [hs,↓reduceIte] at guard
    have tail : X86Routine.run listed exits 0
        ⟨lightCore s kind,some (suitFlags s),0x2fc39⟩ = some (skip (lightCore s kind) (suitFlags s)) := by rfl
    have result := guard.finish tail 7 (by cases kind <;> decide)
    have hz : load32 s.memory (s.regs 6+(56#32)) ≠ (0#32) := hs
    cases kind <;> simpa [hz,lightEnd,lightCore,suitFlags,logical32,compare32,suitWord,player,put,write,hs,BitVec.ult_eq_decide] using result

/-- Suit presence either enters the clock test directly or calls P_Random first. -/
theorem heavy_guard (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed exits 2 ⟨s,f,0x2fbaa⟩
      ⟨s,some (suitFlags s),if suitWord s = (0#32) then 0x2fbbe else 0x2fbb0⟩ := by
  apply X86Routine.Prefix.step (middle := ⟨s,some (suitFlags s),0x2fbae⟩)
    (by simp [exits]) (show listed 0x2fbaa = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,suitFlags,suitWord,player])
  apply X86Routine.Prefix.step (by simp [exits]) (show listed 0x2fbae = _ from rfl)
    (show X86Routine.execute _ _ = some _ from ?_) (X86Routine.Prefix.nil _)
  by_cases hs : suitWord s = (0#32) <;>
    simp [X86Routine.execute,X86Control.execute,suitFlags,compare32,hs]


def called (s : X86Memory.State) := X86Routine.pushWord s (0x2fbb5#32)
def rolled (s : X86Memory.State) (i : UInt8) (b : BitVec 8) := randomEnd (called s) i b

/-- These are concrete memory-read conditions after two specified word stores,
not assumptions about the result of executing the routine. They expose aliasing
between the CALL stack, RNG index, table, and return address. -/
structure RandomInputs (s : X86Memory.State) (i : UInt8) (b : BitVec 8) : Prop where
  index : load32 (called s).memory (0x12720#32) = BitVec.ofNat 32 i.toNat
  table : randomMemory (called s) i ((0x1261c#32)+nextIndex i) = b
  ret : load32 (randomMemory (called s) i) ((called s).regs 4) = (0x2fbb5#32)

theorem listed_active (pc : Nat) (h : listed pc ≠ none) : pc ∉ exits := by
  fun_cases listed pc <;> simp_all [listed,exits]

theorem random_call_finish (s : X86Memory.State) (f : Option Flags) (i : UInt8) (b : BitVec 8)
    (h : RandomInputs s i b) (n : Nat) (last : X86Control.State)
    (tail : X86Routine.run listed exits n (rolled s i b) = some last) :
    X86Routine.run listed exits (8+n) ⟨s,f,0x2fbb0⟩ = some last := by
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path (random_execution (called s) f i b h.index h.table h.ret)
  have path := path.transfer listed exits (by intros; rfl) listed_active
  have callPath : X86Routine.Prefix listed exits 1 ⟨s,f,0x2fbb0⟩ ⟨called s,f,0x24160⟩ := by
    apply X86Routine.Prefix.step (by simp [exits]) (show listed 0x2fbb0 = _ from rfl)
      (show X86Routine.execute _ _ = some _ from ?_) (X86Routine.Prefix.nil _)
    simp [X86Routine.execute,called]
  exact callPath.finish (path.finish tail (7+n) (by omega)) (8+n) (by omega)

theorem roll_compare (b : BitVec 8) :
    ((compare32 (b.zeroExtend 32) (5#32)).sign == (compare32 (b.zeroExtend 32) (5#32)).overflow) =
      decide (5 ≤ b.toNat) := by
  rw [PlayerHeight.cmp_ge]
  have bound := b.isLt
  simp [BitVec.toInt_setWidth,BitVec.toInt_ofNat,Int.bmod] <;> omega

def rollEnd (s : X86Memory.State) (b : BitVec 8) : X86Control.State :=
  if 5 ≤ b.toNat then skip s (compare32 (b.zeroExtend 32) (5#32)) else heavyEnd s

theorem roll_execution (s : X86Memory.State) (f : Option Flags) (b : BitVec 8)
    (eax : s.regs 0 = b.zeroExtend 32) :
    X86Routine.run listed exits 8 ⟨s,f,0x2fbb5⟩ = some (rollEnd s b) := by
  have guard : X86Routine.Prefix listed exits 2 ⟨s,f,0x2fbb5⟩
      ⟨s,some (compare32 (b.zeroExtend 32) (5#32)),if 5 ≤ b.toNat then 0x2fc39 else 0x2fbbe⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (b.zeroExtend 32) (5#32)),0x2fbb8⟩)
      (by simp [exits]) (show listed 0x2fbb5 = _ from rfl) (by simp [X86Routine.execute,eax])
    apply X86Routine.Prefix.step (by simp [exits]) (show listed 0x2fbb8 = _ from rfl)
      (show X86Routine.execute _ _ = some _ from ?_) (X86Routine.Prefix.nil _)
    have hc : (compare32 (b.zeroExtend 32) (5#32)).sign =
        (compare32 (b.zeroExtend 32) (5#32)).overflow ↔ 5 ≤ b.toNat := by
      simpa only [beq_iff_eq,decide_eq_true_eq] using (Bool.eq_iff_iff.mp (roll_compare b))
    simp only [X86Routine.execute,Option.bind_some]
    by_cases hb : 5 ≤ b.toNat <;> simp [hc,hb]
  by_cases hb : 5 ≤ b.toNat
  · simp only [hb,↓reduceIte] at guard
    exact guard.finish (show X86Routine.run listed exits 0 _ = some (rollEnd s b) by
      simp [X86Routine.run,exits,rollEnd,hb,skip]) 8 (by decide)
  · simp only [hb,↓reduceIte] at guard
    simpa [rollEnd,hb] using guard.finish (heavy_clock s (some (compare32 (b.zeroExtend 32) (5#32)))) 8 (by decide)

def heavyResult (s : X86Memory.State) (i : UInt8) (b : BitVec 8) :=
  if suitWord s = (0#32) then heavyEnd s else rollEnd (rolled s i b).core b

theorem heavy_execution (s : X86Memory.State) (f : Option Flags) (i : UInt8) (b : BitVec 8)
    (h : suitWord s ≠ (0#32) → RandomInputs s i b) :
    X86Routine.run listed exits 18 ⟨s,f,0x2fbaa⟩ = some (heavyResult s i b) := by
  have guard := heavy_guard s f
  by_cases hs : suitWord s = (0#32)
  · simp only [hs,↓reduceIte] at guard
    simpa [heavyResult,hs] using guard.finish (heavy_clock s (some (suitFlags s))) 18 (by decide)
  · simp only [hs,↓reduceIte] at guard
    have roll := roll_execution (rolled s i b).core (rolled s i b).flags b
      (by simp [rolled,randomEnd,write])
    have call := random_call_finish s (some (suitFlags s)) i b (h hs) 8 _ roll
    simpa [heavyResult,hs] using guard.finish call 18 (by decide)


inductive Kind where
  | five | seven | four | sixteen
  deriving DecidableEq

def Kind.special : Kind → Nat
  | .five => 5 | .seven => 7 | .four => 4 | .sixteen => 16

def Kind.entry : Kind → Nat
  | .five => 0x2fb57 | .seven => 0x2fb80 | _ => 0x2fbaa

def randomByte (i : UInt8) : BitVec 8 :=
  (Doom19.randomTableBytes.toArray[(i+1).toNat]!).toBitVec

theorem random_value (i : UInt8) : (randomByte i).toNat = randomAt (i+1) := by
  have h := table_matches ⟨(i+1).toNat,(i+1).toNat_lt⟩
  simpa only [randomByte,UInt8.toNat_toBitVec,UInt8.ofNat_toNat] using h

def result (kind : Kind) (s : X86Memory.State) (rng : DoomRandom) := match kind with
  | .five => lightEnd s true
  | .seven => lightEnd s false
  | _ => heavyResult s rng.play (randomByte rng.play)

theorem execution (kind : Kind) (s : X86Memory.State) (f : Option Flags) (rng : DoomRandom)
    (h : suitWord s ≠ (0#32) → RandomInputs s rng.play (randomByte rng.play)) :
    X86Routine.run program exits 18 ⟨s,f,kind.entry⟩ = some (result kind s rng) := by
  have listedRun : X86Routine.run listed exits 18 ⟨s,f,kind.entry⟩ = some (result kind s rng) := by
    cases kind
    · exact X86Routine.run_mono (light_execution s f true) 11
    · exact X86Routine.run_mono (light_execution s f false) 11
    · exact heavy_execution s f rng.play (randomByte rng.play) h
    · exact heavy_execution s f rng.play (randomByte rng.play) h
  rw [X86Routine.run_sound program listed decoded exits 18 _ (by simp [listedRun]),listedRun]

/-- A layout/encoding contract stated only in terms of the incoming state and
explicit CALL/index stores. The latter must preserve the clock, target pointer,
and presentation RNG index. No game result or run equality is assumed. -/
structure Inputs (s : X86Memory.State) (time : Nat) (suit : Bool) (rng : DoomRandom) : Prop where
  suit : suitWord s = (0#32) ↔ suit = false
  clock : s.memory (0x2cf80#32) = BitVec.ofNat 8 time
  index : load32 s.memory (0x12720#32) = BitVec.ofNat 32 rng.play.toNat
  misc : load32 s.memory (0x1271c#32) = BitVec.ofNat 32 rng.misc.toNat
  target : s.regs 0 = load32 s.memory (player s)
  random : suitWord s ≠ (0#32) → RandomInputs s rng.play (randomByte rng.play)
  clockSafe : randomMemory (called s) rng.play (0x2cf80#32) = s.memory (0x2cf80#32)
  targetSafe : load32 (randomMemory (called s) rng.play) (player s) = load32 s.memory (player s)
  miscSafe : load32 (randomMemory (called s) rng.play) (0x1271c#32) = load32 s.memory (0x1271c#32)

def requested (t : X86Control.State) : Nat := if t.pc = 0x2fc39 then 0 else (t.core.regs 1).toNat

def observe (t : X86Control.State) : Nat × Word × Word :=
  (requested t, load32 t.core.memory (0x12720#32),load32 t.core.memory (0x1271c#32))

/-- All four floor kinds agree with the live helper at the damage-call boundary.
The caller supplies the on-floor premise; dispatch and damage side effects are
separate composition obligations. -/
theorem result_observation (kind : Kind) (s : X86Memory.State) (time : Nat)
    (suit : Bool) (rng : DoomRandom) (z floor : Fixed) (onFloor : z = floor)
    (h : Inputs s time suit rng) :
    observe (result kind s rng) =
      let answer := LevelSpecials.floorDamage kind.special z floor suit time rng
      (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat) := by
  have clock : due s = decide (time%32=0) := by rw [due,h.clock,clock_mask]
  have clockAfter : due (rolled s rng.play (randomByte rng.play)).core = decide (time%32=0) := by
    simpa [due,rolled,randomEnd,h.clockSafe,h.clock] using clock_mask time
  have hi := h.index
  have hm := h.misc
  have hmSafe := h.miscSafe
  have self : (floor != floor) = false := by change (!(floor.raw == floor.raw)) = false; simp
  have hz := h.suit
  subst z
  cases kind <;> cases suit <;>
    simp at hz <;>
    by_cases ht : time%32=0 <;> by_cases hb : (randomByte rng.play).toNat < 5 <;>
    simp [result,lightEnd,heavyResult,rollEnd,heavyEnd,observe,requested,damage,skip,
      Kind.special,LevelSpecials.floorDamage,DoomRandom.nextPlay,self,
      hz,clock,clockAfter,ht,hb,show (randomByte rng.play).toNat = randomAt (rng.play+1) from random_value _,
      lightCore,put,write,player,suitWord,due,rolled,randomEnd,randomMemory,
      h.index,h.misc,h.miscSafe,h.clockSafe,h.clock,load_store,nextIndex] at * <;>
    simp_all [← Nat.not_lt,h.index,h.misc,randomMemory,load_store,write,Id.run]

theorem correspondence (kind : Kind) (s : X86Memory.State) (f : Option Flags)
    (time : Nat) (suit : Bool) (rng : DoomRandom) (z floor : Fixed) (onFloor : z = floor)
    (h : Inputs s time suit rng) :
    (X86Routine.run program exits 18 ⟨s,f,kind.entry⟩).map observe =
      let answer := LevelSpecials.floorDamage kind.special z floor suit time rng
      some (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat) := by
  rw [execution kind s f rng h.random,Option.map_some,result_observation kind s time suit rng z floor onFloor h]


/-- The complete memory effect before entering P_DamageMobj: either no writes,
or the RNG call's return-address store followed by its index store. -/
theorem memory_frame (kind : Kind) (s : X86Memory.State) (rng : DoomRandom) :
    (result kind s rng).core.memory =
      if (kind = .four ∨ kind = .sixteen) ∧ suitWord s ≠ (0#32)
      then randomMemory (called s) rng.play else s.memory := by
  cases kind <;> by_cases hs : suitWord s = (0#32) <;>
    simp only [result,lightEnd,heavyResult,rollEnd,heavyEnd,damage,skip,put] <;>
    repeat' split <;> simp_all [suitWord,player,put,write,rolled,randomEnd]

theorem stack_preserved (kind : Kind) (s : X86Memory.State) (rng : DoomRandom) :
    (result kind s rng).core.regs 4 = s.regs 4 := by
  cases kind <;> by_cases hs : suitWord s = (0#32) <;>
    simp [result,lightEnd,heavyResult,rollEnd,heavyEnd,damage,skip,hs,put,suitWord,player,
      rolled,randomEnd,called,X86Routine.pushWord,write,BitVec.sub_add_cancel] <;>
    repeat' split <;> simp_all [damage,skip,put,rolled,randomEnd,write,suitWord,player,called,X86Routine.pushWord,BitVec.sub_add_cancel]

/-- A nonzero request reaches a real original CALL to P_DamageMobj, with the
player object as target and both environmental-damage source pointers null. -/
theorem damage_arguments (kind : Kind) (s : X86Memory.State) (time : Nat)
    (suit : Bool) (rng : DoomRandom) (h : Inputs s time suit rng)
    (damageDue : requested (result kind s rng) ≠ 0) :
    let t := result kind s rng
    t.core.regs 0 = load32 s.memory (player s) ∧
    t.core.regs 2 = (0#32) ∧ t.core.regs 3 = (0#32) ∧
    program t.pc = some (.call ((0x2a460 : Int) - (t.pc+5)),5) := by
  have ht := h.target
  have htSafe := h.targetSafe
  cases kind <;> by_cases hs : suitWord s = (0#32) <;>
    simp [result,lightEnd,heavyResult,rollEnd,heavyEnd,requested,damage,skip,hs,put,
      suitWord,player,rolled,randomEnd,write,called,X86Routine.pushWord] at * <;>
    repeat' split at * <;> simp_all [requested,damage,skip,put,write,player,rolled,randomEnd,called,X86Routine.pushWord]
  all_goals try simp_all [requested,damage,skip,put,write,player,rolled,randomEnd,called,X86Routine.pushWord]
  all_goals first | omega | decide

end Doom.Proofs.FloorDamage

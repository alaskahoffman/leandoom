import Doom.Proofs.OriginalWeaponLower
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponDrop
open Verification X86 X86Memory X86Control BlockSummary
def dropCode : List UInt8 := [0x53,0x52,0x89,0xc2,0x8b,0x58,0x70,0x8d,0x4,0x9d,0x0,0x0,0x0,0x0,0x29,0xd8,0x8b,0x1c,0xc5,0x98,0x2d,0x1,0x0,0x89,0xd0,0x31,0xd2,0xe8,0x60,0xfd,0xff,0xff,0x5a,0x5b,0xc3]
def setterCode : List UInt8 := [0x51,0x56,0x89,0xc6,0x89,0xd8,0xc1,0xe2,0x4,0x8d,0x9e,0xf4,0x0,0x0,0x0,0x1,0xd3,0x85,0xc0,0x75,0x9,0xc7,0x3,0x0,0x0,0x0,0x0,0x5e,0x59,0xc3,0x6b,0xc0,0x1c,0xb9,0x28,0x5a,0x1,0x0,0x1,0xc1,0x89,0xb,0x8b,0x41,0x8,0x89,0x43,0x4,0x8b,0x51,0x14,0x85,0xd2,0x74,0x11,0x89,0xd0,0xc1,0xe0,0x10,0x89,0x43,0x8,0x8b,0x41,0x18,0xc1,0xe0,0x10,0x89,0x43,0xc,0x83,0x79,0xc,0x0,0x74,0xc,0x89,0xf0,0x89,0xda,0xff,0x51,0xc,0x83,0x3b,0x0,0x74,0x12,0x8b,0x3,0x8b,0x53,0x4,0x8b,0x40,0x10,0x85,0xd2,0x75,0x6,0x85,0xc0,0x74,0xab,0xeb,0xb2,0x5e,0x59,0xc3]
def bytesProgram (drop setter lower : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d2c0 ≤ pc ∧ pc < 0x2d2e3 then X86Routine.decodeAt drop (pc-0x2d2c0)
  else if 0x2d040 ≤ pc ∧ pc < 0x2d0af then X86Routine.decodeAt setter (pc-0x2d040)
  else WeaponLower.bytesProgram lower pc
def program := bytesProgram dropCode setterCode WeaponLower.code

def listed : X86Routine.Program
  | 0x2d2c0 => some (.push 3,1)
  | 0x2d2c1 => some (.push 2,1)
  | 0x2d2c2 => some (.control (.block (.legacy (.mov 2 0))),2)
  | 0x2d2c4 => some (.control (.block (.legacy (.load 3 0 112))),3)
  | 0x2d2c7 => some (.control (.block (.lea 0 ⟨none,some 3,2,0⟩)),7)
  | 0x2d2ce => some (.control (.block (.arithmetic (.sub 0 3))),2)
  | 0x2d2d0 => some (.control (.block (.load 3 ⟨none,some 0,3,0x12d98⟩)),7)
  | 0x2d2d7 => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2d2d9 => some (.xorRegister 2 2,2)
  | 0x2d2db => some (.call (-672),5)
  | 0x2d2e0 => some (.pop 2,1)
  | 0x2d2e1 => some (.pop 3,1)
  | 0x2d2e2 => some (.ret,1)
  | 0x2d040 => some (.push 1,1)
  | 0x2d041 => some (.push 6,1)
  | 0x2d042 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2d044 => some (.control (.block (.legacy (.mov 0 3))),2)
  | 0x2d046 => some (.control (.block (.legacy (.shl 2 4))),3)
  | 0x2d049 => some (.control (.block (.lea 3 ⟨some 6,none,0,244⟩)),6)
  | 0x2d04f => some (.control (.block (.arithmetic (.add 3 2))),2)
  | 0x2d051 => some (.control (.testWord 0 0),2)
  | 0x2d053 => some (.control (.jumpZero false 9),2)
  | 0x2d05e => some (.multiplyImmediate 0 0 28,3)
  | 0x2d061 => some (.immediate 1 0x15a28,5)
  | 0x2d066 => some (.control (.block (.arithmetic (.add 1 0))),2)
  | 0x2d068 => some (.control (.block (.store ⟨some 3,none,0,0⟩ 1)),2)
  | 0x2d06a => some (.control (.block (.legacy (.load 0 1 8))),3)
  | 0x2d06d => some (.control (.block (.store ⟨some 3,none,0,4⟩ 0)),3)
  | 0x2d070 => some (.control (.block (.legacy (.load 2 1 20))),3)
  | 0x2d073 => some (.control (.testWord 2 2),2)
  | 0x2d075 => some (.control (.jumpZero true 17),2)
  | 0x2d088 => some (.control (.cmpImmediate ⟨some 1,none,0,12⟩ 0),4)
  | 0x2d08c => some (.control (.jumpZero true 12),2)
  | 0x2d08e => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2d090 => some (.control (.block (.legacy (.mov 2 3))),2)
  | 0x2d092 => some (.callMemory ⟨some 1,none,0,12⟩,3)
  | 0x2d095 => some (.control (.cmpImmediate ⟨some 3,none,0,0⟩ 0),3)
  | 0x2d098 => some (.control (.jumpZero true 18),2)
  | 0x2d09a => some (.control (.block (.legacy (.load 0 3 0))),2)
  | 0x2d09c => some (.control (.block (.legacy (.load 2 3 4))),3)
  | 0x2d09f => some (.control (.block (.legacy (.load 0 0 16))),3)
  | 0x2d0a2 => some (.control (.testWord 2 2),2)
  | 0x2d0a4 => some (.control (.jumpZero false 6),2)
  | 0x2d0ac => some (.pop 6,1)
  | 0x2d0ad => some (.pop 1,1)
  | 0x2d0ae => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def down (w : Fin 3) : Word := BitVec.ofNat 32 (3+8*w.val)
def state (w : Fin 3) : Word := 0x15a28+down w*28
def info (w : Fin 3) : Word := 0x12d98+BitVec.ofNat 32 (24*w.val)
def psp (s : X86Memory.State) : Word := s.regs 0+(244#32)
def saves (s : X86Memory.State) : Memory :=
  store32 (store32 s.memory (s.regs 4-(4#32)) (s.regs 3)) (s.regs 4-(8#32)) (s.regs 2)
def dropMemory (s : X86Memory.State) : Memory := store32 (saves s) (s.regs 4-(12#32)) 0x2d2e0
def setterMemory (s : X86Memory.State) : Memory :=
  store32 (store32 (dropMemory s) (s.regs 4-(16#32)) (s.regs 1)) (s.regs 4-(20#32)) (s.regs 6)
def installed (s : X86Memory.State) (w : Fin 3) : Memory :=
  store32 (store32 (setterMemory s) (psp s) (state w)) (psp s+(4#32)) 1
def actionMemory (s : X86Memory.State) (w : Fin 3) : Memory :=
  store32 (installed s w) (s.regs 4-(24#32)) 0x2d095

def dispatched (s : X86Memory.State) (w : Fin 3) : X86Control.State :=
  ⟨⟨write (write (write s.regs 2 0) 3 (down w)) 4 (s.regs 4-(12#32)),dropMemory s⟩,
    some {(logical32 0) with carry := some false},0x2d040⟩
def action (s : X86Memory.State) (w : Fin 3) : X86Memory.State :=
  ⟨write (write (write (write (write s.regs 1 (state w)) 2 (psp s)) 3 (psp s))
    4 (s.regs 4-(24#32))) 6 (s.regs 0),actionMemory s w⟩

/-- All words read or written by the dead-player path. Separation is a
byte-range property, so unaligned and wrapping addresses are covered too. -/
def location (s : X86Memory.State) (w : Fin 3) (n : Fin 18) : Word := match n.val with
  | 0 => s.regs 0+(4#32)
  | 1 => s.regs 0+(112#32)
  | 2 => psp s+(12#32)
  | 3 => psp s
  | 4 => psp s+(4#32)
  | 5 => info w
  | 6 => state w+8
  | 7 => state w+20
  | 8 => state w+12
  | 9 => state w+16
  | 10 => s.regs 4
  | 11 => s.regs 4-(4#32)
  | 12 => s.regs 4-(8#32)
  | 13 => s.regs 4-(12#32)
  | 14 => s.regs 4-(16#32)
  | 15 => s.regs 4-(20#32)
  | 16 => s.regs 4-(24#32)
  | _ => s.regs 4-(28#32)
structure Inputs (s : X86Memory.State) (w : Fin 3) (y : Fixed) : Prop where
  dead : load32 s.memory (location s w 0)=1
  ready : load32 s.memory (location s w 1)=BitVec.ofNat 32 w.val
  height : load32 s.memory (location s w 2)=y.raw.toBitVec
  downState : load32 s.memory (location s w 5)=down w
  tics : load32 s.memory (location s w 6)=1
  misc : load32 s.memory (location s w 7)=0
  callback : load32 s.memory (location s w 8)=0x2d490
  next : load32 s.memory (location s w 9)=down w
  ret : load32 s.memory (location s w 10)=0x2a38c
  separate : ∀ a b : Fin 18, a≠b → Apart (location s w a) (location s w b)

theorem read_store (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y)
    (m : Memory) (i j : Fin 18) (v : Word) :
    load32 (store32 m (location s w i) v) (location s w j) =
      if j=i then v else load32 m (location s w j) := by
  by_cases eq : j=i
  · subst j; simp [load_store]
  · rw [if_neg eq]; exact load_store_apart _ _ _ _ (h.separate j i eq)

theorem read_saves (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y) (n : Fin 18) :
    load32 (saves s) (location s w n) = if n=12 then s.regs 2 else (if n=11 then s.regs 3 else (load32 s.memory (location s w n))) := by
  change load32 (store32 (store32 (s.memory) (location s w 11) (s.regs 3)) (location s w 12) (s.regs 2)) (location s w n) = _
  simp only [read_store s w y h]

theorem read_setterMemory (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y) (n : Fin 18) :
    load32 (setterMemory s) (location s w n) = if n=15 then s.regs 6 else (if n=14 then s.regs 1 else (if n=13 then 0x2d2e0 else (if n=12 then s.regs 2 else (if n=11 then s.regs 3 else (load32 s.memory (location s w n)))))) := by
  change load32 (store32 (store32 (store32 (store32 (store32 (s.memory) (location s w 11) (s.regs 3)) (location s w 12) (s.regs 2)) (location s w 13) (0x2d2e0)) (location s w 14) (s.regs 1)) (location s w 15) (s.regs 6)) (location s w n) = _
  simp only [read_store s w y h]

theorem read_installed (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y) (n : Fin 18) :
    load32 (installed s w) (location s w n) = if n=4 then 1 else (if n=3 then state w else (if n=15 then s.regs 6 else (if n=14 then s.regs 1 else (if n=13 then 0x2d2e0 else (if n=12 then s.regs 2 else (if n=11 then s.regs 3 else (load32 s.memory (location s w n)))))))) := by
  change load32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (s.memory) (location s w 11) (s.regs 3)) (location s w 12) (s.regs 2)) (location s w 13) (0x2d2e0)) (location s w 14) (s.regs 1)) (location s w 15) (s.regs 6)) (location s w 3) (state w)) (location s w 4) (1)) (location s w n) = _
  simp only [read_store s w y h]

theorem read_actionMemory (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y) (n : Fin 18) :
    load32 (actionMemory s w) (location s w n) = if n=16 then 0x2d095 else (if n=4 then 1 else (if n=3 then state w else (if n=15 then s.regs 6 else (if n=14 then s.regs 1 else (if n=13 then 0x2d2e0 else (if n=12 then s.regs 2 else (if n=11 then s.regs 3 else (load32 s.memory (location s w n))))))))) := by
  change load32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (s.memory) (location s w 11) (s.regs 3)) (location s w 12) (s.regs 2)) (location s w 13) (0x2d2e0)) (location s w 14) (s.regs 1)) (location s w 15) (s.regs 6)) (location s w 3) (state w)) (location s w 4) (1)) (location s w 16) (0x2d095)) (location s w n) = _
  simp only [read_store s w y h]

theorem dispatch (s : X86Memory.State) (f : Option Flags) (w : Fin 3)
    (ready : load32 (saves s) (s.regs 0+(112#32))=BitVec.ofNat 32 w.val)
    (table : load32 (saves s) (info w)=down w) :
    X86Routine.run listed [0x2d040] 10 ⟨s,f,0x2d2c0⟩=some (dispatched s w) := by
  have calcInfo : (((BitVec.ofNat 32 w.val <<< 2)-BitVec.ofNat 32 w.val) <<< 3)+(0x12d98#32)=info w := by
    rcases w with ⟨w,hw⟩; have hc : w=0 ∨ w=1 ∨ w=2 := by omega
    rcases hc with rfl|rfl|rfl <;> simp only [info,Fin.val_mk] <;> decide
  simp only [saves] at ready table
  let c1 := X86Routine.pushWord s (s.regs 3)
  let c2 := X86Routine.pushWord c1 (s.regs 2)
  let c3 := put c2 2 (s.regs 0)
  let c4 := put c3 3 (BitVec.ofNat 32 w.val)
  let c5 := put c4 0 (BitVec.ofNat 32 w.val <<< 2)
  let c6 := put c5 0 ((BitVec.ofNat 32 w.val <<< 2)-BitVec.ofNat 32 w.val)
  let c7 := put c6 3 (down w)
  let c8 := put c7 0 (s.regs 0)
  let c9 := put c8 2 0
  have path : X86Routine.Prefix listed [0x2d040] 10 ⟨s,f,0x2d2c0⟩ (dispatched s w) := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2d2c1⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,BitVec.sub_sub,saves,calcInfo,ready,table])

    apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2d2c2⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,BitVec.sub_sub,saves,calcInfo,ready,table])

    apply X86Routine.Prefix.step (middle := ⟨c3,f,0x2d2c4⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,BitVec.sub_sub,saves,calcInfo,ready,table])

    apply X86Routine.Prefix.step (middle := ⟨c4,f,0x2d2c7⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,BitVec.sub_sub,saves,calcInfo,ready,table])

    apply X86Routine.Prefix.step (middle := ⟨c5,f,0x2d2ce⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,BitVec.sub_sub,saves,calcInfo,ready,table])

    apply X86Routine.Prefix.step (middle := ⟨c6,none,0x2d2d0⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,BitVec.sub_sub,saves,calcInfo,ready,table])

    apply X86Routine.Prefix.step (middle := ⟨c7,none,0x2d2d7⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,BitVec.sub_sub,saves,calcInfo,ready,table])

    apply X86Routine.Prefix.step (middle := ⟨c8,none,0x2d2d9⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,BitVec.sub_sub,saves,calcInfo,ready,table])

    apply X86Routine.Prefix.step (middle := ⟨c9,some {(logical32 0) with carry := some false},0x2d2db⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,BitVec.sub_sub,saves,calcInfo,ready,table])

    apply X86Routine.Prefix.step (middle := dispatched s w) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,BitVec.sub_sub,saves,calcInfo,ready,table,dispatched,dropMemory]
      funext r
      by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [write])
    exact X86Routine.Prefix.nil _
  exact path.finish (fuel := 0) (by simp [X86Routine.run,dispatched]) 10 (by decide)

private theorem write_shadow (rs : Registers) (i : Reg) (a b : Word) :
    write (write rs i a) i b=write rs i b := by
  funext r; by_cases eq : r=i <;> simp [write,eq]

theorem setter_prefix (s : X86Memory.State) (w : Fin 3)
    (tics : load32 (store32 (setterMemory s) (psp s) (state w)) (state w+8)=1)
    (misc : load32 (installed s w) (state w+20)=0)
    (callback : load32 (installed s w) (state w+12)=0x2d490) :
    X86Routine.run listed [0x2d490] 23 (dispatched s w)=
      some ⟨action s w,some (compare32 0x2d490 0),0x2d490⟩ := by
  have nonzero : down w ≠ (0#32) := by
    rcases w with ⟨w,hw⟩; have hc : w=0 ∨ w=1 ∨ w=2 := by omega
    rcases hc with rfl|rfl|rfl <;> simp [down]
  simp [installed,setterMemory,dropMemory,saves,psp,state,BitVec.add_assoc] at tics misc callback
  let c1 : X86Memory.State := X86Routine.pushWord (dispatched s w).core (s.regs 1)
  let c2 : X86Memory.State := X86Routine.pushWord c1 (s.regs 6)
  let c3 : X86Memory.State := put c2 6 (s.regs 0)
  let c4 : X86Memory.State := put c3 0 (down w)
  let c5 : X86Memory.State := put c4 2 0
  let c6 : X86Memory.State := put c5 3 (psp s)
  let c7 : X86Memory.State := c6
  let c8 : X86Memory.State := c7
  let c9 : X86Memory.State := c8
  let c10 : X86Memory.State := put c9 0 (down w*28)
  let c11 : X86Memory.State := put c10 1 0x15a28
  let c12 : X86Memory.State := put c11 1 (state w)
  let c13 : X86Memory.State := {c12 with memory := store32 (setterMemory s) (psp s) (state w)}
  let c14 : X86Memory.State := put c13 0 1
  let c15 : X86Memory.State := {c14 with memory := installed s w}
  let c16 : X86Memory.State := put c15 2 0
  let c17 : X86Memory.State := c16
  let c18 : X86Memory.State := c17
  let c19 : X86Memory.State := c18
  let c20 : X86Memory.State := c19
  let c21 : X86Memory.State := put c20 0 (s.regs 0)
  let c22 : X86Memory.State := put c21 2 (psp s)
  have path : X86Routine.Prefix listed [0x2d490] 23 (dispatched s w)
      ⟨action s w,some (compare32 0x2d490 0),0x2d490⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,some {(logical32 0) with carry := some false},0x2d041⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c2,some {(logical32 0) with carry := some false},0x2d042⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c3,some {(logical32 0) with carry := some false},0x2d044⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c4,some {(logical32 0) with carry := some false},0x2d046⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c5,none,0x2d049⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c6,none,0x2d04f⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c7,none,0x2d051⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c8,some (logical32 (down w)),0x2d053⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c9,some (logical32 (down w)),0x2d05e⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c10,none,0x2d061⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c11,none,0x2d066⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c12,none,0x2d068⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c13,none,0x2d06a⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c14,none,0x2d06d⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c15,none,0x2d070⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c16,none,0x2d073⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c17,some (logical32 0),0x2d075⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c18,some (logical32 0),0x2d088⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c19,some (compare32 0x2d490 0),0x2d08c⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c20,some (compare32 0x2d490 0),0x2d08e⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c21,some (compare32 0x2d490 0),0x2d090⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨c22,some (compare32 0x2d490 0),0x2d092⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback])
    apply X86Routine.Prefix.step (middle := ⟨action s w,some (compare32 0x2d490 0),0x2d490⟩) (by simp [dispatched]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,
        c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,dispatched,action,actionMemory,installed,setterMemory,dropMemory,saves,psp,
        write_shadow,state,BitVec.sub_sub,BitVec.add_assoc,logical32,cmp32_zero,nonzero,tics,misc,callback]
      funext r
      by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
        by_cases h4 : r=4 <;> by_cases h6 : r=6 <;> simp_all [write])
    exact X86Routine.Prefix.nil _
  exact path.finish (fuel := 0) (by simp [X86Routine.run]) 23 (by decide)

end Doom.Proofs.WeaponDrop

import Doom.Proofs.OriginalThingCallback
import Doom.Proofs.OriginalDivlineSide
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalThingDiagonal
open Verification X86 X86Memory X86Control BlockSummary
def thingDiagonal : List UInt8 := [0xa1,0x18,0xba,0x2,0x0,0x33,0x5,0x1c,0xba,0x2,0x0,0x85,0xc0,0xf,0x9f,0xc0,0x25,0xff,0x0,0x0,0x0,0x74,0x22,0x8b,0x79,0xc,0x8b,0x71,0x40,0x8b,0x69,0x40,0x8b,0x41,0xc,0x89,0xeb,0x29,0xf7,0x8b,0x71,0x10,0x1,0xe8,0x1,0xee,0x8b,0x69,0x10,0x89,0x44,0x24,0x14,0x29,0xdd,0xeb,0x1b,0x8b,0x79,0xc,0x8b,0x59,0x40,0x8b,0x71,0x10,0x8b,0x41,0xc,0x8b,0x69,0x10,0x29,0xdf,0x29,0xde,0x1,0xd8,0x1,0xdd,0x89,0x44,0x24,0x14,0xbb,0x10,0xba,0x2,0x0,0x89,0xf8,0x89,0xf2,0xe8,0x53,0xfa,0xff,0xff]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c72b≤pc ∧ pc<0x2c78d then X86Routine.decodeAt bytes (pc-0x2c72b) else none
def program := bytesProgram thingDiagonal
def listed : X86Routine.Program
  | 0x2c72b => some (.control (.block (.load 0 ⟨none,none,0,0x2ba18⟩)),5)
  | 0x2c730 => some (.xorMemory 0 ⟨none,none,0,0x2ba1c⟩,6)
  | 0x2c736 => some (.control (.testWord 0 0),2)
  | 0x2c738 => some (.setGreater 0,3)
  | 0x2c73b => some (.control (.andEax 255),5)
  | 0x2c740 => some (.control (.jumpZero true 34),2)
  | 0x2c742 => some (.control (.block (.legacy (.load 7 1 12))),3)
  | 0x2c745 => some (.control (.block (.legacy (.load 6 1 64))),3)
  | 0x2c748 => some (.control (.block (.legacy (.load 5 1 64))),3)
  | 0x2c74b => some (.control (.block (.legacy (.load 0 1 12))),3)
  | 0x2c74e => some (.control (.block (.legacy (.mov 3 5))),2)
  | 0x2c750 => some (.control (.block (.arithmetic (.sub 7 6))),2)
  | 0x2c752 => some (.control (.block (.legacy (.load 6 1 16))),3)
  | 0x2c755 => some (.control (.block (.arithmetic (.add 0 5))),2)
  | 0x2c757 => some (.control (.block (.arithmetic (.add 6 5))),2)
  | 0x2c759 => some (.control (.block (.legacy (.load 5 1 16))),3)
  | 0x2c75c => some (.control (.block (.store ⟨some 4,none,0,20⟩ 0)),4)
  | 0x2c760 => some (.control (.block (.arithmetic (.sub 5 3))),2)
  | 0x2c762 => some (.jump 27,2)
  | 0x2c764 => some (.control (.block (.legacy (.load 7 1 12))),3)
  | 0x2c767 => some (.control (.block (.legacy (.load 3 1 64))),3)
  | 0x2c76a => some (.control (.block (.legacy (.load 6 1 16))),3)
  | 0x2c76d => some (.control (.block (.legacy (.load 0 1 12))),3)
  | 0x2c770 => some (.control (.block (.legacy (.load 5 1 16))),3)
  | 0x2c773 => some (.control (.block (.arithmetic (.sub 7 3))),2)
  | 0x2c775 => some (.control (.block (.arithmetic (.sub 6 3))),2)
  | 0x2c777 => some (.control (.block (.arithmetic (.add 0 3))),2)
  | 0x2c779 => some (.control (.block (.arithmetic (.add 5 3))),2)
  | 0x2c77b => some (.control (.block (.store ⟨some 4,none,0,20⟩ 0)),4)
  | 0x2c77f => some (.immediate 3 0x2ba10,5)
  | 0x2c784 => some (.control (.block (.legacy (.mov 0 7))),2)
  | 0x2c786 => some (.control (.block (.legacy (.mov 2 6))),2)
  | 0x2c788 => some (.call (-1453),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def xor (s : X86Memory.State) := load32 s.memory (0x2ba18#32) ^^^ load32 s.memory (0x2ba1c#32)
def positive (s : X86Memory.State) : Bool := decide (0<(xor s).toInt)
def bit (s : X86Memory.State) : Word := if positive s then 1 else 0
def g1 (s : X86Memory.State) := put s 0 (load32 s.memory (0x2ba18#32))
def g2 (s : X86Memory.State) := put s 0 (xor s)
def g3 (s : X86Memory.State) := putByte (g2 s) 0 (if positive s then 1 else 0)
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨put s 0 (bit s),some (logical32 (bit s)),if positive s then 0x2c742 else 0x2c764⟩

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2c72b⟩ (gate s) := by
  have path : X86Routine.Prefix listed [] 6 ⟨s,f,0x2c72b⟩ (gate s) := by
    apply X86Routine.Prefix.step (middle := ⟨g1 s,f,0x2c730⟩) (by simp) (by rfl) (by simp [g1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags])
    apply X86Routine.Prefix.step (middle := ⟨g2 s,some (logical32 (xor s)),0x2c736⟩) (by simp) (by rfl) (by simp [g2,g1,xor,X86Routine.execute,X86Block.Address.eval,put,write,OriginalLineSide.write_overwrite])
    apply X86Routine.Prefix.step (middle := ⟨g2 s,some (logical32 (xor s)),0x2c738⟩) (by simp) (by rfl) (by simp [g2,X86Routine.execute,X86Control.execute,put,write])
    apply X86Routine.Prefix.step (middle := ⟨g3 s,some (logical32 (xor s)),0x2c73b⟩) (by simp) (by rfl) (by simp [g3,positive,X86Routine.execute,PlayerHeight.logical_le,Int.not_le])
    apply X86Routine.Prefix.step (middle := ⟨(gate s).core,(gate s).flags,0x2c740⟩) (by simp) (by rfl) (by
      have m0 : (xor s &&& (0xffffff00#32)) &&& (255#32)=(0#32) := by
        simpa using OriginalLineSide.mask_byte (xor s) (0#8)
      have m1 : ((xor s &&& (0xffffff00#32)) ||| (1#32)) &&& (255#32)=(1#32) := by
        simpa using OriginalLineSide.mask_byte (xor s) (1#8)
      cases h : positive s <;> simp [gate,bit,g3,g2,h,m0,m1,X86Routine.execute,X86Control.execute,putByte,byteReg,put,write,eax,OriginalLineSide.mask_byte,OriginalLineSide.write_overwrite])
    apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
      cases h : positive s <;> simp [gate,bit,h,X86Routine.execute,X86Control.execute,logical32])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def p1 (s : X86Memory.State) : X86Memory.State := put s 7 (load32 s.memory (s.regs 1+(12#32)))
def p2 (s : X86Memory.State) : X86Memory.State := put (p1 s) 6 (load32 (p1 s).memory ((p1 s).regs 1+(64#32)))
def p3 (s : X86Memory.State) : X86Memory.State := put (p2 s) 5 (load32 (p2 s).memory ((p2 s).regs 1+(64#32)))
def p4 (s : X86Memory.State) : X86Memory.State := put (p3 s) 0 (load32 (p3 s).memory ((p3 s).regs 1+(12#32)))
def p5 (s : X86Memory.State) : X86Memory.State := put (p4 s) 3 ((p4 s).regs 5)
def p6 (s : X86Memory.State) : X86Memory.State := put (p5 s) 7 ((p5 s).regs 7-(p5 s).regs 6)
def p7 (s : X86Memory.State) : X86Memory.State := put (p6 s) 6 (load32 (p6 s).memory ((p6 s).regs 1+(16#32)))
def p8 (s : X86Memory.State) : X86Memory.State := put (p7 s) 0 ((p7 s).regs 0+(p7 s).regs 5)
def p9 (s : X86Memory.State) : X86Memory.State := put (p8 s) 6 ((p8 s).regs 6+(p8 s).regs 5)
def p10 (s : X86Memory.State) : X86Memory.State := put (p9 s) 5 (load32 (p9 s).memory ((p9 s).regs 1+(16#32)))
def p11 (s : X86Memory.State) : X86Memory.State := {(p10 s) with memory:=store32 (p10 s).memory ((p10 s).regs 4+(20#32)) ((p10 s).regs 0)}
def p12 (s : X86Memory.State) : X86Memory.State := put (p11 s) 5 ((p11 s).regs 5-(p11 s).regs 3)
theorem p_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 13 ⟨s,f,0x2c742⟩ ⟨p12 s,none,0x2c77f⟩ := by
  have path : X86Routine.Prefix listed [] 13 ⟨s,f,0x2c742⟩ ⟨p12 s,none,0x2c77f⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨p1 s,f,0x2c745⟩) (by simp) (by rfl) (by simp [p1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p2 s,f,0x2c748⟩) (by simp) (by rfl) (by simp [p1,p2,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p3 s,f,0x2c74b⟩) (by simp) (by rfl) (by simp [p1,p2,p3,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p4 s,f,0x2c74e⟩) (by simp) (by rfl) (by simp [p1,p2,p3,p4,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p5 s,f,0x2c750⟩) (by simp) (by rfl) (by simp [p1,p2,p3,p4,p5,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p6 s,none,0x2c752⟩) (by simp) (by rfl) (by simp [p1,p2,p3,p4,p5,p6,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p7 s,none,0x2c755⟩) (by simp) (by rfl) (by simp [p1,p2,p3,p4,p5,p6,p7,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p8 s,none,0x2c757⟩) (by simp) (by rfl) (by simp [p1,p2,p3,p4,p5,p6,p7,p8,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p9 s,none,0x2c759⟩) (by simp) (by rfl) (by simp [p1,p2,p3,p4,p5,p6,p7,p8,p9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p10 s,none,0x2c75c⟩) (by simp) (by rfl) (by simp [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p11 s,none,0x2c760⟩) (by simp) (by rfl) (by simp [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p12 s,none,0x2c762⟩) (by simp) (by rfl) (by simp [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨p12 s,none,0x2c77f⟩) (by simp) (by rfl) (by simp [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def n1 (s : X86Memory.State) : X86Memory.State := put s 7 (load32 s.memory (s.regs 1+(12#32)))
def n2 (s : X86Memory.State) : X86Memory.State := put (n1 s) 3 (load32 (n1 s).memory ((n1 s).regs 1+(64#32)))
def n3 (s : X86Memory.State) : X86Memory.State := put (n2 s) 6 (load32 (n2 s).memory ((n2 s).regs 1+(16#32)))
def n4 (s : X86Memory.State) : X86Memory.State := put (n3 s) 0 (load32 (n3 s).memory ((n3 s).regs 1+(12#32)))
def n5 (s : X86Memory.State) : X86Memory.State := put (n4 s) 5 (load32 (n4 s).memory ((n4 s).regs 1+(16#32)))
def n6 (s : X86Memory.State) : X86Memory.State := put (n5 s) 7 ((n5 s).regs 7-(n5 s).regs 3)
def n7 (s : X86Memory.State) : X86Memory.State := put (n6 s) 6 ((n6 s).regs 6-(n6 s).regs 3)
def n8 (s : X86Memory.State) : X86Memory.State := put (n7 s) 0 ((n7 s).regs 0+(n7 s).regs 3)
def n9 (s : X86Memory.State) : X86Memory.State := put (n8 s) 5 ((n8 s).regs 5+(n8 s).regs 3)
def n10 (s : X86Memory.State) : X86Memory.State := {(n9 s) with memory:=store32 (n9 s).memory ((n9 s).regs 4+(20#32)) ((n9 s).regs 0)}
theorem n_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 10 ⟨s,f,0x2c764⟩ ⟨n10 s,none,0x2c77f⟩ := by
  have path : X86Routine.Prefix listed [] 10 ⟨s,f,0x2c764⟩ ⟨n10 s,none,0x2c77f⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨n1 s,f,0x2c767⟩) (by simp) (by rfl) (by simp [n1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨n2 s,f,0x2c76a⟩) (by simp) (by rfl) (by simp [n1,n2,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨n3 s,f,0x2c76d⟩) (by simp) (by rfl) (by simp [n1,n2,n3,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨n4 s,f,0x2c770⟩) (by simp) (by rfl) (by simp [n1,n2,n3,n4,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨n5 s,f,0x2c773⟩) (by simp) (by rfl) (by simp [n1,n2,n3,n4,n5,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨n6 s,none,0x2c775⟩) (by simp) (by rfl) (by simp [n1,n2,n3,n4,n5,n6,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨n7 s,none,0x2c777⟩) (by simp) (by rfl) (by simp [n1,n2,n3,n4,n5,n6,n7,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨n8 s,none,0x2c779⟩) (by simp) (by rfl) (by simp [n1,n2,n3,n4,n5,n6,n7,n8,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨n9 s,none,0x2c77b⟩) (by simp) (by rfl) (by simp [n1,n2,n3,n4,n5,n6,n7,n8,n9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨n10 s,none,0x2c77f⟩) (by simp) (by rfl) (by simp [n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def diagonal (s : X86Memory.State) := if positive s then p12 (gate s).core else n10 (gate s).core

theorem diagonal_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤19, X86Routine.Prefix program [] n ⟨s,f,0x2c72b⟩ ⟨diagonal s,none,0x2c77f⟩ := by
  have a := gate_execution s f
  cases h : positive s
  · have b := n_execution (gate s).core (gate s).flags
    have pc : (gate s).pc=0x2c764 := by simp [gate,h]
    rw [OriginalPathXStep.at_pc _ _ pc] at b
    exact ⟨16,by omega,by simpa only [diagonal,h,Bool.false_eq_true,if_false] using OriginalGroupBounds.prefix_join a b⟩
  · have b := p_execution (gate s).core (gate s).flags
    have pc : (gate s).pc=0x2c742 := by simp [gate,h]
    rw [OriginalPathXStep.at_pc _ _ pc] at b
    exact ⟨19,by omega,by simpa only [diagonal,h,if_true] using OriginalGroupBounds.prefix_join a b⟩

def c1 (s : X86Memory.State) := put s 3 0x2ba10
def c2 (s : X86Memory.State) := put (c1 s) 0 (s.regs 7)
def c3 (s : X86Memory.State) := put (c2 s) 2 (s.regs 6)
def called (s : X86Memory.State) : X86Control.State := ⟨X86Routine.pushWord (c3 s) 0x2c78d,none,0x2c1e0⟩
theorem call_execution (s : X86Memory.State) :
    X86Routine.Prefix program [] 4 ⟨s,none,0x2c77f⟩ (called s) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,none,0x2c77f⟩ (called s) := by
    apply X86Routine.Prefix.step (middle := ⟨c1 s,none,0x2c784⟩) (by simp) (by rfl) (by simp [called,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨c2 s,none,0x2c786⟩) (by simp) (by rfl) (by simp [called,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨c3 s,none,0x2c788⟩) (by simp) (by rfl) (by simp [called,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨(called s).core,none,0x2c1e0⟩) (by simp) (by rfl) (by simp [called,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    exact .nil _
  exact path.transfer program [] decoded (by simp)
def first (s : X86Memory.State) := called (diagonal s)
theorem first_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤23, X86Routine.Prefix program [] n ⟨s,f,0x2c72b⟩ (first s) := by
  obtain ⟨n,hn,a⟩ := diagonal_execution s f
  exact ⟨n+4,by omega,OriginalGroupBounds.prefix_join a (call_execution (diagonal s))⟩

def x (s : X86Memory.State) := load32 s.memory (s.regs 1+(12#32))
def y (s : X86Memory.State) := load32 s.memory (s.regs 1+(16#32))
def radius (s : X86Memory.State) := load32 s.memory (s.regs 1+(64#32))
def y1 (s : X86Memory.State) := if positive s then y s+radius s else y s-radius s
def y2 (s : X86Memory.State) := if positive s then y s-radius s else y s+radius s

theorem diagonal_observe (s : X86Memory.State) :
    (diagonal s).regs 7=x s-radius s ∧ (diagonal s).regs 6=y1 s ∧
    (diagonal s).regs 5=y2 s ∧ (diagonal s).regs 1=s.regs 1 ∧
    (diagonal s).regs 4=s.regs 4 ∧
    (diagonal s).memory=store32 s.memory (s.regs 4+(20#32)) (x s+radius s) := by
  cases hp : positive s <;>
    simp [diagonal,gate,hp,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,
      n10,n9,n8,n7,n6,n5,n4,n3,n2,n1,x,y,radius,y1,y2,put,write]

theorem first_observe (s : X86Memory.State) :
    (first s).pc=0x2c1e0 ∧ (first s).core.regs 0=x s-radius s ∧
    (first s).core.regs 2=y1 s ∧ (first s).core.regs 3=(0x2ba10#32) ∧
    (first s).core.regs 4=s.regs 4-(4#32) ∧
    load32 (first s).core.memory ((first s).core.regs 4)=(0x2c78d#32) := by
  have d := diagonal_observe s
  simp only [first,called,X86Routine.pushWord,c3,c2,c1,put,write]
  simp [d.1,d.2.1,d.2.2.2.2.1,load_store]

theorem first_frame (s : X86Memory.State) (a : Word)
    (scratch : Apart a (s.regs 4+(20#32)))
    (call : Apart a (s.regs 4-(4#32))) :
    load32 (first s).core.memory a=load32 s.memory a := by
  change load32 (store32 (diagonal s).memory ((diagonal s).regs 4-(4#32)) _) a=_
  rw [(diagonal_observe s).2.2.2.2.1,load_store_apart _ _ _ _ call,
    (diagonal_observe s).2.2.2.2.2,load_store_apart _ _ _ _ scratch]

/-- These are the exact endpoints used by the live object-intercept function. -/
def points (trace : Collision.Divline) (thing : Collision.SolidThing) : Fixed × Fixed × Fixed × Fixed :=
  let positive := (trace.dx.raw ^^^ trace.dy.raw)>0
  (thing.x-thing.radius,if positive then thing.y+thing.radius else thing.y-thing.radius,
   thing.x+thing.radius,if positive then thing.y-thing.radius else thing.y+thing.radius)

theorem production (trace : Collision.Divline) (thing : Collision.SolidThing) :
    Collision.thingIntercept trace thing = (do
      let (x1,y1,x2,y2) := points trace thing
      if trace.pointSide x1 y1 == trace.pointSide x2 y2 then return none
      let frac ← Collision.interceptVector trace ⟨x1,y1,x2-x1,y2-y1⟩
      return if frac.raw<0 then none else some frac) := by rfl

structure Inputs (s : X86Memory.State) (trace : Collision.Divline)
    (thing : Collision.SolidThing) (object : Word) : Prop where
  objectArg : s.regs 1=object
  traceDX : load32 s.memory (0x2ba18#32)=trace.dx.raw.toBitVec
  traceDY : load32 s.memory (0x2ba1c#32)=trace.dy.raw.toBitVec
  objectX : load32 s.memory (object+(12#32))=thing.x.raw.toBitVec
  objectY : load32 s.memory (object+(16#32))=thing.y.raw.toBitVec
  objectRadius : load32 s.memory (object+(64#32))=thing.radius.raw.toBitVec

theorem live_diagonal (s : X86Memory.State) (trace : Collision.Divline)
    (thing : Collision.SolidThing) (object : Word) (h : Inputs s trace thing object) :
    (diagonal s).regs 7=(points trace thing).1.raw.toBitVec ∧
    (diagonal s).regs 6=(points trace thing).2.1.raw.toBitVec ∧
    (diagonal s).regs 5=(points trace thing).2.2.2.raw.toBitVec ∧
    load32 (diagonal s).memory (s.regs 4+(20#32))=(points trace thing).2.2.1.raw.toBitVec := by
  have hp : positive s=decide (0<(trace.dx.raw ^^^ trace.dy.raw).toInt) := by
    simp only [positive,xor,h.traceDX,h.traceDY]
    rfl
  have same : (0<(trace.dx.raw ^^^ trace.dy.raw).toInt) ↔ ((trace.dx.raw ^^^ trace.dy.raw)>0) := by
    simp only [Int32.lt_iff_toInt_lt,Int32.toInt_zero]
  have d := diagonal_observe s
  rw [d.1,d.2.1,d.2.2.1,d.2.2.2.2.2,load_store]
  simp only [x,y,radius,h.objectArg,h.objectX,h.objectY,h.objectRadius,y1,y2,hp,same,points]
  by_cases sign : (trace.dx.raw ^^^ trace.dy.raw)>0 <;>
    simp only [sign,if_true,if_false,decide_true,decide_false,Bool.false_eq_true,Prod.fst,Prod.snd] <;>
    exact ⟨rfl,rfl,rfl,rfl⟩
end Doom.Proofs.OriginalThingDiagonal

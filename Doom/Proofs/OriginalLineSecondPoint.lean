import Doom.Proofs.OriginalDivlineSide
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineSecondPoint
open Verification X86 X86Memory X86Control BlockSummary
def wideBytes : List UInt8 := [0x89,0xc6,0x8b,0x41,0x4,0xbb,0x10,0xba,0x2,0x0,0x8b,0x50,0x4,0x8b,0x0,0xe8,0x95,0xfb,0xff,0xff,0xeb,0x36]
def shortBytes : List UInt8 := [0x8b,0x15,0x14,0xba,0x2,0x0,0x8b,0x2d,0x1c,0xba,0x2,0x0,0x8b,0x1d,0x18,0xba,0x2,0x0,0x89,0xc6,0xa1,0x10,0xba,0x2,0x0,0x1,0xea,0x1,0xd8,0x89,0xcb,0xe8,0x8d,0xf9,0xff,0xff,0x39,0xc6,0x75,0xa,0xb8,0x1,0x0,0x0,0x0,0xe9,0x80,0x0,0x0,0x0]
def returnBytes : List UInt8 := [0x83,0xc4,0x10,0x5d,0x5e,0x5a,0x59,0x5b,0xc3]
def localBytes (wide short ret : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c637≤pc ∧ pc<0x2c64d then X86Routine.decodeAt wide (pc-0x2c637)
  else if 0x2c65f≤pc ∧ pc<0x2c691 then X86Routine.decodeAt short (pc-0x2c65f)
  else if 0x2c711≤pc ∧ pc<0x2c71a then X86Routine.decodeAt ret (pc-0x2c711) else none
def bytesProgram (wide short ret : List UInt8) : X86Routine.Program := fun pc =>
  match localBytes wide short ret pc with
  | some op => some op
  | none => match OriginalDivlineSide.program pc with
    | some op => some op
    | none => OriginalLineSide.program pc
def program := bytesProgram wideBytes shortBytes returnBytes

def listed : X86Routine.Program
  | 0x2c637 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2c639 => some (.control (.block (.legacy (.load 0 1 4))),3)
  | 0x2c63c => some (.immediate 3 0x2ba10,5)
  | 0x2c641 => some (.control (.block (.legacy (.load 2 0 4))),3)
  | 0x2c644 => some (.control (.block (.legacy (.load 0 0 0))),2)
  | 0x2c646 => some (.call (-1131),5)
  | 0x2c64b => some (.jump 54,2)
  | 0x2c65f => some (.control (.block (.load 2 ⟨none,none,0,0x2ba14⟩)),6)
  | 0x2c665 => some (.control (.block (.load 5 ⟨none,none,0,0x2ba1c⟩)),6)
  | 0x2c66b => some (.control (.block (.load 3 ⟨none,none,0,0x2ba18⟩)),6)
  | 0x2c671 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2c673 => some (.control (.block (.load 0 ⟨none,none,0,0x2ba10⟩)),5)
  | 0x2c678 => some (.control (.block (.arithmetic (.add 2 5))),2)
  | 0x2c67a => some (.control (.block (.arithmetic (.add 0 3))),2)
  | 0x2c67c => some (.control (.block (.legacy (.mov 3 1))),2)
  | 0x2c67e => some (.call (-1651),5)
  | 0x2c683 => some (.compareRegisters 6 0,2)
  | 0x2c685 => some (.control (.jumpZero false 10),2)
  | 0x2c687 => some (.immediate 0 1,5)
  | 0x2c68c => some (.jump 128,5)
  | 0x2c711 => some (.addImmediate 4 16,3)
  | 0x2c714 => some (.pop 5,1)
  | 0x2c715 => some (.pop 6,1)
  | 0x2c716 => some (.pop 2,1)
  | 0x2c717 => some (.pop 1,1)
  | 0x2c718 => some (.pop 3,1)
  | 0x2c719 => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

theorem contains_divline (pc : Nat) (h : OriginalDivlineSide.program pc≠none) :
    program pc=OriginalDivlineSide.program pc := by
  have range : 0x2c1e0≤pc ∧ pc<0x2c2a7 := by
    by_cases r : 0x2c1e0≤pc ∧ pc<0x2c2a7
    · exact r
    · simp [OriginalDivlineSide.program,OriginalDivlineSide.bytesProgram,r] at h
  simp [program,bytesProgram,localBytes,show ¬(0x2c637≤pc ∧ pc<0x2c64d) by omega,
    show ¬(0x2c65f≤pc ∧ pc<0x2c691) by omega,show ¬(0x2c711≤pc ∧ pc<0x2c71a) by omega]
  cases hp : OriginalDivlineSide.program pc <;> simp_all

theorem contains_line (pc : Nat) (h : OriginalLineSide.program pc≠none) :
    program pc=OriginalLineSide.program pc := by
  have range : 0x2c010≤pc ∧ pc<0x2c0b3 := by
    by_cases r : 0x2c010≤pc ∧ pc<0x2c0b3
    · exact r
    · simp [OriginalLineSide.program,OriginalLineSide.bytesProgram,r] at h
  simp [program,bytesProgram,localBytes,show ¬(0x2c637≤pc ∧ pc<0x2c64d) by omega,
    show ¬(0x2c65f≤pc ∧ pc<0x2c691) by omega,show ¬(0x2c711≤pc ∧ pc<0x2c71a) by omega,
    OriginalDivlineSide.program,OriginalDivlineSide.bytesProgram,show ¬(0x2c1e0≤pc ∧ pc<0x2c2a7) by omega]
def wide1 (s : X86Memory.State) := put s 6 (s.regs 0)
def wide2 (s : X86Memory.State) := put (wide1 s) 0 (load32 (wide1 s).memory ((wide1 s).regs 1+4))
def wide3 (s : X86Memory.State) := put (wide2 s) 3 0x2ba10
def wide4 (s : X86Memory.State) := put (wide3 s) 2 (load32 (wide3 s).memory ((wide3 s).regs 0+4))
def wide5 (s : X86Memory.State) := put (wide4 s) 0 (load32 (wide4 s).memory ((wide4 s).regs 0))
def wide6 (s : X86Memory.State) := X86Routine.pushWord (wide5 s) 0x2c64b
def wideCall := wide6
theorem wide_call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2c637⟩ ⟨wideCall s,f,0x2c1e0⟩ := by
  have path : X86Routine.Prefix listed [] 6 ⟨s,f,0x2c637⟩ ⟨wideCall s,f,0x2c1e0⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨wide1 s,f,0x2c639⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,wide1])
    apply X86Routine.Prefix.step (middle := ⟨wide2 s,f,0x2c63c⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,wide1,wide2])
    apply X86Routine.Prefix.step (middle := ⟨wide3 s,f,0x2c641⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,wide1,wide2,wide3])
    apply X86Routine.Prefix.step (middle := ⟨wide4 s,f,0x2c644⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,wide1,wide2,wide3,wide4])
    apply X86Routine.Prefix.step (middle := ⟨wide5 s,f,0x2c646⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,wide1,wide2,wide3,wide4,wide5])
    apply X86Routine.Prefix.step (middle := ⟨wide6 s,f,0x2c1e0⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,wide1,wide2,wide3,wide4,wide5,wide6])
    exact .nil _
  exact path.transfer program [] decoded (by simp)
def short1 (s : X86Memory.State) := put s 2 (load32 s.memory 0x2ba14)
def short2 (s : X86Memory.State) := put (short1 s) 5 (load32 (short1 s).memory 0x2ba1c)
def short3 (s : X86Memory.State) := put (short2 s) 3 (load32 (short2 s).memory 0x2ba18)
def short4 (s : X86Memory.State) := put (short3 s) 6 ((short3 s).regs 0)
def short5 (s : X86Memory.State) := put (short4 s) 0 (load32 (short4 s).memory 0x2ba10)
def short6 (s : X86Memory.State) := put (short5 s) 2 ((short5 s).regs 2+(short5 s).regs 5)
def short7 (s : X86Memory.State) := put (short6 s) 0 ((short6 s).regs 0+(short6 s).regs 3)
def short8 (s : X86Memory.State) := put (short7 s) 3 ((short7 s).regs 1)
def short9 (s : X86Memory.State) := X86Routine.pushWord (short8 s) 0x2c683
def shortCall := short9
theorem short_call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 9 ⟨s,f,0x2c65f⟩ ⟨shortCall s,none,0x2c010⟩ := by
  have path : X86Routine.Prefix listed [] 9 ⟨s,f,0x2c65f⟩ ⟨shortCall s,none,0x2c010⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨short1 s,f,0x2c665⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,short1])
    apply X86Routine.Prefix.step (middle := ⟨short2 s,f,0x2c66b⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,short1,short2])
    apply X86Routine.Prefix.step (middle := ⟨short3 s,f,0x2c671⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,short1,short2,short3])
    apply X86Routine.Prefix.step (middle := ⟨short4 s,f,0x2c673⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,short1,short2,short3,short4])
    apply X86Routine.Prefix.step (middle := ⟨short5 s,f,0x2c678⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,short1,short2,short3,short4,short5])
    apply X86Routine.Prefix.step (middle := ⟨short6 s,none,0x2c67a⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,short1,short2,short3,short4,short5,short6])
    apply X86Routine.Prefix.step (middle := ⟨short7 s,none,0x2c67c⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,short1,short2,short3,short4,short5,short6,short7])
    apply X86Routine.Prefix.step (middle := ⟨short8 s,none,0x2c67e⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,short1,short2,short3,short4,short5,short6,short7,short8])
    apply X86Routine.Prefix.step (middle := ⟨short9 s,none,0x2c010⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,short1,short2,short3,short4,short5,short6,short7,short8,short9])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def call (wide : Bool) (s : X86Memory.State) := if wide then wideCall s else shortCall s
def helper (wide : Bool) (s : X86Memory.State) :=
  if wide then OriginalDivlineSide.result (call wide s) else OriginalLineSide.result (call wide s)
def second (wide : Bool) (s : X86Memory.State) : X86Control.State :=
  {helper wide s with pc:=0x2c683}
def startPc (wide : Bool) : Nat := if wide then 0x2c637 else 0x2c65f

theorem helper_return (wide : Bool) (s : X86Memory.State) :
    (helper wide s).pc=(if wide then 0x2c64b else 0x2c683) := by
  cases wide <;> simp only [helper,call,Bool.false_eq_true,if_false,if_true]
  · rw [(OriginalLineSide.returned (shortCall s)).2.2.2.2.2]
    simp [shortCall,short9,short8,short7,short6,short5,short4,short3,short2,short1,X86Routine.pushWord,put,write,load_store]
  · rw [(OriginalDivlineSide.returned (wideCall s)).2.2.2.2.2]
    simp [wideCall,wide6,wide5,wide4,wide3,wide2,wide1,X86Routine.pushWord,put,write,load_store]

theorem second_execution (wide : Bool) (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤51 ∧ X86Routine.Prefix program [] n ⟨s,f,startPc wide⟩ (second wide s) := by
  cases wide
  · obtain ⟨n,hn,hp⟩ := OriginalLineSide.execution (shortCall s) none
    have hp := hp.transfer program [] contains_line (by simp)
    have eq : second false s=OriginalLineSide.result (shortCall s) := by
      have pc := helper_return false s
      change (helper false s).pc=0x2c683 at pc
      unfold second
      rw [←pc]
      rfl
    rw [eq]
    exact ⟨9+n,by omega,OriginalGroupBounds.prefix_join (short_call_execution s f) hp⟩
  · obtain ⟨n,hn,hp⟩ := OriginalDivlineSide.execution (wideCall s) f
    have hp := hp.transfer program [] contains_divline (by simp)
    have jump : X86Routine.Prefix listed [] 1 (helper true s) (second true s) := by
      have pc := helper_return true s
      apply X86Routine.Prefix.step (middle := second true s) (by simp) (by simp only [pc]; rfl) (by
        simp [X86Routine.execute,second,pc])
      exact .nil _
    have jump := jump.transfer program [] decoded (by simp)
    exact ⟨6+(n+1),by omega,OriginalGroupBounds.prefix_join (wide_call_execution s f) (OriginalGroupBounds.prefix_join hp jump)⟩
def unwind0 (s : X86Memory.State) := put s 4 (s.regs 4+16)
def unwind1 (s : X86Memory.State) := put (put (unwind0 s) 4 (s.regs 4+20)) 5 (load32 s.memory (s.regs 4+16))
def unwind2 (s : X86Memory.State) := put (put (unwind1 s) 4 (s.regs 4+24)) 6 (load32 s.memory (s.regs 4+20))
def unwind3 (s : X86Memory.State) := put (put (unwind2 s) 4 (s.regs 4+28)) 2 (load32 s.memory (s.regs 4+24))
def unwind4 (s : X86Memory.State) := put (put (unwind3 s) 4 (s.regs 4+32)) 1 (load32 s.memory (s.regs 4+28))
def unwind5 (s : X86Memory.State) := put (put (unwind4 s) 4 (s.regs 4+36)) 3 (load32 s.memory (s.regs 4+32))
def unwind (s : X86Memory.State) : X86Control.State :=
  ⟨put (unwind5 s) 4 (s.regs 4+40),none,(load32 s.memory (s.regs 4+36)).toNat⟩
theorem unwind_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 7 ⟨s,f,0x2c711⟩ (unwind s) := by
  have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c711⟩ (unwind s) := by
    apply X86Routine.Prefix.step (middle := ⟨unwind0 s,none,0x2c714⟩) (by simp) (by rfl) (by simp [X86Routine.execute,unwind,unwind0,unwind1,unwind2,unwind3,unwind4,unwind5,put,write,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨unwind1 s,none,0x2c715⟩) (by simp) (by rfl) (by simp [X86Routine.execute,unwind,unwind0,unwind1,unwind2,unwind3,unwind4,unwind5,put,write,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨unwind2 s,none,0x2c716⟩) (by simp) (by rfl) (by simp [X86Routine.execute,unwind,unwind0,unwind1,unwind2,unwind3,unwind4,unwind5,put,write,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨unwind3 s,none,0x2c717⟩) (by simp) (by rfl) (by simp [X86Routine.execute,unwind,unwind0,unwind1,unwind2,unwind3,unwind4,unwind5,put,write,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨unwind4 s,none,0x2c718⟩) (by simp) (by rfl) (by simp [X86Routine.execute,unwind,unwind0,unwind1,unwind2,unwind3,unwind4,unwind5,put,write,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨unwind5 s,none,0x2c719⟩) (by simp) (by rfl) (by simp [X86Routine.execute,unwind,unwind0,unwind1,unwind2,unwind3,unwind4,unwind5,put,write,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := unwind s) (by simp) (by rfl) (by simp [X86Routine.execute,unwind,unwind0,unwind1,unwind2,unwind3,unwind4,unwind5,put,write,BitVec.add_assoc])
    exact .nil _
  exact path.transfer program [] decoded (by simp)
def rejected (s : X86Memory.State) := unwind (put s 0 1)
def gate (s : X86Memory.State) : X86Control.State :=
  if s.regs 6=s.regs 0 then rejected s else ⟨s,some (compare32 (s.regs 6) (s.regs 0)),0x2c691⟩

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤11 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c683⟩ (gate s) := by
  have flags : (compare32 (s.regs 6) (s.regs 0)).zero=(s.regs 6==s.regs 0) := by exact cmp32_zero _ _
  by_cases h : s.regs 6=s.regs 0
  · have head : X86Routine.Prefix listed [] 4 ⟨s,f,0x2c683⟩ ⟨put s 0 1,some (compare32 (s.regs 6) (s.regs 0)),0x2c711⟩ := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 6) (s.regs 0)),0x2c685⟩) (by simp) (by rfl) (by rfl)
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 6) (s.regs 0)),0x2c687⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,flags,h,compare32])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 1,some (compare32 (s.regs 6) (s.regs 0)),0x2c68c⟩) (by simp) (by rfl) (by rfl)
      apply X86Routine.Prefix.step (middle := ⟨put s 0 1,some (compare32 (s.regs 6) (s.regs 0)),0x2c711⟩) (by simp) (by rfl) (by rfl)
      exact .nil _
    refine ⟨11,by omega,?_⟩
    simpa only [gate,if_pos h,rejected] using OriginalGroupBounds.prefix_join
      (head.transfer program [] decoded (by simp)) (unwind_execution (put s 0 1) _)
  · have path : X86Routine.Prefix listed [] 2 ⟨s,f,0x2c683⟩ (gate s) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 6) (s.regs 0)),0x2c685⟩) (by simp) (by rfl) (by rfl)
      apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by simp [gate,h,X86Routine.execute,X86Control.execute,flags])
      exact .nil _
    exact ⟨2,by omega,path.transfer program [] decoded (by simp)⟩
def result (wide : Bool) (s : X86Memory.State) := gate (second wide s).core

theorem execution (wide : Bool) (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤62 ∧ X86Routine.Prefix program [] n ⟨s,f,startPc wide⟩ (result wide s) := by
  obtain ⟨n,hn,a⟩ := second_execution wide s f
  obtain ⟨m,hm,b⟩ := gate_execution (second wide s).core (second wide s).flags
  exact ⟨n+m,by omega,OriginalGroupBounds.prefix_join a b⟩

theorem call_regs (wide : Bool) (s : X86Memory.State) :
    (call wide s).regs 4=s.regs 4-(4#32) ∧
    (call wide s).regs 1=s.regs 1 ∧ (call wide s).regs 6=s.regs 0 ∧
    (call wide s).regs 0=(if wide then load32 s.memory (load32 s.memory (s.regs 1+4))
      else load32 s.memory 0x2ba10+load32 s.memory 0x2ba18) ∧
    (call wide s).regs 2=(if wide then load32 s.memory (load32 s.memory (s.regs 1+4)+4)
      else load32 s.memory 0x2ba14+load32 s.memory 0x2ba1c) ∧
    (call wide s).regs 3=(if wide then 0x2ba10 else s.regs 1) := by
  cases wide <;> simp [call,wideCall,wide6,wide5,wide4,wide3,wide2,wide1,shortCall,short9,short8,short7,short6,short5,short4,short3,short2,short1,X86Routine.pushWord,put,write]

theorem call_memory (wide : Bool) (s : X86Memory.State) :
    (call wide s).memory=store32 s.memory (s.regs 4-(4#32)) (if wide then 0x2c64b else 0x2c683) := by
  cases wide <;> simp [call,wideCall,wide6,wide5,wide4,wide3,wide2,wide1,shortCall,short9,short8,short7,short6,short5,short4,short3,short2,short1,X86Routine.pushWord,put,write]

theorem call_frame (wide : Bool) (s : X86Memory.State) (a : Word)
    (safe : Apart a (s.regs 4-(4#32))) : load32 (call wide s).memory a=load32 s.memory a := by
  rw [call_memory,load_store_apart _ _ _ _ safe]

theorem second_saved (wide : Bool) (s : X86Memory.State) :
    (second wide s).core.regs 4=s.regs 4 ∧ (second wide s).core.regs 1=s.regs 1 ∧
    (second wide s).core.regs 6=s.regs 0 := by
  have r := call_regs wide s
  have keep : (helper wide s).core.regs 4=(call wide s).regs 4+4 ∧
      (helper wide s).core.regs 1=(call wide s).regs 1 ∧
      (helper wide s).core.regs 6=(call wide s).regs 6 := by
    cases wide
    · have h := OriginalLineSide.returned (call false s)
      exact ⟨h.1,h.2.1,h.2.2.1⟩
    · have h := OriginalDivlineSide.returned (call true s)
      exact ⟨h.1,h.2.1,h.2.2.1⟩
  simpa [second,r.1,r.2.1,r.2.2.1,BitVec.sub_eq_add_neg,BitVec.add_assoc] using keep

theorem second_frame (wide : Bool) (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)) :
    load32 (second wide s).core.memory a=load32 s.memory a := by
  have inner : ∀ off∈[(4#32),8,12,16], Apart a ((call wide s).regs 4-off) := by
    intro off ho
    rw [(call_regs wide s).1]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (8#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (12#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (16#32) (by simp)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (20#32) (by simp)
  have keep : load32 (helper wide s).core.memory a=load32 (call wide s).memory a := by
    cases wide
    · exact OriginalLineSide.frame (call false s) a inner
    · exact OriginalDivlineSide.frame (call true s) a inner
  exact keep.trans (call_frame wide s a (safe _ (by simp)))

def firstSide (trace : Collision.Divline) (line : Collision.Line) : Bool :=
  if trace.usesDivlineTest then trace.pointSide line.x line.y else line.pointSide trace.x trace.y
def lastSide (trace : Collision.Divline) (line : Collision.Line) : Bool :=
  if trace.usesDivlineTest then trace.pointSide (line.x+line.dx) (line.y+line.dy)
  else line.pointSide (trace.x+trace.dx) (trace.y+trace.dy)
def reads (p v w : Word) : List Word :=
  [p,p+4,p+8,p+12,v,v+4,w,w+4,0x2ba10,0x2ba14,0x2ba18,0x2ba1c]

/-- Inputs at the real first-helper return. In the wide branch the second
vertex encoding must agree with the production wrapping endpoint sum. -/
structure Inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) : Prop where
  first : s.regs 0=OriginalLineSide.bit (firstSide trace line)
  pointer : s.regs 1=p
  vertex1 : load32 s.memory p=v
  vertex2 : load32 s.memory (p+4)=w
  x1 : load32 s.memory v=line.x.raw.toBitVec
  y1 : load32 s.memory (v+4)=line.y.raw.toBitVec
  x2 : load32 s.memory w=(line.x+line.dx).raw.toBitVec
  y2 : load32 s.memory (w+4)=(line.y+line.dy).raw.toBitVec
  dx : load32 s.memory (p+8)=line.dx.raw.toBitVec
  dy : load32 s.memory (p+12)=line.dy.raw.toBitVec
  traceX : load32 s.memory 0x2ba10=trace.x.raw.toBitVec
  traceY : load32 s.memory 0x2ba14=trace.y.raw.toBitVec
  traceDX : load32 s.memory 0x2ba18=trace.dx.raw.toBitVec
  traceDY : load32 s.memory 0x2ba1c=trace.dy.raw.toBitVec
  safe : ∀ a∈reads p v w, ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)

theorem inner_safe (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : Inputs s trace line p v w) (wide : Bool) (a : Word) (ha : a∈reads p v w) :
    ∀ off∈[(4#32),8,12,16], Apart a ((call wide s).regs 4-off) := by
  intro off ho
  rw [(call_regs wide s).1]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.safe a ha (8#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.safe a ha (12#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.safe a ha (16#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.safe a ha (20#32) (by simp)

theorem wide_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : Inputs s trace line p v w) :
    OriginalDivlineSide.Inputs (call true s) trace (line.x+line.dx) (line.y+line.dy) 0x2ba10 := by
  have r := call_regs true s
  have keep (a : Word) (ha : a∈reads p v w) := call_frame true s a (h.safe a ha _ (by simp))
  constructor
  · simpa only [if_true,h.pointer,h.vertex2,h.x2] using r.2.2.2.1
  · simpa only [if_true,h.pointer,h.vertex2,h.y2] using r.2.2.2.2.1
  · exact r.2.2.2.2.2
  · rw [keep _ (by simp [reads]),h.traceX]
  · change load32 _ (0x2ba14#32)=_; rw [keep _ (by simp [reads])]; exact h.traceY
  · change load32 _ (0x2ba18#32)=_; rw [keep _ (by simp [reads])]; exact h.traceDX
  · change load32 _ (0x2ba1c#32)=_; rw [keep _ (by simp [reads])]; exact h.traceDY
  · intro a ha
    apply inner_safe s trace line p v w h true a
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> simp [reads]

theorem short_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : Inputs s trace line p v w) :
    OriginalLineSide.Inputs (call false s) line (trace.x+trace.dx) (trace.y+trace.dy) p v := by
  have r := call_regs false s
  have keep (a : Word) (ha : a∈reads p v w) := call_frame false s a (h.safe a ha _ (by simp))
  constructor
  · have hx : load32 s.memory (0x2ba10#32)=trace.x.raw.toBitVec := h.traceX
    have hd : load32 s.memory (0x2ba18#32)=trace.dx.raw.toBitVec := h.traceDX
    simpa [hx,hd,Fixed.add] using r.2.2.2.1
  · have hy : load32 s.memory (0x2ba14#32)=trace.y.raw.toBitVec := h.traceY
    have hd : load32 s.memory (0x2ba1c#32)=trace.dy.raw.toBitVec := h.traceDY
    simpa [hy,hd,Fixed.add] using r.2.2.2.2.1
  · simpa only [if_false,h.pointer,Bool.false_eq_true] using r.2.2.2.2.2
  · rw [keep _ (by simp [reads]),h.vertex1]
  · rw [keep _ (by simp [reads]),h.x1]
  · rw [keep _ (by simp [reads]),h.y1]
  · rw [keep _ (by simp [reads]),h.dx]
  · rw [keep _ (by simp [reads]),h.dy]
  · intro a ha
    apply inner_safe s trace line p v w h false a
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl <;> simp [reads]

theorem second_values (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : Inputs s trace line p v w) :
    (second trace.usesDivlineTest s).core.regs 6=OriginalLineSide.bit (firstSide trace line) ∧
    (second trace.usesDivlineTest s).core.regs 0=OriginalLineSide.bit (lastSide trace line) := by
  refine ⟨(second_saved trace.usesDivlineTest s).2.2.trans h.first,?_⟩
  cases hw : trace.usesDivlineTest
  · simpa only [second,helper,call,Bool.false_eq_true,if_false,lastSide,hw] using
      OriginalLineSide.live (call false s) line (trace.x+trace.dx) (trace.y+trace.dy) p v (short_inputs s trace line p v w h)
  · simpa only [second,helper,call,if_true,lastSide,hw,OriginalDivlineSide.bit,OriginalLineSide.bit] using
      OriginalDivlineSide.live (call true s) trace (line.x+line.dx) (line.y+line.dy) 0x2ba10 (wide_inputs s trace line p v w h)

theorem same_side_none (trace : Collision.Divline) (line : Collision.Line)
    (same : firstSide trace line=lastSide trace line) : Collision.lineIntercept trace line=.ok none := by
  cases hw : trace.usesDivlineTest <;>
    simp [firstSide,lastSide,hw] at same <;> simp [Collision.lineIntercept,hw,same] <;> rfl

theorem bit_injective (a b : Bool) : OriginalLineSide.bit a=OriginalLineSide.bit b ↔ a=b := by
  cases a <;> cases b <;> decide

theorem live (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : Inputs s trace line p v w) :
    let t := second trace.usesDivlineTest s
    result trace.usesDivlineTest s =
      if firstSide trace line=lastSide trace line then rejected t.core
      else ⟨t.core,some (compare32 (t.core.regs 6) (t.core.regs 0)),0x2c691⟩ := by
  dsimp only
  unfold result gate
  simp only [(second_values s trace line p v w h).1,(second_values s trace line p v w h).2,bit_injective]

theorem rejected_value (s : X86Memory.State) : (rejected s).core.regs 0=(1#32) := by
  simp [rejected,unwind,unwind0,unwind1,unwind2,unwind3,unwind4,unwind5,put,write]
theorem rejected_frame (s : X86Memory.State) : (rejected s).core.memory=s.memory := by rfl

theorem frame (wide : Bool) (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)) :
    load32 (result wide s).core.memory a=load32 s.memory a := by
  unfold result gate
  split <;> simpa only [rejected_frame] using second_frame wide s a safe

theorem rejected_pc (wide : Bool) (s : X86Memory.State) :
    (rejected (second wide s).core).pc=(load32 s.memory (s.regs 4+36)).toNat := by
  change (load32 (second wide s).core.memory ((second wide s).core.regs 4+(36#32))).toNat=_
  rw [(second_saved wide s).1,second_frame]
  · rfl
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl <;>
    simpa only [BitVec.sub_eq_add_neg,BitVec.neg_neg] using
      OriginalLineSide.slots_apart (s.regs 4) (-36#32) _ (by unfold Apart; decide)

theorem rejection (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v w : Word) (h : Inputs s trace line p v w) (same : firstSide trace line=lastSide trace line) :
    (result trace.usesDivlineTest s).core.regs 0=(1#32) ∧
    (result trace.usesDivlineTest s).pc=(load32 s.memory (s.regs 4+36)).toNat ∧
    Collision.lineIntercept trace line=.ok none := by
  rw [live s trace line p v w h,if_pos same]
  exact ⟨rejected_value _,rejected_pc _ _,same_side_none trace line same⟩
end Doom.Proofs.OriginalLineSecondPoint

import Doom.Proofs.OriginalWeaponDrop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
/-!
Valid-cache AM_Stop subroutines. The full return theorem below is conditional
on an exit-event layout. The pinned DOS notification instead starts with type
zero; OriginalAutomapHandoff proves that actual keydown branch separately.
See docs/AUTOMAP_STOP_PROOF.md for contracts and the remaining continuation.
-/
namespace Doom.Proofs.AutomapStop
open Verification X86 X86Memory X86Control BlockSummary
def tagCode : List UInt8 := [0x53,0x8d,0x58,0xe8,0x81,0x7b,0xc,0x11,0x4a,0x1d,0x0,0x74,0xd,0x68,0xcc,0x3d,0x2,0x0,0xe8,0x49,0x11,0xfe,0xff,0x83,0xc4,0x4,0x83,0xfa,0x64,0x7c,0x16,0x81,0x7b,0x4,0x0,0x1,0x0,0x0,0x73,0xd,0x68,0xf8,0x3d,0x2,0x0,0xe8,0x2e,0x11,0xfe,0xff,0x83,0xc4,0x4,0x89,0x53,0x8,0x5b,0xc3]
def unloadCode : List UInt8 := [0x53,0x52,0x31,0xdb,0x8d,0x80,0x0,0x0,0x0,0x0,0x8d,0x92,0x0,0x0,0x0,0x0,0x8b,0x83,0x8,0xb7,0x2,0x0,0x81,0x78,0xf4,0x11,0x4a,0x1d,0x0,0x74,0x12,0x68,0xec,0x0,0x0,0x0,0x68,0x8c,0x2b,0x2,0x0,0xe8,0xb2,0x5c,0xff,0xff,0x83,0xc4,0x8,0xba,0x65,0x0,0x0,0x0,0x8b,0x83,0x8,0xb7,0x2,0x0,0x83,0xc3,0x4,0xe8,0x3c,0x4b,0x1,0x0,0x83,0xfb,0x28,0x75,0xc7,0x5a,0x5b,0xc3]
def stopCode : List UInt8 := [0x53,0x52,0xe8,0x99,0xfe,0xff,0xff,0xb8,0x98,0x2c,0x1,0x0,0x31,0xd2,0xbb,0x1,0x0,0x0,0x0,0x89,0x15,0x5c,0x2c,0x1,0x0,0xe8,0xf2,0x4a,0x1,0x0,0x89,0x1d,0x94,0x2c,0x1,0x0,0x5a,0x5b,0xc3]
def responderCode : List UInt8 := [0x53,0x51,0x52,0x56,0x57,0x83,0xec,0x8,0x89,0xc7,0x8b,0x10,0x83,0xfa,0x1,0x75,0x47,0x8b,0x40,0x4,0x66,0x31,0xc0,0x3d,0x0,0x0,0x6d,0x61,0x75,0x3a,0x8b,0x47,0x4,0x3d,0x0,0x65,0x6d,0x61,0xf,0x82,0x50,0x4,0x0,0x0,0x76,0xc,0x3d,0x0,0x78,0x6d,0x61,0x74,0x18,0xe9,0x42,0x4,0x0,0x0,0x31,0xc9,0x89,0x15,0x60,0x54,0x7,0x0,0x89,0xd,0x34,0x54,0x7,0x0,0xe9,0x2f,0x4,0x0,0x0,0x89,0x15,0x34,0x54,0x7,0x0,0xe9,0x24,0x4,0x0,0x0]
def responderReturnCode : List UInt8 := [0x31,0xc0,0x83,0xc4,0x8,0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (tag unload stop responder responderReturn : List UInt8) : X86Routine.Program := fun pc =>
  if 0x399b0 ≤ pc ∧ pc < 0x399ea then X86Routine.decodeAt tag (pc-0x399b0) else
  if 0x24e30 ≤ pc ∧ pc < 0x24e7c then X86Routine.decodeAt unload (pc-0x24e30) else
  if 0x24f90 ≤ pc ∧ pc < 0x24fb7 then X86Routine.decodeAt stop (pc-0x24f90) else
  if 0x39aa0 ≤ pc ∧ pc < 0x39af8 then X86Routine.decodeAt responder (pc-0x39aa0) else
  if 0x39f1c ≤ pc ∧ pc < 0x39f27 then X86Routine.decodeAt responderReturn (pc-0x39f1c) else none
def program := bytesProgram tagCode unloadCode stopCode responderCode responderReturnCode

def tagListed : X86Routine.Program
  | 0x399b0 => some (.push 3,1)
  | 0x399b1 => some (.control (.block (.legacy (.lea 3 0 (-24)))),3)
  | 0x399b4 => some (.control (.cmpImmediate ⟨some 3,none,0,12⟩ 0x1d4a11),7)
  | 0x399bb => some (.control (.jumpZero true 13),2)
  | 0x399ca => some (.compareRegister 2 100,3)
  | 0x399cd => some (.jumpSigned 3 22,2)
  | 0x399cf => some (.control (.cmpImmediate ⟨some 3,none,0,4⟩ 256),7)
  | 0x399d6 => some (.jumpUnsigned 2 13,2)
  | 0x399e5 => some (.control (.block (.store ⟨some 3,none,0,8⟩ 2)),3)
  | 0x399e8 => some (.pop 3,1)
  | 0x399e9 => some (.ret,1)
  | _ => none

theorem tag_decoded (pc : Nat) (h : tagListed pc≠none) : program pc=tagListed pc := by
  fun_cases tagListed pc <;> simp_all [tagListed] <;> decide

def tagSaved (s : X86Memory.State) := store32 s.memory (s.regs 4-(4#32)) (s.regs 3)
def tagMemory (s : X86Memory.State) := store32 (tagSaved s) (s.regs 0-(16#32)) (101#32)
def tagResult (s : X86Memory.State) (ret : Nat) : X86Control.State :=
  ⟨⟨write s.regs 4 (s.regs 4+(4#32)),tagMemory s⟩,
    some (compare32 (load32 s.memory (s.regs 0-(20#32))) 256),ret⟩
structure TagInputs (s : X86Memory.State) (ret : Nat) : Prop where
  tag : s.regs 2=101
  magic : load32 s.memory (s.regs 0-(12#32))=0x1d4a11
  owner : (load32 s.memory (s.regs 0-(20#32))).toNat ≥ 256
  magicSafe : Apart (s.regs 0-(12#32)) (s.regs 4-(4#32))
  ownerSafe : Apart (s.regs 0-(20#32)) (s.regs 4-(4#32))
  saveSafe : Apart (s.regs 4-(4#32)) (s.regs 0-(16#32))
  returnSafe : Apart (s.regs 4) (s.regs 0-(16#32))
  returnSave : Apart (s.regs 4) (s.regs 4-(4#32))
  returnAddress : load32 s.memory (s.regs 4)=BitVec.ofNat 32 ret
  returnBound : ret < 4294967296
  outside : ret ∉ [0x399b0,0x399b1,0x399b4,0x399bb,0x399ca,0x399cd,0x399cf,0x399d6,0x399e5,0x399e8,0x399e9]

theorem tag_reads (s : X86Memory.State) (ret : Nat) (h : TagInputs s ret) :
    load32 (tagSaved s) (s.regs 0-(12#32))=0x1d4a11 ∧
    load32 (tagSaved s) (s.regs 0-(20#32))=load32 s.memory (s.regs 0-(20#32)) ∧
    load32 (tagMemory s) (s.regs 4-(4#32))=s.regs 3 ∧
    load32 (tagMemory s) (s.regs 4)=BitVec.ofNat 32 ret := by
  refine ⟨?_,?_,?_,?_⟩
  · exact (load_store_apart _ _ _ _ h.magicSafe).trans h.magic
  · exact load_store_apart _ _ _ _ h.ownerSafe
  · unfold tagMemory; rw [load_store_apart _ _ _ _ h.saveSafe]; exact load_store _ _ _
  · unfold tagMemory tagSaved; rw [load_store_apart _ _ _ _ h.returnSafe,load_store_apart _ _ _ _ h.returnSave]; exact h.returnAddress

def tagMid (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write s.regs 4 (s.regs 4-(4#32))) 3 (s.regs 0-(24#32)),tagSaved s⟩,
    some (compare32 0x1d4a11 0x1d4a11),0x399ca⟩

theorem tag_prologue (s : X86Memory.State) (f : Option Flags) (h : TagInputs s 0x24e74) :
    X86Routine.Prefix tagListed [0x24e74] 4 ⟨s,f,0x399b0⟩ (tagMid s) := by
  have hr := (tag_reads s 0x24e74 h).1
  let pushed := X86Routine.pushWord s (s.regs 3)
  let addressed := put pushed 3 (s.regs 0-(24#32))
  apply X86Routine.Prefix.step (middle := ⟨pushed,f,0x399b1⟩) (by simp) (by rfl) (by rfl)
  apply X86Routine.Prefix.step (middle := ⟨addressed,f,0x399b4⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
      pushed,addressed,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg])
  apply X86Routine.Prefix.step (middle := {tagMid s with pc := 0x399bb}) (by simp) (by rfl) (by
    simp [tagSaved,BitVec.sub_eq_add_neg] at hr
    simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,addressed,pushed,
      X86Routine.pushWord,put,write,tagMid,tagSaved,BitVec.sub_eq_add_neg,BitVec.add_assoc,hr])
  apply X86Routine.Prefix.step (middle := tagMid s) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,tagMid,compare32])
  exact X86Routine.Prefix.nil _

theorem tag_execution (s : X86Memory.State) (f : Option Flags) (h : TagInputs s 0x24e74) :
    X86Routine.run tagListed [0x24e74] 11 ⟨s,f,0x399b0⟩=some (tagResult s 0x24e74) := by
  have hr := tag_reads s 0x24e74 h
  have ge : (load32 s.memory (s.regs 0-(20#32))).ult (256#32)=false := by
    simp only [BitVec.ult_eq_decide]; simp [show ¬(load32 s.memory (s.regs 0-(20#32))).toNat < 256 by have := h.owner; omega]
  let c := (tagMid s).core
  let flags := some (compare32 (load32 s.memory (s.regs 0-(20#32))) 256)
  let stored : X86Memory.State := {c with memory := tagMemory s}
  let popped : X86Memory.State := ⟨s.regs,tagMemory s⟩
  have path : X86Routine.Prefix tagListed [0x24e74] 7 (tagMid s) (tagResult s 0x24e74) := by
    apply X86Routine.Prefix.step (middle := ⟨c,some (compare32 101 100),0x399cd⟩) (by simp [tagMid]) (by rfl) (by simp [X86Routine.execute,c,tagMid,write,h.tag])
    apply X86Routine.Prefix.step (middle := ⟨c,some (compare32 101 100),0x399cf⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,show (compare32 (101#32) (100#32)).sign=(compare32 (101#32) (100#32)).overflow from by decide])
    apply X86Routine.Prefix.step (middle := ⟨c,flags,0x399d6⟩) (by simp) (by rfl) (by
      have keep := hr.2.1
      simp [tagSaved,BitVec.sub_eq_add_neg] at keep
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,c,tagMid,write,flags,
        tagSaved,BitVec.sub_eq_add_neg,BitVec.add_assoc,keep])
    apply X86Routine.Prefix.step (middle := ⟨c,flags,0x399e5⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,flags,show ∀ a b, (compare32 a b).carry=some (a.ult b) from fun _ _ => rfl,ge])
    apply X86Routine.Prefix.step (middle := ⟨stored,flags,0x399e8⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,X86Block.Address.eval,
        stored,c,tagMid,tagMemory,write,h.tag,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨popped,flags,0x399e9⟩) (by simp) (by rfl) (by
      have keep := hr.2.2.1
      simp [BitVec.sub_eq_add_neg] at keep
      simp [X86Routine.execute,stored,c,tagMid,put,write,keep,popped,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      funext r
      by_cases a : r=3 <;> by_cases b : r=4 <;> simp_all [write])
    apply X86Routine.Prefix.step (middle := tagResult s 0x24e74) (by simp) (by rfl) (by
      simp [X86Routine.execute,popped,hr.2.2.2,put,tagResult,flags])
    exact X86Routine.Prefix.nil _
  apply (tag_prologue s f h).finish (fuel := 7) ?_ 11 (by decide)
  exact path.finish (fuel := 0) (by simp [X86Routine.run,tagResult]) 7 (by decide)


def unloadListed : X86Routine.Program
  | 0x24e30 => some (.push 3,1)
  | 0x24e31 => some (.push 2,1)
  | 0x24e32 => some (.xorRegister 3 3,2)
  | 0x24e34 => some (.control (.block (.lea 0 ⟨some 0,none,0,0⟩)),6)
  | 0x24e3a => some (.control (.block (.lea 2 ⟨some 2,none,0,0⟩)),6)
  | 0x24e40 => some (.control (.block (.load 0 ⟨some 3,none,0,0x2b708⟩)),6)
  | 0x24e46 => some (.control (.cmpImmediate ⟨some 0,none,0,-12⟩ 0x1d4a11),7)
  | 0x24e4d => some (.control (.jumpZero true 18),2)
  | 0x24e61 => some (.immediate 2 101,5)
  | 0x24e66 => some (.control (.block (.load 0 ⟨some 3,none,0,0x2b708⟩)),6)
  | 0x24e6c => some (.addImmediate 3 4,3)
  | 0x24e6f => some (.call 84796,5)
  | 0x24e74 => some (.compareRegister 3 40,3)
  | 0x24e77 => some (.control (.jumpZero false (-57)),2)
  | 0x24e79 => some (.pop 2,1)
  | 0x24e7a => some (.pop 3,1)
  | 0x24e7b => some (.ret,1)
  | _ => none

theorem unload_decoded (pc : Nat) (h : unloadListed pc≠none) : program pc=unloadListed pc := by
  fun_cases unloadListed pc <;> simp_all [unloadListed] <;> decide

def callListed (pc : Nat) := if pc < 0x24e74 then unloadListed pc else none
theorem call_decoded (pc : Nat) (h : callListed pc≠none) : program pc=callListed pc := by
  unfold callListed at h ⊢
  by_cases b : pc < 0x24e74
  · simp only [b,if_true] at h ⊢; exact unload_decoded pc h
  · simp [b] at h

def digit (s : X86Memory.State) := load32 s.memory (s.regs 3+(0x2b708#32))
def tagCall (s : X86Memory.State) : X86Memory.State :=
  X86Routine.pushWord ⟨write (write (write s.regs 0 (digit s)) 2 101) 3 (s.regs 3+(4#32)),s.memory⟩ 0x24e74

theorem unload_call (s : X86Memory.State) (f : Option Flags)
    (magic : load32 s.memory (digit s-(12#32))=0x1d4a11) :
    X86Routine.run callListed [0x399b0] 7 ⟨s,f,0x24e40⟩=some ⟨tagCall s,none,0x399b0⟩ := by
  let c1 := put s 0 (digit s)
  let c2 := put c1 2 101
  let c3 := put c2 3 (s.regs 3+(4#32))
  let flags := some (compare32 0x1d4a11 0x1d4a11)
  have path : X86Routine.Prefix callListed [0x399b0] 7 ⟨s,f,0x24e40⟩ ⟨tagCall s,none,0x399b0⟩ := by
    apply X86Routine.Prefix.step (op := .control (.block (.load 0 ⟨some 3,none,0,0x2b708⟩))) (length := 6) (middle := ⟨c1,f,0x24e46⟩) (by simp) (by simp [callListed,unloadListed]) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,X86Block.Address.eval,c1,digit,put])
    apply X86Routine.Prefix.step (op := .control (.cmpImmediate ⟨some 0,none,0,-12⟩ 0x1d4a11)) (length := 7) (middle := ⟨c1,flags,0x24e4d⟩) (by simp) (by simp [callListed,unloadListed]) (by
      simp [BitVec.sub_eq_add_neg] at magic
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,c1,put,write,flags,magic])
    apply X86Routine.Prefix.step (op := .control (.jumpZero true 18)) (length := 2) (middle := ⟨c1,flags,0x24e61⟩) (by simp) (by simp [callListed,unloadListed]) (by
      simp [X86Routine.execute,X86Control.execute,flags,compare32])
    apply X86Routine.Prefix.step (op := .immediate 2 101) (length := 5) (middle := ⟨c2,flags,0x24e66⟩) (by simp) (by simp [callListed,unloadListed]) (by rfl)
    apply X86Routine.Prefix.step (op := .control (.block (.load 0 ⟨some 3,none,0,0x2b708⟩))) (length := 6) (middle := ⟨c2,flags,0x24e6c⟩) (by simp) (by simp [callListed,unloadListed]) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,X86Block.Address.eval,c2,c1,digit,put,write]
      funext r; by_cases a : r=0 <;> by_cases b : r=2 <;> simp_all [write])
    apply X86Routine.Prefix.step (op := .addImmediate 3 4) (length := 3) (middle := ⟨c3,none,0x24e6f⟩) (by simp) (by simp [callListed,unloadListed]) (by
      simp [X86Routine.execute,c3,c2,c1,put,write])
    apply X86Routine.Prefix.step (op := .call 84796) (length := 5) (middle := ⟨tagCall s,none,0x399b0⟩) (by simp) (by simp [callListed,unloadListed]) (by
      simp [X86Routine.execute,tagCall,c3,c2,c1,put])
    exact X86Routine.Prefix.nil _
  exact path.finish (fuel := 0) (by rfl) 7 (by decide)

/-- One iteration's concrete memory effects: call-save, callee-save, tag write. -/
def iteration (s : X86Memory.State) := (tagResult (tagCall s) 0x24e74).core
structure IterationInputs (s : X86Memory.State) : Prop where
  magic : load32 s.memory (digit s-(12#32))=0x1d4a11
  tag : TagInputs (tagCall s) 0x24e74

theorem listed_active (pc : Nat) (h : tagListed pc≠none) : pc ∉ [0x24e74] := by
  simp only [List.mem_singleton]; intro eq; subst pc; contradiction

theorem iteration_execution (s : X86Memory.State) (f : Option Flags) (h : IterationInputs s) :
    X86Routine.run program [0x24e74] 18 ⟨s,f,0x24e40⟩=some (tagResult (tagCall s) 0x24e74) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (unload_call s f h.magic)
  have active (pc : Nat) (hn : callListed pc≠none) : pc ∉ [0x24e74] := by
    simp only [List.mem_singleton]; intro eq; subst pc
    simp [callListed] at hn
  have first := path.transfer program [0x24e74] call_decoded active
  have last : X86Routine.run program [0x24e74] 11 ⟨tagCall s,none,0x399b0⟩=some (tagResult (tagCall s) 0x24e74) := by
    rw [X86Routine.run_sound program tagListed tag_decoded _ _ _ (by rw [tag_execution _ _ h.tag]; simp)]
    exact tag_execution _ _ h.tag
  exact first.finish last 18 (by omega)




theorem program_active (pc : Nat) (h : program pc≠none) : pc ∉ [0x2a3c8] := by
  simp only [List.mem_singleton]; intro eq; subst pc; exact h (by decide)
theorem append_path {p exits n a b k c} (first : X86Routine.Prefix p exits n a b)
    (last : X86Routine.Prefix p exits k b c) : X86Routine.Prefix p exits (n+k) a c := by
  induction first with
  | nil => simpa using last
  | step active decoded executed rest ih =>
    simpa [Nat.succ_add] using X86Routine.Prefix.step active decoded executed (ih last)

def cycleEnd (s : X86Memory.State) : X86Control.State :=
  ⟨iteration s,some (compare32 ((iteration s).regs 3) 40),
    if (iteration s).regs 3=(40#32) then 0x24e79 else 0x24e40⟩

theorem cycle_prefix (s : X86Memory.State) (f : Option Flags) (h : IterationInputs s) :
    ∃ n, n ≤ 20 ∧ X86Routine.Prefix program [0x2a3c8] n ⟨s,f,0x24e40⟩ (cycleEnd s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (iteration_execution s f h)
  have path := path.transfer program [0x2a3c8] (fun _ _ => rfl) program_active
  have tail : X86Routine.Prefix program [0x2a3c8] 2 (tagResult (tagCall s) 0x24e74) (cycleEnd s) := by
    apply X86Routine.Prefix.step (op := .compareRegister 3 40) (length := 3) (middle := ⟨iteration s,some (compare32 ((iteration s).regs 3) 40),0x24e77⟩)
      (by simp [tagResult]) (show program 0x24e74=some (.compareRegister 3 40,3) from by decide) (by rfl)
    apply X86Routine.Prefix.step (op := .control (.jumpZero false (-57))) (length := 2) (middle := cycleEnd s) (by simp) (show program 0x24e77=some (.control (.jumpZero false (-57)),2) from by decide) (by
      by_cases eq : (iteration s).regs 3=(40#32) <;> simp [X86Routine.execute,X86Control.execute,cycleEnd,cmp32_zero,eq])
    exact X86Routine.Prefix.nil _
  exact ⟨n+2,by omega,append_path path tail⟩

def loopState (s : X86Memory.State) : Nat → X86Memory.State
  | 0 => s
  | n+1 => iteration (loopState s n)
def loopPoint (s : X86Memory.State) (f : Option Flags) (n : Nat) : X86Control.State :=
  ⟨loopState s n,if n=0 then f else some (compare32 (BitVec.ofNat 32 (4*n)) 40),
    if n=10 then 0x24e79 else 0x24e40⟩

theorem iteration_regs (s : X86Memory.State) :
    (iteration s).regs 3=s.regs 3+4 ∧ (iteration s).regs 4=s.regs 4 := by
  simp [iteration,tagResult,tagCall,X86Routine.pushWord,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem loop_counter (s : X86Memory.State) (zero : s.regs 3=0) (n : Nat) (hn : n ≤ 10) :
    (loopState s n).regs 3=BitVec.ofNat 32 (4*n) := by
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 ∨ n=9 ∨ n=10 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [loopState,iteration_regs,zero]

theorem loop_prefix (s : X86Memory.State) (f : Option Flags) (zero : s.regs 3=0)
    (n : Nat) (hn : n ≤ 10) (inputs : ∀ j, j<n → IterationInputs (loopState s j)) :
    ∃ k, k ≤ 20*n ∧ X86Routine.Prefix program [0x2a3c8] k ⟨s,f,0x24e40⟩ (loopPoint s f n) := by
  induction n with
  | zero => exact ⟨0,by decide,by simpa [loopPoint,loopState] using X86Routine.Prefix.nil ⟨s,f,0x24e40⟩⟩
  | succ n ih =>
    obtain ⟨k,hk,path⟩ := ih (by omega) (fun j hj => inputs j (by omega))
    obtain ⟨l,hl,next⟩ := cycle_prefix (loopState s n) (loopPoint s f n).flags (inputs n (by omega))
    have atStart : loopPoint s f n=⟨loopState s n,(loopPoint s f n).flags,0x24e40⟩ := by
      simp [loopPoint,show n≠10 by omega]
    have atEnd : cycleEnd (loopState s n)=loopPoint s f (n+1) := by
      have counter := loop_counter s zero (n+1) hn
      change (iteration (loopState s n)).regs 3=BitVec.ofNat 32 (4*(n+1)) at counter
      have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 ∨ n=9 := by omega
      unfold cycleEnd loopPoint
      rw [counter]
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    rw [← atStart,atEnd] at next
    exact ⟨k+l,by omega,append_path path next⟩



def unloadSaved (s : X86Memory.State) :=
  store32 (store32 s.memory (s.regs 4-(4#32)) (s.regs 3)) (s.regs 4-(8#32)) (s.regs 2)
def unloadStart (s : X86Memory.State) : X86Memory.State :=
  ⟨write (write s.regs 3 0) 4 (s.regs 4-(8#32)),unloadSaved s⟩

theorem unload_prologue (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [0x2a3c8] 5 ⟨s,f,0x24e30⟩ ⟨unloadStart s,some (logical32 0),0x24e40⟩ := by
  let c1 := X86Routine.pushWord s (s.regs 3)
  let c2 := X86Routine.pushWord c1 (s.regs 2)
  apply X86Routine.Prefix.step (op := .push 3) (length := 1) (middle := ⟨c1,f,0x24e31⟩)
    (by simp) (show program 0x24e30=some (.push 3,1) from by decide) (by rfl)
  apply X86Routine.Prefix.step (op := .push 2) (length := 1) (middle := ⟨c2,f,0x24e32⟩)
    (by simp) (show program 0x24e31=some (.push 2,1) from by decide) (by simp [X86Routine.execute,c2,c1,X86Routine.pushWord,write])
  apply X86Routine.Prefix.step (op := .xorRegister 3 3) (length := 2) (middle := ⟨unloadStart s,some (logical32 0),0x24e34⟩)
    (by simp) (show program 0x24e32=some (.xorRegister 3 3,2) from by decide) (by
      simp [X86Routine.execute,unloadStart,unloadSaved,c2,c1,X86Routine.pushWord,put,write,logical32,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      funext r; by_cases a : r=3 <;> by_cases b : r=4 <;> simp_all [write])
  apply X86Routine.Prefix.step (op := .control (.block (.lea 0 ⟨some 0,none,0,0⟩))) (length := 6)
    (middle := ⟨unloadStart s,some (logical32 0),0x24e3a⟩) (by simp)
    (show program 0x24e34=some (.control (.block (.lea 0 ⟨some 0,none,0,0⟩)),6) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,X86Block.Address.eval,put,write,unloadStart]
      funext r; by_cases a : r=0 <;> simp_all [write])
  apply X86Routine.Prefix.step (op := .control (.block (.lea 2 ⟨some 2,none,0,0⟩))) (length := 6)
    (middle := ⟨unloadStart s,some (logical32 0),0x24e40⟩) (by simp)
    (show program 0x24e3a=some (.control (.block (.lea 2 ⟨some 2,none,0,0⟩)),6) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,X86Block.Address.eval,put,write,unloadStart]
      funext r; by_cases a : r=2 <;> simp_all [write])
  exact X86Routine.Prefix.nil _

def unloaded (s : X86Memory.State) := loopState (unloadStart s) 10
structure UnloadInputs (s : X86Memory.State) : Prop where
  digits : ∀ n, n<10 → IterationInputs (loopState (unloadStart s) n)
  savedEdx : load32 (unloaded s).memory (s.regs 4-(8#32))=s.regs 2
  savedEbx : load32 (unloaded s).memory (s.regs 4-(4#32))=s.regs 3
  returnAddress : load32 (unloaded s).memory (s.regs 4)=0x24f97

def unloadResult (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (unloaded s).regs 2 (s.regs 2)) 3 (s.regs 3)) 4 (s.regs 4+(4#32)),(unloaded s).memory⟩,
    some (compare32 40 40),0x24f97⟩

theorem loop_sp (s : X86Memory.State) (n : Nat) : (loopState s n).regs 4=s.regs 4 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (iteration_regs (loopState s n)).2.trans ih

theorem unload_execution (s : X86Memory.State) (f : Option Flags) (h : UnloadInputs s) :
    ∃ k, k ≤ 208 ∧ X86Routine.Prefix program [0x2a3c8] k ⟨s,f,0x24e30⟩ (unloadResult s) := by
  obtain ⟨n,hn,path⟩ := loop_prefix (unloadStart s) (some (logical32 0)) (by simp [unloadStart,write]) 10 (by decide) h.digits
  have sp : (unloaded s).regs 4=s.regs 4-(8#32) := by simpa [unloaded,unloadStart,write] using loop_sp (unloadStart s) 10
  have edx := h.savedEdx
  have ebx := h.savedEbx
  simp [BitVec.sub_eq_add_neg] at edx ebx
  let c1 := put (put (unloaded s) 2 (s.regs 2)) 4 (s.regs 4-(4#32))
  let c2 := put (put c1 3 (s.regs 3)) 4 (s.regs 4)
  have tail : X86Routine.Prefix program [0x2a3c8] 3 (loopPoint (unloadStart s) (some (logical32 0)) 10) (unloadResult s) := by
    apply X86Routine.Prefix.step (op := .pop 2) (length := 1) (middle := ⟨c1,some (compare32 40 40),0x24e7a⟩)
      (by simp [loopPoint]) (show program 0x24e79=some (.pop 2,1) from by decide) (by
        change X86Routine.execute (.pop 2) ⟨unloaded s,some (compare32 40 40),0x24e7a⟩=_
        simp [X86Routine.execute,sp,edx,c1,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
        funext r; by_cases a : r=2 <;> by_cases b : r=4 <;> simp_all [write])
    apply X86Routine.Prefix.step (op := .pop 3) (length := 1) (middle := ⟨c2,some (compare32 40 40),0x24e7b⟩)
      (by simp) (show program 0x24e7a=some (.pop 3,1) from by decide) (by
        simp [X86Routine.execute,c2,c1,put,write,ebx,BitVec.sub_eq_add_neg,BitVec.add_assoc]
        funext r; by_cases a : r=3 <;> by_cases b : r=4 <;> simp_all [write])
    apply X86Routine.Prefix.step (op := .ret) (length := 1) (middle := unloadResult s)
      (by simp) (show program 0x24e7b=some (.ret,1) from by decide) (by
        simp [X86Routine.execute,c2,c1,put,write,h.returnAddress,unloadResult]
        funext r; by_cases a : r=2 <;> by_cases b : r=3 <;> by_cases c : r=4 <;> simp_all [write])
    exact X86Routine.Prefix.nil _
  exact ⟨5+n+3,by omega,append_path (append_path (unload_prologue s f) path) tail⟩



def responderListed : X86Routine.Program
  | 0x39aa0 => some (.push 3,1)
  | 0x39aa1 => some (.push 1,1)
  | 0x39aa2 => some (.push 2,1)
  | 0x39aa3 => some (.push 6,1)
  | 0x39aa4 => some (.push 7,1)
  | 0x39aa5 => some (.addImmediate 4 (-8),3)
  | 0x39aa8 => some (.control (.block (.legacy (.mov 7 0))),2)
  | 0x39aaa => some (.control (.block (.legacy (.load 2 0 0))),2)
  | 0x39aac => some (.compareRegister 2 1,3)
  | 0x39aaf => some (.control (.jumpZero false 71),2)
  | 0x39ab1 => some (.control (.block (.legacy (.load 0 0 4))),3)
  | 0x39ab4 => some (.xorHalf 0 0,3)
  | 0x39ab7 => some (.compareRegister 0 0x616d0000,5)
  | 0x39abc => some (.control (.jumpZero false 58),2)
  | 0x39abe => some (.control (.block (.legacy (.load 0 7 4))),3)
  | 0x39ac1 => some (.compareRegister 0 0x616d6500,5)
  | 0x39ac6 => some (.jumpUnsigned 0 1104,6)
  | 0x39acc => some (.jumpUnsigned 1 12,2)
  | 0x39ace => some (.compareRegister 0 0x616d7800,5)
  | 0x39ad3 => some (.control (.jumpZero true 24),2)
  | 0x39aed => some (.control (.block (.store ⟨none,none,0,0x75434⟩ 2)),6)
  | 0x39af3 => some (.jump 1060,5)
  | 0x39f1c => some (.xorRegister 0 0,2)
  | 0x39f1e => some (.addImmediate 4 8,3)
  | 0x39f21 => some (.pop 7,1)
  | 0x39f22 => some (.pop 6,1)
  | 0x39f23 => some (.pop 2,1)
  | 0x39f24 => some (.pop 1,1)
  | 0x39f25 => some (.pop 3,1)
  | 0x39f26 => some (.ret,1)
  | _ => none

theorem responder_decoded (pc : Nat) (h : responderListed pc≠none) : program pc=responderListed pc := by
  fun_cases responderListed pc <;> simp_all [responderListed] <;> decide

def responderSaved (s : X86Memory.State) :=
  store32 (store32 (store32 (store32 (store32 s.memory
    (s.regs 4-(4#32)) (s.regs 3)) (s.regs 4-(8#32)) (s.regs 1))
    (s.regs 4-(12#32)) (s.regs 2)) (s.regs 4-(16#32)) (s.regs 6)) (s.regs 4-(20#32)) (s.regs 7)
def responderStart (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write s.regs 4 (s.regs 4-(28#32))) 7 (s.regs 0),responderSaved s⟩,none,0x39aaa⟩
def responderMemory (s : X86Memory.State) := store32 (responderSaved s) (0x75434#32) 1
structure ResponderInputs (s : X86Memory.State) : Prop where
  eventType : load32 (responderSaved s) (s.regs 0)=1
  eventData : load32 (responderSaved s) (s.regs 0+(4#32))=0x616d7800
  savedEbx : load32 (responderMemory s) (s.regs 4-(4#32))=s.regs 3
  savedEcx : load32 (responderMemory s) (s.regs 4-(8#32))=s.regs 1
  savedEdx : load32 (responderMemory s) (s.regs 4-(12#32))=s.regs 2
  savedEsi : load32 (responderMemory s) (s.regs 4-(16#32))=s.regs 6
  savedEdi : load32 (responderMemory s) (s.regs 4-(20#32))=s.regs 7
  returnAddress : load32 (responderMemory s) (s.regs 4)=0x24fae

def responderResult (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write s.regs 0 0) 4 (s.regs 4+(4#32)),responderMemory s⟩,none,0x24fae⟩

theorem responder_prologue (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run responderListed [0x39aaa] 7 ⟨s,f,0x39aa0⟩=some (responderStart s) := by
  let c1 := X86Routine.pushWord s (s.regs 3)
  let c2 := X86Routine.pushWord c1 (s.regs 1)
  let c3 := X86Routine.pushWord c2 (s.regs 2)
  let c4 := X86Routine.pushWord c3 (s.regs 6)
  let c5 := X86Routine.pushWord c4 (s.regs 7)
  let c6 := put c5 4 (s.regs 4-(28#32))
  have path : X86Routine.Prefix responderListed [0x39aaa] 7 ⟨s,f,0x39aa0⟩ (responderStart s) := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x39aa1⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,c1,X86Routine.pushWord,write])
    apply X86Routine.Prefix.step (middle := ⟨c2,f,0x39aa2⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,c1,c2,X86Routine.pushWord,write])
    apply X86Routine.Prefix.step (middle := ⟨c3,f,0x39aa3⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,c1,c2,c3,X86Routine.pushWord,write])
    apply X86Routine.Prefix.step (middle := ⟨c4,f,0x39aa4⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,c1,c2,c3,c4,X86Routine.pushWord,write])
    apply X86Routine.Prefix.step (middle := ⟨c5,f,0x39aa5⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,c1,c2,c3,c4,c5,X86Routine.pushWord,write])
    apply X86Routine.Prefix.step (middle := ⟨c6,none,0x39aa8⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,c6,c5,c4,c3,c2,c1,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := responderStart s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
        responderStart,responderSaved,c6,c5,c4,c3,c2,c1,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      funext r; by_cases a : r=4 <;> by_cases b : r=7 <;> simp_all [write])
    exact X86Routine.Prefix.nil _
  exact path.finish (fuel := 0) (by simp [X86Routine.run,responderStart]) 7 (by decide)

theorem responder_execution (s : X86Memory.State) (f : Option Flags) (h : ResponderInputs s) :
    X86Routine.run responderListed [0x24fae] 30 ⟨s,f,0x39aa0⟩=some (responderResult s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (responder_prologue s f)
  have path := path.transfer responderListed [0x24fae] (fun _ _ => rfl) (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; contradiction)
  rcases h with ⟨eventType,eventData,ebx,ecx,edx,esi,edi,ret⟩
  simp [BitVec.sub_eq_add_neg] at ebx ecx edx esi edi
  let c0 := (responderStart s).core
  let c1 := put c0 2 1
  let c2 := put c1 0 0x616d7800
  let c3 := put c1 0 0x616d0000
  let c4 : X86Memory.State := {c2 with memory := responderMemory s}
  let c5 := put c4 0 0
  let c6 := put c5 4 (s.regs 4-(20#32))
  let c7 := put (put c6 7 (s.regs 7)) 4 (s.regs 4-(16#32))
  let c8 := put (put c7 6 (s.regs 6)) 4 (s.regs 4-(12#32))
  let c9 := put (put c8 2 (s.regs 2)) 4 (s.regs 4-(8#32))
  let c10 := put (put c9 1 (s.regs 1)) 4 (s.regs 4-(4#32))
  let c11 := put (put c10 3 (s.regs 3)) 4 (s.regs 4)
  let f1 := some (compare32 1 1)
  let f2 : Option Flags := some ⟨true,false,false,some false⟩
  let f3 := some (compare32 0x616d0000 0x616d0000)
  let f4 := some (compare32 0x616d7800 0x616d6500)
  let f5 := some (compare32 0x616d7800 0x616d7800)
  have tail : X86Routine.Prefix responderListed [0x24fae] 23 (responderStart s) (responderResult s) := by
    apply X86Routine.Prefix.step (middle := ⟨c1,none,0x39aac⟩) (by simp [responderStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c1,f1,0x39aaf⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c1,f1,0x39ab1⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c2,f1,0x39ab4⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c3,f2,0x39ab7⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c3,f3,0x39abc⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c3,f3,0x39abe⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c2,f3,0x39ac1⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c2,f4,0x39ac6⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c2,f4,0x39acc⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c2,f4,0x39ace⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c2,f5,0x39ad3⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c2,f5,0x39aed⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c4,f5,0x39af3⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c4,f5,0x39f1c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c5,some (logical32 0),0x39f1e⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c6,none,0x39f21⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c7,none,0x39f22⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c8,none,0x39f23⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c9,none,0x39f24⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c10,none,0x39f25⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨c11,none,0x39f26⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := responderResult s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,responderStart,responderResult,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,f1,f2,f3,f4,f5,
        eventType,eventData,ebx,ecx,edx,esi,edi,ret,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        compare32,logical32,BitVec.msb]
      try rfl
      try (funext r; by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=3 <;>
        by_cases e : r=4 <;> by_cases f : r=6 <;> by_cases g : r=7 <;> simp_all [write]))
    exact X86Routine.Prefix.nil _
  exact path.finish (tail.finish (fuel := 0) (by simp [X86Routine.run,responderResult]) 23 (by decide)) 30 (by omega)



def stopListed : X86Routine.Program
  | 0x24f90 => some (.push 3,1)
  | 0x24f91 => some (.push 2,1)
  | 0x24f92 => some (.call (-359),5)
  | 0x24f97 => some (.immediate 0 0x12c98,5)
  | 0x24f9c => some (.xorRegister 2 2,2)
  | 0x24f9e => some (.immediate 3 1,5)
  | 0x24fa3 => some (.control (.block (.store ⟨none,none,0,0x12c5c⟩ 2)),6)
  | 0x24fa9 => some (.call 84722,5)
  | 0x24fae => some (.control (.block (.store ⟨none,none,0,0x12c94⟩ 3)),6)
  | 0x24fb4 => some (.pop 2,1)
  | 0x24fb5 => some (.pop 3,1)
  | 0x24fb6 => some (.ret,1)
  | _ => none

theorem stop_decoded (pc : Nat) (h : stopListed pc≠none) : program pc=stopListed pc := by
  fun_cases stopListed pc <;> simp_all [stopListed] <;> decide

def stopUnload (s : X86Memory.State) : X86Memory.State :=
  X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 2)) 0x24f97

def stopResponder (s : X86Memory.State) : X86Memory.State :=
  let u := (unloadResult (stopUnload s)).core
  X86Routine.pushWord ⟨write (write (write u.regs 0 0x12c98) 2 0) 3 1,
    store32 u.memory (0x12c5c#32) 0⟩ 0x24fae

def stopMemory (s : X86Memory.State) := store32 (responderMemory (stopResponder s)) (0x12c94#32) 1
structure StopInputs (s : X86Memory.State) : Prop where
  unload : UnloadInputs (stopUnload s)
  responder : ResponderInputs (stopResponder s)
  savedEdx : load32 (stopMemory s) (s.regs 4-(8#32))=s.regs 2
  savedEbx : load32 (stopMemory s) (s.regs 4-(4#32))=s.regs 3
  returnAddress : load32 (stopMemory s) (s.regs 4)=0x2a3c8

def stopResult (s : X86Memory.State) : X86Control.State :=
  let r := (responderResult (stopResponder s)).core
  ⟨⟨write (write (write r.regs 2 (s.regs 2)) 3 (s.regs 3)) 4 (s.regs 4+(4#32)),stopMemory s⟩,none,0x2a3c8⟩

theorem stop_prologue (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [0x2a3c8] 3 ⟨s,f,0x24f90⟩ ⟨stopUnload s,f,0x24e30⟩ := by
  let c1 := X86Routine.pushWord s (s.regs 3)
  let c2 := X86Routine.pushWord c1 (s.regs 2)
  apply X86Routine.Prefix.step (op := .push 3) (length := 1) (middle := ⟨c1,f,0x24f91⟩)
    (by simp) (show program 0x24f90=some (.push 3,1) from by decide) (by rfl)
  apply X86Routine.Prefix.step (op := .push 2) (length := 1) (middle := ⟨c2,f,0x24f92⟩)
    (by simp) (show program 0x24f91=some (.push 2,1) from by decide) (by simp [X86Routine.execute,c2,c1,X86Routine.pushWord,write])
  apply X86Routine.Prefix.step (op := .call (-359)) (length := 5) (middle := ⟨stopUnload s,f,0x24e30⟩)
    (by simp) (show program 0x24f92=some (.call (-359),5) from by decide) (by rfl)
  exact X86Routine.Prefix.nil _

theorem stop_event_call (s : X86Memory.State) :
    X86Routine.Prefix program [0x2a3c8] 5 (unloadResult (stopUnload s)) ⟨stopResponder s,some (logical32 0),0x39aa0⟩ := by
  let u := (unloadResult (stopUnload s)).core
  let c1 := put u 0 0x12c98
  let c2 := put c1 2 0
  let c3 := put c2 3 1
  let c4 : X86Memory.State := {c3 with memory := store32 u.memory (0x12c5c#32) 0}
  apply X86Routine.Prefix.step (op := .immediate 0 0x12c98) (length := 5) (middle := ⟨c1,some (compare32 40 40),0x24f9c⟩)
    (by simp [unloadResult]) (show program 0x24f97=some (.immediate 0 0x12c98,5) from by decide) (by rfl)
  apply X86Routine.Prefix.step (op := .xorRegister 2 2) (length := 2) (middle := ⟨c2,some (logical32 0),0x24f9e⟩)
    (by simp) (show program 0x24f9c=some (.xorRegister 2 2,2) from by decide) (by simp [X86Routine.execute,c2,logical32])
  apply X86Routine.Prefix.step (op := .immediate 3 1) (length := 5) (middle := ⟨c3,some (logical32 0),0x24fa3⟩)
    (by simp) (show program 0x24f9e=some (.immediate 3 1,5) from by decide) (by rfl)
  apply X86Routine.Prefix.step (op := .control (.block (.store ⟨none,none,0,0x12c5c⟩ 2))) (length := 6)
    (middle := ⟨c4,some (logical32 0),0x24fa9⟩) (by simp)
    (show program 0x24fa3=some (.control (.block (.store ⟨none,none,0,0x12c5c⟩ 2)),6) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,X86Block.Address.eval,c4,c3,c2,c1,put,write])
  apply X86Routine.Prefix.step (op := .call 84722) (length := 5)
    (middle := ⟨stopResponder s,some (logical32 0),0x39aa0⟩) (by simp)
    (show program 0x24fa9=some (.call 84722,5) from by decide) (by
      simp [X86Routine.execute,stopResponder,u,c4,c3,c2,c1,put])
  exact X86Routine.Prefix.nil _

theorem stop_return (s : X86Memory.State) (h : StopInputs s) :
    X86Routine.Prefix program [0x2a3c8] 4 (responderResult (stopResponder s)) (stopResult s) := by
  let r := (responderResult (stopResponder s)).core
  let c1 : X86Memory.State := {r with memory := stopMemory s}
  let c2 := put (put c1 2 (s.regs 2)) 4 (s.regs 4-(4#32))
  let c3 := put (put c2 3 (s.regs 3)) 4 (s.regs 4)
  have sp : r.regs 4=s.regs 4-(8#32) := by
    simp [r,responderResult,stopResponder,unloadResult,stopUnload,X86Routine.pushWord,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have ebx : r.regs 3=1 := by simp [r,responderResult,stopResponder,X86Routine.pushWord,write]
  have savedEdx := h.savedEdx
  have savedEbx := h.savedEbx
  simp [BitVec.sub_eq_add_neg] at savedEdx savedEbx
  apply X86Routine.Prefix.step (op := .control (.block (.store ⟨none,none,0,0x12c94⟩ 3))) (length := 6)
    (middle := ⟨c1,none,0x24fb4⟩) (by simp [responderResult])
    (show program 0x24fae=some (.control (.block (.store ⟨none,none,0,0x12c94⟩ 3)),6) from by decide) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,X86Block.Address.eval,c1,ebx,stopMemory,r,responderResult,stopResponder,X86Routine.pushWord,write])
  apply X86Routine.Prefix.step (op := .pop 2) (length := 1) (middle := ⟨c2,none,0x24fb5⟩) (by simp)
    (show program 0x24fb4=some (.pop 2,1) from by decide) (by
      simp [X86Routine.execute,c2,c1,sp,put,write,savedEdx,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      funext q; by_cases a : q=2 <;> by_cases b : q=4 <;> simp_all [write])
  apply X86Routine.Prefix.step (op := .pop 3) (length := 1) (middle := ⟨c3,none,0x24fb6⟩) (by simp)
    (show program 0x24fb5=some (.pop 3,1) from by decide) (by
      simp [X86Routine.execute,c3,c2,c1,put,write,savedEbx,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      funext q; by_cases a : q=3 <;> by_cases b : q=4 <;> simp_all [write])
  apply X86Routine.Prefix.step (op := .ret) (length := 1) (middle := stopResult s) (by simp)
    (show program 0x24fb6=some (.ret,1) from by decide) (by
      simp [X86Routine.execute,c3,c2,c1,put,write,h.returnAddress,stopResult,r]
      funext q; by_cases a : q=2 <;> by_cases b : q=3 <;> by_cases c : q=4 <;> simp_all [write])
  exact X86Routine.Prefix.nil _

theorem stop_execution (s : X86Memory.State) (f : Option Flags) (h : StopInputs s) :
    X86Routine.run program [0x2a3c8] 250 ⟨s,f,0x24f90⟩=some (stopResult s) := by
  obtain ⟨n,hn,unload⟩ := unload_execution (stopUnload s) f h.unload
  obtain ⟨k,hk,event,_⟩ := X86Routine.run_path (responder_execution (stopResponder s) (some (logical32 0)) h.responder)
  have event := event.transfer program [0x2a3c8] responder_decoded (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; contradiction)
  have path := append_path (append_path (append_path (append_path (stop_prologue s f) unload) (stop_event_call s)) event) (stop_return s h)
  exact path.finish (fuel := 0) (by simp [X86Routine.run,stopResult]) 250 (by omega)

end Doom.Proofs.AutomapStop

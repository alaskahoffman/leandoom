import Doom.Proofs.OriginalUseButton
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.PspriteStep
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0x53,0x51,0x52,0x56,0x57,0x89,0xc7,0x8d,0x88,0xf4,0x0,0x0,0x0,0x31,0xf6,0x8b,0x19,0x85,0xdb,0x74,0x20,0x8b,0x51,0x4,0x83,0xfa,0xff,0x74,0x18,0x8d,0x5a,0xff,0x89,0x59,0x4,0x85,0xdb,0x75,0xe,0x8b,0x19,0x89,0xf8,0x89,0xf2,0x8b,0x5b,0x10,0xe8,0xab,0xf3,0xff,0xff]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2dc60 ≤ pc ∧ pc < 0x2dc95 then X86Routine.decodeAt bytes (pc-0x2dc60) else none
def program := bytesProgram code
def exits := [0x2dc95,0x2d040]
def listed : X86Routine.Program
  | 0x2dc60 => some (.push 3,1)
  | 0x2dc61 => some (.push 1,1)
  | 0x2dc62 => some (.push 2,1)
  | 0x2dc63 => some (.push 6,1)
  | 0x2dc64 => some (.push 7,1)
  | 0x2dc65 => some (.control (.block (.legacy (.mov 7 0))),2)
  | 0x2dc67 => some (.control (.block (.lea 1 ⟨some 0,none,0,244⟩)),6)
  | 0x2dc6d => some (.xorRegister 6 6,2)
  | 0x2dc6f => some (.control (.block (.legacy (.load 3 1 0))),2)
  | 0x2dc71 => some (.control (.testWord 3 3),2)
  | 0x2dc73 => some (.control (.jumpZero true 32),2)
  | 0x2dc75 => some (.control (.block (.legacy (.load 2 1 4))),3)
  | 0x2dc78 => some (.compareRegister 2 0xffffffff,3)
  | 0x2dc7b => some (.control (.jumpZero true 24),2)
  | 0x2dc7d => some (.control (.block (.legacy (.lea 3 2 0xffffffff))),3)
  | 0x2dc80 => some (.control (.block (.store ⟨some 1,none,0,4⟩ 3)),3)
  | 0x2dc83 => some (.control (.testWord 3 3),2)
  | 0x2dc85 => some (.control (.jumpZero false 14),2)
  | 0x2dc87 => some (.control (.block (.legacy (.load 3 1 0))),2)
  | 0x2dc89 => some (.control (.block (.legacy (.mov 0 7))),2)
  | 0x2dc8b => some (.control (.block (.legacy (.mov 2 6))),2)
  | 0x2dc8d => some (.control (.block (.legacy (.load 3 3 16))),3)
  | 0x2dc90 => some (.call (-3157),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- The actual callee saves five registers before selecting weapon slot zero. -/
def saved (s : X86Memory.State) : X86Memory.State :=
  X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord
    (X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 1))
    (s.regs 2)) (s.regs 6)) (s.regs 7)
def entered (s : X86Memory.State) : X86Control.State :=
  ⟨put (put (put (saved s) 7 (s.regs 0)) 1 (s.regs 0+244)) 6 0,
    some {(logical32 0) with carry := some false},0x2dc6f⟩

theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2dc6f] 8 ⟨s,f,0x2dc60⟩=some (entered s) := by
  let c1 := X86Routine.pushWord s (s.regs 3)
  let c2 := X86Routine.pushWord c1 (s.regs 1)
  let c3 := X86Routine.pushWord c2 (s.regs 2)
  let c4 := X86Routine.pushWord c3 (s.regs 6)
  let c5 := saved s
  let c6 := put c5 7 (s.regs 0)
  let c7 := put c6 1 (s.regs 0+244)
  have path : X86Routine.Prefix listed [0x2dc6f] 8 ⟨s,f,0x2dc60⟩ (entered s) := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2dc61⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2dc62⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨c3,f,0x2dc63⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨c4,f,0x2dc64⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨c5,f,0x2dc65⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨c6,f,0x2dc67⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨c7,f,0x2dc6d⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,
        X86Block.Address.eval, c7,c6,c5,saved,X86Routine.pushWord,put,write])
    apply X86Routine.Prefix.step (middle := entered s) (by simp) rfl (by
      simp [X86Routine.execute,entered,c7,c6,c5,put,write])
    exact X86Routine.Prefix.nil _
  have run : X86Routine.run listed [0x2dc6f] 8 ⟨s,f,0x2dc60⟩=some (entered s) := path.finish (fuel := 0) (by simp [X86Routine.run,entered]) 8 (by decide)
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def stateWord (s : X86Memory.State) : Word := load32 s.memory (s.regs 1)
def tics (s : X86Memory.State) : Word := load32 s.memory (s.regs 1+4)
def counting (s : X86Memory.State) : X86Memory.State :=
  put (put s 3 (stateWord s)) 2 (tics s)
def decremented (s : X86Memory.State) : X86Memory.State :=
  {put (counting s) 3 (tics s-1) with memory := store32 s.memory (s.regs 1+4) (tics s-1)}
def dispatch (s : X86Memory.State) : X86Memory.State :=
  let c := decremented s
  put (put (put c 0 (s.regs 7)) 2 (s.regs 6)) 3
    (load32 c.memory (load32 c.memory (s.regs 1)+16))
def result (s : X86Memory.State) : X86Control.State :=
  if stateWord s=0 then ⟨put s 3 0,some (logical32 0),0x2dc95⟩
  else if tics s=0xffffffff then ⟨counting s,some (compare32 (tics s) 0xffffffff),0x2dc95⟩
  else if tics s-1=0 then
    ⟨X86Routine.pushWord (dispatch s) 0x2dc95,some (logical32 0),0x2d040⟩
  else ⟨decremented s,some (logical32 (tics s-1)),0x2dc95⟩

def checkedState (s : X86Memory.State) : X86Control.State :=
  ⟨put s 3 (stateWord s),some (logical32 (stateWord s)),if stateWord s=0 then 0x2dc95 else 0x2dc75⟩
def checkedTimer (s : X86Memory.State) : X86Control.State :=
  ⟨put s 2 (tics s),some (compare32 (tics s) 0xffffffff),if tics s=0xffffffff then 0x2dc95 else 0x2dc7d⟩
def counted (s : X86Memory.State) : X86Control.State :=
  ⟨{put s 3 (s.regs 2+(0xffffffff#32)) with memory := store32 s.memory (s.regs 1+4) (s.regs 2+(0xffffffff#32))},
    some (logical32 (s.regs 2+(0xffffffff#32))),if s.regs 2+(0xffffffff#32)=0 then 0x2dc87 else 0x2dc95⟩
def called (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put (put s 0 (s.regs 7)) 2 (s.regs 6)) 3
    (load32 s.memory (load32 s.memory (s.regs 1)+16))) 0x2dc95,f,0x2d040⟩

private theorem state_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2dc75,0x2dc95] 3 ⟨s,f,0x2dc6f⟩=some (checkedState s) := by
  have run : X86Routine.run listed [0x2dc75,0x2dc95] 3 ⟨s,f,0x2dc6f⟩=some (checkedState s) := by
    by_cases h : stateWord s=(0#32) <;>
    simp [stateWord] at h <;>
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,X86Block.Address.eval,X86.execute,blockPreservesFlags,
      checkedState,stateWord,put,write,logical32,h, List.mem_cons,List.not_mem_nil,or_false,Nat.reduceEqDiff,Fin.reduceEq,↓reduceIte,
      Bind.bind,Option.bind,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.and_self,beq_iff_eq,
      decide_true,decide_false,Bool.true_eq_false,Bool.false_eq_true]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

private theorem timer_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2dc7d,0x2dc95] 3 ⟨s,f,0x2dc75⟩=some (checkedTimer s) := by
  have run : X86Routine.run listed [0x2dc7d,0x2dc95] 3 ⟨s,f,0x2dc75⟩=some (checkedTimer s) := by
    by_cases h : tics s=(0xffffffff#32) <;>
    simp [tics] at h <;>
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,X86Block.Address.eval,X86.execute,blockPreservesFlags,
      checkedTimer,tics,put,write,WeaponSelect.compare_zero,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

private theorem minus_one (v : Word) : v+(0xffffffff#32)=v-(1#32) := by
  rw [BitVec.sub_eq_add_neg,BitVec.neg_one_eq_allOnes]; rfl

private theorem count_prefix (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [0x2dc87,0x2dc95] 3 ⟨s,f,0x2dc7d⟩
      ⟨(counted s).core,(counted s).flags,0x2dc85⟩ := by
  let v := s.regs 2+(0xffffffff#32)
  let c1 := put s 3 v
  let c2 : X86Memory.State := {c1 with memory := store32 s.memory (s.regs 1+4) v}
  apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2dc80⟩) (by simp) rfl rfl
  apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2dc83⟩) (by simp) rfl (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,
      X86Block.Address.eval,c1,c2,put,write])
  apply X86Routine.Prefix.step (middle := ⟨(counted s).core,(counted s).flags,0x2dc85⟩) (by simp) rfl (by
    simp [X86Routine.execute,X86Control.execute,counted,c2,c1,v,put,write])
  exact X86Routine.Prefix.nil _

private theorem count_tail (c : X86Memory.State) (v : Word) :
    X86Routine.run listed [0x2dc87,0x2dc95] 1 ⟨c,some (logical32 v),0x2dc85⟩=
      some ⟨c,some (logical32 v),if v=0 then 0x2dc87 else 0x2dc95⟩ := by
  by_cases h : v=(0#32) <;>
  simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,logical32,h]

private theorem count_listed (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x2dc87,0x2dc95] 4 ⟨s,f,0x2dc7d⟩=some (counted s) :=
  (count_prefix s f).finish (count_tail (counted s).core (s.regs 2+(0xffffffff#32))) 4 (by decide)

private theorem count_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2dc87,0x2dc95] 4 ⟨s,f,0x2dc7d⟩=some (counted s) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [count_listed]; simp),count_listed]

private theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program exits 5 ⟨s,f,0x2dc87⟩=some (called s f) := by
  have run : X86Routine.run listed exits 5 ⟨s,f,0x2dc87⟩=some (called s f) := by
    simp [X86Routine.run,listed,exits,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,X86Block.Address.eval,X86.execute,blockPreservesFlags,
      called,put,write,X86Routine.pushWord]
    funext r
    by_cases h : r=3 <;> simp_all [write]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

private theorem join {s t u : X86Control.State} {stops : List Nat} {n m : Nat}
    (first : X86Routine.run program stops n s=some t)
    (last : X86Routine.run program exits m t=some u) :
    X86Routine.run program exits (n+m) s=some u := by
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path first
  have path := path.transfer program exits (by intros; rfl) (by
    intro a ha; simp only [exits,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨fun e => by subst a; exact ha (by decide),fun e => by subst a; exact ha (by decide)⟩)
  exact path.finish last (n+m) (by omega)

/-- Every 32-bit timer is covered, including zero/negative/wrapping values.
Expired timers reach the actual setter CALL; the setter itself is not stubbed. -/
theorem slot_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program exits 15 ⟨s,f,0x2dc6f⟩=some (result s) := by
  apply join (state_execution s f) (m := 12)
  by_cases empty : stateWord s=(0#32)
  · simp [checkedState,result,empty,X86Routine.run,exits]
  · have first := timer_execution (checkedState s).core (checkedState s).flags
    have atTimer : checkedState s=⟨(checkedState s).core,(checkedState s).flags,0x2dc75⟩ := by simp [checkedState,empty]
    rw [←atTimer] at first
    apply join first (m := 9)
    have timer_eq : checkedTimer (checkedState s).core=
        ⟨counting s,some (compare32 (tics s) 0xffffffff),if tics s=0xffffffff then 0x2dc95 else 0x2dc7d⟩ := rfl
    rw [timer_eq]
    by_cases infinite : tics s=(0xffffffff#32)
    · simp [result,empty,infinite,X86Routine.run,exits]
    · simp only [BitVec.ofNat_eq_ofNat,infinite,↓reduceIte]
      apply join (count_execution (counting s) (some (compare32 (tics s) 0xffffffff))) (m := 5)
      have count_eq : counted (counting s)=
          ⟨decremented s,some (logical32 (tics s-1)),if tics s-1=0 then 0x2dc87 else 0x2dc95⟩ := by
        simp only [counted,counting,decremented,put,write,Fin.reduceEq,↓reduceIte,minus_one,BitVec.ofNat_eq_ofNat]
      rw [count_eq]
      by_cases zero : tics s-(1#32)=(0#32)
      · simp only [result,BitVec.ofNat_eq_ofNat,empty,infinite,zero,↓reduceIte]
        have last := call_execution (decremented s) (some (logical32 0))
        exact last
      · simp [result,empty,infinite,zero,X86Routine.run,exits]

/-- Entry and first slot compose without a memory or register reset. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program exits 23 ⟨s,f,0x2dc60⟩=some (result (entered s).core) := by
  have tail := slot_execution (entered s).core (entered s).flags
  have tail : X86Routine.run program exits 15 (entered s)=some (result (entered s).core) := tail
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (entry_execution s f)
  have path := path.transfer program exits (by intros; rfl) (by
    intro a ha; simp only [exits,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨fun e => by subst a; exact ha (by decide),fun e => by subst a; exact ha (by decide)⟩)
  exact path.finish tail 23 (by omega)

/-- The transition receives the player, slot index, next state, and the genuine
return address; the setter's own effects remain a separate obligation. -/
theorem dispatch_arguments (s : X86Memory.State) (present : stateWord s≠0)
    (finite : tics s≠0xffffffff) (expired : tics s-1=0) :
    (result s).pc=0x2d040 ∧ (result s).core.regs 0=s.regs 7 ∧
    (result s).core.regs 2=s.regs 6 ∧
    (result s).core.regs 3=load32 (decremented s).memory
      (load32 (decremented s).memory (s.regs 1)+16) ∧
    load32 (result s).core.memory ((result s).core.regs 4)=0x2dc95 := by
  simp only [BitVec.ofNat_eq_ofNat] at present finite expired
  simp [result,present,finite,expired,dispatch,X86Routine.pushWord,put,write,load_store]

end Doom.Proofs.PspriteStep

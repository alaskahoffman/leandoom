import Doom.Proofs.OriginalKillEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.KillBookkeeping
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x85,0xc9,0x74,0x40,0x8b,0x81,0x84,0x0,0x0,0x0,0x85,0xc0,0x74,0x36,0xf6,0x43,0x6a,0x40,0x74,0x6,0xff,0x80,0xcc,0x0,0x0,0x0,0x8b,0xab,0x84,0x0,0x0,0x0,0x85,0xed,0x74,0x35,0x89,0xea,0x81,0xea,0x78,0xae,0x2,0x0,0xbe,0x18,0x1,0x0,0x0,0x89,0xd0,0xc1,0xfa,0x1f,0xf7,0xfe,0x8b,0x91,0x84,0x0,0x0,0x0,0xff,0x44,0x82,0x60,0xeb,0x15,0x83,0x3d,0x0,0xb4,0x2,0x0,0x0,0x75,0xc,0xf6,0x43,0x6a,0x40,0x74,0x6,0xff,0x5,0x44,0xaf,0x2,0x0,0x8b,0xbb,0x84,0x0,0x0,0x0,0x85,0xff,0xf,0x84,0x7b,0x0,0x0,0x0,0x85,0xc9,0x75,0x1a,0x89,0xfa,0x81,0xea,0x78,0xae,0x2,0x0,0xb9,0x18,0x1,0x0,0x0,0x89,0xd0,0xc1,0xfa,0x1f,0xf7,0xf9,0x89,0xfa,0xff,0x44,0x82,0x60,0x8a,0x4b,0x68,0x80,0xe1,0xfd,0x8b,0x83,0x84,0x0,0x0,0x0,0x88,0x4b,0x68,0xc7,0x40,0x4,0x1,0x0,0x0,0x0,0x8b,0x83,0x84,0x0,0x0,0x0,0xe8,0x34,0x2f,0x0,0x0]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2a2e6 ≤ pc ∧ pc < 0x2a38c then X86Routine.decodeAt bytes (pc-0x2a2e6) else none
def program := bytesProgram code

def creditListed : X86Routine.Program
  | 0x2a2e6 => some (.control (.testWord 1 1),2)
  | 0x2a2e8 => some (.control (.jumpZero true 64),2)
  | 0x2a32a => some (.control (.cmpImmediate ⟨none,none,0,0x2b400⟩ 0),7)
  | 0x2a331 => some (.control (.jumpZero false 12),2)
  | 0x2a333 => some (.testMemoryByte ⟨some 3,none,0,106⟩ 64,4)
  | 0x2a337 => some (.control (.jumpZero true 6),2)
  | 0x2a339 => some (.incrementMemory ⟨none,none,0,0x2af44⟩,6)
  | _ => none

def fragListed : X86Routine.Program
  | 0x2a33f => some (.control (.block (.load 7 ⟨some 3,none,0,132⟩)),6)
  | 0x2a345 => some (.control (.testWord 7 7),2)
  | 0x2a347 => some (.control (.jumpZero true 123),6)
  | 0x2a34d => some (.control (.testWord 1 1),2)
  | 0x2a34f => some (.control (.jumpZero false 26),2)
  | 0x2a351 => some (.control (.block (.legacy (.mov 2 7))),2)
  | 0x2a353 => some (.addImmediate 2 (-0x2ae78),6)
  | 0x2a359 => some (.immediate 1 280,5)
  | 0x2a35e => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2a360 => some (.sar 2 31,3)
  | 0x2a363 => some (.signedDivide 1,2)
  | 0x2a365 => some (.control (.block (.legacy (.mov 2 7))),2)
  | 0x2a367 => some (.incrementMemory ⟨some 2,some 0,2,96⟩,4)
  | _ => none

def markListed : X86Routine.Program
  | 0x2a36b => some (.control (.loadByte 1 ⟨some 3,none,0,104⟩),3)
  | 0x2a36e => some (.andByteImmediate 1 0xfd,3)
  | 0x2a371 => some (.control (.block (.load 0 ⟨some 3,none,0,132⟩)),6)
  | 0x2a377 => some (.storeByte ⟨some 3,none,0,104⟩ 1,3)
  | 0x2a37a => some (.storeImmediate ⟨some 0,none,0,4⟩ 1,7)
  | 0x2a381 => some (.control (.block (.load 0 ⟨some 3,none,0,132⟩)),6)
  | 0x2a387 => some (.call 12084,5)
  | _ => none

theorem credit_decoded (pc : Nat) (h : creditListed pc ≠ none) : program pc=creditListed pc := by
  fun_cases creditListed pc <;> simp_all [creditListed] <;> decide
theorem frag_decoded (pc : Nat) (h : fragListed pc ≠ none) : program pc=fragListed pc := by
  fun_cases fragListed pc <;> simp_all [fragListed] <;> decide
theorem mark_decoded (pc : Nat) (h : markListed pc ≠ none) : program pc=markListed pc := by
  fun_cases markListed pc <;> simp_all [markListed] <;> decide

def counted (s : X86Memory.State) := s.memory (s.regs 3+(106#32)) &&& (64#8)
def net (s : X86Memory.State) := load32 s.memory (0x2b400#32)
def creditMemory (s : X86Memory.State) :=
  if net s=0 ∧ counted s≠0 then store32 s.memory (0x2af44#32) (load32 s.memory (0x2af44#32)+1) else s.memory
def creditFlags (s : X86Memory.State) :=
  if net s≠0 then some (compare32 (net s) 0)
  else if counted s=0 then some (logical8 (counted s)) else none
def credited (s : X86Memory.State) : X86Control.State := ⟨{s with memory := creditMemory s},creditFlags s,0x2a33f⟩

theorem credit_execution (s : X86Memory.State) (f : Option Flags) (source : s.regs 1=0) :
    X86Routine.run creditListed [0x2a33f] 7 ⟨s,f,0x2a2e6⟩ = some (credited s) := by
  by_cases hn : net s=(0#32) <;> by_cases hc : counted s=(0#8) <;>
    simp only [net] at hn <;> simp only [counted] at hc <;>
    simp [X86Routine.run,creditListed,X86Routine.execute,X86Control.execute,X86Block.Address.eval,
      credited,creditMemory,creditFlags,source,logical32,logical8,compare32,net,counted,hn,hc] <;> (intro _; rfl)

def player (i : Fin 4) : Word := 0x2ae78+BitVec.ofNat 32 (280*i.val)
def fragAddress (i : Fin 4) : Word := player i + BitVec.ofNat 32 (4*i.val) + 96
def fragged (s : X86Memory.State) (i : Fin 4) : X86Control.State :=
  ⟨⟨write (write (write (write s.regs 0 (BitVec.ofNat 32 i.val)) 1 280) 2 (player i)) 7 (player i),
    store32 s.memory (fragAddress i) (load32 s.memory (fragAddress i)+1)⟩,none,0x2a36b⟩

theorem frag_execution (s : X86Memory.State) (f : Option Flags) (i : Fin 4)
    (source : s.regs 1=0) (ptr : load32 s.memory (s.regs 3+(132#32))=player i) :
    X86Routine.run fragListed [0x2a36b] 13 ⟨s,f,0x2a33f⟩ = some (fragged s i) := by
  rcases i with ⟨i,hi⟩
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp (config := { maxSteps := 500000 }) [X86Routine.run,fragListed,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,put,write,source,ptr,player,
      fragAddress,fragged,logical32] <;> funext r <;>
      by_cases a : r=0 <;> by_cases b : r=1 <;> by_cases c : r=2 <;> by_cases d : r=7 <;> simp_all [write]


def flagByte (s : X86Memory.State) := s.memory (s.regs 3+(104#32)) &&& (0xfd#8)
def playerPointer (s : X86Memory.State) := load32 s.memory (s.regs 3+(132#32))
def nonSolid (s : X86Memory.State) := PainHandoff.byteStore s.memory (s.regs 3+(104#32)) (flagByte s)
def deadMemory (s : X86Memory.State) := store32 (nonSolid s) (playerPointer s+(4#32)) (1#32)
def markedCore (s : X86Memory.State) :=
  put ({(putByte s 1 (flagByte s)) with memory := deadMemory s}) 0 (load32 (deadMemory s) (s.regs 3+(132#32)))
def marked (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (markedCore s) (0x2a38c#32),some {(logical8 (flagByte s)) with carry := some false},0x2d2c0⟩

theorem putByte_twice (s : X86Memory.State) (a b : BitVec 8) :
    putByte (putByte s 1 a) 1 b = putByte s 1 b := by
  simp only [putByte,byteReg,put,write,↓reduceIte]
  congr 1
  funext r
  by_cases hr : r=1 <;>
    simp [write,hr,BitVec.and_or_distrib_right,BitVec.and_assoc,PainHandoff.byte_high_zero]

theorem mark_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run markListed [0x2d2c0] 7 ⟨s,f,0x2a36b⟩ = some (marked s) := by
  let c1 := putByte s 1 (s.memory (s.regs 3+(104#32)))
  let c2 := putByte s 1 (flagByte s)
  let c3 := put c2 0 (playerPointer s)
  let c4 : X86Memory.State := {c3 with memory := nonSolid s}
  let c5 : X86Memory.State := {c4 with memory := deadMemory s}
  let c6 := put c5 0 (load32 (deadMemory s) (s.regs 3+(132#32)))
  let flags := some {(logical8 (flagByte s)) with carry := some false}
  have path : X86Routine.Prefix markListed [0x2d2c0] 7 ⟨s,f,0x2a36b⟩
      ⟨X86Routine.pushWord c6 (0x2a38c#32),flags,0x2d2c0⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2a36e⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,c1])
    apply X86Routine.Prefix.step (middle := ⟨c2,flags,0x2a371⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,c1,c2,flags,flagByte,PainHandoff.cl_written,putByte_twice])
    apply X86Routine.Prefix.step (middle := ⟨c3,flags,0x2a377⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,
        X86Block.Address.eval,c3,c2,playerPointer,putByte,byteReg,put,write])
    apply X86Routine.Prefix.step (middle := ⟨c4,flags,0x2a37a⟩) (by simp) (by rfl) (by
      have cl : readByte c3.regs 1=flagByte s := by
        simpa [c3,c2,readByte,byteReg,put,write] using PainHandoff.cl_written s (flagByte s)
      simp only [X86Routine.execute,cl]
      simp [X86Block.Address.eval,c4,c3,c2,nonSolid,PainHandoff.byteStore,putByte,byteReg,put,write]
      rfl)
    apply X86Routine.Prefix.step (middle := ⟨c5,flags,0x2a381⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Block.Address.eval,c5,c4,c3,c2,deadMemory,put,write])
    apply X86Routine.Prefix.step (middle := ⟨c6,flags,0x2a387⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,
        X86Block.Address.eval,c6,c5,c4,c3,c2,putByte,byteReg,put,write])
    apply X86Routine.Prefix.step (middle := ⟨X86Routine.pushWord c6 (0x2a38c#32),flags,0x2d2c0⟩)
      (by simp) (by rfl) (by simp [X86Routine.execute])
    exact X86Routine.Prefix.nil _
  have run := path.finish (fuel := 0) (by rfl) 7 (by decide)
  have core : c6=markedCore s := by
    simp [markedCore,c6,c5,c4,c3,c2,put,write]
    funext r
    by_cases hr : r=0 <;> simp_all [write]
  rw [run,core]
  rfl

theorem clear_word (m : Memory) (a : Word) :
    load32 (PainHandoff.byteStore m a (m a &&& (0xfd#8))) a = load32 m a &&& (0xfffffffd#32) := by
  have h1 : a+(1#32) ≠ a := by
    simpa using (show a+(1#32) ≠ a+(0#32) by
      intro h; have := (BitVec.add_right_inj a).mp h; contradiction)
  have h2 : a+(2#32) ≠ a := by
    simpa using (show a+(2#32) ≠ a+(0#32) by
      intro h; have := (BitVec.add_right_inj a).mp h; contradiction)
  have h3 : a+(3#32) ≠ a := by
    simpa using (show a+(3#32) ≠ a+(0#32) by
      intro h; have := (BitVec.add_right_inj a).mp h; contradiction)
  simp only [load32,PainHandoff.byteStore,show (1 : Word)=(1#32) from rfl,
    show (2 : Word)=(2#32) from rfl,show (3 : Word)=(3#32) from rfl,if_neg h1,if_neg h2,if_neg h3,ite_true]
  rw [show (0xfffffffd#32)=((0xff#8 ++ 0xff#8) ++ (0xff#8 ++ 0xfd#8)) from by decide]
  rw [BitVec.and_append,BitVec.and_append,BitVec.and_append]
  have mask (v : BitVec 8) : v &&& (255#8)=v := BitVec.and_allOnes
  rw [mask,mask,mask]

theorem counted_word (m : Memory) (a : Word) :
    (m (a+(2#32)) &&& (64#8) = 0) ↔ (load32 m a &&& (0x400000#32) = 0) := by
  have fact (a b c d : BitVec 8) : (c &&& (64#8)=0) ↔
      (((d ++ c) ++ (b ++ a)) &&& (0x400000#32)=0) := by
    rw [show (0x400000#32)=((0#8 ++ 64#8) ++ (0#8 ++ 0#8)) from by decide]
    rw [BitVec.and_append,BitVec.and_append,BitVec.and_append]
    simp only [BitVec.and_zero,BitVec.zero_append_zero]
    change (c &&& (64#8)=0) ↔ ((0#8 ++ (c &&& 64#8)) ++ (0#16)=(0#8 ++ 0#8) ++ (0#16))
    rw [BitVec.append_left_inj,BitVec.append_right_inj]
    rfl
  exact fact (m a) (m (a+1)) (m (a+2)) (m (a+3))

def markWrites (s : X86Memory.State) := [s.regs 3+104,playerPointer s+4,s.regs 4-4]
theorem mark_frame (s : X86Memory.State) : PlayerHeight.Frame s.memory (marked s).core.memory (markWrites s) := by
  intro a safe
  simp only [marked,markedCore,X86Routine.pushWord,putByte,byteReg,put,write,↓reduceIte]
  rw [load_store_apart _ _ _ _ (safe _ (by simp [markWrites]))]
  unfold deadMemory
  rw [load_store_apart _ _ _ _ (safe _ (by simp [markWrites]))]
  exact PainHandoff.byteStore_word_apart _ _ _ _ (safe _ (by simp [markWrites]))


def layout (s : X86Memory.State) (i : Fin 4) (n : Fin 5) : Word := match n.val with
  | 0 => s.regs 3+132
  | 1 => s.regs 3+104
  | 2 => player i+4
  | 3 => fragAddress i
  | _ => 0x2af44
structure Layout (s : X86Memory.State) (i : Fin 4) : Prop where
  ptr : playerPointer s=player i
  separated : ∀ a b : Fin 5, a ≠ b → Apart (layout s i a) (layout s i b)
  stackSafe : ∀ a : Fin 5, Apart (layout s i a) (s.regs 4-4)

theorem credit_frame (s : X86Memory.State) : PlayerHeight.Frame s.memory (credited s).core.memory [0x2af44] := by
  intro a safe
  unfold credited creditMemory
  split
  · exact load_store_apart _ _ _ _ (safe _ (by simp))
  · rfl

theorem frag_frame (s : X86Memory.State) (i : Fin 4) :
    PlayerHeight.Frame s.memory (fragged s i).core.memory [fragAddress i] := by
  intro a safe
  exact load_store_apart _ _ _ _ (safe _ (by simp))

def prepared (s : X86Memory.State) (i : Fin 4) := (fragged (credited s).core i).core

theorem prepared_regs (s : X86Memory.State) (i : Fin 4) :
    (prepared s i).regs 3=s.regs 3 ∧ (prepared s i).regs 4=s.regs 4 := by simp [prepared,fragged,credited,write]

theorem prepared_keep (s : X86Memory.State) (i : Fin 4) (h : Layout s i)
    (a : Fin 5) (notFrag : a ≠ 3) (notKill : a ≠ 4) :
    load32 (prepared s i).memory (layout s i a)=load32 s.memory (layout s i a) := by
  rw [show (prepared s i).memory=(fragged (credited s).core i).core.memory from rfl]
  rw [frag_frame _ i _ (fun b mem => by simp only [List.mem_singleton] at mem; subst b; exact h.separated a 3 notFrag)]
  exact credit_frame s _ (fun b mem => by simp only [List.mem_singleton] at mem; subst b; exact h.separated a 4 notKill)

theorem prepared_layout (s : X86Memory.State) (i : Fin 4) (h : Layout s i) : Layout (prepared s i) i := by
  have regs := prepared_regs s i
  have same (n : Fin 5) : layout (prepared s i) i n=layout s i n := by simp [layout,regs.1]
  refine ⟨?_,?_,?_⟩
  · change load32 (prepared s i).memory ((prepared s i).regs 3+132)=player i
    rw [regs.1]
    exact (prepared_keep s i h 0 (by decide) (by decide)).trans h.ptr
  · intro a b ne; rw [same,same]; exact h.separated a b ne
  · intro a; rw [same,regs.2]; exact h.stackSafe a

def complete (s : X86Memory.State) (i : Fin 4) := marked (prepared s i)

theorem active_credit (pc : Nat) (h : creditListed pc ≠ none) : pc ∉ [0x2d2c0] := by
  intro mem; simp only [List.mem_singleton] at mem; subst pc; contradiction
theorem active_frag (pc : Nat) (h : fragListed pc ≠ none) : pc ∉ [0x2d2c0] := by
  intro mem; simp only [List.mem_singleton] at mem; subst pc; contradiction

theorem execution (s : X86Memory.State) (f : Option Flags) (i : Fin 4)
    (source : s.regs 1=0) (h : Layout s i) :
    X86Routine.run program [0x2d2c0] 27 ⟨s,f,0x2a2e6⟩ = some (complete s i) := by
  obtain ⟨n,hn,first,_⟩ := X86Routine.run_path (credit_execution s f source)
  have first := first.transfer program [0x2d2c0] credit_decoded active_credit
  have ptr : load32 (credited s).core.memory ((credited s).core.regs 3+(132#32))=player i := by
    rw [credit_frame s _ (fun b mem => by simp only [List.mem_singleton] at mem; subst b; exact h.separated 0 4 (by decide))]
    exact h.ptr
  have frun := frag_execution (credited s).core (credited s).flags i source ptr
  obtain ⟨k,hk,middle,_⟩ := X86Routine.run_path frun
  have middle := middle.transfer program [0x2d2c0] frag_decoded active_frag
  have last := mark_execution (prepared s i) none
  rw [← X86Routine.run_sound program markListed mark_decoded _ _ _ (by rw [mark_execution]; simp)] at last
  have rest : X86Routine.run program [0x2d2c0] 20 (credited s) = some (complete s i) :=
    middle.finish last 20 (by omega)
  exact first.finish rest 27 (by omega)


theorem marked_memory (s : X86Memory.State) :
    (marked s).core.memory=store32 (deadMemory s) (s.regs 4-(4#32)) (0x2a38c#32) := rfl

theorem mark_pointer (s : X86Memory.State) (i : Fin 4) (h : Layout s i) :
    (marked s).core.regs 0=player i := by
  change load32 (deadMemory s) (s.regs 3+(132#32))=player i
  unfold deadMemory
  rw [h.ptr]
  have sep : Apart (s.regs 3+(132#32)) (player i+(4#32)) := h.separated 0 2 (by decide)
  rw [load_store_apart _ _ _ _ sep]
  unfold nonSolid
  have sep : Apart (s.regs 3+(132#32)) (s.regs 3+(104#32)) := h.separated 0 1 (by decide)
  rw [PainHandoff.byteStore_word_apart _ _ _ _ sep]
  exact h.ptr

theorem mark_fields (s : X86Memory.State) (i : Fin 4) (h : Layout s i) :
    load32 (marked s).core.memory (s.regs 3+104)=load32 s.memory (s.regs 3+104) &&& (0xfffffffd#32) ∧
    load32 (marked s).core.memory (player i+4)=1 ∧
    load32 (marked s).core.memory (s.regs 4-4)=0x2a38c := by
  rw [marked_memory]
  constructor
  · have sep : Apart (s.regs 3+104) (s.regs 4-(4#32)) := h.stackSafe 1
    rw [load_store_apart _ _ _ _ sep]
    unfold deadMemory
    rw [h.ptr]
    have sep : Apart (s.regs 3+104) (player i+(4#32)) := h.separated 1 2 (by decide)
    rw [load_store_apart _ _ _ _ sep]
    exact clear_word _ _
  · constructor
    · have sep : Apart (player i+4) (s.regs 4-(4#32)) := h.stackSafe 2
      rw [load_store_apart _ _ _ _ sep,deadMemory,h.ptr]
      exact load_store _ _ _
    · exact load_store _ _ _

theorem mark_keeps_counter (s : X86Memory.State) (i : Fin 4) (h : Layout s i)
    (a : Fin 5) (flag : a ≠ 1) (dead : a ≠ 2) :
    load32 (marked s).core.memory (layout s i a)=load32 s.memory (layout s i a) := by
  apply mark_frame
  intro b hb
  simp only [markWrites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact h.separated a 1 flag
  · rw [h.ptr]; exact h.separated a 2 dead
  · exact h.stackSafe a

def kills (s : X86Memory.State) :=
  if net s=0 ∧ counted s≠0 then load32 s.memory (0x2af44#32)+1 else load32 s.memory (0x2af44#32)

theorem complete_fields (s : X86Memory.State) (i : Fin 4) (h : Layout s i) :
    load32 (complete s i).core.memory (0x2af44#32)=kills s ∧
    load32 (complete s i).core.memory (fragAddress i)=load32 s.memory (fragAddress i)+1 ∧
    load32 (complete s i).core.memory (s.regs 3+104)=load32 s.memory (s.regs 3+104) &&& (0xfffffffd#32) ∧
    load32 (complete s i).core.memory (player i+4)=1 ∧
    (complete s i).core.regs 0=player i ∧
    load32 (complete s i).core.memory (s.regs 4-4)=0x2a38c := by
  have ph := prepared_layout s i h
  have regs := prepared_regs s i
  have field := mark_fields (prepared s i) i ph
  rw [regs.1,regs.2] at field
  refine ⟨?_,?_,?_,field.2.1,mark_pointer _ i ph,field.2.2⟩
  · change load32 (marked (prepared s i)).core.memory _=kills s
    have keep : load32 (marked (prepared s i)).core.memory (0x2af44#32)=load32 (prepared s i).memory (0x2af44#32) := mark_keeps_counter _ i ph 4 (by decide) (by decide)
    rw [keep]
    change load32 (fragged (credited s).core i).core.memory _=kills s
    rw [frag_frame _ i _ (fun b hb => by simp only [List.mem_singleton] at hb; subst b; exact h.separated 4 3 (by decide))]
    simp [credited,creditMemory,kills]; split <;> simp [load_store]
  · change load32 (marked (prepared s i)).core.memory _=_
    have keep : load32 (marked (prepared s i)).core.memory (fragAddress i)=load32 (prepared s i).memory (fragAddress i) := mark_keeps_counter _ i ph 3 (by decide) (by decide)
    rw [keep]
    change load32 (store32 (credited s).core.memory (fragAddress i) _) (fragAddress i)=_
    rw [load_store,credit_frame s _ (fun b hb => by simp only [List.mem_singleton] at hb; subst b; exact h.separated 3 4 (by decide))]
  · change load32 (marked (prepared s i)).core.memory _=_
    rw [field.1]
    have keep : load32 (prepared s i).memory (s.regs 3+104)=load32 s.memory (s.regs 3+104) := prepared_keep s i h 1 (by decide) (by decide)
    rw [keep]

def writes (s : X86Memory.State) (i : Fin 4) :=
  [0x2af44,fragAddress i,s.regs 3+104,player i+4,s.regs 4-4]

theorem complete_frame (s : X86Memory.State) (i : Fin 4) (h : Layout s i) :
    PlayerHeight.Frame s.memory (complete s i).core.memory (writes s i) := by
  intro a safe
  change load32 (marked (prepared s i)).core.memory a=load32 s.memory a
  rw [mark_frame _ a]
  · change load32 (fragged (credited s).core i).core.memory a=_
    rw [frag_frame _ i a]
    · exact credit_frame s a (fun b hb => safe b (by simpa [writes] using Or.inl hb))
    · intro b hb; simp only [List.mem_singleton] at hb; subst b; exact safe _ (by simp [writes])
  · intro b hb
    have ptr := (prepared_layout s i h).ptr
    have regs := prepared_regs s i
    simp only [markWrites,regs.1,regs.2,ptr,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
    apply safe
    simp only [writes,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
    rcases hb with rfl | rfl | rfl <;> simp

theorem live_fields (body : Death.Body) (world : Death.World) (i : Fin 4)
    (source : world.source=none) (victim : body.player=some i) :
    let out := Death.bookkeeping body world
    out.1.flags=body.flags &&& ~~~(2 : UInt32) ∧
    out.2.players[0].kills=(if !world.netgame && body.flags &&& (0x400000 : UInt32) != 0 then world.players[0].kills+1 else world.players[0].kills) ∧
    out.2.players[i].frags[i]=world.players[i].frags[i]+1 ∧
    out.2.players[i].dead=true ∧ out.2.events=world.events.push (.dropWeapon i.val) := by
  rcases i with ⟨i,hi⟩
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [Death.bookkeeping,source,victim] <;> split <;> simp
  all_goals (try simp only [Vector.getElem_set])
  all_goals (try simp only [show ¬(0 : Nat) = (3 : Fin 4).val from by decide, if_false])
  all_goals first | exact ⟨True.intro,rfl⟩ | rfl


structure Inputs (s : X86Memory.State) (i : Fin 4) (body : Death.Body) (world : Death.World)
    extends Layout s i where
  source : s.regs 1=0
  environmental : world.source=none
  victim : body.player=some i
  flags : load32 s.memory (s.regs 3+104)=body.flags.toBitVec
  netgame : net s=if world.netgame then 1 else 0
  kills : load32 s.memory (0x2af44#32)=world.players[0].kills.toBitVec
  frags : load32 s.memory (fragAddress i)=world.players[i].frags[i].toBitVec

def observation (obj : Word) (i : Fin 4) (t : X86Control.State) :=
  (load32 t.core.memory (obj+104),load32 t.core.memory (0x2af44#32),
   load32 t.core.memory (fragAddress i),load32 t.core.memory (player i+4))
def liveObservation (i : Fin 4) (body : Death.Body) (world : Death.World) :=
  let out := Death.bookkeeping body world
  (out.1.flags.toBitVec,out.2.players[0].kills.toBitVec,out.2.players[i].frags[i].toBitVec,
   if out.2.players[i].dead then (1#32) else 0)

theorem live_result (s : X86Memory.State) (i : Fin 4) (body : Death.Body) (world : Death.World)
    (h : Inputs s i body world) :
    observation (s.regs 3) i (complete s i)=liveObservation i body world := by
  have fields := complete_fields s i h.toLayout
  have live := live_fields body world i h.environmental h.victim
  have count : counted s=0 ↔ body.flags &&& (0x400000 : UInt32)=0 := by
    unfold counted
    rw [show s.regs 3+(106#32)=(s.regs 3+104)+(2#32) by simp [BitVec.add_assoc]]
    rw [counted_word,h.flags]
    exact UInt32.toBitVec_inj
  simp only [observation,liveObservation,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,
    live.1,live.2.1,live.2.2.1,live.2.2.2.1,ite_true,h.flags,h.frags]
  simp only [kills,h.netgame,h.kills]
  by_cases hn : world.netgame=true <;> by_cases hc : body.flags &&& (0x400000 : UInt32)=0 <;>
    simp_all [count]

theorem live_execution (s : X86Memory.State) (f : Option Flags) (i : Fin 4)
    (body : Death.Body) (world : Death.World) (h : Inputs s i body world) :
    (X86Routine.run program [0x2d2c0] 27 ⟨s,f,0x2a2e6⟩).map (observation (s.regs 3) i)=
      some (liveObservation i body world) := by
  rw [execution s f i h.source h.toLayout]
  exact congrArg some (live_result s i body world h)


/-- Same initial memory, with the registers known at the corpse-setup boundary.
No intermediate machine state is assumed. -/
def entryView (s : X86Memory.State) : X86Memory.State :=
  ⟨write (write (write s.regs 3 (s.regs 0)) 4 (s.regs 4-52)) 1 0,s.memory⟩
def priorWrites (s : X86Memory.State) := ActorHealth.joinedWrites s ++ KillEntry.suffixWrites s
def reads (s : X86Memory.State) (i : Fin 4) := [s.regs 0+132,0x2b400,0x2af44,fragAddress i]
def retained (s : X86Memory.State) := KillEntry.retained s ++ [s.regs 0+68]
structure JoinedInputs (s : X86Memory.State) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (i : Fin 4) (body : Death.Body) (world : Death.World)
    extends toKill : KillEntry.JoinedInputs s v d baby body where
  book : Inputs (entryView s) i body world
  bookReadsSafe : ∀ a, a ∈ reads s i → ∀ b, b ∈ priorWrites s → Apart a b
  bookRetained : ∀ a, a ∈ retained s → ∀ b, b ∈ writes (entryView s) i → Apart a b

def joined : X86Routine.Program := fun pc =>
  if 0x2a2e6 ≤ pc ∧ pc < 0x2a38c then program pc else KillEntry.joined pc
def exits := [0x2d2c0,0x2a6b6,0x2a747]

theorem contains_book (pc : Nat) (h : program pc ≠ none) : joined pc=program pc := by
  unfold joined
  split
  · rfl
  · rename_i hn; simp [program,bytesProgram,hn] at h

theorem contains_previous (pc : Nat) (h : KillEntry.joined pc ≠ none) : joined pc=KillEntry.joined pc := by
  unfold joined
  split
  · rename_i hb
    have b1 : ¬(0x2a6a6 ≤ pc ∧ pc < 0x2a6b1) := by omega
    have b2 : ¬(0x2a2b0 ≤ pc ∧ pc < 0x2a2e6) := by omega
    have b3 : ¬(0x2a650 ≤ pc ∧ pc < 0x2a6a6) := by omega
    have b4 : ¬(0x1bb50 ≤ pc ∧ pc < 0x1bb66) := by omega
    have b5 : ¬(0x1bc41 ≤ pc ∧ pc < 0x1bc45) := by omega
    have b6 : ¬(0x2a616 ≤ pc ∧ pc < 0x2a650) := by omega
    have b7 : ¬(0x2a460 ≤ pc ∧ pc < 0x2a5d5) := by omega
    have b8 : ¬(0x2a5d5 ≤ pc ∧ pc < 0x2a616) := by omega
    simp [KillEntry.joined,ActorHealth.joined,PlayerHealth.joined,PlayerDamageEntry.program,
      PlayerDamageEntry.bytesProgram,b1,b2,b3,b4,b5,b6,b7,b8,
      show pc ≠ 0x2fb76 by omega,show pc ≠ 0x2fba0 by omega,show pc ≠ 0x2fbd2 by omega] at h
  · rfl

theorem previous_active (pc : Nat) (h : KillEntry.joined pc ≠ none) : pc ∉ exits := by
  intro mem
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl <;> contradiction

theorem book_active (pc : Nat) (h : program pc ≠ none) : pc ∉ exits := by
  intro mem
  simp only [exits,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl <;> contradiction

def joinedObservation (s : X86Memory.State) (i : Fin 4) (t : X86Control.State) :=
  (KillEntry.damageFields s t.core.memory,load32 t.core.memory (s.regs 0+68),observation (s.regs 0) i t)
def joinedLiveObservation (out : PlayerDamage.Result) (i : Fin 4) (body : Death.Body) (world : Death.World) :=
  (KillEntry.liveDamageFields out,(Death.corpse body).height.raw.toBitVec,liveObservation i (Death.corpse body) world)

/-- From the real floor CALL through the real P_DropWeapon CALL. The callee
is deliberately the next proof boundary; its effects are not assumed here. -/
def stackWrites (s : X86Memory.State) (i : Fin 4) := KillEntry.stackWrites s ++ writes (entryView s) i
def returnWrites (s : X86Memory.State) (i : Fin 4) := KillEntry.returnWrites s ++ writes (entryView s) i

theorem joined_execution_detailed_tracked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (i : Fin 4) (body : Death.Body) (world : Death.World)
    (h : JoinedInputs s v d baby i body world)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t,
      DeathStack.Saved s pc t.core.memory (stackWrites s i) (returnWrites s i) ∧ X86Routine.run joined exits 158 ⟨s,f,pc⟩=some t ∧
      joinedObservation s i t=joinedLiveObservation (PlayerDamage.apply v d none false baby rng) i body world ∧
      t.pc=0x2d2c0 ∧ t.core.regs 0=player i ∧ t.core.regs 4=s.regs 4-56 ∧
      load32 t.core.memory (s.regs 4-56)=0x2a38c ∧
      t.core.regs 3=s.regs 0 ∧
      PlayerHeight.Frame s.memory t.core.memory (priorWrites s ++ writes (entryView s) i) := by
  obtain ⟨g,gsaved,grun,gobs,gpc,gsource,gobj,gsp,gframe⟩ :=
    KillEntry.joined_execution_tracked s f pc site v d baby rng body h.toKill dead
  have keep (a : Word) (ha : a ∈ reads s i) : load32 g.core.memory a=load32 s.memory a :=
    gframe a (h.bookReadsSafe a ha)
  have regs3 : (entryView s).regs 3=s.regs 0 := by simp [entryView,write]
  have regs4 : (entryView s).regs 4=s.regs 4-52 := by simp [entryView,write]
  have layouts (n : Fin 5) : layout g.core i n=layout (entryView s) i n := by simp [layout,gobj,regs3]
  have ins : Inputs g.core i (Death.corpse body) world := by
    refine ⟨⟨?_,?_,?_⟩,gsource,h.book.environmental,?_,?_,?_,?_,?_⟩
    · change load32 g.core.memory (g.core.regs 3+132)=player i
      rw [gobj,keep _ (by simp [reads])]
      exact h.book.ptr
    · intro a b ne; rw [layouts,layouts]; exact h.book.separated a b ne
    · intro a; rw [layouts,gsp]; exact h.book.stackSafe a
    · simpa [Death.corpse,h.player] using h.book.victim
    · have eq := congrArg (fun x => x.2.1) gobs
      simpa [KillEntry.observation,KillEntry.liveObservation,gobj] using eq
    · change load32 g.core.memory (0x2b400#32)=_
      rw [keep _ (by simp [reads])]; exact h.book.netgame
    · rw [keep _ (by simp [reads])]; exact h.book.kills
    · rw [keep _ (by simp [reads])]; exact h.book.frags
  have wr : writes g.core i=writes (entryView s) i := by simp [writes,gobj,gsp,regs3,regs4]
  have stable (a : Word) (ha : a ∈ retained s) :
      load32 (complete g.core i).core.memory a=load32 g.core.memory a := by
    apply complete_frame _ i ins.toLayout
    intro b hb; rw [wr] at hb; exact h.bookRetained a ha b hb
  have damage : KillEntry.damageFields s (complete g.core i).core.memory=KillEntry.damageFields s g.core.memory := by
    unfold KillEntry.damageFields
    dsimp only
    repeat rw [stable _ (by simp [retained,KillEntry.retained,ActorHealth.fields])]
  have obs := live_result g.core i (Death.corpse body) world ins
  rw [gobj] at obs
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path grun
  have path := path.transfer joined exits contains_previous previous_active
  obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path (execution g.core g.flags i gsource ins.toLayout)
  have tail := tail.transfer joined exits contains_book book_active
  have last : X86Routine.run joined exits 27 g=some (complete g.core i) := by
    have geq : g=⟨g.core,g.flags,0x2a2e6⟩ := by
      cases g with
      | mk core flags pc => change pc=0x2a2e6 at gpc; cases gpc; rfl
    rw [geq]
    exact tail.finish (fuel := 0) (by simp [X86Routine.run,complete,marked,exits]) 27 (by omega)
  have fields := complete_fields g.core i ins.toLayout
  have tracked : DeathStack.Saved s pc (complete g.core i).core.memory (stackWrites s i) (returnWrites s i) := by
    have fr := complete_frame g.core i ins.toLayout
    rw [wr] at fr
    exact gsaved.then_frame _ _ _ _ _ _ _ fr
  refine ⟨complete g.core i,tracked,path.finish last 158 (by omega),?_,rfl,fields.2.2.2.2.1,?_,?_,?_,?_⟩
  · change (_,_,_)=(_,_,_)
    rw [damage,stable _ (by simp [retained]),obs]
    have dam := congrArg Prod.fst gobs
    have ht := congrArg (fun x => x.2.2) gobs
    exact Prod.ext dam (Prod.ext ht rfl)
  · simp [complete,marked,markedCore,prepared,fragged,credited,X86Routine.pushWord,put,putByte,byteReg,write,gsp,BitVec.sub_sub]
  · simpa [gsp,BitVec.sub_sub] using fields.2.2.2.2.2
  · simp [complete,marked,markedCore,prepared,fragged,credited,X86Routine.pushWord,put,putByte,byteReg,write,gobj]
  · intro a safe
    rw [complete_frame g.core i ins.toLayout a]
    · exact gframe a (fun b hb => safe b (List.mem_append.mpr (Or.inl hb)))
    · intro b hb; rw [wr] at hb; exact safe b (by simp [hb])

theorem joined_execution_detailed (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (i : Fin 4) (body : Death.Body) (world : Death.World)
    (h : JoinedInputs s v d baby i body world)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t, X86Routine.run joined exits 158 ⟨s,f,pc⟩=some t ∧
      joinedObservation s i t=joinedLiveObservation (PlayerDamage.apply v d none false baby rng) i body world ∧
      t.pc=0x2d2c0 ∧ t.core.regs 0=player i ∧ t.core.regs 4=s.regs 4-56 ∧
      load32 t.core.memory (s.regs 4-56)=0x2a38c ∧
      t.core.regs 3=s.regs 0 ∧
      PlayerHeight.Frame s.memory t.core.memory (priorWrites s ++ writes (entryView s) i) := by
  obtain ⟨t,_,rest⟩ :=
    joined_execution_detailed_tracked s f pc site v d baby rng i body world h dead
  exact ⟨t,rest⟩

theorem joined_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (i : Fin 4) (body : Death.Body) (world : Death.World)
    (h : JoinedInputs s v d baby i body world)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t, X86Routine.run joined exits 158 ⟨s,f,pc⟩=some t ∧
      joinedObservation s i t=joinedLiveObservation (PlayerDamage.apply v d none false baby rng) i body world ∧
      t.pc=0x2d2c0 ∧ t.core.regs 0=player i ∧ t.core.regs 4=s.regs 4-56 ∧
      load32 t.core.memory (s.regs 4-56)=0x2a38c ∧
      PlayerHeight.Frame s.memory t.core.memory (priorWrites s ++ writes (entryView s) i) := by
  obtain ⟨t,run,obs,pc,player,sp,ret,_,frame⟩ :=
    joined_execution_detailed s f pc site v d baby rng i body world h dead
  exact ⟨t,run,obs,pc,player,sp,ret,frame⟩

end Doom.Proofs.KillBookkeeping




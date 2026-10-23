import Doom.Proofs.OriginalWeaponDropDispatch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponDrop
open Verification X86 X86Memory X86Control BlockSummary
@[simp] theorem location_0 (s : X86Memory.State) (w : Fin 3) : location s w 0=s.regs 0+(4#32) := rfl
@[simp] theorem location_1 (s : X86Memory.State) (w : Fin 3) : location s w 1=s.regs 0+(112#32) := rfl
@[simp] theorem location_2 (s : X86Memory.State) (w : Fin 3) : location s w 2=psp s+(12#32) := rfl
@[simp] theorem location_3 (s : X86Memory.State) (w : Fin 3) : location s w 3=psp s := rfl
@[simp] theorem location_4 (s : X86Memory.State) (w : Fin 3) : location s w 4=psp s+(4#32) := rfl
@[simp] theorem location_5 (s : X86Memory.State) (w : Fin 3) : location s w 5=info w := rfl
@[simp] theorem location_6 (s : X86Memory.State) (w : Fin 3) : location s w 6=state w+8 := rfl
@[simp] theorem location_7 (s : X86Memory.State) (w : Fin 3) : location s w 7=state w+20 := rfl
@[simp] theorem location_8 (s : X86Memory.State) (w : Fin 3) : location s w 8=state w+12 := rfl
@[simp] theorem location_9 (s : X86Memory.State) (w : Fin 3) : location s w 9=state w+16 := rfl
@[simp] theorem location_10 (s : X86Memory.State) (w : Fin 3) : location s w 10=s.regs 4 := rfl
@[simp] theorem location_11 (s : X86Memory.State) (w : Fin 3) : location s w 11=s.regs 4-(4#32) := rfl
@[simp] theorem location_12 (s : X86Memory.State) (w : Fin 3) : location s w 12=s.regs 4-(8#32) := rfl
@[simp] theorem location_13 (s : X86Memory.State) (w : Fin 3) : location s w 13=s.regs 4-(12#32) := rfl
@[simp] theorem location_14 (s : X86Memory.State) (w : Fin 3) : location s w 14=s.regs 4-(16#32) := rfl
@[simp] theorem location_15 (s : X86Memory.State) (w : Fin 3) : location s w 15=s.regs 4-(20#32) := rfl
@[simp] theorem location_16 (s : X86Memory.State) (w : Fin 3) : location s w 16=s.regs 4-(24#32) := rfl
@[simp] theorem location_17 (s : X86Memory.State) (w : Fin 3) : location s w 17=s.regs 4-(28#32) := rfl
def lowerLocation (n : Fin 4) : Fin 18 := match n.val with
  | 0 => 0 | 1 => 2 | 2 => 17 | _ => 16

theorem lower_layout (s : X86Memory.State) (w : Fin 3) (n : Fin 4) :
    WeaponLower.layout (action s w) n=location s w (lowerLocation n) := by
  rcases n with ⟨n,hn⟩; have hc : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
  rcases hc with rfl|rfl|rfl|rfl <;>
    simp [WeaponLower.layout,WeaponLower.yAddress,action,write,lowerLocation,BitVec.sub_sub]

theorem lower_inputs (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y) :
    WeaponLower.Inputs (action s w) y := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa [action,write] using (read_actionMemory s w y h 0).trans (by simpa using h.dead)
  · simpa [WeaponLower.yAddress,action,write] using (read_actionMemory s w y h 2).trans (by simpa using h.height)
  · simpa [action,write] using read_actionMemory s w y h 16
  · intro a b ne
    rw [lower_layout,lower_layout]
    apply h.separate
    have inj : ∀ a b : Fin 4, lowerLocation a=lowerLocation b → a=b := by decide
    exact fun eq => ne (inj a b eq)

theorem prefix_inputs (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y) :
    load32 (saves s) (s.regs 0+(112#32))=BitVec.ofNat 32 w.val ∧
    load32 (saves s) (info w)=down w ∧
    load32 (store32 (setterMemory s) (psp s) (state w)) (state w+8)=1 ∧
    load32 (installed s w) (state w+20)=0 ∧
    load32 (installed s w) (state w+12)=0x2d490 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [] using (read_saves s w y h 1).trans (by simpa using h.ready)
  · simpa [] using (read_saves s w y h 5).trans (by simpa using h.downState)
  · have safe : Apart (state w+8) (psp s) := h.separate 6 3 (by decide)
    rw [load_store_apart _ _ _ _ safe]
    simpa [] using (read_setterMemory s w y h 6).trans (by simpa using h.tics)
  · simpa [] using (read_installed s w y h 7).trans (by simpa using h.misc)
  · simpa [] using (read_installed s w y h 8).trans (by simpa using h.callback)

def lowered (s : X86Memory.State) (w : Fin 3) := WeaponLower.result (action s w)

theorem lower_keep (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y)
    (n : Fin 18) (ny : n≠2) (ns : n≠17) :
    load32 (lowered s w).core.memory (location s w n)=load32 (actionMemory s w) (location s w n) := by
  apply WeaponLower.result_frame (action s w)
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl
  · simpa [action,write,BitVec.sub_sub] using h.separate n 17 ns
  · simpa [WeaponLower.yAddress,action,write] using h.separate n 2 ny

def tailStart (s : X86Memory.State) (w : Fin 3) (m : Memory) (f : Option Flags) : X86Control.State :=
  ⟨⟨write (write (write (write (write s.regs 1 (state w)) 2 (psp s)) 3 (psp s))
    4 (s.regs 4-(20#32))) 6 (s.regs 0),m⟩,f,0x2d095⟩
def final (s : X86Memory.State) (w : Fin 3) : X86Control.State :=
  ⟨⟨write (write s.regs 0 (down w)) 4 (s.regs 4+(4#32)),(lowered s w).core.memory⟩,
    some (logical32 1),0x2a38c⟩

theorem lowered_eq (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y) :
    lowered s w=tailStart s w (lowered s w).core.memory (lowered s w).flags := by
  have regs := WeaponLower.result_registers (action s w) y (lower_inputs s w y h)
  change X86Control.State.mk ⟨(lowered s w).core.regs,(lowered s w).core.memory⟩ (lowered s w).flags 0x2d095=_
  change (lowered s w).core.regs=_ at regs
  rw [regs]
  simp only [tailStart,action,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  congr 2
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
    by_cases h4 : r=4 <;> by_cases h6 : r=6 <;> simp_all [write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem tail_execution (s : X86Memory.State) (w : Fin 3) (m : Memory) (f : Option Flags)
    (st : load32 m (psp s)=state w)
    (tic : load32 m (psp s+4)=1)
    (next : load32 m (state w+16)=down w)
    (ebx : load32 m (s.regs 4-4)=s.regs 3)
    (edx : load32 m (s.regs 4-8)=s.regs 2)
    (returnSetter : load32 m (s.regs 4-12)=0x2d2e0)
    (ecx : load32 m (s.regs 4-16)=s.regs 1)
    (esi : load32 m (s.regs 4-20)=s.regs 6)
    (returnDrop : load32 m (s.regs 4)=0x2a38c) :
    X86Routine.run listed [0x2a38c] 13 (tailStart s w m f)=
      some ⟨⟨write (write s.regs 0 (down w)) 4 (s.regs 4+4),m⟩,some (logical32 1),0x2a38c⟩ := by
  have nz : state w ≠ (0#32) := by
    rcases w with ⟨w,hw⟩; have hc : w=0 ∨ w=1 ∨ w=2 := by omega
    rcases hc with rfl|rfl|rfl <;> simp [state,down]
  simp [psp,BitVec.sub_eq_add_neg,BitVec.add_assoc] at st tic next ebx edx returnSetter ecx esi returnDrop
  let c0 := (tailStart s w m f).core
  let c1 : X86Memory.State := c0
  let c2 : X86Memory.State := c1
  let c3 : X86Memory.State := put c2 0 (state w)
  let c4 : X86Memory.State := put c3 2 1
  let c5 : X86Memory.State := put c4 0 (down w)
  let c6 : X86Memory.State := c5
  let c7 : X86Memory.State := c6
  let c8 : X86Memory.State := put (put c7 4 (s.regs 4-16)) 6 (s.regs 6)
  let c9 : X86Memory.State := put (put c8 4 (s.regs 4-12)) 1 (s.regs 1)
  let c10 : X86Memory.State := put c9 4 (s.regs 4-8)
  let c11 : X86Memory.State := put (put c10 4 (s.regs 4-4)) 2 (s.regs 2)
  let c12 : X86Memory.State := put (put c11 4 (s.regs 4)) 3 (s.regs 3)
  have path : X86Routine.Prefix listed [0x2a38c] 13 (tailStart s w m f)
      ⟨⟨write (write s.regs 0 (down w)) 4 (s.regs 4+4),m⟩,some (logical32 1),0x2a38c⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,some (compare32 (state w) 0),0x2d098⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c2,some (compare32 (state w) 0),0x2d09a⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c3,some (compare32 (state w) 0),0x2d09c⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c4,some (compare32 (state w) 0),0x2d09f⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,c4,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c5,some (compare32 (state w) 0),0x2d0a2⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,c4,c5,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c6,some (logical32 1),0x2d0a4⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,c4,c5,c6,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c7,some (logical32 1),0x2d0ac⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,c4,c5,c6,c7,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c8,some (logical32 1),0x2d0ad⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c9,some (logical32 1),0x2d0ae⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c10,some (logical32 1),0x2d2e0⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c11,some (logical32 1),0x2d2e1⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨c12,some (logical32 1),0x2d2e2⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz])
    apply X86Routine.Prefix.step (middle := ⟨⟨write (write s.regs 0 (down w)) 4 (s.regs 4+4),m⟩,some (logical32 1),0x2a38c⟩) (by simp [tailStart]) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        blockPreservesFlags,X86Block.Address.eval,put,write,
        c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,tailStart,psp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        st,tic,next,ebx,edx,returnSetter,ecx,esi,returnDrop,cmp32_zero,logical32,nz]
      funext r
      by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
        by_cases h4 : r=4 <;> by_cases h6 : r=6 <;> simp_all [write])
    exact X86Routine.Prefix.nil _
  exact path.finish (fuel := 0) (by simp [X86Routine.run]) 13 (by decide)

theorem lower_contains (pc : Nat) (h : WeaponLower.program pc ≠ none) :
    program pc=WeaponLower.program pc := by
  have bound : 0x2d490 ≤ pc ∧ pc < 0x2d4cc := by
    by_cases yes : 0x2d490 ≤ pc ∧ pc < 0x2d4cc
    · exact yes
    · simp [WeaponLower.program,WeaponLower.bytesProgram,yes] at h
  simp [program,bytesProgram,show ¬(0x2d2c0 ≤ pc ∧ pc < 0x2d2e3) by omega,
    show ¬(0x2d040 ≤ pc ∧ pc < 0x2d0af) by omega,WeaponLower.program]

theorem listed_active (pc : Nat) (h : listed pc ≠ none) : pc ∉ [0x2a38c] := by
  simp only [List.mem_singleton]; intro eq; subst pc; exact h rfl

theorem lower_active (pc : Nat) (h : WeaponLower.program pc ≠ none) : pc ∉ [0x2a38c] := by
  simp only [List.mem_singleton]; intro eq; subst pc; exact h rfl

/-- Complete original call chain: P_DropWeapon -> P_SetPsprite -> A_Lower,
then both returns to P_KillMobj. No intermediate state is reset. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (w : Fin 3) (y : Fixed) (h : Inputs s w y) :
    X86Routine.run program [0x2a38c] 55 ⟨s,f,0x2d2c0⟩=some (final s w) := by
  have hin := prefix_inputs s w y h
  obtain ⟨n,hn,first,_⟩ := X86Routine.run_path (dispatch s f w hin.1 hin.2.1)
  have first := first.transfer program [0x2a38c] decoded listed_active
  obtain ⟨k,hk,second,_⟩ := X86Routine.run_path (setter_prefix s w hin.2.2.1 hin.2.2.2.1 hin.2.2.2.2)
  have second := second.transfer program [0x2a38c] decoded listed_active
  obtain ⟨j,hj,third,_⟩ := X86Routine.run_path
    (WeaponLower.original_execution (action s w) (some (compare32 0x2d490 0)) y (lower_inputs s w y h))
  have third := third.transfer program [0x2a38c] lower_contains lower_active
  have read (i : Fin 18) (ny : i≠2) (ns : i≠17) :=
    (lower_keep s w y h i ny ns).trans (read_actionMemory s w y h i)
  have tail : X86Routine.run listed [0x2a38c] 13 (lowered s w)=some (final s w) := by
    rw [lowered_eq s w y h]
    apply tail_execution
    · simpa using read 3 (by decide) (by decide)
    · simpa using read 4 (by decide) (by decide)
    · simpa using (read 9 (by decide) (by decide)).trans (by simpa using h.next)
    · simpa using read 11 (by decide) (by decide)
    · simpa using read 12 (by decide) (by decide)
    · simpa using read 13 (by decide) (by decide)
    · simpa using read 14 (by decide) (by decide)
    · simpa using read 15 (by decide) (by decide)
    · simpa using (read 10 (by decide) (by decide)).trans (by simpa using h.ret)
  have tailActual : X86Routine.run program [0x2a38c] 13 (lowered s w)=some (final s w) := by
    rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [tail]; simp)]
    exact tail
  exact first.finish (second.finish (third.finish tailActual 22 (by omega)) 45 (by omega)) 55 (by omega)

def writes (s : X86Memory.State) : List Word :=
  [s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16,s.regs 4-20,s.regs 4-24,s.regs 4-28,
    psp s,psp s+4,psp s+12]

theorem frame (s : X86Memory.State) (w : Fin 3) :
    PlayerHeight.Frame s.memory (final s w).core.memory (writes s) := by
  intro a safe
  change load32 (WeaponLower.result (action s w)).core.memory a=load32 s.memory a
  rw [WeaponLower.result_frame (action s w) a (by
    intro b hb
    simp [action,write,WeaponLower.yAddress,BitVec.sub_sub] at hb
    rcases hb with rfl|rfl <;> exact safe _ (by simp [writes]))]
  change load32 (actionMemory s w) a=_
  have keep (m : Memory) (b v : Word) (hb : b ∈ writes s) := load_store_apart m b a v (safe b hb)
  simp only [actionMemory,installed,setterMemory,dropMemory,saves]
  repeat rw [keep _ _ _ (by simp [writes])]

/-- The selected state IDs are the live engine's down states. -/
theorem down_live (w : Fin 3) : down w=BitVec.ofNat 32 (Weapon.down w.val) := by
  rcases w with ⟨w,hw⟩; have hc : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases hc with rfl|rfl|rfl <;> rfl

theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (w : Fin 3) (y : Fixed) (h : Inputs s w y) :
    ∃ t, X86Routine.run program [0x2a38c] 55 ⟨s,f,0x2d2c0⟩=some t ∧
      load32 t.core.memory (psp s)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (psp s+4)=1 ∧
      load32 t.core.memory (psp s+12)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=0x2a38c ∧ t.core.regs=write (write s.regs 0 (down w)) 4 (s.regs 4+4) ∧
      PlayerHeight.Frame s.memory t.core.memory (writes s) := by
  refine ⟨final s w,execution s f w y h,?_,?_,?_,rfl,rfl,frame s w⟩
  · have read := (lower_keep s w y h 3 (by decide) (by decide)).trans (read_actionMemory s w y h 3)
    simpa [final,state,down_live] using read
  · have read := (lower_keep s w y h 4 (by decide) (by decide)).trans (read_actionMemory s w y h 4)
    simpa [final] using read
  · simpa [final,lowered,WeaponLower.result,WeaponLower.yAddress,action,write] using
      WeaponLower.final_height (action s w) y (lower_inputs s w y h)

end Doom.Proofs.WeaponDrop

import Doom.Proofs.E1M1NoiseImage
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalSideLoader
open Verification X86 X86Memory X86Control BlockSummary E1M1NoiseImage
def publishBytes : List UInt8 := [0x89,0xc3,0xa3,0x18,0xc1,0x2,0x0]
def linkBytes : List UInt8 := [0xf,0xbf,0x43,0x1c,0x6b,0xc0,0x56,0x45,0x83,0xc3,0x1e,0x83,0xc2,0x12,0x89,0x4,0x24,0xa1,0x48,0xc1,0x2,0x0,0x83,0xc1,0x1e,0x3,0x4,0x24,0x83,0xc7,0x1e,0x89,0x42,0xfc]
def bytesProgram (publish link : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e415≤pc ∧ pc<0x2e41c then X86Routine.decodeAt publish (pc-0x2e415)
  else if 0x2e4af≤pc ∧ pc<0x2e4d1 then X86Routine.decodeAt link (pc-0x2e4af) else none
def program := bytesProgram publishBytes linkBytes
def listed : X86Routine.Program
  | 0x2e415 => some (.control (.block (.legacy (.mov 3 0))),2)
  | 0x2e417 => some (.control (.storeEax 0x2c118),5)
  | 0x2e4af => some (.control (.block (.legacy (.movsx16 0 3 28))),4)
  | 0x2e4b3 => some (.multiplyImmediate 0 0 86,3)
  | 0x2e4b6 => some (.addImmediate 5 1,1)
  | 0x2e4b7 => some (.addImmediate 3 30,3)
  | 0x2e4ba => some (.addImmediate 2 18,3)
  | 0x2e4bd => some (.control (.block (.store ⟨some 4,none,0,0⟩ 0)),3)
  | 0x2e4c0 => some (.control (.block (.load 0 ⟨none,none,0,0x2c148⟩)),5)
  | 0x2e4c5 => some (.addImmediate 1 30,3)
  | 0x2e4c8 => some (.addMemory 0 ⟨some 4,none,0,0⟩,3)
  | 0x2e4cb => some (.addImmediate 7 30,3)
  | 0x2e4ce => some (.control (.block (.store ⟨some 2,none,0,0xfffffffc⟩ 0)),3)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- Publication immediately after Z_Malloc returns. The allocation itself is
not part of this segment; incoming EAX is left unconstrained. -/
def published (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨{ put s 3 (s.regs 0) with memory := store32 s.memory 0x2c118 (s.regs 0) },f,0x2e41c⟩

/-- The signed on-disk sector index is converted before any temporary write. -/
def offset (s : X86Memory.State) : Word := (load16 s.memory (s.regs 3+28)).signExtend 32 * 86
def scratch (s : X86Memory.State) : Memory := store32 s.memory (s.regs 4) (offset s)
/-- The global is deliberately read AFTER the scratch store, even if aliased. -/
def target (s : X86Memory.State) : Word := load32 (scratch s) 0x2c148 + offset s

def linked (s : X86Memory.State) : X86Control.State :=
  let t := put s 0 (target s)
  let t := put t 5 (s.regs 5+1)
  let t := put t 3 (s.regs 3+30)
  let t := put t 2 (s.regs 2+18)
  let t := put t 1 (s.regs 1+30)
  let t := put t 7 (s.regs 7+30)
  ⟨{ t with memory := store32 (scratch s) (s.regs 2+14) (target s) },none,0x2e4d1⟩

@[local simp] private theorem step_2e415 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e41c] (n+1) ⟨s,f,0x2e415⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 3 0)))) ⟨s,f,0x2e417⟩).bind (X86Routine.run listed [0x2e41c] n) := by rfl
@[local simp] private theorem step_2e417 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e41c] (n+1) ⟨s,f,0x2e417⟩ =
      (X86Routine.execute (.control (.storeEax 0x2c118)) ⟨s,f,0x2e41c⟩).bind (X86Routine.run listed [0x2e41c] n) := by rfl
@[local simp] private theorem stop_2e41c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e41c] n ⟨s,f,0x2e41c⟩=some ⟨s,f,0x2e41c⟩ := by cases n <;> rfl
theorem publish_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e41c] 2 ⟨s,f,0x2e415⟩=some (published s f) := by
  have run : X86Routine.run listed [0x2e41c] 2 ⟨s,f,0x2e415⟩=some (published s f) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,published,linked,target,scratch,offset,
      put,write,load_store,BitVec.add_assoc,-BitVec.toInt_add]
    <;> (funext r
         have cases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 := by
           have bound := r.isLt
           simp only [Fin.ext_iff]
           omega
         rcases cases with h|h|h|h|h|h|h|h <;> subst r <;> rfl)
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e4af (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4af⟩ =
      (X86Routine.execute (.control (.block (.legacy (.movsx16 0 3 28)))) ⟨s,f,0x2e4b3⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem step_2e4b3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4b3⟩ =
      (X86Routine.execute (.multiplyImmediate 0 0 86) ⟨s,f,0x2e4b6⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem step_2e4b6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4b6⟩ =
      (X86Routine.execute (.addImmediate 5 1) ⟨s,f,0x2e4b7⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem step_2e4b7 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4b7⟩ =
      (X86Routine.execute (.addImmediate 3 30) ⟨s,f,0x2e4ba⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem step_2e4ba (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4ba⟩ =
      (X86Routine.execute (.addImmediate 2 18) ⟨s,f,0x2e4bd⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem step_2e4bd (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4bd⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 4,none,0,0⟩ 0))) ⟨s,f,0x2e4c0⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem step_2e4c0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4c0⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨none,none,0,0x2c148⟩))) ⟨s,f,0x2e4c5⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem step_2e4c5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4c5⟩ =
      (X86Routine.execute (.addImmediate 1 30) ⟨s,f,0x2e4c8⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem step_2e4c8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4c8⟩ =
      (X86Routine.execute (.addMemory 0 ⟨some 4,none,0,0⟩) ⟨s,f,0x2e4cb⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem step_2e4cb (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4cb⟩ =
      (X86Routine.execute (.addImmediate 7 30) ⟨s,f,0x2e4ce⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem step_2e4ce (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] (n+1) ⟨s,f,0x2e4ce⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 2,none,0,0xfffffffc⟩ 0))) ⟨s,f,0x2e4d1⟩).bind (X86Routine.run listed [0x2e4d1] n) := by rfl
@[local simp] private theorem stop_2e4d1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4d1] n ⟨s,f,0x2e4d1⟩=some ⟨s,f,0x2e4d1⟩ := by cases n <;> rfl
theorem link_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e4d1] 11 ⟨s,f,0x2e4af⟩=some (linked s) := by
  have run : X86Routine.run listed [0x2e4d1] 11 ⟨s,f,0x2e4af⟩=some (linked s) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,published,linked,target,scratch,offset,
      put,write,load_store,BitVec.add_assoc,-BitVec.toInt_add]
    <;> (funext r
         have cases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 := by
           have bound := r.isLt
           simp only [Fin.ext_iff]
           omega
         rcases cases with h|h|h|h|h|h|h|h <;> subst r <;> rfl)
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- Both publication and pointer emission refine the previous byte-plan model. -/
theorem publish_patch (s : X86Memory.State) (f : Option Flags) :
    (published s f).core.memory=applyPatch (word 0x2c118 (s.regs 0)) s.memory := by
  simp [published,apply_word]

def linkPatch (s : X86Memory.State) : E1M1NoiseImage.Patch :=
  word (s.regs 4) (offset s) ++ word (s.regs 2+14) (target s)

theorem link_patch (s : X86Memory.State) :
    (linked s).core.memory=applyPatch (linkPatch s) s.memory := by
  simp only [linkPatch,applyPatch,List.foldl_append]
  change store32 (scratch s) (s.regs 2+14) (target s)=
    applyPatch (word (s.regs 2+14) (target s)) (applyPatch (word (s.regs 4) (offset s)) s.memory)
  simp [apply_word,scratch]

theorem untouched (s : X86Memory.State) (a : Word)
    (outside : ∀ p∈linkPatch s, p.1≠a) : (linked s).core.memory a=s.memory a := by
  rw [link_patch]; exact frame _ _ _ outside

/-- A physical separation premise gives the usual loader formula. Without it,
our execution theorem still retains the actual post-scratch global read. -/
theorem target_value (s : X86Memory.State) (index : BitVec 16) (base : Word)
    (source : load16 s.memory (s.regs 3+28)=index)
    (sectors : load32 s.memory 0x2c148=base) (safe : Apart 0x2c148 (s.regs 4)) :
    target s=base+index.signExtend 32*86 := by
  simp only [target,scratch,load_store_apart _ _ _ _ safe,sectors,offset,source]

theorem pointer_value (s : X86Memory.State) :
    load32 (linked s).core.memory (s.regs 2+14)=target s := by
  exact load_store _ _ _

/-- Connect the concrete loader's side record to the sound graph's lookup
address; side and sector indices are separate quantities. -/
theorem graph_pointer (s : X86Memory.State) (side index : BitVec 16) (sides sectors : Word)
    (record : s.regs 2=sides+side.signExtend 32*18)
    (source : load16 s.memory (s.regs 3+28)=index)
    (base : load32 s.memory 0x2c148=sectors) (safe : Apart 0x2c148 (s.regs 4)) :
    load32 (linked s).core.memory (E1M1NoiseGraph.sideAddress sides side)=sectors+index.signExtend 32*86 := by
  have address : E1M1NoiseGraph.sideAddress sides side=s.regs 2+14 := by
    simp [E1M1NoiseGraph.sideAddress,record,BitVec.add_comm]
  rw [address,pointer_value,target_value s index sectors source base safe]

/-- Ordinary (nonnegative) WAD indices yield the 86-byte sector-array address.
Negative 16-bit values remain covered by the unconditional execution theorem. -/
theorem nonnegative_offset (index : BitVec 16) (valid : index.toNat<32768) :
    index.signExtend 32*86=BitVec.ofNat 32 (index.toNat*86) := by
  have msb : index.msb=false := by
    simp [BitVec.msb_eq_decide] ; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul,BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_mul_right_mod]

/-- Original bytes, modeled instructions and the initializer readback are joined
at this segment's entry. This does not assume that startup reaches that entry. -/
theorem link_execution_pointer (s : X86Memory.State) (f : Option Flags)
    (index : BitVec 16) (base : Word)
    (source : load16 s.memory (s.regs 3+28)=index)
    (sectors : load32 s.memory 0x2c148=base) (safe : Apart 0x2c148 (s.regs 4))
    (valid : index.toNat<32768) :
    ∃ out, X86Routine.run program [0x2e4d1] 11 ⟨s,f,0x2e4af⟩=some out ∧
      out.core.memory=applyPatch (linkPatch s) s.memory ∧
      load32 out.core.memory (s.regs 2+14)=base+BitVec.ofNat 32 (index.toNat*86) := by
  refine ⟨linked s,link_execution s f,link_patch s,?_⟩
  rw [pointer_value,target_value s index base source sectors safe,nonnegative_offset index valid]

end Doom.Proofs.OriginalSideLoader

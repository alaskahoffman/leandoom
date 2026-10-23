import Doom.Proofs.OriginalGroupCount
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace Doom.Verification.GroupCountFixture
open X86 X86Memory X86Control Doom.Proofs Doom.Proofs.OriginalGroupCount BlockSummary

def initial (b : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x6000 else if r=2 then 0xffffffff else if r=6 then 474 else 0x12345678,
    [(0x602e,0xa000),(0x6032,b),(0xa04e,0xffffffff),(0xb04e,7),(0x2c134,475)].foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0x5a)⟩

theorem missing_back :
    load32 (result (initial 0)).core.memory 0xa04e=0 ∧
    load32 (result (initial 0)).core.memory 0xb04e=7 ∧
    (result (initial 0)).core.regs 2=0 ∧ (result (initial 0)).pc=0x2e62b := by decide +kernel

theorem same_sector :
    load32 (result (initial 0xa000)).core.memory 0xa04e=0 ∧
    (result (initial 0xa000)).core.regs 2=0 := by decide +kernel

theorem two_sectors :
    load32 (result (initial 0xb000)).core.memory 0xa04e=0 ∧
    load32 (result (initial 0xb000)).core.memory 0xb04e=8 ∧
    (result (initial 0xb000)).core.regs 2=1 := by decide +kernel

def aliases : X86Memory.State :=
  ⟨fun r => if r=0 then 0x6000 else 0,
    [(0x602e,0x5fe4),(0x6032,0xb000),(0xb04f,7),(0x2c134,2)].foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0x5a)⟩
-- The front-sector count overwrites the back pointer before it is read.
theorem ordered_alias :
    back aliases=0xb001 ∧
    load32 (result aliases).core.memory 0xb04f=8 ∧
    (result aliases).pc=0x2e602 := by decide +kernel

def wraps : X86Memory.State :=
  ⟨fun r => if r=0 then 0x6000 else if r=6 then 0x7fffffff else 0,
    [(0x602e,0xffffffb0),(0x6032,0),(0xfffffffe,0xffffffff),(0x2c134,475)].foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0x5a)⟩
theorem wraps_counter_and_signed_index :
    load32 (result wraps).core.memory 0xfffffffe=0 ∧
    (result wraps).core.regs 6=0x80000000 ∧ (result wraps).pc=0x2e602 := by decide +kernel

theorem linked_inputs :
    OriginalGroupOutput.Inputs [⟨0x6000,0xa000,0xb000⟩] (result (initial 0xb000)).core.memory := by
  apply inputs_preserved
  · intro e member
    simp only [List.mem_singleton] at member
    subst e
    constructor <;> decide +kernel
  · intro e member
    simp only [List.mem_singleton] at member
    subst e
    constructor <;> constructor
    all_goals simp only [Apart]
    all_goals decide +kernel +revert

theorem preservation (s : X86Memory.State) (a : Word) (h : Protected a s) :
    load32 (result s).core.memory a=load32 s.memory a := frame s a h

-- Allocation arithmetic is modulo 2^32; no unwarranted size bound is assumed.
theorem wrapped_allocation :
    (allocation (initial 0)).core.regs 0=0xfffffffc ∧
    (allocation (initial 0)).core.regs 2=50 ∧
    (allocation (initial 0)).core.regs 3=0 := by decide +kernel

#print axioms missing_back
#print axioms same_sector
#print axioms two_sectors
#print axioms ordered_alias
#print axioms wraps_counter_and_signed_index
#print axioms linked_inputs
#print axioms preservation
#print axioms wrapped_allocation
end Doom.Verification.GroupCountFixture

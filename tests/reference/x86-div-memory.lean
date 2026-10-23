import Doom.Verification.X86Routine
namespace Doom.Verification.DivInstructionFixture
open X86 X86Memory X86Control
example : X86Routine.decode [0x99]=some (.cdq,[]) := by decide +kernel
example : X86Routine.decode [0x0f,0x9c,0xc4]=some (.setLess 4,[]) := by decide +kernel
example : X86Routine.decode [0x0f,0xa4,0xc2,0x10]=some (.shld 2 0 16,[]) := by decide +kernel
example : X86Routine.decode [0x0f,0xa4,0x02,0x10]=none := by decide +kernel
example : X86Routine.decode [0x0f,0x9c,0x04]=none := by decide +kernel
example : X86Routine.decode [0x0f,0xa4,0xc2]=none := by decide +kernel

def flags : Flags := ⟨false,true,false,some true⟩
def core : X86Memory.State := ⟨fun r => if r=0 then 0x80001234 else if r=2 then 0x12345678 else 0,fun _ => 0⟩
def observed (op : X86Routine.Op) :=
  (X86Routine.execute op ⟨core,some flags,4⟩).map (fun s => (s.core.regs 0,s.core.regs 2,s.flags,s.pc))
example : observed .cdq=some (0x80001234,0xffffffff,some flags,4) := by decide +kernel
example : observed (.setLess 4)=some (0x80000134,0x12345678,some flags,4) := by decide +kernel
example : observed (.shld 2 0 16)=some (0x80001234,0x56788000,none,4) := by decide +kernel
example : observed (.shld 2 0 32)=some (0x80001234,0x12345678,some flags,4) := by decide +kernel
example : (X86Routine.execute (.setLess 0) ⟨core,none,4⟩).map (·.pc)=none := by decide +kernel
end Doom.Verification.DivInstructionFixture

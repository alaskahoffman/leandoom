import Doom.Proofs.E1M1AimSetupEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimSetupLink
open Verification X86 X86Memory X86Control BlockSummary

/-- The ray and aim epilogue decode identically in the existing union. -/
theorem ray (pc : Nat) (present : X86ReturnCleanup.embed OriginalAimQuery.program pc≠none) :
    E1M1AimProgramLink.program pc=X86ReturnCleanup.embed OriginalAimQuery.program pc := by
  by_cases first : 0x2bb80≤pc ∧ pc<0x2bba0
  · have all : ∀ i : Fin 32, E1M1AimProgramLink.program (0x2bb80+i.val)=
        X86ReturnCleanup.embed OriginalAimQuery.program (0x2bb80+i.val) := by decide
    have eq : 0x2bb80+(pc-0x2bb80)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2bb80,by omega⟩
  · by_cases last : 0x2bbff≤pc ∧ pc<0x2bc19
    · have all : ∀ i : Fin 26, E1M1AimProgramLink.program (0x2bbff+i.val)=
          X86ReturnCleanup.embed OriginalAimQuery.program (0x2bbff+i.val) := by decide
      have eq : 0x2bbff+(pc-0x2bbff)=pc := by omega
      simpa only [eq] using all ⟨pc-0x2bbff,by omega⟩
    · exact False.elim (present (by simp [X86ReturnCleanup.embed,OriginalAimQuery.program,
        OriginalAimQuery.bytesProgram,first,last]))

/-- Setup's original decoded operations and lengths need no new program map. -/
theorem setup (pc : Nat) (present : X86ReturnCleanup.embed OriginalAimSetup.program pc≠none) :
    E1M1AimProgramLink.program pc=X86ReturnCleanup.embed OriginalAimSetup.program pc := by
  have inside : 0x2bba0≤pc ∧ pc<0x2bbff := by
    by_cases inside : 0x2bba0≤pc ∧ pc<0x2bbff
    · exact inside
    · exact False.elim (present (by simp [X86ReturnCleanup.embed,OriginalAimSetup.program,
        OriginalAimSetup.bytesProgram,inside]))
  have all : ∀ i : Fin 95, E1M1AimProgramLink.program (0x2bba0+i.val)=
      X86ReturnCleanup.embed OriginalAimSetup.program (0x2bba0+i.val) := by decide
  have eq : 0x2bba0+(pc-0x2bba0)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2bba0,by omega⟩

/-- All 36 actual instructions from aim entry to the traversal CALL in the same
map used by collection, ordered processing, returns and target decisions. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] 36
      ⟨s,f,0x2bb80⟩ (E1M1PathMapQuery.traversal s) := by
  have a := (X86ReturnCleanup.lift (X86CodeMemory.lift_success
    (OriginalAimQuery.ray_execution s f) FloorCaller.cm)).transfer E1M1AimProgramLink.program ray
  have b := (X86ReturnCleanup.lift (X86CodeMemory.lift_success
    (OriginalAimSetup.execution (OriginalAimQuery.ray s).core none) FloorCaller.cm)).transfer
    E1M1AimProgramLink.program setup
  exact a.trans b
end Doom.Proofs.E1M1AimSetupLink

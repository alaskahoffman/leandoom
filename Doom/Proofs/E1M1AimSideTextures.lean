import Doom.Proofs.OriginalSideTextures
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimSideTextures
open Verification X86 X86Memory X86Control BlockSummary
open OriginalSideTextures (firstCall secondCall thirdCall stored finished)
open E1M1NoiseImage (Realizes word)
open E1M1AimSideEncoding (Input sectorAddress)

/-- Actual lookup-body executions are premises, not a texture oracle or an
invented return instruction. They must start at the caller's real pushed state
and end at its exact return PC. The enclosing program may contain those bodies. -/
theorem caller_path (q : X86Routine.Program)
    (agree : ∀ pc, OriginalSideTextures.program pc≠none → q pc=OriginalSideTextures.program pc)
    (s a b c : X86Memory.State) (f fa fb fc : Option Flags) (na nb nc : Nat)
    (lookupA : X86Routine.Prefix q [] na (firstCall s f) ⟨a,fa,0x2e483⟩)
    (lookupB : X86Routine.Prefix q [] nb (secondCall a fa) ⟨b,fb,0x2e494⟩)
    (lookupC : X86Routine.Prefix q [] nc (thirdCall b fb) ⟨c,fc,0x2e4a5⟩) :
    ∃ n≤14+na+nb+nc, X86Routine.Prefix q [] n ⟨s,f,0x2e47e⟩ (finished c fc) := by
  obtain ⟨i,hi,pi,_⟩ := X86Routine.run_path (OriginalSideTextures.first_execution s f)
  obtain ⟨j,hj,pj,_⟩ := X86Routine.run_path (OriginalSideTextures.second_execution a fa)
  obtain ⟨k,hk,pk,_⟩ := X86Routine.run_path (OriginalSideTextures.third_execution b fb)
  obtain ⟨l,hl,pl,_⟩ := X86Routine.run_path (OriginalSideTextures.finish_execution c fc)
  have pi := pi.transfer q [] agree (by simp)
  have pj := pj.transfer q [] agree (by simp)
  have pk := pk.transfer q [] agree (by simp)
  have pl := pl.transfer q [] agree (by simp)
  exact ⟨i+na+j+nb+k+nc+l,by omega,
    OriginalGroupBounds.prefix_join
      (OriginalGroupBounds.prefix_join
        (OriginalGroupBounds.prefix_join
          (OriginalGroupBounds.prefix_join
            (OriginalGroupBounds.prefix_join
              (OriginalGroupBounds.prefix_join pi lookupA) pj) lookupB) pk) lookupC) pl⟩

/-- Once the real lookup paths are supplied, the caller joins directly to the
already proved pointer emission and loop latch. Input describes the actual
post-texture memory; establishing it from startup is still a separate task. -/
theorem linked_path (q : X86Routine.Program)
    (agree : ∀ pc, OriginalSideTextures.program pc≠none → q pc=OriginalSideTextures.program pc)
    (advance : ∀ pc, OriginalSideAdvance.program pc≠none → q pc=OriginalSideAdvance.program pc)
    (s a b c : X86Memory.State) (f fa fb fc : Option Flags) (na nb nc : Nat)
    (lookupA : X86Routine.Prefix q [] na (firstCall s f) ⟨a,fa,0x2e483⟩)
    (lookupB : X86Routine.Prefix q [] nb (secondCall a fa) ⟨b,fb,0x2e494⟩)
    (lookupC : X86Routine.Prefix q [] nc (thirdCall b fb) ⟨c,fc,0x2e4a5⟩)
    (side : BitVec 16) (sectorIndex : Nat) (sideBase sectorBase : Word)
    (input : Input (stored c 12) side sectorIndex sideBase sectorBase) :
    (∃ n≤29+na+nb+nc, X86Routine.Prefix q [] n ⟨s,f,0x2e47e⟩
      (OriginalSideAdvance.result (stored c 12))) ∧
    Realizes (word (E1M1NoiseGraph.sideAddress sideBase side) (sectorAddress sectorBase sectorIndex))
      (OriginalSideAdvance.result (stored c 12)).core.memory := by
  obtain ⟨n,hn,path⟩ := caller_path q agree s a b c f fa fb fc na nb nc lookupA lookupB lookupC
  have emitted := E1M1AimSideAdvance.emitted (stored c 12) fc side sectorIndex sideBase sectorBase input
  obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path emitted.1
  have tail := tail.transfer q [] advance (by simp)
  exact ⟨⟨n+k,by omega,OriginalGroupBounds.prefix_join path tail⟩,emitted.2⟩

structure Safe (s : X86Memory.State) (a off : Word) : Prop where
  scratch : Apart a (s.regs 4)
  field : HalfMemory.Separate 4 2 a (s.regs 2+off)
  call : Apart a (s.regs 4-4)

/-- The caller's own stores/pushes are discharged by precise write separation.
Only the helper-body word frames are left as preservation premises. -/
theorem caller_frame (s a b c : X86Memory.State) (f fa fb fc : Option Flags) (address : Word)
    (firstSafe : Apart address (s.regs 4-4))
    (secondSafe : Safe a address 8) (thirdSafe : Safe b address 10)
    (finalScratch : Apart address (c.regs 4))
    (finalField : HalfMemory.Separate 4 2 address (c.regs 2+12))
    (lookupA : load32 a.memory address=load32 (firstCall s f).core.memory address)
    (lookupB : load32 b.memory address=load32 (secondCall a fa).core.memory address)
    (lookupC : load32 c.memory address=load32 (thirdCall b fb).core.memory address) :
    load32 (finished c fc).core.memory address=load32 s.memory address := by
  exact (OriginalSideTextures.stored_frame c 12 address finalScratch finalField).trans
    (lookupC.trans ((OriginalSideTextures.third_frame b fb address thirdSafe.scratch thirdSafe.field thirdSafe.call).trans
    (lookupB.trans ((OriginalSideTextures.second_frame a fa address secondSafe.scratch secondSafe.field secondSafe.call).trans
    (lookupA.trans (OriginalSideTextures.first_frame s f address firstSafe))))))

theorem caller_encoding (s a b c : X86Memory.State) (f fa fb fc : Option Flags) (address value : Word)
    (image : Realizes (word address value) s.memory)
    (firstSafe : Apart address (s.regs 4-4))
    (secondSafe : Safe a address 8) (thirdSafe : Safe b address 10)
    (finalScratch : Apart address (c.regs 4))
    (finalField : HalfMemory.Separate 4 2 address (c.regs 2+12))
    (lookupA : load32 a.memory address=load32 (firstCall s f).core.memory address)
    (lookupB : load32 b.memory address=load32 (secondCall a fa).core.memory address)
    (lookupC : load32 c.memory address=load32 (thirdCall b fb).core.memory address) :
    Realizes (word address value) (finished c fc).core.memory := by
  apply E1M1AimSideEncoding.word_of_load
  exact (caller_frame s a b c f fa fb fc address firstSafe secondSafe thirdSafe finalScratch finalField
    lookupA lookupB lookupC).trans (E1M1NoiseImage.read_word image)

/-- The previous side's sector pointer and this side's three texture fields
have disjoint modular byte ranges. No heap nonwrapping assumption is needed. -/
theorem previous_fields (base off : Word) (member : off∈[(8#32),10,12]) :
    HalfMemory.Separate 4 2 (base+14) (base+18+off) := by
  have h : HalfMemory.Separate 4 2 (14#32) (18+off) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> unfold HalfMemory.Separate <;> decide
  simpa only [BitVec.add_assoc] using HalfMemory.translate base 14 (18+off) 4 2 h

theorem previous_safe (s : X86Memory.State) (base sp off : Word)
    (member : off∈[(8#32),10,12]) (record : s.regs 2=base+18) (stack : s.regs 4=sp)
    (scratch : Apart (base+14) sp) (call : Apart (base+14) (sp-4)) :
    Safe s (base+14) off := by
  refine ⟨by rw [stack]; exact scratch,?_,by rw [stack]; exact call⟩
  rw [record]
  exact previous_fields base off member

end Doom.Proofs.E1M1AimSideTextures

import Doom.Proofs.OriginalNoiseOpening
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1NoiseOpening
open Verification X86 X86Memory X86Control

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2c340≤pc ∧ pc<0x2c3aa then NoiseOpening.program pc else E1M1NoiseTraversal.program pc

theorem contains_opening (pc : Nat) (h : NoiseOpening.program pc≠none) : program pc=NoiseOpening.program pc := by
  by_cases inside : 0x2c340≤pc ∧ pc<0x2c3aa
  · simp [program,inside]
  · by_cases neighbor : 0x26fc4≤pc ∧ pc<0x26fee
    · have checked : ∀ i : Fin 42, program (0x26fc4+i.val)=NoiseOpening.program (0x26fc4+i.val) := by decide
      have eq : 0x26fc4+(pc-0x26fc4)=pc := by omega
      simpa only [eq] using checked ⟨pc-0x26fc4,by omega⟩
    · exact False.elim (h (by simp [NoiseOpening.program,NoiseOpening.bytesProgram,inside,neighbor]))
theorem contains_prior (pc : Nat) (h : E1M1NoiseTraversal.program pc≠none) : program pc=E1M1NoiseTraversal.program pc := by
  by_cases inside : 0x2c340≤pc ∧ pc<0x2c3aa
  · have checked : ∀ i : Fin 106, E1M1NoiseTraversal.program (0x2c340+i.val)=none := by decide
    have eq : 0x2c340+(pc-0x2c340)=pc := by omega
    exact False.elim (h (by simpa only [eq] using checked ⟨pc-0x2c340,by omega⟩))
  · simp [program,inside]
private theorem contains_traversal (pc : Nat) (h : NoiseTraversal.program pc≠none) : program pc=NoiseTraversal.program pc := by
  have a := E1M1NoiseTraversal.contains_traversal pc h
  rw [contains_prior pc (by rw [a]; exact h),a]
private theorem path {stops n s t} (run : X86Routine.run NoiseOpening.program stops n s=some t) :
    ∃ k, k≤n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_opening (by simp)⟩
private theorem traversal_path {stops n s t} (run : X86Routine.run NoiseTraversal.program stops n s=some t) :
    ∃ k, k≤n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,p,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success p FloorCaller.cm).transfer program [] contains_traversal (by simp)⟩

private theorem range_flags (s : X86Memory.State) : (NoiseOpening.range s).flags=none := rfl

def result (s : X86Memory.State) : X86Control.State :=
  let e := NoiseOpening.entry s
  let r := if e.pc=0x2c34f then NoiseOpening.closed e.core else
    NoiseOpening.range (NoiseOpening.floor (NoiseOpening.ceiling e.core).core).core
  NoiseOpening.returned r.core r.flags

/-- Entire original P_LineOpening, including its real RET. All reads observe
preceding stack/global writes; no separation assumptions are hidden here. -/
theorem opening_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤31 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2c340⟩ (result s) := by
  obtain ⟨n,hn,p⟩ := path (NoiseOpening.entry_execution s f)
  by_cases one : (NoiseOpening.entry s).pc=0x2c34f
  · obtain ⟨m,hm,q⟩ := path (NoiseOpening.closed_execution (NoiseOpening.entry s).core (NoiseOpening.entry s).flags)
    have eq : NoiseOpening.entry s=⟨(NoiseOpening.entry s).core,(NoiseOpening.entry s).flags,0x2c34f⟩ := by rw [←one]
    rw [←eq] at q
    have r := (X86CodeMemory.lift_success (NoiseOpening.return_execution (NoiseOpening.closed (NoiseOpening.entry s).core).core (NoiseOpening.closed (NoiseOpening.entry s).core).flags) FloorCaller.cm).transfer program [] contains_opening (by simp)
    exact ⟨n+m+6,by omega,by simpa only [result,one,if_pos,ite_true] using E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r⟩
  · have pc : (NoiseOpening.entry s).pc=0x2c353 := by simp_all [NoiseOpening.entry]
    obtain ⟨a,ha,q⟩ := path (NoiseOpening.ceiling_execution (NoiseOpening.entry s).core (NoiseOpening.entry s).flags)
    have eq : NoiseOpening.entry s=⟨(NoiseOpening.entry s).core,(NoiseOpening.entry s).flags,0x2c353⟩ := by rw [←pc]
    rw [←eq] at q
    obtain ⟨b,hb,r⟩ := path (NoiseOpening.floor_execution (NoiseOpening.ceiling (NoiseOpening.entry s).core).core (NoiseOpening.ceiling (NoiseOpening.entry s).core).flags)
    obtain ⟨c,hc,t⟩ := path (NoiseOpening.range_execution (NoiseOpening.floor (NoiseOpening.ceiling (NoiseOpening.entry s).core).core).core (NoiseOpening.floor (NoiseOpening.ceiling (NoiseOpening.entry s).core).core).flags)
    have u := (X86CodeMemory.lift_success (NoiseOpening.return_execution (NoiseOpening.range (NoiseOpening.floor (NoiseOpening.ceiling (NoiseOpening.entry s).core).core).core).core none) FloorCaller.cm).transfer program [] contains_opening (by simp)
    exact ⟨n+a+b+c+6,by omega,by simpa only [result,one,if_neg,ite_false,range_flags] using E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r) t) u⟩

def neighbor (s : X86Memory.State) : X86Control.State :=
  let g := NoiseOpening.neighborGate s
  if g.pc=0x26fdd then NoiseOpening.backNeighbor g.core else NoiseOpening.frontNeighbor g.core g.flags

theorem neighbor_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤13 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26fc4⟩ (neighbor s) := by
  obtain ⟨n,hn,p⟩ := path (NoiseOpening.neighbor_gate_execution s f)
  by_cases back : (NoiseOpening.neighborGate s).pc=0x26fdd
  · obtain ⟨m,hm,q⟩ := path (NoiseOpening.back_neighbor_execution (NoiseOpening.neighborGate s).core (NoiseOpening.neighborGate s).flags)
    have eq : NoiseOpening.neighborGate s=⟨(NoiseOpening.neighborGate s).core,(NoiseOpening.neighborGate s).flags,0x26fdd⟩ := by rw [←back]
    rw [←eq] at q
    exact ⟨n+m,by omega,by simpa only [neighbor,back,if_pos,ite_true] using E1M1PspriteStep.prefix_trans p q⟩
  · have pc : (NoiseOpening.neighborGate s).pc=0x26fec := by simp_all [NoiseOpening.neighborGate]
    obtain ⟨m,hm,q⟩ := path (NoiseOpening.front_neighbor_execution (NoiseOpening.neighborGate s).core (NoiseOpening.neighborGate s).flags)
    have eq : NoiseOpening.neighborGate s=⟨(NoiseOpening.neighborGate s).core,(NoiseOpening.neighborGate s).flags,0x26fec⟩ := by rw [←pc]
    rw [←eq] at q
    exact ⟨n+m,by omega,by simpa only [neighbor,back,if_neg,ite_false] using E1M1PspriteStep.prefix_trans p q⟩

def opened (s : X86Memory.State) (f : Option Flags) := result (NoiseTraversal.openingCall s f).core
def lineResult (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let g := NoiseTraversal.openingGate (opened s f).core
  if g.pc=0x26fc4 then neighbor g.core else g

theorem line_execution (s : X86Memory.State) (f : Option Flags)
    (ret : (opened s f).pc=0x26fbb) :
    ∃ n, n≤48 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26fb4⟩ (lineResult s f) := by
  obtain ⟨a,ha,p⟩ := traversal_path (NoiseTraversal.opening_call_execution s f)
  obtain ⟨b,hb,q⟩ := opening_execution (NoiseTraversal.openingCall s f).core (NoiseTraversal.openingCall s f).flags
  obtain ⟨c,hc,r⟩ := traversal_path (NoiseTraversal.opening_gate_execution (opened s f).core (opened s f).flags)
  have eq : opened s f=⟨(opened s f).core,(opened s f).flags,0x26fbb⟩ := by rw [←ret]
  rw [←eq] at r
  have joined :=  E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r
  by_cases pass : (NoiseTraversal.openingGate (opened s f).core).pc=0x26fc4
  · obtain ⟨d,hd,t⟩ := neighbor_execution (NoiseTraversal.openingGate (opened s f).core).core (NoiseTraversal.openingGate (opened s f).core).flags
    have eg : NoiseTraversal.openingGate (opened s f).core=⟨(NoiseTraversal.openingGate (opened s f).core).core,(NoiseTraversal.openingGate (opened s f).core).flags,0x26fc4⟩ := by rw [←pass]
    rw [←eg] at t
    exact ⟨a+b+c+d,by omega,by simpa only [lineResult,pass,if_pos,ite_true] using E1M1PspriteStep.prefix_trans joined t⟩
  · exact ⟨a+b+c,by omega,by simpa only [lineResult,pass,if_neg,ite_false] using joined⟩

def blockResult (s : X86Memory.State) (f : Option Flags) :=
  let t := lineResult s f
  if t.pc=0x26fee then NoiseTraversal.blockResult t.core else t

theorem block_execution (s : X86Memory.State) (f : Option Flags)
    (ret : (opened s f).pc=0x26fbb) :
    ∃ n, n≤55 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x26fb4⟩ (blockResult s f) := by
  obtain ⟨n,hn,p⟩ := line_execution s f ret
  by_cases pass : (lineResult s f).pc=0x26fee
  · obtain ⟨m,hm,q⟩ := traversal_path (NoiseTraversal.block_execution (lineResult s f).core (lineResult s f).flags)
    have eq : lineResult s f=⟨(lineResult s f).core,(lineResult s f).flags,0x26fee⟩ := by rw [←pass]
    rw [←eq] at q
    exact ⟨n+m,by omega,by simpa only [blockResult,pass,if_pos,ite_true] using E1M1PspriteStep.prefix_trans p q⟩
  · exact ⟨n,by omega,by simpa only [blockResult,pass,if_neg,ite_false] using p⟩
end Doom.Proofs.E1M1NoiseOpening

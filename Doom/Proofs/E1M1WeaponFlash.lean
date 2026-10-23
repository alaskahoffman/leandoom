import Doom.Proofs.E1M1FlashExpiry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Proofs.E1M1WeaponFlash
open Verification X86 X86Memory X86Control BlockSummary

/-- At the completed weapon-slot boundary. The fields refer to the state after
weapon actions, so a newly-created flash is counted down on the same tic. -/
structure Boundary (s : X86Memory.State) (p : Word) (v : Weapon.State) : Prop where
  slot : s.regs 1=p+(244#32)
  player : s.regs 7=p
  index : s.regs 6=(0#32)
  state : load32 s.memory (p+(260#32))=WeaponFlash.pointer v.flash.frame
  timer : load32 s.memory (p+(264#32))=v.flash.tics.toBitVec
  light : load32 s.memory (p+(232#32))=v.extraLight.toBitVec
  x : load32 s.memory (p+(252#32))=v.weapon.x.raw.toBitVec
  y : load32 s.memory (p+(256#32))=v.weapon.y.raw.toBitVec

theorem advance_inputs (s : X86Memory.State) (p : Word) (v : Weapon.State) (h : Boundary s p v) :
    E1M1FlashUpdate.Inputs (PspriteLoop.advanced s).core p v := by
  constructor <;> simp [PspriteLoop.advanced,put,write,h.slot,h.player,h.index,h.state,h.timer,h.light,h.x,h.y,BitVec.add_assoc]

/-- The actual loop increment connects the weapon boundary to the flash theorem. -/
theorem suffix_correspondence (s : X86Control.State) (p : Word) (v : Weapon.State)
    (pc : s.pc=0x2dc95) (h : Boundary s.core p v) (supported : WeaponFlash.Supported v)
    (expiry : ¬ E1M1FlashUpdate.NoTransition v → E1M1FlashExpiry.Tables s.core.memory ∧
      E1M1FlashExpiry.Separated p (s.core.regs 4)) :
    ∃ n t, n ≤ 110 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n s t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (PspriteLoop.advance_execution s.core s.flags)
  have a := (X86CodeMemory.lift_success a FloorCaller.cm).transfer E1M1PspriteLight.program [] E1M1PspriteLight.contains_tail (by simp)
  have start : s=⟨s.core,s.flags,0x2dc95⟩ := by rw [←pc]
  rw [←start] at a
  have next : PspriteLoop.advanced s.core=⟨(PspriteLoop.advanced s.core).core,(PspriteLoop.advanced s.core).flags,0x2dc6f⟩ := by
    simp [PspriteLoop.advanced,h.index]
  obtain ⟨m,t,hm,b,obs⟩ := E1M1FlashExpiry.live_correspondence (PspriteLoop.advanced s.core).core
    (PspriteLoop.advanced s.core).flags p v (advance_inputs _ _ _ h) supported
    (by simpa [PspriteLoop.advanced,put,write] using expiry)
  rw [←next] at b
  exact ⟨n+m,t,by omega,E1M1PspriteStep.prefix_trans a b,obs⟩

/-- A reusable seam for future weapon-action proofs. The preceding prefix and
its complete machine state remain explicit; this theorem does not prove it. -/
theorem append (budget : Nat) (s u : X86Control.State) (p : Word) (v : Weapon.State)
    (earlier : ∃ n, n ≤ budget ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n s u)
    (pc : u.pc=0x2dc95) (h : Boundary u.core p v) (supported : WeaponFlash.Supported v)
    (expiry : ¬ E1M1FlashUpdate.NoTransition v → E1M1FlashExpiry.Tables u.core.memory ∧
      E1M1FlashExpiry.Separated p (u.core.regs 4)) :
    ∃ n t, n ≤ budget+110 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n s t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) := by
  obtain ⟨n,hn,a⟩ := earlier
  obtain ⟨m,t,hm,b,obs⟩ := suffix_correspondence u p v pc h supported expiry
  exact ⟨n+m,t,by omega,E1M1PspriteStep.prefix_trans a b,obs⟩

/-- No weapon state/action transition occurs. This does not restrict the flash. -/
def Quiet (v : Weapon.State) : Prop :=
  v.weapon.frame=0 ∨ v.weapon.tics=(-1 : Int32) ∨ v.weapon.tics-1≠(0 : Int32)

def countdown (v : Weapon.State) : Weapon.State :=
  if v.weapon.frame=0 ∨ v.weapon.tics=(-1 : Int32) then v
  else {v with weapon := {v.weapon with tics := v.weapon.tics-1}}

theorem live_tick (c : Weapon.Context) (quiet : Quiet c.state) :
    Weapon.tick c={c with events := #[],state := Weapon.tickFlash (countdown c.state)} := by
  rcases quiet with empty|permanent|running
  · simp [Weapon.tick,countdown,empty]
  · simp [Weapon.tick,countdown,permanent]
  · by_cases empty : c.state.weapon.frame=0 <;> by_cases permanent : c.state.weapon.tics=(-1 : Int32) <;>
      simp [Weapon.tick,countdown,empty,permanent,running]

/-- The only memory write on the quiet weapon path. -/
def counted (m : Memory) (p : Word) (v : Weapon.State) : Memory :=
  if v.weapon.frame=0 ∨ v.weapon.tics=(-1 : Int32) then m
  else store32 m (p+(248#32)) (v.weapon.tics.toBitVec-(1#32))

structure Inputs (s : X86Memory.State) (p : Word) (v : Weapon.State) extends Boundary s p v where
  weaponPresent : load32 s.memory (p+(244#32))=(0#32) ↔ v.weapon.frame=0
  weaponTimer : load32 s.memory (p+(248#32))=v.weapon.tics.toBitVec

/-- Precise countdown result before the loop advances to the flash. -/
theorem weapon_summary (s : X86Memory.State) (p : Word) (v : Weapon.State)
    (h : Inputs s p v) (quiet : Quiet v) :
    (PspriteStep.result s).pc=0x2dc95 ∧ (PspriteStep.result s).core.regs 1=s.regs 1 ∧
    (PspriteStep.result s).core.regs 7=s.regs 7 ∧ (PspriteStep.result s).core.regs 6=s.regs 6 ∧
    (PspriteStep.result s).core.regs 4=s.regs 4 ∧ (PspriteStep.result s).core.memory=counted s.memory p v := by
  have state : PspriteStep.stateWord s=(0#32) ↔ v.weapon.frame=0 := by simpa [PspriteStep.stateWord,h.slot] using h.weaponPresent
  have timer : PspriteStep.tics s=v.weapon.tics.toBitVec := by simpa [PspriteStep.tics,h.slot,BitVec.add_assoc] using h.weaponTimer
  have minus : v.weapon.tics=(-1 : Int32) ↔ v.weapon.tics.toBitVec=(0xffffffff#32) := by
    constructor
    · intro e; rw [e]; decide
    · intro e; exact Int32.toBitVec_inj.mp e
  have zero : v.weapon.tics-1=(0 : Int32) ↔ v.weapon.tics.toBitVec-(1#32)=(0#32) := by
    constructor
    · intro e; exact congrArg Int32.toBitVec e
    · intro e; exact Int32.toBitVec_inj.mp e
  unfold PspriteStep.result
  simp only [BitVec.ofNat_eq_ofNat,state,timer,←minus,←zero]
  rcases quiet with empty|permanent|running
  · simp [empty,counted,put,write]
  · by_cases empty : v.weapon.frame=0 <;> simp [empty,permanent,counted,PspriteStep.counting,put,write]
  · by_cases empty : v.weapon.frame=0 <;> by_cases permanent : v.weapon.tics=(-1 : Int32) <;>
      simp [empty,permanent,running,counted,PspriteStep.counting,PspriteStep.decremented,put,write,
        h.slot,timer,BitVec.add_assoc,BitVec.ofNat_eq_ofNat]


/-- The weapon countdown word cannot overlap any of the flash proof's player,
stack, or table words. This is an initial byte-range condition. -/
def Safe (p sp : Word) : Prop :=
  ∀ i : Fin 19, Apart (E1M1FlashExpiry.location p sp i) (p+(248#32))

theorem counted_read (m : Memory) (p sp : Word) (v : Weapon.State) (safe : Safe p sp) (i : Fin 19) :
    load32 (counted m p v) (E1M1FlashExpiry.location p sp i)=
      load32 m (E1M1FlashExpiry.location p sp i) := by
  unfold counted
  split
  · rfl
  · exact load_store_apart _ _ _ _ (safe i)

@[simp] theorem countdown_flash (v : Weapon.State) : (countdown v).flash=v.flash := by
  unfold countdown; split <;> rfl
@[simp] theorem countdown_light (v : Weapon.State) : (countdown v).extraLight=v.extraLight := by
  unfold countdown; split <;> rfl
@[simp] theorem countdown_x (v : Weapon.State) : (countdown v).weapon.x=v.weapon.x := by
  unfold countdown; split <;> rfl
@[simp] theorem countdown_y (v : Weapon.State) : (countdown v).weapon.y=v.weapon.y := by
  unfold countdown; split <;> rfl

theorem boundary_transport (s : X86Memory.State) (p : Word) (v : Weapon.State)
    (h : Inputs s p v) (quiet : Quiet v) (safe : Safe p (s.regs 4)) :
    Boundary (PspriteStep.result s).core p (countdown v) := by
  have sum := weapon_summary s p v h quiet
  constructor
  · rw [sum.2.1]; exact h.slot
  · rw [sum.2.2.1]; exact h.player
  · rw [sum.2.2.2.1]; exact h.index
  · rw [sum.2.2.2.2.2]
    have read := counted_read s.memory p (s.regs 4) v safe 3
    rw [E1M1FlashExpiry.location_3] at read
    simpa using read.trans h.state
  · rw [sum.2.2.2.2.2]
    have read := counted_read s.memory p (s.regs 4) v safe 4
    rw [E1M1FlashExpiry.location_4] at read
    simpa using read.trans h.timer
  · rw [sum.2.2.2.2.2]
    have read := counted_read s.memory p (s.regs 4) v safe 0
    rw [E1M1FlashExpiry.location_0] at read
    simpa using read.trans h.light
  · rw [sum.2.2.2.2.2]
    have read := counted_read s.memory p (s.regs 4) v safe 1
    rw [E1M1FlashExpiry.location_1] at read
    simpa using read.trans h.x
  · rw [sum.2.2.2.2.2]
    have read := counted_read s.memory p (s.regs 4) v safe 2
    rw [E1M1FlashExpiry.location_2] at read
    simpa using read.trans h.y

theorem tables_transport (m : Memory) (p sp : Word) (v : Weapon.State)
    (tables : E1M1FlashExpiry.Tables m) (safe : Safe p sp) :
    E1M1FlashExpiry.Tables (counted m p v) := by
  constructor
  · have read := counted_read m p sp v safe 9
    rw [E1M1FlashExpiry.location_9] at read
    exact read.trans tables.lightDoneTics
  · have read := counted_read m p sp v safe 10
    rw [E1M1FlashExpiry.location_10] at read
    exact read.trans tables.lightDoneAction
  · have read := counted_read m p sp v safe 11
    rw [E1M1FlashExpiry.location_11] at read
    exact read.trans tables.lightDoneNext
  · have read := counted_read m p sp v safe 12
    rw [E1M1FlashExpiry.location_12] at read
    exact read.trans tables.lightDoneMisc
  · have read := counted_read m p sp v safe 13
    rw [E1M1FlashExpiry.location_13] at read
    exact read.trans tables.shotgun2Tics
  · have read := counted_read m p sp v safe 14
    rw [E1M1FlashExpiry.location_14] at read
    exact read.trans tables.shotgun2Action
  · have read := counted_read m p sp v safe 15
    rw [E1M1FlashExpiry.location_15] at read
    exact read.trans tables.shotgun2Next
  · have read := counted_read m p sp v safe 16
    rw [E1M1FlashExpiry.location_16] at read
    exact read.trans tables.shotgun2Misc
  · have read := counted_read m p sp v safe 17
    rw [E1M1FlashExpiry.location_17] at read
    exact read.trans tables.pistolNext
  · have read := counted_read m p sp v safe 18
    rw [E1M1FlashExpiry.location_18] at read
    exact read.trans tables.shotgun1Next

/-- Concrete weapon countdown followed by every supported flash case. The
observation is of the production Weapon.tick, not just its isolated helper.
The conclusion covers the five flash fields; other weapon/player fields and
weapon action transitions need their own correspondence theorems. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (p : Word) (c : Weapon.Context)
    (h : Inputs s p c.state) (quiet : Quiet c.state) (supported : WeaponFlash.Supported c.state)
    (safe : Safe p (s.regs 4))
    (expiry : ¬ E1M1FlashUpdate.NoTransition c.state → E1M1FlashExpiry.Tables s.memory ∧
      E1M1FlashExpiry.Separated p (s.regs 4)) :
    ∃ n t, n ≤ 125 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n ⟨s,f,0x2dc6f⟩ t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tick c).state := by
  have sum := weapon_summary s p c.state h quiet
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (PspriteStep.slot_execution s f)
  have a := (X86CodeMemory.lift_success a FloorCaller.cm).transfer E1M1PspriteLight.program [] E1M1PspriteLight.contains_slot (by simp)
  obtain ⟨m,t,hm,b,obs⟩ := suffix_correspondence (PspriteStep.result s) p (countdown c.state) sum.1
    (boundary_transport s p c.state h quiet safe)
    (by simpa [WeaponFlash.Supported] using supported) (by
      intro expires
      have original : ¬ E1M1FlashUpdate.NoTransition c.state := by simpa [E1M1FlashUpdate.NoTransition] using expires
      obtain ⟨tables,sep⟩ := expiry original
      rw [sum.2.2.2.2.1,sum.2.2.2.2.2]
      exact ⟨tables_transport s.memory p (s.regs 4) c.state tables safe,sep⟩)
  refine ⟨n+m,t,by omega,E1M1PspriteStep.prefix_trans a b,?_⟩
  rw [live_tick c quiet]
  exact obs

end Doom.Proofs.E1M1WeaponFlash

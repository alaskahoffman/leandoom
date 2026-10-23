import Doom.Proofs.E1M1PreparedFloor
import Doom.Proofs.OriginalWeaponSelect
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1PlayerSelection
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match WeaponSelect.program pc with
  | some op => some op
  | none => E1M1PreparedFloor.program pc

theorem contains_selection (pc : Nat) (h : WeaponSelect.program pc≠none) :
    program pc=WeaponSelect.program pc := by
  unfold program
  cases eq : WeaponSelect.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_prepared (pc : Nat) (h : E1M1PreparedFloor.program pc≠none) :
    program pc=E1M1PreparedFloor.program pc := by
  by_cases inside : 0x333e5 ≤ pc ∧ pc < 0x33476
  · have checked : ∀ i : Fin 145, E1M1PreparedFloor.program (0x333e5+i.val)=none := by decide
    have e : 0x333e5+(pc-0x333e5)=pc := by omega
    exact False.elim (h (by simpa only [e] using checked ⟨pc-0x333e5,by omega⟩))
  · simp [program,WeaponSelect.program,WeaponSelect.bytesProgram,inside]

/-- Stitch the selection instructions onto a previously proved preparation and
floor run. This lemma changes no register, flag, PC or memory at the seam. -/
theorem append_selection (s before : X86Control.State) (b : BitVec 8) (w : Fin 3)
    (earlier : X86CodeMemory.run FloorCaller.cm E1M1PreparedFloor.program [0x333e5] 567 s=some before)
    (pc : before.pc=0x333e5) (h : WeaponSelect.Inputs before.core b w) :
    X86CodeMemory.run FloorCaller.cm program [0x33476] 591 s=some (WeaponSelect.result before.core b w) := by
  have suffix := WeaponSelect.execution before.core before.flags b w h
  have suffix : X86Routine.run WeaponSelect.program [0x33476] 24 before=some (WeaponSelect.result before.core b w) := by
    have e : before=⟨before.core,before.flags,0x333e5⟩ := by rw [←pc]
    rw [e]; exact suffix
  obtain ⟨k,hk,path,done⟩ := X86Routine.run_path suffix
  have path := (X86CodeMemory.lift_success path FloorCaller.cm).transfer program [0x33476]
    contains_selection (by intro a ha; simp only [List.mem_singleton]; intro e; subst a; exact ha (by decide))
  have tail : X86CodeMemory.run FloorCaller.cm program [0x33476] 24 before=some (WeaponSelect.result before.core b w) := path.finish (fuel := 0) (by simp [X86CodeMemory.run,done]) 24 (by omega)
  obtain ⟨n,hn,path,_⟩ := X86CodeMemory.run_path earlier
  have path := path.transfer program [0x33476] contains_prepared (by
    intro a ha; simp only [List.mem_singleton]; intro e; subst a; exact ha (by decide))
  exact path.finish tail 591 (by omega)

/-- Reads needed by the selector and its live-helper correspondence. The
buttons byte is read through cmd+4's containing word: reading four bytes from
cmd+7 would overlap the adjacent view-height field in the real player layout. -/
def reads (s : X86Memory.State) (w : Fin 3) : List Word :=
  [s.regs 3+4,s.regs 2+148,0x2a3bc,s.regs 2+BitVec.ofNat 32 w.val*4+120,s.regs 2+112,s.regs 2+116]

def priorWrites (kind : FloorDamage.Kind) (s : X86Memory.State) (rng : DoomRandom) :=
  SectorDispatch.writes s ++ (FloorJoined.effectWrites s ++ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind s rng).core)

theorem command_byte (m : Memory) (a : Word) :
    (load32 m (a+4)).extractLsb' 24 8=m (a+7) := by
  unfold load32
  rw [BitVec.extractLsb'_append_eq_of_le (show 16 ≤ 24 by decide)]
  rw [BitVec.extractLsb'_append_eq_left]
  simp [BitVec.add_assoc]

theorem inputs_transport (s t : X86Memory.State) (b : BitVec 8) (w : Fin 3) (writes : List Word)
    (h : WeaponSelect.Inputs s b w) (edx : t.regs 2=s.regs 2) (ebx : t.regs 3=s.regs 3)
    (frame : PlayerHeight.Frame s.memory t.memory writes)
    (safe : ∀ a, a ∈ reads s w → ∀ v, v ∈ writes → Apart a v) :
    WeaponSelect.Inputs t b w := by
  refine ⟨?_,h.ordinary,h.selection,?_,?_⟩
  · have word := frame (s.regs 3+4) (safe _ (by simp [reads]))
    have byte := congrArg (fun v : Word => v.extractLsb' 24 8) word
    rw [command_byte,command_byte] at byte
    rw [ebx,byte,h.encoded]
  · rw [edx,frame _ (safe _ (by simp [reads])),h.noChainsaw]
  · rw [frame _ (safe _ (by simp [reads])),h.shareware]

/-- The selector contracts are derived from the initial state and the proved
preparation/floor memory frame, including a lethal floor hit on this same tic. -/
theorem joined_execution (kind : FloorDamage.Kind) (s : X86Memory.State) (f : Option Flags)
    (motion : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (view : ViewState) (time : Int32) (cached : Bool) (floor : Fixed) (tick : Nat) (suit : Bool)
    (sim : Simulation) (map : sim.map.name="E1M1")
    (h : FloorJoined.Inputs kind s motion anim cmd timer view time cached true floor tick suit sim.rng)
    (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (info : body.info=E1M1Death.playerInfo)
    (w : Fin 3) (y : Fixed)
    (contract : DamageTransport.Contract (E1M1FloorCycle.boundary kind s sim.rng).core v d
      (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim) body w y)
    (nonzero : FloorDamage.requested (E1M1FloorCycle.boundary kind s sim.rng)≠0)
    (readSafe : ∀ a, a ∈ DamageTransport.reads (E1M1FloorCycle.boundary kind s sim.rng).core w
      (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng → a≠0x12720 →
      ∀ b, b ∈ E1M1PreparedFloor.prefixWrites s → Apart a b)
    (savedSafe : ∀ a, a ∈ SectorCaller.slots s →
      ∀ b, b ∈ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind s sim.rng).core → Apart a b)
    (buttons : BitVec 8) (choice : Fin 3) (selection : WeaponSelect.Inputs s buttons choice)
    (selectionSafe : ∀ a, a ∈ reads s choice → ∀ v, v ∈ priorWrites kind s sim.rng → Apart a v) :
    ∃ before : X86Control.State,
      X86CodeMemory.run FloorCaller.cm E1M1PreparedFloor.program [0x333e5] 567 ⟨s,f,0x333b1⟩=some before ∧
      X86CodeMemory.run FloorCaller.cm program [0x33476] 591 ⟨s,f,0x333b1⟩=some (WeaponSelect.result before.core buttons choice) ∧
      before.core.regs 2=s.regs 2 ∧ before.core.regs 3=s.regs 3 ∧
      PlayerHeight.Frame s.memory before.core.memory (priorWrites kind s sim.rng) ∧
      (∀ c : Weapon.Context,
        (WeaponSelect.owns s choice != 0)=c.player.weapons[choice.val] →
        WeaponSelect.current s=BitVec.ofNat 32 c.player.readyWeapon.val →
        load32 s.memory (s.regs 2+116)=BitVec.ofNat 32 c.player.pendingWeapon.val →
        load32 (WeaponSelect.result before.core buttons choice).core.memory (s.regs 2+116)=
          BitVec.ofNat 32 (c.select (if buttons &&& (4#8)=(0#8) then none else some choice.val)).player.pendingWeapon.val) := by
  obtain ⟨p,extreme,t,prep,pc,run,death,tpc,tsp,si,dx,cx,bx,bp,di,fields,index,misc,off,obs,weapon,tics,height,frame⟩ :=
    E1M1PreparedFloor.joined_execution kind s f motion anim cmd timer view time cached floor tick suit sim map h
      v d body info w y contract nonzero readSafe savedSafe
  obtain ⟨q,qr,_,_,_,_,_,edx⟩ := PlayerPreparation.execution_preserved s f motion anim cmd timer view time cached true h.preparation
  have same : q=p := Option.some.inj (qr.symm.trans prep)
  subst q
  obtain ⟨q,qr,ebx⟩ := PlayerPreparation.execution_command s f motion anim cmd timer view time cached true h.preparation
  have same : q=p := Option.some.inj (qr.symm.trans prep)
  subst q
  have dx := dx.trans edx
  have bx := bx.trans ebx
  have inputs := inputs_transport s t.core buttons choice (priorWrites kind s sim.rng) selection dx bx frame selectionSafe
  refine ⟨t,run,append_selection _ t buttons choice run tpc inputs,dx,bx,frame,?_⟩
  intro c owned ready pending
  have keep (a : Word) (ha : a ∈ reads s choice) := frame a (selectionSafe a ha)
  have owns : WeaponSelect.owns t.core choice=WeaponSelect.owns s choice := by
    unfold WeaponSelect.owns; rw [dx,keep _ (by simp [reads])]
  have current : WeaponSelect.current t.core=WeaponSelect.current s := by
    unfold WeaponSelect.current; rw [dx,keep _ (by simp [reads])]
  have pending' : load32 t.core.memory (t.core.regs 2+116)=load32 s.memory (s.regs 2+116) := by
    rw [dx,keep _ (by simp [reads])]
  have answer := WeaponSelect.live_pending t.core buttons choice c (by rw [owns]; exact owned)
    (current.trans ready) (pending'.trans pending)
  simpa only [dx] using answer

end Doom.Proofs.E1M1PlayerSelection

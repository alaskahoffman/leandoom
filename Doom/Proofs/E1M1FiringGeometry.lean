import Doom.Proofs.E1M1AimGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1FiringGeometry
open Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMapFiring (Safe)
open E1M1PathMapQuery (withStack)

theorem flashed_player (gun : Fire.Gun) (s : X86Memory.State) :
    (E1M1DischargeSetters.flashed gun s).core.regs 1=s.regs 1 := by
  change (E1M1DischargeSetters.flashCall gun s).core.regs 1=_
  exact (E1M1DischargeSetters.flash_registers gun s).2.1

theorem flashed_frame (gun : Fire.Gun) (s : X86Memory.State) (a : Word) (h : Safe gun s a) :
    load32 (E1M1DischargeSetters.flashed gun s).core.memory a=load32 s.memory a :=
  (E1M1FlashInstall.memory_frame gun _ a h.flash).trans
    (E1M1DischargeSetters.before_flash_frame gun s a h.beforeFlash)

theorem aim_frame (gun : Fire.Gun) (s : X86Memory.State) (a : Word) (h : Safe gun s a) :
    load32 (E1M1DischargeSetters.aimCall gun s).core.memory a=load32 s.memory a := by
  change load32 (store32 (E1M1DischargeSetters.flashed gun s).core.memory
    ((E1M1DischargeSetters.flashed gun s).core.regs 4-(4#32)) _) a=_
  rw [E1M1PathMapFiring.flashed_stack,load_store_apart _ _ _ _ h.aim]
  exact flashed_frame gun s a h

theorem aim_actor (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (value : load32 s.memory (s.regs 1)=actor) (safe : Safe gun s (s.regs 1)) :
    (E1M1DischargeSetters.aimCall gun s).core.regs 0=actor := by
  change load32 (E1M1DischargeSetters.flashed gun s).core.memory
    ((E1M1DischargeSetters.flashed gun s).core.regs 1)=actor
  rw [flashed_player,flashed_frame gun s _ safe,value]

/-- The initial angle is read after P_BulletSlope saves its registers, before
its first query CALL. Both stages are connected to post-sound memory. -/
theorem first_request (gun : Fire.Gun) (s : X86Memory.State) (actor : Word) (angle : Angle)
    (pointer : load32 s.memory (s.regs 1)=actor) (pointerSafe : Safe gun s (s.regs 1))
    (value : load32 s.memory (actor+32)=angle.raw.toBitVec) (angleSafe : Safe gun s (actor+32)) :
    (E1M1BulletAim.firstQuery gun s).core.regs 0=actor ∧
    (E1M1BulletAim.firstQuery gun s).core.regs 2=angle.raw.toBitVec ∧
    (E1M1BulletAim.firstQuery gun s).core.regs 3=(Fixed.ofInt 1024).raw.toBitVec := by
  have actorEq := aim_actor gun s actor pointer pointerSafe
  have args := E1M1BulletAim.first_query_request gun s angle (by
    rw [actorEq,aim_frame gun s _ angleSafe,value]) (by
    rw [actorEq]
    intro b hb
    exact angleSafe.slope b (by simp [E1M1PathMapFiring.slopeWrites,hb]))
  exact ⟨args.1.trans actorEq,args.2⟩

def reads (s : X86Memory.State) (actor : Word) (angle : Angle) : List Word :=
  [s.regs 1,actor+12,actor+16,actor+20,actor+68,actor+32,0x13584,
   (angle.raw.toBitVec >>> 19 <<< 2)+0x7a84,(angle.raw.toBitVec >>> 19 <<< 2)+0x5a84,
   0x2c104,0x2c108]

/-- All values and write-separation premises are at the common post-sound
firing boundary. Later layout states specify only stack-derived addresses. -/
structure Inputs (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed) : Prop where
  pointer : load32 s.memory (s.regs 1)=actor
  angleValue : load32 s.memory (actor+32)=angle.raw.toBitVec
  x : load32 s.memory (actor+12)=thing.x.raw.toBitVec
  y : load32 s.memory (actor+16)=thing.y.raw.toBitVec
  z : load32 s.memory (actor+20)=thing.z.raw.toBitVec
  height : load32 s.memory (actor+68)=thing.height.raw.toBitVec
  cosinePointer : load32 s.memory 0x13584=0x7a84
  cosine : load32 s.memory ((angle.raw.toBitVec >>> 19 <<< 2)+0x7a84)=angle.fineCosine.raw.toBitVec
  sine : load32 s.memory ((angle.raw.toBitVec >>> 19 <<< 2)+0x5a84)=angle.fineSine.raw.toBitVec
  originX : load32 s.memory 0x2c104=ox.raw.toBitVec
  originY : load32 s.memory 0x2c108=oy.raw.toBitVec
  safe : ∀ a∈reads s actor angle, Safe gun s a
  aimLayout : OriginalAimSetup.Separated (withStack s (s.regs 4-(40#32)))
  flagSafe : ∀ b∈(OriginalPathInit.writes (withStack s (s.regs 4-(52#32)))).toList,
    Apart (s.regs 4-(48#32)) b
  pathLayout : OriginalPathInit.Separated (withStack s (s.regs 4-(52#32)))

theorem aim_layout (s q : X86Memory.State) (sp : q.regs 4=s.regs 4-(24#32))
    (h : OriginalAimSetup.Separated (withStack s (s.regs 4-(40#32)))) :
    OriginalAimSetup.Separated (withStack q (q.regs 4-(16#32))) := by
  have stack : (withStack q (q.regs 4-(16#32))).regs 4=
      (withStack s (s.regs 4-(40#32))).regs 4 := by
    change q.regs 4-(16#32)=s.regs 4-(40#32)
    rw [sp]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have eq : OriginalAimSetup.writes (withStack q (q.regs 4-(16#32)))=
      OriginalAimSetup.writes (withStack s (s.regs 4-(40#32))) := by
    simp only [OriginalAimSetup.writes,stack]
  unfold OriginalAimSetup.Separated
  rw [eq]
  exact h

theorem path_writes (s q : X86Memory.State) (sp : q.regs 4=s.regs 4-(24#32)) :
    OriginalPathInit.writes (withStack q (q.regs 4-(28#32)))=
    OriginalPathInit.writes (withStack s (s.regs 4-(52#32))) := by
  have stack : (withStack q (q.regs 4-(28#32))).regs 4=
      (withStack s (s.regs 4-(52#32))).regs 4 := by
    change q.regs 4-(28#32)=s.regs 4-(52#32)
    rw [sp]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  simp only [OriginalPathInit.writes,stack]

theorem flag_layout (s q : X86Memory.State) (sp : q.regs 4=s.regs 4-(24#32))
    (h : ∀ b∈(OriginalPathInit.writes (withStack s (s.regs 4-(52#32)))).toList,
      Apart (s.regs 4-(48#32)) b) :
    ∀ b∈(OriginalPathInit.writes (withStack q (q.regs 4-(28#32)))).toList,
      Apart (q.regs 4-(24#32)) b := by
  rw [path_writes s q sp,sp]
  simpa only [BitVec.sub_sub,show (24#32)+(24#32)=(48#32) by decide] using h

theorem path_layout (s q : X86Memory.State) (sp : q.regs 4=s.regs 4-(24#32))
    (h : OriginalPathInit.Separated (withStack s (s.regs 4-(52#32)))) :
    OriginalPathInit.Separated (withStack q (q.regs 4-(28#32))) := by
  unfold OriginalPathInit.Separated
  rw [path_writes s q sp]
  exact h

/-- Assemble query geometry from read preservation and register facts, without
unfolding a particular executed-state expression at every field. -/
theorem transport (gun : Fire.Gun) (s q : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (h : Inputs gun s actor thing angle ox oy)
    (args : q.regs 0=actor ∧ q.regs 2=angle.raw.toBitVec ∧ q.regs 3=(Fixed.ofInt 1024).raw.toBitVec)
    (keep : ∀ a∈reads s actor angle, load32 q.memory a=load32 s.memory a)
    (later : ∀ a∈reads s actor angle, E1M1PathMapQuery.Safe q a)
    (sp : q.regs 4=s.regs 4-(24#32)) :
    E1M1AimGeometry.Inputs q thing angle (Fixed.ofInt 1024) ox oy := by
  refine ⟨⟨args.2.1,args.2.2,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,
    later _ (by simp [reads]),later _ (by simp [reads]),?_,?_,?_⟩
  · exact (keep _ (by simp [reads])).trans h.cosinePointer
  · exact (keep _ (by simp [reads])).trans h.cosine
  · exact (keep _ (by simp [reads])).trans h.sine
  · intro a ha
    have member : a∈reads s actor angle := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl <;> simp [reads]
    exact (later a member).saves
  · rw [args.1,keep _ (by simp [reads]),h.x]
  · rw [args.1,keep _ (by simp [reads]),h.y]
  · rw [args.1,keep _ (by simp [reads]),h.z]
  · rw [args.1,keep _ (by simp [reads]),h.height]
  · intro a ha
    apply later
    simp only [OriginalAimSetup.actorReads,args.1,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> simp [reads]
  · exact (keep _ (by simp [reads])).trans h.originX
  · exact (keep _ (by simp [reads])).trans h.originY
  · exact aim_layout s _ sp h.aimLayout
  · exact flag_layout s _ sp h.flagSafe
  · exact path_layout s _ sp h.pathLayout

theorem query_geometry (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (h : Inputs gun s actor thing angle ox oy) :
    E1M1AimGeometry.Inputs (E1M1BulletAim.firstQuery gun s).core thing angle (Fixed.ofInt 1024) ox oy :=
  transport gun s _ actor thing angle ox oy h
    (first_request gun s actor angle h.pointer (h.safe _ (by simp [reads]))
      h.angleValue (h.safe _ (by simp [reads])))
    (fun a ha => E1M1PathMapFiring.query_frame gun s a (h.safe a ha))
    (fun a ha => E1M1PathMapFiring.query_safe gun s a (h.safe a ha))
    (E1M1PathMapFiring.query_stack gun s)

theorem first_path_correspondence (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (weapon : Weapon.Context) (input : E1M1DischargeSetters.Inputs gun s weapon)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : Inputs gun s actor thing angle ox oy) :
    ∃ n, n≤223 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PathInit.program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (E1M1PathInit.firstPath gun s) ∧
    OriginalPathInit.Ready (E1M1AimSetup.firstTraversal gun s).core (E1M1PathInit.firstPath gun s)
      (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1
        (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) :=
  E1M1PathInit.first_path_correspondence gun s f weapon input ox oy _ _ _ _
    (E1M1AimGeometry.path_inputs _ thing angle _ ox oy (query_geometry gun s actor thing angle ox oy geometry))
theorem first_scan_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (weapon : Weapon.Context) (input : E1M1DischargeSetters.Inputs gun s weapon)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : Inputs gun s actor thing angle ox oy)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).yStep=.ok yout)
    (base lines : Word) (words : Array Nat) (c : E1M1PathMap.Cell) (w h : Nat)
    (map : E1M1PathMapFiring.MapInputs gun s base lines words w h)
    (cursorSafe : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x2c028#32))
    (inside : Collision.pathCellInside (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).startBlockX
      (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).startBlockY w h=true)
    (valid : c.Valid words)
    (selected : words[4+Collision.pathCellIndex (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).startBlockX
      (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1 (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).startBlockY w]?=some c.offset) :
    (∃ n≤368, X86CodeMemory.Prefix FloorCaller.cm E1M1PathMapCaller.firingProgram [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core)) ∧
    E1M1PathMapLookup.ScanWords (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core).core lines c ∧
    OriginalLineCollection.Tracks (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core).core
      0x2ba20 (E1M1PathMap.resolve lines) #[] c.ids.length :=
  E1M1AimGeometry.first_scan_execution gun s f weapon input thing angle ox oy
    (query_geometry gun s actor thing angle ox oy geometry) xout yout okX okY
    base lines words c w h map cursorSafe inside valid selected
end Doom.Proofs.E1M1FiringGeometry

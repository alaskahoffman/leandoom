import Doom.Proofs.OriginalPlayerJoined

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6400000
namespace Doom.Proofs
open Verification X86 X86Memory X86Control BlockSummary
namespace PlayerFunction

theorem write_shadow (rs : Registers) (i : Reg) (a b : Word) :
    write (write rs i a) i b = write rs i b := by
  funext j; by_cases h : j = i <;> simp [write,h]

def prologueBytes : List UInt8 := [0x53,0x51,0x52,0x56,0x57,0x55,0x83,0xec,0x04]
def epilogueBytes : List UInt8 := [0x83,0xc4,0x04,0x5d,0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def functionBytes := prologueBytes ++ PlayerJoined.callerBytes ++ epilogueBytes

def bytesProgram (code callee : List UInt8) : X86Routine.Program := fun pc =>
  if 0x33160 ≤ pc ∧ pc < 0x33160+code.length then X86Routine.decodeAt code (pc-0x33160)
  else if 0x30ea0 ≤ pc ∧ pc < 0x30ea0+callee.length then X86Routine.decodeAt callee (pc-0x30ea0) else none

def program := bytesProgram functionBytes Doom19.setMobjStateBytes

def saved (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 (store32 (store32 s.memory
    (s.regs 4-(4#32)) (s.regs 3)) (s.regs 4-(8#32)) (s.regs 1))
    (s.regs 4-(12#32)) (s.regs 2)) (s.regs 4-(16#32)) (s.regs 6))
    (s.regs 4-(20#32)) (s.regs 7)) (s.regs 4-(24#32)) (s.regs 5)

/-- Entry data with the future scratch address, before any stack writes. -/
def frameView (s : X86Memory.State) : X86Memory.State := put s 4 (s.regs 4-(28#32))
def enter (s : X86Memory.State) : X86Memory.State := {frameView s with memory := saved s}

theorem prologue (s : X86Memory.State) (flags : Option Flags) (ret : Nat) (hr : 0x33268 ≤ ret) :
    X86Routine.Prefix program [ret] 7 ⟨s,flags,0x33160⟩ ⟨enter s,none,0x33169⟩ := by
  have d0 : program 0x33160 = some (.push 3,1) := by decide
  have d1 : program 0x33161 = some (.push 1,1) := by decide
  have d2 : program 0x33162 = some (.push 2,1) := by decide
  have d3 : program 0x33163 = some (.push 6,1) := by decide
  have d4 : program 0x33164 = some (.push 7,1) := by decide
  have d5 : program 0x33165 = some (.push 5,1) := by decide
  have d6 : program 0x33166 = some (.addImmediate 4 (-4),3) := by decide
  apply X86Routine.Prefix.step (by simp; omega) d0 (by rfl)
  apply X86Routine.Prefix.step (by simp; omega) d1 (by rfl)
  apply X86Routine.Prefix.step (by simp; omega) d2 (by rfl)
  apply X86Routine.Prefix.step (by simp; omega) d3 (by rfl)
  apply X86Routine.Prefix.step (by simp; omega) d4 (by rfl)
  apply X86Routine.Prefix.step (by simp; omega) d5 (by rfl)
  apply X86Routine.Prefix.step (by simp; omega) d6 (by rfl)
  simpa [enter,frameView,saved,X86Routine.pushWord,put,write,BitVec.sub_sub,
    BitVec.sub_eq_add_neg,BitVec.add_assoc,write_shadow] using
    (X86Routine.Prefix.nil (program := program) (exits := [ret]) ⟨enter s,none,0x33169⟩)

theorem contains_joined (pc : Nat) (h : PlayerJoined.program pc ≠ none) :
    program pc = PlayerJoined.program pc := by
  unfold PlayerJoined.program PlayerJoined.bytesProgram at h ⊢
  split at h
  next hp =>
    unfold program bytesProgram
    rw [if_pos (show 0x33160 ≤ pc ∧ pc < 0x33160+functionBytes.length by
      change 0x33169 ≤ pc ∧ pc < 0x33169+245 at hp
      change _ ∧ _ < 0x33160+264; omega),if_pos hp]
    have check : ∀ i : Fin 245, (X86Routine.decodeAt PlayerJoined.callerBytes i.val).isSome →
      X86Routine.decodeAt functionBytes (9+i.val) = X86Routine.decodeAt PlayerJoined.callerBytes i.val := by decide
    have bound : pc-0x33169 < 245 := by change _ ∧ _ < 0x33169+245 at hp; omega
    have hc := check ⟨pc-0x33169,bound⟩ (by cases he : X86Routine.decodeAt PlayerJoined.callerBytes (pc-0x33169) <;> simp_all)
    rw [show pc-0x33160 = 9+(pc-0x33169) by omega]
    exact hc
  next hp =>
    split at h
    next hc =>
      unfold program bytesProgram
      rw [if_neg (by change 0x30ea0 ≤ pc ∧ pc < 0x30ea0+91 at hc; omega),if_pos hc,if_neg hp]
    next hc => simp_all

theorem joined_active (pc ret : Nat) (hr : 0x33268 ≤ ret) (h : PlayerJoined.program pc ≠ none) :
    pc ∉ [ret] := by
  unfold PlayerJoined.program PlayerJoined.bytesProgram at h
  split at h
  next hp => change _ ∧ pc < 0x33169+245 at hp; simp only [List.mem_singleton]; omega
  next hp => split at h
             next hc => change 0x30ea0 ≤ pc ∧ pc < 0x30ea0+91 at hc; simp only [List.mem_singleton]; omega
             next hc => simp_all

/-- Exact pop order, retaining the memory produced by the body. -/
def leave (t : X86Control.State) : X86Control.State :=
  let sp := t.core.regs 4
  let m := t.core.memory
  ⟨⟨write (write (write (write (write (write (write t.core.regs
    5 (load32 m (sp+(4#32)))) 7 (load32 m (sp+(8#32))))
    6 (load32 m (sp+(12#32)))) 2 (load32 m (sp+(16#32))))
    1 (load32 m (sp+(20#32)))) 3 (load32 m (sp+(24#32)))) 4 (sp+(32#32)),m⟩,
    none,(load32 m (sp+(28#32))).toNat⟩

theorem epilogue (t : X86Control.State) (ret : Nat) (hr : 0x33268 ≤ ret)
    (hp : t.pc = 0x3325e) (returnAddress : (load32 t.core.memory (t.core.regs 4+(28#32))).toNat = ret) :
    X86Routine.run program [ret] 8 t = some (leave t) := by
  rcases t with ⟨s,f,pc⟩; dsimp at hp; subst pc
  have h0 : (0x3325e:Nat) ∉ [ret] := by simp; omega
  have h1 : (0x33261:Nat) ∉ [ret] := by simp; omega
  have h2 : (0x33262:Nat) ∉ [ret] := by simp; omega
  have h3 : (0x33263:Nat) ∉ [ret] := by simp; omega
  have h4 : (0x33264:Nat) ∉ [ret] := by simp; omega
  have h5 : (0x33265:Nat) ∉ [ret] := by simp; omega
  have h6 : (0x33266:Nat) ∉ [ret] := by simp; omega
  have h7 : (0x33267:Nat) ∉ [ret] := by simp; omega
  have d0 : program 0x3325e = some (.addImmediate 4 4,3) := rfl
  have d1 : program 0x33261 = some (.pop 5,1) := rfl
  have d2 : program 0x33262 = some (.pop 7,1) := rfl
  have d3 : program 0x33263 = some (.pop 6,1) := rfl
  have d4 : program 0x33264 = some (.pop 2,1) := rfl
  have d5 : program 0x33265 = some (.pop 1,1) := rfl
  have d6 : program 0x33266 = some (.pop 3,1) := rfl
  have d7 : program 0x33267 = some (.ret,1) := rfl
  simp only [X86Routine.run,h0,h1,h2,h3,h4,h5,h6,h7,↓reduceIte,d0,d1,d2,d3,d4,d5,d6,d7,
    X86Routine.execute,Bind.bind,Option.bind,put,write,↓reduceIte,BitVec.add_assoc] at *
  simp_all [leave,put,write,BitVec.add_assoc]
  funext r
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by
    have hb := r.isLt
    simp only [Fin.ext_iff]; omega
  rcases cases with h|h|h|h|h|h|h|h <;> subst r <;> rfl

/-- Read footprint of the initial relation; stack preservation is bytewise. -/
def Reads (s : X86Memory.State) (a : Word) : Prop :=
  a ∈ [s.regs 0,s.regs 0+(8#32),s.regs 0+(9#32),s.regs 0+(10#32),
    entryObject s+(20#32),entryObject s+(32#32),entryObject s+(56#32),
    entryObject s+(72#32),entryObject s+(76#32),entryObject s+(96#32),entryObject s+(100#32),0x13584] ∨
  a ∈ PlayerAnimation.tableWords ∨ ∃ i : Fin 10240, a = 0x5a84 + BitVec.ofNat 32 (i.val*4)

theorem transport_inputs (s : X86Memory.State) (m : Memory) (body : Motion)
    (anim : PlayerAnim.State) (cmd : Ticcmd) (h : PlayerJoined.Inputs s body anim cmd)
    (keep : ∀ a, Reads s a → load32 m a = load32 s.memory a) :
    PlayerJoined.Inputs {s with memory := m} body anim cmd := by
  have byteKeep (a : Word) (ha : Reads s a) : m a = s.memory a := by
    have eq := congrArg (fun v : Word => v.extractLsb' 0 8) (keep a ha)
    have low (a b c d : BitVec 8) : ((d ++ c) ++ (b ++ a)).extractLsb' 0 8 = a := by bv_decide
    simpa only [load32,low] using eq
  have halfKeep (a : Word) (ha : Reads s a) : load16 m a = load16 s.memory a := by
    have eq := congrArg (fun v : Word => v.extractLsb' 0 16) (keep a ha)
    have low (a b c d : BitVec 8) : ((d ++ c) ++ (b ++ a)).extractLsb' 0 16 = b ++ a := by bv_decide
    simpa only [load32,load16,low] using eq
  have hp := keep (s.regs 0) (by simp [Reads])
  have tables : ThrustTables m := by
    constructor
    · rw [keep _ (by simp [Reads])]; exact h.tables.cosinePointer
    · intro i; rw [keep _ (by exact Or.inr (Or.inr ⟨i,rfl⟩))]; exact h.tables.entries i
  have animationTable : PlayerAnimation.RunTable m := by
    constructor
    all_goals rw [keep _ (by simp [Reads,PlayerAnimation.tableWords])]
    · exact h.animationTable.sprite
    · exact h.animationTable.frame
    · exact h.animationTable.tics
    · exact h.animationTable.action
    · exact h.animationTable.next
  refine {
    tables := tables
    animationTable := animationTable
    angle := ?_,
    turn := ?_,
    forward := ?_,
    height := ?_,
    floor := ?_,
    playerApart := ?_,
    heightApart := ?_,
    floorApart := ?_,
    commandsApart := ?_,
    groundApartAngle := ?_,
    momx := ?_,
    momy := ?_,
    side := ?_,
    angleScratch := ?_,
    angleMomx := ?_,
    angleMomy := ?_,
    readsProtected := ?_,
    tableProtected := ?_,
    scratchProtected := ?_,
    tableScratch := ?_,
    tableMomx := ?_,
    momxProtected := ?_,
    momyProtected := ?_,
    playerMomy := ?_,
    pointerMomx := ?_,
    pointerMomy := ?_,
    tableMomy := ?_,
    animationFrame := ?_,
    frameBound := ?_,
    animationTics := ?_,
    readsSafe := ?_,
    animationTableSafe := ?_,
    stackSafe := ?_,
    motionSafe := ?_ }
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.angle
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.turn
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.forward
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.height
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.floor
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.playerApart
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.heightApart
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.floorApart
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.commandsApart
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.groundApartAngle
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.momx
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.momy
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.side
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.angleScratch
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.angleMomx
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.angleMomy
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.readsProtected
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.tableProtected
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.scratchProtected
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.tableScratch
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.tableMomx
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.momxProtected
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.momyProtected
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.playerMomy
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.pointerMomx
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.pointerMomy
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.tableMomy
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.animationFrame
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.frameBound
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.animationTics
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.readsSafe
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.animationTableSafe
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.stackSafe
  · simpa (disch := simp [Reads,entryObject]) only [entryObject,entryAngleAddress,PlayerJoined.animationReads,
      PlayerJoined.animationWrites,PlayerJoined.motionWrites,keep,byteKeep,halfKeep,eax] using h.motionSafe

def savedSlots (s : X86Memory.State) : List Word :=
  [s.regs 4,s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),
   s.regs 4-(16#32),s.regs 4-(20#32),s.regs 4-(24#32)]

def pushSlots (s : X86Memory.State) : List Word := (savedSlots s).tail

/-- All facts concern function-entry data and layout. The virtual frame view
changes only the address used for scratch/stack separation, not memory. -/
structure Inputs (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) : Prop
    extends PlayerJoined.Inputs (frameView s) body anim cmd where
  pushesSafe : ∀ a, Reads (frameView s) a → ∀ b, b ∈ pushSlots s → Apart a b
  savedSafe : ∀ a, a ∈ savedSlots s → ∀ b,
    b ∈ PlayerJoined.motionWrites (frameView s) ++ PlayerJoined.animationWrites (frameView s) → Apart a b
  returnOutside : 0x33268 ≤ (load32 s.memory (s.regs 4)).toNat

theorem saved_load (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ pushSlots s → Apart a b) : load32 (saved s) a = load32 s.memory a := by
  unfold saved
  rw [load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots])),
      load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots])),
      load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots])),
      load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots])),
      load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots])),
      load_store_apart _ _ _ _ (safe _ (by simp [pushSlots,savedSlots]))]

theorem establishes_body (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : PlayerJoined.Inputs (enter s) body anim cmd :=
  transport_inputs (frameView s) (saved s) body anim cmd h.toInputs
    (fun a ha => saved_load s a (h.pushesSafe a ha))

theorem enter_object (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : entryObject (enter s) = entryObject (frameView s) := by
  change load32 (saved s) ((frameView s).regs 0) = _
  exact saved_load s _ (h.pushesSafe _ (by simp [Reads]))

def bodyEnd (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) : X86Control.State :=
  PlayerAnimation.result (motionEnd (enter s) body cmd).core

theorem body_stack (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : (bodyEnd s body cmd).core.regs 4 = s.regs 4-(28#32) := by
  have fields := PlayerAnimation.result_fields _ anim cmd
    (PlayerJoined.establishes_animation _ body anim cmd (establishes_body s body anim cmd h))
  have eq := congrArg (fun x => x.2.2) fields
  rw [(motion_end_pointers (enter s) body cmd).2.2] at eq
  simpa only [bodyEnd,enter,frameView,put,write,↓reduceIte] using eq

theorem body_pc (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : (bodyEnd s body cmd).pc = 0x3325e := by
  obtain ⟨_,_,_,done⟩ := X86Routine.run_path
    (PlayerJoined.joined_execution (enter s) none body anim cmd (establishes_body s body anim cmd h))
  simpa only [List.mem_singleton,bodyEnd] using done

theorem body_saved_load (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) (a : Word) (ha : a ∈ savedSlots s) :
    load32 (bodyEnd s body cmd).core.memory a = load32 (saved s) a := by
  have hi := establishes_body s body anim cmd h
  have obj := enter_object s body anim cmd h
  have sameMotion : PlayerJoined.motionWrites (enter s) = PlayerJoined.motionWrites (frameView s) := by
    simp only [PlayerJoined.motionWrites,entryAngleAddress,obj]; rfl
  have sameAnimation : PlayerJoined.animationWrites (enter s) = PlayerJoined.animationWrites (frameView s) := by
    simp only [PlayerJoined.animationWrites,obj]; rfl
  unfold bodyEnd
  rw [PlayerJoined.animation_load _ a (by
    intro b hb
    rw [PlayerJoined.end_object _ body anim cmd hi,(motion_end_pointers (enter s) body cmd).2.2] at hb
    change b ∈ PlayerJoined.animationWrites (enter s) at hb
    rw [sameAnimation] at hb
    exact h.savedSafe a ha b (List.mem_append_right _ hb))]
  rw [(motion_end_memory_pc (enter s) none body cmd hi.toMoveMotionInputs).2]
  exact PlayerJoined.motion_load (enter s) body cmd hi.toMoveMotionInputs a (by
    intro b hb; rw [sameMotion] at hb
    exact h.savedSafe a ha b (List.mem_append_left _ hb))

/-- Distinct aligned word slots remain disjoint even across 32-bit wraparound. -/
theorem slots_apart (sp : Word) (i j : Fin 11) (hne : i ≠ j) :
    Apart (sp-BitVec.ofNat 32 (i.val*4)) (sp-BitVec.ofNat 32 (j.val*4)) := by
  have checked : ∀ i j : Fin 11, i ≠ j →
      Apart (-BitVec.ofNat 32 (i.val*4)) (-BitVec.ofNat 32 (j.val*4)) := by unfold Apart; decide
  intro a b eq
  apply checked i j hne a b
  apply (BitVec.add_right_inj sp).mp
  simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc] using eq

theorem saved_return (s : X86Memory.State) : load32 (saved s) (s.regs 4) = load32 s.memory (s.regs 4) := by
  apply saved_load
  intro b hb
  simp only [pushSlots,savedSlots,List.tail_cons,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h|h|h|h|h|h <;> subst b
  · have h := slots_apart (s.regs 4) 0 1 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(4#32)) at h
    simpa only [BitVec.sub_zero] using h
  · have h := slots_apart (s.regs 4) 0 2 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(8#32)) at h
    simpa only [BitVec.sub_zero] using h
  · have h := slots_apart (s.regs 4) 0 3 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(12#32)) at h
    simpa only [BitVec.sub_zero] using h
  · have h := slots_apart (s.regs 4) 0 4 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(16#32)) at h
    simpa only [BitVec.sub_zero] using h
  · have h := slots_apart (s.regs 4) 0 5 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(20#32)) at h
    simpa only [BitVec.sub_zero] using h
  · have h := slots_apart (s.regs 4) 0 6 (by decide)
    change Apart (s.regs 4-(0#32)) (s.regs 4-(24#32)) at h
    simpa only [BitVec.sub_zero] using h

def result (s : X86Memory.State) (body : Motion) (cmd : Ticcmd) := leave (bodyEnd s body cmd)

/-- Entire original P_MovePlayer, from its first PUSH through its final RET.
One function-entry relation; no intermediate state is assumed or reset. -/
theorem execution (s : X86Memory.State) (flags : Option Flags) (body : Motion)
    (anim : PlayerAnim.State) (cmd : Ticcmd) (h : Inputs s body anim cmd) :
    X86Routine.run program [(load32 s.memory (s.regs 4)).toNat] 117 ⟨s,flags,0x33160⟩ =
      some (result s body cmd) := by
  have hi := establishes_body s body anim cmd h
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path (PlayerJoined.joined_execution (enter s) none body anim cmd hi)
  have path := path.transfer program [(load32 s.memory (s.regs 4)).toNat]
    contains_joined (fun pc hp => joined_active pc _ h.returnOutside hp)
  have tail := epilogue (bodyEnd s body cmd) _ h.returnOutside (body_pc s body anim cmd h) (by
    rw [body_stack s body anim cmd h,BitVec.sub_add_cancel,
      body_saved_load s body anim cmd h _ (by simp [savedSlots]),saved_return])
  have middle := path.finish tail 110 (by omega)
  exact (prologue s flags _ h.returnOutside).finish middle 117 (by omega)

theorem saved_registers (s : X86Memory.State) :
    (load32 (saved s) (s.regs 4-(4#32)),load32 (saved s) (s.regs 4-(8#32)),
     load32 (saved s) (s.regs 4-(12#32)),load32 (saved s) (s.regs 4-(16#32)),
     load32 (saved s) (s.regs 4-(20#32)),load32 (saved s) (s.regs 4-(24#32))) =
    (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5) := by
  have k12 : Apart (s.regs 4-(4#32)) (s.regs 4-(8#32)) := slots_apart (s.regs 4) 1 2 (by decide)
  have k13 : Apart (s.regs 4-(4#32)) (s.regs 4-(12#32)) := slots_apart (s.regs 4) 1 3 (by decide)
  have k14 : Apart (s.regs 4-(4#32)) (s.regs 4-(16#32)) := slots_apart (s.regs 4) 1 4 (by decide)
  have k15 : Apart (s.regs 4-(4#32)) (s.regs 4-(20#32)) := slots_apart (s.regs 4) 1 5 (by decide)
  have k16 : Apart (s.regs 4-(4#32)) (s.regs 4-(24#32)) := slots_apart (s.regs 4) 1 6 (by decide)
  have k23 : Apart (s.regs 4-(8#32)) (s.regs 4-(12#32)) := slots_apart (s.regs 4) 2 3 (by decide)
  have k24 : Apart (s.regs 4-(8#32)) (s.regs 4-(16#32)) := slots_apart (s.regs 4) 2 4 (by decide)
  have k25 : Apart (s.regs 4-(8#32)) (s.regs 4-(20#32)) := slots_apart (s.regs 4) 2 5 (by decide)
  have k26 : Apart (s.regs 4-(8#32)) (s.regs 4-(24#32)) := slots_apart (s.regs 4) 2 6 (by decide)
  have k34 : Apart (s.regs 4-(12#32)) (s.regs 4-(16#32)) := slots_apart (s.regs 4) 3 4 (by decide)
  have k35 : Apart (s.regs 4-(12#32)) (s.regs 4-(20#32)) := slots_apart (s.regs 4) 3 5 (by decide)
  have k36 : Apart (s.regs 4-(12#32)) (s.regs 4-(24#32)) := slots_apart (s.regs 4) 3 6 (by decide)
  have k45 : Apart (s.regs 4-(16#32)) (s.regs 4-(20#32)) := slots_apart (s.regs 4) 4 5 (by decide)
  have k46 : Apart (s.regs 4-(16#32)) (s.regs 4-(24#32)) := slots_apart (s.regs 4) 4 6 (by decide)
  have k56 : Apart (s.regs 4-(20#32)) (s.regs 4-(24#32)) := slots_apart (s.regs 4) 5 6 (by decide)
  simp only [saved,load_store,
    load_store_apart _ _ _ _ k12,
    load_store_apart _ _ _ _ k13,
    load_store_apart _ _ _ _ k14,
    load_store_apart _ _ _ _ k15,
    load_store_apart _ _ _ _ k16,
    load_store_apart _ _ _ _ k23,
    load_store_apart _ _ _ _ k24,
    load_store_apart _ _ _ _ k25,
    load_store_apart _ _ _ _ k26,
    load_store_apart _ _ _ _ k34,
    load_store_apart _ _ _ _ k35,
    load_store_apart _ _ _ _ k36,
    load_store_apart _ _ _ _ k45,
    load_store_apart _ _ _ _ k46,
    load_store_apart _ _ _ _ k56]

def preservedRegisters (s : X86Memory.State) :=
  (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5,s.regs 4)

theorem result_registers (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : preservedRegisters (result s body cmd).core =
      (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5,s.regs 4+(4#32)) := by
  have addback (sp : Word) :
      sp-(28#32)+(4#32) = sp-(24#32) ∧ sp-(28#32)+(8#32) = sp-(20#32) ∧
      sp-(28#32)+(12#32) = sp-(16#32) ∧ sp-(28#32)+(16#32) = sp-(12#32) ∧
      sp-(28#32)+(20#32) = sp-(8#32) ∧ sp-(28#32)+(24#32) = sp-(4#32) ∧
      sp-(28#32)+(32#32) = sp+(4#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have ha := addback (s.regs 4)
  simp only [preservedRegisters,result,leave,write,↓reduceIte,body_stack s body anim cmd h,
    ha.1,ha.2.1,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1,ha.2.2.2.2.2.1,ha.2.2.2.2.2.2]
  rw [body_saved_load s body anim cmd h _ (by simp [savedSlots]),
      body_saved_load s body anim cmd h _ (by simp [savedSlots]),
      body_saved_load s body anim cmd h _ (by simp [savedSlots]),
      body_saved_load s body anim cmd h _ (by simp [savedSlots]),
      body_saved_load s body anim cmd h _ (by simp [savedSlots]),
      body_saved_load s body anim cmd h _ (by simp [savedSlots])]
  have eq := saved_registers s
  simp only [Prod.mk.injEq] at eq ⊢
  exact ⟨eq.1,eq.2.1,eq.2.2.1,eq.2.2.2.1,eq.2.2.2.2.1,eq.2.2.2.2.2,True.intro⟩

theorem result_return (s : X86Memory.State) (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd)
    (h : Inputs s body anim cmd) : (result s body cmd).pc = (load32 s.memory (s.regs 4)).toNat := by
  change (load32 (bodyEnd s body cmd).core.memory ((bodyEnd s body cmd).core.regs 4+(28#32))).toNat = _
  rw [body_stack s body anim cmd h,BitVec.sub_add_cancel,
    body_saved_load s body anim cmd h _ (by simp [savedSlots]),saved_return]

/-- Runtime fields, the actual return address, and all six saved registers plus
ESP after RET, from the function-entry relation. EAX is intentionally a clobber. -/
theorem observation (s : X86Memory.State) (flags : Option Flags) (body : Motion)
    (anim : PlayerAnim.State) (cmd : Ticcmd) (h : Inputs s body anim cmd) :
    (X86Routine.run program [(load32 s.memory (s.regs 4)).toNat] 117 ⟨s,flags,0x33160⟩).map (fun t =>
      (t.pc,(load32 t.core.memory (entryAngleAddress s),load32 t.core.memory (entryObject s+(72#32)),
        load32 t.core.memory (entryObject s+(76#32))),
        load32 t.core.memory (entryObject s+(100#32)),load32 t.core.memory (entryObject s+(96#32)),
        preservedRegisters t.core)) =
      some ((load32 s.memory (s.regs 4)).toNat,
        ((body.movePlayer cmd).angle.raw.toBitVec,(body.movePlayer cmd).momx.raw.toBitVec,
         (body.movePlayer cmd).momy.raw.toBitVec),PlayerAnimation.statePointer (anim.startWalking cmd).frame,
        (anim.startWalking cmd).tics.toBitVec,
        (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5,s.regs 4+(4#32))) := by
  rw [execution s flags body anim cmd h]
  simp only [Option.map_some,result_return s body anim cmd h,result_registers s body anim cmd h]
  have hi := establishes_body s body anim cmd h
  have obj : entryObject (enter s) = entryObject s := by
    simpa [frameView,entryObject,put,write,eax] using enter_object s body anim cmd h
  have fields := PlayerAnimation.result_fields _ anim cmd (PlayerJoined.establishes_animation _ body anim cmd hi)
  rw [PlayerJoined.end_object _ body anim cmd hi,obj] at fields
  have motion := PlayerJoined.final_motion_fields (enter s) none body anim cmd hi
  simp only [entryAngleAddress,obj] at motion
  change some (_,_,_,_,_) = _
  simp only [Prod.mk.injEq] at fields
  simp only [result,leave,bodyEnd,entryAngleAddress,motion,fields.1,fields.2.1]

end PlayerFunction
end Doom.Proofs

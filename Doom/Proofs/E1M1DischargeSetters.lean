import Doom.Proofs.OriginalWeaponDischarge
import Doom.Proofs.OriginalActorSetterReturn
import Doom.Proofs.E1M1FlashInstall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1DischargeSetters
open Verification X86 X86Memory X86Control BlockSummary

def actorEntry : DeathSetter.Entry := ⟨155,28,0x8005,6,154,by decide,by decide⟩
def poseBytes : List UInt8 := [28,0,0,0,5,128,0,0,6,0,0,0,0,0,0,0,154,0,0,0,0,0,0,0,0,0,0,0]
theorem pose_table : DeathSetter.Table actorEntry (fun a =>
    if 0x16b1c ≤ a.toNat ∧ a.toNat < 0x16b38 then poseBytes.toArray[a.toNat-0x16b1c]!.toBitVec else 0) := by
  constructor <;> decide

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if (0x2d890 ≤ pc ∧ pc < 0x2d8ec) ∨ (0x2d910 ≤ pc ∧ pc < 0x2d96d) then OriginalWeaponDischarge.program pc
  else if 0x30ea0 ≤ pc ∧ pc < 0x30efb then DeathSetter.program pc
  else E1M1PspriteLight.program pc

theorem contains_discharge (pc : Nat) (h : OriginalWeaponDischarge.program pc≠none) : program pc=OriginalWeaponDischarge.program pc := by
  by_cases inside : (0x2d890 ≤ pc ∧ pc < 0x2d8ec) ∨ (0x2d910 ≤ pc ∧ pc < 0x2d96d)
  · simp [program,inside]
  · have a : ¬(0x2d890 ≤ pc ∧ pc < 0x2d8ec) := by omega
    have b : ¬(0x2d910 ≤ pc ∧ pc < 0x2d96d) := by omega
    exact False.elim (h (by simp [OriginalWeaponDischarge.program,OriginalWeaponDischarge.bytesProgram,a,b]))
theorem contains_actor (pc : Nat) (h : DeathSetter.program pc≠none) : program pc=DeathSetter.program pc := by
  have inside : 0x30ea0 ≤ pc ∧ pc < 0x30efb := by
    by_cases yes : 0x30ea0 ≤ pc ∧ pc < 0x30efb
    · exact yes
    · exact False.elim (h (by simp [DeathSetter.program,PainSetter.program,PainSetter.bytesProgram,yes]))
  have no : ¬((0x2d890 ≤ pc ∧ pc < 0x2d8ec) ∨ (0x2d910 ≤ pc ∧ pc < 0x2d96d)) := by omega
  simp [program,inside,no]
theorem contains_flash (pc : Nat) (h : E1M1PspriteLight.program pc≠none) : program pc=E1M1PspriteLight.program pc := by
  by_cases a : 0x2d890 ≤ pc ∧ pc < 0x2d8ec
  · have q : ∀ i : Fin 92, E1M1PspriteLight.program (0x2d890+i.val)=none := by decide
    have eq : 0x2d890+(pc-0x2d890)=pc := by omega
    exact False.elim (h (by simpa only [eq] using q ⟨pc-0x2d890,by omega⟩))
  by_cases b : 0x2d910 ≤ pc ∧ pc < 0x2d96d
  · have q : ∀ i : Fin 93, E1M1PspriteLight.program (0x2d910+i.val)=none := by decide
    have eq : 0x2d910+(pc-0x2d910)=pc := by omega
    exact False.elim (h (by simpa only [eq] using q ⟨pc-0x2d910,by omega⟩))
  by_cases c : 0x30ea0 ≤ pc ∧ pc < 0x30efb
  · have q : ∀ i : Fin 91, E1M1PspriteLight.program (0x30ea0+i.val)=none ∨
        E1M1PspriteLight.program (0x30ea0+i.val)=DeathSetter.program (0x30ea0+i.val) := by decide
    have eq : 0x30ea0+(pc-0x30ea0)=pc := by omega
    have checked := q ⟨pc-0x30ea0,by omega⟩
    simp only [eq] at checked
    rcases checked with no | yes
    · exact False.elim (h no)
    · simp [program,a,b,c,yes]
  simp [program,a,b,c]

def call (gun : Fire.Gun) (s : X86Memory.State) := OriginalWeaponDischarge.poseCall gun s none
def posed (gun : Fire.Gun) (s : X86Memory.State) :=
  ActorSetterReturn.result actorEntry (call gun s).core (BitVec.ofNat 32 (OriginalWeaponDischarge.afterPose gun))

theorem posed_pc (gun : Fire.Gun) (s : X86Memory.State) : (posed gun s).pc=OriginalWeaponDischarge.afterPose gun := by
  cases gun <;> rfl
theorem posed_registers (gun : Fire.Gun) (s : X86Memory.State) :
    (posed gun s).core.regs 1=s.regs 1 ∧ (posed gun s).core.regs 4=s.regs 4 := by
  simp [posed,call,OriginalWeaponDischarge.poseCall,ActorSetterReturn.result,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- The actual CALL, actor setter body and RET. Starts immediately after sound;
no correctness or preservation claim about that earlier sound call is assumed. -/
theorem pose_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (h : DeathSetter.SetterInputs actorEntry (call gun s).core (BitVec.ofNat 32 (OriginalWeaponDischarge.afterPose gun))) :
    ∃ n, n≤27 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (posed gun s) := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (OriginalWeaponDischarge.pose_execution gun s f)
  have a := (X86CodeMemory.lift_success (a.transfer OriginalWeaponDischarge.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_discharge (by simp)
  obtain ⟨m,hm,b⟩ := ActorSetterReturn.execution actorEntry (call gun s).core f (BitVec.ofNat 32 (OriginalWeaponDischarge.afterPose gun)) h
  have eq : (OriginalWeaponDischarge.poseCall gun s f)=⟨(call gun s).core,f,0x30ea0⟩ := rfl
  rw [←eq] at b
  have b := (X86CodeMemory.lift_success b FloorCaller.cm).transfer program [] contains_actor (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩

theorem live_pose (gun : Fire.Gun) (s : X86Memory.State) :
    DeathSetter.observeFields (posed gun s).core.memory ((call gun s).core.regs 0) =
      (BitVec.ofNat 32 (0x15a28+28*(PlayerAnim.enter 155).1.frame),
        (PlayerAnim.enter 155).1.tics.toBitVec,28,0x8005) := by
  simpa [posed,actorEntry,DeathSetter.Entry.pointer,PlayerAnim.enter] using
    ActorSetterReturn.fields actorEntry (call gun s).core (BitVec.ofNat 32 (OriginalWeaponDischarge.afterPose gun))

def poseWrites (gun : Fire.Gun) (s : X86Memory.State) :=
  [s.regs 4-4] ++ DeathSetter.writes (call gun s).core

theorem pose_frame (gun : Fire.Gun) (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ poseWrites gun s → Apart a b) :
    load32 (posed gun s).core.memory a=load32 s.memory a := by
  have keep := ActorSetterReturn.memory_frame actorEntry (call gun s).core
    (BitVec.ofNat 32 (OriginalWeaponDischarge.afterPose gun)) a (fun b hb => safe b (by simp [poseWrites,hb]))
  change load32 (posed gun s).core.memory a = load32 (call gun s).core.memory a at keep
  rw [keep]
  change load32 (store32 s.memory (s.regs 4-4) _) a = _
  exact load_store_apart _ _ _ _ (safe _ (by simp [poseWrites]))

def debitReads (gun : Fire.Gun) (s : X86Memory.State) : List Word :=
  [s.regs 1+112, OriginalWeaponDischarge.tableOffset (OriginalWeaponDischarge.weaponNumber gun)+0x12d90,
   OriginalWeaponDischarge.tableOffset (OriginalWeaponDischarge.weaponNumber gun)+0x12da4, OriginalWeaponDischarge.playerAmmo gun s]

/-- Transport the previous turn's input relation across the real actor setter,
using its write footprint instead of assuming related post-call ammo/tables. -/
theorem transport (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (h : OriginalWeaponDischarge.Inputs gun s c)
    (safe : ∀ a, a ∈ debitReads gun s → ∀ b, b ∈ poseWrites gun s → Apart a b) :
    OriginalWeaponDischarge.Inputs gun (posed gun s).core c := by
  have regs := posed_registers gun s
  have keep (a : Word) (ha : a ∈ debitReads gun s) := pose_frame gun s a (safe a ha)
  constructor
  · simp only [OriginalWeaponDischarge.weapon,regs.1]; rw [keep _ (by simp [debitReads])]; exact h.ready
  · rw [keep _ (by simp [debitReads])]; exact h.kind
  · rw [keep _ (by simp [debitReads])]; exact h.flash
  · change load32 (posed gun s).core.memory (OriginalWeaponDischarge.playerAmmo gun s) = _
    rw [keep _ (by simp [debitReads])]; exact h.ammo
  · simpa only [OriginalWeaponDischarge.playerAmmo,regs.1] using h.readySafe
  · simpa only [OriginalWeaponDischarge.playerAmmo,regs.1] using h.flashSafe
  · simpa only [OriginalWeaponDischarge.playerAmmo,regs.1,regs.2] using h.stackSafe

def flashCall (gun : Fire.Gun) (s : X86Memory.State) := OriginalWeaponDischarge.flashCall gun (posed gun s).core

theorem pose_debit_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (h : DeathSetter.SetterInputs actorEntry (call gun s).core (BitVec.ofNat 32 (OriginalWeaponDischarge.afterPose gun))) :
    ∃ n, n≤39 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (flashCall gun s) := by
  obtain ⟨n,hn,a⟩ := pose_execution gun s f h
  obtain ⟨m,hm,b,_⟩ := X86Routine.run_path (OriginalWeaponDischarge.debit_flash_execution gun (posed gun s).core (posed gun s).flags)
  have eq : posed gun s=⟨(posed gun s).core,(posed gun s).flags,OriginalWeaponDischarge.afterPose gun⟩ := by rw [←posed_pc gun s]
  rw [←eq] at b
  have b := (X86CodeMemory.lift_success (b.transfer OriginalWeaponDischarge.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_discharge (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩


/-- Writes up to the flash setter's entry, including both real CALLs. -/
def beforeFlashWrites (gun : Fire.Gun) (s : X86Memory.State) :=
  poseWrites gun s ++ [OriginalWeaponDischarge.ammoAddress (posed gun s).core,
    (posed gun s).core.regs 4-4]

theorem before_flash_frame (gun : Fire.Gun) (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ beforeFlashWrites gun s → Apart a b) :
    load32 (flashCall gun s).core.memory a=load32 s.memory a := by
  rw [show load32 (flashCall gun s).core.memory a=load32 (posed gun s).core.memory a from
    OriginalWeaponDischarge.memory_frame gun (posed gun s).core a
      (safe _ (by simp [beforeFlashWrites])) (safe _ (by simp [beforeFlashWrites]))]
  exact pose_frame gun s a (fun b hb => safe b (by simp [beforeFlashWrites,hb]))

def flashReads (gun : Fire.Gun) : List Word :=
  [E1M1FlashInstall.pointer gun+8,E1M1FlashInstall.pointer gun+12,
   E1M1FlashInstall.pointer gun+16,E1M1FlashInstall.pointer gun+20]
structure FlashTables (gun : Fire.Gun) (m : Memory) : Prop where
  tics : load32 m (E1M1FlashInstall.pointer gun+8)=E1M1FlashInstall.timer gun
  action : load32 m (E1M1FlashInstall.pointer gun+12)=0x2db50
  next : load32 m (E1M1FlashInstall.pointer gun+16)=E1M1FlashInstall.successor gun
  misc : load32 m (E1M1FlashInstall.pointer gun+20)=0

theorem flash_registers (gun : Fire.Gun) (s : X86Memory.State) :
    (flashCall gun s).core.regs 0=s.regs 1 ∧
    (flashCall gun s).core.regs 1=s.regs 1 ∧
    (flashCall gun s).core.regs 4=s.regs 4-4 := by
  have regs := posed_registers gun s
  simp [flashCall,OriginalWeaponDischarge.flashCall,OriginalWeaponDischarge.debited,
    X86Routine.pushWord,put,write,regs.1,regs.2]

/-- Derive every flash-setter input from pre-pose memory and footprints. -/
theorem flash_inputs (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (h : OriginalWeaponDischarge.Inputs gun s c)
    (poseSafe : ∀ a, a ∈ debitReads gun s → ∀ b, b ∈ poseWrites gun s → Apart a b)
    (tables : FlashTables gun s.memory)
    (tableSafe : ∀ a, a ∈ flashReads gun → ∀ b, b ∈ beforeFlashWrites gun s → Apart a b)
    (sep : E1M1FlashInstall.Separated gun (s.regs 1) (s.regs 4-4)) :
    E1M1FlashInstall.Inputs gun (flashCall gun s).core := by
  have related := transport gun s c h poseSafe
  have args := OriginalWeaponDischarge.call_arguments gun (posed gun s).core c related
  have regs := flash_registers gun s
  have keep (a : Word) (ha : a ∈ flashReads gun) := before_flash_frame gun s a (tableSafe a ha)
  refine ⟨args.2.1,args.2.2.1,?_,?_,?_,?_,?_⟩
  · rw [keep _ (by simp [flashReads])]; exact tables.tics
  · rw [keep _ (by simp [flashReads])]; exact tables.action
  · rw [keep _ (by simp [flashReads])]; exact tables.next
  · rw [keep _ (by simp [flashReads])]; exact tables.misc
  · simpa only [regs.1,regs.2.2] using sep

def flashed (gun : Fire.Gun) (s : X86Memory.State) := E1M1FlashInstall.result gun (flashCall gun s).core

theorem flashed_pc (gun : Fire.Gun) (s : X86Memory.State) : (flashed gun s).pc=OriginalWeaponDischarge.afterFlash gun := by
  simp only [flashed,E1M1FlashInstall.result,flashCall,OriginalWeaponDischarge.flashCall,
    X86Routine.pushWord]
  simp [put,write,OriginalWeaponDischarge.debited,load_store]
  cases gun <;> decide

/-- Actual pose body/RET, indexed debit, flash body, A_Light1 and flash RET.
Every callee in this interval is executed, rather than supplied as an oracle. -/
theorem setters_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags) (c : Weapon.Context)
    (actor : DeathSetter.SetterInputs actorEntry (call gun s).core (BitVec.ofNat 32 (OriginalWeaponDischarge.afterPose gun)))
    (h : OriginalWeaponDischarge.Inputs gun s c)
    (poseSafe : ∀ a, a ∈ debitReads gun s → ∀ b, b ∈ poseWrites gun s → Apart a b)
    (tables : FlashTables gun s.memory)
    (tableSafe : ∀ a, a ∈ flashReads gun → ∀ b, b ∈ beforeFlashWrites gun s → Apart a b)
    (sep : E1M1FlashInstall.Separated gun (s.regs 1) (s.regs 4-4)) :
    ∃ n, n≤116 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (flashed gun s) := by
  obtain ⟨n,hn,a⟩ := pose_debit_execution gun s f actor
  obtain ⟨m,hm,b⟩ := E1M1FlashInstall.execution gun (flashCall gun s).core (flashCall gun s).flags
    (flash_inputs gun s c h poseSafe tables tableSafe sep)
  have eq : flashCall gun s=⟨(flashCall gun s).core,(flashCall gun s).flags,0x2d040⟩ := rfl
  rw [←eq] at b
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a (b.transfer program [] contains_flash (by simp))⟩

def aimCall (gun : Fire.Gun) (s : X86Memory.State) :=
  OriginalWeaponDischarge.aimCall gun (flashed gun s).core (flashed gun s).flags

theorem aim_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags) (c : Weapon.Context)
    (actor : DeathSetter.SetterInputs actorEntry (call gun s).core (BitVec.ofNat 32 (OriginalWeaponDischarge.afterPose gun)))
    (h : OriginalWeaponDischarge.Inputs gun s c)
    (poseSafe : ∀ a, a ∈ debitReads gun s → ∀ b, b ∈ poseWrites gun s → Apart a b)
    (tables : FlashTables gun s.memory)
    (tableSafe : ∀ a, a ∈ flashReads gun → ∀ b, b ∈ beforeFlashWrites gun s → Apart a b)
    (sep : E1M1FlashInstall.Separated gun (s.regs 1) (s.regs 4-4)) :
    ∃ n, n≤118 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (aimCall gun s) := by
  obtain ⟨n,hn,a⟩ := setters_execution gun s f c actor h poseSafe tables tableSafe sep
  obtain ⟨m,hm,b,_⟩ := X86Routine.run_path (OriginalWeaponDischarge.aim_execution gun (flashed gun s).core (flashed gun s).flags)
  have eq : flashed gun s=⟨(flashed gun s).core,(flashed gun s).flags,OriginalWeaponDischarge.afterFlash gun⟩ := by rw [←flashed_pc gun s]
  rw [←eq] at b
  have b := (X86CodeMemory.lift_success (b.transfer OriginalWeaponDischarge.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_discharge (by simp)
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩

/-- Flash installation agrees with the live action before the later flash tick. -/
theorem live_flash (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (sep : E1M1FlashInstall.Separated gun (s.regs 1) (s.regs 4-4)) :
    (load32 (flashed gun s).core.memory (s.regs 1+260),
     load32 (flashed gun s).core.memory (s.regs 1+264),
     load32 (flashed gun s).core.memory (s.regs 1+232)) =
      (BitVec.ofNat 32 (0x15a28+28*(Weapon.fireAction gun c).state.flash.frame),
       (Weapon.fireAction gun c).state.flash.tics.toBitVec,
       (Weapon.fireAction gun c).state.extraLight.toBitVec) := by
  have regs := flash_registers gun s
  have sep' : E1M1FlashInstall.Separated gun ((flashCall gun s).core.regs 0) ((flashCall gun s).core.regs 4) := by
    simpa only [regs.1,regs.2.2] using sep
  simpa only [flashed,regs.1] using E1M1FlashInstall.live_observations gun (flashCall gun s).core c sep'

theorem live_ammo (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (h : OriginalWeaponDischarge.Inputs gun s c)
    (poseSafe : ∀ a, a ∈ debitReads gun s → ∀ b, b ∈ poseWrites gun s → Apart a b)
    (ammoSafe : ∀ b, b ∈ E1M1FlashInstall.writes (flashCall gun s).core → Apart (OriginalWeaponDischarge.playerAmmo gun s) b) :
    load32 (flashed gun s).core.memory (OriginalWeaponDischarge.playerAmmo gun s) =
      (Weapon.fireAction gun c).player.ammo[gun.ammoIndex].toBitVec := by
  unfold flashed
  rw [E1M1FlashInstall.memory_frame gun (flashCall gun s).core _ ammoSafe]
  have eq : OriginalWeaponDischarge.playerAmmo gun (posed gun s).core=OriginalWeaponDischarge.playerAmmo gun s := by
    simp only [OriginalWeaponDischarge.playerAmmo,(posed_registers gun s).1]
  rw [←eq]
  exact OriginalWeaponDischarge.action_ammo gun (posed gun s).core c (transport gun s c h poseSafe)

/-- The later debit, CALL and complete flash writes must preserve the actor. -/
def afterPoseWrites (gun : Fire.Gun) (s : X86Memory.State) : List Word :=
  [OriginalWeaponDischarge.ammoAddress (posed gun s).core, (posed gun s).core.regs 4-4] ++
    E1M1FlashInstall.writes (flashCall gun s).core

theorem live_actor (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (safe : ∀ a, a ∈ DeathSetter.fields ((call gun s).core.regs 0) →
      ∀ b, b ∈ afterPoseWrites gun s → Apart a b) :
    DeathSetter.observeFields (flashed gun s).core.memory ((call gun s).core.regs 0) =
      (BitVec.ofNat 32 (0x15a28+28*(Weapon.fireAction gun c).body.frame),
        (Weapon.fireAction gun c).body.tics.toBitVec,28,0x8005) := by
  have keep (a : Word) (ha : a ∈ DeathSetter.fields ((call gun s).core.regs 0)) :
      load32 (flashed gun s).core.memory a=load32 (posed gun s).core.memory a := by
    unfold flashed
    rw [E1M1FlashInstall.memory_frame gun (flashCall gun s).core a
      (fun b hb => safe a ha b (by simp [afterPoseWrites,hb]))]
    exact OriginalWeaponDischarge.memory_frame gun (posed gun s).core a
      (safe a ha _ (by simp [afterPoseWrites])) (safe a ha _ (by simp [afterPoseWrites]))
  have fields : DeathSetter.observeFields (flashed gun s).core.memory ((call gun s).core.regs 0) =
      DeathSetter.observeFields (posed gun s).core.memory ((call gun s).core.regs 0) := by
    unfold DeathSetter.observeFields
    repeat rw [keep _ (by simp [DeathSetter.fields,PainSetter.fields])]
  rw [fields,live_pose]
  cases gun <;> rfl

/-- Initial representation and separation obligations, not assumed post-call results. -/
structure Inputs (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context) : Prop where
  actor : DeathSetter.SetterInputs actorEntry (call gun s).core (BitVec.ofNat 32 (OriginalWeaponDischarge.afterPose gun))
  related : OriginalWeaponDischarge.Inputs gun s c
  poseSafe : ∀ a, a ∈ debitReads gun s → ∀ b, b ∈ poseWrites gun s → Apart a b
  tables : FlashTables gun s.memory
  tableSafe : ∀ a, a ∈ flashReads gun → ∀ b, b ∈ beforeFlashWrites gun s → Apart a b
  separated : E1M1FlashInstall.Separated gun (s.regs 1) (s.regs 4-4)
  ammoSafe : ∀ b, b ∈ E1M1FlashInstall.writes (flashCall gun s).core → Apart (OriginalWeaponDischarge.playerAmmo gun s) b
  actorSafe : ∀ a, a ∈ DeathSetter.fields ((call gun s).core.regs 0) → ∀ b, b ∈ afterPoseWrites gun s → Apart a b

/-- Observable firing-action state at the return from the flash setter.
The later same-tic flash countdown and event handler are outside this interval. -/
def Agrees (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context) (t : X86Control.State) : Prop :=
  load32 t.core.memory (OriginalWeaponDischarge.playerAmmo gun s) =
    (Weapon.fireAction gun c).player.ammo[gun.ammoIndex].toBitVec ∧
  DeathSetter.observeFields t.core.memory ((call gun s).core.regs 0) =
    (BitVec.ofNat 32 (0x15a28+28*(Weapon.fireAction gun c).body.frame),
      (Weapon.fireAction gun c).body.tics.toBitVec,28,0x8005) ∧
  (load32 t.core.memory (s.regs 1+260),load32 t.core.memory (s.regs 1+264),
    load32 t.core.memory (s.regs 1+232)) =
    (BitVec.ofNat 32 (0x15a28+28*(Weapon.fireAction gun c).state.flash.frame),
      (Weapon.fireAction gun c).state.flash.tics.toBitVec,
      (Weapon.fireAction gun c).state.extraLight.toBitVec)

theorem live_joined (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : Inputs gun s c) :
    ∃ n, n≤116 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (flashed gun s) ∧
      Agrees gun s c (flashed gun s) := by
  obtain ⟨n,hn,path⟩ := setters_execution gun s f c h.actor h.related h.poseSafe h.tables h.tableSafe h.separated
  exact ⟨n,hn,path,live_ammo gun s c h.related h.poseSafe h.ammoSafe,
    live_actor gun s c h.actorSafe,live_flash gun s c h.separated⟩

end Doom.Proofs.E1M1DischargeSetters

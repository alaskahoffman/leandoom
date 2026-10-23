import Doom.Proofs.OriginalFloorJoined
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Proofs
open Doom.Proofs.FloorDamage (Kind)
namespace FloorJoinedFixture

-- One shared byte memory for the original tables, player, sector, and stack.
def tables : Memory := fun a =>
  if 0x1261c ≤ a.toNat ∧ a.toNat < 0x1271c then
    Doom19.randomTableBytes.toArray[a.toNat-0x1261c]!.toBitVec
  else if 0x5a84 ≤ a.toNat ∧ a.toNat < 0xfa84 then
    let offset := a.toNat-0x5a84
    (Tables.fineSine.toArray[offset/4]!.toBitVec >>> (8*(offset%4))).setWidth 8
  else 0

def body (z : Int32) : Motion := {
  z := ⟨z⟩, floorz := ⟨0⟩, ceilingz := Fixed.ofInt 128,
  momx := Fixed.ofInt 1, momy := Fixed.ofInt (-1), frame := 0 }
def anim : PlayerAnim.State := ⟨149,-1⟩
def command : Ticcmd := { forwardMove := 50, sideMove := -40, angleTurn := 1000 }
def view : ViewState := { height := Fixed.ofInt 41, delta := ⟨-16384⟩ }

def initial (kind : Kind) (z sectorFloor timer time : Int32) (seed : UInt8) (suit : Nat) : X86Memory.State :=
  let b := body z
  let fields : List (Word × Word) := [
    (0x40000,0x41000),(0x40004,0),(0x40014,view.height.raw.toBitVec),(0x40018,view.delta.raw.toBitVec),
    (0x400c4,0),(0x40038,BitVec.ofNat 32 suit),
    (0x41014,z.toBitVec),(0x41020,b.angle.raw.toBitVec),(0x41038,b.floorz.raw.toBitVec),
    (0x4103c,b.ceilingz.raw.toBitVec),(0x41048,b.momx.raw.toBitVec),(0x4104c,b.momy.raw.toBitVec),
    (0x41060,anim.tics.toBitVec),(0x41064,PlayerAnimation.statePointer anim.frame),(0x4107c,timer.toBitVec),
    (0x41034,0x42000),(0x42000,0x43000),(0x43000,sectorFloor.toBitVec),
    (0x2cf80,time.toBitVec),(0x2cf90,0),(0x12720,BitVec.ofNat 32 seed.toNat),(0x1271c,173),
    (0x13584,0x7a84),(0x16a90,28),(0x16a94,0),(0x16a98,4),(0x16a9c,0),(0x16aa0,151)]
  let m := fields.foldl (fun m (a,v) => store32 m a v) tables
  let m := X86Routine.store16 m 0x4300e (BitVec.ofNat 16 kind.special)
  let m := X86Routine.store16 m 0x4000a command.angleTurn.toBitVec
  let m := fun a => if a = (0x40008#32) then command.forwardMove.toBitVec
    else if a = (0x40009#32) then command.sideMove.toBitVec else m a
  ⟨fun r => if r=2 then 0x40000 else if r=4 then 0x50003 else 0xa5a5a5a5,m⟩

def checks (kind : Kind) (z sectorFloor timer time : Int32) (seed : UInt8) (suit : Nat) : Bool :=
  let s := initial kind z sectorFloor timer time seed suit
  let rng : DoomRandom := ⟨seed,173⟩
  let answer := LevelSpecials.floorDamage kind.special ⟨z⟩ ⟨sectorFloor⟩ (suit != 0) time.toBitVec.toNat rng
  (X86CodeMemory.run FloorJoined.cm FloorJoined.program FloorDamage.exits 267 ⟨s,none,0x333b1⟩).map (FloorJoined.observe s) ==
    some (PreparedState.expected (body z) anim command timer view time false true,
      (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat),(0x50003#32)-(20#32))

#eval [checks .five 0 0 0 32 65 0,checks .five 0 0 2 32 65 1,
  checks .seven 0 0 0 32 0 0,checks .seven 0 0 2 1 0 0,
  checks .four 0 0 0 32 65 1,checks .four 0 0 2 1 65 1,
  checks .four 1 0 0 32 65 1,checks .four (-1) 0 2 32 65 1,
  checks .sixteen 0 0 0 (-2147483648) 255 1,checks .sixteen 0 0 2 (-1) 255 1,
  checks .sixteen 0 0 0 32 0 1,checks .sixteen 0 0 (-2147483648) 32 65 0]
end FloorJoinedFixture

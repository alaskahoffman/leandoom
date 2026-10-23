/-
Secret-sector and normal exit-switch branches from Chocolate Doom 3.1.1,
commit 410d96855b5df5410ff591a90efeafa889119224, p_spec.c/p_switch.c/g_game.c.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Fixed
import Doom.Wad
import Doom.Random

namespace Doom.LevelSpecials

/-- P_PlayerInSpecialSector's ordinary damaging floors (5/7/4/16).
Use the sector floor, before mobj movement, and the pre-increment level time.
The leaking-suit RNG draw precedes the 32-tic gate, even on non-damage tics.
Damage itself (armor, pain/death and its RNG) remains the caller's callback.
The special-11 finale/god-mode/exit branch is outside this function. -/
def floorDamage (special : Nat) (z floor : Fixed) (suit : Bool)
    (levelTime : Nat) (rng : DoomRandom) : Nat × DoomRandom := Id.run do
  if z != floor then return (0,rng)
  let mut rng := rng
  let amount ← match special with
    | 5 => pure (if suit then 0 else 10)
    | 7 => pure (if suit then 0 else 5)
    | 4 | 16 => do
      if !suit then pure 20 else
        let (roll,next) := rng.nextPlay
        rng := next
        pure (if roll < 5 then 20 else 0)
    | _ => pure 0
  return (if levelTime % 32 == 0 then amount else 0,rng)

/-- P_PlayerInSpecialSector case 9. This is sector floor equality, not floorz
from collision contacts; a player standing on a higher neighboring floor does
not discover the lower sector. The live-player gate belongs to PlayerThink. -/
def secret (special : Nat) (z floor : Fixed) (count : Int32) : Nat × Int32 :=
  if z == floor && special == 9 then (0,count+1) else (special,count)

/-- P_SpawnSpecials case 9, counted once at level initialization. -/
def totalSecrets (specials : Array Nat) : Int32 :=
  specials.foldl (fun n special => if special == 9 then n+1 else n) 0

/-- Original alphSwitchList order matters: it precedes top/middle/bottom order. -/
def switchPairs : Array (String × String × Nat) := #[
  ("SW1BRCOM","SW2BRCOM",1),
  ("SW1BRN1","SW2BRN1",1),
  ("SW1BRN2","SW2BRN2",1),
  ("SW1BRNGN","SW2BRNGN",1),
  ("SW1BROWN","SW2BROWN",1),
  ("SW1COMM","SW2COMM",1),
  ("SW1COMP","SW2COMP",1),
  ("SW1DIRT","SW2DIRT",1),
  ("SW1EXIT","SW2EXIT",1),
  ("SW1GRAY","SW2GRAY",1),
  ("SW1GRAY1","SW2GRAY1",1),
  ("SW1METAL","SW2METAL",1),
  ("SW1PIPE","SW2PIPE",1),
  ("SW1SLAD","SW2SLAD",1),
  ("SW1STARG","SW2STARG",1),
  ("SW1STON1","SW2STON1",1),
  ("SW1STON2","SW2STON2",1),
  ("SW1STONE","SW2STONE",1),
  ("SW1STRTN","SW2STRTN",1),
  ("SW1BLUE","SW2BLUE",2),
  ("SW1CMT","SW2CMT",2),
  ("SW1GARG","SW2GARG",2),
  ("SW1GSTON","SW2GSTON",2),
  ("SW1HOT","SW2HOT",2),
  ("SW1LION","SW2LION",2),
  ("SW1SATYR","SW2SATYR",2),
  ("SW1SKIN","SW2SKIN",2),
  ("SW1VINE","SW2VINE",2),
  ("SW1WOOD","SW2WOOD",2),
  ("SW1PANEL","SW2PANEL",3),
  ("SW1ROCK","SW2ROCK",3),
  ("SW1MET2","SW2MET2",3),
  ("SW1WDMET","SW2WDMET",3),
  ("SW1BRIK","SW2BRIK",3),
  ("SW1MOD1","SW2MOD1",3),
  ("SW1ZIM","SW2ZIM",3),
  ("SW1STON6","SW2STON6",3),
  ("SW1TEK","SW2TEK",3),
  ("SW1MARB","SW2MARB",3),
  ("SW1SKULL","SW2SKULL",3)
]

def switchList (episode : Nat) : Array String :=
  switchPairs.foldl (fun out (a,b,minimum) => if minimum ≤ episode then out ++ #[a,b] else out) #[]

/-- Normal IWAD mode detection from the base archive only. Map-only diagnostic
PWADs default to the shareware switch set. Patches do not change game mode. -/
def switchEpisode (lumps : Array Lump) : Nat :=
  if lumps.any (fun l => l.archive == 0 && l.name == "MAP01") then 3
  else if lumps.any (fun l => l.archive == 0 && l.name == "E2M1") then 2 else 1

structure Textures (α : Type) where
  top : α
  middle : α
  bottom : α
  deriving Inhabited, Repr

structure ExitResult (α : Type) where
  textures : Textures α
  special : Nat
  completed : Bool := false
  switchSound : Bool := false
  deriving Inhabited, Repr

/-- P_UseSpecialLine case 11 and one-shot P_ChangeSwitchTexture. Front/player
only. Texture-list order wins over slot order. Clearing special precedes sound
selection, so this exit requests swtchn, not swtchx. Completion is requested even
without a matching texture. The caller supplies an even-length switch list.
Repeatable buttons and their historical sound-origin pointer are outside this API. -/
def exitSwitch [BEq α] [Inhabited α] (palette : Array α) (textures : Textures α)
    (special : Nat) (player back : Bool) : ExitResult α := Id.run do
  if special != 11 || !player || back then return ⟨textures,special,false,false⟩
  for i in [:palette.size] do
    let value := palette[i]!
    let alternate := palette[i ^^^ 1]!
    if value == textures.top then return ⟨{ textures with top := alternate },0,true,true⟩
    if value == textures.middle then return ⟨{ textures with middle := alternate },0,true,true⟩
    if value == textures.bottom then return ⟨{ textures with bottom := alternate },0,true,true⟩
  return ⟨textures,0,true,false⟩

end Doom.LevelSpecials

/- Generated from pinned Chocolate Doom 3.1.1 info.c by scripts/generate-weapons.py.
Copyright 1993-1996 id Software; 2005-2014 Simon Howard. GPL-2.0-or-later.
Lean adaptation 2026-10-03. See COPYING.md. -/
namespace Doom.WeaponData
structure Frame where
  name : String
  sprite : String
  frame : Nat
  tics : Int32
  next : Nat
  action : String
  deriving Inhabited

def frames : Array Frame := #[
  ⟨"S_NULL","TROO",0,-1,0,"NULL"⟩,
  ⟨"S_LIGHTDONE","SHTG",4,0,0,"A_Light0"⟩,
  ⟨"S_PUNCH","PUNG",0,1,2,"A_WeaponReady"⟩,
  ⟨"S_PUNCHDOWN","PUNG",0,1,3,"A_Lower"⟩,
  ⟨"S_PUNCHUP","PUNG",0,1,4,"A_Raise"⟩,
  ⟨"S_PUNCH1","PUNG",1,4,6,"NULL"⟩,
  ⟨"S_PUNCH2","PUNG",2,4,7,"A_Punch"⟩,
  ⟨"S_PUNCH3","PUNG",3,5,8,"NULL"⟩,
  ⟨"S_PUNCH4","PUNG",2,4,9,"NULL"⟩,
  ⟨"S_PUNCH5","PUNG",1,5,2,"A_ReFire"⟩,
  ⟨"S_PISTOL","PISG",0,1,10,"A_WeaponReady"⟩,
  ⟨"S_PISTOLDOWN","PISG",0,1,11,"A_Lower"⟩,
  ⟨"S_PISTOLUP","PISG",0,1,12,"A_Raise"⟩,
  ⟨"S_PISTOL1","PISG",0,4,14,"NULL"⟩,
  ⟨"S_PISTOL2","PISG",1,6,15,"A_FirePistol"⟩,
  ⟨"S_PISTOL3","PISG",2,4,16,"NULL"⟩,
  ⟨"S_PISTOL4","PISG",1,5,10,"A_ReFire"⟩,
  ⟨"S_PISTOLFLASH","PISF",32768,7,1,"A_Light1"⟩,
  ⟨"S_SGUN","SHTG",0,1,18,"A_WeaponReady"⟩,
  ⟨"S_SGUNDOWN","SHTG",0,1,19,"A_Lower"⟩,
  ⟨"S_SGUNUP","SHTG",0,1,20,"A_Raise"⟩,
  ⟨"S_SGUN1","SHTG",0,3,22,"NULL"⟩,
  ⟨"S_SGUN2","SHTG",0,7,23,"A_FireShotgun"⟩,
  ⟨"S_SGUN3","SHTG",1,5,24,"NULL"⟩,
  ⟨"S_SGUN4","SHTG",2,5,25,"NULL"⟩,
  ⟨"S_SGUN5","SHTG",3,4,26,"NULL"⟩,
  ⟨"S_SGUN6","SHTG",2,5,27,"NULL"⟩,
  ⟨"S_SGUN7","SHTG",1,5,28,"NULL"⟩,
  ⟨"S_SGUN8","SHTG",0,3,29,"NULL"⟩,
  ⟨"S_SGUN9","SHTG",0,7,18,"A_ReFire"⟩,
  ⟨"S_SGUNFLASH1","SHTF",32768,4,31,"A_Light1"⟩,
  ⟨"S_SGUNFLASH2","SHTF",32769,3,1,"A_Light2"⟩
]
def NULL : Nat := 0
def LIGHTDONE : Nat := 1
def PUNCH : Nat := 2
def PUNCHDOWN : Nat := 3
def PUNCHUP : Nat := 4
def PUNCH1 : Nat := 5
def PUNCH2 : Nat := 6
def PUNCH3 : Nat := 7
def PUNCH4 : Nat := 8
def PUNCH5 : Nat := 9
def PISTOL : Nat := 10
def PISTOLDOWN : Nat := 11
def PISTOLUP : Nat := 12
def PISTOL1 : Nat := 13
def PISTOL2 : Nat := 14
def PISTOL3 : Nat := 15
def PISTOL4 : Nat := 16
def PISTOLFLASH : Nat := 17
def SGUN : Nat := 18
def SGUNDOWN : Nat := 19
def SGUNUP : Nat := 20
def SGUN1 : Nat := 21
def SGUN2 : Nat := 22
def SGUN3 : Nat := 23
def SGUN4 : Nat := 24
def SGUN5 : Nat := 25
def SGUN6 : Nat := 26
def SGUN7 : Nat := 27
def SGUN8 : Nat := 28
def SGUN9 : Nat := 29
def SGUNFLASH1 : Nat := 30
def SGUNFLASH2 : Nat := 31
end Doom.WeaponData

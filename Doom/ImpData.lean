/- Generated from pinned Chocolate Doom 3.1.1 info.c by scripts/generate-imp.py.
Derived from id Software / Simon Howard. SPDX-License-Identifier: GPL-2.0-or-later. -/
import Doom.Death
namespace Doom.ImpData
def TBALL1 : Nat := 97
def TBALL2 : Nat := 98
def TBALLX1 : Nat := 99
def TBALLX2 : Nat := 100
def TBALLX3 : Nat := 101
def TROO_STND : Nat := 442
def TROO_STND2 : Nat := 443
def TROO_RUN1 : Nat := 444
def TROO_RUN2 : Nat := 445
def TROO_RUN3 : Nat := 446
def TROO_RUN4 : Nat := 447
def TROO_RUN5 : Nat := 448
def TROO_RUN6 : Nat := 449
def TROO_RUN7 : Nat := 450
def TROO_RUN8 : Nat := 451
def TROO_ATK1 : Nat := 452
def TROO_ATK2 : Nat := 453
def TROO_ATK3 : Nat := 454
def TROO_PAIN : Nat := 455
def TROO_PAIN2 : Nat := 456
def frames : Array Death.Frame := #[
  ⟨97,"S_TBALL1","BAL1",32768,4,98,"NULL"⟩,
  ⟨98,"S_TBALL2","BAL1",32769,4,97,"NULL"⟩,
  ⟨99,"S_TBALLX1","BAL1",32770,6,100,"NULL"⟩,
  ⟨100,"S_TBALLX2","BAL1",32771,6,101,"NULL"⟩,
  ⟨101,"S_TBALLX3","BAL1",32772,6,0,"NULL"⟩,
  ⟨442,"S_TROO_STND","TROO",0,10,443,"A_Look"⟩,
  ⟨443,"S_TROO_STND2","TROO",1,10,442,"A_Look"⟩,
  ⟨444,"S_TROO_RUN1","TROO",0,3,445,"A_Chase"⟩,
  ⟨445,"S_TROO_RUN2","TROO",0,3,446,"A_Chase"⟩,
  ⟨446,"S_TROO_RUN3","TROO",1,3,447,"A_Chase"⟩,
  ⟨447,"S_TROO_RUN4","TROO",1,3,448,"A_Chase"⟩,
  ⟨448,"S_TROO_RUN5","TROO",2,3,449,"A_Chase"⟩,
  ⟨449,"S_TROO_RUN6","TROO",2,3,450,"A_Chase"⟩,
  ⟨450,"S_TROO_RUN7","TROO",3,3,451,"A_Chase"⟩,
  ⟨451,"S_TROO_RUN8","TROO",3,3,444,"A_Chase"⟩,
  ⟨452,"S_TROO_ATK1","TROO",4,8,453,"A_FaceTarget"⟩,
  ⟨453,"S_TROO_ATK2","TROO",5,8,454,"A_FaceTarget"⟩,
  ⟨454,"S_TROO_ATK3","TROO",6,6,444,"A_TroopAttack"⟩,
  ⟨455,"S_TROO_PAIN","TROO",7,2,456,"NULL"⟩,
  ⟨456,"S_TROO_PAIN2","TROO",7,2,444,"A_Pain"⟩
]
end Doom.ImpData

import Std

namespace Doom.DosVideo

/-- The pinned high-detail DOS presenter rotates three Mode X pages, stepping
0x4000 bytes and wrapping at 0xc000 (I_FinishUpdate, code offset 0x19fca).
A BSP gap retains the contents of this page, not the last displayed frame.
Store palette indices: the current palette applies even to retained pixels. -/
structure Pages where
  screens : Vector ByteArray 3 := Vector.replicate 3 ⟨Array.replicate 64000 0⟩
  next : Fin 3 := 0

/-- Restore only the directly rendered 320×168 viewport. The status bar and
message/widget bookkeeping continue from the latest presentation; DOS copies
status updates separately from its directly rendered VGA world. -/
def Pages.restore (pages : Pages) (latest : ByteArray) : ByteArray :=
  pages.screens[pages.next].copySlice 0 latest 0 (320*168)

def Pages.present (pages : Pages) (indices : ByteArray) : Pages :=
  { screens := pages.screens.set pages.next indices
    next := ⟨(pages.next.val+1)%3, Nat.mod_lt _ (by decide)⟩ }

/-- The completed opening melt leaves its final image on every video page.
Page numbers here are relative to the next draw, not physical VGA addresses. -/
def afterMelt (indices : ByteArray) : Pages :=
  { screens := Vector.replicate 3 indices }

end Doom.DosVideo

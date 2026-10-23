namespace Doom.UseButton

/-- P_PlayerThink invokes P_UseLines only on the rising edge of BT_USE. -/
def request (held pressed : Bool) : Bool := pressed && !held

end Doom.UseButton

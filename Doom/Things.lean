import Doom.Map

namespace Doom

/-- Vanilla editor-number metadata. Spawn dimensions; idle frame metadata follows below.
Format reference: id Software linuxdoom-1.10/info.c (see docs/ROADMAP.md). -/
structure ThingDef where
  frame : String
  fullbright : Bool
  radius : Nat
  height : Nat
  solid : Bool
  ceiling : Bool
  deriving Inhabited

def thingDef : Nat → Option ThingDef
  | 3004 => some ⟨"POSSA", false, 20, 56, true, false⟩
  | 9 => some ⟨"SPOSA", false, 20, 56, true, false⟩
  | 64 => some ⟨"VILEA", false, 20, 56, true, false⟩
  | 66 => some ⟨"SKELA", false, 20, 56, true, false⟩
  | 67 => some ⟨"FATTA", false, 48, 64, true, false⟩
  | 65 => some ⟨"CPOSA", false, 20, 56, true, false⟩
  | 3001 => some ⟨"TROOA", false, 20, 56, true, false⟩
  | 3002 => some ⟨"SARGA", false, 30, 56, true, false⟩
  | 58 => some ⟨"SARGA", false, 30, 56, true, false⟩
  | 3005 => some ⟨"HEADA", false, 31, 56, true, false⟩
  | 3003 => some ⟨"BOSSA", false, 24, 64, true, false⟩
  | 69 => some ⟨"BOS2A", false, 24, 64, true, false⟩
  | 3006 => some ⟨"SKULA", true, 16, 56, true, false⟩
  | 7 => some ⟨"SPIDA", false, 128, 100, true, false⟩
  | 68 => some ⟨"BSPIA", false, 64, 64, true, false⟩
  | 16 => some ⟨"CYBRA", false, 40, 110, true, false⟩
  | 71 => some ⟨"PAINA", false, 31, 56, true, false⟩
  | 84 => some ⟨"SSWVA", false, 20, 56, true, false⟩
  | 72 => some ⟨"KEENA", false, 16, 72, true, true⟩
  | 88 => some ⟨"BBRNA", false, 16, 16, true, false⟩
  | 2035 => some ⟨"BAR1A", false, 10, 42, true, false⟩
  | 2018 => some ⟨"ARM1A", false, 20, 16, false, false⟩
  | 2019 => some ⟨"ARM2A", false, 20, 16, false, false⟩
  | 2014 => some ⟨"BON1A", false, 20, 16, false, false⟩
  | 2015 => some ⟨"BON2A", false, 20, 16, false, false⟩
  | 5 => some ⟨"BKEYA", false, 20, 16, false, false⟩
  | 13 => some ⟨"RKEYA", false, 20, 16, false, false⟩
  | 6 => some ⟨"YKEYA", false, 20, 16, false, false⟩
  | 39 => some ⟨"YSKUA", false, 20, 16, false, false⟩
  | 38 => some ⟨"RSKUA", false, 20, 16, false, false⟩
  | 40 => some ⟨"BSKUA", false, 20, 16, false, false⟩
  | 2011 => some ⟨"STIMA", false, 20, 16, false, false⟩
  | 2012 => some ⟨"MEDIA", false, 20, 16, false, false⟩
  | 2013 => some ⟨"SOULA", true, 20, 16, false, false⟩
  | 2022 => some ⟨"PINVA", true, 20, 16, false, false⟩
  | 2023 => some ⟨"PSTRA", true, 20, 16, false, false⟩
  | 2024 => some ⟨"PINSA", true, 20, 16, false, false⟩
  | 2025 => some ⟨"SUITA", true, 20, 16, false, false⟩
  | 2026 => some ⟨"PMAPA", true, 20, 16, false, false⟩
  | 2045 => some ⟨"PVISA", true, 20, 16, false, false⟩
  | 83 => some ⟨"MEGAA", true, 20, 16, false, false⟩
  | 2007 => some ⟨"CLIPA", false, 20, 16, false, false⟩
  | 2048 => some ⟨"AMMOA", false, 20, 16, false, false⟩
  | 2010 => some ⟨"ROCKA", false, 20, 16, false, false⟩
  | 2046 => some ⟨"BROKA", false, 20, 16, false, false⟩
  | 2047 => some ⟨"CELLA", false, 20, 16, false, false⟩
  | 17 => some ⟨"CELPA", false, 20, 16, false, false⟩
  | 2008 => some ⟨"SHELA", false, 20, 16, false, false⟩
  | 2049 => some ⟨"SBOXA", false, 20, 16, false, false⟩
  | 8 => some ⟨"BPAKA", false, 20, 16, false, false⟩
  | 2006 => some ⟨"BFUGA", false, 20, 16, false, false⟩
  | 2002 => some ⟨"MGUNA", false, 20, 16, false, false⟩
  | 2005 => some ⟨"CSAWA", false, 20, 16, false, false⟩
  | 2003 => some ⟨"LAUNA", false, 20, 16, false, false⟩
  | 2004 => some ⟨"PLASA", false, 20, 16, false, false⟩
  | 2001 => some ⟨"SHOTA", false, 20, 16, false, false⟩
  | 82 => some ⟨"SGN2A", false, 20, 16, false, false⟩
  | 85 => some ⟨"TLMPA", true, 16, 16, true, false⟩
  | 86 => some ⟨"TLP2A", true, 16, 16, true, false⟩
  | 2028 => some ⟨"COLUA", true, 16, 16, true, false⟩
  | 30 => some ⟨"COL1A", false, 16, 16, true, false⟩
  | 31 => some ⟨"COL2A", false, 16, 16, true, false⟩
  | 32 => some ⟨"COL3A", false, 16, 16, true, false⟩
  | 33 => some ⟨"COL4A", false, 16, 16, true, false⟩
  | 37 => some ⟨"COL6A", false, 16, 16, true, false⟩
  | 36 => some ⟨"COL5A", false, 16, 16, true, false⟩
  | 41 => some ⟨"CEYEA", true, 16, 16, true, false⟩
  | 42 => some ⟨"FSKUA", true, 16, 16, true, false⟩
  | 43 => some ⟨"TRE1A", false, 16, 16, true, false⟩
  | 44 => some ⟨"TBLUA", true, 16, 16, true, false⟩
  | 45 => some ⟨"TGRNA", true, 16, 16, true, false⟩
  | 46 => some ⟨"TREDA", true, 16, 16, true, false⟩
  | 55 => some ⟨"SMBTA", true, 16, 16, true, false⟩
  | 56 => some ⟨"SMGTA", true, 16, 16, true, false⟩
  | 57 => some ⟨"SMRTA", true, 16, 16, true, false⟩
  | 47 => some ⟨"SMITA", false, 16, 16, true, false⟩
  | 48 => some ⟨"ELECA", false, 16, 16, true, false⟩
  | 34 => some ⟨"CANDA", true, 20, 16, false, false⟩
  | 35 => some ⟨"CBRAA", true, 16, 16, true, false⟩
  | 49 => some ⟨"GOR1A", false, 16, 68, true, true⟩
  | 50 => some ⟨"GOR2A", false, 16, 84, true, true⟩
  | 51 => some ⟨"GOR3A", false, 16, 84, true, true⟩
  | 52 => some ⟨"GOR4A", false, 16, 68, true, true⟩
  | 53 => some ⟨"GOR5A", false, 16, 52, true, true⟩
  | 59 => some ⟨"GOR2A", false, 20, 84, false, true⟩
  | 60 => some ⟨"GOR4A", false, 20, 68, false, true⟩
  | 61 => some ⟨"GOR3A", false, 20, 52, false, true⟩
  | 62 => some ⟨"GOR5A", false, 20, 52, false, true⟩
  | 63 => some ⟨"GOR1A", false, 20, 68, false, true⟩
  | 22 => some ⟨"HEADL", false, 20, 16, false, false⟩
  | 15 => some ⟨"PLAYN", false, 20, 16, false, false⟩
  | 18 => some ⟨"POSSL", false, 20, 16, false, false⟩
  | 21 => some ⟨"SARGN", false, 20, 16, false, false⟩
  | 23 => some ⟨"SKULK", false, 20, 16, false, false⟩
  | 20 => some ⟨"TROOM", false, 20, 16, false, false⟩
  | 19 => some ⟨"SPOSL", false, 20, 16, false, false⟩
  | 10 => some ⟨"PLAYW", false, 20, 16, false, false⟩
  | 12 => some ⟨"PLAYW", false, 20, 16, false, false⟩
  | 28 => some ⟨"POL2A", false, 16, 16, true, false⟩
  | 24 => some ⟨"POL5A", false, 20, 16, false, false⟩
  | 27 => some ⟨"POL4A", false, 16, 16, true, false⟩
  | 29 => some ⟨"POL3A", true, 16, 16, true, false⟩
  | 25 => some ⟨"POL1A", false, 16, 16, true, false⟩
  | 26 => some ⟨"POL6A", false, 16, 16, true, false⟩
  | 54 => some ⟨"TRE2A", false, 32, 16, true, false⟩
  | 70 => some ⟨"FCANA", true, 16, 16, true, false⟩
  | 73 => some ⟨"HDB1A", false, 16, 88, true, true⟩
  | 74 => some ⟨"HDB2A", false, 16, 88, true, true⟩
  | 75 => some ⟨"HDB3A", false, 16, 64, true, true⟩
  | 76 => some ⟨"HDB4A", false, 16, 64, true, true⟩
  | 77 => some ⟨"HDB5A", false, 16, 64, true, true⟩
  | 78 => some ⟨"HDB6A", false, 16, 64, true, true⟩
  | 79 => some ⟨"POB1A", false, 20, 16, false, false⟩
  | 80 => some ⟨"POB2A", false, 20, 16, false, false⟩
  | 81 => some ⟨"BRS1A", false, 20, 16, false, false⟩
  | _ => none

/-- Current scene uses single-player, medium-difficulty map things. -/
def Thing.active (t : Thing) : Bool := t.flags / 2 % 2 == 1 && t.flags / 16 % 2 == 0

structure ThingPose where
  frame : String
  fullbright : Bool
  ticks : Nat  -- Zero means a permanent pose.
  deriving Inhabited

/-- Spawn/idle frame timing from the published vanilla state metadata.
Action callbacks (AI, attacks, etc.) are deliberately not executed here. -/
def thingPoses (kind : Nat) : Array ThingPose := match kind with
  | 3004 => #[⟨"POSSA", false, 10⟩, ⟨"POSSB", false, 10⟩]
  | 9 => #[⟨"SPOSA", false, 10⟩, ⟨"SPOSB", false, 10⟩]
  | 64 => #[⟨"VILEA", false, 10⟩, ⟨"VILEB", false, 10⟩]
  | 66 => #[⟨"SKELA", false, 10⟩, ⟨"SKELB", false, 10⟩]
  | 67 => #[⟨"FATTA", false, 15⟩, ⟨"FATTB", false, 15⟩]
  | 65 => #[⟨"CPOSA", false, 10⟩, ⟨"CPOSB", false, 10⟩]
  | 3001 => #[⟨"TROOA", false, 10⟩, ⟨"TROOB", false, 10⟩]
  | 3002 => #[⟨"SARGA", false, 10⟩, ⟨"SARGB", false, 10⟩]
  | 58 => #[⟨"SARGA", false, 10⟩, ⟨"SARGB", false, 10⟩]
  | 3003 => #[⟨"BOSSA", false, 10⟩, ⟨"BOSSB", false, 10⟩]
  | 69 => #[⟨"BOS2A", false, 10⟩, ⟨"BOS2B", false, 10⟩]
  | 3006 => #[⟨"SKULA", true, 10⟩, ⟨"SKULB", true, 10⟩]
  | 7 => #[⟨"SPIDA", false, 10⟩, ⟨"SPIDB", false, 10⟩]
  | 68 => #[⟨"BSPIA", false, 10⟩, ⟨"BSPIB", false, 10⟩]
  | 16 => #[⟨"CYBRA", false, 10⟩, ⟨"CYBRB", false, 10⟩]
  | 84 => #[⟨"SSWVA", false, 10⟩, ⟨"SSWVB", false, 10⟩]
  | 2035 => #[⟨"BAR1A", false, 6⟩, ⟨"BAR1B", false, 6⟩]
  | 2018 => #[⟨"ARM1A", false, 6⟩, ⟨"ARM1B", true, 7⟩]
  | 2019 => #[⟨"ARM2A", false, 6⟩, ⟨"ARM2B", true, 6⟩]
  | 2014 => #[⟨"BON1A", false, 6⟩, ⟨"BON1B", false, 6⟩, ⟨"BON1C", false, 6⟩, ⟨"BON1D", false, 6⟩, ⟨"BON1C", false, 6⟩, ⟨"BON1B", false, 6⟩]
  | 2015 => #[⟨"BON2A", false, 6⟩, ⟨"BON2B", false, 6⟩, ⟨"BON2C", false, 6⟩, ⟨"BON2D", false, 6⟩, ⟨"BON2C", false, 6⟩, ⟨"BON2B", false, 6⟩]
  | 5 => #[⟨"BKEYA", false, 10⟩, ⟨"BKEYB", true, 10⟩]
  | 13 => #[⟨"RKEYA", false, 10⟩, ⟨"RKEYB", true, 10⟩]
  | 6 => #[⟨"YKEYA", false, 10⟩, ⟨"YKEYB", true, 10⟩]
  | 39 => #[⟨"YSKUA", false, 10⟩, ⟨"YSKUB", true, 10⟩]
  | 38 => #[⟨"RSKUA", false, 10⟩, ⟨"RSKUB", true, 10⟩]
  | 40 => #[⟨"BSKUA", false, 10⟩, ⟨"BSKUB", true, 10⟩]
  | 2013 => #[⟨"SOULA", true, 6⟩, ⟨"SOULB", true, 6⟩, ⟨"SOULC", true, 6⟩, ⟨"SOULD", true, 6⟩, ⟨"SOULC", true, 6⟩, ⟨"SOULB", true, 6⟩]
  | 2022 => #[⟨"PINVA", true, 6⟩, ⟨"PINVB", true, 6⟩, ⟨"PINVC", true, 6⟩, ⟨"PINVD", true, 6⟩]
  | 2024 => #[⟨"PINSA", true, 6⟩, ⟨"PINSB", true, 6⟩, ⟨"PINSC", true, 6⟩, ⟨"PINSD", true, 6⟩]
  | 2026 => #[⟨"PMAPA", true, 6⟩, ⟨"PMAPB", true, 6⟩, ⟨"PMAPC", true, 6⟩, ⟨"PMAPD", true, 6⟩, ⟨"PMAPC", true, 6⟩, ⟨"PMAPB", true, 6⟩]
  | 2045 => #[⟨"PVISA", true, 6⟩, ⟨"PVISB", false, 6⟩]
  | 83 => #[⟨"MEGAA", true, 6⟩, ⟨"MEGAB", true, 6⟩, ⟨"MEGAC", true, 6⟩, ⟨"MEGAD", true, 6⟩]
  | 85 => #[⟨"TLMPA", true, 4⟩, ⟨"TLMPB", true, 4⟩, ⟨"TLMPC", true, 4⟩, ⟨"TLMPD", true, 4⟩]
  | 86 => #[⟨"TLP2A", true, 4⟩, ⟨"TLP2B", true, 4⟩, ⟨"TLP2C", true, 4⟩, ⟨"TLP2D", true, 4⟩]
  | 36 => #[⟨"COL5A", false, 14⟩, ⟨"COL5B", false, 14⟩]
  | 41 => #[⟨"CEYEA", true, 6⟩, ⟨"CEYEB", true, 6⟩, ⟨"CEYEC", true, 6⟩, ⟨"CEYEB", true, 6⟩]
  | 42 => #[⟨"FSKUA", true, 6⟩, ⟨"FSKUB", true, 6⟩, ⟨"FSKUC", true, 6⟩]
  | 44 => #[⟨"TBLUA", true, 4⟩, ⟨"TBLUB", true, 4⟩, ⟨"TBLUC", true, 4⟩, ⟨"TBLUD", true, 4⟩]
  | 45 => #[⟨"TGRNA", true, 4⟩, ⟨"TGRNB", true, 4⟩, ⟨"TGRNC", true, 4⟩, ⟨"TGRND", true, 4⟩]
  | 46 => #[⟨"TREDA", true, 4⟩, ⟨"TREDB", true, 4⟩, ⟨"TREDC", true, 4⟩, ⟨"TREDD", true, 4⟩]
  | 55 => #[⟨"SMBTA", true, 4⟩, ⟨"SMBTB", true, 4⟩, ⟨"SMBTC", true, 4⟩, ⟨"SMBTD", true, 4⟩]
  | 56 => #[⟨"SMGTA", true, 4⟩, ⟨"SMGTB", true, 4⟩, ⟨"SMGTC", true, 4⟩, ⟨"SMGTD", true, 4⟩]
  | 57 => #[⟨"SMRTA", true, 4⟩, ⟨"SMRTB", true, 4⟩, ⟨"SMRTC", true, 4⟩, ⟨"SMRTD", true, 4⟩]
  | 49 => #[⟨"GOR1A", false, 10⟩, ⟨"GOR1B", false, 15⟩, ⟨"GOR1C", false, 8⟩, ⟨"GOR1B", false, 6⟩]
  | 63 => #[⟨"GOR1A", false, 10⟩, ⟨"GOR1B", false, 15⟩, ⟨"GOR1C", false, 8⟩, ⟨"GOR1B", false, 6⟩]
  | 23 => #[⟨"SKULK", false, 6⟩]
  | 29 => #[⟨"POL3A", true, 6⟩, ⟨"POL3B", true, 6⟩]
  | 26 => #[⟨"POL6A", false, 6⟩, ⟨"POL6B", false, 8⟩]
  | 70 => #[⟨"FCANA", true, 4⟩, ⟨"FCANB", true, 4⟩, ⟨"FCANC", true, 4⟩]
  | _ => match thingDef kind with
    | some d => #[⟨d.frame, d.fullbright, 0⟩]
    | none => #[]

def thingPose (kind tick : Nat) : Option ThingPose := Id.run do
  let poses := thingPoses kind
  if poses.isEmpty then return none
  let duration := poses.foldl (fun n p => n + p.ticks) 0
  if duration == 0 then return poses[0]?
  -- The dead lost-soul decoration reaches the null state and disappears.
  if kind == 23 && tick ≥ duration then return none
  let mut time := tick % duration
  for pose in poses do
    if pose.ticks == 0 || time < pose.ticks then return some pose
    time := time - pose.ticks
  return none

/-- Built-in switch names use SW1/SW2 paired textures. -/
def switchPartner (label : String) : Option String :=
  if label.startsWith "SW1" then some ("SW2" ++ (label.drop 3).toString)
  else if label.startsWith "SW2" then some ("SW1" ++ (label.drop 3).toString)
  else none

end Doom

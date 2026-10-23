import Doom.Assets
import Doom.Simulation

namespace Doom.DosHeap
open Binary

/-- sprnames from the original info table; absent shareware sprites allocate no frames. -/
private def spriteNames : Array String :=
  ("TROO SHTG PUNG PISG PISF SHTF SHT2 CHGG CHGF MISG MISF SAWG PLSG PLSF BFGG BFGF BLUD PUFF BAL1 BAL2 PLSS PLSE MISL BFS1 BFE1 BFE2 TFOG IFOG PLAY POSS SPOS VILE FIRE FATB FBXP SKEL MANF FATT CPOS SARG HEAD BAL7 BOSS BOS2 SKUL SPID BSPI APLS APBX CYBR PAIN SSWV KEEN BBRN BOSF ARM1 ARM2 BAR1 BEXP FCAN BON1 BON2 BKEY RKEY YKEY BSKU RSKU YSKU STIM MEDI SOUL PINV PSTR PINS MEGA SUIT PMAP PVIS CLIP AMMO ROCK BROK CELL CELP SHEL SBOX BPAK BFUG MGUN CSAW LAUN PLAS SHOT SGN2 COLU SMT2 GOR1 POL2 POL5 POL4 POL3 POL1 POL6 GOR2 GOR3 GOR4 GOR5 SMIT COL1 COL2 COL3 COL4 CAND CBRA COL6 TRE1 TRE2 ELEC CEYE FSKU COL5 TBLU TGRN TRED SMBT SMGT SMRT HDB1 HDB2 HDB3 HDB4 HDB5 HDB6 POB1 POB2 BRS1 TLMP TLP2".splitOn " ").toArray

private def index (name : String) : Action Nat := do
  let some i := findLump (← get).lumps name | throw s!"DOS startup missing {name}"
  return i

private def allocateOnly (size : Nat) (value : Int32 := 1) : Action Unit := do
  let address ← allocate size value
  forget address size

private def cacheOnly (name : String) (value : Int32 := 1) : Action Unit := do
  let _ ← named name value

/-- Port of the DOS allocation lifecycle, not of Chocolate's later hash tables
and heap-allocated lookup scratch space. Payloads not yet modeled remain unknown. -/
private def initializeHeap (art : Art) (s : Simulation) (layout : Layout) : Action Unit := do
  let pnames ← named "PNAMES" 1
  release pnames
  let defs ← named "TEXTURE1" 1
  let n := art.textureNames.size
  for i in [:7] do
    let ptr ← allocate (n*4)
    if i == 3 then
      write ptr ⟨Array.replicate (n*4) 0⟩
      modify fun h => { h with compositeCells := ptr }
  for name in art.textureNames do
    let some d := art.definitions[name]? | throw "DOS texture definition missing"
    allocateOnly (14+12*d.patches.size)
    allocateOnly (d.width*2)
    allocateOnly (d.width*2)
  release defs
  let mut composites := #[]
  let mut patchCache := {}
  for name in art.textureNames do
    let some d := art.definitions[name]? | throw "DOS texture definition missing"
    let mut patches := #[]
    for p in d.patches do
      let i ← index art.pnames[p.patch]!
      let _ ← load i
      patches := patches.push i
    let (t,next) ← art.texture name patchCache
    patchCache := next
    let bytes := (t.columnSources.findSome? fun c => c >>= fun c => if c.patch then none else some c.bytes).getD ByteArray.empty
    composites := composites.push { bytes, patches }
  modify fun h => { h with composites }
  allocateOnly ((n+1)*4)
  let flats := (← index "F_END") - (← index "F_START") - 1
  allocateOnly ((flats+1)*4)
  let first := (← index "S_START")+1
  let stop ← index "S_END"
  for _ in [:3] do allocateOnly ((stop-first)*4)
  for i in [first:stop] do let _ ← load i
  let maps ← lumpBytes art.lumps "COLORMAP"
  let base ← allocate (maps.size+255)
  write ((base+255) &&& 0xffffff00) maps
  allocateOnly (3*256+255)
  allocateOnly (spriteNames.size*8)
  for sprite in spriteNames do
    let mut frames := 0
    for i in [first:stop] do
      let name := art.lumps[i]!.name
      if (name.take 4).toString != sprite then continue
      let chars := name.toList.toArray
      for j in #[4,6] do
        if let some c := chars[j]? then frames := max frames (c.toNat-65+1)
    if frames > 0 then allocateOnly (frames*28)
  -- Original S_Init: default snd_channels=3, 12-byte channel_t.
  allocateOnly (3*12)
  for c in [33:96] do
    cacheOnly ("STCFN" ++ (if c < 100 then "0" else "") ++ toString c)
  for i in [:10] do
    cacheOnly s!"STTNUM{i}"
    cacheOnly s!"STYSNUM{i}"
  cacheOnly "STTPRCNT"
  for i in [:6] do cacheOnly s!"STKEYS{i}"
  cacheOnly "STARMS"
  for i in [2:8] do cacheOnly s!"STGNUM{i}"
  cacheOnly "STFB0"
  cacheOnly "STBAR"
  for i in [:5] do
    for j in [:3] do cacheOnly s!"STFST{i}{j}"
    for name in #[s!"STFTR{i}0",s!"STFTL{i}0",s!"STFOUCH{i}",s!"STFEVL{i}",s!"STFKILL{i}"] do cacheOnly name
  cacheOnly "STFGOD0"
  cacheOnly "STFDEAD0"
  allocateOnly (320*32)
  cacheOnly "PLAYPAL" 101
  cacheOnly "STDISK" 101
  -- G_TimeDemo's transport lump, same capacity/header as the DOS worker.
  let owner ← (← get).cache.cell art.lumps.size
  let _ ← allocate (13+layout.inputCapacity*4+1) 1 owner
  cacheOnly "D_E1M1" 3
  -- First P_SetupLevel has no prior PU_LEVEL allocations to release.
  let mapStart ← index s.map.name
  let mapLump := fun label => do
    let some offset := (art.lumps.extract (mapStart+1) (mapStart+11)).findIdx? (·.name == label)
      | throw s!"DOS missing map lump {label}"
    pure (mapStart+1+offset)
  let _ ← load (← mapLump "BLOCKMAP") 50
  let block := art.lumps[← mapLump "BLOCKMAP"]!.bytes
  allocateOnly ((← u16 block 4)*(← u16 block 6)*4) 50
  -- Convert on-disk records in the original P_Load* order; discard input lumps.
  for (label,count,size) in #[("VERTEXES",s.map.vertices.size,8),
      ("SECTORS",s.map.sectors.size,86),("SIDEDEFS",s.map.sides.size,18),
      ("LINEDEFS",s.map.lines.size,62),("SSECTORS",s.map.subsectors.size,8),
      ("NODES",s.map.nodes.size,52),("SEGS",s.map.segs.size,32)] do
    allocateOnly (count*size) 50
    let input ← load (← mapLump label) 1
    release input
  let _ ← load (← mapLump "REJECT") 50
  let mut lines := 0
  for line in s.map.lines do
    lines := lines+1
    if let some back := s.map.sides[line.back]? then
      if back.sector != s.map.sides[line.front]!.sector then lines := lines+1
  allocateOnly (lines*4) 50
  let things ← load (← mapLump "THINGS") 1
  for i in [:s.spawnStates.size] do
    if s.spawnStates[i]!.isSome then
      spawn s!"thing:{i}" 154
      if s.map.things[i]!.kind == 1 then cacheOnly "STTMINUS"
  release things
  for light in s.lights do
    allocateOnly (match light.kind with | .glow => 28 | .flash => 36 | .strobe => 36 | .fire => 28) 51

/-- Supports exactly the current shareware E1M1 comparison ABI. Other profiles
must supply/port their own startup lifecycle rather than inheriting addresses. -/
def startup (art : Art) (s : Simulation) (layout : Layout := {}) (tracing := false) : Except String Heap := do
  if s.map.name != "E1M1" || (findLump art.lumps "TEXTURE2").isSome || art.lumps.size != 1264 then
    throw "DOS heap profile requires the original shareware E1M1 WAD"
  let h ← create art.lumps layout
  return (← (initializeHeap art s layout).run { h with tracing }).2

end Doom.DosHeap

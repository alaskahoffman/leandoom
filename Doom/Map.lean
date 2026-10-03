import Doom.Wad

namespace Doom
open Binary

structure Vertex where
  x : Int
  y : Int
  deriving Inhabited, Repr

structure Thing where
  position : Vertex
  angle : Nat
  kind : Nat
  flags : Nat
  deriving Inhabited, Repr

structure Linedef where
  v1 : Nat
  v2 : Nat
  flags : Nat
  special : Nat
  tag : Nat
  front : Nat
  back : Nat
  deriving Inhabited, Repr

structure Sidedef where
  xOffset : Int
  yOffset : Int
  upper : String
  lower : String
  middle : String
  sector : Nat
  deriving Inhabited, Repr

structure Sector where
  floor : Int
  ceiling : Int
  floorTexture : String
  ceilingTexture : String
  light : Int
  special : Nat
  tag : Nat
  deriving Inhabited, Repr

structure Seg where
  v1 : Nat
  v2 : Nat
  angle : Nat
  linedef : Nat
  side : Nat
  offset : Nat
  deriving Inhabited, Repr

structure Subsector where
  count : Nat
  first : Nat
  deriving Inhabited, Repr

structure Bounds where
  top : Int
  bottom : Int
  left : Int
  right : Int
  deriving Inhabited, Repr

inductive Child where
  | node (index : Nat)
  | subsector (index : Nat)
  deriving Inhabited, Repr

structure Node where
  origin : Vertex
  delta : Vertex
  rightBounds : Bounds
  leftBounds : Bounds
  right : Child
  left : Child
  deriving Inhabited, Repr

structure Blockmap where
  origin : Vertex
  width : Nat
  height : Nat
  cells : Array (Array Nat)
  /-- The diagnostic decoder accepts unsigned offsets/indices; vanilla's
  signed-short iterator cannot safely use values above 32767. -/
  vanillaOffsets : Bool := true
  deriving Inhabited

structure Map where
  name : String
  things : Array Thing
  vertices : Array Vertex
  lines : Array Linedef
  sides : Array Sidedef
  sectors : Array Sector
  segs : Array Seg
  subsectors : Array Subsector
  nodes : Array Node
  reject : ByteArray
  blockmap : Blockmap

private def vertex (b : ByteArray) (o : Nat) : Parse Vertex := do
  return ⟨← i16 b o, ← i16 b (o + 2)⟩

private def thing (b : ByteArray) (o : Nat) : Parse Thing := do
  return ⟨← vertex b o, ← u16 b (o+4), ← u16 b (o+6), ← u16 b (o+8)⟩

private def linedef (b : ByteArray) (o : Nat) : Parse Linedef := do
  return ⟨← u16 b o, ← u16 b (o+2), ← u16 b (o+4), ← u16 b (o+6),
    ← u16 b (o+8), ← u16 b (o+10), ← u16 b (o+12)⟩

private def sidedef (b : ByteArray) (o : Nat) : Parse Sidedef := do
  return ⟨← i16 b o, ← i16 b (o+2), ← name b (o+4) 8, ← name b (o+12) 8,
    ← name b (o+20) 8, ← u16 b (o+28)⟩

private def sector (b : ByteArray) (o : Nat) : Parse Sector := do
  return ⟨← i16 b o, ← i16 b (o+2), ← name b (o+4) 8, ← name b (o+12) 8,
    ← i16 b (o+20), ← u16 b (o+22), ← u16 b (o+24)⟩

private def seg (b : ByteArray) (o : Nat) : Parse Seg := do
  return ⟨← u16 b o, ← u16 b (o+2), ← u16 b (o+4), ← u16 b (o+6),
    ← u16 b (o+8), ← u16 b (o+10)⟩

private def subsector (b : ByteArray) (o : Nat) : Parse Subsector := do
  return ⟨← u16 b o, ← u16 b (o+2)⟩

private def bounds (b : ByteArray) (o : Nat) : Parse Bounds := do
  return ⟨← i16 b o, ← i16 b (o+2), ← i16 b (o+4), ← i16 b (o+6)⟩

private def child (b : ByteArray) (o : Nat) : Parse Child := do
  let n ← u16 b o
  return if n ≥ 32768 then .subsector (n - 32768) else .node n

private def node (b : ByteArray) (o : Nat) : Parse Node := do
  return ⟨← vertex b o, ← vertex b (o+4), ← bounds b (o+8), ← bounds b (o+16),
    ← child b (o+24), ← child b (o+26)⟩

private def parseBlockmap (b : ByteArray) : Parse Blockmap := do
  let origin ← vertex b 0
  let width ← u16 b 4
  let height ← u16 b 6
  require (width > 0 && height > 0) "BLOCKMAP: empty grid"
  require (b.size % 2 == 0) "BLOCKMAP: odd byte count"
  checkRange b 8 (width * height * 2)
  let mut cells := #[]
  let mut vanillaOffsets := true
  for i in [:width * height] do
    let offset ← u16 b (8 + i * 2)
    if offset ≥ 32768 then vanillaOffsets := false
    require (offset ≥ 4 + width * height) s!"BLOCKMAP cell {i}: offset overlaps header"
    let dummy ← u16 b (offset * 2)
    require (dummy == 0) s!"BLOCKMAP cell {i}: missing leading zero"
    let mut lines := #[]
    let mut terminated := false
    for word in [offset + 1:b.size / 2] do
      let value ← u16 b (word * 2)
      if value == 65535 then
        terminated := true
        break
      if value ≥ 32768 then vanillaOffsets := false
      lines := lines.push value
    require terminated s!"BLOCKMAP cell {i}: unterminated list"
    cells := cells.push lines
  return { origin, width, height, cells, vanillaOffsets }

/-- Validate graph references before any renderer can follow them. -/
def Map.validate (m : Map) : Parse Unit := do
  require (!m.vertices.isEmpty && !m.sectors.isEmpty && !m.subsectors.isEmpty)
    "map needs vertices, sectors, and subsectors"
  for i in [:m.lines.size] do
    let l := m.lines[i]!
    require (l.v1 < m.vertices.size && l.v2 < m.vertices.size) s!"LINEDEFS[{i}]: bad vertex"
    require (l.front < m.sides.size) s!"LINEDEFS[{i}]: bad front sidedef"
    require (l.back == 65535 || l.back < m.sides.size) s!"LINEDEFS[{i}]: bad back sidedef"
    require (l.flags / 4 % 2 == 0 || l.back != 65535) s!"LINEDEFS[{i}]: two-sided line without back"
  for i in [:m.sides.size] do
    require (m.sides[i]!.sector < m.sectors.size) s!"SIDEDEFS[{i}]: bad sector"
  for i in [:m.segs.size] do
    let s := m.segs[i]!
    require (s.v1 < m.vertices.size && s.v2 < m.vertices.size) s!"SEGS[{i}]: bad vertex"
    require (s.linedef < m.lines.size && s.side < 2) s!"SEGS[{i}]: bad linedef or side"
    let l := m.lines[s.linedef]!
    require ((if s.side == 0 then l.front else l.back) < m.sides.size) s!"SEGS[{i}]: absent sidedef"
  for i in [:m.subsectors.size] do
    let s := m.subsectors[i]!
    require (s.count > 0 && s.first + s.count ≤ m.segs.size) s!"SSECTORS[{i}]: bad seg range"
  for i in [:m.nodes.size] do
    for c in #[m.nodes[i]!.right, m.nodes[i]!.left] do
      match c with
      | .node n => require (n < m.nodes.size) s!"NODES[{i}]: bad node child"
      | .subsector n => require (n < m.subsectors.size) s!"NODES[{i}]: bad subsector child"
  if m.nodes.isEmpty then
    require (m.subsectors.size == 1) "zero BSP nodes requires exactly one subsector"
  -- Iterative DFS detects cycles without recursion or trusting node ordering.
  let mut colors := Array.replicate m.nodes.size (0 : Nat)
  for root in [:m.nodes.size] do
    if colors[root]! != 0 then continue
    let mut stack := [(root, false)]
    for _ in [:m.nodes.size * 3 + 1] do
      match stack with
      | [] => break
      | (i, exiting) :: rest =>
        stack := rest
        if exiting then
          colors := colors.set! i 2
        else if colors[i]! == 1 then
          throw s!"NODES[{i}]: BSP cycle"
        else if colors[i]! == 0 then
          colors := colors.set! i 1
          stack := (i, true) :: stack
          for c in #[m.nodes[i]!.right, m.nodes[i]!.left] do
            if let .node n := c then stack := (n, false) :: stack
    require stack.isEmpty "BSP traversal exceeded node budget"
  for i in [:m.blockmap.cells.size] do
    for l in m.blockmap.cells[i]! do
      require (l < m.lines.size) s!"BLOCKMAP cell {i}: bad linedef {l}"

def Map.load (lumps : Array Lump) (mapName : String) : Parse Map := do
  let mapName := mapName.toUpper
  let some start := findLump lumps mapName | throw s!"map {mapName} not found"
  let expected := #["THINGS", "LINEDEFS", "SIDEDEFS", "VERTEXES", "SEGS",
    "SSECTORS", "NODES", "SECTORS", "REJECT", "BLOCKMAP"]
  require (start + 10 < lumps.size) s!"{mapName}: incomplete map group"
  for i in [:expected.size] do
    require (lumps[start+i+1]!.archive == lumps[start]!.archive)
      s!"{mapName}: map group crosses archive boundary"
    require (lumps[start+i+1]!.name == expected[i]!)
      s!"{mapName}: expected {expected[i]!}, found {lumps[start+i+1]!.name}"
  if start + 11 < lumps.size && lumps[start+11]!.archive == lumps[start]!.archive then
    require (lumps[start+11]!.name != "BEHAVIOR") "Hexen-format maps are not supported"
  let data := fun i => lumps[start+i]!.bytes
  let m : Map := {
    name := mapName
    things := ← records "THINGS" (data 1) 10 thing
    lines := ← records "LINEDEFS" (data 2) 14 linedef
    sides := ← records "SIDEDEFS" (data 3) 30 sidedef
    vertices := ← records "VERTEXES" (data 4) 4 vertex
    segs := ← records "SEGS" (data 5) 12 seg
    subsectors := ← records "SSECTORS" (data 6) 4 subsector
    nodes := ← records "NODES" (data 7) 28 node
    sectors := ← records "SECTORS" (data 8) 26 sector
    reject := data 9
    blockmap := ← parseBlockmap (data 10)
  }
  m.validate
  return m

end Doom

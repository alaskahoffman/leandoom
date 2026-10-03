import Doom.Map

namespace Doom

private def escapeXml (s : String) : String :=
  (((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;").replace "\"" "&quot;"

/-- Diagnostic automap: shows all geometry, including secrets and hidden lines. -/
def Map.toSvg (m : Map) : String := Id.run do
  let first := m.vertices[0]!
  let mut minX := first.x
  let mut maxX := first.x
  let mut minY := first.y
  let mut maxY := first.y
  for v in m.vertices do
    minX := min minX v.x
    maxX := max maxX v.x
    minY := min minY v.y
    maxY := max maxY v.y
  let width := max 1 (maxX - minX)
  let height := max 1 (maxY - minY)
  let extent := max width height
  let margin := max 32 (extent / 32)
  let stroke := max 1 (extent / 1100)
  let radius := max 4 (extent / 350)
  let mut out := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1200\" height=\"900\" viewBox=\"{minX-margin} {-maxY-margin} {width+2*margin} {height+2*margin}\">\n"
  out := out ++ s!"<title>Lean DOOM — {escapeXml m.name}</title>\n"
  out := out ++ "<rect x=\"-100000\" y=\"-100000\" width=\"200000\" height=\"200000\" fill=\"#0b1017\"/>\n"
  out := out ++ s!"<g stroke-width=\"{stroke}\" stroke-linecap=\"round\">\n"
  for l in m.lines do
    let a := m.vertices[l.v1]!
    let b := m.vertices[l.v2]!
    let color := if l.special != 0 then "#75d6ff" else if l.back == 65535 then "#ff6268" else "#526071"
    out := out ++ s!"<line x1=\"{a.x}\" y1=\"{-a.y}\" x2=\"{b.x}\" y2=\"{-b.y}\" stroke=\"{color}\"/>\n"
  out := out ++ "</g>\n"
  for t in m.things do
    let isPlayer := t.kind ≥ 1 && t.kind ≤ 4
    let color := if isPlayer then "#b4ff75" else "#dcb577"
    out := out ++ s!"<circle cx=\"{t.position.x}\" cy=\"{-t.position.y}\" r=\"{if isPlayer then radius*2 else radius}\" fill=\"{color}\"><title>Thing {t.kind}, angle {t.angle}</title></circle>\n"
  return out ++ "</svg>\n"

end Doom

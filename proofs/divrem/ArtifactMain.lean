import DivRemFV.ArtifactBinding
import DivRemFV.AirJson

open DivRemFV DivRemFV.ArtifactWire

private def fail (message : String) : IO α := throw (IO.userError message)

private def checkJson (artifact : Artifact) (path : String) : IO Unit := do
  let .ok json := Lean.Json.parse (← IO.FS.readFile path) | fail "invalid inspection JSON"
  let .ok original := AirJson.readArtifact json | fail "invalid inspection AIR"
  unless artifact.modules.length = original.modules.size do fail "module count differs"
  unless artifact.entries.length = original.entries.size do fail "constraint count differs"
  for module in artifact.modules do
    let some m := original.modules.find? (·.id == module.id) | fail "module missing in JSON"
    unless module.name == m.name.toUTF8.data.toList.map UInt8.toNat &&
        module.isStatic == m.isStatic && module.columns.length == m.columnCount &&
        module.content == m.content.toList.map Array.toList do
      fail s!"module {module.id} differs from JSON"
  for (e, i) in artifact.entries.zipIdx do
    let some c := original.entries[i]? | fail "constraint missing in JSON"
    unless e.id == c.id && e.owner == c.owner && e.rule.translate == c.constraint.translate do
      fail s!"constraint {e.id} differs from JSON"

def main (args : List String) : IO UInt32 := do
  try
    let path := args[0]?.getD "artifacts/air.wire"
    let bytes ← IO.FS.readBinFile path
    let some full := ArtifactWire.decode bytes.data.toList | fail "whole AIR wire decode rejected"
    let inspection := args[1]?.getD "artifacts/air.json"
    unless inspection == "--wire-only" do checkJson full inspection
    unless ArtifactBinding.check full do fail "whole AIR component binding rejected"
    IO.println s!"Full wire binding passed: {bytes.size} bytes, {full.modules.length} modules, {full.entries.length} constraints, {ArtifactBinding.selectedRaw full |>.length} selected, {ArtifactBinding.incomingEntries full |>.length} interfaces"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"Full wire binding rejected: {error}"
    return (1 : UInt32)

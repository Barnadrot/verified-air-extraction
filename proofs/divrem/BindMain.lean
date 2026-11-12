import DivRemFV.AirJson
import DivRemFV.BoundSigned64

open Lean (Json)
open DivRemFV DivRemFV.NativeImport DivRemFV.AirJson

private def expectedDynamic : Array (Nat × String × Nat) := #[
  (55, "absolute_value_double_word", 28), (56, "absolute_value_word", 14),
  (61, "divMod_64_uu", 123), (62, "divMod_64_ss", 47),
  (63, "divMod_32_uu", 53), (64, "divMod_32_ss", 27),
  (65, "negative_of_double_word", 30), (66, "negative_of_word", 16)]

private def findModule (artifact : Artifact) (id : Nat) : Except String Module :=
  match artifact.modules.find? (·.id == id) with
  | some module => .ok module
  | none => .error s!"missing module {id}"

private def checkEntries (full : Artifact) (entries : Array Entry) : Except String Unit := do
  let mut seen : Array Nat := #[]
  for entry in entries do
    unless !seen.contains entry.id do throw "duplicate selected constraint"
    seen := seen.push entry.id
    let some original := full.entries[entry.id]? | throw "constraint absent from full AIR"
    unless entry.owner == original.owner &&
        entry.constraint.translate == original.constraint.translate do
      throw s!"constraint {entry.id} differs from full AIR"

private def checkBinding (full slice : Artifact) (interfaces : Array Entry) : Except String Unit := do
  for (module, i) in full.modules.zipIdx do
    unless module.id == i do throw "full AIR module IDs are not indexed"
  for (entry, i) in full.entries.zipIdx do
    unless entry.id == i do throw "full AIR constraint IDs are not indexed"
  unless slice.modules.size == expectedDynamic.size + rangeTablePairs.length do
    throw "unexpected component module set"
  let mut selected : Array Nat := #[]
  for module in slice.modules do
    unless !selected.contains module.id do throw "duplicate component module"
    selected := selected.push module.id
    unless module == (← findModule full module.id) do
      throw s!"module {module.id} differs from full AIR"
  for (id, name, width) in expectedDynamic do
    let module ← findModule slice id
    unless module.name == name && module.columnCount == width &&
        !module.isStatic && module.content.isEmpty do
      throw s!"arithmetic module {id} has changed its interface"
  for (id, bits) in rangeTablePairs do
    let module ← findModule slice id
    unless module.isStatic && module.columnCount == 1 && module.content.size == 2 ^ bits do
      throw s!"range table {id} has changed its shape"
    for i in [:module.content.size] do
      unless module.content[i]! == #[i] do throw s!"range table {id} has changed its values"
  checkEntries full slice.entries
  checkEntries full interfaces
  let owned := (full.entries.filter fun entry => selected.contains entry.owner).map Entry.id
  unless owned == slice.entries.map Entry.id do throw "component slice omits or adds owned constraints"
  let calls := full.entries.filter fun entry => match entry.constraint with
    | .lookup _ targets => targets.any fun port => #[61, 62, 63, 64].contains port.moduleId
    | _ => false
  unless calls.map Entry.id == interfaces.map Entry.id do throw "helper call interface set changed"
  unless Binding.check slice.rawConstraints Generated.constraints do
    throw "captured component constraints differ from the proved Lean relation"
  unless Binding.subsetCheck (full.rawConstraints.map RawConstraint.translate) Generated.constraints do
    throw "proved component relation is not a subset of the captured full AIR"
  unless Binding.check (interfaces.toList.map Entry.constraint) Generated.incomingConstraints do
    throw "captured call interfaces differ from the proved Lean interfaces"

private def scalarText (value : Scalar) : String := s!"⟨{value.val}, by decide⟩"

private def termText : Nat → Term → Except String String
  | 0, _ => throw "term exceeds printer depth"
  | fuel + 1, term => do
    let rec argsText : Args → Except String (List String)
      | .nil => return []
      | .cons head tail => return (← termText fuel head) :: (← argsText tail)
    let printArgs (args : Args) : Except String String := do
      let values ← argsText args
      return values.foldr (fun head tail => s!"(.cons {head} {tail})") ".nil"
    match term with
    | .constant value => return s!"(.constant {scalarText value})"
    | .column id shift => return s!"(.column {id} ({shift}))"
    | .sum args => return s!"(.sum {← printArgs args})"
    | .product args => return s!"(.product {← printArgs args})"
    | .difference first rest => return s!"(.difference {← termText fuel first} {← printArgs rest})"

private def portText (port : Port) : String :=
  s!"⟨{port.moduleId}, {repr port.selector}, {repr port.columns}⟩"

private def constraintText (constraint : RawConstraint) : Except String String := do
  let portsText (ports : List Port) := "[" ++ String.intercalate ", " (ports.map portText) ++ "]"
  match constraint with
  | .vanishing owner domain term => return s!".vanishing {owner} ({repr domain}) {← termText 256 term}"
  | .range owner col bits => return s!".range {owner} {col} {bits}"
  | .lookup sources targets => return s!".lookup {portsText sources} {portsText targets}"
  | .bus sources targets => return s!".bus {portsText sources} {portsText targets}"

private def snapshot (slice : Artifact) : Except String String := do
  let mut source := "import DivRemFV.BoundSigned64\n\nset_option maxRecDepth 4096\nset_option maxHeartbeats 4000000\n\nnamespace DivRemFV.CapturedData\n\nopen NativeImport\n\n"
  for entry in slice.entries do
    source := source ++ s!"def c{entry.id} : RawConstraint := {← constraintText entry.constraint}\n"
  source := source ++ "\ndef rawConstraints : List RawConstraint := [\n" ++
    String.intercalate ",\n" (slice.entries.toList.map fun entry => s!"  c{entry.id}") ++ "]\n\n"
  source := source ++ "theorem translated_constraints :\n    rawConstraints.map RawConstraint.translate = Generated.constraints := by rfl\n\n"
  source := source ++ "theorem binding_checked : Binding.check rawConstraints Generated.constraints = true := by\n  unfold Binding.check\n  exact decide_eq_true translated_constraints\n\n"
  source := source ++ "def Accepts := BoundSigned64.Accepts rawConstraints\n\ntheorem component_iff (a b : BitVec 64) (q r : Scalar × Scalar × Scalar × Scalar) :\n    Accepts (encodeFour a.toNat) (encodeFour b.toNat) q r ↔\n      q = encodeFour (signedQuotient a b).toNat ∧\n      r = encodeFour (signedRemainder a b).toNat :=\n  BoundSigned64.component_iff rawConstraints binding_checked a b q r\n\nend DivRemFV.CapturedData\n"
  return source

private def loadJson (path : String) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok json => return json
  | .error error => throw (IO.userError s!"{path}: {error}")

def main (args : List String) : IO UInt32 := do
  try
    let fullJson ← loadJson (args[0]?.getD "artifacts/air.json")
    let sliceJson ← loadJson (args[1]?.getD "artifacts/divrem-air.json")
    let interfaceJson ← loadJson (args[2]?.getD "artifacts/helper-interfaces.json")
    let result : Except String (Artifact × Array Entry) := do
      let full ← readArtifact fullJson
      let slice ← readArtifact sliceJson
      let interfaces ← (← interfaceJson.getArr?).mapM readEntry
      checkBinding full slice interfaces
      return (slice, interfaces)
    match result with
    | .error error =>
      IO.eprintln s!"AIR binding rejected: {error}"
      return (1 : UInt32)
    | .ok (slice, interfaces) =>
      if let some output := (args[3]? : Option String) then
        match snapshot slice with
        | .error error => throw (IO.userError error)
        | .ok source => IO.FS.writeFile (System.FilePath.mk output) source
      IO.println s!"AIR binding passed: {slice.entries.size} constraints, {interfaces.size} call interfaces, {rangeTablePairs.length} static tables"
      return (0 : UInt32)
  catch error =>
    IO.eprintln s!"AIR binding rejected: {error}"
    return (1 : UInt32)

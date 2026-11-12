import Lean
import DivRemFV.TraceCheck
import DivRemFV.ArtifactBinding
import DivRemFV.SignedTrace64Data
import DivRemFV.SignedTrace32Data

open Lean DivRemFV

private def fail (message : String) : IO α := throw (IO.userError message)

private def dynamicIds : List Nat := [55,56,61,62,63,64,65,66]

private def rowsJson (rows : Array Row) : Json :=
  toJson (rows.map fun row => row.map Fin.val)

private def witnesses (input output : String) : IO Unit := do
  let .ok json := Json.parse (← IO.FS.readFile input) | fail "invalid witness input"
  let .ok pairs := json.getObjValAs? (Array (Array Nat)) "pairs" | fail "pairs missing"
  let mut cases : Array Json := #[]
  for pair in pairs do
    let a := pair[0]!
    let b := pair[1]!
    let tables := witnessTables fun mid =>
      signed64Rows a b mid ++ signed32Rows (a % 2^32) (b % 2^32) mid
    let modules := dynamicIds.map fun mid =>
      Json.mkObj [("id", toJson mid), ("rows", rowsJson (tables mid))]
    cases := cases.push (Json.mkObj [("name", toJson s!"honest-{cases.size}"),
      ("modules", toJson modules)])
  IO.FS.writeFile output (Json.mkObj [("cases", toJson cases)]).compress

private def parseTables (fixed : Tables) (json : Json) : Except String Tables := do
  let modules ← json.getObjValAs? (Array Json) "modules"
  let mut rows : Array (Nat × Array Row) := #[]
  for module in modules do
    let mid ← module.getObjValAs? Nat "id"
    unless mid ∈ dynamicIds do throw "only selected dynamic modules can vary"
    unless (rows.find? (fun entry => entry.1 == mid)).isNone do throw "duplicate module"
    let values ← module.getObjValAs? (Array (Array Nat)) "rows"
    let encoded ← values.mapM fun row => row.mapM fun n =>
      if h : n < fieldModulus then pure (⟨n, h⟩ : Scalar) else throw "noncanonical field value"
    rows := rows.push (mid, encoded)
  unless rows.size == dynamicIds.length do throw "dynamic module missing"
  let statics ← match json.getObjVal? "static_tables" with
    | .ok value => value.getArr?
    | .error _ => pure #[]
  for table in statics do
    let mid ← table.getObjValAs? Nat "id"
    let some (_, bits) := rangeTablePairs.find? (fun entry => entry.1 == mid)
      | throw "only selected range tables can vary"
    unless (rows.find? (fun entry => entry.1 == mid)).isNone do throw "duplicate table"
    let values ← table.getObjValAs? (Array (Array Nat)) "rows"
    let encoded ← values.mapM fun row => do
      unless row.size == 1 do throw "range table must have one column"
      row.mapM fun n =>
        if h : n < fieldModulus then
          if n < 2^bits then pure (⟨n, h⟩ : Scalar) else throw "table entry outside range"
        else throw "noncanonical field value"
    rows := rows.push (mid, encoded)
  return fun mid => match rows.find? (fun entry => entry.1 == mid) with
    | some entry => entry.2
    | none => fixed mid

private def compare (artifactPath input output : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile artifactPath
  let some full := ArtifactWire.decode bytes.data.toList | fail "AIR decode failed"
  unless ArtifactBinding.check full do fail "AIR binding failed"
  let constraints := (ArtifactBinding.selectedRaw full).map NativeImport.RawConstraint.translate
  let ports := constraints.flatMap fun c => match c with
    | .lookup _ targets => targets
    | _ => []
  let .ok json := Json.parse (← IO.FS.readFile input) | fail "invalid trace corpus"
  let .ok cases := json.getObjValAs? (Array Json) "cases" | fail "cases missing"
  let mut results : Array Json := #[]
  for c in cases do
    let .ok tables := parseTables fixedRangeTables c | fail "invalid trace tables"
    let cache := TraceCheck.prepare tables ports
    let verdicts := constraints.map (TraceCheck.constraint tables cache)
    let .ok name := c.getObjValAs? String "name" | fail "case name missing"
    results := results.push (Json.mkObj [("name", toJson name),
      ("accepted", toJson (verdicts.all id)), ("verdicts", toJson verdicts)])
  IO.FS.writeFile output (Json.mkObj [("results", toJson results)]).compress
  IO.println s!"Lean checked {cases.size} traces against {constraints.length} selected constraints"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--witnesses", input, output] => witnesses input output
    | [artifact, input, output] => compare artifact input output
    | _ => fail "usage: trace_semantics AIR CORPUS RESULT | --witnesses PAIRS OUTPUT"
    return 0
  catch error =>
    IO.eprintln s!"Trace semantics check failed: {error}"
    return 1

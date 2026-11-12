import Lean
import DivRemFV

open Lean (Json)
open DivRemFV

private def natField (j : Json) (name : String) : Except String Nat :=
  j.getObjValAs? Nat name

private def optionalNat (j : Json) : Except String (Option Nat) :=
  if j == Json.null then pure none else return some (← j.getNat?)

private partial def readExpr (j : Json) : Except String Expr := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "constant" =>
    let value ← natField j "value"
    if h : value < fieldModulus then return .constant ⟨value, h⟩
    else throw "noncanonical constant"
  | "column" => return .column (← natField j "column") (← j.getObjValAs? Int "shift")
  | "add" | "mul" | "sub" =>
    let args ← (← j.getObjValAs? (Array Json) "args").mapM readExpr
    match kind with
    | "add" => return args.foldl Expr.add (.constant 0)
    | "mul" => return args.foldl Expr.mul (.constant 1)
    | _ =>
      if h : 0 < args.size then
        return (args.extract 1 args.size).foldl Expr.sub args[0]
      else throw "empty subtraction"
  | _ => throw s!"unsupported expression: {kind}"

private def readPort (j : Json) : Except String Port := do
  return ⟨← natField j "module", ← optionalNat (← j.getObjVal? "selector"),
    ← j.getObjValAs? (Array Nat) "columns"⟩

private def readConstraint (j : Json) : Except String Constraint := do
  match ← j.getObjValAs? String "kind" with
  | "vanishing" =>
    return .vanishing (← natField j "owner") (← j.getObjValAs? (Option Int) "domain")
      (← readExpr (← j.getObjVal? "expr"))
  | "range" => return .range (← natField j "owner") (← natField j "column") (← natField j "bits")
  | "lookup" =>
    return .lookup ((← (← j.getObjValAs? (Array Json) "sources").mapM readPort).toList)
      ((← (← j.getObjValAs? (Array Json) "targets").mapM readPort).toList)
  | "bus" =>
    return .bus ((← (← j.getObjValAs? (Array Json) "sources").mapM readPort).toList)
      ((← (← j.getObjValAs? (Array Json) "targets").mapM readPort).toList)
  | kind => throw s!"unsupported constraint: {kind}"

private def validColumns (width : Nat) : Expr → Bool
  | .constant _ => true
  | .column col _ => col < width
  | .add a b | .sub a b | .mul a b => validColumns width a && validColumns width b

private def moduleWidth (widths : Array (Nat × Nat)) (mid : Nat) : Except String Nat :=
  match widths.find? (fun pair => pair.1 == mid) with
  | none => throw s!"unknown module {mid}"
  | some pair => pure pair.2

private def validatePorts (widths : Array (Nat × Nat)) (sources targets : List Port)
    (bus : Bool) : Except String Unit := do
  let some first := sources.head? | throw "empty source side"
  unless !targets.isEmpty && !first.columns.isEmpty do throw "empty target side or tuple"
  for port in sources ++ targets do
    let width ← moduleWidth widths port.moduleId
    unless port.columns.size == first.columns.size do throw "tuple width mismatch"
    for col in port.columns do
      unless col < width do throw "invalid tuple column"
    match port.selector with
    | some col => unless col < width do throw "invalid selector column"
    | none => if bus then throw "bus selector absent"

private def validateConstraint (widths : Array (Nat × Nat)) (c : Constraint) : Except String Unit := do
  match c with
  | .vanishing owner _ expr =>
    unless validColumns (← moduleWidth widths owner) expr do throw "invalid expression column"
  | .range owner col _ =>
    unless col < (← moduleWidth widths owner) do throw "invalid range column"
  | .lookup sources targets => validatePorts widths sources targets false
  | .bus sources targets => validatePorts widths sources targets true

private def validateArtifact (j : Json) : Except String (Nat × Nat × Nat) := do
  unless (← j.getObjValAs? String "format") == "divrem-air-v1" do throw "unsupported format"
  unless (← j.getObjValAs? String "field") == "KOALABEAR_16" do throw "unsupported field"
  unless (← natField j "modulus") == fieldModulus do throw "wrong modulus"
  let modules ← j.getObjValAs? (Array Json) "modules"
  let constraints ← j.getObjValAs? (Array Json) "constraints"
  let mut cells := 0
  let mut widths : Array (Nat × Nat) := #[]
  for m in modules do
    let mid ← natField m "id"
    unless (widths.find? (fun pair => pair.1 == mid)).isNone do throw "duplicate module"
    let columns ← m.getObjValAs? (Array Json) "columns"
    widths := widths.push (mid, columns.size)
    for i in [:columns.size] do
      let col := columns[i]!
      unless (← natField col "id") == i do throw "column id mismatch"
      let native ← col.getObjValAs? Bool "native"
      let bits ← col.getObjValAs? (Option Nat) "bits"
      unless native == bits.isNone do throw "column type mismatch"
      if let some n := bits then
        unless n ≤ 16 do throw "unsupported physical column width"
    let content ← m.getObjValAs? (Array (Array Nat)) "content"
    let isStatic ← m.getObjValAs? Bool "static"
    unless isStatic || content.isEmpty do throw "dynamic module has static content"
    for row in content do
      unless row.size == columns.size do throw "wrong static row width"
      for value in row do
        unless value < fieldModulus do throw "noncanonical static value"
        cells := cells + 1
    if isStatic && columns.size == 1 then
      let bits ← (← columns[0]!.getObjVal? "bits").getNat?
      unless bits ≤ 16 do throw "unsupported static range width"
      unless content.size == 2 ^ bits do throw "range table has wrong length"
      for i in [:content.size] do
        unless content[i]![0]! == i do throw "range table does not enumerate its range"
  let mut ids : Array Nat := #[]
  for c in constraints do
    let id ← natField c "id"
    unless !ids.contains id do throw "duplicate constraint"
    ids := ids.push id
    let _ ← moduleWidth widths (← natField c "owner")
    validateConstraint widths (← readConstraint c)
  return (modules.size, constraints.size, cells)

private def validateExpressionVectors (j : Json) : Except String Nat := do
  unless (← j.getObjValAs? String "format") == "divrem-expression-vectors-v1" do throw "unsupported vector format"
  let cases ← j.getObjValAs? (Array Json) "cases"
  let mut count := 0
  for vector in cases do
    let expr ← readExpr (← vector.getObjVal? "expr")
    let rawRows ← vector.getObjValAs? (Array (Array Nat)) "rows"
    let rows ← rawRows.mapM fun row => row.mapM fun value => do
      if h : value < fieldModulus then pure (⟨value, h⟩ : Scalar)
      else throw "noncanonical vector cell"
    for expected in (← vector.getObjValAs? (Array Json) "expected") do
      let row ← expected.getObjValAs? Int "row"
      let value ← natField expected "value"
      unless expr.eval (fun _ => rows) 0 row == value do throw "expression evaluation mismatch"
      count := count + 1
  return count

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--vectors" then
    let path := args[1]?.getD "artifacts/expression-vectors.json"
    match Json.parse (← IO.FS.readFile path) >>= validateExpressionVectors with
    | .error error =>
      IO.eprintln s!"Expression vectors rejected: {error}"
      return 1
    | .ok count =>
      IO.println s!"Lean/ZkC expression evaluations matched: {count}"
      return 0
  let path := args.headD "artifacts/divrem-air.json"
  match Json.parse (← IO.FS.readFile path) >>= validateArtifact with
  | .error error =>
    IO.eprintln s!"AIR data rejected: {error}"
    return 1
  | .ok (modules, constraints, cells) =>
    IO.println s!"AIR data read: modules={modules} constraints={constraints} static_cells={cells}"
    IO.println "Reader scope: structural validation only. See the separate component and binding checks."
    return 0

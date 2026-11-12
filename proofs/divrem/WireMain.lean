import DivRemFV.ByteWire
import DivRemFV.AirJson

open DivRemFV DivRemFV.NativeImport Lean

private def checkVectors (json : Json) : Except String Nat := do
  let cases ← json.getArr?
  for (entry, index) in cases.zipIdx do
    let numbers ← entry.getObjValAs? (Array Nat) "bytes"
    let mut bytes : List UInt8 := []
    for number in numbers.reverse do
      if number < 256 then bytes := UInt8.ofNat number :: bytes
      else throw "invalid test byte"
    let expected ← AirJson.readTerm 4096 (← entry.getObjVal? "expr")
    let some term := ByteWire.readTerm 4096 bytes | throw s!"wire case {index} rejected"
    unless term.translate == expected.translate do throw s!"wire case {index} differs"
    unless (ByteWire.readTerm 4096 bytes.dropLast).isNone do throw "truncated word accepted"
    let unknown := (255 : UInt8) :: bytes.drop 1
    unless (ByteWire.readTerm 4096 unknown).isNone do throw "unknown root tag accepted"
  return cases.size

def main (args : List String) : IO UInt32 := do
  try
    let path := args[0]?.getD "artifacts/term-wire-vectors.json"
    let text ← IO.FS.readFile path
    let result : Except String Nat := do
      let json ← Json.parse text
      checkVectors json
    match result with
    | .error message => IO.eprintln message; return (1 : UInt32)
    | .ok count =>
      IO.println s!"Term wire passed: {count} expressions; {count} truncations and {count} unknown tags rejected"
      return (0 : UInt32)
  catch error =>
    IO.eprintln s!"Term wire check failed: {error}"
    return (1 : UInt32)

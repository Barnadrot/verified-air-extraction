import Lean
import DivRemFV.NativeImport

namespace DivRemFV.AirJson

open Lean (Json)
open NativeImport

structure Entry where
  id : Nat
  owner : Nat
  constraint : RawConstraint

structure Module where
  id : Nat
  name : String
  isStatic : Bool
  columnCount : Nat
  content : Array (Array Nat)
  deriving BEq

structure Artifact where
  modules : Array Module
  entries : Array Entry

private def argsOfArray (args : Array Term) : Args :=
  args.toList.foldr Args.cons Args.nil

def readTerm : Nat → Json → Except String Term
  | 0, _ => throw "AIR expression exceeds the supported nesting depth"
  | fuel + 1, json => do
    match ← json.getObjValAs? String "kind" with
    | "constant" =>
      let value ← json.getObjValAs? Nat "value"
      if bounded : value < fieldModulus then
        return .constant ⟨value, bounded⟩
      else throw "noncanonical constant"
    | "column" =>
      return .column (← json.getObjValAs? Nat "column") (← json.getObjValAs? Int "shift")
    | "add" =>
      let args ← (← json.getObjValAs? (Array Json) "args").mapM (readTerm fuel)
      return .sum (argsOfArray args)
    | "mul" =>
      let args ← (← json.getObjValAs? (Array Json) "args").mapM (readTerm fuel)
      return .product (argsOfArray args)
    | "sub" =>
      let args ← (← json.getObjValAs? (Array Json) "args").mapM (readTerm fuel)
      if nonempty : 0 < args.size then
        return .difference args[0] (argsOfArray (args.extract 1 args.size))
      else throw "empty subtraction"
    | kind => throw s!"unsupported AIR term: {kind}"

def readPort (json : Json) : Except String Port := do
  return ⟨← json.getObjValAs? Nat "module",
    ← json.getObjValAs? (Option Nat) "selector",
    ← json.getObjValAs? (Array Nat) "columns"⟩

private def readConstraint (json : Json) : Except String RawConstraint := do
  let owner ← json.getObjValAs? Nat "owner"
  match ← json.getObjValAs? String "kind" with
    | "vanishing" => do
      return RawConstraint.vanishing owner (← json.getObjValAs? (Option Int) "domain")
        (← readTerm 256 (← json.getObjVal? "expr"))
    | "range" => do
      return RawConstraint.range owner (← json.getObjValAs? Nat "column")
        (← json.getObjValAs? Nat "bits")
    | "lookup" => do
      return RawConstraint.lookup
        ((← (← json.getObjValAs? (Array Json) "sources").mapM readPort).toList)
        ((← (← json.getObjValAs? (Array Json) "targets").mapM readPort).toList)
    | "bus" => do
      return RawConstraint.bus
        ((← (← json.getObjValAs? (Array Json) "sources").mapM readPort).toList)
        ((← (← json.getObjValAs? (Array Json) "targets").mapM readPort).toList)
    | kind => throw s!"unsupported AIR constraint: {kind}"

def readEntry (json : Json) : Except String Entry := do
  return ⟨← json.getObjValAs? Nat "id", ← json.getObjValAs? Nat "owner",
    ← readConstraint json⟩

def readModule (json : Json) : Except String Module := do
  return ⟨← json.getObjValAs? Nat "id", ← json.getObjValAs? String "name",
    ← json.getObjValAs? Bool "static", (← json.getObjValAs? (Array Json) "columns").size,
    ← json.getObjValAs? (Array (Array Nat)) "content"⟩

def readArtifact (json : Json) : Except String Artifact := do
  unless (← json.getObjValAs? String "format") == "divrem-air-v1" do
    throw "unsupported AIR format"
  unless (← json.getObjValAs? String "field") == "KOALABEAR_16" do
    throw "unsupported AIR field"
  unless (← json.getObjValAs? Nat "modulus") == fieldModulus do
    throw "wrong AIR modulus"
  return ⟨← (← json.getObjValAs? (Array Json) "modules").mapM readModule,
    ← (← json.getObjValAs? (Array Json) "constraints").mapM readEntry⟩

def Artifact.rawConstraints (artifact : Artifact) : List RawConstraint :=
  artifact.entries.toList.map Entry.constraint

end DivRemFV.AirJson

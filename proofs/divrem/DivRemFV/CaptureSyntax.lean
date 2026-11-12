import Std

namespace DivRemFV.CaptureSyntax

def modulus : Nat := 2130706433
abbrev FieldValue := Fin modulus

mutual
  inductive Term where
    | constant (value : FieldValue)
    | column (index : Nat) (shift : Int)
    | sum (args : Args)
    | difference (first : Term) (rest : Args)
    | product (args : Args)
  inductive Args where
    | nil
    | cons (head : Term) (tail : Args)
end

def Args.toList : Args → List Term
  | .nil => []
  | .cons h t => h :: t.toList

def encodeInt (n : Int) : Nat :=
  if n < 0 then 2 * (-n).toNat - 1 else 2 * n.toNat

mutual
  def Term.words : Term → List Nat
    | .constant value => [0,value.val]
    | .column index shift => [1,index,encodeInt shift]
    | .sum args => 2 :: args.words
    | .difference head tail => 3 :: (head.words ++ tail.words)
    | .product args => 4 :: args.words
  def Args.words : Args → List Nat
    | .nil => [0]
    | .cons head tail => 1 :: (head.words ++ tail.words)
end

def natWords (values : List Nat) : List Nat := values.length :: values

def boolWords (value : Bool) : List Nat := if value then [1,0] else [0,0]

def optionNatWords : Option Nat → List Nat
  | none => [0,0]
  | some n => [1,n]

def optionIntWords : Option Int → List Nat
  | none => [0,0]
  | some n => [1,encodeInt n]

structure Column where
  id : Nat
  name : List Nat
  bits : Option Nat
  input : Bool
  output : Bool
  isNative : Bool

def Column.words (column : Column) : List Nat :=
  [column.id] ++ natWords column.name ++ optionNatWords column.bits ++ boolWords column.input ++
    boolWords column.output ++ boolWords column.isNative

structure Port where
  moduleId : Nat
  selector : Option Nat
  columns : List Nat

def Port.words (port : Port) : List Nat :=
  [port.moduleId] ++ optionNatWords port.selector ++ natWords port.columns

inductive Rule where
  | vanishing (owner : Nat) (domain : Option Int) (term : Term)
  | range (owner column bits : Nat)
  | lookup (sources targets : List Port)
  | bus (sources targets : List Port)

def Rule.words : Rule → List Nat
  | .vanishing owner domain term => [0,owner] ++ optionIntWords domain ++ natWords term.words
  | .range owner column bits => [1,0,owner,column,bits]
  | .lookup sources targets => [1,1,0,sources.length] ++ sources.flatMap Port.words ++
      (targets.length :: targets.flatMap Port.words)
  | .bus sources targets => [1,1,1,sources.length] ++ sources.flatMap Port.words ++
      (targets.length :: targets.flatMap Port.words)

structure Entry where
  id : Nat
  owner : Nat
  name : List Nat
  rule : Rule

def Entry.words (entry : Entry) : List Nat :=
  [entry.id,entry.owner] ++ natWords entry.name ++ entry.rule.words

structure Module where
  id : Nat
  name : List Nat
  isStatic : Bool
  isNative : Bool
  columns : List Column
  content : List (List Nat)

def Module.words (module : Module) : List Nat :=
  [module.id] ++ natWords module.name ++ boolWords module.isStatic ++ boolWords module.isNative ++
    (module.columns.length :: module.columns.flatMap Column.words) ++
    (module.content.length :: module.content.flatMap natWords)

structure Artifact where
  modules : List Module
  entries : List Entry

def Artifact.words (artifact : Artifact) : List Nat :=
  [1146242647,1,modulus,artifact.modules.length] ++ artifact.modules.flatMap Module.words ++
    (artifact.entries.length :: artifact.entries.flatMap Entry.words)

def wordBytes (n : Nat) : List Nat :=
  [n % 256, (n/256) % 256, (n/65536) % 256, (n/16777216) % 256,
    (n/4294967296) % 256, (n/1099511627776) % 256,
    (n/281474976710656) % 256, (n/72057594037927936) % 256]

def byteValues (words : List Nat) : List Nat := words.flatMap wordBytes

end DivRemFV.CaptureSyntax

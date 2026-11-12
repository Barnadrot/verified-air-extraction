import DivRemFV.ArtifactWire

namespace DivRemFV.ArtifactWire
open WireCodec NativeImport

def natListWords (xs : List Nat) : List Nat := xs.length :: xs
def boolWords (b : Bool) : List Nat := if b then [1,0] else [0,0]
def optionNatWords : Option Nat → List Nat
  | none => [0,0]
  | some n => [1,n]
def optionIntWords : Option Int → List Nat
  | none => [0,0]
  | some n => [1,TermWire.encodeInt n]

theorem nat_fast (n : Nat) : nat.encode n = [n] := rfl
theorem nat_fast_fun : nat.encode = fun n => [n] := rfl
theorem list_fast (c : Codec α) (xs : List α) :
    (list c).encode xs = xs.length :: xs.flatMap c.encode := rfl

theorem natList_fast (xs : List Nat) : (list nat).encode xs = natListWords xs := by
  change xs.length :: xs.flatMap (fun n => [n]) = xs.length :: xs
  simp
theorem natList_fast_fun : (list nat).encode = natListWords := funext natList_fast
theorem bool_fast (b : Bool) : boolean.encode b = boolWords b := by cases b <;> rfl
theorem optionNat_fast (o : Option Nat) : (option nat).encode o = optionNatWords o := by cases o <;> rfl
theorem optionInt_fast (o : Option Int) : (option integer).encode o = optionIntWords o := by cases o <;> rfl

def columnWords (c : Column) : List Nat :=
  [c.id] ++ natListWords c.name ++ optionNatWords c.bits ++ boolWords c.input ++
    boolWords c.output ++ boolWords c.native

theorem column_fast (c : Column) : column.encode c = columnWords c := by
  simp [column,columnWords,iso,pair,nat_fast,natList_fast,bool_fast,optionNat_fast,List.append_assoc]
theorem column_fast_fun : column.encode = columnWords := funext column_fast

def moduleWords (m : Module) : List Nat :=
  [m.id] ++ natListWords m.name ++ boolWords m.isStatic ++ boolWords m.native ++
    (m.columns.length :: m.columns.flatMap columnWords) ++
    (m.content.length :: m.content.flatMap natListWords)

theorem module_fast (m : Module) : module.encode m = moduleWords m := by
  rw [module_encoding]
  simp [bool_fast,list_fast,column_fast_fun,natList_fast_fun,nat_fast_fun,moduleWords,natListWords]

def portWords (p : Port) : List Nat :=
  [p.moduleId] ++ optionNatWords p.selector ++ natListWords p.columns.toList

theorem port_fast (p : Port) : port.encode p = portWords p := by
  simp [port,portWords,iso,pair,nat_fast,natList_fast,optionNat_fast,List.append_assoc]
theorem port_fast_fun : port.encode = portWords := funext port_fast

def constraintWords : RawConstraint → List Nat
  | .vanishing owner domain t => [0,owner] ++ optionIntWords domain ++ natListWords (TermWire.encodeTerm t)
  | .range owner col bits => [1,0,owner,col,bits]
  | .lookup sources targets => [1,1,0,sources.length] ++ sources.flatMap portWords ++
      (targets.length :: targets.flatMap portWords)
  | .bus sources targets => [1,1,1,sources.length] ++ sources.flatMap portWords ++
      (targets.length :: targets.flatMap portWords)

theorem constraint_fast (c : RawConstraint) : constraint.encode c = constraintWords c := by
  cases c <;>
    simp [constraint,constraintWords,fromConstraint,iso,sum,pair,nat_fast,term,natList_fast,optionInt_fast,
      list_fast,port_fast_fun,nat_fast_fun,natListWords,List.append_assoc]

def entryWords (e : Entry) : List Nat :=
  [e.id,e.owner] ++ natListWords e.name ++ constraintWords e.rule

theorem entry_fast (e : Entry) : entry.encode e = entryWords e := by
  simp [entry,entryWords,iso,pair,nat_fast,natList_fast,constraint_fast,List.append_assoc]
theorem entry_fast_fun : entry.encode = entryWords := funext entry_fast

end DivRemFV.ArtifactWire

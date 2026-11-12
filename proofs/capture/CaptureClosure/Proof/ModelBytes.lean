module
public import CaptureClosure.Proof.TermModel
public import CaptureClosure.Proof.WordWire

@[expose] public section
namespace Perennial.divremfv.internal.airdata.SourceCapture

def wireBytes (tokens : List Nat) : List w8 := tokens.flatMap (fun (n : Nat) => u64Le (W64 n))

theorem wireBytes_append (a b : List Nat) : wireBytes (a ++ b) = wireBytes a ++ wireBytes b :=
  List.flatMap_append

theorem wireBytes_nil : wireBytes [] = [] := rfl

theorem wireBytes_cons (n : Nat) (tail : List Nat) :
    wireBytes (n :: tail) = u64Le (W64 n) ++ wireBytes tail := rfl

def argStream (models : List ModelTerm) : List Nat :=
  models.flatMap (fun model => 1 :: model.words)

theorem args_words (args : ModelArgs) : args.words = argStream args.toList ++ [0] := by
  cases args with
  | nil => rfl
  | cons first rest =>
    simp only [DivRemFV.CaptureSyntax.Args.words,DivRemFV.CaptureSyntax.Args.toList,
      argStream,List.flatMap_cons,args_words rest,List.cons_append,List.append_assoc]
termination_by sizeOf args

end Perennial.divremfv.internal.airdata.SourceCapture

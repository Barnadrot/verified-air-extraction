module
public import CaptureClosure.Proof.ArtifactWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

def WordsBounded (words : List Nat) : Prop := ∀ n ∈ words, n < 2^64

@[simp] theorem bounded_nil : WordsBounded [] := by simp [WordsBounded]
@[simp] theorem bounded_cons (n : Nat) (tail : List Nat) :
    WordsBounded (n :: tail) ↔ n < 2^64 ∧ WordsBounded tail := by simp [WordsBounded]
@[simp] theorem bounded_append (a b : List Nat) :
    WordsBounded (a ++ b) ↔ WordsBounded a ∧ WordsBounded b := by
  simp [WordsBounded,List.mem_append,or_imp,forall_and]

theorem bounded_word (value : w64) : value.toNat < 2^64 := by word
theorem bounded_byte (value : w8) : value.toNat < 2^64 := by word
theorem bounded_int (word : w64) : DivRemFV.CaptureSyntax.encodeInt (sint.Z word) < 2^64 := by
  rw [← zigzag_word_value]
  exact bounded_word _

theorem bounded_natWords (values : List Nat) (hlen : values.length < 2^64) (hvalues : WordsBounded values) :
    WordsBounded (DivRemFV.CaptureSyntax.natWords values) := (bounded_cons _ _).2 ⟨hlen,hvalues⟩

theorem bounded_name (value : GoString) (hlen : value.length < 2^63) :
    WordsBounded (DivRemFV.CaptureSyntax.natWords (value.map BitVec.toNat)) := by
  apply bounded_natWords
  · simpa only [List.length_map] using (show value.length < 2^64 by omega)
  · intro n member
    rcases List.mem_map.mp member with ⟨byte,_,rfl⟩
    exact bounded_byte byte

theorem bounded_bool (value : Bool) : WordsBounded (DivRemFV.CaptureSyntax.boolWords value) := by
  cases value <;> simp [DivRemFV.CaptureSyntax.boolWords]

theorem bounded_optional (value : Option w64) :
    WordsBounded (DivRemFV.CaptureSyntax.optionNatWords (value.map BitVec.toNat)) := by
  cases value with
  | none => simp [DivRemFV.CaptureSyntax.optionNatWords]
  | some value =>
    simp only [Option.map_some,DivRemFV.CaptureSyntax.optionNatWords,bounded_cons,bounded_nil,and_true]
    exact ⟨by decide,bounded_word value⟩

theorem bounded_domain (value : Option w64) :
    WordsBounded (DivRemFV.CaptureSyntax.optionIntWords (value.map sint.Z)) := by
  cases value with
  | none => simp [DivRemFV.CaptureSyntax.optionIntWords]
  | some value =>
    simp only [Option.map_some,DivRemFV.CaptureSyntax.optionIntWords,bounded_cons,bounded_nil,and_true]
    exact ⟨by decide,bounded_int value⟩

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

mutual
  theorem output_term_bounded (model : ModelTerm) (value : Term) :
      OutputTerm (GF := GF) model value ⊢ iprop(⌜WordsBounded model.words⌝) := by
    iintro Hmodel
    cases model with
    | constant value =>
      ipureintro
      simp only [DivRemFV.CaptureSyntax.Term.words,bounded_cons,bounded_nil,and_true]
      have Hvalue := value.isLt
      change value.val < 2130706433 at Hvalue
      exact ⟨by decide,by omega⟩
    | column index shift =>
      isimp only [OutputTerm] at Hmodel
      icases Hmodel with ⟨⟨_,_,%Hindex,%Hshift⟩,_⟩
      ipureintro
      simp only [DivRemFV.CaptureSyntax.Term.words,bounded_cons,bounded_nil,and_true]
      exact ⟨by decide,Hindex ▸ bounded_word _,Hshift ▸ bounded_int _⟩
    | sum args | product args =>
      isimp only [OutputTerm] at Hmodel
      icases Hmodel with ⟨%values,_,_,Hargs⟩
      ihave %Hargs := output_args_bounded args values $$ Hargs
      ipureintro
      simp only [DivRemFV.CaptureSyntax.Term.words,bounded_cons]
      exact ⟨by decide,Hargs⟩
    | difference head tail =>
      isimp only [OutputTerm] at Hmodel
      icases Hmodel with ⟨%first,%rest,_,_,Hhead,Htail⟩
      ihave %Hhead := output_term_bounded head first $$ Hhead
      ihave %Htail := output_args_bounded tail rest $$ Htail
      ipureintro
      simp only [DivRemFV.CaptureSyntax.Term.words,bounded_cons,bounded_append]
      exact ⟨by decide,Hhead,Htail⟩

  theorem output_args_bounded (model : ModelArgs) (values : List Term) :
      OutputArgs (GF := GF) model values ⊢ iprop(⌜WordsBounded model.words⌝) := by
    iintro Hmodel
    cases model with
    | nil =>
      ipureintro
      change WordsBounded [0]
      exact (bounded_cons _ _).2 ⟨by decide,bounded_nil⟩
    | cons head tail =>
      cases values with
      | nil =>
        isimp only [OutputArgs] at Hmodel
        icases Hmodel with ⟨⟩
      | cons first rest =>
        isimp only [OutputArgs] at Hmodel
        icases Hmodel with ⟨Hhead,Htail⟩
        ihave %Hhead := output_term_bounded head first $$ Hhead
        ihave %Htail := output_args_bounded tail rest $$ Htail
        ipureintro
        simp only [DivRemFV.CaptureSyntax.Args.words,bounded_cons,bounded_append]
        exact ⟨by decide,Hhead,Htail⟩
end

theorem list_models_pure {A B : Type} (relation : A → B → IProp GF) (property : A → Prop)
    (proof : ∀ model value, relation model value ⊢ iprop(⌜property model⌝))
    (models : List A) (values : List B) :
    (iprop([∗list] _k ↦ model;value ∈ models;values, relation model value) : IProp GF) ⊢
      iprop(⌜∀ model ∈ models, property model⌝) := by
  induction models generalizing values with
  | nil => iintro _; ipureintro; simp
  | cons head tail ih =>
    cases values with
    | nil => iintro H; icases H with ⟨⟩
    | cons first rest =>
      iintro ⟨Hhead,Htail⟩
      ihave %Hhead := proof head first $$ Hhead
      ihave %Htail := ih rest $$ Htail
      ipureintro
      simpa only [List.forall_mem_cons] using And.intro Hhead Htail

#print axioms output_term_bounded
#print axioms output_args_bounded

theorem list_models_pure_member {A B : Type} (relation : A → B → IProp GF) (property : A → Prop)
    (models : List A) (values : List B)
    (proof : ∀ model ∈ models, ∀ value, relation model value ⊢ iprop(⌜property model⌝)) :
    (iprop([∗list] _k ↦ model;value ∈ models;values, relation model value) : IProp GF) ⊢
      iprop(⌜∀ model ∈ models, property model⌝) := by
  cases models with
  | nil => iintro _; ipureintro; simp
  | cons head tail =>
    cases values with
    | nil => iintro H; icases H with ⟨⟩
    | cons first rest =>
      iintro ⟨Hhead,Htail⟩
      ihave %Hhead := proof head (by simp) first $$ Hhead
      ihave %Htail := list_models_pure_member relation property tail rest
        (fun m member v => proof m (List.mem_cons_of_mem head member) v) $$ Htail
      ipureintro
      simpa only [List.forall_mem_cons] using And.intro Hhead Htail
termination_by models.length
end
end divremfv.internal.airdata.SourceCapture
end Perennial

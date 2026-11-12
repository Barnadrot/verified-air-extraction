module
public import CaptureClosure.Proof.WordBounds

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

theorem bounded_flatMap {A : Type} (values : List A) (encode : A → List Nat)
    (bounded : ∀ value ∈ values, WordsBounded (encode value)) : WordsBounded (values.flatMap encode) := by
  intro n member
  rcases List.mem_flatMap.mp member with ⟨value,hvalue,hn⟩
  exact bounded value hvalue n hn

theorem flatMap_member_length {A : Type} (values : List A) (encode : A → List Nat) (value : A)
    (member : value ∈ values) : (encode value).length ≤ (values.flatMap encode).length := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.flatMap_cons,List.length_append]
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have := ih member; omega

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem column_bounded (model : DivRemFV.CaptureSyntax.Column) (value : Column) (dq : DFrac) :
    ColumnValue (GF := GF) model value dq ⊢ iprop(⌜WordsBounded model.words⌝) := by
  iintro Hmodel
  isimp only [ColumnValue] at Hmodel
  icases Hmodel with ⟨%bits,⟨%Heq,%Hlen⟩,_⟩
  subst model
  ipureintro
  have Hid : WordsBounded [value.ID'.toNat] := (bounded_cons _ _).2 ⟨bounded_word _,bounded_nil⟩
  simpa only [portableColumn,DivRemFV.CaptureSyntax.Column.words,bounded_append] using
    And.intro (And.intro (And.intro (And.intro (And.intro Hid (bounded_name value.Name' Hlen))
      (bounded_optional bits)) (bounded_bool value.Input')) (bounded_bool value.Output')) (bounded_bool value.Native')

theorem port_bounded (model : DivRemFV.CaptureSyntax.Port) (value : Vector) (dq : DFrac) :
    PortValue (GF := GF) model value dq ⊢ iprop(⌜WordsBounded model.words⌝) := by
  iintro Hmodel
  isimp only [PortValue] at Hmodel
  icases Hmodel with ⟨%selector,%columns,%Heq,_,Hcolumns⟩
  ihave %Hlen := ownSlice_len $$ Hcolumns
  subst model
  ipureintro
  have Hid : WordsBounded [value.Module'.toNat] := (bounded_cons _ _).2 ⟨bounded_word _,bounded_nil⟩
  have Hcolumns : WordsBounded (columns.map BitVec.toNat) := by
    intro n member
    rcases List.mem_map.mp member with ⟨word,_,rfl⟩
    exact bounded_word word
  have Hcount : (columns.map BitVec.toNat).length < 2^64 := by simp only [List.length_map]; word
  simpa only [portablePort,DivRemFV.CaptureSyntax.Port.words,bounded_append] using
    And.intro (And.intro Hid (bounded_optional selector)) (bounded_natWords _ Hcount Hcolumns)

theorem row_bounded (model : List Nat) (value : GoSlice) (dq : DFrac) :
    RowValue (GF := GF) model value dq ⊢ iprop(⌜WordsBounded (DivRemFV.CaptureSyntax.natWords model)⌝) := by
  iintro Hmodel
  isimp only [RowValue] at Hmodel
  icases Hmodel with ⟨%words,%Heq,Hwords⟩
  ihave %Hlen := ownSlice_len $$ Hwords
  subst model
  ipureintro
  apply bounded_natWords
  · simp only [List.length_map]; word
  · intro n member
    rcases List.mem_map.mp member with ⟨word,_,rfl⟩
    exact bounded_word word

theorem module_bounded (model : DivRemFV.CaptureSyntax.Module) (value : Module) (dq : DFrac) :
    ModuleValue (GF := GF) model value dq ⊢ iprop(⌜WordsBounded model.words⌝) := by
  iintro Hmodel
  isimp only [ModuleValue] at Hmodel
  icases Hmodel with ⟨%columns,%rows,%columnValues,%rowValues,⟨%Heq,%HnameLen⟩,
    Hcolumns,HcolumnModels,Hrows,HrowModels⟩
  ihave %HcolumnLen := ownSlice_len $$ Hcolumns
  ihave %HrowLen := ownSlice_len $$ Hrows
  ihave %HcolumnCount := BigSepL2.bigSepL2_length $$ HcolumnModels
  ihave %HrowCount := BigSepL2.bigSepL2_length $$ HrowModels
  ihave %HcolumnBounds := list_models_pure (fun m v => ColumnValue m v dq)
    (fun m => WordsBounded m.words) (fun m v => column_bounded m v dq) columns columnValues $$ HcolumnModels
  ihave %HrowBounds := list_models_pure (fun m v => RowValue m v dq)
    (fun m => WordsBounded (DivRemFV.CaptureSyntax.natWords m)) (fun m v => row_bounded m v dq) rows rowValues $$ HrowModels
  subst model
  ipureintro
  have Hid : WordsBounded [value.ID'.toNat] := (bounded_cons _ _).2 ⟨bounded_word _,bounded_nil⟩
  have Hcolumns := (bounded_cons _ _).2
    ⟨(show columns.length < 2^64 by word),bounded_flatMap columns DivRemFV.CaptureSyntax.Column.words HcolumnBounds⟩
  have Hrows := (bounded_cons _ _).2
    ⟨(show rows.length < 2^64 by word),bounded_flatMap rows DivRemFV.CaptureSyntax.natWords HrowBounds⟩
  simpa only [portableModule,DivRemFV.CaptureSyntax.Module.words,bounded_append] using
    And.intro (And.intro (And.intro (And.intro (And.intro Hid (bounded_name value.Name' HnameLen))
      (bounded_bool value.Static')) (bounded_bool value.Native')) Hcolumns) Hrows

theorem rule_bounded (model : DivRemFV.CaptureSyntax.Rule) (value : Constraint) (dq : DFrac)
    (size : model.words.length < 2^64) :
    RuleValue (GF := GF) model value dq ⊢ iprop(⌜WordsBounded model.words⌝) := by
  iintro Hmodel
  cases model with
  | vanishing owner domain term =>
    isimp only [RuleValue] at Hmodel
    icases Hmodel with ⟨%rawDomain,%expression,⟨_,%Howner,%Hdomain,_⟩,_,_,Hterm⟩
    ihave %HtermBounds := output_term_bounded term expression $$ Hterm
    ipureintro
    have HtermSize : term.words.length < 2^64 := by
      simp only [DivRemFV.CaptureSyntax.Rule.words,DivRemFV.CaptureSyntax.natWords,List.length_append,List.length_cons] at size
      omega
    have Hprefix : WordsBounded [0,owner] := by
      rw [Howner]
      simp only [bounded_cons,bounded_nil,and_true]
      exact ⟨by decide,bounded_word _⟩
    simpa only [DivRemFV.CaptureSyntax.Rule.words,Hdomain,bounded_append] using
      And.intro (And.intro Hprefix (bounded_domain rawDomain)) (bounded_natWords _ HtermSize HtermBounds)
  | range owner column bits =>
    isimp only [RuleValue] at Hmodel
    icases Hmodel with ⟨_,%Howner,%Hcolumn,%Hbits⟩
    ipureintro
    simp only [DivRemFV.CaptureSyntax.Rule.words,bounded_cons,bounded_nil,and_true,Howner,Hcolumn,Hbits]
    exact ⟨by decide,by decide,bounded_word _,bounded_word _,bounded_word _⟩
  | lookup sources targets | bus sources targets =>
    isimp only [RuleValue] at Hmodel
    icases Hmodel with ⟨%sourceValues,%targetValues,_,Hsources,HsourceModels,Htargets,HtargetModels⟩
    ihave %HsourceLen := ownSlice_len $$ Hsources
    ihave %HtargetLen := ownSlice_len $$ Htargets
    ihave %HsourceCount := BigSepL2.bigSepL2_length $$ HsourceModels
    ihave %HtargetCount := BigSepL2.bigSepL2_length $$ HtargetModels
    ihave %HsourceBounds := list_models_pure (fun m v => PortValue m v dq)
      (fun m => WordsBounded m.words) (fun m v => port_bounded m v dq) sources sourceValues $$ HsourceModels
    ihave %HtargetBounds := list_models_pure (fun m v => PortValue m v dq)
      (fun m => WordsBounded m.words) (fun m v => port_bounded m v dq) targets targetValues $$ HtargetModels
    ipureintro
    have Hsources := bounded_flatMap sources DivRemFV.CaptureSyntax.Port.words HsourceBounds
    have Htargets := (bounded_cons _ _).2
      ⟨(show targets.length < 2^64 by word),bounded_flatMap targets DivRemFV.CaptureSyntax.Port.words HtargetBounds⟩
    simp only [DivRemFV.CaptureSyntax.Rule.words,bounded_append,bounded_cons,bounded_nil,_root_.and_true]
    exact ⟨⟨⟨by decide,by decide,by decide,by word⟩,Hsources⟩,(bounded_cons _ _).1 Htargets⟩

theorem entry_bounded (model : DivRemFV.CaptureSyntax.Entry) (value : Constraint) (dq : DFrac)
    (size : model.words.length < 2^64) :
    EntryValue (GF := GF) model value dq ⊢ iprop(⌜WordsBounded model.words⌝) := by
  iintro Hmodel
  isimp only [EntryValue] at Hmodel
  icases Hmodel with ⟨⟨%Hid,%Howner,%Hname,%Hlen⟩,Hrule⟩
  have HruleSize : model.rule.words.length < 2^64 := by
    simp only [DivRemFV.CaptureSyntax.Entry.words,List.length_append] at size
    omega
  ihave %HruleBound := rule_bounded model.rule value dq HruleSize $$ Hrule
  ipureintro
  have Hprefix : WordsBounded [model.id,model.owner] := by
    simp only [Hid,Howner,bounded_cons,bounded_nil,and_true]
    exact ⟨bounded_word _,bounded_word _⟩
  simpa only [DivRemFV.CaptureSyntax.Entry.words,Hname,bounded_append] using
    And.intro (And.intro Hprefix (bounded_name value.Name' Hlen)) HruleBound

#print axioms module_bounded
#print axioms entry_bounded
end
end divremfv.internal.airdata.SourceCapture
end Perennial

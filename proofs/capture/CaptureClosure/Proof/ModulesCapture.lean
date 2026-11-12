module
public import CaptureClosure.Proof.ModuleCapture
public import CaptureClosure.Proof.ModulesWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
open github_com.LFDT_Lineth.zkc.pkg.schema.register

def tableModels [FfiSyntax] (tables : List TableData) (inputTag outputTag : Type') :
    List DivRemFV.CaptureSyntax.Module :=
  tables.mapIdx (fun i data => tableModel (W64 i) data inputTag outputTag)

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
abbrev InputModules (models : List TableData) (values : List Loc) : IProp GF :=
  iprop([∗list] _k ↦ data;value ∈ models;values, InputModule data value)

variable [Module.TypeAssumptions] [Column.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.Table.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.register.«Type».TypeAssumptions] [Register.TypeAssumptions]
variable [FuncUnfold exportModules [] exportModules.impl]
variable [FuncUnfold exportModule [] exportModule.impl]
variable [FuncUnfold exportColumns [] exportColumns.impl]
variable [FuncUnfold exportColumn [] exportColumn.impl]
variable [FuncUnfold exportStaticRows [] exportStaticRows.impl]
variable [FuncUnfold exportStaticRow [] exportStaticRow.impl]
variable [FuncUnfold github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.montgomeryReduce []
  github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.montgomeryReduce.impl]
variable [FuncUnfold math.bits.Sub32 [] math.bits.Sub32.impl]

theorem capture_modules (sl : GoSlice) (tables : List TableData) (sources : List Loc) (inputTag outputTag : Type') :
    {{ (sl ↦*□ sources ∗ InputModules tables sources ∗ globalAddr INPUT_REGISTER ↦□ inputTag ∗
        globalAddr OUTPUT_REGISTER ↦□ outputTag : IProp GF) }}
      (App (Val (@! exportModules)) (Val #sl))
    {{ (result : GoSlice), RET #result; ∃ values : List Module,
      result ↦* values ∗ ownSliceCap Module result (DFrac.own 1) ∗
      ModulesValue (tableModels tables inputTag outputTag) values (DFrac.own 1) }} := by
  wp_start as ⟨#Hsource,#Hinputs,#Hinput,#Houtput⟩
  ihave %Hlen := ownSlice_len $$ Hsource
  ihave %HmodelLen := BigSepL2.bigSepL2_length $$ Hinputs
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Module.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Module) (t := Module.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %empty ⟨Hout,Hcap⟩
  wp_auto
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : Loc) (values : List Module) (key : w64),
      "i" ∷ i_ptr ↦ n ∗ "mid" ∷ mid_ptr ↦ key ∗ "out" ∷ out_ptr ↦ current ∗ "m" ∷ m_ptr ↦ last ∗
      "Hout" ∷ current ↦* values ∗ "Hcap" ∷ ownSliceCap Module current (DFrac.own 1) ∗
      "Hmodels" ∷ ModulesValue ((tableModels tables inputTag outputTag).take (sint.nat n)) values (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i mid out m Hout Hcap]
  · iexists (W64 0),_,null,[],(W64 0)
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero]
    iframe
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < sources.length := by word
    have Hmlt : sint.nat n < tables.length := by word
    have Hlookup := List.getElem?_eq_getElem Hlt
    have Hmodel := List.getElem?_eq_getElem Hmlt
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1,Hif⟩,_root_.and_self,ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) sources DFrac.discard sources[sint.nat n] Hn.1 with _
    · iframe Hsource; ipureintro; exact Hlookup
    ihave #Hchild := BigSepL2.bigSepL2_lookup Hmodel Hlookup $$ Hinputs
    wp_apply (capture_module n tables[sint.nat n] sources[sint.nat n] inputTag outputTag)
      with %value Hvalue
    · iframe Hchild Hinput Houtput
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Module.ty)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Module) (t := Module.ty) [value]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %item ⟨Hitem,HitemCap⟩
    wp_auto
    wp_apply wp_slice_append (V := Module) (st := go.SliceType Module.ty) (t := Module.ty)
      current values _ [value] (DFrac.own 1) $$ [Hout Hcap Hitem] with %result ⟨Hout,Hcap,Hitem⟩
    · iframe Hout Hcap Hitem
    wp_for_post
    iframe
    iexists (n + W64 1),result,sources[sint.nat n],(values ++ [value]),n
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have HvalueLookup : (tableModels tables inputTag outputTag)[sint.nat n]? =
        some (tableModel n tables[sint.nat n] inputTag outputTag) := by
      simp [tableModels,List.getElem?_mapIdx,Hmodel]
      have Hcast : BitVec.ofNat 64 (sint.nat n) = n := by word
      rw [Hcast]
    rw [Hstep,List.take_add_one,HvalueLookup]
    simp only [Option.toList_some]
    ihave Hnext : ModulesValue
        ((tableModels tables inputTag outputTag).take (sint.nat n) ++ [tableModel n tables[sint.nat n] inputTag outputTag])
        (values ++ [value]) (DFrac.own 1) $$ [Hmodels Hvalue]
    · iapply BigSepL2.bigSepL2_snoc.2; iframe Hmodels Hvalue
    iframe
    ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = (tableModels tables inputTag outputTag).length := by simp [tableModels]; word
    isimp only [Heq,List.take_length] at Hmodels
    iapply HΦ
    iexists values
    iframe Hout Hcap Hmodels

#print axioms capture_modules
end
end divremfv.internal.airdata.SourceCapture
end Perennial

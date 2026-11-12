module
public import CaptureClosure.Proof.ColumnCapture
public import CaptureClosure.Proof.ColumnsWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
open github_com.LFDT_Lineth.zkc.pkg.schema.register

def registerColumns [FfiSyntax] (registers : List Register) (inputTag outputTag : Type') :
    List DivRemFV.CaptureSyntax.Column :=
  registers.mapIdx (fun i value => registerColumn (W64 i) value inputTag outputTag)

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Column.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.register.«Type».TypeAssumptions]
variable [Register.TypeAssumptions]
variable [FuncUnfold exportColumns [] exportColumns.impl]
variable [FuncUnfold exportColumn [] exportColumn.impl]

theorem capture_columns (sl : GoSlice) (registers : List Register) (inputTag outputTag : Type')
    (dq : DFrac) (bounded : ∀ value ∈ registers, value.name'.length < 2^63) :
    {{ (sl ↦*{dq} registers ∗ globalAddr INPUT_REGISTER ↦□ inputTag ∗
        globalAddr OUTPUT_REGISTER ↦□ outputTag : IProp GF) }}
      (App (Val (@! exportColumns)) (Val #sl))
    {{ (result : GoSlice), RET #result; ∃ values : List Column,
      result ↦* values ∗ ownSliceCap Column result (DFrac.own 1) ∗
      ColumnsValue (registerColumns registers inputTag outputTag) values (DFrac.own 1) ∗
      sl ↦*{dq} registers }} := by
  wp_start as ⟨Hsource,#Hinput,#Houtput⟩
  ihave %Hlen := ownSlice_len $$ Hsource
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Column.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Column) (t := Column.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %empty ⟨Hout,Hcap⟩
  wp_auto
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : Register) (values : List Column) (key : w64),
      "i" ∷ i_ptr ↦ n ∗ "rid" ∷ rid_ptr ↦ key ∗
      "columns" ∷ columns_ptr ↦ current ∗ "r" ∷ r_ptr ↦ last ∗
      "Hsource" ∷ sl ↦*{dq} registers ∗ "Hout" ∷ current ↦* values ∗
      "Hcap" ∷ ownSliceCap Column current (DFrac.own 1) ∗
      "Hmodels" ∷ ColumnsValue ((registerColumns registers inputTag outputTag).take (sint.nat n)) values (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝)
      $$ [i rid columns r Hsource Hout Hcap]
  · iexists (W64 0),_,zero_val Register,[],(W64 0)
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero]
    iframe
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < registers.length := by word
    have Hlookup := List.getElem?_eq_getElem Hlt
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1,Hif⟩,
      _root_.and_self,ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) registers dq registers[sint.nat n] Hn.1
      $$ [Hsource] with Hsource
    · iframe Hsource; ipureintro; exact Hlookup
    wp_apply (capture_column n registers[sint.nat n] inputTag outputTag
      (bounded _ (List.getElem_mem Hlt))) with %column Hcolumn
    · iframe Hinput Houtput
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Column.ty)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Column) (t := Column.ty) [column]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %item ⟨Hitem,HitemCap⟩
    wp_auto
    wp_apply wp_slice_append (V := Column) (st := go.SliceType Column.ty) (t := Column.ty)
      current values _ [column] (DFrac.own 1) $$ [Hout Hcap Hitem]
      with %result ⟨Hout,Hcap,Hitem⟩
    · iframe Hout Hcap Hitem
    wp_for_post
    iframe
    iexists (n + W64 1),result,registers[sint.nat n],(values ++ [column]),n
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hvalue : (registerColumns registers inputTag outputTag)[sint.nat n]? =
        some (registerColumn n registers[sint.nat n] inputTag outputTag) := by
      simp [registerColumns,List.getElem?_mapIdx,Hlookup]
      have Hcast : BitVec.ofNat 64 (sint.nat n) = n := by word
      rw [Hcast]
    rw [Hstep,List.take_add_one,Hvalue]
    simp only [Option.toList_some]
    ihave Hnext : ColumnsValue
        ((registerColumns registers inputTag outputTag).take (sint.nat n) ++
          [registerColumn n registers[sint.nat n] inputTag outputTag])
        (values ++ [column]) (DFrac.own 1) $$ [Hmodels Hcolumn]
    · iapply BigSepL2.bigSepL2_snoc.2; iframe Hmodels Hcolumn
    iframe
    ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = (registerColumns registers inputTag outputTag).length := by
      simp [registerColumns]; word
    isimp only [Heq,List.take_length] at Hmodels
    iapply HΦ
    iexists values
    iframe Hout Hcap Hmodels Hsource

#print axioms capture_columns
end
end divremfv.internal.airdata.SourceCapture
end Perennial

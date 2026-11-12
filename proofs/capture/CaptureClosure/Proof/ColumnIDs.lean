module
public import CaptureClosure.Proof.ColumnId
public import CaptureClosure.Code.divremfv.internal.airdata

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
open github_com.LFDT_Lineth.zkc.pkg.trace

def registerIds [FfiSyntax] (indices : List w64) : List ColumnId := indices.map ColumnId.mk

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [ColumnId.TypeAssumptions]
variable [FuncUnfold exportColumnIDs [] exportColumnIDs.impl]

theorem capture_column_ids (sl : GoSlice) (indices : List w64) (dq : DFrac)
    (valid : ∀ index ∈ indices, index ≠ W64 (2^64-1)) :
    {{ (sl ↦*{dq} registerIds indices : IProp GF) }}
      (App (Val (@! exportColumnIDs)) (Val #sl))
    {{ (result : GoSlice), RET #result;
      result ↦* indices ∗ ownSliceCap w64 result (DFrac.own 1) ∗ sl ↦*{dq} registerIds indices }} := by
  wp_start as Hsource
  ihave %Hlen := ownSlice_len $$ Hsource
  have HsourceLen : (registerIds indices).length = indices.length := by simp [registerIds]
  rw [HsourceLen] at Hlen
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := w64) (t := go.uint) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %empty ⟨Hout,Hcap⟩
  wp_auto
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : ColumnId),
      "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ current ∗ "r" ∷ r_ptr ↦ last ∗
      "Hsource" ∷ sl ↦*{dq} registerIds indices ∗
      "Hout" ∷ current ↦* (indices.take (sint.nat n)) ∗
      "Hcap" ∷ ownSliceCap w64 current (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝)
      $$ [i out r Hsource Hout Hcap]
  · iexists (W64 0),_,zero_val ColumnId
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < indices.length := by word
    have Hlookup : (registerIds indices)[sint.nat n]? = some (ColumnId.mk indices[sint.nat n]) := by
      simp [registerIds,List.getElem?_eq_getElem Hlt]
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1,Hif⟩,
      _root_.and_self,ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) (registerIds indices) dq
      (ColumnId.mk indices[sint.nat n]) Hn.1 $$ [Hsource] with Hsource
    · iframe Hsource; ipureintro; exact Hlookup
    wp_apply (ColumnId.unwrap_correct indices[sint.nat n]
      (valid _ (List.getElem_mem Hlt)))
    all_goals try itrivial
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w64) (t := go.uint) [indices[sint.nat n]]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %item ⟨Hitem,HitemCap⟩
    wp_auto
    wp_apply wp_slice_append (V := w64) (st := go.SliceType go.uint) (t := go.uint)
      current (indices.take (sint.nat n)) _ [indices[sint.nat n]] (DFrac.own 1)
      $$ [Hout Hcap Hitem] with %result ⟨Hout,Hcap,Hitem⟩
    · iframe Hout Hcap Hitem
    wp_for_post
    iframe
    iexists (n + W64 1),result,(ColumnId.mk indices[sint.nat n])
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hvalue := List.getElem?_eq_getElem Hlt
    rw [Hstep,List.take_add_one,Hvalue]
    simp only [Option.toList_some]
    iframe
    ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = indices.length := by word
    isimp only [Heq,List.take_length] at Hout
    iapply HΦ
    iframe Hout Hcap Hsource

#print axioms capture_column_ids
end
end divremfv.internal.airdata.SourceCapture
end Perennial

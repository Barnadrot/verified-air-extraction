module
public import CaptureClosure.Proof.LoadElement
public import CaptureClosure.Proof.FieldWord
public import CaptureClosure.Code.divremfv.internal.airdata

@[expose] public section
noncomputable section
set_option maxRecDepth 1000000
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
open github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear

def rowElements (raw : List w32) : List (GoArray w32 1) := raw.map (fun x => array.mk 1 [x])
def rowValues (raw : List w32) : List w64 := raw.map fieldWord

theorem rowValues_exact (raw : List w32) :
    rowValues raw = raw.map (fun x => W64 (decodedValue x.toNat)) := by
  simp only [rowValues]
  exact List.map_congr_left (fun value _ => fieldWord_value value)

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Element.TypeAssumptions]
variable [FuncUnfold exportStaticRow [] exportStaticRow.impl]
variable [FuncUnfold montgomeryReduce [] montgomeryReduce.impl]
variable [FuncUnfold math.bits.Sub32 [] math.bits.Sub32.impl]

theorem capture_static_row (sl : GoSlice) (raw : List w32) (dq : DFrac) :
    {{ (sl ↦*{dq} rowElements raw : IProp GF) }}
      (App (Val (@! exportStaticRow)) (Val #sl))
    {{ (result : GoSlice), RET #result;
      result ↦* rowValues raw ∗ ownSliceCap w64 result (DFrac.own 1) ∗ sl ↦*{dq} rowElements raw }} := by
  wp_start as Hsource
  ihave %Hlen := ownSlice_len $$ Hsource
  have HsourceLen : (rowElements raw).length = raw.length := by simp [rowElements]
  rw [HsourceLen] at Hlen
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint64)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := w64) (t := go.uint64) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %empty ⟨Hout,Hcap⟩
  wp_auto
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : w32),
      "i" ∷ i_ptr ↦ n ∗ "values" ∷ values_ptr ↦ current ∗ "value" ∷ value_ptr ↦ (array.mk 1 [last]) ∗
      "Hsource" ∷ sl ↦*{dq} rowElements raw ∗
      "Hout" ∷ current ↦* ((rowValues raw).take (sint.nat n)) ∗
      "Hcap" ∷ ownSliceCap w64 current (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝)
      $$ [i values value Hsource Hout Hcap]
  · iexists (W64 0),_,(W32 0)
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < raw.length := by word
    have Hlookup : (rowElements raw)[sint.nat n]? = some (array.mk 1 [raw[sint.nat n]]) := by
      simp [rowElements,List.getElem?_eq_getElem Hlt]
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1,Hif⟩,
      _root_.and_self,ite_true]
    wp_apply (load_element sl (sint.Z n) (rowElements raw) raw[sint.nat n] dq Hn.1)
      $$ [Hsource] with Hsource
    · iframe Hsource; ipureintro; exact Hlookup
    wp_apply Element.word_capture raw[sint.nat n]
    all_goals try itrivial
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint64)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w64) (t := go.uint64) [fieldWord raw[sint.nat n]]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %item ⟨Hitem,HitemCap⟩
    wp_auto
    wp_apply wp_slice_append (V := w64) (st := go.SliceType go.uint64) (t := go.uint64)
      current ((rowValues raw).take (sint.nat n)) _ [fieldWord raw[sint.nat n]] (DFrac.own 1)
      $$ [Hout Hcap Hitem] with %result ⟨Hout,Hcap,Hitem⟩
    · iframe Hout Hcap Hitem
    wp_for_post
    iframe
    iexists (n + W64 1),result,raw[sint.nat n]
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hvalue : (rowValues raw)[sint.nat n]? = some (fieldWord raw[sint.nat n]) := by
      simp [rowValues,List.getElem?_eq_getElem Hlt]
    rw [Hstep,List.take_add_one,Hvalue]
    simp only [Option.toList_some]
    iframe
    ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = (rowValues raw).length := by simp [rowValues]; word
    isimp only [Heq,List.take_length] at Hout
    iapply HΦ
    iframe Hout Hcap Hsource

#print axioms capture_static_row
end
end divremfv.internal.airdata.SourceCapture
end Perennial

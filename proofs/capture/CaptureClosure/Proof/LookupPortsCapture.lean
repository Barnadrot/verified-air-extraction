module
public import CaptureClosure.Proof.PortCapture

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port.TypeAssumptions]
variable [FuncUnfold lookupVector [] lookupVector.impl]
variable [FuncUnfold busVector [] busVector.impl]
variable [FuncUnfold uintRef [] uintRef.impl]
variable [FuncUnfold exportColumnIDs [] exportColumnIDs.impl]
variable [FuncUnfold exportLookupVectors [] exportLookupVectors.impl]

abbrev InputLookupPorts (models : List DivRemFV.CaptureSyntax.Port) (values : List github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) : IProp GF :=
  iprop([∗list] _k ↦ model;value ∈ models;values, InputLookupPort model value)

theorem capture_lookup_ports (sl : GoSlice) (models : List DivRemFV.CaptureSyntax.Port) (sources : List github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (dq : DFrac) :
    {{ (sl ↦*{dq} sources ∗ InputLookupPorts models sources : IProp GF) }}
      (App (Val (@! exportLookupVectors)) (Val #sl))
    {{ (result : GoSlice), RET #result; ∃ values : List Vector,
      result ↦* values ∗ ownSliceCap Vector result (DFrac.own 1) ∗
      PortsValue (models) values (DFrac.own 1) ∗
      sl ↦*{dq} sources ∗ InputLookupPorts models sources }} := by
  wp_start as ⟨Hsource,Hinputs⟩
  ihave %Hlen := ownSlice_len $$ Hsource
  ihave %HmodelLen := BigSepL2.bigSepL2_length $$ Hinputs
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Vector.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Vector) (t := Vector.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %empty ⟨Hout,Hcap⟩
  wp_auto
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (values : List Vector),
      "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ current ∗ "v" ∷ v_ptr ↦ last ∗
      "Hsource" ∷ sl ↦*{dq} sources ∗ "Hinputs" ∷ InputLookupPorts models sources ∗
      "Hout" ∷ current ↦* values ∗ "Hcap" ∷ ownSliceCap Vector current (DFrac.own 1) ∗
      "Hmodels" ∷ PortsValue ((models).take (sint.nat n)) values (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝)
      $$ [i out v Hsource Hinputs Hout Hcap]
  · iexists (W64 0),_,zero_val github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector,[]
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero]
    iframe
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < sources.length := by word
    have Hmlt : sint.nat n < models.length := by word
    have Hlookup := List.getElem?_eq_getElem Hlt
    have Hmodel := List.getElem?_eq_getElem Hmlt
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1,Hif⟩,
      _root_.and_self,ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) sources dq sources[sint.nat n] Hn.1
      $$ [Hsource] with Hsource
    · iframe Hsource; ipureintro; exact Hlookup
    ihave ⟨Hchild,Hrestore⟩ := BigSepL2.bigSepL2_lookup_acc Hmodel Hlookup $$ Hinputs
    wp_apply (capture_lookup_model models[sint.nat n] sources[sint.nat n])
      $$ [Hchild] with %row ⟨Hrow,Hchild⟩
    · iframe Hchild
    ihave Hinputs := Hrestore $$ Hchild
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Vector.ty)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Vector) (t := Vector.ty) [row]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %item ⟨Hitem,HitemCap⟩
    wp_auto
    wp_apply wp_slice_append (V := Vector) (st := go.SliceType Vector.ty) (t := Vector.ty)
      current values _ [row] (DFrac.own 1) $$ [Hout Hcap Hitem]
      with %result ⟨Hout,Hcap,Hitem⟩
    · iframe Hout Hcap Hitem
    wp_for_post
    iframe
    iexists (n + W64 1),result,sources[sint.nat n],(values ++ [row])
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hvalue := List.getElem?_eq_getElem Hmlt
    rw [Hstep,List.take_add_one,Hvalue]
    simp only [Option.toList_some]
    ihave Hnext : PortsValue
        ((models).take (sint.nat n) ++ [models[sint.nat n]])
        (values ++ [row]) (DFrac.own 1) $$ [Hmodels Hrow]
    · iapply BigSepL2.bigSepL2_snoc.2
      iframe Hmodels Hrow
    iframe
    ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = (models).length := by word
    isimp only [Heq,List.take_length] at Hmodels
    iapply HΦ
    iexists values
    iframe Hout Hcap Hmodels Hsource Hinputs

#print axioms capture_lookup_ports
end
end divremfv.internal.airdata.SourceCapture
end Perennial

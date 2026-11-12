module
public import CaptureClosure.Proof.TermLoopSource

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [Term.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.TypeAssumptions]
variable [FuncUnfold ExportTerm [] ExportTerm.impl]
local notation "FType" => github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty
local notation "Air" => github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.ty FType

theorem capture_args (models : List ModelTerm) (sources : List GoInterface) (sl : GoSlice)
    (out arg : Loc) (initial : Term)
    (calls : ∀ model ∈ models, ∀ source : GoInterface,
      ⊢ iprop({{ InputTerm (GF := GF) model source }}
        (App (Val (@! ExportTerm)) (Val #source))
        {{ (result : Term), RET (PairV #result #interface.nil); OutputTerm model result }})) :
    {{ (sl ↦*□ sources ∗ InputList models sources ∗ out ↦ initial ∗
        initial.Args' ↦* ([] : List Term) ∗ ownSliceCap Term initial.Args' (DFrac.own 1) ∗
        arg ↦ (interface.nil : GoInterface) : IProp GF) }}
      (App (App (Val (slice.forRange Air)) (Val #sl)) (Val (captureArgsBody out arg)))
    {{ (args : GoSlice) (results : List Term), RET executeVal;
      out ↦ ({ initial with Args' := args } : Term) ∗ args ↦* results ∗
      ownSliceCap Term args (DFrac.own 1) ∗ OutputList models results }} := by
  simp only [captureArgsBody,captureArgsExpr,subst,subst',substKeyedElements,
    substKeyedElement,substOptKey,substElement]
  iintro %Φ ⟨#Hsl,#Hinputs,Hout,Hargs,Hcap,Harg⟩ HΦ
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hmodels := BigSepL2.bigSepL2_length $$ Hinputs
  wp_auto
  ihave IH : iprop(∃ (n : w64) (args : GoSlice) (results : List Term) (last : GoInterface),
      "i" ∷ i_ptr ↦ n ∗ "Hout" ∷ out ↦ ({ initial with Args' := args } : Term) ∗
      "Hargs" ∷ args ↦* results ∗ "Hcap" ∷ ownSliceCap Term args (DFrac.own 1) ∗
      "Hresults" ∷ OutputList (models.take (sint.nat n)) results ∗
      "Harg" ∷ arg ↦ last ∗ "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝)
      $$ [i Hout Hargs Hcap Harg]
  · iexists (W64 0),initial.Args',[],interface.nil
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero]
    iframe
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    · ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Htest := Hif
    have Hlt : sint.nat n < sources.length := by word
    have Hsource := List.getElem?_eq_getElem Hlt
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1,Htest⟩,
      _root_.and_self,ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) sources DFrac.discard sources[sint.nat n] Hn.1
      $$ [Hsl] with Hsl
    · iframe Hsl; ipureintro; exact Hsource
    ihave ⟨%model,⟨%Hmodel,#Hnode⟩⟩ := BigSepL2.bigSepL2_lookup_right Hsource $$ Hinputs
    have Hmem : model ∈ models := List.mem_of_getElem? Hmodel
    try wp_auto
    wp_apply (calls model Hmem _) $$ Hnode with %captured Hcaptured
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Term.ty)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Term) (t := Term.ty) [captured]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %one ⟨Hone,HoneCap⟩
    wp_auto
    wp_apply wp_slice_append (V := Term) (st := go.SliceType Term.ty) (t := Term.ty)
      args results _ [captured] (DFrac.own 1) $$ [Hargs Hcap Hone] with %next ⟨Hargs,Hcap,Hone⟩
    · iframe Hargs Hcap Hone
    wp_for_post
    iframe
    iexists (n + W64 1),next,(results ++ [captured]),sources[sint.nat n]
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [Hstep,List.take_add_one,Hmodel]
    simp only [Option.toList_some]
    iframe
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2
      itrivial
    · ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = models.length := by word
    try simp only [decide_true,ite_true]
    iapply HΦ
    isimp only [Heq,List.take_length] at Hresults
    iframe Hout Hargs Hcap Hresults

end
end divremfv.internal.airdata.SourceCapture
end Perennial

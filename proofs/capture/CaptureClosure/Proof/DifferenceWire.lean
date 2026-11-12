module
public import CaptureClosure.Proof.CompositeWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Term.TypeAssumptions]
variable [FuncUnfold appendTermWire [] appendTermWire.impl]
variable [FuncUnfold appendArgsWire [] appendArgsWire.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

theorem append_difference (out : GoSlice) (prior : List w8) (sl : GoSlice)
    (first : ModelTerm) (rest : ModelArgs) (head : Term) (tail : List Term)
    (calls : ∀ model ∈ first :: rest.toList, ∀ (out : GoSlice) (prior : List w8) (value : Term),
      ⊢ iprop({{ out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ OutputTerm (GF := GF) model value }}
        (App (App (Val (@! appendTermWire)) (Val #out)) (Val #value))
        {{ (result : GoSlice), RET (PairV #result #interface.nil);
          result ↦* (prior ++ wireBytes model.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OutputTerm model value }})) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ sl ↦* (head :: tail) ∗
        OutputTerm first head ∗ OutputArgs rest tail : IProp GF) }}
      (App (App (Val (@! appendTermWire)) (Val #out))
        (Val #(Term.mk go!"sub" (W64 0) (W64 0) (W64 0) sl)))
    {{ (result : GoSlice), RET (PairV #result #interface.nil);
      result ↦* (prior ++ wireBytes (DivRemFV.CaptureSyntax.Term.difference first rest).words) ∗
      ownSliceCap w8 result (DFrac.own 1) ∗ sl ↦* (head :: tail) ∗
      OutputTerm first head ∗ OutputArgs rest tail }} := by
  wp_start as ⟨Hout,Hcap,Hsl,Hhead,Hrest⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hwf := ownSlice_wf $$ Hsl
  ihave Hlist := (output_args_list rest tail).1 $$ Hrest
  have Hnonzero : sl.len ≠ W64 0 := by simp only [List.length_cons] at Hlen; word
  have Hpositive : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z sl.len := by
    simp only [List.length_cons] at Hlen
    constructor <;> word
  wp_auto
  rw [decide_eq_false Hnonzero]
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by word,by word⟩,
    _root_.and_self,ite_true]
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) (head :: tail) (DFrac.own 1) head (by word)
    $$ [Hsl] with Hsl
  · iframe Hsl; ipureintro; rfl
  wp_apply (calls first (by simp) _ _ head) $$ [Hout Hcap Hhead]
    with %next ⟨Hout,Hcap,Hhead⟩
  · iframe Hout Hcap Hhead
  ihave ⟨Hprefix,Htail⟩ := (ownSlice_split_all (W64 1) sl (DFrac.own 1) (head :: tail) Hpositive).1 $$ Hsl
  isimp only [show sint.nat (W64 1) = 1 from rfl,List.take_succ_cons,List.take_zero,
    List.drop_succ_cons,List.drop_zero] at Hprefix Htail
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z sl.len ∧
      sint.Z sl.len ≤ sint.Z sl.cap from ⟨Hpositive.1,Hpositive.2,Hwf.2⟩)]
  try wp_auto
  wp_apply (append_args _ _ (slice.slice sl Term (W64 1) sl.len) (DFrac.own 1) rest.toList tail
    (fun model inside => calls model (List.mem_cons_of_mem first inside)))
    $$ [Hout Hcap Htail Hlist] with %result ⟨Hout,Hcap,Htail,Hlist⟩
  · iframe Hout Hcap Htail Hlist
  ihave Hsl : iprop(sl ↦* (head :: tail)) $$ [Hprefix Htail]
  · iapply (ownSlice_split_all (W64 1) sl (DFrac.own 1) (head :: tail) Hpositive).2
    simp only [show sint.nat (W64 1) = 1 from rfl,List.take_succ_cons,List.take_zero,
      List.drop_succ_cons,List.drop_zero]
    iframe Hprefix Htail
  iapply HΦ
  isimp only [List.append_assoc] at Hout
  simp only [DivRemFV.CaptureSyntax.Term.words,args_words,wireBytes_cons,wireBytes_append,List.append_assoc]
  iframe Hout Hcap Hsl Hhead
  iapply (output_args_list rest tail).2
  iexact Hlist

#print axioms append_difference
end
end divremfv.internal.airdata.SourceCapture
end Perennial

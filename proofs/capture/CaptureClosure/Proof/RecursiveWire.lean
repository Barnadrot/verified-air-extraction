module
public import CaptureClosure.Proof.DifferenceWire
public import CaptureClosure.Proof.WireNumbers

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

mutual
  theorem wire_term (model : ModelTerm) (out : GoSlice) (prior : List w8) (value : Term) :
      ⊢ iprop({{ out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ OutputTerm (GF := GF) model value }}
        (App (App (Val (@! appendTermWire)) (Val #out)) (Val #value))
        {{ (result : GoSlice), RET (PairV #result #interface.nil);
          result ↦* (prior ++ wireBytes model.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OutputTerm model value }}) := by
    cases model with
    | constant c =>
      cases value with | mk kind stored index offset args =>
      imodintro
      iintro %Φ ⟨Hout,Hcap,Hmodel⟩ HΦ
      iunfold OutputTerm at Hmodel
      icases Hmodel with ⟨⟨%Hkind,%Hstored,%Hindex,%Hoffset⟩,Hargs⟩
      dsimp only at Hkind Hstored Hindex Hoffset
      subst kind; subst stored; subst index; subst offset
      wp_apply (append_constant out prior c args) $$ [Hout Hcap Hargs]
        with %result ⟨Hout,Hcap,Hargs⟩
      · iframe Hout Hcap Hargs
      iapply HΦ
      isimp only [List.append_assoc] at Hout
      simp only [DivRemFV.CaptureSyntax.Term.words,wireBytes_cons,wireBytes_nil,List.append_nil,List.append_assoc]
      iframe Hout Hcap
      simp only [OutputTerm]
      isplitl []
      · ipureintro; trivial
      iexact Hargs
    | column id shift =>
      cases value with | mk kind stored index offset args =>
      imodintro
      iintro %Φ ⟨Hout,Hcap,Hmodel⟩ HΦ
      iunfold OutputTerm at Hmodel
      icases Hmodel with ⟨⟨%Hkind,%Hstored,%Hindex,%Hoffset⟩,Hargs⟩
      dsimp only at Hkind Hstored Hindex Hoffset
      subst kind; subst stored
      wp_apply (append_column out prior index offset args) $$ [Hout Hcap Hargs]
        with %result ⟨Hout,Hcap,Hargs⟩
      · iframe Hout Hcap Hargs
      have HindexWord : W64 id = index := by rw [← Hindex]; word
      have HshiftWord : W64 (DivRemFV.CaptureSyntax.encodeInt shift) = zigzagWord offset := by
        rw [← Hoffset,← zigzag_word_value]
        word
      iapply HΦ
      isimp only [List.append_assoc] at Hout
      simp only [DivRemFV.CaptureSyntax.Term.words,wireBytes_cons,wireBytes_nil,List.append_nil,
        HindexWord,HshiftWord,List.append_assoc]
      iframe Hout Hcap
      simp only [OutputTerm]
      isplitl []
      · ipureintro; simp [Hindex,Hoffset]
      iexact Hargs
    | sum models =>
      cases value with | mk kind stored index offset args =>
      imodintro
      iintro %Φ ⟨Hout,Hcap,Hmodel⟩ HΦ
      iunfold OutputTerm at Hmodel
      icases Hmodel with ⟨%values,⟨%Hkind,%Hstored,%Hindex,%Hoffset⟩,Hargs,Hvalues⟩
      dsimp only at Hkind Hstored Hindex Hoffset
      subst kind; subst stored; subst index; subst offset
      wp_apply (append_sum out prior args models values (wire_arg_calls models))
        $$ [Hout Hcap Hargs Hvalues] with %result ⟨Hout,Hcap,Hargs,Hvalues⟩
      · iframe Hout Hcap Hargs Hvalues
      iapply HΦ
      iframe Hout Hcap
      simp only [OutputTerm]
      iexists values
      isplitl []
      · ipureintro; trivial
      iframe Hargs Hvalues
    | product models =>
      cases value with | mk kind stored index offset args =>
      imodintro
      iintro %Φ ⟨Hout,Hcap,Hmodel⟩ HΦ
      iunfold OutputTerm at Hmodel
      icases Hmodel with ⟨%values,⟨%Hkind,%Hstored,%Hindex,%Hoffset⟩,Hargs,Hvalues⟩
      dsimp only at Hkind Hstored Hindex Hoffset
      subst kind; subst stored; subst index; subst offset
      wp_apply (append_product out prior args models values (wire_arg_calls models))
        $$ [Hout Hcap Hargs Hvalues] with %result ⟨Hout,Hcap,Hargs,Hvalues⟩
      · iframe Hout Hcap Hargs Hvalues
      iapply HΦ
      iframe Hout Hcap
      simp only [OutputTerm]
      iexists values
      isplitl []
      · ipureintro; trivial
      iframe Hargs Hvalues
    | difference first rest =>
      cases value with | mk kind stored index offset args =>
      imodintro
      iintro %Φ ⟨Hout,Hcap,Hmodel⟩ HΦ
      iunfold OutputTerm at Hmodel
      icases Hmodel with ⟨%head,%tail,⟨%Hkind,%Hstored,%Hindex,%Hoffset⟩,Hargs,Hhead,Htail⟩
      dsimp only at Hkind Hstored Hindex Hoffset
      subst kind; subst stored; subst index; subst offset
      have calls : ∀ m ∈ first :: rest.toList, ∀ o p v,
          ⊢ iprop({{ o ↦* p ∗ ownSliceCap w8 o (DFrac.own 1) ∗ OutputTerm (GF := GF) m v }}
            (App (App (Val (@! appendTermWire)) (Val #o)) (Val #v))
            {{ (result : GoSlice), RET (PairV #result #interface.nil);
              result ↦* (p ++ wireBytes m.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OutputTerm m v }}) := by
        intro m member o p v
        rcases List.mem_cons.mp member with equal | inside
        · subst m; exact wire_term first o p v
        · exact wire_arg_calls rest m inside o p v
      wp_apply (append_difference out prior args first rest head tail calls)
        $$ [Hout Hcap Hargs Hhead Htail] with %result ⟨Hout,Hcap,Hargs,Hhead,Htail⟩
      · iframe Hout Hcap Hargs Hhead Htail
      iapply HΦ
      iframe Hout Hcap
      simp only [OutputTerm]
      iexists head,tail
      isplitl []
      · ipureintro; trivial
      iframe Hargs Hhead Htail

  theorem wire_arg_calls (models : ModelArgs) (model : ModelTerm) (member : model ∈ models.toList)
      (out : GoSlice) (prior : List w8) (value : Term) :
      ⊢ iprop({{ out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ OutputTerm (GF := GF) model value }}
        (App (App (Val (@! appendTermWire)) (Val #out)) (Val #value))
        {{ (result : GoSlice), RET (PairV #result #interface.nil);
          result ↦* (prior ++ wireBytes model.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OutputTerm model value }}) := by
    cases models with
    | nil => simp [DivRemFV.CaptureSyntax.Args.toList] at member
    | cons first rest =>
      rcases List.mem_cons.mp member with equal | inside
      · subst model; exact wire_term first out prior value
      · exact wire_arg_calls rest model inside out prior value
end

#print axioms wire_term
end
end divremfv.internal.airdata.SourceCapture
end Perennial


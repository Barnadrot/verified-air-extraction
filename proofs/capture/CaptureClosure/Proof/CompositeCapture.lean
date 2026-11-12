module
public import CaptureClosure.Proof.TermLoop

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
variable [github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Add.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Sub.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Mul.TypeAssumptions]
variable [FuncUnfold ExportTerm [] ExportTerm.impl]
local notation "FType" => github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty
local notation "Air" => github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.ty FType
local notation "Add" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Add (GoArray w32 1) GoInterface
local notation "AddType" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Add.ty FType Air
local notation "Mul" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Mul (GoArray w32 1) GoInterface
local notation "MulType" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Mul.ty FType Air
local notation "Sub" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Sub (GoArray w32 1) GoInterface
local notation "SubType" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Sub.ty FType Air

attribute [-instance] pure_wp_slice_for_range in
theorem sum_capture (p : Loc) (sl : GoSlice) (models : ModelArgs) (sources : List GoInterface)
    (nonnull : p ≠ null)
    (calls : ∀ model ∈ models.toList, ∀ source : GoInterface,
      ⊢ iprop({{ InputTerm (GF := GF) model source }}
        (App (Val (@! ExportTerm)) (Val #source))
        {{ (result : Term), RET (PairV #result #interface.nil); OutputTerm model result }})) :
    {{ (p.[Add,go!"Args"] ↦□ sl ∗ sl ↦*□ sources ∗ InputList models.toList sources : IProp GF) }}
      (App (Val (@! ExportTerm)) (Val #(interface.mkOk (go.PointerType AddType) #p)))
    {{ (result : Term), RET (PairV #result #interface.nil); OutputTerm (.sum models) result }} := by
  wp_start as ⟨#Hfield,#Hsl,#Hmodels⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Term.ty))))
    (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Term) (t := Term.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %empty ⟨Hargs,Hcap⟩
  wp_auto
  dsimp only
  simp only [show (0 : w64) = W64 0 by word]
  wp_apply (capture_args models.toList sources sl out_ptr arg_ptr
    (Term.mk go!"add" (W64 0) (W64 0) (W64 0)
      (slice.mk empty (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])))) calls)
    $$ [out Hargs Hcap arg] with %args %results ⟨Hout,Hargs,Hcap,Hresults⟩
  · iframe
    iframe #
  try wp_auto
  iapply HΦ
  simp only [OutputTerm]
  iexists results
  isplitl []
  · ipureintro; trivial
  iframe Hargs
  iapply (output_args_list models results).2
  iexact Hresults

#print axioms sum_capture

attribute [-instance] pure_wp_slice_for_range in
theorem product_capture (p : Loc) (sl : GoSlice) (models : ModelArgs) (sources : List GoInterface)
    (nonnull : p ≠ null)
    (calls : ∀ model ∈ models.toList, ∀ source : GoInterface,
      ⊢ iprop({{ InputTerm (GF := GF) model source }}
        (App (Val (@! ExportTerm)) (Val #source))
        {{ (result : Term), RET (PairV #result #interface.nil); OutputTerm model result }})) :
    {{ (p.[Mul,go!"Args"] ↦□ sl ∗ sl ↦*□ sources ∗ InputList models.toList sources : IProp GF) }}
      (App (Val (@! ExportTerm)) (Val #(interface.mkOk (go.PointerType MulType) #p)))
    {{ (result : Term), RET (PairV #result #interface.nil); OutputTerm (.product models) result }} := by
  wp_start as ⟨#Hfield,#Hsl,#Hmodels⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Term.ty))))
    (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Term) (t := Term.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %empty ⟨Hargs,Hcap⟩
  wp_auto
  dsimp only
  simp only [show (0 : w64) = W64 0 by word]
  wp_apply (capture_args models.toList sources sl out_ptr arg_ptr
    (Term.mk go!"mul" (W64 0) (W64 0) (W64 0)
      (slice.mk empty (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])))) calls)
    $$ [out Hargs Hcap arg] with %args %results ⟨Hout,Hargs,Hcap,Hresults⟩
  · iframe
    iframe #
  try wp_auto
  iapply HΦ
  simp only [OutputTerm]
  iexists results
  isplitl []
  · ipureintro; trivial
  iframe Hargs
  iapply (output_args_list models results).2
  iexact Hresults

#print axioms product_capture

attribute [-instance] pure_wp_slice_for_range in
theorem difference_capture (p : Loc) (sl : GoSlice) (first : ModelTerm) (rest : ModelArgs) (sources : List GoInterface)
    (nonnull : p ≠ null)
    (calls : ∀ model ∈ (first :: rest.toList), ∀ source : GoInterface,
      ⊢ iprop({{ InputTerm (GF := GF) model source }}
        (App (Val (@! ExportTerm)) (Val #source))
        {{ (result : Term), RET (PairV #result #interface.nil); OutputTerm model result }})) :
    {{ (p.[Sub,go!"Args"] ↦□ sl ∗ sl ↦*□ sources ∗ InputList (first :: rest.toList) sources : IProp GF) }}
      (App (Val (@! ExportTerm)) (Val #(interface.mkOk (go.PointerType SubType) #p)))
    {{ (result : Term), RET (PairV #result #interface.nil); OutputTerm (.difference first rest) result }} := by
  wp_start as ⟨#Hfield,#Hsl,#Hmodels⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Term.ty))))
    (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Term) (t := Term.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %empty ⟨Hargs,Hcap⟩
  wp_auto
  dsimp only
  simp only [show (0 : w64) = W64 0 by word]
  wp_apply (capture_args (first :: rest.toList) sources sl out_ptr arg_ptr
    (Term.mk go!"sub" (W64 0) (W64 0) (W64 0)
      (slice.mk empty (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])))) calls)
    $$ [out Hargs Hcap arg] with %args %results ⟨Hout,Hargs,Hcap,Hresults⟩
  · iframe
    iframe #
  try wp_auto
  iapply HΦ
  simp only [OutputTerm]
  ihave ⟨%head,%tail,⟨%Heq,⟨Hhead,Htail⟩⟩⟩ :=
    BigSepL2.bigSepL2_cons_inv_left.1 $$ Hresults
  subst results
  iexists head,tail
  isplitl []
  · ipureintro; trivial
  iframe Hargs Hhead
  iapply (output_args_list rest tail).2
  iexact Htail

#print axioms difference_capture
end
end divremfv.internal.airdata.SourceCapture
end Perennial

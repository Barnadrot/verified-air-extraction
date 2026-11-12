module
public import CaptureClosure.Proof.TermLayout

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Term.TypeAssumptions] [captureError.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.TypeAssumptions]
variable [FuncUnfold ExportTerm [] ExportTerm.impl]
variable [FuncUnfold appendTermWire [] appendTermWire.impl]

theorem reject_nil_term :
    {{ (True : IProp GF) }}
      (App (Val (@! ExportTerm)) (Val #interface.nil))
    {{ (result : Term), RET (PairV #result
        #(interface.mkOk captureError.ty #(go!"unsupported AIR term"))); True }} := by
  wp_start as _
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Term.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Term) (t := Term.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %args ⟨Hargs,Hcap⟩
  wp_auto
  iapply HΦ
  itrivial

local notation "F" => github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty
local notation "Air" => github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.ty F
local notation "Const" => go.PointerType (github_com.LFDT_Lineth.zkc.pkg.ir.term.Constant.ty F Air)
local notation "Column" => go.PointerType (github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess.ty F Air)
local notation "Add" => go.PointerType (github_com.LFDT_Lineth.zkc.pkg.ir.term.Add.ty F Air)
local notation "Sub" => go.PointerType (github_com.LFDT_Lineth.zkc.pkg.ir.term.Sub.ty F Air)
local notation "Mul" => go.PointerType (github_com.LFDT_Lineth.zkc.pkg.ir.term.Mul.ty F Air)

theorem reject_other_term (ty : go.GoType) (value : val)
    (h0 : ty ≠ Const) (h1 : ty ≠ Column) (h2 : ty ≠ Add) (h3 : ty ≠ Sub) (h4 : ty ≠ Mul) :
    {{ (True : IProp GF) }}
      (App (Val (@! ExportTerm)) (Val #(interface.mkOk ty value)))
    {{ (result : Term), RET (PairV #result
        #(interface.mkOk captureError.ty #(go!"unsupported AIR term"))); True }} := by
  wp_start as _
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Term.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Term) (t := Term.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %args ⟨Hargs,Hcap⟩
  wp_auto
  simp only [if_neg h0,decide_eq_false h0]
  wp_auto
  simp only [if_neg h1,decide_eq_false h1]
  wp_auto
  simp only [if_neg h2,decide_eq_false h2]
  wp_auto
  simp only [if_neg h3,decide_eq_false h3]
  wp_auto
  simp only [if_neg h4,decide_eq_false h4]
  wp_auto
  iapply HΦ
  itrivial

theorem reject_unknown_wire (out : GoSlice) (value : Term)
    (h0 : value.Kind' ≠ go!"constant") (h1 : value.Kind' ≠ go!"column")
    (h2 : value.Kind' ≠ go!"add") (h3 : value.Kind' ≠ go!"sub") (h4 : value.Kind' ≠ go!"mul") :
    {{ (True : IProp GF) }}
      (App (App (Val (@! appendTermWire)) (Val #out)) (Val #value))
    {{ RET (PairV #slice.nil
        #(interface.mkOk captureError.ty #(go!"unsupported wire term"))); True }} := by
  wp_start as _
  wp_auto
  rw [decide_eq_false h0]
  wp_auto
  rw [decide_eq_false h1]
  wp_auto
  rw [decide_eq_false h2]
  wp_auto
  rw [decide_eq_false h3]
  wp_auto
  rw [decide_eq_false h4]
  wp_auto
  iapply HΦ
  itrivial

#print axioms reject_nil_term
#print axioms reject_other_term
#print axioms reject_unknown_wire
end
end divremfv.internal.airdata.SourceCapture
end Perennial

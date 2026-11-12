module
public import CaptureClosure.Proof.RecordLayouts

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
local notation "F" => github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty
local notation "Logical" => github_com.LFDT_Lineth.zkc.pkg.ir.air.LogicalTerm.ty F
local notation "VanishingType" => go.PointerType (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing.Constraint.ty F Logical)
local notation "RangeType" => go.PointerType (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged.Constraint.ty F)
local notation "LookupType" => go.PointerType (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Constraint.ty F)
local notation "BusType" => go.PointerType (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Constraint.ty F)
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Constraint.TypeAssumptions] [Vector.TypeAssumptions] [captureError.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.LogicalTerm.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.Constraint.TypeAssumptions]
variable [FuncUnfold exportConstraint [] exportConstraint.impl]

theorem reject_other_constraint (mid id : w64) (ty : go.GoType) (value : val)
    (h0 : ty ≠ VanishingType) (h1 : ty ≠ RangeType) (h2 : ty ≠ LookupType) (h3 : ty ≠ BusType) :
    {{ (True : IProp GF) }}
      (App (App (App (Val (@! exportConstraint)) (Val #mid)) (Val #id)) (Val #(interface.mkOk ty value)))
    {{ (result : Constraint), RET (PairV #result
        #(interface.mkOk captureError.ty #(go!"unsupported AIR constraint"))); True }} := by
  wp_start
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Vector.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Vector) (t := Vector.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sources ⟨Hsources,HsourceCap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Vector.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Vector) (t := Vector.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %targets ⟨Htargets,HtargetCap⟩
  wp_auto
  simp only [if_neg h0,decide_eq_false h0]
  wp_auto
  simp only [if_neg h1,decide_eq_false h1]
  wp_auto
  simp only [if_neg h2,decide_eq_false h2]
  wp_auto
  simp only [if_neg h3,decide_eq_false h3]
  wp_auto
  iapply HΦ
  itrivial

theorem reject_nil_constraint (mid id : w64) :
    {{ (True : IProp GF) }}
      (App (App (App (Val (@! exportConstraint)) (Val #mid)) (Val #id)) (Val #interface.nil))
    {{ (result : Constraint), RET (PairV #result
        #(interface.mkOk captureError.ty #(go!"unsupported AIR constraint"))); True }} := by
  wp_start
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Vector.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Vector) (t := Vector.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sources ⟨Hsources,HsourceCap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Vector.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Vector) (t := Vector.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %targets ⟨Htargets,HtargetCap⟩
  wp_auto
  iapply HΦ
  itrivial

#print axioms reject_other_constraint
#print axioms reject_nil_constraint
end
end divremfv.internal.airdata.SourceCapture
end Perennial

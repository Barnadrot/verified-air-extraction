module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import CaptureClosure.Proof.FieldCapture
public import CaptureClosure.Proof.TermLayout
public import CaptureClosure.Proof.RegisterReads
public import CaptureClosure.Code.divremfv.internal.airdata

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata
namespace SourceCapture

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
open github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear
local notation "Air" => github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.ty Element.ty
local notation "ConstantType" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Constant.ty Element.ty Air

variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Constant.TypeAssumptions]
variable [Term.TypeAssumptions] [Element.TypeAssumptions]
variable [FuncUnfold ExportTerm [] ExportTerm.impl]
variable [FuncUnfold montgomeryReduce [] montgomeryReduce.impl]
variable [FuncUnfold math.bits.Sub32 [] math.bits.Sub32.impl]

theorem constant_capture (p : Loc) (raw : w32) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[github_com.LFDT_Lineth.zkc.pkg.ir.term.Constant (GoArray w32 1) GoInterface, go!"Value"]
          ↦{dq} (array.mk 1 [raw]) : IProp GF) }}
      (App (Val (@! ExportTerm))
        (Val #(interface.mkOk (go.GoType.PointerType ConstantType) #p)))
    {{ (args : GoSlice), RET (PairV #(Term.mk go!"constant" (W64 (decodedValue raw.toNat)) (W64 0) (W64 0) args) #interface.nil);
      ownSlice args ([] : List Term) (DFrac.own 1) }} := by
  wp_start as Hvalue
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Term.ty))))
    (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Term) (t := Term.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %args ⟨Hargs, Hcap⟩
  wp_auto
  wp_apply Element.uint64_capture raw
  all_goals try itrivial
  try wp_auto
  rw [doFor_unseal]
  wp_call
  wp_auto
  dsimp only
  rw [show (0 : w64) = W64 0 by word]
  iapply HΦ $$ Hargs

#print axioms constant_capture

section column
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.TypeAssumptions]
local notation "Access" => github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess (GoArray w32 1) GoInterface
local notation "AccessType" => github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess.ty Element.ty Air

theorem column_capture (p : Loc) (index shift : w64) (dq : DFrac)
    (nonnull : p ≠ null) (valid : index ≠ W64 (2^64-1)) :
    {{ (p.[Access, go!"register"] ↦{dq} (github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.mk index) ∗
        p.[Access, go!"shift"] ↦{dq} shift : IProp GF) }}
      (App (Val (@! ExportTerm))
        (Val #(interface.mkOk (go.GoType.PointerType AccessType) #p)))
    {{ (args : GoSlice), RET (PairV #(Term.mk go!"column" (W64 0) index shift args) #interface.nil);
      ownSlice args ([] : List Term) (DFrac.own 1) }} := by
  wp_start as ⟨Hreg, Hshift⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Term.ty))))
    (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Term) (t := Term.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %args ⟨Hargs, Hcap⟩
  wp_auto
  wp_apply (github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess.register_correct
    Element.ty Air p (github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.mk index) dq nonnull) $$ Hreg with Hreg
  wp_apply (github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.unwrap_correct index valid)
  all_goals try itrivial
  wp_apply (github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess.shift_correct
    Element.ty Air p shift dq nonnull) $$ Hshift with Hshift
  try wp_auto
  rw [doFor_unseal]
  wp_call
  wp_auto
  dsimp only
  rw [show (0 : w64) = W64 0 by word]
  iapply HΦ $$ Hargs

#print axioms column_capture
end column

end SourceCapture
end divremfv.internal.airdata
end Perennial

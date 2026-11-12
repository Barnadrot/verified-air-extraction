module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import CaptureClosure.Proof.ColumnId
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.ir.term

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.ir.term

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [RegisterAccess.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.TypeAssumptions]
variable (F T : go.GoType) {F' T' : Type}
variable [ZeroVal F'] [TypeRepr F F'] [ZeroVal T'] [TypeRepr T T']

theorem RegisterAccess.register_correct (p : Loc)
    (id : github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[RegisterAccess F' T', go!"register"] ↦{dq} id : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType (RegisterAccess.ty F T) @!! go!"Register")) (Val #()))
    {{ RET #id; p.[RegisterAccess F' T', go!"register"] ↦{dq} id }} := by
  wp_start as Hfield
  wp_auto
  iapply HΦ $$ Hfield

theorem RegisterAccess.shift_correct (p : Loc) (shift : w64) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[RegisterAccess F' T', go!"shift"] ↦{dq} shift : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType (RegisterAccess.ty F T) @!! go!"RelativeShift")) (Val #()))
    {{ RET #shift; p.[RegisterAccess F' T', go!"shift"] ↦{dq} shift }} := by
  wp_start as Hfield
  wp_auto
  iapply HΦ $$ Hfield

#print axioms RegisterAccess.register_correct
#print axioms RegisterAccess.shift_correct
end
end github_com.LFDT_Lineth.zkc.pkg.ir.term
end Perennial

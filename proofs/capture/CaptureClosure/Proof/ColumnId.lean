module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.trace

@[expose] public section
noncomputable section

namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.trace

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [ColumnId.TypeAssumptions]

instance : TypedPointsto (GF := GF) ColumnId where
  typedPointstoDef l v dq := iprop(
    "index" ∷ typedPointsto (structFieldRef ColumnId go!"index" l) v.index' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance : IntoValTypedUnderlying (GF := GF) ColumnId ColumnId.underlying := by
  solve_into_val_typed_struct

instance (l : Loc) (v : ColumnId) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef ColumnId go!"index" l) v.index' dq)
      (typedPointsto (structFieldRef ColumnId go!"index" l) v.index' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

/-- The actual translated Go accessor returns every valid column index unchanged. -/
theorem ColumnId.unwrap_correct (index : w64) (valid : index ≠ W64 (2^64-1)) :
    {{ (True : IProp GF) }}
      (App (Val ((ColumnId.mk index) @!! ColumnId.ty @!! go!"Unwrap")) (Val #()))
    {{ RET #index; True }} := by
  wp_start
  wp_auto
  change index ≠ W64 18446744073709551615 at valid
  rw [decide_eq_false valid]
  wp_auto
  wp_end

#print axioms ColumnId.unwrap_correct
end
end github_com.LFDT_Lineth.zkc.pkg.trace
end Perennial


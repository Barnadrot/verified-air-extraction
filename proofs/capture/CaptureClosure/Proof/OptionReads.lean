module
public import CaptureClosure.Proof.OptionLayout

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.util

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Option.TypeAssumptions]
variable (T : go.GoType) {V : Type} [ZeroVal V] [TypeRepr T V] [TypedPointsto (GF := GF) V]
variable [IntoValTyped (GF := GF) V T]

theorem Option.hasValue_correct (value : Option V) :
    {{ (True : IProp GF) }}
      (App (Val (value @!! Option.ty T @!! go!"HasValue")) (Val #()))
    {{ RET #value.some'; True }} := by
  wp_start as _
  wp_auto
  iapply HΦ
  itrivial

theorem Option.unwrap_correct (value : Option V) (present : value.some' = true) :
    {{ (True : IProp GF) }}
      (App (Val (value @!! Option.ty T @!! go!"Unwrap")) (Val #()))
    {{ RET #value.value'; True }} := by
  wp_start as _
  wp_auto
  rw [present]
  wp_auto
  iapply HΦ
  itrivial

#print axioms Option.hasValue_correct
#print axioms Option.unwrap_correct
end
end github_com.LFDT_Lineth.zkc.pkg.util
end Perennial

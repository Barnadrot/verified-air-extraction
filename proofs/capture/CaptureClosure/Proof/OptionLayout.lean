module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.util

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.util

namespace Option
section def_

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]

instance Option_typed_pointsto {T' : Type} [TypedPointsto (GF := GF) T'] :
    TypedPointsto (GF := GF) (github_com.LFDT_Lineth.zkc.pkg.util.Option T') where
  typedPointstoDef l v dq := iprop(
    "some" ∷ typedPointsto (structFieldRef (github_com.LFDT_Lineth.zkc.pkg.util.Option T') go!"some" l) v.some' dq ∗
    "value" ∷ typedPointsto (structFieldRef (github_com.LFDT_Lineth.zkc.pkg.util.Option T') go!"value" l) v.value' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Option_into_val_typed (T : go.GoType) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] [IntoValTyped (GF := GF) T' T] :
    IntoValTypedUnderlying (GF := GF) (github_com.LFDT_Lineth.zkc.pkg.util.Option T') (github_com.LFDT_Lineth.zkc.pkg.util.Option.underlying T) := by
  solve_into_val_typed_struct

instance Option_access_load_some {T' : Type} [TypedPointsto (GF := GF) T'] (l : Loc) (v : (github_com.LFDT_Lineth.zkc.pkg.util.Option T')) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef (github_com.LFDT_Lineth.zkc.pkg.util.Option T') go!"some" l) v.some' dq)
      (typedPointsto (structFieldRef (github_com.LFDT_Lineth.zkc.pkg.util.Option T') go!"some" l) v.some' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Option_access_store_some {T' : Type} [TypedPointsto (GF := GF) T'] (l : Loc) (v : (github_com.LFDT_Lineth.zkc.pkg.util.Option T')) (some' : Bool) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef (github_com.LFDT_Lineth.zkc.pkg.util.Option T') go!"some" l) v.some' (DFrac.own 1))
      (typedPointsto (structFieldRef (github_com.LFDT_Lineth.zkc.pkg.util.Option T') go!"some" l) some' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with some' := some' } : (github_com.LFDT_Lineth.zkc.pkg.util.Option T')) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Option_access_load_value {T' : Type} [TypedPointsto (GF := GF) T'] (l : Loc) (v : (github_com.LFDT_Lineth.zkc.pkg.util.Option T')) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef (github_com.LFDT_Lineth.zkc.pkg.util.Option T') go!"value" l) v.value' dq)
      (typedPointsto (structFieldRef (github_com.LFDT_Lineth.zkc.pkg.util.Option T') go!"value" l) v.value' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Option_access_store_value {T' : Type} [TypedPointsto (GF := GF) T'] (l : Loc) (v : (github_com.LFDT_Lineth.zkc.pkg.util.Option T')) (value' : T') :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef (github_com.LFDT_Lineth.zkc.pkg.util.Option T') go!"value" l) v.value' (DFrac.own 1))
      (typedPointsto (structFieldRef (github_com.LFDT_Lineth.zkc.pkg.util.Option T') go!"value" l) value' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with value' := value' } : (github_com.LFDT_Lineth.zkc.pkg.util.Option T')) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end Option

end github_com.LFDT_Lineth.zkc.pkg.util
end Perennial

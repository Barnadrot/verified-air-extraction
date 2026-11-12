module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import CaptureClosure.Code.divremfv.internal.airdata
@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Term.TypeAssumptions]
instance Term_typed_pointsto :
    TypedPointsto (GF := GF) divremfv.internal.airdata.Term where
  typedPointstoDef l v dq := iprop(
    "Kind" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Kind" l) v.Kind' dq ∗
    "Value" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Value" l) v.Value' dq ∗
    "Column" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Column" l) v.Column' dq ∗
    "Shift" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Shift" l) v.Shift' dq ∗
    "Args" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Args" l) v.Args' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Term_into_val_typed :
    IntoValTypedUnderlying (GF := GF) divremfv.internal.airdata.Term divremfv.internal.airdata.Term.underlying := by
  solve_into_val_typed_struct

instance Term_access_load_Kind (l : Loc) (v : divremfv.internal.airdata.Term) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Kind" l) v.Kind' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Kind" l) v.Kind' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Term_access_store_Kind (l : Loc) (v : divremfv.internal.airdata.Term) (Kind' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Kind" l) v.Kind' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Kind" l) Kind' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Kind' := Kind' } : divremfv.internal.airdata.Term) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Term_access_load_Value (l : Loc) (v : divremfv.internal.airdata.Term) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Value" l) v.Value' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Value" l) v.Value' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Term_access_store_Value (l : Loc) (v : divremfv.internal.airdata.Term) (Value' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Value" l) v.Value' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Value" l) Value' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Value' := Value' } : divremfv.internal.airdata.Term) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Term_access_load_Column (l : Loc) (v : divremfv.internal.airdata.Term) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Column" l) v.Column' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Column" l) v.Column' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Term_access_store_Column (l : Loc) (v : divremfv.internal.airdata.Term) (Column' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Column" l) v.Column' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Column" l) Column' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Column' := Column' } : divremfv.internal.airdata.Term) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Term_access_load_Shift (l : Loc) (v : divremfv.internal.airdata.Term) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Shift" l) v.Shift' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Shift" l) v.Shift' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Term_access_store_Shift (l : Loc) (v : divremfv.internal.airdata.Term) (Shift' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Shift" l) v.Shift' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Shift" l) Shift' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Shift' := Shift' } : divremfv.internal.airdata.Term) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Term_access_load_Args (l : Loc) (v : divremfv.internal.airdata.Term) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Args" l) v.Args' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Args" l) v.Args' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Term_access_store_Args (l : Loc) (v : divremfv.internal.airdata.Term) (Args' : GoSlice) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Args" l) v.Args' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Term go!"Args" l) Args' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Args' := Args' } : divremfv.internal.airdata.Term) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct


end divremfv.internal.airdata
end Perennial


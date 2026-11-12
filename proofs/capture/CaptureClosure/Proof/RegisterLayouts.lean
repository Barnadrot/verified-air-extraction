module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.schema.register

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.schema.register

namespace Type'
section def_

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.register.«Type».TypeAssumptions]

instance Type'_typed_pointsto :
    TypedPointsto (GF := GF) github_com.LFDT_Lineth.zkc.pkg.schema.register.Type' where
  typedPointstoDef l v dq := iprop(
    "kind" ∷ typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Type' go!"kind" l) v.kind' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Type'_into_val_typed :
    IntoValTypedUnderlying (GF := GF) github_com.LFDT_Lineth.zkc.pkg.schema.register.Type' github_com.LFDT_Lineth.zkc.pkg.schema.register.Type'.underlying := by
  solve_into_val_typed_struct

instance Type'_access_load_kind (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.register.Type') (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Type' go!"kind" l) v.kind' dq)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Type' go!"kind" l) v.kind' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Type'_access_store_kind (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.register.Type') (kind' : w8) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Type' go!"kind" l) v.kind' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Type' go!"kind" l) kind' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with kind' := kind' } : github_com.LFDT_Lineth.zkc.pkg.schema.register.Type') (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end Type'

namespace Register
section def_

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.register.«Type».TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.TypeAssumptions]

instance Register_typed_pointsto :
    TypedPointsto (GF := GF) github_com.LFDT_Lineth.zkc.pkg.schema.register.Register where
  typedPointstoDef l v dq := iprop(
    "kind" ∷ typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"kind" l) v.kind' dq ∗
    "name" ∷ typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"name" l) v.name' dq ∗
    "width" ∷ typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"width" l) v.width' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Register_into_val_typed :
    IntoValTypedUnderlying (GF := GF) github_com.LFDT_Lineth.zkc.pkg.schema.register.Register github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.underlying := by
  solve_into_val_typed_struct

instance Register_access_load_kind (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.register.Register) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"kind" l) v.kind' dq)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"kind" l) v.kind' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Register_access_store_kind (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.register.Register) (kind' : github_com.LFDT_Lineth.zkc.pkg.schema.register.Type') :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"kind" l) v.kind' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"kind" l) kind' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with kind' := kind' } : github_com.LFDT_Lineth.zkc.pkg.schema.register.Register) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Register_access_load_name (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.register.Register) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"name" l) v.name' dq)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"name" l) v.name' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Register_access_store_name (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.register.Register) (name' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"name" l) v.name' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"name" l) name' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with name' := name' } : github_com.LFDT_Lineth.zkc.pkg.schema.register.Register) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Register_access_load_width (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.register.Register) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"width" l) v.width' dq)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"width" l) v.width' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Register_access_store_width (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.register.Register) (width' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"width" l) v.width' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.register.Register go!"width" l) width' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with width' := width' } : github_com.LFDT_Lineth.zkc.pkg.schema.register.Register) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end Register

end github_com.LFDT_Lineth.zkc.pkg.schema.register
end Perennial

module
public import CaptureClosure.Proof.ColumnId
public import CaptureClosure.Proof.OptionLayout
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup
namespace Vector
section def_

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.TypeAssumptions]

instance Vector_typed_pointsto :
    TypedPointsto (GF := GF) github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector where
  typedPointstoDef l v dq := iprop(
    "Module" ∷ typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Module" l) v.Module' dq ∗
    "Selector" ∷ typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Selector" l) v.Selector' dq ∗
    "Registers" ∷ typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Registers" l) v.Registers' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Vector_into_val_typed :
    IntoValTypedUnderlying (GF := GF) github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector.underlying := by
  solve_into_val_typed_struct

instance Vector_access_load_Module (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Module" l) v.Module' dq)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Module" l) v.Module' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Vector_access_store_Module (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (Module' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Module" l) v.Module' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Module" l) Module' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Module' := Module' } : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Vector_access_load_Selector (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Selector" l) v.Selector' dq)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Selector" l) v.Selector' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Vector_access_store_Selector (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (Selector' : (github_com.LFDT_Lineth.zkc.pkg.util.Option github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId)) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Selector" l) v.Selector' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Selector" l) Selector' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Selector' := Selector' } : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Vector_access_load_Registers (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Registers" l) v.Registers' dq)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Registers" l) v.Registers' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Vector_access_store_Registers (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (Registers' : GoSlice) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Registers" l) v.Registers' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector go!"Registers" l) Registers' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Registers' := Registers' } : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end Vector
end github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup

namespace github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus
namespace Port
section def_

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.TypeAssumptions]

instance Port_typed_pointsto :
    TypedPointsto (GF := GF) github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port where
  typedPointstoDef l v dq := iprop(
    "Module" ∷ typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Module" l) v.Module' dq ∗
    "Selector" ∷ typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Selector" l) v.Selector' dq ∗
    "Registers" ∷ typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Registers" l) v.Registers' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Port_into_val_typed :
    IntoValTypedUnderlying (GF := GF) github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port.underlying := by
  solve_into_val_typed_struct

instance Port_access_load_Module (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Module" l) v.Module' dq)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Module" l) v.Module' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Port_access_store_Module (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port) (Module' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Module" l) v.Module' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Module" l) Module' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Module' := Module' } : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Port_access_load_Selector (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Selector" l) v.Selector' dq)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Selector" l) v.Selector' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Port_access_store_Selector (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port) (Selector' : github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Selector" l) v.Selector' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Selector" l) Selector' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Selector' := Selector' } : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Port_access_load_Registers (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Registers" l) v.Registers' dq)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Registers" l) v.Registers' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Port_access_store_Registers (l : Loc) (v : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port) (Registers' : GoSlice) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Registers" l) v.Registers' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port go!"Registers" l) Registers' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Registers' := Registers' } : github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end Port
end github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus
end Perennial

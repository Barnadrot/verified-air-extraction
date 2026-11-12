module
public import CaptureClosure.Proof.TermLayout

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata

namespace Column
section def_

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [divremfv.internal.airdata.Column.TypeAssumptions]

instance Column_typed_pointsto :
    TypedPointsto (GF := GF) divremfv.internal.airdata.Column where
  typedPointstoDef l v dq := iprop(
    "ID" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"ID" l) v.ID' dq ∗
    "Name" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Name" l) v.Name' dq ∗
    "Bits" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Bits" l) v.Bits' dq ∗
    "Input" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Input" l) v.Input' dq ∗
    "Output" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Output" l) v.Output' dq ∗
    "Native" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Native" l) v.Native' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Column_into_val_typed :
    IntoValTypedUnderlying (GF := GF) divremfv.internal.airdata.Column divremfv.internal.airdata.Column.underlying := by
  solve_into_val_typed_struct

instance Column_access_load_ID (l : Loc) (v : divremfv.internal.airdata.Column) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"ID" l) v.ID' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"ID" l) v.ID' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Column_access_store_ID (l : Loc) (v : divremfv.internal.airdata.Column) (ID' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"ID" l) v.ID' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"ID" l) ID' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with ID' := ID' } : divremfv.internal.airdata.Column) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Column_access_load_Name (l : Loc) (v : divremfv.internal.airdata.Column) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Name" l) v.Name' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Name" l) v.Name' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Column_access_store_Name (l : Loc) (v : divremfv.internal.airdata.Column) (Name' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Name" l) v.Name' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Name" l) Name' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Name' := Name' } : divremfv.internal.airdata.Column) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Column_access_load_Bits (l : Loc) (v : divremfv.internal.airdata.Column) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Bits" l) v.Bits' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Bits" l) v.Bits' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Column_access_store_Bits (l : Loc) (v : divremfv.internal.airdata.Column) (Bits' : Loc) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Bits" l) v.Bits' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Bits" l) Bits' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Bits' := Bits' } : divremfv.internal.airdata.Column) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Column_access_load_Input (l : Loc) (v : divremfv.internal.airdata.Column) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Input" l) v.Input' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Input" l) v.Input' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Column_access_store_Input (l : Loc) (v : divremfv.internal.airdata.Column) (Input' : Bool) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Input" l) v.Input' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Input" l) Input' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Input' := Input' } : divremfv.internal.airdata.Column) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Column_access_load_Output (l : Loc) (v : divremfv.internal.airdata.Column) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Output" l) v.Output' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Output" l) v.Output' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Column_access_store_Output (l : Loc) (v : divremfv.internal.airdata.Column) (Output' : Bool) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Output" l) v.Output' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Output" l) Output' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Output' := Output' } : divremfv.internal.airdata.Column) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Column_access_load_Native (l : Loc) (v : divremfv.internal.airdata.Column) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Native" l) v.Native' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Native" l) v.Native' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Column_access_store_Native (l : Loc) (v : divremfv.internal.airdata.Column) (Native' : Bool) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Native" l) v.Native' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Column go!"Native" l) Native' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Native' := Native' } : divremfv.internal.airdata.Column) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end Column

namespace Module
section def_

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [divremfv.internal.airdata.Module.TypeAssumptions]

instance Module_typed_pointsto :
    TypedPointsto (GF := GF) divremfv.internal.airdata.Module where
  typedPointstoDef l v dq := iprop(
    "ID" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"ID" l) v.ID' dq ∗
    "Name" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Name" l) v.Name' dq ∗
    "Static" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Static" l) v.Static' dq ∗
    "Native" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Native" l) v.Native' dq ∗
    "Columns" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Columns" l) v.Columns' dq ∗
    "Content" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Content" l) v.Content' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Module_into_val_typed :
    IntoValTypedUnderlying (GF := GF) divremfv.internal.airdata.Module divremfv.internal.airdata.Module.underlying := by
  solve_into_val_typed_struct

instance Module_access_load_ID (l : Loc) (v : divremfv.internal.airdata.Module) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"ID" l) v.ID' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"ID" l) v.ID' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Module_access_store_ID (l : Loc) (v : divremfv.internal.airdata.Module) (ID' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"ID" l) v.ID' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"ID" l) ID' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with ID' := ID' } : divremfv.internal.airdata.Module) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Module_access_load_Name (l : Loc) (v : divremfv.internal.airdata.Module) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Name" l) v.Name' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Name" l) v.Name' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Module_access_store_Name (l : Loc) (v : divremfv.internal.airdata.Module) (Name' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Name" l) v.Name' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Name" l) Name' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Name' := Name' } : divremfv.internal.airdata.Module) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Module_access_load_Static (l : Loc) (v : divremfv.internal.airdata.Module) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Static" l) v.Static' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Static" l) v.Static' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Module_access_store_Static (l : Loc) (v : divremfv.internal.airdata.Module) (Static' : Bool) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Static" l) v.Static' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Static" l) Static' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Static' := Static' } : divremfv.internal.airdata.Module) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Module_access_load_Native (l : Loc) (v : divremfv.internal.airdata.Module) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Native" l) v.Native' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Native" l) v.Native' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Module_access_store_Native (l : Loc) (v : divremfv.internal.airdata.Module) (Native' : Bool) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Native" l) v.Native' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Native" l) Native' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Native' := Native' } : divremfv.internal.airdata.Module) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Module_access_load_Columns (l : Loc) (v : divremfv.internal.airdata.Module) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Columns" l) v.Columns' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Columns" l) v.Columns' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Module_access_store_Columns (l : Loc) (v : divremfv.internal.airdata.Module) (Columns' : GoSlice) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Columns" l) v.Columns' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Columns" l) Columns' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Columns' := Columns' } : divremfv.internal.airdata.Module) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Module_access_load_Content (l : Loc) (v : divremfv.internal.airdata.Module) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Content" l) v.Content' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Content" l) v.Content' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Module_access_store_Content (l : Loc) (v : divremfv.internal.airdata.Module) (Content' : GoSlice) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Content" l) v.Content' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Module go!"Content" l) Content' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Content' := Content' } : divremfv.internal.airdata.Module) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end Module

namespace Vector
section def_

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [divremfv.internal.airdata.Vector.TypeAssumptions]

instance Vector_typed_pointsto :
    TypedPointsto (GF := GF) divremfv.internal.airdata.Vector where
  typedPointstoDef l v dq := iprop(
    "Module" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Module" l) v.Module' dq ∗
    "Selector" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Selector" l) v.Selector' dq ∗
    "Columns" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Columns" l) v.Columns' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Vector_into_val_typed :
    IntoValTypedUnderlying (GF := GF) divremfv.internal.airdata.Vector divremfv.internal.airdata.Vector.underlying := by
  solve_into_val_typed_struct

instance Vector_access_load_Module (l : Loc) (v : divremfv.internal.airdata.Vector) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Module" l) v.Module' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Module" l) v.Module' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Vector_access_store_Module (l : Loc) (v : divremfv.internal.airdata.Vector) (Module' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Module" l) v.Module' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Module" l) Module' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Module' := Module' } : divremfv.internal.airdata.Vector) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Vector_access_load_Selector (l : Loc) (v : divremfv.internal.airdata.Vector) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Selector" l) v.Selector' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Selector" l) v.Selector' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Vector_access_store_Selector (l : Loc) (v : divremfv.internal.airdata.Vector) (Selector' : Loc) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Selector" l) v.Selector' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Selector" l) Selector' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Selector' := Selector' } : divremfv.internal.airdata.Vector) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Vector_access_load_Columns (l : Loc) (v : divremfv.internal.airdata.Vector) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Columns" l) v.Columns' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Columns" l) v.Columns' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Vector_access_store_Columns (l : Loc) (v : divremfv.internal.airdata.Vector) (Columns' : GoSlice) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Columns" l) v.Columns' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Vector go!"Columns" l) Columns' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Columns' := Columns' } : divremfv.internal.airdata.Vector) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end Vector

namespace Constraint
section def_

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [divremfv.internal.airdata.Constraint.TypeAssumptions]

instance Constraint_typed_pointsto :
    TypedPointsto (GF := GF) divremfv.internal.airdata.Constraint where
  typedPointstoDef l v dq := iprop(
    "ID" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"ID" l) v.ID' dq ∗
    "Owner" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Owner" l) v.Owner' dq ∗
    "Name" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Name" l) v.Name' dq ∗
    "Kind" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Kind" l) v.Kind' dq ∗
    "Domain" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Domain" l) v.Domain' dq ∗
    "Expr" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Expr" l) v.Expr' dq ∗
    "Column" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Column" l) v.Column' dq ∗
    "Bits" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Bits" l) v.Bits' dq ∗
    "Sources" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Sources" l) v.Sources' dq ∗
    "Targets" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Targets" l) v.Targets' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Constraint_into_val_typed :
    IntoValTypedUnderlying (GF := GF) divremfv.internal.airdata.Constraint divremfv.internal.airdata.Constraint.underlying := by
  solve_into_val_typed_struct

instance Constraint_access_load_ID (l : Loc) (v : divremfv.internal.airdata.Constraint) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"ID" l) v.ID' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"ID" l) v.ID' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_store_ID (l : Loc) (v : divremfv.internal.airdata.Constraint) (ID' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"ID" l) v.ID' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"ID" l) ID' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with ID' := ID' } : divremfv.internal.airdata.Constraint) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_load_Owner (l : Loc) (v : divremfv.internal.airdata.Constraint) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Owner" l) v.Owner' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Owner" l) v.Owner' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_store_Owner (l : Loc) (v : divremfv.internal.airdata.Constraint) (Owner' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Owner" l) v.Owner' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Owner" l) Owner' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Owner' := Owner' } : divremfv.internal.airdata.Constraint) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_load_Name (l : Loc) (v : divremfv.internal.airdata.Constraint) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Name" l) v.Name' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Name" l) v.Name' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_store_Name (l : Loc) (v : divremfv.internal.airdata.Constraint) (Name' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Name" l) v.Name' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Name" l) Name' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Name' := Name' } : divremfv.internal.airdata.Constraint) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_load_Kind (l : Loc) (v : divremfv.internal.airdata.Constraint) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Kind" l) v.Kind' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Kind" l) v.Kind' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_store_Kind (l : Loc) (v : divremfv.internal.airdata.Constraint) (Kind' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Kind" l) v.Kind' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Kind" l) Kind' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Kind' := Kind' } : divremfv.internal.airdata.Constraint) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_load_Domain (l : Loc) (v : divremfv.internal.airdata.Constraint) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Domain" l) v.Domain' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Domain" l) v.Domain' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_store_Domain (l : Loc) (v : divremfv.internal.airdata.Constraint) (Domain' : Loc) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Domain" l) v.Domain' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Domain" l) Domain' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Domain' := Domain' } : divremfv.internal.airdata.Constraint) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_load_Expr (l : Loc) (v : divremfv.internal.airdata.Constraint) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Expr" l) v.Expr' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Expr" l) v.Expr' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_store_Expr (l : Loc) (v : divremfv.internal.airdata.Constraint) (Expr' : Loc) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Expr" l) v.Expr' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Expr" l) Expr' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Expr' := Expr' } : divremfv.internal.airdata.Constraint) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_load_Column (l : Loc) (v : divremfv.internal.airdata.Constraint) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Column" l) v.Column' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Column" l) v.Column' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_store_Column (l : Loc) (v : divremfv.internal.airdata.Constraint) (Column' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Column" l) v.Column' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Column" l) Column' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Column' := Column' } : divremfv.internal.airdata.Constraint) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_load_Bits (l : Loc) (v : divremfv.internal.airdata.Constraint) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Bits" l) v.Bits' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Bits" l) v.Bits' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_store_Bits (l : Loc) (v : divremfv.internal.airdata.Constraint) (Bits' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Bits" l) v.Bits' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Bits" l) Bits' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Bits' := Bits' } : divremfv.internal.airdata.Constraint) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_load_Sources (l : Loc) (v : divremfv.internal.airdata.Constraint) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Sources" l) v.Sources' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Sources" l) v.Sources' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_store_Sources (l : Loc) (v : divremfv.internal.airdata.Constraint) (Sources' : GoSlice) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Sources" l) v.Sources' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Sources" l) Sources' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Sources' := Sources' } : divremfv.internal.airdata.Constraint) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_load_Targets (l : Loc) (v : divremfv.internal.airdata.Constraint) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Targets" l) v.Targets' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Targets" l) v.Targets' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Constraint_access_store_Targets (l : Loc) (v : divremfv.internal.airdata.Constraint) (Targets' : GoSlice) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Targets" l) v.Targets' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Constraint go!"Targets" l) Targets' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Targets' := Targets' } : divremfv.internal.airdata.Constraint) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end Constraint

namespace Artifact
section def_

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [divremfv.internal.airdata.Artifact.TypeAssumptions]

instance Artifact_typed_pointsto :
    TypedPointsto (GF := GF) divremfv.internal.airdata.Artifact where
  typedPointstoDef l v dq := iprop(
    "Format" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Format" l) v.Format' dq ∗
    "Field" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Field" l) v.Field' dq ∗
    "Modulus" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Modulus" l) v.Modulus' dq ∗
    "Modules" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Modules" l) v.Modules' dq ∗
    "Constraints" ∷ typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Constraints" l) v.Constraints' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance Artifact_into_val_typed :
    IntoValTypedUnderlying (GF := GF) divremfv.internal.airdata.Artifact divremfv.internal.airdata.Artifact.underlying := by
  solve_into_val_typed_struct

instance Artifact_access_load_Format (l : Loc) (v : divremfv.internal.airdata.Artifact) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Format" l) v.Format' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Format" l) v.Format' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Artifact_access_store_Format (l : Loc) (v : divremfv.internal.airdata.Artifact) (Format' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Format" l) v.Format' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Format" l) Format' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Format' := Format' } : divremfv.internal.airdata.Artifact) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Artifact_access_load_Field (l : Loc) (v : divremfv.internal.airdata.Artifact) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Field" l) v.Field' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Field" l) v.Field' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Artifact_access_store_Field (l : Loc) (v : divremfv.internal.airdata.Artifact) (Field' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Field" l) v.Field' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Field" l) Field' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Field' := Field' } : divremfv.internal.airdata.Artifact) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Artifact_access_load_Modulus (l : Loc) (v : divremfv.internal.airdata.Artifact) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Modulus" l) v.Modulus' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Modulus" l) v.Modulus' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Artifact_access_store_Modulus (l : Loc) (v : divremfv.internal.airdata.Artifact) (Modulus' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Modulus" l) v.Modulus' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Modulus" l) Modulus' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Modulus' := Modulus' } : divremfv.internal.airdata.Artifact) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Artifact_access_load_Modules (l : Loc) (v : divremfv.internal.airdata.Artifact) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Modules" l) v.Modules' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Modules" l) v.Modules' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Artifact_access_store_Modules (l : Loc) (v : divremfv.internal.airdata.Artifact) (Modules' : GoSlice) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Modules" l) v.Modules' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Modules" l) Modules' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Modules' := Modules' } : divremfv.internal.airdata.Artifact) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

instance Artifact_access_load_Constraints (l : Loc) (v : divremfv.internal.airdata.Artifact) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Constraints" l) v.Constraints' dq)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Constraints" l) v.Constraints' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance Artifact_access_store_Constraints (l : Loc) (v : divremfv.internal.airdata.Artifact) (Constraints' : GoSlice) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Constraints" l) v.Constraints' (DFrac.own 1))
      (typedPointsto (structFieldRef divremfv.internal.airdata.Artifact go!"Constraints" l) Constraints' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Constraints' := Constraints' } : divremfv.internal.airdata.Artifact) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end Artifact

end divremfv.internal.airdata
end Perennial

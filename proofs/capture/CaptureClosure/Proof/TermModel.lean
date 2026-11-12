module
public import CaptureSyntax
public import CaptureClosure.Proof.TermCapture

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

abbrev ModelTerm := DivRemFV.CaptureSyntax.Term
abbrev ModelArgs := DivRemFV.CaptureSyntax.Args

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear
local notation "FType" => github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty
local notation "Air" => github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.ty FType
local notation "Const" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Constant
local notation "Access" => github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess
local notation "Add" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Add
local notation "Sub" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Sub
local notation "Mul" => github_com.LFDT_Lineth.zkc.pkg.ir.term.Mul

-- Read-only ownership permits shared AIR subtrees.
mutual
  def InputTerm : ModelTerm → GoInterface → IProp GF
    | .constant value, source => iprop(∃ (p : Loc) (raw : w32),
        ⌜source = interface.mkOk (go.PointerType (github_com.LFDT_Lineth.zkc.pkg.ir.term.Constant.ty FType Air)) #p ∧ p ≠ null ∧
          decodedValue raw.toNat = value.val⌝ ∗
        p.[Const (GoArray w32 1) GoInterface, go!"Value"] ↦{DFrac.discard} (array.mk 1 [raw]))
    | .column id shift, source => iprop(∃ (p : Loc) (index offset : w64),
        ⌜source = interface.mkOk (go.PointerType (github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess.ty FType Air)) #p ∧ p ≠ null ∧
          index.toNat = id ∧ sint.Z offset = shift ∧ index ≠ W64 (2^64-1)⌝ ∗
        p.[Access (GoArray w32 1) GoInterface, go!"register"] ↦{DFrac.discard}
          (github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.mk index) ∗
        p.[Access (GoArray w32 1) GoInterface, go!"shift"] ↦{DFrac.discard} offset)
    | .sum args, source => iprop(∃ (p : Loc) (sl : GoSlice) (values : List GoInterface),
        ⌜source = interface.mkOk (go.PointerType (github_com.LFDT_Lineth.zkc.pkg.ir.term.Add.ty FType Air)) #p ∧ p ≠ null⌝ ∗
        p.[Add (GoArray w32 1) GoInterface, go!"Args"] ↦{DFrac.discard} sl ∗
        ownSlice sl values DFrac.discard ∗ InputArgs args values)
    | .product args, source => iprop(∃ (p : Loc) (sl : GoSlice) (values : List GoInterface),
        ⌜source = interface.mkOk (go.PointerType (github_com.LFDT_Lineth.zkc.pkg.ir.term.Mul.ty FType Air)) #p ∧ p ≠ null⌝ ∗
        p.[Mul (GoArray w32 1) GoInterface, go!"Args"] ↦{DFrac.discard} sl ∗
        ownSlice sl values DFrac.discard ∗ InputArgs args values)
    | .difference first rest, source => iprop(∃ (p : Loc) (sl : GoSlice) (head : GoInterface) (values : List GoInterface),
        ⌜source = interface.mkOk (go.PointerType (github_com.LFDT_Lineth.zkc.pkg.ir.term.Sub.ty FType Air)) #p ∧ p ≠ null⌝ ∗
        p.[Sub (GoArray w32 1) GoInterface, go!"Args"] ↦{DFrac.discard} sl ∗
        ownSlice sl (head :: values) DFrac.discard ∗ InputTerm first head ∗ InputArgs rest values)
  def InputArgs : ModelArgs → List GoInterface → IProp GF
    | .nil, [] => iprop(True)
    | .cons h t, v :: vs => iprop(InputTerm h v ∗ InputArgs t vs)
    | _, _ => iprop(False)
end

mutual
  theorem input_term_persistent (model : ModelTerm) (source : GoInterface) :
      Persistent (InputTerm (GF := GF) model source) := by
    cases model with
    | constant value => simp only [InputTerm]; infer_instance
    | column index shift => simp only [InputTerm]; infer_instance
    | sum args =>
      letI (vs : List GoInterface) := input_args_persistent args vs
      simp only [InputTerm]; infer_instance
    | product args =>
      letI (vs : List GoInterface) := input_args_persistent args vs
      simp only [InputTerm]; infer_instance
    | difference first rest =>
      letI (v : GoInterface) := input_term_persistent first v
      letI (vs : List GoInterface) := input_args_persistent rest vs
      simp only [InputTerm]; infer_instance
  theorem input_args_persistent (model : ModelArgs) (source : List GoInterface) :
      Persistent (InputArgs (GF := GF) model source) := by
    cases model with
    | nil => cases source <;> simp only [InputArgs] <;> infer_instance
    | cons head tail =>
      cases source with
      | nil => simp only [InputArgs]; infer_instance
      | cons value rest =>
        letI := input_term_persistent head value
        letI := input_args_persistent tail rest
        simp only [InputArgs]; infer_instance
end

instance (model : ModelTerm) (source : GoInterface) :
    Persistent (InputTerm (GF := GF) model source) := input_term_persistent model source

instance (model : ModelArgs) (source : List GoInterface) :
    Persistent (InputArgs (GF := GF) model source) := input_args_persistent model source

mutual
  def OutputTerm : ModelTerm → Term → IProp GF
    | .constant value, result => iprop(
        ⌜result.Kind' = go!"constant" ∧ result.Value' = W64 value.val ∧ result.Column' = W64 0 ∧ result.Shift' = W64 0⌝ ∗
        ownSlice result.Args' ([] : List Term) (DFrac.own 1))
    | .column id shift, result => iprop(
        ⌜result.Kind' = go!"column" ∧ result.Value' = W64 0 ∧ result.Column'.toNat = id ∧ sint.Z result.Shift' = shift⌝ ∗
        ownSlice result.Args' ([] : List Term) (DFrac.own 1))
    | .sum args, result => iprop(∃ values : List Term,
        ⌜result.Kind' = go!"add" ∧ result.Value' = W64 0 ∧ result.Column' = W64 0 ∧ result.Shift' = W64 0⌝ ∗
        ownSlice result.Args' values (DFrac.own 1) ∗ OutputArgs args values)
    | .product args, result => iprop(∃ values : List Term,
        ⌜result.Kind' = go!"mul" ∧ result.Value' = W64 0 ∧ result.Column' = W64 0 ∧ result.Shift' = W64 0⌝ ∗
        ownSlice result.Args' values (DFrac.own 1) ∗ OutputArgs args values)
    | .difference first rest, result => iprop(∃ (head : Term) (values : List Term),
        ⌜result.Kind' = go!"sub" ∧ result.Value' = W64 0 ∧ result.Column' = W64 0 ∧ result.Shift' = W64 0⌝ ∗
        ownSlice result.Args' (head :: values) (DFrac.own 1) ∗ OutputTerm first head ∗ OutputArgs rest values)
  def OutputArgs : ModelArgs → List Term → IProp GF
    | .nil, [] => iprop(True)
    | .cons h t, v :: vs => iprop(OutputTerm h v ∗ OutputArgs t vs)
    | _, _ => iprop(False)
end

abbrev InputList (models : List ModelTerm) (sources : List GoInterface) : IProp GF :=
  iprop([∗list] k ↦ model;source ∈ models;sources, InputTerm model source)

abbrev OutputList (models : List ModelTerm) (results : List Term) : IProp GF :=
  iprop([∗list] k ↦ model;result ∈ models;results, OutputTerm model result)

theorem input_args_list (models : ModelArgs) (sources : List GoInterface) :
    InputArgs (GF := GF) models sources ⊣⊢ InputList models.toList sources := by
  cases models with
  | nil => cases sources with
    | nil => exact true_emp
    | cons _ _ => exact .rfl
  | cons head tail => cases sources with
    | nil => exact .rfl
    | cons value rest => exact sep_congr_right (input_args_list tail rest)
termination_by sizeOf models

theorem output_args_list (models : ModelArgs) (results : List Term) :
    OutputArgs (GF := GF) models results ⊣⊢ OutputList models.toList results := by
  cases models with
  | nil => cases results with
    | nil => exact true_emp
    | cons _ _ => exact .rfl
  | cons head tail => cases results with
    | nil => exact .rfl
    | cons value rest => exact sep_congr_right (output_args_list tail rest)
termination_by sizeOf models

end
end divremfv.internal.airdata.SourceCapture
end Perennial




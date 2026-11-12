module
public import CaptureClosure.Proof.RecordBounds

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem artifact_bounded (model : DivRemFV.CaptureSyntax.Artifact) (value : Artifact) (dq : DFrac)
    (size : model.words.length < 2^64) :
    ArtifactValue (GF := GF) model value dq ⊢ iprop(⌜WordsBounded model.words⌝) := by
  iintro Hmodel
  isimp only [ArtifactValue] at Hmodel
  icases Hmodel with ⟨%modules,%constraints,_,Hmodules,HmoduleModels,Hconstraints,HconstraintModels⟩
  ihave %HmoduleLen := ownSlice_len $$ Hmodules
  ihave %HconstraintLen := ownSlice_len $$ Hconstraints
  ihave %HmoduleCount := BigSepL2.bigSepL2_length $$ HmoduleModels
  ihave %HconstraintCount := BigSepL2.bigSepL2_length $$ HconstraintModels
  ihave %HmoduleBounds := list_models_pure (fun m v => ModuleValue m v dq)
    (fun m => WordsBounded m.words) (fun m v => module_bounded m v dq) model.modules modules $$ HmoduleModels
  have HentrySize (entry : DivRemFV.CaptureSyntax.Entry) (member : entry ∈ model.entries) : entry.words.length < 2^64 := by
    have Hpart := flatMap_member_length model.entries DivRemFV.CaptureSyntax.Entry.words entry member
    simp only [DivRemFV.CaptureSyntax.Artifact.words,List.length_append,List.length_cons] at size
    omega
  ihave %HentryBounds := list_models_pure_member (fun m v => EntryValue m v dq)
    (fun m => WordsBounded m.words) model.entries constraints
    (fun m member v => entry_bounded m v dq (HentrySize m member)) $$ HconstraintModels
  ipureintro
  have Hprefix : WordsBounded [1146242647,1,DivRemFV.CaptureSyntax.modulus,model.modules.length] := by
    simp only [bounded_cons,bounded_nil,_root_.and_true]
    exact ⟨by decide,by decide,by decide,by word⟩
  have Hmodules := bounded_flatMap model.modules DivRemFV.CaptureSyntax.Module.words HmoduleBounds
  have Hentries := (bounded_cons _ _).2
    ⟨(show model.entries.length < 2^64 by word),bounded_flatMap model.entries DivRemFV.CaptureSyntax.Entry.words HentryBounds⟩
  simpa only [DivRemFV.CaptureSyntax.Artifact.words,bounded_append] using And.intro (And.intro Hprefix Hmodules) Hentries

#print axioms artifact_bounded
end
end divremfv.internal.airdata.SourceCapture
end Perennial

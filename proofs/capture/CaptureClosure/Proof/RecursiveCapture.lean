module
public import CaptureClosure.Proof.CompositeCapture

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
variable [Term.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Constant.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Add.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Sub.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Mul.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.TypeAssumptions]
variable [FuncUnfold ExportTerm [] ExportTerm.impl]
variable [FuncUnfold github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.montgomeryReduce []
  github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.montgomeryReduce.impl]
variable [FuncUnfold math.bits.Sub32 [] math.bits.Sub32.impl]

mutual
  theorem capture_term (model : ModelTerm) (source : GoInterface) :
      ⊢ iprop({{ InputTerm (GF := GF) model source }}
        (App (Val (@! ExportTerm)) (Val #source))
        {{ (result : Term), RET (PairV #result #interface.nil); OutputTerm model result }}) := by
    cases model with
    | constant value =>
      imodintro
      iintro %Φ Hsource HΦ
      iunfold InputTerm at Hsource
      icases Hsource with ⟨%p,%raw,⟨%Hsource,%nonnull,%Hvalue⟩,Hfield⟩
      subst source
      wp_apply (constant_capture p raw DFrac.discard nonnull) $$ Hfield with %args Hargs
      iapply HΦ
      simp only [OutputTerm]
      isplitl []
      · ipureintro; simp [Hvalue]
      iexact Hargs
    | column id shift =>
      imodintro
      iintro %Φ Hsource HΦ
      iunfold InputTerm at Hsource
      icases Hsource with ⟨%p,%index,%offset,⟨%Hsource,%nonnull,%Hindex,%Hshift,%valid⟩,Hreg,Hshift⟩
      subst source
      wp_apply (column_capture p index offset DFrac.discard nonnull valid)
        $$ [Hreg Hshift] with %args Hargs
      · iframe Hreg Hshift
      iapply HΦ
      simp only [OutputTerm]
      isplitl []
      · ipureintro; simp [Hindex,Hshift]
      iexact Hargs
    | sum args =>
      imodintro
      iintro %Φ Hsource HΦ
      iunfold InputTerm at Hsource
      icases Hsource with ⟨%p,%sl,%sources,⟨%Hsource,%nonnull⟩,Hfield,Hsl,Hargs⟩
      subst source
      ihave #Hlist := (input_args_list args sources).1 $$ Hargs
      wp_apply (sum_capture p sl args sources nonnull (capture_arg_calls args))
        $$ [Hfield Hsl] with %result Hresult
      · iframe; iframe #
      iapply HΦ $$ Hresult
    | product args =>
      imodintro
      iintro %Φ Hsource HΦ
      iunfold InputTerm at Hsource
      icases Hsource with ⟨%p,%sl,%sources,⟨%Hsource,%nonnull⟩,Hfield,Hsl,Hargs⟩
      subst source
      ihave #Hlist := (input_args_list args sources).1 $$ Hargs
      wp_apply (product_capture p sl args sources nonnull (capture_arg_calls args))
        $$ [Hfield Hsl] with %result Hresult
      · iframe; iframe #
      iapply HΦ $$ Hresult
    | difference first rest =>
      imodintro
      iintro %Φ Hsource HΦ
      iunfold InputTerm at Hsource
      icases Hsource with ⟨%p,%sl,%head,%sources,⟨%Hsource,%nonnull⟩,Hfield,Hsl,Hhead,Hrest⟩
      subst source
      have calls : ∀ m ∈ first :: rest.toList, ∀ s : GoInterface,
          ⊢ iprop({{ InputTerm (GF := GF) m s }}
            (App (Val (@! ExportTerm)) (Val #s))
            {{ (result : Term), RET (PairV #result #interface.nil); OutputTerm m result }}) := by
        intro m member s
        rcases List.mem_cons.mp member with equal | inside
        · subst m
          exact capture_term first s
        · exact capture_arg_calls rest m inside s
      ihave #Htail := (input_args_list rest sources).1 $$ Hrest
      wp_apply (difference_capture p sl first rest (head :: sources) nonnull calls)
        $$ [Hfield Hsl Hhead] with %result Hresult
      · iframe
        iframe #
      iapply HΦ $$ Hresult

  theorem capture_arg_calls (args : ModelArgs) (model : ModelTerm)
      (member : model ∈ args.toList) (source : GoInterface) :
      ⊢ iprop({{ InputTerm (GF := GF) model source }}
        (App (Val (@! ExportTerm)) (Val #source))
        {{ (result : Term), RET (PairV #result #interface.nil); OutputTerm model result }}) := by
    cases args with
    | nil => simp [DivRemFV.CaptureSyntax.Args.toList] at member
    | cons first rest =>
      rcases List.mem_cons.mp member with equal | inside
      · subst model
        exact capture_term first source
      · exact capture_arg_calls rest model inside source
end

#print axioms capture_term
#print axioms capture_arg_calls
end
end divremfv.internal.airdata.SourceCapture
end Perennial

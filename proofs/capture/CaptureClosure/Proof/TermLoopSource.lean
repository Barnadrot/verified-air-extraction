module
public import CaptureClosure.Proof.TermModel

@[expose] public section
noncomputable section
namespace Perennial.divremfv.internal.airdata.SourceCapture

@[reducible] def captureArgsExpr [FfiSyntax] [GoGlobalContext] : Expr :=
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (_root_.Perennial.github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.ty _root_.Perennial.github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty)))) (Var "arg"))
  (App (App (Val (GoInstruction (FuncResolve ExportTerm []))) (Val #())) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc Term.ty))) (App (Val (GoInstruction (GoZeroVal Term.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType Term.ty)))) (App (Val (GoInstruction (StructFieldRef Term.ty go!"Args"))) (Var "out")))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (GoLoad Term.ty))) (Var "v"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType Term.ty)))) (LiteralValue [(KeyedElement none (ElementExpression Term.ty (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType Term.ty)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType Term.ty)))) (Pair (App (Val (GoInstruction (StructFieldRef Term.ty go!"Args"))) (Var "out")) (Var "$r0")))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Pair (App (Val (GoInstruction (GoLoad Term.ty))) (Var "out")) (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore Term.ty))) (Pair (Var "v") (Var "$r0"))))))))))))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (_root_.Perennial.github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.ty _root_.Perennial.github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty)))) (Pair (Var "arg") (Var "$value")))))))

@[reducible] def captureArgsBody [FfiSyntax] [GoGlobalContext] (out arg : Loc) : val :=
  (LamV "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (_root_.Perennial.github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.ty _root_.Perennial.github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty)))) (Val #arg))
  (App (App (Val (GoInstruction (FuncResolve ExportTerm []))) (Val #())) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc Term.ty))) (App (Val (GoInstruction (GoZeroVal Term.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType Term.ty)))) (App (Val (GoInstruction (StructFieldRef Term.ty go!"Args"))) (Val #out)))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (GoLoad Term.ty))) (Var "v"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType Term.ty)))) (LiteralValue [(KeyedElement none (ElementExpression Term.ty (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType Term.ty)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType Term.ty)))) (Pair (App (Val (GoInstruction (StructFieldRef Term.ty go!"Args"))) (Val #out)) (Var "$r0")))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Pair (App (Val (GoInstruction (GoLoad Term.ty))) (Val #out)) (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore Term.ty))) (Pair (Var "v") (Var "$r0"))))))))))))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (_root_.Perennial.github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.ty _root_.Perennial.github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty)))) (Pair (Val #arg) (Var "$value")))))))

theorem captureArgsBody_source [FfiSyntax] [GoGlobalContext] (out arg : Loc) :
    (match subst "arg" #arg (subst "out" #out captureArgsExpr) with
      | .Rec name arg body => .RecV name arg body
      | _ => #()) = captureArgsBody out arg := by rfl

end Perennial.divremfv.internal.airdata.SourceCapture

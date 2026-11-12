"""Copy a translated source loop for a reusable WP lemma.

This does not add source semantics. The parent program proof must match this
expression by kernel conversion at the actual loop in ExportTerm.impl.
"""
from pathlib import Path

root = Path(__file__).resolve().parent
source = (root / "CaptureClosure/Code/divremfv/internal/airdata.lean").read_text(encoding="utf-8")
source = source[source.index("noncomputable def ExportTerm.impl"):]
start = source.index('(Lam "$key"')
depth, quoted, escaped = 0, False, False
for end in range(start, len(source)):
    char = source[end]
    if quoted:
        if escaped:
            escaped = False
        elif char == "\\":
            escaped = True
        elif char == '"':
            quoted = False
    elif char == '"':
        quoted = True
    elif char == "(":
        depth += 1
    elif char == ")":
        depth -= 1
        if not depth:
            break
else:
    raise ValueError("unclosed source loop")
body = source[start:end+1]
closed = body.replace('(Lam "$key"', '(LamV "$key"', 1)
closed = closed.replace('(Var "arg")', '(Val #arg)').replace('(Var "out")', '(Val #out)')
result = '''module
public import CaptureClosure.Proof.TermModel

@[expose] public section
noncomputable section
namespace Perennial.divremfv.internal.airdata.SourceCapture

@[reducible] def captureArgsExpr [FfiSyntax] [GoGlobalContext] : Expr :=
  ''' + body + '''

@[reducible] def captureArgsBody [FfiSyntax] [GoGlobalContext] (out arg : Loc) : val :=
  ''' + closed + '''

theorem captureArgsBody_source [FfiSyntax] [GoGlobalContext] (out arg : Loc) :
    (match subst "arg" #arg (subst "out" #out captureArgsExpr) with
      | .Rec name arg body => .RecV name arg body
      | _ => #()) = captureArgsBody out arg := by rfl

end Perennial.divremfv.internal.airdata.SourceCapture
'''
(root / "CaptureClosure/Proof/TermLoopSource.lean").write_text(result, encoding="utf-8")
print("Copied the actual ExportTerm argument-loop expression for kernel matching")

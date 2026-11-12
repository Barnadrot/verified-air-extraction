"""Emit source-linked getter statements; Lean checks each proof body."""
from pathlib import Path

root = Path(__file__).resolve().parent
header = '''module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
'''
base = 'github_com.LFDT_Lineth.zkc.pkg.schema.constraint.'
for kind in ('vanishing', 'ranged', 'lookup', 'bus'):
    header += 'public import CaptureClosure.Code.'+base+kind+'\n'
header += '''
@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
'''
blocks = []
for kind in ('vanishing', 'ranged', 'lookup', 'bus'):
    has_term = kind == 'vanishing'
    gt = 'F T' if has_term else 'F'
    lt = "F' T'" if has_term else "F'"
    variables = '''variable (F : go.GoType) {F' : Type} [ZeroVal F'] [TypeRepr F F']
'''
    if has_term:
        variables += "variable (T : go.GoType) {T' : Type} [ZeroVal T'] [TypeRepr T T']\n"
    blocks.append('namespace '+base+kind+'''
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Constraint.TypeAssumptions]
'''+variables+f'''
theorem Constraint.name_correct (p : Loc) (name : GoString) (dq : DFrac) (nonnull : p ≠ null) :
    {{{{ (p.[Constraint {lt},go!"Handle"] ↦{{dq}} name : IProp GF) }}}}
      (App (Val (p @!! go.PointerType (Constraint.ty {gt}) @!! go!"Name")) (Val #()))
    {{{{ RET #name; p.[Constraint {lt},go!"Handle"] ↦{{dq}} name }}}} := by
  wp_start as Hname
  wp_auto
  iapply HΦ $$ Hname

#print axioms Constraint.name_correct
end
end {base+kind}
''')
(root/'CaptureClosure/Proof/ConstraintReads.lean').write_text(
    header+'\n'.join(blocks)+'end Perennial\n', encoding='utf-8')
print('Emitted the four actual constraint-name getter proofs')

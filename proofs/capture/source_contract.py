"""Assemble explicit contexts for the checked API composition.

No source semantics are generated here. Both APIs refer to translated Go bodies.
"""
from pathlib import Path
root = Path(__file__).resolve().parent
declarations = []
for name in ('ArtifactCapture', 'CheckedWire'):
    source = (root/f'CaptureClosure/Proof/{name}.lean').read_text(encoding='utf-8')
    context = source[source.index('variable [Artifact.TypeAssumptions]'):source.index('\ntheorem ')]
    for part in ('\n'+context).split('\nvariable '):
        part = part.strip()
        if part:
            declaration = 'variable ' + part
            if declaration not in declarations:
                declarations.append(declaration)
header = '''module
public import CaptureClosure.Proof.ArtifactCapture
public import CaptureClosure.Proof.CheckedWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
open github_com.LFDT_Lineth.zkc.pkg.schema
open github_com.LFDT_Lineth.zkc.pkg.schema.register
local notation "SourceSchema" => UniformSchema (GoArray w32 1) Loc
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
'''
body = '''

theorem capture_to_checked_wire (tables : List TableData) (entries : List (List DivRemFV.CaptureSyntax.Entry))
    (schema : SourceSchema) (inputTag outputTag : Type') :
    {{ (InputSchema tables entries schema ∗ globalAddr INPUT_REGISTER ↦□ inputTag ∗
        globalAddr OUTPUT_REGISTER ↦□ outputTag : IProp GF) }}
      (App (Val (@! Export)) (Val #schema))
    {{ (artifact : Artifact), RET (PairV #artifact #interface.nil);
      WP (App (Val (@! EncodeArtifactWire)) (Val #artifact))
        {{ value, ∃ result : GoSlice, ⌜value = PairV #result #interface.nil⌝ ∗
          WireResult (schemaModel tables entries inputTag outputTag) result }} }} := by
  iintro %Φ ⟨Hsource,Hinput,Houtput⟩ HΦ
  iapply (capture_artifact tables entries schema inputTag outputTag) $$ [Hsource Hinput Houtput]
  · iframe Hsource Hinput Houtput
  iintro %artifact
  imodintro
  iintro Hcaptured
  iapply HΦ
  iapply (serialize_checked_artifact (schemaModel tables entries inputTag outputTag) artifact (DFrac.own 1)) $$ [Hcaptured]
  · iframe Hcaptured
  iintro %result
  imodintro
  iintro Hwire
  iexists result
  iframe Hwire
  ipureintro; rfl

#print axioms capture_to_checked_wire
end
end divremfv.internal.airdata.SourceCapture
end Perennial
'''
(root/'CaptureClosure/Proof/SourceContract.lean').write_text(header+'\n'.join(declarations)+body,encoding='utf-8')
print('Emitted checked capture-to-byte API composition')

"""Specialize the ordered-list proof skeleton to actual Go column records."""
from pathlib import Path
root=Path(__file__).resolve().parent
source=(root/'CaptureClosure/Proof/RowsWire.lean').read_text(encoding='utf-8')
start=source.index('theorem serialize_rows ')
end=source.index('\n#print axioms serialize_row',start)
body=source[start:end]
for old,new in (
    ('serialize_rows','serialize_columns'),('appendWireRows','appendWireColumns'),
    ('List (List Nat)','List DivRemFV.CaptureSyntax.Column'),('List GoSlice','List Column'),
    ('RowsValue','ColumnsValue'),('DivRemFV.CaptureSyntax.natWords','DivRemFV.CaptureSyntax.Column.words'),
    ('(last : GoSlice)','(last : Column)'),('"row" ∷ row_ptr','"c" ∷ c_ptr'),
    ('[i out row Hout','[i out c Hout'),('next,slice.nil','next,zero_val Column'),
    ('serialize_row _ _','serialize_column _ _')):
    body=body.replace(old,new)
header='''module
public import CaptureClosure.Proof.ColumnModel

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Column.TypeAssumptions]
variable [FuncUnfold appendWireColumns [] appendWireColumns.impl]
variable [FuncUnfold appendWireColumn [] appendWireColumn.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]
variable [FuncUnfold appendWireName [] appendWireName.impl]
variable [FuncUnfold appendWireBool [] appendWireBool.impl]

abbrev ColumnsValue (models : List DivRemFV.CaptureSyntax.Column) (values : List Column) (dq : DFrac) : IProp GF :=
  iprop([∗list] k ↦ model;value ∈ models;values, ColumnValue model value dq)

'''
(root/'CaptureClosure/Proof/ColumnsWire.lean').write_text(header+body+'''
#print axioms serialize_columns
end
end divremfv.internal.airdata.SourceCapture
end Perennial
''',encoding='utf-8')
print('Emitted actual column-list serialization proof')

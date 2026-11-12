"""Instantiate the kernel-checked ordered-list pattern for Go records.

This only emits proof text. Lean must check each generated theorem.
"""
from pathlib import Path

root = Path(__file__).resolve().parent
source = (root / 'CaptureClosure/Proof/RowsWire.lean').read_text(encoding='utf-8')
body = source[source.index('theorem serialize_rows '):source.index('\n#print axioms serialize_row')]
common = source[source.index('variable [ext :'):source.index('variable [sem :')]

for plural, singular, record, model, extra in [
    ('ports', 'port', 'Vector', 'Port', '''variable [Vector.TypeAssumptions]
variable [FuncUnfold appendWirePort [] appendWirePort.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]'''),
    ('constraints', 'entry', 'Constraint', 'Entry', '''variable [Constraint.TypeAssumptions] [Term.TypeAssumptions] [Vector.TypeAssumptions]
variable [FuncUnfold appendWireConstraint [] appendWireConstraint.impl]
variable [FuncUnfold appendWireName [] appendWireName.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]
variable [FuncUnfold appendWireDomain [] appendWireDomain.impl]
variable [FuncUnfold appendWireFramedTerm [] appendWireFramedTerm.impl]
variable [FuncUnfold EncodeTermWire [] EncodeTermWire.impl]
variable [FuncUnfold appendTermWire [] appendTermWire.impl]
variable [FuncUnfold appendArgsWire [] appendArgsWire.impl]
variable [FuncUnfold appendWirePorts [] appendWirePorts.impl]
variable [FuncUnfold appendWirePort [] appendWirePort.impl]'''),
    ('modules', 'module', 'Module', 'Module', '''variable [Module.TypeAssumptions] [Column.TypeAssumptions]
variable [FuncUnfold appendWireModule [] appendWireModule.impl]
variable [FuncUnfold appendWireColumns [] appendWireColumns.impl]
variable [FuncUnfold appendWireColumn [] appendWireColumn.impl]
variable [FuncUnfold appendWireRows [] appendWireRows.impl]
variable [FuncUnfold appendWireRow [] appendWireRow.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]
variable [FuncUnfold appendWireName [] appendWireName.impl]
variable [FuncUnfold appendWireBool [] appendWireBool.impl]''')]:
    cap = plural.capitalize()
    one = singular.capitalize()
    text = body
    for old, new in [
        ('serialize_rows', f'serialize_{plural}'), ('appendWireRows', f'appendWire{cap}'),
        ('List (List Nat)', f'List DivRemFV.CaptureSyntax.{model}'),
        ('List GoSlice', f'List {record}'), ('RowsValue', f'{cap}Value'),
        ('DivRemFV.CaptureSyntax.natWords', f'DivRemFV.CaptureSyntax.{model}.words'),
        ('(last : GoSlice)', f'(last : {record})'),
        ('"row" ∷ row_ptr', '"p" ∷ p_ptr' if plural == 'ports' else '"m" ∷ m_ptr' if plural == 'modules' else '"c" ∷ c_ptr'),
        ('[i out row Hout', '[i out p Hout' if plural == 'ports' else '[i out m Hout' if plural == 'modules' else '[i out c Hout'),
        ('next,slice.nil', f'next,zero_val {record}'),
        ('serialize_row _ _', f'serialize_{singular} _ _')]:
        text = text.replace(old, new)
    if plural == 'constraints':
        text = text.replace('RET #result;', 'RET (PairV #result #interface.nil);')
    dependency = {'ports': 'PortModel', 'modules': 'ModuleWire', 'constraints': 'ConstraintWire'}[plural]
    header = f'''module
public import CaptureClosure.Proof.{dependency}

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
section
{common}variable [sem : go.Semantics]
{extra}
variable [FuncUnfold appendWire{cap} [] appendWire{cap}.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

abbrev {cap}Value (models : List DivRemFV.CaptureSyntax.{model}) (values : List {record}) (dq : DFrac) : IProp GF :=
  iprop([∗list] _k ↦ model;value ∈ models;values, {one}Value model value dq)

'''
    (root / f'CaptureClosure/Proof/{cap}Wire.lean').write_text(header + text + f'''
#print axioms serialize_{plural}
end
end divremfv.internal.airdata.SourceCapture
end Perennial
''', encoding='utf-8')
print('Emitted ordered port, module and constraint serialization proofs')

"""Emit the ordered capture loops; generated proofs require kernel checks."""
from pathlib import Path
root = Path(__file__).resolve().parent
source = (root/'CaptureClosure/Proof/RowsCapture.lean').read_text(encoding='utf-8')
body = source[source.index('theorem capture_rows '):source.index('\n#print axioms capture_rows')]
for kind, record, function in [('Lookup', 'lookup.Vector', 'exportLookupVectors'), ('Bus', 'bus.Port', 'exportBusPorts')]:
    term = 'lookup' if kind == 'Lookup' else 'bus'
    source_record = 'github_com.LFDT_Lineth.zkc.pkg.schema.constraint.' + record
    text = body
    for old,new in [
        ('capture_rows',f'capture_{term}_ports'), ('exportStaticRows',function),
        ('(raw : List (List w32))','(models : List DivRemFV.CaptureSyntax.Port)'),
        ('(sources : List GoSlice)',f'(sources : List {source_record})'),
        ('List GoSlice','List Vector'), ('ownSliceCap GoSlice','ownSliceCap Vector'),
        ('InputRows raw sources dq',f'Input{kind}Ports models sources'),
        ('RowsValue','PortsValue'), ('capturedRows raw','models'),
        ('raw.length','models.length'), ('raw[sint.nat n]','models[sint.nat n]'),
        ('(go.SliceType (go.SliceType go.uint64))','(go.SliceType Vector.ty)'),
        ('(V := GoSlice) (t := go.SliceType go.uint64)','(V := Vector) (t := Vector.ty)'),
        ('(V := GoSlice) (st := go.SliceType (go.SliceType go.uint64)) (t := go.SliceType go.uint64)',
         '(V := Vector) (st := go.SliceType Vector.ty) (t := Vector.ty)'),
        ('"values" ∷ values_ptr','"out" ∷ out_ptr'), ('"row" ∷ row_ptr','"v" ∷ v_ptr'),
        ('[i values row Hsource','[i out v Hsource'),
        ('(last : GoSlice)',f'(last : {source_record})'),
        ('_,slice.nil,[]',f'_,zero_val {source_record},[]'),
        ('capture_static_row sources[sint.nat n] models[sint.nat n] dq',
         f'capture_{term}_model models[sint.nat n] sources[sint.nat n]'),
        ('with %row ⟨Hrow,HrowCap,Hchild⟩','with %row ⟨Hrow,Hchild⟩'),
        ('have Hmodel := List.getElem?_eq_getElem Hmlt','have Hmodel := List.getElem?_eq_getElem Hmlt')]:
        text = text.replace(old,new)
    start = text.index('    have Hvalue :')
    end = text.index('    rw [Hstep',start)
    text = text[:start] + '    have Hvalue := List.getElem?_eq_getElem Hmlt\n' + text[end:]
    text = text.replace('[(rowValues models[sint.nat n]).map BitVec.toNat]','[models[sint.nat n]]')
    text = text.replace('by simp [capturedRows]; word','by word')
    start = text.index('      iframe Hmodels\n      isimp only [RowValue]')
    end = text.index('    iframe\n',start)
    text = text[:start]+'      iframe Hmodels Hrow\n'+text[end:]
    header = '''module
public import CaptureClosure.Proof.PortCapture

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port.TypeAssumptions]
variable [FuncUnfold lookupVector [] lookupVector.impl]
variable [FuncUnfold busVector [] busVector.impl]
variable [FuncUnfold uintRef [] uintRef.impl]
variable [FuncUnfold exportColumnIDs [] exportColumnIDs.impl]
'''+f'''variable [FuncUnfold {function} [] {function}.impl]

abbrev Input{kind}Ports (models : List DivRemFV.CaptureSyntax.Port) (values : List {source_record}) : IProp GF :=
  iprop([∗list] _k ↦ model;value ∈ models;values, Input{kind}Port model value)

'''
    (root/f'CaptureClosure/Proof/{kind}PortsCapture.lean').write_text(header+text+f'''
#print axioms capture_{term}_ports
end
end divremfv.internal.airdata.SourceCapture
end Perennial
''',encoding='utf-8')
print('Emitted lookup and bus port-list capture proofs')

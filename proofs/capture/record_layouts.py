"""Select checked layout proof scaffolds for the capture records."""
from pathlib import Path

root = Path(__file__).resolve().parent
source = (root/'ClosureProofGenerated/divremfv/internal/airdata.lean').read_text(encoding='utf-8')
header = '''module
public import CaptureClosure.Proof.TermLayout

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata

'''
blocks = []
for name in ('Column','Module','Vector','Constraint','Artifact'):
    start = source.index('\nnamespace '+name+'\n')+1
    end = source.index('\nend '+name+'\n',start)+len('\nend '+name+'\n')
    block = source[start:end]
    block = block.replace("variable [package_sem' : divremfv.internal.airdata.Assumptions]",
                          'variable [divremfv.internal.airdata.'+name+'.TypeAssumptions]')
    blocks.append(block)
result = header+'\n'.join(blocks)+'\nend divremfv.internal.airdata\nend Perennial\n'
(root/'CaptureClosure/Proof/RecordLayouts.lean').write_text(result,encoding='utf-8')
print('Selected record layout proofs for Column, Module, Vector, Constraint and Artifact')

register_ns = 'github_com.LFDT_Lineth.zkc.pkg.schema.register'
register_source = (root/'ClosureProofGenerated/github_com/LFDT_Lineth/zkc/pkg/schema/register.lean').read_text(encoding='utf-8')
register_header = '''module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.schema.register

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace '''+register_ns+'\n\n'
register_blocks=[]
for name, assumption in (("Type'", '«Type»'), ('Register', 'Register')):
    start = register_source.index('\nnamespace '+name+'\n')+1
    end = register_source.index('\nend '+name+'\n', start)+len('\nend '+name+'\n')
    block = register_source[start:end].replace(
        "variable [package_sem' : "+register_ns+'.Assumptions]',
        'variable ['+register_ns+'.«Type».TypeAssumptions]'+
        ('\nvariable ['+register_ns+'.Register.TypeAssumptions]' if name=='Register' else ''))
    register_blocks.append(block)
(root/'CaptureClosure/Proof/RegisterLayouts.lean').write_text(
    register_header+'\n'.join(register_blocks)+'\nend '+register_ns+'\nend Perennial\n', encoding='utf-8')
print('Selected register and register-kind layout proofs')

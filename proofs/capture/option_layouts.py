"""Select the Option record proof scaffold for kernel checking."""
from pathlib import Path

root=Path(__file__).resolve().parent
ns='github_com.LFDT_Lineth.zkc.pkg.util'
source=(root/'ClosureProofGenerated/github_com/LFDT_Lineth/zkc/pkg/util.lean').read_text(encoding='utf-8')
start=source.index('\nnamespace Option\n')+1
end=source.index('\nend Option\n',start)+len('\nend Option\n')
block=source[start:end].replace("variable [package_sem' : "+ns+'.Assumptions]',
                               'variable ['+ns+'.Option.TypeAssumptions]')
header='''module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.util

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace '''+ns+'\n\n'
(root/'CaptureClosure/Proof/OptionLayout.lean').write_text(
    header+block+'\nend '+ns+'\nend Perennial\n',encoding='utf-8')
print('Selected the Option layout proof')

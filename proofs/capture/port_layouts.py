"""Select source record layouts for lookup and bus ports."""
from pathlib import Path

root=Path(__file__).resolve().parent
base='github_com.LFDT_Lineth.zkc.pkg.schema.constraint.'
imports='''module
public import CaptureClosure.Proof.ColumnId
public import CaptureClosure.Proof.OptionLayout
'''
blocks=[]
for kind,name in (('lookup','Vector'),('bus','Port')):
    ns=base+kind
    imports+='public import CaptureClosure.Code.'+ns+'\n'
    source=(root/('ClosureProofGenerated/github_com/LFDT_Lineth/zkc/pkg/schema/constraint/'+kind+'.lean')).read_text(encoding='utf-8')
    start=source.index('\nnamespace '+name+'\n')+1
    end=source.index('\nend '+name+'\n',start)+len('\nend '+name+'\n')
    assumptions='variable ['+ns+'.'+name+'.TypeAssumptions]\n'+\
        'variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]\n'+\
        'variable [github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.TypeAssumptions]'
    block=source[start:end].replace("variable [package_sem' : "+ns+'.Assumptions]',assumptions)
    blocks.append('namespace '+ns+'\n'+block+'end '+ns+'\n')
header=imports+'''
@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
'''
(root/'CaptureClosure/Proof/PortLayouts.lean').write_text(header+'\n'.join(blocks)+'end Perennial\n',encoding='utf-8')
print('Selected lookup-vector and bus-port layout proofs')

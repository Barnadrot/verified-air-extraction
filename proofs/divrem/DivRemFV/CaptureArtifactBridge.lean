import DivRemFV.CaptureBridge
import DivRemFV.FastEncode

namespace DivRemFV.CaptureSyntax

def Column.toWire (c : Column) : ArtifactWire.Column :=
  ⟨c.id,c.name,c.bits,c.input,c.output,c.isNative⟩

def Port.toRaw (p : Port) : DivRemFV.Port :=
  ⟨p.moduleId,p.selector,p.columns.toArray⟩

def Rule.toRaw : Rule → NativeImport.RawConstraint
  | .vanishing owner domain term => .vanishing owner domain term.native
  | .range owner column bits => .range owner column bits
  | .lookup sources targets => .lookup (sources.map Port.toRaw) (targets.map Port.toRaw)
  | .bus sources targets => .bus (sources.map Port.toRaw) (targets.map Port.toRaw)

def Entry.toWire (e : Entry) : ArtifactWire.Entry := ⟨e.id,e.owner,e.name,e.rule.toRaw⟩

def Module.toWire (m : Module) : ArtifactWire.Module :=
  ⟨m.id,m.name,m.isStatic,m.isNative,m.columns.map Column.toWire,m.content⟩

def Artifact.toWire (a : Artifact) : ArtifactWire.Artifact :=
  ⟨a.modules.map Module.toWire,a.entries.map Entry.toWire⟩

theorem Column.words_raw (c : Column) : ArtifactWire.columnWords c.toWire = c.words := rfl

theorem Column.wire_correspondence (c : Column) : ArtifactWire.column.encode c.toWire = c.words := by
  rw [ArtifactWire.column_fast]
  exact c.words_raw

theorem Port.words_raw (p : Port) : ArtifactWire.portWords p.toRaw = p.words := by
  simp [Port.toRaw,ArtifactWire.portWords,Port.words,ArtifactWire.natListWords,natWords,
    ArtifactWire.optionNatWords,optionNatWords]
  rfl

theorem Rule.words_raw (r : Rule) : ArtifactWire.constraintWords r.toRaw = r.words := by
  cases r <;>
    simp [Rule.toRaw,ArtifactWire.constraintWords,Rule.words,Term.wire_correspondence,
      List.flatMap_map,Port.words_raw,ArtifactWire.optionIntWords,optionIntWords,
      ArtifactWire.natListWords,natWords,TermWire.encodeInt,encodeInt]
  all_goals rfl

theorem Entry.words_raw (e : Entry) : ArtifactWire.entryWords e.toWire = e.words := by
  simp [Entry.toWire,ArtifactWire.entryWords,Entry.words,Rule.words_raw,ArtifactWire.natListWords,natWords]

theorem Entry.wire_correspondence (e : Entry) : ArtifactWire.entry.encode e.toWire = e.words := by
  rw [ArtifactWire.entry_fast]
  exact e.words_raw

theorem Module.words_raw (m : Module) : ArtifactWire.moduleWords m.toWire = m.words := by
  have sameNatWords : ArtifactWire.natListWords = natWords := rfl
  simp [Module.toWire,ArtifactWire.moduleWords,Module.words,List.flatMap_map,Column.words_raw,
    sameNatWords,ArtifactWire.boolWords,boolWords]
  rfl

theorem Module.wire_correspondence (m : Module) : ArtifactWire.module.encode m.toWire = m.words := by
  rw [ArtifactWire.module_fast]
  exact m.words_raw

theorem Artifact.wire_correspondence (a : Artifact) : ArtifactWire.artifact.encode a.toWire = a.words := by
  rw [ArtifactWire.artifact_encoding]
  simp [Artifact.toWire,Artifact.words,WireCodec.list,Module.wire_correspondence,Entry.wire_correspondence,
    List.flatMap_map,modulus,fieldModulus]

end DivRemFV.CaptureSyntax

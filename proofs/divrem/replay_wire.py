"""Emit kernel replay data from the complete wire artifact, not from JSON.

The generator is untrusted. Lean checks every emitted record against its wire
tokens. Run compression is lossless and is checked by reconstructing the input.
"""
from pathlib import Path
import hashlib
import json
import struct

ROOT = Path(__file__).resolve().parent
DEST = ROOT / "DivRemFV" / "Replay"
GENERATED = {}
SELECTED = {55,56,61,62,63,64,65,66,84,85,86,90,94,95,96,97,98}


class Reader:
    def __init__(self, data):
        if len(data) % 8:
            raise ValueError("partial word")
        self.words = list(struct.unpack("<" + "Q" * (len(data) // 8), data))
        self.pos = 0

    def word(self):
        v = self.words[self.pos]
        self.pos += 1
        return v

    def expect(self, n):
        if self.word() != n:
            raise ValueError("invalid wire tag")

    def seq(self, read):
        return [read() for _ in range(self.word())]

    def boolean(self):
        n = self.word()
        if n > 1:
            raise ValueError("invalid boolean")
        self.expect(0)
        return bool(n)

    def option(self, read):
        n = self.word()
        if n == 0:
            self.expect(0)
            return None
        if n == 1:
            return read()
        raise ValueError("invalid option")

    def integer(self):
        n = self.word()
        return n // 2 if n % 2 == 0 else -(n // 2 + 1)

    def term(self):
        n = self.word()
        if n == 0:
            v = self.word()
            if v >= 2130706433:
                raise ValueError("noncanonical constant")
            return ("constant", v)
        if n == 1:
            return ("column", self.word(), self.integer())
        if n in (2, 4):
            return ("sum" if n == 2 else "product", self.args())
        if n == 3:
            return ("difference", self.term(), self.args())
        raise ValueError("unknown term")

    def args(self):
        out = []
        while True:
            n = self.word()
            if n == 0:
                return out
            if n != 1:
                raise ValueError("invalid argument list")
            out.append(self.term())

    def port(self):
        return (self.word(), self.option(self.word), self.seq(self.word))

    def rule(self):
        tag = self.word()
        if tag == 0:
            owner = self.word()
            domain = self.option(self.integer)
            n = self.word()
            end = self.pos + n
            t = self.term()
            if self.pos != end:
                raise ValueError("term length differs")
            return ("vanishing", owner, domain, t)
        if tag != 1:
            raise ValueError("unknown constraint")
        tag = self.word()
        if tag == 0:
            return ("range", self.word(), self.word(), self.word())
        if tag != 1:
            raise ValueError("unknown constraint")
        tag = self.word()
        if tag not in (0, 1):
            raise ValueError("unknown constraint")
        return ("lookup" if tag == 0 else "bus", self.seq(self.port), self.seq(self.port))

    def column(self):
        return (self.word(), self.seq(self.word), self.option(self.word),
                self.boolean(), self.boolean(), self.boolean())

    def module(self):
        return (self.word(), self.seq(self.word), self.boolean(), self.boolean(),
                self.seq(self.column), self.seq(lambda: self.seq(self.word)))

    def entry(self):
        return (self.word(), self.word(), self.seq(self.word), self.rule())


def ls(values):
    return "[" + ",".join(map(str, values)) + "]"


def opt(v):
    return "none" if v is None else f"(some ({v}))"


def boolean(v):
    return "true" if v else "false"


def args(v):
    out = ".nil"
    for x in reversed(v):
        out = f"(.cons {term(x)} {out})"
    return out


def term(t):
    kind = t[0]
    if kind == "constant":
        return f"(.constant ⟨{t[1]}, by decide⟩)"
    if kind == "column":
        return f"(.column {t[1]} ({t[2]}))"
    if kind in ("sum", "product"):
        return f"(.{kind} {args(t[1])})"
    return f"(.difference {term(t[1])} {args(t[2])})"


def port(p):
    return f"⟨{p[0]}, {opt(p[1])}, #{ls(p[2])}⟩"


def rule(r):
    kind = r[0]
    if kind == "vanishing":
        return f"(.vanishing {r[1]} {opt(r[2])} {term(r[3])})"
    if kind == "range":
        return f"(.range {r[1]} {r[2]} {r[3]})"
    return f"(.{kind} {ls(map(port, r[1]))} {ls(map(port, r[2]))})"


def column(c):
    return f"⟨{c[0]}, {ls(c[1])}, {opt(c[2])}, {boolean(c[3])}, {boolean(c[4])}, {boolean(c[5])}⟩"


def content(rows):
    if all(row == [i] for i, row in enumerate(rows)):
        return f"((List.range {len(rows)}).map (fun n => [n]))"
    return ls(map(ls, rows))


def module(m, rows=None, columns=None):
    return f"⟨{m[0]}, {ls(m[1])}, {boolean(m[2])}, {boolean(m[3])}, {columns if columns is not None else ls(map(column, m[4]))}, {rows if rows is not None else content(m[5])}⟩"


def entry(e):
    return f"⟨{e[0]}, {e[1]}, {ls(e[2])}, {rule(e[3])}⟩"


def word_expr(words):
    # Compress only arithmetic runs and [1,n] runs. No AIR meaning is used.
    pieces, proofs, literal, expanded = [], [], [], []

    def flush():
        if literal:
            pieces.append(ls(literal))
            proofs.append(f"(by decide : {ls(literal)}.all wordBound = true)")
            expanded.extend(literal)
            literal.clear()

    i = 0
    while i < len(words):
        j = i
        if i + 1 < len(words) and words[i] == 1:
            start = words[i + 1]
            while j + 1 < len(words) and words[j:j+2] == [1, start + (j-i)//2]:
                j += 2
            count = (j-i)//2
            if count >= 32:
                flush()
                pieces.append(f"((List.range' {start} {count}).flatMap (fun n => [1,n]))")
                proofs.append(f"(pairRangeBound {start} {count} (by decide))")
                expanded.extend(x for n in range(start, start+count) for x in (1,n))
                i = j
                continue
        j = i
        start = words[i]
        while j < len(words) and words[j] == start + j-i:
            j += 1
        if j-i >= 32:
            flush()
            pieces.append(f"(List.range' {start} {j-i})")
            proofs.append(f"(rangeBound {start} {j-i} (by decide))")
            expanded.extend(range(start, start+j-i))
            i = j
            continue
        literal.append(words[i])
        i += 1
        if len(literal) == 128:
            flush()
    flush()
    if expanded != words:
        raise AssertionError("compression changed input")
    return list(zip(pieces, proofs))


HEADER = """import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

"""


def emit(name, declaration, words, encoded, extra="", range_table=False, proof=None, write=True):
    pieces = word_expr(words)
    source = HEADER + declaration
    for i, (value, part_proof) in enumerate(pieces):
        source += f"\ndef {name}p{i} : List Nat := {value}\n"
        source += f"theorem {name}p{i}bound : {name}p{i}.all wordBound = true := {part_proof}\n"
    source += f"\ndef {name}words : List Nat := " + (" ++ ".join(f"{name}p{i}" for i in range(len(pieces))) or "[]") + "\n\n"
    if proof is None:
        if name.startswith("M"):
            proof = "rw [module_fast]\n  rfl"
        elif name.startswith("R"):
            proof = "rw [natList_fast_fun]\n  rfl"
        else:
            proof = "rw [entry_fast_fun]\n  rfl"
    if range_table:
        proof = "rw [module_fast]\n  " + f"simp only [{name}, {name}words," + ",".join(f"{name}p{i}" for i in range(len(pieces))) + ",moduleWords,columnWords,natListWords,boolWords,optionNatWords,List.length_cons,List.length_nil,List.length_map,List.length_range,List.length_range',List.flatMap_cons,List.flatMap_nil,List.flatMap_map,List.nil_append,List.cons_append,List.append_assoc,List.range_eq_range']\n  norm_num1\n  try rfl"
    source += f"theorem {name}wire : {encoded} = {name}words := by\n  {proof}\n\n"
    source += f"theorem {name}wordBound : {name}words.all wordBound = true := by\n"
    source += f"  simp only [{name}words,List.all_append," + ",".join(f"{name}p{i}bound" for i in range(len(pieces))) + "]\n  try rfl\n\n"
    source += f"theorem {name}bounded : ∀ n ∈ {name}words, n < 2^64 := by\n"
    source += f"  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using {name}wordBound\n\n"
    source += extra
    if name.startswith("R"):
        source += f"theorem {name}fast : {name}.flatMap natListWords = {name}words := by\n  simpa only [natList_fast_fun] using {name}wire\n\n"
    source += "end DivRemFV.Replay\n"
    body = source[len(HEADER):source.rindex("end DivRemFV.Replay")]
    if write:
        (DEST / f"{name}.lean").write_text(source, encoding="utf-8")
        GENERATED[name] = body
    return body


def save_body(name, body):
    (DEST / f"{name}.lean").write_text(HEADER+body+"end DivRemFV.Replay\n",encoding="utf-8")
    GENERATED[name] = body


def assembled_bound(name, parts):
    body = f"theorem {name}wordBound : {name}words.all wordBound = true := by\n"
    body += f"  simp only [{name}words,List.all_append,"+",".join(p+"wordBound" for p in parts)+"]\n  decide\n\n"
    body += f"theorem {name}bounded : ∀ n ∈ {name}words, n < 2^64 := by\n"
    body += f"  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using {name}wordBound\n\n"
    return body


def emit_column_module(m, words):
    # Split at real column boundaries. Each small equality is kernel checked;
    # the parent uses only flatMap/length laws and those checked equalities.
    name = f"M{m[0]}"
    r = Reader(b"".join(struct.pack("<Q",n) for n in words))
    r.word(); r.seq(r.word); r.boolean(); r.boolean()
    count = r.word()
    prefix = words[:r.pos]
    chunks, body = [], ""
    for start in range(0,count,8):
        begin = r.pos
        cols = [r.column() for _ in range(min(8,count-start))]
        cname = f"C{m[0]}_{start//8}"
        body += emit(cname,f"def {cname} : List Column := {ls(map(column,cols))}\n",
                     words[begin:r.pos],f"{cname}.flatMap columnWords",
                     f"theorem {cname}length : {cname}.length = {len(cols)} := by rfl\n\n",
                     proof="rfl",write=False)
        chunks.append(cname)
    if words[r.pos:] != [0] or m[5]:
        raise ValueError("column module must be dynamic")
    body += f"def {name} : Module := {module(m,columns=' ++ '.join(chunks))}\n\n"
    body += f"def {name}prefix : List Nat := {ls(prefix)}\n"
    body += f"theorem {name}prefixwordBound : {name}prefix.all wordBound = true := by decide\n\n"
    body += f"def {name}words : List Nat := {name}prefix ++ "+" ++ ".join(c+"words" for c in chunks)+" ++ [0]\n\n"
    body += f"theorem {name}wire : module.encode {name} = {name}words := by\n"
    body += f"  rw [module_fast]\n  simp only [{name},moduleWords,List.length_append,List.flatMap_append,"
    body += ",".join(c+"length" for c in chunks)+","+",".join(c+"wire" for c in chunks)+"]\n  rfl\n\n"
    body += assembled_bound(name,[name+"prefix"]+chunks)
    save_body(name,body)


def emit_entry_group(name, entries, words, extra):
    r = Reader(b"".join(struct.pack("<Q",n) for n in words))
    names, body = [], ""
    for i,e in enumerate(entries):
        start = r.pos
        if r.entry() != e:
            raise ValueError("entry boundary differs")
        cname = f"{name}c{i}"
        body += emit(cname,f"def {cname} : Entry := {entry(e)}\n",words[start:r.pos],
                     f"entryWords {cname}",proof="rfl",write=False)
        names.append(cname)
    body += f"def {name} : List Entry := {ls(names)}\n\n"
    body += f"def {name}words : List Nat := "+" ++ ".join(c+"words" for c in names)+"\n\n"
    body += f"theorem {name}wire : {name}.flatMap entry.encode = {name}words := by\n"
    body += "  rw [entry_fast_fun]\n  simp only ["+name+",List.flatMap_cons,List.flatMap_nil,List.append_nil,"
    body += ",".join(c+"wire" for c in names)+"]\n  rfl\n\n"
    body += assembled_bound(name,names)+extra
    save_body(name,body)


def emit_large_module(m, words):
    name = f"M{m[0]}"
    cells = m[5]
    row_words = sum(1+len(row) for row in cells)
    prefix = words[:-row_words]
    names = []
    offset = len(prefix)
    for start in range(0,len(cells),256):
        chunk = cells[start:start+256]
        size = sum(1+len(row) for row in chunk)
        rowname = f"R{m[0]}_{start//256}"
        emit(rowname, f"def {rowname} : List (List Nat) := {ls(map(ls,chunk))}\n",
             words[offset:offset+size], f"{rowname}.flatMap (WireCodec.list WireCodec.nat).encode",
             f"theorem {rowname}length : {rowname}.length = {len(chunk)} := by rfl\n\n")
        names.append(rowname)
        offset += size
    if offset != len(words):
        raise AssertionError("row segmentation differs")
    source = HEADER + f"def {name} : Module := {module(m,' ++ '.join(names))}\n\n"
    source += f"def {name}prefix : List Nat := {ls(prefix)}\n"
    source += f"theorem {name}prefixBound : {name}prefix.all wordBound = true := by decide\n\n"
    source += f"def {name}words : List Nat := {name}prefix ++ " + " ++ ".join(n+"words" for n in names) + "\n\n"
    source += f"theorem {name}wire : module.encode {name} = {name}words := by\n"
    source += f"  rw [module_fast]\n  simp only [{name},moduleWords,List.length_append,List.flatMap_append,"
    source += ",".join(n+"length" for n in names) + "," + ",".join(n+"fast" for n in names) + "]\n"
    source += f"  rfl\n\n"
    source += f"theorem {name}wordBound : {name}words.all wordBound = true := by\n"
    source += f"  simp only [{name}words,List.all_append,{name}prefixBound," + ",".join(n+"wordBound" for n in names) + "]\n  try rfl\n\n"
    source += f"theorem {name}bounded : ∀ n ∈ {name}words, n < 2^64 := by\n"
    source += f"  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using {name}wordBound\n\n"
    source += "end DivRemFV.Replay\n"
    (DEST / f"{name}.lean").write_text(source,encoding="utf-8")
    GENERATED[name] = source[len(HEADER):source.rindex("end DivRemFV.Replay")]


def byte_table_matches(m):
    if len(m[5]) != 65536 or len(m[4]) != 5:
        return False
    for n,row in enumerate(m[5]):
        a,b = divmod(n,256)
        if row != [a,b,a&b,a|b,a^b]:
            return False
    return True


def emit_byte_table(m,words):
    name = f"M{m[0]}"
    # Check every row before using this lossless representation. A changed
    # table takes the general row-certificate path instead.
    if not byte_table_matches(m):
        raise ValueError("not a byte operation table")
    prefix = words[:-6*65536]
    body = f"def {name} : Module := {module(m,rows='(List.range 65536).map byteTableRow')}\n\n"
    body += f"def {name}prefix : List Nat := {ls(prefix)}\n"
    body += f"theorem {name}prefixwordBound : {name}prefix.all wordBound = true := by decide\n\n"
    body += f"def {name}words : List Nat := {name}prefix ++ (List.range 65536).flatMap (fun n => 5 :: byteTableRow n)\n\n"
    body += f"theorem {name}wire : module.encode {name} = {name}words := by\n"
    body += f"  rw [module_fast]\n  simp only [{name},moduleWords,List.length_map,List.length_range,List.flatMap_map,byteTableRow_fast]\n  rfl\n\n"
    body += f"theorem {name}wordBound : {name}words.all wordBound = true := by\n"
    body += f"  simp only [{name}words,List.all_append,{name}prefixwordBound,byteTable_bounded]\n  rfl\n\n"
    body += f"theorem {name}bounded : ∀ n ∈ {name}words, n < 2^64 := by\n"
    body += f"  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using {name}wordBound\n\n"
    save_body(name,body)
    path = DEST/f"{name}.lean"
    path.write_text("import DivRemFV.TableCompression\n"+path.read_text(encoding="utf-8"),encoding="utf-8")


def emit_final(modules, groups, count):
    # Independent certificates permit bounded parallel replay. Only a large
    # module record depends on its own row certificates.
    parts = list(GENERATED)
    for name in modules:
        rows = [r for r in parts if r.startswith("R"+name[1:]+"_")]
        if rows:
            path = DEST / f"{name}.lean"
            imports = "".join(f"import DivRemFV.Replay.{r}\n" for r in rows)
            path.write_text(imports + path.read_text(encoding="utf-8"), encoding="utf-8")
    imports = "".join(f"import DivRemFV.Replay.{p}\n" for p in modules+groups)
    source = imports + "import DivRemFV.CapturedData\n\n"
    source += HEADER[HEADER.index("set_option"):]
    source += f"def full : Artifact := ⟨{ls(modules)}, {' ++ '.join(groups)}⟩\n\n"
    source += f"def words : List Nat := [1146242647,1,fieldModulus,{len(modules)}] ++\n  "
    source += " ++\n  ".join(m+"words" for m in modules)
    source += f" ++\n  {count} :: (" + " ++\n  ".join(g+"words" for g in groups) + ")\n\n"
    source += "theorem full_wire : artifact.encode full = words := by\n  unfold full words\n  rw [artifact_encoding]\n"
    simp = ["List.length_cons", "List.length_nil", "List.length_append", "List.flatMap_cons",
            "List.flatMap_nil", "List.flatMap_append", "List.append_nil", "List.append_assoc"]
    simp += [g+"length" for g in groups] + [x+"wire" for x in modules+groups]
    source += "  simp only [" + ",".join(simp) + "]\n  try rfl\n\n"
    source += "theorem words_bounded : ∀ n ∈ words, n < 2^64 := by\n"
    source += "  have h : words.all wordBound = true := by\n    unfold words\n"
    source += "    simp only [List.all_append,List.all_cons,List.all_nil," + ",".join(x+"wordBound" for x in modules+groups) + "]\n    decide\n"
    source += "  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using h\n\n"
    source += "def bytes : List UInt8 := ByteWire.writeWords words\n\n"
    source += "theorem decoded : ArtifactWire.decode bytes = some full := by\n"
    source += "  apply (ArtifactWire.decode_iff bytes full).2\n  unfold ArtifactWire.Encodes bytes\n"
    source += "  rw [full_wire]\n  exact ByteWire.writeWords_encodes words words_bounded\n\n"
    source += "theorem selected_raw : ArtifactBinding.selectedRaw full = CapturedData.rawConstraints := by\n"
    source += "  unfold ArtifactBinding.selectedRaw ArtifactBinding.selectedEntries full\n"
    source += "  simp only [List.filter_append,List.map_append," + ",".join(g+"select" for g in groups) + "]\n  rfl\n\n"
    source += "theorem incoming_raw : (ArtifactBinding.incomingEntries full).map Entry.rule = "
    source += "[" + ",".join(g+"incoming" for g in groups) + "].flatten := by\n"
    source += "  unfold ArtifactBinding.incomingEntries full\n"
    source += "  simp only [List.filter_append,List.map_append," + ",".join(g+"calls" for g in groups) + "]\n  rfl\n\n"
    source += "theorem closure_checked : ArtifactBinding.closureCheck full = true := by\n"
    source += "  unfold ArtifactBinding.closureCheck ArtifactBinding.selectedEntries full\n"
    source += "  simp only [List.filter_append,List.all_append," + ",".join(g+"closure" for g in groups) + "]\n  decide\n\n"
    for mid in sorted(SELECTED):
        source += f"theorem findM{mid} : full.modules.find? (fun m => decide (m.id = {mid})) = some M{mid} := by rfl\n"
    source += "\ntheorem ranges_checked : ArtifactBinding.rangeCheck full = true := by\n"
    source += "  simp only [ArtifactBinding.rangeCheck,rangeTablePairs,List.all_cons,List.all_nil,"
    source += ",".join(f"findM{m}" for m in (84,85,86,90,94,95,96,97,98))
    source += ",Bool.and_eq_true,decide_eq_true_eq]\n"
    source += "  repeat' first | apply And.intro | rfl | trivial\n\n"
    source += "theorem index_checked : ArtifactBinding.indexCheck full = true := by decide\n\n"
    source += "theorem dynamic_checked : ArtifactBinding.dynamicCheck full = true := by decide\n\n"
    source += "theorem component_checked : Binding.check (ArtifactBinding.selectedRaw full) Generated.constraints = true := by\n"
    source += "  rw [selected_raw]\n  exact CapturedData.binding_checked\n\n"
    source += "theorem interfaces_checked : Binding.check ((ArtifactBinding.incomingEntries full).map Entry.rule) Generated.incomingConstraints = true := by\n"
    source += "  rw [incoming_raw]\n  rfl\n\n"
    source += "theorem checked : ArtifactBinding.check full = true := by\n"
    source += "  simp only [ArtifactBinding.check,index_checked,dynamic_checked,ranges_checked,closure_checked,component_checked,interfaces_checked]\n  rfl\n\n"
    source += "theorem component (a b : BitVec 64) (q r : Scalar × Scalar × Scalar × Scalar) :\n"
    source += "    ArtifactBinding.Accepts full (encodeFour a.toNat) (encodeFour b.toNat) q r ↔\n"
    source += "      q = encodeFour (signedQuotient a b).toNat ∧ r = encodeFour (signedRemainder a b).toNat :=\n"
    source += "  ArtifactBinding.component full checked a b q r\n\n"
    source += "end DivRemFV.Replay\n"
    # Keep encoding, selection and metadata replay independently cacheable.
    # Their propositions are unchanged; a failure does not discard other stages.
    source = source.replace("simp only [", "simp (maxSteps := 1000000) only [")
    source = source.replace("\n  rfl\n", "\n  try rfl\n")
    wire_start = source.index("theorem full_wire")
    selection_start = source.index("theorem selected_raw")
    metadata_start = source.index("theorem findM")
    final_start = source.index("theorem component_checked")
    end = "end DivRemFV.Replay\n"
    (DEST / "FullData.lean").write_text(source[:wire_start]+end, encoding="utf-8")
    stage_header = HEADER[HEADER.index("set_option"):]
    for name, start, stop in (
        ("FullEncoding", wire_start, selection_start),
        ("FullSelection", selection_start, metadata_start),
        ("FullMetadata", metadata_start, final_start),
    ):
        (DEST / (name+".lean")).write_text(
            "import DivRemFV.Replay.FullData\n\n"+stage_header+source[start:stop]+end,
            encoding="utf-8")
    final_imports = "".join("import DivRemFV.Replay."+name+"\n" for name in
                            ("FullEncoding", "FullSelection", "FullMetadata"))
    (DEST / "Full.lean").write_text(final_imports+"\n"+stage_header+source[final_start:], encoding="utf-8")
    return parts


def main():
    data = (ROOT / "artifacts/air.wire").read_bytes()
    r = Reader(data)
    r.expect(1146242647)
    r.expect(1)
    r.expect(2130706433)
    DEST.mkdir(parents=True, exist_ok=True)
    modules = []
    for _ in range(r.word()):
        start = r.pos
        m = r.module()
        name = f"M{m[0]}"
        range_table = bool(m[5]) and all(row == [i] for i,row in enumerate(m[5]))
        if byte_table_matches(m):
            emit_byte_table(m,r.words[start:r.pos])
        elif len(m[5]) > 256 and not range_table:
            emit_large_module(m,r.words[start:r.pos])
        elif not m[5] and len(m[4]) >= 16:
            emit_column_module(m,r.words[start:r.pos])
        else:
            emit(name, f"def {name} : Module := {module(m)}\n", r.words[start:r.pos], f"module.encode {name}",
                 range_table=range_table and r.pos-start>4096)
        modules.append(name)
    count = r.word()
    groups = []
    for i in range(0, count, 32):
        start = r.pos
        entries = [r.entry() for _ in range(min(32, count-i))]
        name = f"E{i//32}"
        selected = [e[3] for e in entries if e[1] in SELECTED]
        incoming = [e[3] for e in entries if e[3][0] == "lookup" and any(p[0] in (61,62,63,64) for p in e[3][2])]
        extra = f"theorem {name}length : {name}.length = {len(entries)} := by rfl\n\n"
        extra += f"def {name}selected : List RawConstraint := {ls(map(rule, selected))}\n"
        extra += f"theorem {name}select : ({name}.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).map Entry.rule = {name}selected := by rfl\n\n"
        extra += f"def {name}incoming : List RawConstraint := {ls(map(rule, incoming))}\n"
        extra += f"theorem {name}calls : (ArtifactBinding.incomingEntries ⟨[],{name}⟩).map Entry.rule = {name}incoming := by rfl\n\n"
        extra += f"theorem {name}closure : ({name}.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).all (fun e => (ArtifactBinding.referencedModules e).all (fun id => decide (id ∈ ArtifactBinding.selectedIds))) = true := by decide\n\n"
        emit_entry_group(name,entries,r.words[start:r.pos],extra)
        groups.append(name)
    if r.pos != len(r.words):
        raise ValueError("trailing words")
    # Confirms the exact delivered bytes, including byte order and word count.
    reconstructed = b"".join(struct.pack("<Q", n) for n in r.words)
    if reconstructed != data:
        raise AssertionError("input reconstruction differs")
    parts = emit_final(modules, groups, count)
    manifest = {"format": "air-kernel-replay-v1", "bytes": len(data), "words": len(r.words), "parts": parts,
                "sha256": hashlib.sha256(data).hexdigest(), "modules": modules, "entry_groups": groups,
                "constraint_count": count, "claim": "generated candidates; kernel checks still required"}
    (ROOT / "artifacts/replay-manifest.json").write_text(json.dumps(manifest, indent=2)+"\n")
    print(f"replay candidates: {len(modules)} modules, {count} constraints, {len(r.words)} words")


if __name__ == "__main__":
    main()

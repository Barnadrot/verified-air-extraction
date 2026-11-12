"""Exercise the verified wire decoder and component checker on changed inputs."""
from pathlib import Path
import json
import os
import struct
import subprocess
from replay_wire import Reader, ROOT


def main():
    data = (ROOT / "artifacts/air.wire").read_bytes()
    r = Reader(data)
    for expected in (1146242647, 1, 2130706433):
        r.expect(expected)
    modules = []
    for _ in range(r.word()):
        start = r.pos
        m = r.module()
        modules.append((start, r.pos, m))
    count_at = r.pos
    count = r.word()
    entries = []
    for _ in range(count):
        start = r.pos
        e = r.entry()
        entries.append((start, r.pos, e))
    assert r.pos == len(r.words)
    original = r.words
    fixtures = []

    def changed(name, pos, value, accepted=False):
        words = original.copy()
        words[pos] = value
        fixtures.append((name, words, accepted))

    changed("wrong_modulus", 2, 17)
    # The first nonzero constant in a selected vanishing constraint.
    for start, end, e in entries:
        if e[1] != 62 or e[3][0] != "vanishing":
            continue
        # Entry prefix: id, owner, name count, name; then vanishing tag,
        # owner, optional domain, term word count, term tokens.
        q = Reader(b"".join(struct.pack("<Q", n) for n in original[start:end]))
        q.entry()
        p = start + 3 + len(e[2]) + 2
        p += 2  # option domain occupies two words for both variants
        token_count_at = p
        p += 1
        for i in range(p, p + original[token_count_at]-1):
            if original[i] == 0 and 0 < original[i+1] < 2130706432:
                candidate = original.copy()
                candidate[i+1] += 1
                # Ensure this remains a valid encoding before using the fixture.
                try:
                    check = Reader(b"".join(struct.pack("<Q", n) for n in candidate[start:end]))
                    parsed = check.entry()
                    if check.pos != end-start or parsed[3] == e[3]:
                        continue
                except (ValueError, IndexError):
                    continue
                fixtures.append(("changed_coefficient", candidate, False))
                changed("unsupported_term", p, 255)
                break
        if any(f[0] == "changed_coefficient" for f in fixtures):
            break

    start, end, m = next(m for m in modules if m[2][0] == 98)
    changed("changed_static_value", end-1, original[end-1]+1)
    # Keep the same UTF-8 length; metadata names have no arithmetic meaning.
    changed("renamed_module", start+2, ord("R"), True)

    # Find an actual helper target port. Mutate its selector and tuple order.
    start, end, e = next(e for e in entries if e[2][3][0] == "lookup" and
                         any(p[0] == 62 for p in e[2][3][2]))
    local = Reader(b"".join(struct.pack("<Q", n) for n in original[start:end]))
    local.word(); local.word(); local.seq(local.word)
    local.expect(1); local.expect(1); local.expect(0)
    local.seq(local.port)
    for _ in range(local.word()):
        mid = local.word()
        sel_tag_at = local.pos
        selector = local.option(local.word)
        width = local.word()
        cols_at = local.pos
        cols = [local.word() for _ in range(width)]
        if mid == 62:
            assert selector == 43 and original[start+sel_tag_at] == 1
            changed("changed_selector", start+sel_tag_at+1, 42)
            words = original.copy()
            words[start+cols_at], words[start+cols_at+1] = words[start+cols_at+1], words[start+cols_at]
            fixtures.append(("swapped_columns", words, False))
            break

    # Delete a selected constraint, repair the length and all subsequent IDs.
    removed = next(i for i, (_, _, e) in enumerate(entries) if e[1] == 62)
    start, end, _ = entries[removed]
    words = original.copy()
    words[count_at] -= 1
    for s, _, _ in entries[removed+1:]:
        words[s] -= 1
    del words[start:end]
    fixtures.append(("omitted_constraint", words, False))

    required = {"wrong_modulus", "changed_coefficient", "changed_static_value", "renamed_module",
                "changed_selector", "swapped_columns", "omitted_constraint", "unsupported_term"}
    assert required == {name for name, _, _ in fixtures}
    destination = ROOT / "artifacts/wire-mutations"
    destination.mkdir(exist_ok=True)
    reader = ROOT / ".lake/build/bin" / ("artifact_reader.exe" if os.name == "nt" else "artifact_reader")
    results = []
    for name, words, expected in fixtures:
        path = destination / (name+".wire")
        path.write_bytes(b"".join(struct.pack("<Q", n) for n in words))
        run = subprocess.run([str(reader), str(path), "--wire-only"], capture_output=True, text=True)
        accepted = run.returncode == 0
        result = {"name": name, "expected_acceptance": expected, "accepted": accepted,
                  "message": (run.stdout+run.stderr).strip()}
        results.append(result)
        print(name, "PASS" if accepted == expected else "FAIL")
        if accepted != expected:
            raise RuntimeError(result)
    for name, malformed in (("truncated_byte", data[:-1]), ("trailing_word", data+struct.pack("<Q",0))):
        path = destination/(name+".wire")
        path.write_bytes(malformed)
        run = subprocess.run([str(reader), str(path), "--wire-only"], capture_output=True, text=True)
        assert run.returncode != 0, name
        results.append({"name": name, "accepted": False, "expected_acceptance": False,
                        "message": (run.stdout+run.stderr).strip()})
        print(name, "PASS")
    (ROOT / "artifacts/wire-mutations.json").write_text(json.dumps(results, indent=2)+"\n")


if __name__ == "__main__":
    main()

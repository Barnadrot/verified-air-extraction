# Signed RV64 DIV/REM and AIR extraction: component specification

Publication specification, revised 12 November 2026. The helper statement and
raw-input / call-port contracts retain their meaning. This revision adds
publication and test requirements. Instruction execution and the production
verifier remain outside scope.

## Component 1: signed division helper

Verify the generated AIR for Lineth's `divMod_64_ss`, including its unsigned
division, absolute-value, negation and fixed range-table dependencies.

For all 64-bit words `a,b` and four raw field limbs `q,r`, prove:

$$
\mathrm{Accepts}(a,b,q,r)
\iff
q=\mathrm{enc}(SQ(a,b))\ \land\ r=\mathrm{enc}(SR(a,b)).
$$

`enc` gives four canonical 16-bit limbs, most significant first. `Accepts`
requires a trace satisfying the selected constraints and fixed tables, with the
complete active helper tuple at the actual incoming lookup target. Input words
are canonically encoded. Output canonicality is a conclusion.

`SQ` and `SR` are the signed quotient and remainder words:

| Case | Quotient | Remainder |
|---|---|---|
| Zero divisor | All bits set | Dividend |
| Minimum signed word divided by `-1` | Minimum signed word | Zero |
| Otherwise | Integer quotient truncated toward zero | Corresponding integer remainder |

The forward direction must cover every accepted witness. The reverse direction
must construct a witness satisfying the complete selected slice. This is local
completeness, not existence of a whole interpreter execution.

The fixed target is [Statement.lean](../proofs/divrem/DivRemFV/Statement.lean).
Agreement with the pinned published Sail Lean DIV/REM model must also be checked.
The reference generator and original Sail source correspondence remain trusted.

### Added interface contracts

For arbitrary raw input and output limbs, derive input canonicality from the
helper constraints. Do not require the caller to supply input limb bounds.
`decodeFour` reads the weighted limbs modulo `2^64`; acceptance must also prove
that the original limbs equal the canonical encoding of that word.

Separate the trace-table requirements:

- Soundness requires `StaticRanges`: every range-table entry is in range.
  It does not require exact row order, multiplicity or table equality.
- Local completeness constructs the existing canonical tables. It does not
  promise a witness for arbitrary in-range tables, which can be empty.
- Artifact capture and its canonical table-data checks remain unchanged.
  Permitting duplicate in-range trace entries does not prove backend padding.

Prove soundness at the actual DIV and REM lookup ports, each with eight input
limbs and four result limbs. Link the results to checked incoming constraints
`9618` and `9622`, including caller selectors `131` and `133`. Prove the result
at the caller's result columns, before register writeback. No dispatch, register
or PC theorem is added.

Bind these contracts to the same captured artifact and explicit byte premises.
Audit them through `InterfaceAudit.lean`; retain the original ISA target unchanged.

## Component 2: extraction and binding

Start at the actual Go AIR object supplied by `AirConstraints()`. Verify the
custom capture library against its actual Goose-translated bodies and critical
callees. No capture-critical accessor may be replaced by an assumed correct
return value. Include field conversion from KoalaBear's stored representation.

The build embeds `.zkc` source and compiles it before obtaining the AIR object.
The capture proof starts at that object. It does not prove the ZkC compiler
correct or establish source-program semantics.

Specify a portable binary grammar. Prove writer correspondence, bounded words,
decoder soundness and supported-input completeness. Reject unsupported syntax.
Capture the full supported AIR, then select the helper inside the checked path.
Full syntax replay does not require proving every component's arithmetic.

Prove the selection/interface checks sound: include every selected owner's
constraint and its module dependencies; fix static table contents; bind input,
output and activation columns to the incoming lookup interface. Derive the
constraint gate from active target membership.

Bind the decoded artifact to the arithmetic relation. Prove semantic preservation
of the native AIR importer. Keep its defined semantics and their adequacy to the
upstream evaluator separate.

Source contracts use Lean 4.34.1; arithmetic and decoding use Lean 4.30.0.
Their shared definitions must agree. The final binding must expose the bounded
word and byte-identity premises. Check actual delivered bytes against the
kernel-replayed instance. Do not call the two builds one whole-application proof.

## Completion evidence

- Required arithmetic, source, decoder, interface and final-binding endpoints compile.
- Transitive axiom audits allow only `propext`, `Classical.choice`, `Quot.sound`.
- The final theorem covers raw limbs, activation, zero division and overflow.
- A false result is universally rejected by a theorem.
- Source and artifact mutations fail against unchanged proofs or binding checks.
- At least one supported equivalent change passes. General refactors can require
  proof repair. Exhaustive constraint deletion testing is not claimed.
- Record toolchain pins, artifact identity, exact check commands and remaining trust.

## Publication evidence

Use `Statement.lean` and `StatementAudit.lean` as the public names of the
reviewed target and its audit. Keep explicit specification definitions and
prove their equality to the reusable signed operations. A rename must not
weaken the accepted-witness relation or either proof direction.

Compare finite-trace verdicts with the pinned upstream ZkC evaluator for the
selected slice. Include accepted witnesses for ordinary signs, zero division
and overflow, one-cell mutations, canonical-field values outside limb ranges,
non-Boolean selectors and random traces. Compare each constraint verdict as
well as overall acceptance. Save deterministic seeds, counts and coverage.
Any disagreement inside the supported domain must fail the test. This is
finite differential evidence, not a proof of upstream semantic adequacy.

The executable Lean checker must have a kernel-checked agreement theorem with
`ConstraintsHold`. The test harness and its input/output delivery remain
runtime evidence. Do not put testing axioms into the arithmetic result.

Supply a digest-pinned container environment and validate bootstrap and both
proof builds without pre-existing local dependency or project caches. Record
actual resources and elapsed time. Write a separate local report for each run. Run reports remain
outside version control. Distinguish a fresh environment from `--clean` alone.

## Maintenance and later expansion

Regenerate the artifact, translations and certificates after relevant changes.
Recheck the same semantic target. Hash changes record identity; they cannot
approve a behavior change. Target, semantics, trusted tools and approval rules
need separate review. This local runner does not enforce protected branch policy.

Later contracts can add instruction dispatch, register reads/writes, `x0`, PC,
unsigned and W instructions, memory/bus consistency and interpreter composition.
Backend enforcement and deployed artifact identity are separate extensions.

The [README](../README.md) explains the current results and remaining trust.
The [audit guide](audit-guide.md) gives the review order.

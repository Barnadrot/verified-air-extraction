# DIV REM audit guide

Audit the signed RV64 helper and its extraction chain against the component specification. The guide separates a theorem's validity, its source connection and the production guarantee.

The [walkthrough](walkthrough.md) defines the notation and explains the proof.
The [self-audit](self-audit.md) records the reviewed scope and remaining limits.
The build regenerates its own reports. Bootstrap downloads mathlib's precompiled
dependency cache; it does not rebuild every third-party library from source.

## 1. Freeze the target before reviewing proof code

Start with [Statement.lean](../proofs/divrem/DivRemFV/Statement.lean). Read `quotient`, `remainder`, `enc` and `component` in full.

Confirm:

- `a,b` range over all 64-bit words, including zero and signed overflow.
- `q,r` are raw field limbs. Their canonical encoding is a conclusion.
- Acceptance requires the fixed range tables, all selected constraints and an active complete helper tuple.
- The claim has both directions. The reverse direction constructs a helper witness, rather than assuming one exists.
- No hypothesis assumes that the quotient, remainder, signs or lifted arithmetic are already correct.
- The scope is the signed helper, rather than instruction dispatch or a production verifier.

The two named equality lemmas in `Statement.lean` must compile by `rfl` and
appear in `StatementAudit.lean`. Their proofs establish agreement between the reviewed specification and
the reusable signed operations.

Then read [SignedInterface64.lean](../proofs/divrem/DivRemFV/SignedInterface64.lean).
Check `signed64_inputs_canonical`, `signed64_raw_component_iff` and the two
12-column port lemmas. Raw inputs must be proved canonical; their bounds must
not be caller premises. Read [ComponentBoundary64.lean](../proofs/divrem/DivRemFV/ComponentBoundary64.lean)
to follow the actual incoming constraints to caller result columns.

Soundness uses `StaticRanges`. Completeness constructs the existing canonical
tables. Do not infer completeness for every range-safe table: an empty table
can omit required entries. The artifact's canonical table-data check and a
trace's permitted range entries are distinct requirements.

Read the [component specification](spec.md) as requirements. Keep the mathematical target fixed during proof review.

## 2. Check the arithmetic argument

Read these files in order:

| File | Audit question |
|---|---|
| [Air.lean](../proofs/divrem/DivRemFV/Air.lean) | What do row reads, selectors, lookup membership and constraint satisfaction mean? |
| [SharedTables.lean](../proofs/divrem/DivRemFV/SharedTables.lean) | Do fixed tables actually imply the required ranges? |
| [FieldLifting.lean](../proofs/divrem/DivRemFV/FieldLifting.lean), [Intervals.lean](../proofs/divrem/DivRemFV/Intervals.lean) | Do the integer bounds exclude nonzero multiples of the field modulus? |
| [Unsigned64.lean](../proofs/divrem/DivRemFV/Unsigned64.lean), [Unsigned64Result.lean](../proofs/divrem/DivRemFV/Unsigned64Result.lean) | Are the division identity and strict remainder bound derived from the captured equations? Are zero and nonzero flags constrained? |
| [SignedRows.lean](../proofs/divrem/DivRemFV/SignedRows.lean), [SignedColumns.lean](../proofs/divrem/DivRemFV/SignedColumns.lean) | Do signs, magnitudes, dependency calls and raw output limbs follow from those constraints? |
| [SignedSpec.lean](../proofs/divrem/DivRemFV/SignedSpec.lean) | Does the algorithm match integer division toward zero, including both special cases? |
| [SignedComplete64.lean](../proofs/divrem/DivRemFV/SignedComplete64.lean) | Does the constructed witness satisfy the whole selected slice? |
| [SignedContract64.lean](../proofs/divrem/DivRemFV/SignedContract64.lean) | Does active target membership imply the same gate used by the arithmetic proof? |

Generated field bounds and equations are proof inputs that require a binding to the captured AIR. They are not independent permission to assume the desired arithmetic. Follow their uses back through [CapturedData](../proofs/divrem/DivRemFV/CapturedData.lean).

## 3. Check artifact coverage and meaning

Read [NativeImport.lean](../proofs/divrem/DivRemFV/NativeImport.lean), [ArtifactBinding.lean](../proofs/divrem/DivRemFV/ArtifactBinding.lean) and [Replay/Full.lean](../proofs/divrem/DivRemFV/Replay/Full.lean).

Check `selectedEntries`, `incomingEntries`, `check`, `owned_coverage`, `component` and `full_sound`.

The expected slice has 548 constraints, eight dynamic modules and nine static tables. The full replay has 99 modules and 12,885 constraint records. These numbers identify coverage. They do not establish semantic correctness by themselves.

Ask:

- Does selection operate on the full artifact, rather than accept a caller-supplied subset?
- Do every selected owner's constraints and its module references enter the checked slice?
- Are the actual incoming selectors and port-column orders compared with the proved interfaces?
- Does `StaticHolds` connect the actual trace's static data to the captured table contents?
- Does `full_sound` require full constraint satisfaction and active target membership explicitly?
- Do `ComponentBoundary64.div_call_sound` and `rem_call_sound` derive the actual
  lookup from the checked full artifact and use only range safety for trace tables?
- Is local completeness kept separate from the existence of a full interpreter execution?

The importer proves preservation between two defined semantics. Review their adequacy against the upstream evaluator separately. The selected fragment uses unshifted vanishing constraints and lookups. Do not infer proved upstream padding, sharding or local-domain behavior from generic constructor coverage.

### Differential evaluator evidence

Read [TraceCheck.lean](../proofs/divrem/DivRemFV/TraceCheck.lean), its
[axiom audit](../proofs/divrem/TraceAudit.lean), the
[executable](../proofs/divrem/TraceMain.lean) and the
[upstream comparison test](../proofs/divrem/internal/airdata/trace_semantics_test.go).
`constraint_iff` and `all_iff` connect finite executable decisions to the
existing Lean satisfaction relation. Target indexes carry proved membership
contracts; hashing does not introduce a new logical assumption.

Check that the Go comparison uses the pinned upstream constraint checker,
not the local exported-expression evaluator. It filters the constraint
list and assigns unique diagnostic handles to shallow copies, because upstream
lookup handles can repeat. Expressions, domains, ports and selectors retain
the upstream values. Dynamic rows are shared between both evaluators.
For canonical cases, static contents also retain the upstream values. For
synthetic range-safe variants, Lean receives table overrides and ZkC receives
the same contents through isolated schema-table copies: its checker reads
static contents from the schema, not the trace. The original schema and
captured artifact stay unchanged.
The corpus includes honest traces with all eight dynamic modules populated,
changed cells, random traces and targeted input/output/selector cases.
A per-constraint disagreement fails even when both overall verdicts reject.

Table variants have explicit expected results. Duplicate entries and removal
of an unused entry preserve acceptance. Removing a required entry or emptying
a required table rejects the witness. Wrong remainders remain rejected with
duplicated entries or a missing unused entry. Both parsers require table
overrides to stay within their declared ranges; the other tables remain
canonical. These cases exercise the range-only soundness assumption without
claiming completeness for an arbitrary range-safe table.

This evidence covers one unsharded slice, which contains unshifted vanishing
constraints and lookups. It does not validate shifts, local domains, buses,
backend padding or all possible traces. Accepted honest cases are required;
a large collection of rejected random traces alone is insufficient.

## 4. Check the actual extractor source connection

The custom source files are [export.go](../proofs/divrem/internal/airdata/export.go), [artifact_wire.go](../proofs/divrem/internal/airdata/artifact_wire.go) and [term_wire.go](../proofs/divrem/internal/airdata/term_wire.go).

The build compiles embedded `.zkc` source before calling `AirConstraints()`.
It does not consume a precompiled interpreter binary. The capture theorem starts
at the AIR object and does not prove the ZkC compiler correct.

The proof entry point is [SourceContract.lean](../proofs/capture/CaptureClosure/Proof/SourceContract.lean). Follow `InputSchema`, `capture_artifact`, `WireResult` and `serialize_checked_artifact` to their definitions.

Check that:

- Goose translates the actual current source, including capture-critical callees.
- Accessor proofs read actual fields rather than assume the desired return values.
- Constant conversion includes KoalaBear's stored Montgomery representation.
- The visitor copies all modules, constraints, selectors, domains, column order and static contents.
- Unsupported dynamic nodes fail rather than disappear.
- The precondition describes the source heap. It does not assume exporter correctness.
- The `TypeAssumptions`, `FuncUnfold`, Go semantics and global-context parameters receive their declared interpretation. A clean axiom list alone does not establish that interpretation.
- Successful-call contracts are not described as termination or whole-driver proofs.

Goose frontend correctness remains trusted. This work verifies our bounded capture library under that frontend and model. It does not verify the frontend itself or ZkC's compiler.

## 5. Check the join between proof builds

Read [CaptureSyntax.lean](../proofs/divrem/DivRemFV/CaptureSyntax.lean), [CaptureByteBridge.lean](../proofs/divrem/DivRemFV/CaptureByteBridge.lean), [ExtractorBinding.lean](../proofs/divrem/DivRemFV/ExtractorBinding.lean) and [ReplayDump.lean](../proofs/divrem/ReplayDump.lean).

`ExtractorBinding.component` has `bounded` and `same` premises. Identify exactly how each is supplied. Read `captured_model_eq` to see that artifact equality follows from decoding and byte identity.

Source proofs run under Lean 4.34.1. The arithmetic/decoder build runs under Lean 4.30.0. The portable definitions must agree. The actual delivered file must match the replayed bytes. These are explicit connections between two proof sets, rather than one kernel theorem about the application.

## 6. Rebuild and check the evidence

From the repository root:

```bash
python3 bootstrap.py
bash build.sh --clean
```

The default runner regenerates the AIR, data candidates and actual-source translations, builds both proof sets, audits exact endpoints, checks delivered byte identity, and runs source and data mutations. A staged run covers only that stage. Logs and `build-status.json` are written under `proofs/divrem/artifacts/linux/`.

`--clean` moves aside the two root proof caches. Third-party dependency caches remain. Cold full-metadata checking has caused high memory and swap use; a cached success does not resolve that resource limit.

Run reports are generated locally and excluded from version control. A reference
run is not a substitute for an independent kernel run. Check the new
`build-status.json`, every required audit endpoint and all expected mutation
outcomes. The runner snapshots its protected inputs and rejects changes during
the run; those hashes do not approve changes made before the run.

| Audit source | New report, relative to `proofs/divrem/artifacts/linux/` |
|---|---|
| [TraceAudit.lean](../proofs/divrem/TraceAudit.lean) | `trace-axioms.log` |
| [StatementAudit.lean](../proofs/divrem/StatementAudit.lean) | `statement-axioms.log` |
| [ReplayAudit.lean](../proofs/divrem/ReplayAudit.lean) | `replay-axioms.log` |
| [InterfaceAudit.lean](../proofs/divrem/InterfaceAudit.lean) | `interface-axioms.log` |
| [PartsAudit.lean](../proofs/capture/CaptureClosure/PartsAudit.lean) | `source-axioms.log`, `restored-source-axioms.log` |

Each required endpoint must have an audit report. Only `propext`, `Classical.choice` and `Quot.sound` are permitted in its transitive axiom list. Generated dependency packages can contain unused opaque declarations; a whole-directory symbol count is not an endpoint audit. Read the explicit type-layout, function-resolution and semantic premises as well.

## 7. Attack the claimed guarantee

Perform mutations in a disposable copy while keeping the reviewed ISA target and approval rules unchanged.

| Mutation | Expected consequence |
|---|---|
| Drop a captured lookup selector | The source correspondence proof must fail against the changed body |
| Change a coefficient, omit a constraint or alter a fixed table | Binding or the unchanged component theorem must fail |
| Swap quotient output columns | The checked interface or raw-column result must fail |
| Propose noncanonical output limbs with the same decoded word | The raw-output equality must exclude them |
| Propose an oversized input limb that wraps to a valid word | Input canonicality must exclude it; `signed64_noncanonical_input_rejected` proves a concrete case for all outputs |
| Disable the helper gate but try to consume its tuple | Active target membership must fail or the same gate must be forced |
| Add a constraint that excludes honest helper witnesses | Completeness must fail unless the selected semantics remain unchanged |
| Rename a column | The supported equivalent change should pass |
| Renumber modules or refactor an equivalent polynomial | Record proof/binding repair. Automatic acceptance is not currently promised |

The saved tests cover a subset of these cases. Exhaustive deletion of every constraint is not claimed. A redundant constraint need not make a proof fail when removed.

The saved false-remainder row is a module-level test after deliberate constraint deletion. It is not a production exploit. A new suspected upstream defect needs a separate trace and reachability analysis.

## 8. Audit the reference and expansion claims

[SailBridge.lean](../proofs/divrem/DivRemFV/SailBridge.lean) checks agreement with the pinned published Lean model. [source-lock.json](../proofs/divrem/source-lock.json) explicitly records that its exact original Sail source/compiler correspondence is not established. Do not silently equate the separate Sail source pin with proved provenance of the published model.

Instruction, memory, bus and whole-execution contracts are future layers. An instruction proof must also close the caller activation, operand source, output selection, `x0` and PC conditions. A backend proof must establish that a verifier accepts only traces satisfying the required relations, under its cryptographic assumptions.

## 9. Suggested standalone audit request

> Review this package and the referenced code independently. Keep the specification, ISA target and approval policy fixed. Trace each theorem premise to evidence or an explicit assumption. Check arithmetic soundness and completeness, raw-limb canonicality, activation, slice coverage, source-code correspondence, the two-version byte join and reference provenance. Distinguish a proof defect from an acknowledged boundary or a documentation error. Report a concrete counterexample or missing implication for each material finding. Do not count saved logs as a fresh kernel run. Do not change code before recording findings.

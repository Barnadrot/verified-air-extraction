# Self-audit

Review date: 12 November 2026. Scope: the signed RV64 helper, source capture,
artifact binding and finite trace checker. The review separates kernel-checked
claims, executable checks and trusted premises.

## Results and limits

| Area | Finding |
|---|---|
| Mathematical target | Original ISA theorem retained. The added raw-input contract derives input and output canonicality from the constraints. |
| Tables | Soundness uses range-safe entries. Completeness constructs canonical tables; it does not require or promise an honest witness for arbitrary range-safe tables. |
| Activation | Added contracts follow the actual separate DIV and REM lookups to caller result columns. Dispatch, register state and PC remain outside scope. |
| Artifact | Complete binary replay and a checked 548-constraint helper slice; full syntax replay is not a full-interpreter proof. |
| Extractor | Contracts refer to translated actual Go bodies and critical callees. Goose, modeled operations and context interpretation remain trusted. |
| Final join | Two Lean versions, shared portable definitions and explicit byte-identity premises. The runtime comparison is an executable check. |
| Semantics | The importer preserves the defined native semantics. Adequacy to the upstream evaluator remains a reviewed assumption for the selected fragment. |
| Reference | Sail Lean bridges are checked; exact original source/compiler provenance remains open. |
| Maintenance | IDs, column layout and polynomial structure still require proof repair after some equivalent refactors. Automatic refactor tolerance is not claimed. |
| Approval | This runner does not protect its own target or policy against an actor who can also edit them. |
| Production | Backend enforcement, verifier generation and deployment identity are later work. |

## Verification

From the repository root:

```bash
python3 bootstrap.py
bash build.sh --clean
```

The runner regenerates the AIR and proof candidates, builds both Lean projects,
checks all required axiom endpoints, compares delivered bytes with the replay,
and runs data and source mutations. Source mutation changes are restored before
the final audit. Only `propext`, `Classical.choice` and `Quot.sound` are permitted
in required theorem dependencies. Explicit theorem premises still need review.

A reference full run passed all 123 steps. The extended differential corpus
passed 3,341 traces and 1,830,868 individual constraint verdicts, with no
disagreements. Run reports are generated locally under
`proofs/divrem/artifacts/`; they are not checked into this release. The
[audit guide](audit-guide.md) lists the commands, endpoints and review questions.

## Range-safe table cases

The cross-check includes accepted honest witnesses, changed cells, random
traces and eight synthetic table variants. Duplicated entries and removal of an
unused entry preserve the chosen honest witness. Removing a required entry or
emptying a required table rejects it. Wrong remainders remain rejected with
duplicates or a missing unused entry. Every table override is range-safe.

ZkC reads static contents from the schema. The harness changes isolated schema
table copies and supplies the same contents to Lean. Constraint expressions,
selectors, ports, the original schema and the captured artifact stay unchanged.
This exercises range-only soundness. Completeness still constructs canonical
tables; an arbitrary range-safe table can omit required values.

The finite checker has a kernel-checked equivalence to `ConstraintsHold`.
Differential testing supplies finite evidence against the upstream evaluator,
not a proof of general semantic adequacy or backend enforcement.

## Source and artifact boundaries

Lineth embeds `.zkc` source and compiles it before obtaining the AIR object.
The capture proof starts at that object. It does not prove the ZkC compiler's
source-to-AIR transformation. Internal representation import preserves the
defined Lean semantics; it does not establish upstream evaluator equivalence.

Outside lookups into the selected modules still impose message-matching
obligations. Local helper completeness does not construct a globally consistent
interpreter execution. Instruction state, memory/bus consistency, backend
arguments and deployed verifier identity require later contracts.

## Adversarial checks

The intact signed relation universally excludes the false remainder used by
the executable example. The separate unsigned example accepts a false row only
after deliberate deletion of constraint `11783`; its remaining 192 module
constraints hold. This is a constraint-necessity example, not an upstream
vulnerability report or an accepted production proof.

Data mutations cover changed coefficients, omitted constraints, fixed data,
selectors, output order and unsupported syntax. A supported column rename
passes. Removing a selector in the actual capture source breaks the unchanged
source proof; the runner restores and rechecks the source. Exhaustive mutation
coverage and automatic tolerance of arbitrary refactors are not claimed.

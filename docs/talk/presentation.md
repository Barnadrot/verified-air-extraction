# DIV REM presentation and speaker notes

20 slides. Slides 19–20 are technical appendices. The slides below describe the same chain as the root README and proof walkthrough.

Source paths below are relative to `proofs/divrem`, unless shown otherwise.

## 1. DIV/REM component verification

A signed RV64 helper and a source-linked AIR extractor

Architecture, proof boundaries and expansion for Lineth

**Speaker notes**

The scope is divMod_64_ss, the signed 64-bit arithmetic helper used by DIV and REM. There are two results: the constraint theorem and the actual-source capture contracts. They connect through an explicit byte contract. A fresh Linux container passed all 123 validation steps on 12 November 2026, including both proof builds, the differential evaluator corpus and source-selector mutation. Bootstrap and the full build took 41 minutes 11 seconds under a four-CPU quota. Aggregate container memory peaked at 21.1 GiB; the evidence records the remaining trust boundaries.

**Source files**

- `DivRemFV/Statement.lean`
- `DivRemFV/ExtractorBinding.lean`
- `artifacts/linux/build-status.json`

## 2. Completed scope

**Signed RV64 helper**

Every input pair and every accepted witness.
Canonical input, quotient and remainder limbs, derived from the constraints.
A valid helper witness for every input pair.

**AIR extraction path**

Actual Go capture and binary writer contracts.
Kernel-checked decoding and component binding.
Explicit toolchain and byte-delivery assumptions.

Instruction state, W variants and production backend enforcement remain later layers.

**Speaker notes**

The original helper theorem includes zero division and signed overflow. The added raw-input contract derives canonical inputs as well as outputs. Soundness needs range-safe table entries; completeness constructs canonical tables. This does not promise completeness for arbitrary range-safe tables. The extraction result applies to supported finite AIR graphs. Neither result claims a proved complete interpreter. Source contracts use Lean 4.34.1 and the arithmetic build uses Lean 4.30.0.

**Source files**

- `DivRemFV/Statement.lean`
- `../../README.md`
- `../capture/CaptureClosure/Proof/SourceContract.lean`

## 3. Signed division rules

| Case | Quotient | Remainder |
| --- | --- | --- |
| Divisor is zero | All bits set | Dividend |
| −2^63 divided by −1 | Minimum signed word | Zero |
| Ordinary division | Truncate toward zero | Zero or dividend sign |

Signed operands x,y and integer results Q,R:  x = yQ + R,   |R| < |y|

**Speaker notes**

The input words a and b have signed integer values x and y. Q and R in the ordinary-case equation are signed integers, not field elements or raw limbs. For example, -7 divided by 3 gives -2 and -1. Overflow is an architectural exception to the ordinary signed-integer equation with the returned quotient. It must be specified separately.

**Source files**

- `DivRemFV/Statement.lean`
- `DivRemFV/SignedSpec.lean`

## 4. Canonical 16-bit limbs

KoalaBear modulus p = 2^31 − 2^24 + 1 = 2130706433

n = B³l₀ + B²l₁ + Bl₂ + l₃,    B = 65536

enc(n) is the unique four-limb encoding with 0 ≤ lᵢ < B.

The theorem starts with raw output field limbs and proves equality to enc.

**Speaker notes**

A field element cannot hold every 64-bit word. The helper stores each word as four 16-bit limbs in most-significant-first order. Correct decoded values alone would be weaker than correct raw columns. The final theorem compares each output column to the canonical encoding. Input canonicality is part of the helper interface; a future register-memory contract must supply it.

**Source files**

- `DivRemFV/Statement.lean`
- `DivRemFV/Unsigned64Result.lean`

## 5. The component theorem

a,b: 64-bit input words.  q,r: four raw field limbs each.

SQ and SR: signed ISA results, including both special cases.

Accepts: some helper trace satisfies the constraints, fixed tables and active tuple.

```text
Accepts(a,b,q,r) ⇔
q = enc(SQ(a,b)) ∧ r = enc(SR(a,b))
```

Soundness excludes other accepted outputs. Completeness constructs a helper witness.

**Speaker notes**

Read the equivalence in both directions. The forward direction quantifies over every accepted witness, including malicious intermediate choices. The reverse direction excludes an empty or over-constrained helper relation. Completeness belongs to this selected slice. It does not promise an entire surrounding program execution. The exact existing Lean declaration is shown in the appendix.

**Source files**

- `DivRemFV/Statement.lean`
- `DivRemFV/BoundSigned64.lean`

## 6. Active helper interface

Module 62, selector column 43

Inputs: columns 0–7

Quotient: columns 8–11

Remainder: columns 12–15

Target membership supplies the same active gate used by the arithmetic proof.

**Speaker notes**

The proof does not choose a convenient inactive row. signed64Target is derived from the incoming helper call targets. Its checked shape gives selector 43 and the complete ordered tuple. signed64_component_iff turns membership into a row, a nonzero gate and column equalities. The arithmetic proof uses that same gate. The added call-site lemmas prove results through the separate actual 12-column DIV and REM ports. Dispatch and register writeback remain later work. This slice covers 548 constraints, eight dynamic modules and nine range tables. Ten incoming interfaces are checked across the four division helpers.

**Source files**

- `DivRemFV/SignedContract64.lean`
- `DivRemFV/ArtifactBinding.lean`

## 7. Field equations and integer meaning

e is an integer expression. Range-table lookups bound its column values.

Proved interval rules bound each integer expression.

Limb and carry equations reconstruct the 64-bit arithmetic.

```text
e ≡ 0 (mod p)  and  −p < e < p
imply  e = 0
```

Storage limbs are 16 bits. The multiplication expansion also uses 15-bit digits.

**Speaker notes**

The central risk is modular aliasing. A field equality alone allows a nonzero integer multiple of p. lift_integer_zero excludes that with strict integer bounds. Expr.interval_correct proves the expression bounds, and the generated lifting lemmas apply them to the captured equations. A representative step lifts low + 32768*high = u*v from the field when all four digits are below 32768. One cannot simply regard the 64-bit product as a single field element.

**Source files**

- `DivRemFV/FieldLifting.lean`
- `DivRemFV/Intervals.lean`
- `DivRemFV/Unsigned64.lean`

## 8. Unsigned witness uniqueness

Natural numbers A,D,U,V: dividend, divisor, quotient and remainder. D > 0.

W is a nonnegative auxiliary witness, so V < D.

Therefore U = A / D and V = A mod D.

```text
A = DU + V
D = V + W + 1
```

The zero-divisor branch has its own constrained flags and outputs.

**Speaker notes**

The hint can propose U,V,W, but the lifted integer equations pin the quotient and remainder down. unsigned_hint_iff uses natural-number division uniqueness. The constraint proof must first derive both equations and the nonzero divisor branch. For a zero divisor, the proof derives all-ones quotient limbs and the original dividend as remainder. It does not apply the positive-divisor lemma to zero.

**Source files**

- `DivRemFV/Arithmetic.lean`
- `DivRemFV/Unsigned64Result.lean`

## 9. Signed result and witness construction

**Soundness**

Derive magnitudes and sign bits.
Apply the unsigned helper contract.
Check sign correction and canonical output limbs.

**Completeness**

Construct division and dependency rows.
Supply the canonical fixed tables.
Prove the full selected slice accepts the specified tuple.

Magnitude division also gives the specified −2^63 / −1 result.

**Speaker notes**

For nonzero b, signedNatResult divides the magnitudes and restores the quotient and remainder signs. SignedSpec proves that algorithm agrees with signed bit-vector division and integer truncation. For overflow, magnitude division gives 2^63, whose 64-bit word is the minimum signed word, and remainder zero. SignedColumns uses limb bounds to turn correct reconstructed values into exact column equalities. SignedComplete64 constructs the whole local witness before SignedContract64 combines both directions.

**Source files**

- `DivRemFV/SignedRows.lean`
- `DivRemFV/SignedSpec.lean`
- `DivRemFV/SignedColumns.lean`
- `DivRemFV/SignedComplete64.lean`

## 10. Actual AIR to the helper theorem

A: actual AIR object → E: Go capture and writer → J: shared bytes and input delivery → D: decoder, representation import and binding → H: signed helper theorem.

E,D,H: kernel-checked claims under premises. J: explicit contract plus executable checks. Goose/Go model and reference provenance remain trusted. Instruction composition is future work.

**Speaker notes**

Use the same A,E,J,D,H node names as the README. A is the actual AIR object supplied at AirConstraints(). E is our actual-source capture and binary writer contract. J is the explicit byte and cross-build connection. D decodes the full input, proves translation between the defined Lean representations and checks component binding. It is not an upstream evaluator proof. H proves signed helper soundness and completeness. Green means the stated theorem under its premises, not assumption-free application verification. Amber marks trusted or executable joins. Grey marks the input or later work. ZkC source-to-AIR correctness and production backend enforcement lie outside this chain.

**Source files**

- `../../README.md`
- `DivRemFV/ExtractorBinding.lean`
- `DivRemFV/Replay/Full.lean`
- `../capture/CaptureClosure/Proof/SourceContract.lean`

## 11. Actual-source capture contracts

Goose translates the real Go capture code and its critical callees.

Perennial proofs check modules, expressions, ports, selectors and static data.

Field conversion includes KoalaBear's Montgomery representation.

The final writer derives bounded words and the shared byte representation.

Supported finite read-only input graphs. Successful library calls. Trusted Goose and Go model.

**Speaker notes**

The exporter is custom code. Goose/Perennial supplies the source-verification framework. InputSchema describes the actual heap fields; it does not grant that extraction is correct. Accessor bodies and field conversion have source proofs. capture_to_checked_wire composes Export with EncodeArtifactWire. Its context includes Go semantics, type assumptions and function-body resolution. Those parameters matter even when the axiom report is clean. The theorem does not cover arbitrary malformed heaps, termination, resource availability or the host IO driver.

**Source files**

- `../capture/CaptureClosure/Proof/SourceContract.lean`
- `../capture/CaptureClosure/Proof/ArtifactCapture.lean`
- `../capture/CaptureClosure/Proof/CheckedWire.lean`

## 12. The explicit byte join

bounded: every encoded word fits in 64 bits

same: the source bytes equal the replayed bytes

Decoding proves captured artifact = checked artifact.

Two kernel-checked proof sets. Host IO and the cross-build checks remain explicit assumptions.

**Speaker notes**

The source build uses Lean 4.34.1 and the arithmetic build uses Lean 4.30.0. Both prove correspondence to portable CaptureSyntax definitions. The build compares those definitions. ReplayDump checks every actual input byte using the same encoding definition. ExtractorBinding.captured_model_eq uses bounded and same to prove artifact equality, then transfers the helper theorem. We do not claim one theorem in one environment about the running application.

**Source files**

- `DivRemFV/CaptureByteBridge.lean`
- `DivRemFV/ExtractorBinding.lean`
- `ReplayDump.lean`
- `LinuxBuild.py`

## 13. Full replay and selected proof

**Full input replay**

99 modules
12,885 constraint records
10,176,360 input bytes

**Helper arithmetic**

548 constraints
8 dynamic modules and 9 range tables
10 incoming helper interfaces

Replaying all AIR data does not prove all interpreter arithmetic.

**Speaker notes**

The replay checks syntax, encoding and selection across the complete captured artifact. The helper arithmetic proof covers the selected slice. ArtifactBinding.full_sound states the trace implication: checked binding plus full constraint satisfaction plus matching static contents plus an active helper tuple give the correct result. Backend enforcement of those premises is outside the component theorem. The selected fragment uses unshifted vanishing constraints and lookups; generic importer coverage does not prove the upstream evaluator for all fragments.

**Source files**

- `DivRemFV/ArtifactBinding.lean`
- `DivRemFV/Replay/Full.lean`
- `artifacts/kernel-replay-status.json`

## 14. Adversarial checks

The intact signed theorem rejects this output for every helper witness.

Deleting constraint 11783 admits the saved false row in the unsigned dependency.

That row satisfies the other 192 module constraints.

```text
Inputs 0, 2
Proposed quotient 0, remainder 1
```

Deliberate module-level mutation. No defect in the intact upstream component was established.

**Speaker notes**

The universal rejection theorem is Statement.false_remainder_rejected. The deletion counterexample is executable evidence about an altered module. It is not a production proof accepted by the verifier. The 26 October review executed the saved row again against the decoded AIR. Other saved tests reject changed coefficients, omitted constraints, static values, selectors and output-column order. A source mutation that drops a selector breaks the unchanged capture proof. This is finite adversarial evidence, not exhaustive mutation testing.

**Source files**

- `DivRemFV/Statement.lean`
- `artifacts/checked-mutation64.json`
- `artifacts/wire-binding-tests.json`
- `LinuxBuild.py`

## 15. Maintenance after a code change

| Change | Recheck or repair |
| --- | --- |
| Supported AIR data | Regenerate input and replay. Recheck the same target. |
| Capture implementation | Translate the changed source. Recheck its contracts. |
| IDs, columns or polynomial refactor | Repair the checked mapping or proof where needed. |
| Spec, toolchain or approval rules | Require separate review of the changed trust boundary. |

A rename passes today. Arbitrary equivalent refactors can require proof repair.

**Speaker notes**

The specification should remain stable while proofs and generated data follow implementation changes. A green run matters only against the reviewed target and checker policy. Module IDs and widths are currently explicit in ArtifactBinding. Generated arithmetic proofs also depend on polynomial structure. More durable interface resolution and gadget-level contracts are future engineering work. Hashes provide provenance; changing a hash does not approve behavior. Proof search or repair can use agents after repeated failure, without allowing them to redefine success.

**Source files**

- `DivRemFV/ArtifactBinding.lean`
- `LinuxBuild.py`
- `artifacts/wire-binding-tests.json`

## 16. Remaining trust boundaries

| Boundary | Current limit |
| --- | --- |
| Go source connection | Trusted Goose frontend and Go model |
| Proof-build join | Runtime byte delivery and matching portable definitions |
| AIR and ISA meaning | Reviewed semantics and reference provenance |
| Production guarantee | Backend enforcement and deployed artifact identity |

Axiom audits permit propext, Classical.choice and Quot.sound. Premises still require evidence.

**Speaker notes**

Add the Go compiler/platform, runtime and host driver to the execution boundary. The source contract is a library theorem. NativeImport proves its own semantic-preservation statement, not the upstream Go evaluator. SailBridge connects to a pinned published Lean model, whose exact original Sail/compiler provenance remains open. The local pipeline does not protect approval policy against an attacker who can edit that policy. Independent target and policy review is required. These limits should be stated directly, without describing the completed library proofs as an end-to-end production guarantee.

**Source files**

- `../../README.md`
- `source-lock.json`
- `DivRemFV/ExtractorBinding.lean`

## 17. Expansion for Lineth

Current: signed helper contract. Proposed: instruction-state contract, register/memory and bus consistency, whole-interpreter composition, then backend enforcement.

Reuse extraction and binding. Add a semantic contract and proof for each component.

**Speaker notes**

The current helper contract is the first proved layer. The next bounded target is a signed DIV/REM instruction-state theorem: decoding, operand provenance, dispatch, register writes, x0 behavior and PC update. The added call-site contracts already connect active DIV and REM lookups to their result columns. Unsigned and W variants need their own final contracts, including sign extension of unsigned W results. Later composition needs register-memory and bus consistency and whole-execution reasoning. Local helper completeness alone does not construct a consistent program trace. A separate backend connection turns AIR satisfaction into a production-verifier guarantee under cryptographic assumptions. These are proposed extensions, not completed claims.

**Source files**

- `../../docs/spec.md`
- `DivRemFV/ArtifactBinding.lean`
- `../../README.md`

## 18. The next component

Reuse the capture, wire decoder and checked selection framework.

Choose a bounded slice and fix its input/output contract first.

Prove its ranges, activation and arithmetic from the actual constraints.

Compose with the helper and state contracts only after their boundaries match.

New AIR behavior can require a new semantic review, even when the extractor supports its syntax.

**Speaker notes**

A useful next engineering improvement is checked interface resolution that tolerates renumbering. A useful next proof target is the signed DIV/REM instruction boundary. These are distinct tasks. For each new slice, derive coverage and dependencies from the full artifact, define local soundness and completeness, then verify its connection to the unchanged reference. Reuse established low-level gadgets rather than prove the whole AIR in one theorem. The approach can extend to many arithmetic components, but memory, buses and state composition bring new obligations.

**Source files**

- `DivRemFV/ArtifactBinding.lean`
- `DivRemFV/NativeImport.lean`
- `../../docs/spec.md`

## 19. Appendix: exact Lean target

```lean
theorem component (a b : BitVec 64) (q r : Limbs) :
    (∃ tables : Tables, StaticTablesFixed tables ∧
      NativeImport.RawConstraintsHold tables
        CapturedData.rawConstraints ∧
      fourList (enc a) ++ fourList (enc b) ++
        fourList q ++ fourList r ∈
          signed64Target.messages tables) ↔
      q = enc (quotient a b) ∧ r = enc (remainder a b) :=
  CapturedData.component_iff a b q r
```

Existing declaration in DivRemFV.Statement. Definitions and proof steps appear in the walkthrough.

**Speaker notes**

This is the actual target, with only a line wrap changed. Tables is the modeled trace collection. StaticTablesFixed fixes canonical range contents. RawConstraintsHold requires the captured selected constraints. The message-membership clause fixes activation and all ordered input/output columns. Limbs is a four-tuple of field values. enc is canonical. quotient and remainder state zero, overflow and ordinary rules explicitly. CapturedData connects the native captured snapshot to the arithmetic component proof.

**Source files**

- `DivRemFV/Statement.lean`
- `DivRemFV/CapturedData.lean`
- `DivRemFV/SignedContract64.lean`

## 20. Appendix: audit entry points

| Claim | Entry point |
| --- | --- |
| Reviewed helper target | Statement.component |
| Raw inputs and range-only soundness | signed64_raw_component_iff |
| Actual DIV and REM call ports | ComponentBoundary64.div_call_sound / rem_call_sound |
| Actual capture and writer | SourceCapture.capture_to_checked_wire |
| Binary input and selection | Replay.decoded and Replay.checked |
| Capture-to-helper binding | ExtractorBinding.component |
| Added interface audit | InterfaceAudit.lean |

Fresh-container validation: 12 November 2026. All 123 steps passed, including both proof builds and the differential corpus. Reviewed ISA statement preserved across the rename.

**Speaker notes**

The separate audit should trace every premise to a proof, executable check or declared assumption. The repository has an audit guide and the 12 November fresh-container report. Both proof builds passed, including 17 statement endpoints, 16 interface endpoints, two checker-equivalence endpoints, full replay, the Sail bridge and source-selector mutation. Bootstrap downloaded mathlib’s pinned cache. The Linux entry point now selects the pinned local toolchains. Cold replay metadata checking still needs substantial memory. The original ISA target is unchanged; the bounded interface extension adds stronger soundness contracts. The self-audit records the remaining resource and layout-specific maintenance limits.

**Source files**

- `StatementAudit.lean`
- `ReplayAudit.lean`
- `../capture/CaptureClosure/PartsAudit.lean`
- `artifacts/linux/build-status.json`

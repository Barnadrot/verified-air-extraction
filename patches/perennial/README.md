# Local Goose package-ID fix

Verdict: **OK, with a test-suite limitation below.** This is a local review. This patch has no upstream approval.

Trust delta: one translator line changes how an existing package-ID reference is printed. `ctx.pkgIdent` already comes from `LeanPkgId`, the same renderer used for its declaration. It must not pass through ordinary Go term renaming again. For a package ending in `array`, that second pass changes the reference to `array'` and makes the generated Lean module fail to compile.

The fix uses `VerbatimExpr` for this already rendered identifier. It does not add a model, axiom, semantics rule, type-dependent choice or evaluation-order rule. The Go body and the package initializer's order are unchanged. The lower alternative, editing the generated Lean, would lose reproducibility and violate R7. The change follows R1, R7, R8, R10 and R11 of Perennial's trusted-code review procedure.

Checked:

- The regression fails before the fix and passes after it.
- A complete Go `array` fixture and its regenerated Lean golden file test the initializer reference.
- The actual AIR visitor and its translated datatype dependencies compile after regeneration.
- The full Goose/glang tests were run before and after the fix. Both runs have baseline failures on this Windows setup, including CRLF golden-file comparisons, platform-specific dependencies, an import-path expectation and existing evaluation-order cases. The new `array` fixture's baseline failure is removed by the fix. The broad suite is **not reported as passing**.
- `etc/trusted-delta.py` identifies the one translator line. The added test and fixture were also read. The four exact patched files and their checksums are included here.

The translator remains trusted. This review does not prove Goose or the full AIR capture program correct. The core source proofs and their axiom audits must still be rerun with this exact patch; The Linux runner verifies its file hashes before it builds the tool.

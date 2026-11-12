# Source-linked AIR capture proofs

Start with the [root walkthrough](../../README.md) and [audit guide](../../docs/audit-guide.md).

`CaptureClosure/Proof/SourceContract.lean` composes the contracts for the actual
Go `Export` and `EncodeArtifactWire` bodies. `AirCapture` proves the index and
field-conversion dependencies. `CaptureClosure/PartsAudit.lean` lists required
source endpoints. `Config` and `ClosureConfig` select the translated source.

The build regenerates `Code` from actual Go source. Goose's frontend, Go models,
type-layout and function-resolution assumptions remain trusted. Unused opaque
symbols in generated packages do not become proved implementations. Audit the
exact required endpoint dependencies and all explicit theorem premises.

Run `bash build.sh --stage capture` from the repository root after bootstrap.

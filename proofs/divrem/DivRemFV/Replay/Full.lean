import DivRemFV.Replay.FullEncoding
import DivRemFV.Replay.FullSelection
import DivRemFV.Replay.FullMetadata

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

theorem component_checked : Binding.check (ArtifactBinding.selectedRaw full) Generated.constraints = true := by
  rw [selected_raw]
  exact CapturedData.binding_checked

theorem interfaces_checked : Binding.check ((ArtifactBinding.incomingEntries full).map Entry.rule) Generated.incomingConstraints = true := by
  rw [incoming_raw]
  try rfl

theorem checked : ArtifactBinding.check full = true := by
  simp (maxSteps := 1000000) only [ArtifactBinding.check,index_checked,dynamic_checked,ranges_checked,closure_checked,component_checked,interfaces_checked]
  try rfl

theorem component (a b : BitVec 64) (q r : Scalar × Scalar × Scalar × Scalar) :
    ArtifactBinding.Accepts full (encodeFour a.toNat) (encodeFour b.toNat) q r ↔
      q = encodeFour (signedQuotient a b).toNat ∧ r = encodeFour (signedRemainder a b).toNat :=
  ArtifactBinding.component full checked a b q r

end DivRemFV.Replay

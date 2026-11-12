import DivRemFV.Replay.Full
import DivRemFV.CaptureByteBridge
import DivRemFV.ComponentBoundary64

namespace DivRemFV.ExtractorBinding

theorem captured_model_eq (source : CaptureSyntax.Artifact)
    (bounded : ∀ n ∈ source.words, n < 2^64)
    (same : CaptureSyntax.byteValues source.words = Replay.bytes.map UInt8.toNat) :
    source.toWire = Replay.full := by
  have bytes : ByteWire.writeWords source.words = Replay.bytes := by
    apply (List.map_inj_right (f := UInt8.toNat) (fun _ _ h => UInt8.toNat_inj.mp h)).mp
    rw [CaptureSyntax.all_byte_values]
    exact same
  have decoded := CaptureSyntax.artifact_decode source bounded
  rw [bytes,Replay.decoded] at decoded
  exact (Option.some.inj decoded).symm

theorem component (source : CaptureSyntax.Artifact)
    (bounded : ∀ n ∈ source.words, n < 2^64)
    (same : CaptureSyntax.byteValues source.words = Replay.bytes.map UInt8.toNat)
    (a b : BitVec 64) (q r : Scalar × Scalar × Scalar × Scalar) :
    ArtifactBinding.Accepts source.toWire (encodeFour a.toNat) (encodeFour b.toNat) q r ↔
      q = encodeFour (signedQuotient a b).toNat ∧ r = encodeFour (signedRemainder a b).toNat := by
  rw [captured_model_eq source bounded same]
  exact Replay.component a b q r

theorem raw_component (source : CaptureSyntax.Artifact)
    (bounded : ∀ n ∈ source.words, n < 2^64)
    (same : CaptureSyntax.byteValues source.words = Replay.bytes.map UInt8.toNat)
    (a b q r : Limbs64) :
    ComponentBoundary64.Accepts source.toWire a b q r ↔ Signed64Result a b q r := by
  rw [captured_model_eq source bounded same]
  exact ComponentBoundary64.raw_component Replay.full Replay.checked a b q r

theorem div_call_sound (source : CaptureSyntax.Artifact)
    (bounded : ∀ n ∈ source.words, n < 2^64)
    (same : CaptureSyntax.byteValues source.words = Replay.bytes.map UInt8.toNat)
    (tables : Tables) (ranges : StaticRanges tables)
    (accepted : NativeImport.RawConstraintsHold tables source.toWire.rawConstraints)
    (row : Nat) (inside : row < (tables 41).size) (active : readCell tables 41 131 row ≠ 0) :
    let a := readFour tables 41 32 row
    let b := readFour tables 41 36 row
    a = encodeFour (decodeFour a).toNat ∧ b = encodeFour (decodeFour b).toNat ∧
    readFour tables 41 55 row = encodeFour (signedQuotient (decodeFour a) (decodeFour b)).toNat := by
  rw [captured_model_eq source bounded same] at accepted
  exact ComponentBoundary64.div_call_sound Replay.full Replay.checked tables ranges accepted row inside active

theorem rem_call_sound (source : CaptureSyntax.Artifact)
    (bounded : ∀ n ∈ source.words, n < 2^64)
    (same : CaptureSyntax.byteValues source.words = Replay.bytes.map UInt8.toNat)
    (tables : Tables) (ranges : StaticRanges tables)
    (accepted : NativeImport.RawConstraintsHold tables source.toWire.rawConstraints)
    (row : Nat) (inside : row < (tables 41).size) (active : readCell tables 41 133 row ≠ 0) :
    let a := readFour tables 41 32 row
    let b := readFour tables 41 36 row
    a = encodeFour (decodeFour a).toNat ∧ b = encodeFour (decodeFour b).toNat ∧
    readFour tables 41 55 row = encodeFour (signedRemainder (decodeFour a) (decodeFour b)).toNat := by
  rw [captured_model_eq source bounded same] at accepted
  exact ComponentBoundary64.rem_call_sound Replay.full Replay.checked tables ranges accepted row inside active

end DivRemFV.ExtractorBinding

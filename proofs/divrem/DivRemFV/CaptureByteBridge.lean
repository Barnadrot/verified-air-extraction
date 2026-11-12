import DivRemFV.CaptureArtifactBridge
import DivRemFV.WriteBytes

namespace DivRemFV.CaptureSyntax

theorem word_byte_values (n : Nat) :
    (ByteWire.writeWord n).map UInt8.toNat = wordBytes n := by
  simp [ByteWire.writeWord,wordBytes,UInt8.toNat_ofNat']

theorem all_byte_values (words : List Nat) :
    (ByteWire.writeWords words).map UInt8.toNat = byteValues words := by
  simp only [ByteWire.writeWords,byteValues,List.map_flatMap,word_byte_values]

theorem artifact_decode (a : Artifact) (bounded : ∀ n ∈ a.words, n < 2^64) :
    ArtifactWire.decode (ByteWire.writeWords a.words) = some a.toWire := by
  apply (ArtifactWire.decode_iff _ _).2
  unfold ArtifactWire.Encodes
  rw [Artifact.wire_correspondence]
  exact ByteWire.writeWords_encodes a.words bounded

end DivRemFV.CaptureSyntax

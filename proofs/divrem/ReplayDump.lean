import DivRemFV.Replay.Full

open DivRemFV

def main (args : List String) : IO UInt32 := do
  let path := args[0]?.getD "artifacts/air.wire"
  let delivered ← IO.FS.readBinFile path
  let mut offset := 0
  -- Compare the same writeWords definition one word at a time. This avoids
  -- allocating a second ten-megabyte file as a ten-million-element Lean list.
  for word in Replay.words do
    for byte in ByteWire.writeWord word do
      unless delivered[offset]? == some byte do
        IO.eprintln s!"Kernel replay input differs at byte {offset}"
        return 1
      offset := offset + 1
  unless offset == delivered.size do
    IO.eprintln "Kernel replay input has a different length"
    return 1
  IO.println s!"Kernel replay input matches the delivered AIR file: {offset} bytes"
  return 0

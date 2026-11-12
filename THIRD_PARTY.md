# Third-party source and tools

The bootstrap fetches upstream dependencies at the revisions recorded in
`proofs/divrem/source-lock.json`, the two Lake manifests and `bootstrap.py`.
Their licenses remain with those checkouts. Toolchain archives have fixed
checksums in `proofs/divrem/bootstrap_linux.py`.

- Lineth supplies the `.zkc` interpreter source compiled for this instance.
- ZkC supplies the compiler, AIR object types and accessors. Its translated Lean
  definitions retain their source package names. The Apache 2.0 license is in
  [LICENSES/ZkC-Apache-2.0.txt](LICENSES/ZkC-Apache-2.0.txt).
- Goose / Perennial supplies Go-to-Lean translation, modeled Go operations and
  program logic. A local one-line translator change and regression fixtures
  are in [patches/perennial](patches/perennial), with the upstream MIT license.
  Goose remains trusted; the patch is not an upstream release.
- Translated Go standard-library fragments retain their source package names.
  The Go BSD license is in [LICENSES/Go-BSD-3-Clause.txt](LICENSES/Go-BSD-3-Clause.txt).
- The published Sail RISC-V Lean model and lean-sail runtime supply the second
  arithmetic reference. Their generation provenance is a stated trust boundary.
- Lean, mathlib and Iris supply the logical and arithmetic libraries.

Some translated dependency modules also contain unused opaque declarations.
The required theorem endpoints are audited transitively; this artifact does
not claim that every declaration in each translated package is implemented.

The root MIT license covers original contributions. Third-party files and
translations retain their upstream terms and notices listed here.

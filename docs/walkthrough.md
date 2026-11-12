# DIV/REM proof walkthrough

## 1. The exact component

The source helper is `divMod_64_ss` in [multiplication.zkc](https://github.com/LFDT-Lineth/lineth-monorepo/blob/2737d8c6b0cdba2b54c195aa6c10958538c5f3e4/arithmetization/src/main/riscv/utils/multiplication.zkc). It computes both signed results. The DIV branch uses its quotient. The REM branch uses its remainder.

This is the source structure, with comments omitted:

```text
fn divMod_64_ss(a:u64, b:u64) -> (q:u64, r:u64) {
    var q_u:u64
    var r_u:u64
    q_u, r_u = divMod_64_uu(absolute_value_double_word(a), absolute_value_double_word(b))
    var a_sign:u1 = sign_bit_of_double_word(a)
    if b == 0 {
        q = NEGATIVE_ONE_AS_I64
        r = a
        return
    }
    q = a_sign == sign_bit_of_double_word(b) ? q_u:negative_of_double_word(q_u)
    r = a_sign == 0 ? r_u:negative_of_double_word(r_u)
}
```

The source helps explain the algorithm. The arithmetic proof checks the generated constraints, rather than assuming that this source compiled correctly.

The [interpreter](https://github.com/LFDT-Lineth/lineth-monorepo/blob/2737d8c6b0cdba2b54c195aa6c10958538c5f3e4/arithmetization/src/main/riscv/interpreter.zkc) also has an explicit overflow branch before its DIV helper call. The helper itself gives the required overflow result. Proving the helper does not prove that outer branch, its opcode selection or its register write.

The completed scope excludes instruction dispatch, register memory, writes to `x0`, PC updates and W instructions. Some supporting unsigned and 32-bit work exists. It does not expand the final signed-helper claim.

## 2. The statement

Let `a` and `b` be 64-bit words. Let `x` and `y` be their signed integer values. Let `SQ(a,b)` and `SR(a,b)` be the specified quotient and remainder words.

| Case | `SQ(a,b)` | `SR(a,b)` |
|---|---|---|
| `b = 0` | All bits set, which represents `-1` | `a` |
| `x = -2^63` and `y = -1` | The word that represents `-2^63` | Zero |
| Otherwise | The integer quotient truncated toward zero, encoded in 64 bits | The corresponding integer remainder, encoded in 64 bits |

For ordinary division, let `Q` and `R` be the signed integer quotient and remainder. Then:

$$
x=yQ+R,\qquad |R|<|y|,\qquad R=0\ \lor\ \mathrm{sign}(R)=\mathrm{sign}(x).
$$

For example, `-7 / 3` gives `Q = -2` and `R = -1`:

$$
-7=3(-2)+(-1).
$$

The special cases are part of the specification. The ordinary integer equation cannot describe signed overflow with the returned signed quotient.

The existing Lean definitions in [Statement.lean](../proofs/divrem/DivRemFV/Statement.lean) state these rules directly:

```lean
def quotient (a b : BitVec 64) : BitVec 64 :=
  if b = 0 then BitVec.allOnes 64
  else if a = BitVec.intMin 64 ∧ b = BitVec.allOnes 64 then BitVec.intMin 64
  else BitVec.ofInt 64 (a.toInt.tdiv b.toInt)

def remainder (a b : BitVec 64) : BitVec 64 :=
  if b = 0 then a
  else if a = BitVec.intMin 64 ∧ b = BitVec.allOnes 64 then 0
  else BitVec.ofInt 64 (a.toInt.tmod b.toInt)
```

`BitVec 64` is a 64-bit word. `toInt` reads it as a signed integer. `tdiv` truncates division toward zero. `tmod` gives its remainder. `ofInt` encodes the integer result back into 64 bits.

## 3. Why the theorem uses raw limbs

KoalaBear has modulus:

$$
p=2^{31}-2^{24}+1=2130706433.
$$

A field element cannot hold every 64-bit word. The helper carries each word as four 16-bit limbs. Let `B = 65536`. For a word with unsigned value `n`, its canonical encoding is:

$$
\mathrm{enc}(n)=\left(
\left\lfloor\frac{n}{B^3}\right\rfloor\bmod B,
\left\lfloor\frac{n}{B^2}\right\rfloor\bmod B,
\left\lfloor\frac{n}{B}\right\rfloor\bmod B,
n\bmod B\right).
$$

The order is most significant limb first. Each limb is a field element whose value is less than `B`.

Let `q` and `r` each be four **raw field limbs**. They are not assumed to be canonical. Define `Accepts(a,b,q,r)` to mean that there are trace tables which satisfy the selected constraints and fixed range tables, and contain the active helper tuple `(enc(a), enc(b), q, r)`.

The claim is:

$$
\forall a,b,q,r,\quad
\mathrm{Accepts}(a,b,q,r)
\iff
\left(q=\mathrm{enc}(SQ(a,b))\ \land\ r=\mathrm{enc}(SR(a,b))\right).
$$

The forward direction is soundness: no accepted witness gives another result. It includes malicious choices of quotient, remainder and intermediate values. Equality to `enc` also proves that the output limbs are canonical.

The reverse direction is completeness: for every input pair, the specified outputs have an accepted helper witness. This is local completeness for the selected slice. It does not assert that every surrounding program execution exists.

### Raw inputs and table requirements

The helper range-checks all eight input limbs. A caller does not need to supply those bounds. It must still connect the limbs to the intended operand values.

Let `A,B,Q,R` be arbitrary four-limb tuples. Let `d` be `decodeFour`: the weighted limb value encoded as a 64-bit word. `Accepts_range` requires an active combined tuple and all selected constraints, with every range-table entry in range. The added theorem is:

$$
\mathrm{Accepts}_{\mathrm{range}}(A,B,Q,R)\iff
\begin{aligned}
&A=\mathrm{enc}(d(A))\ \land\ B=\mathrm{enc}(d(B))\\
&\land\ Q=\mathrm{enc}(SQ(d(A),d(B)))\\
&\land\ R=\mathrm{enc}(SR(d(A),d(B))).
\end{aligned}
$$

[SignedInterface64.lean](../proofs/divrem/DivRemFV/SignedInterface64.lean) proves this contract. Noncanonical raw inputs cannot pass by decoding to a convenient word: canonicality is also a conclusion.

| Direction | Trace-table requirement |
|---|---|
| Soundness | `StaticRanges`: each entry is in range. Order, duplicates and exact table equality are not required. |
| Local completeness | Construct the existing canonical tables and helper witness. Arbitrary in-range tables need not support every input. |

For example, empty tables satisfy the range predicate but can omit values needed by an honest witness. The reverse direction proves that a suitable witness exists. It does not promise completeness for every choice of tables. The captured artifact still contains the checked canonical table data. Backend padding remains a separate obligation.

## 4. The proof starts with the constraints

The selected slice has 548 constraints, eight dynamic modules and nine fixed range tables. It retains four division helpers and their arithmetic dependencies. All ten incoming division-helper interfaces are checked. The final claim selects the signed 64-bit helper.

For that helper, the checked target is module `62`, with selector column `43`. Columns `0–7` carry `a,b`, columns `8–11` carry `q`, and columns `12–15` carry `r`.

An active tuple is a message in this lookup target. It is not an arbitrary row chosen by the proof. [SignedContract64.lean](../proofs/divrem/DivRemFV/SignedContract64.lean) derives the target from the incoming calls, checks its shape, and obtains the same nonzero gate used by the helper constraints. Range constraints then give the relevant Boolean flag bounds.

This prevents the proof from using a row whose constraint gate is off. Connecting a dispatched instruction to this active call remains a later instruction proof.

The combined target has 16 columns. The real DIV and REM calls each use 12: eight operand limbs and four result limbs. [ComponentBoundary64.lean](../proofs/divrem/DivRemFV/ComponentBoundary64.lean) now proves soundness through the actual incoming lookup constraints. DIV uses caller selector `131`; REM uses `133`. Both take operand columns `32–39` and return the selected result at columns `55–58` in caller module `41`. These are lookup result contracts, before register writeback.

## 5. Field equations must become integer equations

Equality in the field means equality modulo `p`. It does not directly establish integer equality. A false integer equation could differ by a multiple of `p`.

For an integer expression value `e`, the lifting rule is:

$$
e\equiv0\pmod p\ \land\ -p<e<p\quad\Longrightarrow\quad e=0.
$$

[FieldLifting.lean](../proofs/divrem/DivRemFV/FieldLifting.lean) proves this rule. [Intervals.lean](../proofs/divrem/DivRemFV/Intervals.lean) proves the expression interval rules. The generated lifting lemmas apply those rules to the captured polynomials.

Bounds come from the actual range-table lookups and canonical fixed tables. They are not free assumptions supplied for a quotient or remainder chosen by the prover.

The storage limbs are 16 bits, but the multiplication expansion also uses smaller digits. A useful checked step is a 15-bit partial product. Let `u,v,l,h` be natural numbers less than `2^15`. Then:

$$
l+2^{15}h\equiv uv\pmod p
\quad\Longrightarrow\quad
l+2^{15}h=uv.
$$

Both sides are below `p`. This is the `lift_partial_product` lemma. It illustrates why one cannot replace the actual limb proof with the single field equation `a = bq + r`.

## 6. The unsigned division core fixes the witness

For this section only, let `A,D,U,V,W` be nonnegative integers: dividend, nonzero divisor, quotient, remainder and the range witness.

After lifting and recombining the small equations, the proof obtains:

$$
A=DU+V,\qquad D=V+W+1.
$$

Since `W` is nonnegative, the second equation gives `V < D`. Division uniqueness then gives:

$$
U=\left\lfloor\frac{A}{D}\right\rfloor,\qquad V=A\bmod D.
$$

The key existing Lean statement is concise:

```lean
theorem unsigned_hint_iff (a b q r : Nat) (positive : 0 < b) :
    (∃ auxiliary : Nat, a = b * q + r ∧ b = r + auxiliary + 1) ↔
      (q = a / b ∧ r = a % b)
```

Its proof is in [Arithmetic.lean](../proofs/divrem/DivRemFV/Arithmetic.lean). It uses the proved uniqueness of natural-number division. The preceding constraint-to-integer argument is in [Unsigned64.lean](../proofs/divrem/DivRemFV/Unsigned64.lean) and [Unsigned64Result.lean](../proofs/divrem/DivRemFV/Unsigned64Result.lean).

The zero-divisor case is separate. The proof checks the selector and zero/nonzero flags, then derives all-ones quotient limbs and remainder limbs equal to the dividend. It does not try to apply `D = V + W + 1` with `D = 0`.

## 7. The signed layer restores the signs

For a nonzero divisor, the signed helper calls unsigned division on the magnitudes. It negates the quotient exactly when the operand signs differ. It gives a nonzero remainder the dividend's sign.

The proof establishes each magnitude, sign bit, dependency call and negation from the constraints. [SignedRows.lean](../proofs/divrem/DivRemFV/SignedRows.lean) combines them. [SignedSpec.lean](../proofs/divrem/DivRemFV/SignedSpec.lean) connects that magnitude algorithm to signed bit-vector division and then to the integer rules in section 2.

For `-2^63 / -1`, the unsigned magnitude quotient is `2^63`. Its 64-bit encoding is the minimum signed word. The remainder is zero. Thus, the helper gives the required overflow result without an explicit overflow branch inside the helper.

[SignedColumns.lean](../proofs/divrem/DivRemFV/SignedColumns.lean) finishes the raw-column equality. It uses output limb bounds plus the result's reconstructed value to identify each canonical limb.

## 8. Completeness constructs the whole helper witness

Soundness alone would also hold for a constraint system that accepts nothing. Completeness excludes that failure.

[UnsignedComplete64.lean](../proofs/divrem/DivRemFV/UnsignedComplete64.lean) and [SignedComplete64.lean](../proofs/divrem/DivRemFV/SignedComplete64.lean) construct the division rows, arithmetic dependency rows and fixed tables. They show that all constraints in the selected slice hold and the correct active tuple exists.

[SignedContract64.lean](../proofs/divrem/DivRemFV/SignedContract64.lean) combines both directions in `signed64_component_iff`. [CapturedData.lean](../proofs/divrem/DivRemFV/CapturedData.lean) binds the independently emitted native constraint data to that relation. [Statement.component](../proofs/divrem/DivRemFV/Statement.lean) states the reviewed result.

These modules build the claim in this order. The final theorem does not rely only on a manually transcribed DIV/REM algorithm.

## 9. Connect the actual AIR to the arithmetic result

The [export driver](../proofs/divrem/cmd/export-air/main.go) compiles Lineth's
embedded `.zkc` source, obtains `AirConstraints()`, calls the custom Go `Export`
function and serializes its result with `EncodeArtifactWire`. The extraction
proof starts at the AIR object. It does not assume that the ZkC compiler
correctly implements the `.zkc` program.

Goose translates the actual capture and writer bodies into Lean program terms.
The Perennial endpoint
[`capture_to_checked_wire`](../proofs/capture/CaptureClosure/Proof/SourceContract.lean)
composes their contracts. `InputSchema` describes the supported finite,
read-only source graph. `WireResult` describes the serialized representation
and derives the word bounds needed by the decoder. The contract is partial
correctness under the stated Go-model and function-resolution premises.

Field conversion is part of capture. A KoalaBear element is stored in Montgomery
form; copying its stored word would copy a representation, not its canonical
field value. The source proofs include conversion to the value used by the
portable AIR syntax.

The source proofs use Lean 4.34.1. Decoding and arithmetic use Lean 4.30.0.
Their portable definitions are compared during the build. The compiled
`replay_input_check` checks each delivered byte against the representation
replayed by Lean. This join is an executable check, not one kernel theorem
about the Go process and both proof builds.

In the arithmetic build,
[`captured_model_eq`](../proofs/divrem/DivRemFV/ExtractorBinding.lean) takes:

```lean
(bounded : ∀ n ∈ source.words, n < 2^64)
(same : CaptureSyntax.byteValues source.words = Replay.bytes.map UInt8.toNat)
```

Here `source` is the captured artifact model. These premises imply
`source.toWire = Replay.full` by writer/decoder correspondence and the checked
replay. `ExtractorBinding.component` transfers the helper theorem across this
equality. The raw-input and actual call-port contracts use the same connection.

The decoder checks the full artifact as syntax. Slice binding then checks all
selected constraints, dependencies, canonical static contents and the incoming
interfaces. Replaying the rest of the artifact does not prove its arithmetic.

[`NativeImport`](../proofs/divrem/DivRemFV/NativeImport.lean) proves that the two
defined AIR representations have the same satisfaction relation. The finite
[`TraceCheck`](../proofs/divrem/DivRemFV/TraceCheck.lean) has a kernel proof that
its Boolean verdict agrees with that relation. Comparing it with ZkC's upstream
evaluator adds differential evidence for the selected fragment. The remaining
semantic-adequacy assumption and production boundaries are listed in the
[README trust table](../README.md#main-result).

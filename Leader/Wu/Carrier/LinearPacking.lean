import Leader.AAFJ.Protocol
import Leader.Wu.Carrier.FivePassStateCount

/-!
# Static linear carrier packing

This module isolates the finite-state arithmetic behind a possible spatial
packing of the generalized AAFJ source state.  A source state has four Boolean
controls and one `Fin k` label.  The label is stored in the bit length of
`k - 1`, so

`width k = 4 + (log2 (k - 1) + 1)`.

The packed physical cell keeps one position in `Fin h`, two source payload
bits, and exactly the constant five-pass controls already exposed by
`PPLLPairedFivePassCarrier`.  The current controls have `65536` values, so the
audited product has `262144 * h` states.  No transition, stabilization, or
leader-election result is asserted here.
-/

namespace PPLLLinearCarrierPacking

open AAFJExactN
open PPLLPairedFivePassCarrier
open PPLLPolylogCarrierParameters

set_option autoImplicit false
set_option warningAsError true

/-! ## Width arithmetic -/

/-- Number of spatial bits needed for every value of `Fin k`.

For `k >= 2` this is the bit length of the largest label `k - 1`, equivalently
the least positive `ell` for which `k <= 2^ell`.
-/
def bitLength (k : Nat) : Nat := Nat.log2 (k - 1) + 1

/-- Four source-control slots followed by the binary label slots. -/
def width (k : Nat) : Nat := 4 + bitLength k

/-- The new label width is definitionally the existing rooted-carrier height
when both use the exact-size modulus `leastNonDivisor n`. -/
@[simp] theorem bitLength_leastNonDivisor_eq_carrierHeight (n : Nat) :
    bitLength (leastNonDivisor n) = carrierHeight n := rfl

theorem bitLength_pos (k : Nat) : 0 < bitLength k := by
  simp [bitLength]

theorem width_pos (k : Nat) : 0 < width k := by
  unfold width bitLength
  omega

/-- Every canonical `Fin k` label fits in `bitLength k` bits. -/
theorem le_two_pow_bitLength {k : Nat} (hk : 2 <= k) :
    k <= 2 ^ bitLength k := by
  have hm : k - 1 ≠ 0 := by omega
  have hlt : k - 1 < 2 ^ (Nat.log2 (k - 1) + 1) :=
    (Nat.log2_lt hm).1 (by omega)
  simpa [bitLength] using (show k <= 2 ^ (Nat.log2 (k - 1) + 1) by omega)

private theorem log2_add_five_le {m : Nat} (hm : 7 <= m) :
    Nat.log2 m + 5 <= m := by
  by_cases hsmall : m < 12
  · have hcases : m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;> decide
  · have hm2 : 2 <= m := by omega
    have hlog := Nat.log2_def m
    rw [if_pos hm2] at hlog
    have hhalf := Nat.log2_le_self (m / 2)
    rw [hlog]
    omega

/-- The seven-slot endpoint is sharp: `width 8 = 7`; thereafter width remains
strictly below the source modulus. -/
theorem width_lt {k : Nat} (hk : 8 <= k) : width k < k := by
  have hm : 7 <= k - 1 := by omega
  have hlog := log2_add_five_le hm
  unfold width bitLength
  omega

/-- Existing parameter arithmetic bounds the new four-control-plus-label width
by four more than the checked iterated-logarithm height envelope. -/
theorem width_leastNonDivisor_le_explicitHeightBound {n : Nat}
    (hn : 0 < n) :
    width (leastNonDivisor n) <= 4 + explicitHeightBound n := by
  unfold width
  rw [bitLength_leastNonDivisor_eq_carrierHeight]
  exact Nat.add_le_add_left (carrierHeight_le_explicitHeightBound hn) 4

/-- Minimality of `leastNonDivisor n` makes the static packing width divide the
physical ring size on the large branch. -/
theorem width_leastNonDivisor_dvd {n : Nat} (hn : 0 < n)
    (hk : 8 <= leastNonDivisor n) :
    width (leastNonDivisor n) ∣ n := by
  exact dvd_of_lt_leastNonDivisor hn
    (by unfold width; omega)
    (width_lt hk)

/-- Number of exact equal-width blocks in the packed physical ring. -/
def blockCount (n : Nat) : Nat := n / width (leastNonDivisor n)

/-- Dividing into exact-width blocks preserves the same nondivisor `k` needed
by the generalized AAFJ source protocol. -/
theorem leastNonDivisor_not_dvd_blockCount {n : Nat} (hn : 0 < n)
    (hk : 8 <= leastNonDivisor n) :
    ¬ leastNonDivisor n ∣ blockCount n := by
  intro hd
  rcases hd with ⟨q, hq⟩
  have hnfac : width (leastNonDivisor n) * blockCount n = n := by
    exact Nat.mul_div_cancel' (width_leastNonDivisor_dvd hn hk)
  apply leastNonDivisor_not_dvd hn
  refine ⟨width (leastNonDivisor n) * q, ?_⟩
  calc
    n = width (leastNonDivisor n) * blockCount n := hnfac.symm
    _ = width (leastNonDivisor n) * (leastNonDivisor n * q) := by rw [hq]
    _ = leastNonDivisor n * (width (leastNonDivisor n) * q) := by
      simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-! ## Explicit spatial source bits -/

/-- Numeric code for the four source controls in slots `0,1,2,3`, ordered as
`bullet`, `leader`, `probe`, and `phase`. -/
def sourceControlCode {k : Nat} (q : AAFJPK.State k) : Nat :=
  q.bullet.toNat + 2 * q.leader.toNat +
    4 * q.probe.toNat + 8 * q.phase.toNat

private theorem sourceControlCode_lt {k : Nat} (q : AAFJPK.State k) :
    sourceControlCode q < 16 := by
  rcases q with ⟨bullet, leader, label, probe, phase⟩
  cases bullet <;> cases leader <;> cases probe <;> cases phase <;>
    simp [sourceControlCode] <;> omega

/-- Mixed binary code: four low control bits followed by the label bits. -/
def sourceCode {k : Nat} (q : AAFJPK.State k) : Nat :=
  sourceControlCode q + q.label.val * 16

private theorem sourceCode_lt_two_pow_width {k : Nat} (hk : 2 <= k)
    (q : AAFJPK.State k) : sourceCode q < 2 ^ width k := by
  have hlabel : q.label.val < 2 ^ bitLength k :=
    Nat.lt_of_lt_of_le q.label.isLt (le_two_pow_bitLength hk)
  have hcontrol := sourceControlCode_lt q
  have hcode : sourceCode q < 16 * 2 ^ bitLength k := by
    unfold sourceCode
    omega
  simpa [width, Nat.pow_add] using hcode

/-- The fixed-width source snapshot.  Reading bit `i` gives the payload stored
at physical slot `i`. -/
def sourceBits {k : Nat} (q : AAFJPK.State k) : BitVec (width k) :=
  BitVec.ofNat (width k) (sourceCode q)

@[simp] theorem sourceBits_toNat {k : Nat} (hk : 2 <= k)
    (q : AAFJPK.State k) : (sourceBits q).toNat = sourceCode q := by
  rw [sourceBits, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (sourceCode_lt_two_pow_width hk q)]

private theorem sourceCode_div_sixteen {k : Nat} (q : AAFJPK.State k) :
    sourceCode q / 16 = q.label.val := by
  unfold sourceCode
  rw [Nat.add_mul_div_right _ _ (by decide)]
  rw [Nat.div_eq_of_lt (sourceControlCode_lt q)]
  simp

private theorem sourceCode_low_bit {k : Nat} (q : AAFJPK.State k)
    (i : Nat) (hi : i < 4) :
    (sourceCode q).testBit i = (sourceControlCode q).testBit i := by
  rw [sourceCode, Nat.add_comm, Nat.mul_comm q.label.val 16,
    show 16 = 2 ^ 4 by decide,
    Nat.testBit_two_pow_mul_add q.label.val (sourceControlCode_lt q) i,
    if_pos hi]

private theorem sourceControlCode_bit_zero {k : Nat} (q : AAFJPK.State k) :
    (sourceControlCode q).testBit 0 = q.bullet := by
  rcases q with ⟨bullet, leader, label, probe, phase⟩
  cases bullet <;> cases leader <;> cases probe <;> cases phase <;>
    simp [sourceControlCode] <;> decide

private theorem sourceControlCode_bit_one {k : Nat} (q : AAFJPK.State k) :
    (sourceControlCode q).testBit 1 = q.leader := by
  rcases q with ⟨bullet, leader, label, probe, phase⟩
  cases bullet <;> cases leader <;> cases probe <;> cases phase <;>
    simp [sourceControlCode] <;> decide

private theorem sourceControlCode_bit_two {k : Nat} (q : AAFJPK.State k) :
    (sourceControlCode q).testBit 2 = q.probe := by
  rcases q with ⟨bullet, leader, label, probe, phase⟩
  cases bullet <;> cases leader <;> cases probe <;> cases phase <;>
    simp [sourceControlCode] <;> decide

private theorem sourceControlCode_bit_three {k : Nat} (q : AAFJPK.State k) :
    (sourceControlCode q).testBit 3 = q.phase := by
  rcases q with ⟨bullet, leader, label, probe, phase⟩
  cases bullet <;> cases leader <;> cases probe <;> cases phase <;>
    simp [sourceControlCode] <;> decide

private theorem sourceState_ext {k : Nat} {q r : AAFJPK.State k}
    (hbullet : q.bullet = r.bullet) (hleader : q.leader = r.leader)
    (hlabel : q.label = r.label) (hprobe : q.probe = r.probe)
    (hphase : q.phase = r.phase) : q = r := by
  cases q
  cases r
  simp_all

/-- Total decoder for arbitrary spatial patterns.  Noncanonical label words
are reduced modulo `k`, as required for arbitrary initial physical states. -/
def decodeSource {k : Nat} (hk : 0 < k) (bits : BitVec (width k)) :
    AAFJPK.State k :=
  { bullet := bits.getLsbD 0
    leader := bits.getLsbD 1
    label := ⟨(bits.toNat / 16) % k, Nat.mod_lt _ hk⟩
    probe := bits.getLsbD 2
    phase := bits.getLsbD 3 }

/-- Decoding the spatial source bits recovers the full five-field source
state, including its `Fin k` label. -/
@[simp] theorem decodeSource_sourceBits {k : Nat} (hk : 2 <= k)
    (q : AAFJPK.State k) :
    decodeSource (by omega) (sourceBits q) = q := by
  have hnat := sourceBits_toNat hk q
  apply sourceState_ext
  · change (sourceBits q).toNat.testBit 0 = q.bullet
    rw [hnat]
    rw [sourceCode_low_bit q 0 (by omega), sourceControlCode_bit_zero]
  · change (sourceBits q).toNat.testBit 1 = q.leader
    rw [hnat]
    rw [sourceCode_low_bit q 1 (by omega), sourceControlCode_bit_one]
  · apply Fin.ext
    change ((sourceBits q).toNat / 16) % k = q.label.val
    rw [hnat]
    rw [sourceCode_div_sixteen, Nat.mod_eq_of_lt q.label.isLt]
  · change (sourceBits q).toNat.testBit 2 = q.probe
    rw [hnat]
    rw [sourceCode_low_bit q 2 (by omega), sourceControlCode_bit_two]
  · change (sourceBits q).toNat.testBit 3 = q.phase
    rw [hnat]
    rw [sourceCode_low_bit q 3 (by omega), sourceControlCode_bit_three]

/-- Reading a source snapshot at one physical slot. -/
def sourceBit {k : Nat} (q : AAFJPK.State k) (slot : Fin (width k)) : Bool :=
  (sourceBits q).getLsb slot

/-- Physical slot occupied by label bit `j`; slots `0..3` are the four
source-control bits. -/
def labelSlot {k : Nat} (j : Fin (bitLength k)) : Fin (width k) :=
  ⟨4 + j.val, by unfold width; omega⟩

/-- The label suffix of the spatial word is independent of all four source
controls.  This is the bit-level interface used by a streaming compiler that
rewrites the finite control prefix separately. -/
theorem sourceBit_labelSlot {k : Nat} (hk : 2 ≤ k) (q : AAFJPK.State k)
    (j : Fin (bitLength k)) :
    sourceBit q (labelSlot j) = q.label.val.testBit j.val := by
  unfold sourceBit sourceBits BitVec.getLsb
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (sourceCode_lt_two_pow_width hk q)]
  change (sourceCode q).testBit (4 + j.val) = q.label.val.testBit j.val
  rw [sourceCode, Nat.add_comm, Nat.mul_comm q.label.val 16,
    show 16 = 2 ^ 4 by decide,
    Nat.testBit_two_pow_mul_add q.label.val (sourceControlCode_lt q)]
  rw [if_neg (by omega)]
  simp

/-- The spatial bit layout is injective: no two AAFJ source states have the
same bit at every physical slot. -/
theorem sourceBit_injective {k : Nat} (hk : 2 <= k) :
    Function.Injective (sourceBit (k := k)) := by
  intro q r hbits
  have hvec : sourceBits q = sourceBits r := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have h := congrFun hbits (⟨i, hi⟩ : Fin (width k))
    simpa [sourceBit, BitVec.getLsb_eq_getElem] using h
  have hdecoded := congrArg (decodeSource (k := k) (by omega)) hvec
  rw [decodeSource_sourceBits hk q, decodeSource_sourceBits hk r] at hdecoded
  exact hdecoded

/-! ## Exact finite packed-cell carrier -/

/-- Linear physical carrier using the actual current five-pass controls.

The two Boolean payloads are the committed and staging source bits at `pos`.
The four constant controls are exactly the current `Role4`, `RootCtl32`,
`Msg32`, and `Trail16` fields; none carries another `Fin h`.
-/
structure PackedCell (h : Nat) where
  pos : Fin h
  activeBit : Bool
  stagingBit : Bool
  role : Role4
  rootCtl : RootCtl32
  message : Msg32
  trail : Trail16
  deriving DecidableEq, Repr

private abbrev PackedCellCode (h : Nat) :=
  ((((((Fin h × Bool) × Bool) × Role4) × RootCtl32) × Msg32) × Trail16)

private def decodePackedCell (h : Nat) (x : PackedCellCode h) : PackedCell h :=
  { pos := x.1.1.1.1.1.1
    activeBit := x.1.1.1.1.1.2
    stagingBit := x.1.1.1.1.2
    role := x.1.1.1.2
    rootCtl := x.1.1.2
    message := x.1.2
    trail := x.2 }

private def encodePackedCell (h : Nat) (x : PackedCell h) : PackedCellCode h :=
  ((((((x.pos, x.activeBit), x.stagingBit), x.role), x.rootCtl), x.message),
    x.trail)

@[simp] private theorem decode_encode_packedCell (h : Nat) (x : PackedCell h) :
    decodePackedCell h (encodePackedCell h x) = x := by
  cases x
  rfl

@[simp] private theorem encode_decode_packedCell (h : Nat)
    (x : PackedCellCode h) :
    encodePackedCell h (decodePackedCell h x) = x := by
  rcases x with ⟨⟨⟨⟨⟨⟨pos, activeBit⟩, stagingBit⟩, role⟩,
    rootCtl⟩, message⟩, trail⟩
  rfl

private theorem decodePackedCell_injective (h : Nat) :
    Function.Injective (decodePackedCell h) := by
  intro x y hxy
  have h := congrArg (encodePackedCell h) hxy
  simpa using h

private theorem decodePackedCell_surjective (h : Nat) :
    Function.Surjective (decodePackedCell h) := by
  intro x
  exact ⟨encodePackedCell h x, decode_encode_packedCell h x⟩

private def packedCellCodeSource (h : Nat) : ExhaustiveList (PackedCellCode h) :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod
        (ExhaustiveList.prod
          (ExhaustiveList.prod
            (ExhaustiveList.prod (ExhaustiveList.fin h) ExhaustiveList.bool)
            ExhaustiveList.bool)
          (ExhaustiveList.fin 4))
        (ExhaustiveList.fin 32))
      (ExhaustiveList.fin 32))
    (ExhaustiveList.fin 16)

/-- Constructive exhaustive list for the exact packed-cell type. -/
def packedCellStates (h : Nat) : ExhaustiveList (PackedCell h) :=
  ExhaustiveList.mapSurjective (packedCellCodeSource h) (decodePackedCell h)
    (decodePackedCell_surjective h)

private theorem packedCellCodeSource_nodup (h : Nat) :
    (packedCellCodeSource h).values.Nodup := by
  unfold packedCellCodeSource
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod
      · apply ExhaustiveList.values_nodup_prod
        · apply ExhaustiveList.values_nodup_prod
          · exact ExhaustiveList.values_nodup_prod _ _
              (ExhaustiveList.values_nodup_fin h)
              ExhaustiveList.values_nodup_bool
          · exact ExhaustiveList.values_nodup_bool
        · exact ExhaustiveList.values_nodup_fin 4
      · exact ExhaustiveList.values_nodup_fin 32
    · exact ExhaustiveList.values_nodup_fin 32
  · exact ExhaustiveList.values_nodup_fin 16

/-- The exhaustive packed-cell list contains no duplicates. -/
theorem packedCellStates_nodup (h : Nat) :
    (packedCellStates h).values.Nodup := by
  unfold packedCellStates
  exact ExhaustiveList.values_nodup_mapSurjective _ _ _
    (packedCellCodeSource_nodup h) (decodePackedCell_injective h)

/-- Exact audited cardinality.  The earlier value `98304 * h` used a different
hypothetical control product; the current source exposes `65536` control modes,
and the two payload bits multiply that by four. -/
theorem packedCellStates_length (h : Nat) :
    (packedCellStates h).values.length = 262144 * h := by
  unfold packedCellStates
  rw [ExhaustiveList.values_length_mapSurjective]
  simp [packedCellCodeSource, ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_bool, ExhaustiveList.values_length_fin,
    Nat.mul_comm]
  omega

/-! ## Static exact-size family envelope -/

/-- Exact count of the large static packed branch at physical size `n`. -/
def packedLargeBranchStateCount (n : Nat) : Nat :=
  262144 * width (leastNonDivisor n)

/-- The large-branch number is exactly the length of the packed-cell
certificate at the selected width. -/
theorem packedLargeBranchStateCount_eq_states (n : Nat) :
    packedLargeBranchStateCount n =
      (packedCellStates (width (leastNonDivisor n))).values.length := by
  rw [packedCellStates_length]
  rfl

/-- Explicit `O(log log n)` inequality inherited from the checked bound on the
least nondivisor.  This is a state-count statement, not a protocol theorem. -/
theorem packedLargeBranchStateCount_le_explicit {n : Nat} (hn : 0 < n) :
    packedLargeBranchStateCount n <=
      262144 * (4 + explicitHeightBound n) := by
  exact Nat.mul_le_mul_left 262144
    (width_leastNonDivisor_le_explicitHeightBound hn)

/-- The same bound with the iterated logarithm unfolded. -/
theorem packedLargeBranchStateCount_le_loglog {n : Nat} (hn : 0 < n) :
    packedLargeBranchStateCount n <=
      262144 * (4 + (Nat.log2 (Nat.log2 n + 1) + 1)) := by
  simpa [explicitHeightBound] using
    packedLargeBranchStateCount_le_explicit hn

/-- Piecewise static state count: use the literal `16*k` AAFJ source carrier
for `k < 8`, and the spatially packed carrier for `k >= 8`. -/
def staticPackingStateCount (n : Nat) : Nat :=
  if leastNonDivisor n < 8 then
    16 * leastNonDivisor n
  else
    packedLargeBranchStateCount n

theorem staticPackingStateCount_eq (n : Nat) :
    staticPackingStateCount n =
      if leastNonDivisor n < 8 then
        16 * leastNonDivisor n
      else
        262144 * width (leastNonDivisor n) := rfl

/-- The direct small-modulus source branch uses at most `112` local states. -/
theorem staticPackingStateCount_le_112_of_small {n : Nat}
    (hsmall : leastNonDivisor n < 8) :
    staticPackingStateCount n <= 112 := by
  simp [staticPackingStateCount, hsmall]
  omega

/-- One numerical envelope covering both static branches. -/
theorem staticPackingStateCount_le_piecewiseExplicit {n : Nat} (hn : 0 < n) :
    staticPackingStateCount n <=
      if leastNonDivisor n < 8 then
        112
      else
        262144 * (4 + explicitHeightBound n) := by
  by_cases hsmall : leastNonDivisor n < 8
  · simp [hsmall, staticPackingStateCount]
    omega
  · simp [hsmall, staticPackingStateCount]
    exact packedLargeBranchStateCount_le_explicit hn

/-- Finite-index decoder induced by the exact duplicate-free list. -/
def packedCellDecoder (h : Nat) :
    Fin (packedCellStates h).values.length -> PackedCell h :=
  (packedCellStates h).decode

theorem packedCellDecoder_bijective (h : Nat) :
    Function.Injective (packedCellDecoder h) ∧
      Function.Surjective (packedCellDecoder h) := by
  constructor
  · exact ExhaustiveList.decode_injective_of_values_nodup
      (packedCellStates h) (packedCellStates_nodup h)
  · exact ExhaustiveList.decode_surjective (packedCellStates h)

end PPLLLinearCarrierPacking

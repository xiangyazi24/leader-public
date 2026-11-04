import Leader.PPL.StateCount


/-!
# P_PL literal state view


The physical carrier is exactly `PPLv2.State`. This module fixes the two
representation choices needed by the literal transition:


* `mode = true` means `Detect`; `mode = false` means `Construct`.
* the finite token-offset code is decoded to the paper's signed nonzero range.


No transition semantics are defined here.
-/


namespace PPL


set_option autoImplicit false


abbrev State (psi kappa : Nat) := PPLv2.State psi kappa
abbrev Token (psi : Nat) := PPLv2.Token psi


inductive Mode where
  | Detect
  | Construct
  deriving DecidableEq


/-- Boolean representation used in `PPLv2.State`: true is Detect, false is
Construct. This makes Algorithm 4 line 50 literally the test
`clock = kappa`, and is the Boolean view of the Detect/Construct strings in
`scripts/ppl_reference.py`. -/
def modeView {psi kappa : Nat} (q : State psi kappa) : Mode :=
  if q.mode then .Detect else .Construct


@[simp] theorem mode_true_iff_detect {psi kappa : Nat}
    (q : State psi kappa) :
    q.mode = true ↔ modeView q = .Detect := by
  cases h : q.mode <;> simp [modeView, h]


@[simp] theorem mode_false_iff_construct {psi kappa : Nat}
    (q : State psi kappa) :
    q.mode = false ↔ modeView q = .Construct := by
  cases h : q.mode <;> simp [modeView, h]


/-- The paper domain for a non-bottom token offset:
`[-psi+1,-1] ∪ [1,psi]`. -/
def ValidOffset (psi : Nat) (z : Int) : Prop :=
  ((1 - ((psi : Nat) : Int) ≤ z ∧ z ≤ -1) ∨
    (1 ≤ z ∧ z ≤ ((psi : Nat) : Int)))


/-- Decode the `Fin (2*psi-1)` code in increasing signed order:
codes `0,...,psi-2` are `-psi+1,...,-1`, and
codes `psi-1,...,2*psi-2` are `1,...,psi`. -/
def decodeOffset (psi : Nat) (i : Fin (2 * psi - 1)) : Int :=
  if i.val < psi - 1 then
    ((i.val : Nat) : Int) - (((psi - 1 : Nat)) : Int)
  else
    (((i.val - (psi - 1) : Nat)) : Int) + 1


theorem decodeOffset_valid (psi : Nat) (hpsi : 0 < psi)
    (i : Fin (2 * psi - 1)) :
    ValidOffset psi (decodeOffset psi i) := by
  unfold decodeOffset ValidOffset
  by_cases h : i.val < psi - 1
  · rw [if_pos h]
    left
    constructor <;> omega
  · rw [if_neg h]
    right
    constructor <;> omega


/-- Encode a signed paper offset. No clamping or modulo is used: the
`ValidOffset` proof gives exactly the required finite index bound. -/
def encodeOffset (psi : Nat) (z : Int) (hz : ValidOffset psi z) :
    Fin (2 * psi - 1) :=
  match z, hz with
  | .ofNat 0, hz =>
      False.elim (by
        unfold ValidOffset at hz
        simp only [Int.ofNat_eq_natCast] at hz
        rcases hz with h | h <;> omega)
  | .ofNat (Nat.succ k), hz =>
      ⟨(psi - 1) + k, by
        unfold ValidOffset at hz
        simp only [Int.ofNat_eq_natCast] at hz
        rcases hz with h | h <;> omega⟩
  | .negSucc k, hz =>
      ⟨(psi - 2) - k, by
        unfold ValidOffset at hz
        simp only [Int.negSucc_eq] at hz
        rcases hz with h | h <;> omega⟩


theorem decode_encode (psi : Nat) (z : Int) (hz : ValidOffset psi z) :
    decodeOffset psi (encodeOffset psi z hz) = z := by
  cases z with
  | ofNat n =>
      have hz' := hz
      unfold ValidOffset at hz'
      simp only [Int.ofNat_eq_natCast] at hz'
      cases n with
      | zero =>
          exfalso
          rcases hz' with h | h <;> omega
      | succ k =>
          have hk : k + 1 ≤ psi := by
            rcases hz' with h | h <;> omega
          have hnot : ¬ ((psi - 1) + k < psi - 1) := by omega
          simp [encodeOffset, decodeOffset, hnot]
          all_goals omega
  | negSucc k =>
      have hz' := hz
      unfold ValidOffset at hz'
      simp only [Int.negSucc_eq] at hz'
      have hk : k + 2 ≤ psi := by
        rcases hz' with h | h <;> omega
      have hlt : (psi - 2) - k < psi - 1 := by omega
      simp [encodeOffset, decodeOffset, hlt, Int.negSucc_eq]
      all_goals omega


theorem decodeOffset_injective (psi : Nat) (hpsi : 0 < psi) :
    Function.Injective (decodeOffset psi) := by
  intro i j hij
  apply Fin.ext
  by_cases hi : i.val < psi - 1
  · by_cases hj : j.val < psi - 1
    · simp [decodeOffset, hi, hj] at hij
      omega
    · simp [decodeOffset, hi, hj] at hij
      omega
  · by_cases hj : j.val < psi - 1
    · simp [decodeOffset, hi, hj] at hij
      omega
    · simp [decodeOffset, hi, hj] at hij
      omega


theorem encode_decode (psi : Nat) (hpsi : 0 < psi)
    (i : Fin (2 * psi - 1)) :
    encodeOffset psi (decodeOffset psi i) (decodeOffset_valid psi hpsi i) = i := by
  apply decodeOffset_injective psi hpsi
  exact decode_encode psi (decodeOffset psi i) (decodeOffset_valid psi hpsi i)


/-! Boundary codes used by the transition and differential test.
The paper regime is psi >= 2. -/


def offsetNegPsiPlusOneCode (psi : Nat) (hpsi : 2 ≤ psi) :
    Fin (2 * psi - 1) :=
  ⟨0, by omega⟩


def offsetNegOneCode (psi : Nat) (hpsi : 2 ≤ psi) :
    Fin (2 * psi - 1) :=
  ⟨psi - 2, by omega⟩


def offsetOneCode (psi : Nat) (hpsi : 2 ≤ psi) :
    Fin (2 * psi - 1) :=
  ⟨psi - 1, by omega⟩


def offsetPsiCode (psi : Nat) (hpsi : 2 ≤ psi) :
    Fin (2 * psi - 1) :=
  ⟨2 * psi - 2, by omega⟩


theorem decodeOffset_negPsiPlusOne (psi : Nat) (hpsi : 2 ≤ psi) :
    decodeOffset psi (offsetNegPsiPlusOneCode psi hpsi) =
      1 - ((psi : Nat) : Int) := by
  have hlt : 0 < psi - 1 := by omega
  simp [decodeOffset, offsetNegPsiPlusOneCode, hlt]
  omega


theorem decodeOffset_negOne (psi : Nat) (hpsi : 2 ≤ psi) :
    decodeOffset psi (offsetNegOneCode psi hpsi) = -1 := by
  have hlt : psi - 2 < psi - 1 := by omega
  simp [decodeOffset, offsetNegOneCode, hlt]
  omega


theorem decodeOffset_one (psi : Nat) (hpsi : 2 ≤ psi) :
    decodeOffset psi (offsetOneCode psi hpsi) = 1 := by
  have hnot : ¬ (psi - 1 < psi - 1) := by omega
  simp [decodeOffset, offsetOneCode, hnot]


theorem decodeOffset_psi (psi : Nat) (hpsi : 2 ≤ psi) :
    decodeOffset psi (offsetPsiCode psi hpsi) = ((psi : Nat) : Int) := by
  have hnot : ¬ (2 * psi - 2 < psi - 1) := by omega
  simp [decodeOffset, offsetPsiCode, hnot]
  omega


end PPL

#print axioms PPL.decodeOffset_valid
#print axioms PPL.decode_encode
#print axioms PPL.encode_decode
#print axioms PPL.decodeOffset_injective
#print axioms PPL.decodeOffset_negPsiPlusOne
#print axioms PPL.decodeOffset_psi

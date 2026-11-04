import Leader.Wu.Entrance.LeafHorizonCalibration

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceK2Budget

open B6EntranceV2 B6EntranceV2K2
open B6EntranceV3 B6EntranceAdmissionV3
open B6EntranceK2Mass3 B6EntranceK2Mass4

variable {n psi : Nat}

/-- Exact smallest `B,Q` for fixed `L,M`. -/
private def exactStageBudget (n L M : Nat) : StageBudget where
  L := L
  M := M
  B := 2 * n * L
  Q := (4 * M) ^ L

private theorem exactStageBudget_valid
    (n L M : Nat) (hM : 1 <= M) :
    (exactStageBudget n L M).Valid n := by
  change B6EntranceCompose.EscapeBudget
    n L M (2 * n * L) ((4 * M) ^ L)
  unfold B6EntranceCompose.EscapeBudget
  exact ⟨hM, Nat.one_le_pow L (4 * M) (by omega), rfl, Nat.le_refl _⟩

theorem one_le_envelopeTouchBound (psi : Nat) :
    1 <= envelopeTouchBound psi := by
  unfold envelopeTouchBound envelopeWidth coreWidth collarWidth
  omega

/--
Source-certified arithmetic floor, NOT an inhabitance theorem for V3b laws.
Only the fixed reverse K2 word currently has a landed exact positive length.
The K2 matcher must carry the whole-envelope touch bound in order to satisfy
the final `postWriterMatch` clause exactly; zero-length unresolved stages use
minimal `M=1`.
-/
def c4Budget (n psi : Nat) : EntranceBudgets where
  writer := exactStageBudget n 0 (envelopeTouchBound psi)
  traffic := exactStageBudget n 0 1
  expiry := exactStageBudget n 0 1
  k2 := exactStageBudget n (k2DrainLength psi) (envelopeTouchBound psi)
  ruler := exactStageBudget n 0 1
  route := exactStageBudget n 0 1

@[simp] theorem c4Budget_postWriterL (n psi : Nat) :
    postWriterL (c4Budget n psi) = k2DrainLength psi := by
  simp [c4Budget, exactStageBudget, postWriterL]

@[simp] theorem c4Budget_postWriterQ (n psi : Nat) :
    postWriterQ (c4Budget n psi) =
      (4 * envelopeTouchBound psi) ^ k2DrainLength psi := by
  simp [c4Budget, exactStageBudget, postWriterQ]

@[simp] theorem c4Budget_entranceQ (n psi : Nat) :
    entranceQ (c4Budget n psi) =
      (4 * envelopeTouchBound psi) ^ k2DrainLength psi := by
  simp [entranceQ, c4Budget, exactStageBudget, postWriterQ]

@[simp] theorem c4Budget_totalL (n psi : Nat) :
    c4TotalL (c4Budget n psi) = k2DrainLength psi := by
  simp [c4TotalL, c4Budget, exactStageBudget, postWriterL]

theorem c4Budget_valid (n psi : Nat) :
    (c4Budget n psi).Valid n psi := by
  unfold EntranceBudgets.Valid
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exactStageBudget_valid n 0 (envelopeTouchBound psi)
      (one_le_envelopeTouchBound psi)
  · simp [c4Budget, exactStageBudget]
  · exact exactStageBudget_valid n 0 1 (by decide)
  · exact exactStageBudget_valid n 0 1 (by decide)
  · exact exactStageBudget_valid n (k2DrainLength psi)
      (envelopeTouchBound psi) (one_le_envelopeTouchBound psi)
  · exact exactStageBudget_valid n 0 1 (by decide)
  · exact exactStageBudget_valid n 0 1 (by decide)
  · rw [c4Budget_postWriterQ]
    exact Nat.one_le_pow _ _ (by
      have h := one_le_envelopeTouchBound psi
      omega)
  · rw [c4Budget_postWriterL, c4Budget_postWriterQ]
    exact Nat.le_refl _


namespace B6EntranceK2Budget

open B6EntranceV2 B6EntranceV2K2
open B6EntranceK2Mass4

/-- Closed coefficient forced already by the K2-only arithmetic floor. -/
def c4FrozenCoeff (psi Q2 : Nat) : Nat :=
  6 *
    (((4 * envelopeTouchBound psi) ^ k2DrainLength psi) * Q2) *
    (k2DrainLength psi + (psi - 1))

@[simp] theorem c4LeafCoeff_c4Budget
    (n psi Q2 : Nat) :
    c4LeafCoeff psi (c4Budget n psi) Q2 = c4FrozenCoeff psi Q2 := by
  unfold c4LeafCoeff c4FrozenCoeff
  rw [c4Budget_entranceQ, c4Budget_totalL]

/-- No hidden `b`: this is the specialized corrected leaf. -/
def C4CorrectedFinalLeafH (n psi Q2 : Nat) : Nat :=
  c4FrozenCoeff psi Q2 * n ^ 2

theorem c4BoostedH_eq_frozenCoeff_mul_n
    (n psi Q2 : Nat) :
    c4BoostedH n psi (c4Budget n psi) Q2 =
      c4FrozenCoeff psi Q2 * n := by
  have h := c4BoostedH_eq_coeff_mul_n_of_valid
    (n := n) (psi := psi) (c4Budget n psi) Q2
    (c4Budget_valid n psi)
  rw [c4LeafCoeff_c4Budget] at h
  exact h

theorem c4BoostedH_le_correctedFinalLeafH
    (n psi Q2 : Nat) (hn : 1 <= n) :
    c4BoostedH n psi (c4Budget n psi) Q2 <=
      C4CorrectedFinalLeafH n psi Q2 := by
  rw [c4BoostedH_eq_frozenCoeff_mul_n]
  unfold C4CorrectedFinalLeafH
  have hnn : n <= n ^ 2 := by
    have h := Nat.le_mul_of_pos_right n hn
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using h
  exact Nat.mul_le_mul_left _ hnn

theorem c4Calibration256_iff
    (n psi Q2 : Nat) :
    C4LedgerCalibration256 n psi (c4Budget n psi) Q2 <->
      c4FrozenCoeff psi Q2 <= 256 * n := by
  unfold C4LedgerCalibration256
  rw [c4LeafCoeff_c4Budget]


namespace B6EntranceK2Budget

open B6EntranceV2 B6EntranceV3 B6EntranceAdmissionV3

/-- Requested fixed-budget C4 target.  Inhabitance is intentionally separate. -/
def FrozenC4GateBundle
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ∃ WP : WriterProtected ring psi (Phys psi psi (16 * psi)),
    (c4Budget n psi).Valid n psi ∧
    ∃ hlaws : EntranceHostLawsV3b hpsi h2
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        (fun q : Phys psi psi (16 * psi) => q)
        ring WP (c4Budget n psi),
      B6EntranceK2Gate.C4K2EnvelopeGate
        hpsi h2 ring WP (c4Budget n psi) hlaws

theorem frozenC4GateBundle_readyWindow
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (hC4 : FrozenC4GateBundle hpsi h2 ring) :
    ∃ WP : WriterProtected ring psi (Phys psi psi (16 * psi)),
      ∃ hlaws : EntranceHostLawsV3b hpsi h2
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          (fun q : Phys psi psi (16 * psi) => q)
          ring WP (c4Budget n psi),
        UniformHostReadyWindowEscape
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          (fun q : Phys psi psi (16 * psi) => q) ring
          (entranceB n (c4Budget n psi))
          (entranceQ (c4Budget n psi)) := by
  rcases hC4 with ⟨WP, hbud, hlaws, _hGate⟩
  refine ⟨WP, hlaws, ?_⟩
  exact B6EntranceAdmissionV3.entranceLawsV3b_to_V2
    hpsi h2
    (B9Host.r1Host
      (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q)
    ring WP (c4Budget n psi) hbud hlaws

end B6EntranceK2Budget

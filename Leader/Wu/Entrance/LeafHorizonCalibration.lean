import Leader.Wu.Entrance.ReadyWindowMassSimulation


set_option autoImplicit false
set_option Elab.async false


namespace B6EntranceK2Mass4


open B6EntranceV2 B6EntranceV3 B6EntranceAdmissionV3
open B6EntranceK2Mass3
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C


variable {n psi : Nat}


def c4TotalL (b : EntranceBudgets) : Nat :=
  b.writer.L + postWriterL b


theorem entranceB_eq_two_mul_totalL_of_valid
    (b : EntranceBudgets) (hbud : b.Valid n psi) :
    entranceB n b = 2 * n * c4TotalL b := by
  have hw := hbud.1
  change B6EntranceCompose.EscapeBudget
    n b.writer.L b.writer.M b.writer.B b.writer.Q at hw
  have hB : b.writer.B = 2 * n * b.writer.L := hw.2.2.1
  unfold entranceB postWriterB c4TotalL
  rw [hB, Nat.mul_add]


theorem entranceQ_eq_product (b : EntranceBudgets) :
    entranceQ b =
      b.writer.Q *
        ((((b.traffic.Q * b.expiry.Q) * b.k2.Q) *
          b.ruler.Q) * b.route.Q) := by
  rfl


def c4BoostedH
    (n psi : Nat) (b : EntranceBudgets) (Q₂ : Nat) : Nat :=
  3 * (entranceQ b * Q₂) *
    (entranceB n b + 2 * n * (psi - 1))


def c4LeafCoeff
    (psi : Nat) (b : EntranceBudgets) (Q₂ : Nat) : Nat :=
  6 * (entranceQ b * Q₂) *
    (c4TotalL b + (psi - 1))


theorem c4BoostedH_eq_coeff_mul_n_of_valid
    (b : EntranceBudgets) (Q₂ : Nat)
    (hbud : b.Valid n psi) :
    c4BoostedH n psi b Q₂ = c4LeafCoeff psi b Q₂ * n := by
  unfold c4BoostedH c4LeafCoeff
  rw [entranceB_eq_two_mul_totalL_of_valid
    (n := n) (psi := psi) b hbud]
  have hadd :
      2 * n * c4TotalL b + 2 * n * (psi - 1) =
        2 * n * (c4TotalL b + (psi - 1)) := by
    rw [Nat.mul_add]
  rw [hadd]
  have h6 : 6 = 3 * 2 := by decide
  rw [h6]
  ac_rfl


def C4LedgerCalibration256
    (n psi : Nat) (b : EntranceBudgets) (Q₂ : Nat) : Prop :=
  c4LeafCoeff psi b Q₂ ≤ 256 * n


theorem r1LeafHorizonFits_of_valid_and_calibration
    (b : EntranceBudgets) (Q₂ : Nat)
    (hbud : b.Valid n psi)
    (hcal : C4LedgerCalibration256 n psi b Q₂) :
    R1LeafHorizonFits n psi
      (entranceB n b) (entranceQ b) Q₂ := by
  unfold R1LeafHorizonFits
  change c4BoostedH n psi b Q₂ ≤ 256 * n ^ 2
  rw [c4BoostedH_eq_coeff_mul_n_of_valid
    (n := n) (psi := psi) b Q₂ hbud]
  unfold C4LedgerCalibration256 at hcal
  have hmul := Nat.mul_le_mul_right n hcal
  simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc] using hmul


def C4CorrectedFinalLeafH
    (n psi : Nat) (b : EntranceBudgets) (Q₂ : Nat) : Nat :=
  c4LeafCoeff psi b Q₂ * n ^ 2


theorem c4BoostedH_le_correctedFinalLeafH
    (b : EntranceBudgets) (Q₂ : Nat)
    (hbud : b.Valid n psi) (hn : 1 ≤ n) :
    c4BoostedH n psi b Q₂ ≤
      C4CorrectedFinalLeafH n psi b Q₂ := by
  rw [c4BoostedH_eq_coeff_mul_n_of_valid
    (n := n) (psi := psi) b Q₂ hbud]
  unfold C4CorrectedFinalLeafH
  have hnn : n ≤ n ^ 2 := by
    have h := Nat.le_mul_of_pos_right n hn
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using h
  exact Nat.mul_le_mul_left _ hnn



def C4GateBundleWithBudget
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∃ WP : WriterProtected ring psi (Phys psi psi (16 * psi)),
    ∃ b : EntranceBudgets,
      b.Valid n psi ∧
      ∃ hlaws : EntranceHostLawsV3b hpsi h2
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          (fun q : Phys psi psi (16 * psi) => q) ring WP b,
        B6EntranceK2Gate.C4K2EnvelopeGate
          hpsi h2 ring WP b hlaws


theorem c4ReadyWindowMass_of_bundle
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (hC4 : C4GateBundleWithBudget hpsi h2 ring) :
    ∃ WP : WriterProtected ring psi (Phys psi psi (16 * psi)),
      ∃ b : EntranceBudgets,
        ∃ hlaws : EntranceHostLawsV3b hpsi h2
            (B9Host.r1Host
              (kappa := psi) (tau := 16 * psi) hpsi h2)
            (fun q : Phys psi psi (16 * psi) => q) ring WP b,
          b.Valid n psi ∧
          B6EntranceK2Gate.C4K2EnvelopeGate
            hpsi h2 ring WP b hlaws ∧
          UniformHostReadyWindowEscape
            (B9Host.r1Host
              (kappa := psi) (tau := 16 * psi) hpsi h2)
            (fun q : Phys psi psi (16 * psi) => q) ring
            (entranceB n b) (entranceQ b) := by
  rcases hC4 with ⟨WP, b, hbud, hlaws, hGate⟩
  refine ⟨WP, b, hlaws, hbud, hGate, ?_⟩
  exact B6EntranceAdmissionV3.entranceLawsV3b_to_V2
    hpsi h2
    (B9Host.r1Host
      (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q)
    ring WP b hbud hlaws


end B6EntranceK2Mass4

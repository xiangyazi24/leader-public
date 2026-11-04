import Leader.Wu.Entrance.ReadyWindowMassSimulation
import Leader.Wu.Entrance.PassiveProjection
import Leader.Wu.Entrance.PassiveAdmission
import Leader.Wu.Entrance.SharedBirthLeaf

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceK2MassAdmitted

open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open BirthCheckPermitRepairLeaf BirthCheckChainR1PerBlock
open B6EntranceK2Mass3
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi : Nat}

/-- R183 repair: same domination as the refuted global statement, but only
from a genuinely admitted final-carrier state. -/
def C4C5AdmittedR1MassSimulation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ (H : Nat) (C : Config n psi psi (16 * psi)),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C →
      BirthShortDoneTerminalFirstHit.Leaderless (finalBase C) ∧
      aliveCount
          (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
          FinalLeaderless C H ≤
        aliveCount (step1 hpsi h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless (finalBase C) H

private theorem baseLeaderless_of_final
    (C : Config n psi psi (16 * psi)) (hL : FinalLeaderless C) :
    BirthShortDoneTerminalFirstHit.Leaderless (finalBase C) := by
  intro i
  change outputFinal (C i) = false
  exact hL i

private theorem aliveAlong_r1_of_admitted
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (hn : 2 ≤ n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (C : Config n psi psi (16 * psi)) (u : List (Fin n))
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C)
    (hAlive : AliveAlong
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C u) :
    AliveAlong (step1 hpsi h2 ring)
      BirthShortDoneTerminalFirstHit.Leaderless (finalBase C) u := by
  induction u generalizing C with
  | nil => exact baseLeaderless_of_final C hAlive
  | cons e rest ih =>
      rcases hAlive with ⟨hL, hRest⟩
      have hstep := stepConcrete_base_eq_step1_of_passive_admitted
        hpsi h2 ring hn hR2 C e hA hL
      have hLnext : FinalLeaderless
          (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e) :=
        aliveAlong_good hRest
      have hnext := hClosed C e hA hL
      have hA' : ConcreteB7AdmittedPassive hpsi h2 ring
          (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e) := by
        rcases hnext with hLead | hAdm
        · rcases hLead with ⟨i, hi⟩
          have hz := hLnext i
          rw [hz] at hi
          cases hi
        · exact hAdm
      refine ⟨baseLeaderless_of_final C hL, ?_⟩
      have ht := ih
        (C := stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e)
        hA' hRest
      simpa only [hstep] using ht

private theorem wordSum_mono_length
    {m T : Nat} (f g : List (Fin m) → Nat)
    (h : ∀ u, u.length = T → f u ≤ g u) :
    FixedSpanRenewalPayload.wordSum m T f ≤
      FixedSpanRenewalPayload.wordSum m T g := by
  rw [← FixedSpanRenewalPayload.rawWord_sum m T f,
      ← FixedSpanRenewalPayload.rawWord_sum m T g]
  apply FiniteUniformStoppingTree.ofFn_sum_le
  intro i
  exact h _ (FixedSpanRenewalPayload.rawWord_length m T i)

private theorem aliveBit_le_r1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (hn : 2 ≤ n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (C : Config n psi psi (16 * psi)) (u : List (Fin n))
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C) :
    aliveBit (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        FinalLeaderless C u ≤
      aliveBit (step1 hpsi h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless (finalBase C) u := by
  classical
  by_cases hc : AliveAlong
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C u
  · have hr := aliveAlong_r1_of_admitted
      hpsi h2 ring hn hClosed hR2 C u hA hc
    simp [aliveBit, hc, hr]
  · simp [aliveBit, hc]

theorem c4C5AdmittedR1MassSimulation_of_closed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (hn : 2 ≤ n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring) :
    C4C5AdmittedR1MassSimulation hpsi h2 ring := by
  intro H C hA hL
  refine ⟨baseLeaderless_of_final C hL, ?_⟩
  unfold aliveCount
  apply wordSum_mono_length
  intro u _
  exact aliveBit_le_r1 hpsi h2 ring hn hClosed hR2 C u hA


/-- Stage-two C4/C5 leaf, restricted to admitted starts. -/
def C4C5SharedBirthWordMassAdmittedAt
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (H : Nat) : Prop :=
  ∀ C : Config n psi psi (16 * psi),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C →
    8 * avoidCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (fun _ : Config n psi psi (16 * psi) => True)
        HasLeader C H ≤
      (8 - 1) * n ^ H

private theorem aliveMass_pad_at {S : Type} {m : Nat}
    (step : S → Fin m → S) (Good : S → Prop)
    (x : S) (B H Q : Nat) (hBH : B ≤ H)
    (hb : Q * aliveCount step Good x B ≤ (Q - 1) * m ^ B) :
    Q * aliveCount step Good x H ≤ (Q - 1) * m ^ H := by
  have hp := alive_pad step Good (H - B) B x
  have hsum : B + (H - B) = H := by omega
  rw [hsum] at hp
  calc
    Q * aliveCount step Good x H
        ≤ Q * (aliveCount step Good x B * m ^ (H - B)) :=
      Nat.mul_le_mul_left Q hp
    _ = (Q * aliveCount step Good x B) * m ^ (H - B) := by
      rw [Nat.mul_assoc]
    _ ≤ ((Q - 1) * m ^ B) * m ^ (H - B) :=
      Nat.mul_le_mul_right _ hb
    _ = (Q - 1) * m ^ H := by
      rw [Nat.mul_assoc, ← Nat.pow_add, hsum]

theorem c4C5SharedBirthWordMassAdmittedAt_of_r1ReadyWindowMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (hpsin : psi ≤ n) (ring : DirectedRing n)
    (B₁ Q₁ Q₂ H : Nat) (hQ₁ : 1 ≤ Q₁)
    (hQ₂ : (4 * (psi + 1)) ^ (psi - 1) ≤ 3 ^ (psi - 1) * Q₂)
    (hReady : ∀ C : BirthCheckPermitRepairLeaf.FC n psi psi (16 * psi),
      BirthShortDoneTerminalFirstHit.Leaderless C →
      Q₁ * avoidCount (step1 hpsi h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless
          (ReadyWindow ring) C B₁ ≤ (Q₁ - 1) * n ^ B₁)
    (hSim : C4C5AdmittedR1MassSimulation hpsi h2 ring)
    (hH : 3 * (Q₁ * Q₂) * (B₁ + 2 * n * (psi - 1)) ≤ H) :
    C4C5SharedBirthWordMassAdmittedAt hpsi h2 ring H := by
  let H₀ := 3 * (Q₁ * Q₂) * (B₁ + 2 * n * (psi - 1))
  have hR1 : UniformEscapeMass
      (S := BirthCheckPermitRepairLeaf.FC n psi psi (16 * psi))
      (n := n)
      (step1 (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
      (fun C : BirthCheckPermitRepairLeaf.FC n psi psi (16 * psi) =>
        BirthShortDoneTerminalFirstHit.Leaderless C)
      H₀ 8 := by
    dsimp only [H₀]
    exact BirthCheckChainR1PerBlock.leaf_of_ready_window_mass
      (κ := psi) (τ := 16 * psi) hpsi h3 ring hpsin
      B₁ Q₁ Q₂ hQ₁ hQ₂ hReady
  intro C hA hL
  have hs := hSim H₀ C hA hL
  have hr := hR1 (finalBase C) hs.1
  have h0 : 8 * aliveCount
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C H₀ ≤ (8 - 1) * n ^ H₀ :=
    (Nat.mul_le_mul_left 8 hs.2).trans hr
  have hm := aliveMass_pad_at
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    FinalLeaderless C H₀ H 8 hH h0
  rw [B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
    (kappa := psi) (tau := 16 * psi) hpsi h2 ring C H] at hm
  exact hm

/-- Exact reduced-input producer surface.  Its proof is bookkeeping once
`CFinalSharedBirthLeaf.readyWindow_of_reducedInputs` is public. -/
def C4C5SharedBirthWordMassAdmittedReducedProducer
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ (_h3 : 2 < psi) (_hpsin : psi ≤ n),
    CFinalSharedBirthLeaf.ReducedC4LeafInputsV31 hpsi h2 ring →
    C4C5AdmittedR1MassSimulation hpsi h2 ring →
    C4C5SharedBirthWordMassAdmittedAt hpsi h2 ring
      (CFinalAssembly2.FinalLeafHV2 n psi)

/-- The raw B7 conclusion on the admitted lane. -/
def FinalB7OneOverNAdmittedAt
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (H : Nat) : Prop :=
  ∀ C : Config n psi psi (16 * psi),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C →
    n * BirthLeaderlessBirthMassB7Generic.firstLeaderFailureNumerator
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        FinalLeaderless C (6 * (Nat.log2 n + 1) * H) ≤
      n ^ (6 * (Nat.log2 n + 1) * H)

end B6EntranceK2MassAdmitted

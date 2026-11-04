import Leader.Wu.Birth.InstalledTwoStageSlots

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace ZZG4Assembly

open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape

variable {n ψ κ τ : Nat}

/-!
R322 / G4 horizon repair.

The stage-2 producer fixes its own block horizon to

  BoostedLeafH n B2 Q2

and the renewal consumers are horizon-parametric.  Therefore the primary
assembly below keeps that horizon literally; no equality with `FinalLeafHV2`
is assumed.
-/

/-- First convert the supplied Good=True first-hit mass into the exact
`Good := B` stage-1 currency expected by the compiled two-stage producer, then
invoke the compiled boosted leaf. -/
theorem boosted_block_escape
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (B2 Q2 : Nat) (hQ2 : 1 ≤ Q2)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hStage2 : ZZStage2Leaf.Stage2LeadershipMassV3
      (κ := κ) (τ := τ) hψ h2 ring B2 Q2) :
    ZZBlockEscape.StateUniformFixedWindowEscapeV3
      n ψ κ τ (ZZStage2Leaf.BoostedLeafH n B2 Q2)
      hψ h2 ring ZZBlockEscape.FinalLeaderlessV3 := by
  have hStage1 : ZZStage2Leaf.RecoveryFirstHitMassOnB
      (κ := κ) (τ := τ) hψ h2 ring :=
    ZZStage2Leaf.recoveryFirstHitMassOnB_of_true
      (κ := κ) (τ := τ) hψ h2 ring hFirst
  exact ZZStage2Leaf.two_stage_boosted_ZZBlockEscape_leaf
    (κ := κ) (τ := τ) hψ h2 ring hn
    B2 Q2 hQ2 hStage1 hStage2

/-- Item (1): exact final mass statement, with no `step` or `Good` drift. -/
theorem boosted_uniform_escape
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (B2 Q2 : Nat) (hQ2 : 1 ≤ Q2)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hStage2 : ZZStage2Leaf.Stage2LeadershipMassV3
      (κ := κ) (τ := τ) hψ h2 ring B2 Q2) :
    UniformEscapeMass
      (ZZFinalCarrierV3.stepConcreteV3
        (κ := κ) (τ := τ) hψ h2 ring)
      ZZBlockEscape.FinalLeaderlessV3
      (ZZStage2Leaf.BoostedLeafH n B2 Q2) 8 := by
  simpa only [ZZBlockEscape.StateUniformFixedWindowEscapeV3] using
    (boosted_block_escape
      (κ := κ) (τ := τ) hψ h2 ring hn
      B2 Q2 hQ2 hFirst hStage2)

/-- Item (2a): instantiate the geometric-tail consumer at exactly the boosted
block horizon.  No additional arithmetic side condition is needed. -/
theorem boosted_alive_tail
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (B2 Q2 : Nat) (hQ2 : 1 ≤ Q2)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hStage2 : ZZStage2Leaf.Stage2LeadershipMassV3
      (κ := κ) (τ := τ) hψ h2 ring B2 Q2) :
    ∀ (k : Nat) (C : ZZFinalCarrierV3.Config n ψ κ τ),
      ZZBlockEscape.FinalLeaderlessV3 C →
      8 ^ k *
          aliveCount
            (ZZFinalCarrierV3.stepConcreteV3
              (κ := κ) (τ := τ) hψ h2 ring)
            ZZBlockEscape.FinalLeaderlessV3 C
            (k * ZZStage2Leaf.BoostedLeafH n B2 Q2) ≤
        (8 - 1) ^ k *
          n ^ (k * ZZStage2Leaf.BoostedLeafH n B2 Q2) := by
  exact ZZBlockEscape.alive_tail_v3
    n ψ κ τ (ZZStage2Leaf.BoostedLeafH n B2 Q2)
    hψ h2 ring ZZBlockEscape.FinalLeaderlessV3
    (boosted_block_escape
      (κ := κ) (τ := τ) hψ h2 ring hn
      B2 Q2 hQ2 hFirst hStage2)

/-- Item (2b): instantiate the `1/n` consumer at the same boosted horizon. -/
theorem boosted_tail_one_over_n
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (B2 Q2 : Nat) (hQ2 : 1 ≤ Q2)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hStage2 : ZZStage2Leaf.Stage2LeadershipMassV3
      (κ := κ) (τ := τ) hψ h2 ring B2 Q2)
    (C : ZZFinalCarrierV3.Config n ψ κ τ)
    (hC : ZZBlockEscape.FinalLeaderlessV3 C) :
    n *
        aliveCount
          (ZZFinalCarrierV3.stepConcreteV3
            (κ := κ) (τ := τ) hψ h2 ring)
          ZZBlockEscape.FinalLeaderlessV3 C
          (6 * (Nat.log2 n + 1) *
            ZZStage2Leaf.BoostedLeafH n B2 Q2) ≤
      n ^
        (6 * (Nat.log2 n + 1) *
          ZZStage2Leaf.BoostedLeafH n B2 Q2) := by
  exact ZZBlockEscape.tail_one_over_n_v3
    n ψ κ τ (ZZStage2Leaf.BoostedLeafH n B2 Q2)
    hψ h2 ring ZZBlockEscape.FinalLeaderlessV3
    (boosted_block_escape
      (κ := κ) (τ := τ) hψ h2 ring hn
      B2 Q2 hQ2 hFirst hStage2)
    hn C hC

/-!
Quantifier-order audit.

`Stage2LeadershipExistsV3` existentially chooses `B2,Q2`.  They must be
eliminated before the consumer is instantiated, because they occur in the
consumer horizon.  The next two theorems make that order literal in Lean.
-/

theorem boosted_uniform_escape_of_stage2_exists
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hExists : ZZStage2Leaf.Stage2LeadershipExistsV3
      (κ := κ) (τ := τ) hψ h2 ring) :
    ∃ B2 Q2 : Nat,
      1 ≤ Q2 ∧
      UniformEscapeMass
        (ZZFinalCarrierV3.stepConcreteV3
          (κ := κ) (τ := τ) hψ h2 ring)
        ZZBlockEscape.FinalLeaderlessV3
        (ZZStage2Leaf.BoostedLeafH n B2 Q2) 8 := by
  rcases hExists with ⟨B2, Q2, hQ2, hStage2⟩
  refine ⟨B2, Q2, hQ2, ?_⟩
  exact boosted_uniform_escape
    (κ := κ) (τ := τ) hψ h2 ring hn
    B2 Q2 hQ2 hFirst hStage2

theorem boosted_tail_one_over_n_of_stage2_exists
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hExists : ZZStage2Leaf.Stage2LeadershipExistsV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : ZZFinalCarrierV3.Config n ψ κ τ)
    (hC : ZZBlockEscape.FinalLeaderlessV3 C) :
    ∃ B2 Q2 : Nat,
      1 ≤ Q2 ∧
      n *
          aliveCount
            (ZZFinalCarrierV3.stepConcreteV3
              (κ := κ) (τ := τ) hψ h2 ring)
            ZZBlockEscape.FinalLeaderlessV3 C
            (6 * (Nat.log2 n + 1) *
              ZZStage2Leaf.BoostedLeafH n B2 Q2) ≤
        n ^
          (6 * (Nat.log2 n + 1) *
            ZZStage2Leaf.BoostedLeafH n B2 Q2) := by
  rcases hExists with ⟨B2, Q2, hQ2, hStage2⟩
  refine ⟨B2, Q2, hQ2, ?_⟩
  exact boosted_tail_one_over_n
    (κ := κ) (τ := τ) hψ h2 ring hn
    B2 Q2 hQ2 hFirst hStage2 C hC

/-!
Optional compatibility with a corollary whose leaf parameter is frozen to
`CFinalAssembly2.FinalLeafHV2 n ψ`.

The required inequality direction is

  BoostedLeafH n B2 Q2 ≤ FinalLeafHV2 n ψ.

This is only a horizon-padding statement inside the SAME V3 step/Good process;
it does not identify the V3 carrier with the older `FinalCandidateR2C` carrier.
-/

/-- Public local copy of the already-used padding argument from
`CFinalAssembly2.uniformEscapeMass_pad_v2`. -/
private theorem uniformEscapeMass_pad
    {S : Type} {m : Nat}
    (step : S → Fin m → S) (Good : S → Prop)
    (B H Q : Nat) (hBH : B ≤ H)
    (hMass : UniformEscapeMass step Good B Q) :
    UniformEscapeMass step Good H Q := by
  intro x hx
  have hb := hMass x hx
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

/-- Item (3): if an external final statement insists on `FinalLeafHV2`, this
is the exact arithmetic premise needed to transfer the boosted mass to it. -/
theorem finalLeaf_block_escape_of_le
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (B2 Q2 : Nat) (hQ2 : 1 ≤ Q2)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hStage2 : ZZStage2Leaf.Stage2LeadershipMassV3
      (κ := κ) (τ := τ) hψ h2 ring B2 Q2)
    (hH : ZZStage2Leaf.BoostedLeafH n B2 Q2 ≤
      CFinalAssembly2.FinalLeafHV2 n ψ) :
    ZZBlockEscape.StateUniformFixedWindowEscapeV3
      n ψ κ τ (CFinalAssembly2.FinalLeafHV2 n ψ)
      hψ h2 ring ZZBlockEscape.FinalLeaderlessV3 := by
  change UniformEscapeMass
    (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    ZZBlockEscape.FinalLeaderlessV3
    (CFinalAssembly2.FinalLeafHV2 n ψ) 8
  exact uniformEscapeMass_pad
    (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    ZZBlockEscape.FinalLeaderlessV3
    (ZZStage2Leaf.BoostedLeafH n B2 Q2)
    (CFinalAssembly2.FinalLeafHV2 n ψ) 8 hH
    (boosted_uniform_escape
      (κ := κ) (τ := τ) hψ h2 ring hn
      B2 Q2 hQ2 hFirst hStage2)

/-- Consequently the old *numeric* leaf horizon can be fed to the V3 consumer
if and only if an adequate forward-padding inequality is supplied. -/
theorem finalLeaf_tail_one_over_n_of_le
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (B2 Q2 : Nat) (hQ2 : 1 ≤ Q2)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hStage2 : ZZStage2Leaf.Stage2LeadershipMassV3
      (κ := κ) (τ := τ) hψ h2 ring B2 Q2)
    (hH : ZZStage2Leaf.BoostedLeafH n B2 Q2 ≤
      CFinalAssembly2.FinalLeafHV2 n ψ)
    (C : ZZFinalCarrierV3.Config n ψ κ τ)
    (hC : ZZBlockEscape.FinalLeaderlessV3 C) :
    n *
        aliveCount
          (ZZFinalCarrierV3.stepConcreteV3
            (κ := κ) (τ := τ) hψ h2 ring)
          ZZBlockEscape.FinalLeaderlessV3 C
          (6 * (Nat.log2 n + 1) *
            CFinalAssembly2.FinalLeafHV2 n ψ) ≤
      n ^
        (6 * (Nat.log2 n + 1) *
          CFinalAssembly2.FinalLeafHV2 n ψ) := by
  exact ZZBlockEscape.tail_one_over_n_v3
    n ψ κ τ (CFinalAssembly2.FinalLeafHV2 n ψ)
    hψ h2 ring ZZBlockEscape.FinalLeaderlessV3
    (finalLeaf_block_escape_of_le
      (κ := κ) (τ := τ) hψ h2 ring hn
      B2 Q2 hQ2 hFirst hStage2 hH)
    hn C hC

#print axioms ZZG4Assembly.boosted_block_escape
#print axioms ZZG4Assembly.boosted_uniform_escape
#print axioms ZZG4Assembly.boosted_alive_tail
#print axioms ZZG4Assembly.boosted_tail_one_over_n
#print axioms ZZG4Assembly.boosted_uniform_escape_of_stage2_exists
#print axioms ZZG4Assembly.boosted_tail_one_over_n_of_stage2_exists
#print axioms ZZG4Assembly.finalLeaf_block_escape_of_le
#print axioms ZZG4Assembly.finalLeaf_tail_one_over_n_of_le

end ZZG4Assembly

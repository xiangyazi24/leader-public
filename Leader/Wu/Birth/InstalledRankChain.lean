import Leader.Wu.Scheduler.BellmanRankMass
import Leader.Wu.Birth.InstalledBoostedTail


set_option autoImplicit false
set_option Elab.async false


namespace ZZInstalledChain


open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open ZZBellmanTemplate
open ZZBellmanTemplate.InstalledV3


variable {n ψ κ τ : Nat}


/-!
R406 source-state note.


At the default-branch source state used to assemble this file, the R401
producer for `ZZStage2Leaf.RecoveryFirstHitMassV3` has not landed.  Therefore
`hFirst` remains an explicit stage-1 wrapper hypothesis below.


The two open *rank* premises are exactly:
* ingredient (b): `InstalledRankNonincreaseV3` (`hMono`);
* ingredient (c): `InstalledRankDescentV3` (`hDesc`).


Ingredient (a), `InstalledRankBoundV3`, is also passed explicitly because the
rank and its numerical bound `K` are parameters of this conditional artifact.
Once the R401 wrapper producer lands, the composed theorems below can replace
`hFirst` by that producer without changing the stage-2/rank part.
-/


/-- The installed Bellman theorem at its native Q=2 horizon. -/
theorem installed_rank_half_mass
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank) :
    UniformEscapeMass
      (ZZFinalCarrierV3.stepConcreteV3
        (κ := κ) (τ := τ) hψ h2 ring)
      ZZBlockEscape.FinalLeaderlessV3
      (rankHalfH n K) 2 := by
  exact installed_half_mass_of_rank
    (κ := κ) (τ := τ) hψ h2 ring rank K hBound hMono hDesc


/-- Direct rank-only Q=8 leaf.  Q=8 is not available at `rankHalfH n K`
from the installed Bellman theorem; the compiled boost gives the exact horizon
`3 * 2 * rankHalfH n K`. -/
theorem installed_rank_eighth_block_escape
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank) :
    ZZBlockEscape.StateUniformFixedWindowEscapeV3
      n ψ κ τ (3 * 2 * rankHalfH n K)
      hψ h2 ring ZZBlockEscape.FinalLeaderlessV3 := by
  change UniformEscapeMass
    (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    ZZBlockEscape.FinalLeaderlessV3
    (3 * 2 * rankHalfH n K) 8
  apply rank_eighth_uniformEscapeMass
    (step := ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (Bad := ZZBlockEscape.FinalLeaderlessV3)
    (rank := rank) (K := K)
  · simpa [InstalledRankBoundV3] using hBound
  · simpa [InstalledRankNonincreaseV3] using hMono
  · simpa [InstalledRankDescentV3] using hDesc


/-- Stage-1 wrapper hookup.  This is the exact compiled conversion used by
`ZZG4Assembly.boosted_block_escape`: the Good=True first-hit currency implies
the Good=B first-hit currency required by `two_stage_escape`. -/
theorem recovery_stage1_onB_of_wrapper
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring) :
    ZZStage2Leaf.RecoveryFirstHitMassOnB
      (κ := κ) (τ := τ) hψ h2 ring := by
  exact ZZStage2Leaf.recoveryFirstHitMassOnB_of_true
    (κ := κ) (τ := τ) hψ h2 ring hFirst


/-- Use the installed Q=2 rank block as stage 2.


The extra `RecoveryTargetV3` hypothesis in the stage-2 interface is unused:
the installed rank theorem is stronger, since it is uniform over every
`FinalLeaderlessV3` state. -/
theorem stage2_rank_half_of_installed_rank
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank) :
    ZZStage2Leaf.Stage2LeadershipMassV3
      (κ := κ) (τ := τ) hψ h2 ring (rankHalfH n K) 2 := by
  apply
    (ZZStage2Leaf.stage2_B_iff_finalLeaderlessV3
      (κ := κ) (τ := τ) hψ h2 ring (rankHalfH n K) 2).2
  unfold ZZStage2Leaf.Stage2LeadershipMassFinalLeaderlessV3
  intro C hC _hRecovery
  have hm := installed_rank_half_mass
    (κ := κ) (τ := τ) hψ h2 ring rank K hBound hMono hDesc
  have hCmass := hm C hC
  simpa only [ZZStage2Leaf.stepV3] using hCmass


/-- The requested single-import conditional chain:
recovery first-hit (stage 1) + installed rank (stage 2) -> exact V3 Q=8 block. -/
theorem installed_two_stage_block_escape
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring) :
    ZZBlockEscape.StateUniformFixedWindowEscapeV3
      n ψ κ τ
      (ZZStage2Leaf.BoostedLeafH n (rankHalfH n K) 2)
      hψ h2 ring ZZBlockEscape.FinalLeaderlessV3 := by
  exact ZZG4Assembly.boosted_block_escape
    (κ := κ) (τ := τ) hψ h2 ring hn
    (rankHalfH n K) 2 (by omega) hFirst
    (stage2_rank_half_of_installed_rank
      (κ := κ) (τ := τ) hψ h2 ring rank K hBound hMono hDesc)


/-- `alive_tail` at the exact composed/boosted horizon.
All side conditions are explicit in the theorem telescope. -/
theorem installed_two_stage_alive_tail
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring) :
    ∀ (k : Nat) (C : ZZFinalCarrierV3.Config n ψ κ τ),
      ZZBlockEscape.FinalLeaderlessV3 C →
      8 ^ k *
          aliveCount
            (ZZFinalCarrierV3.stepConcreteV3
              (κ := κ) (τ := τ) hψ h2 ring)
            ZZBlockEscape.FinalLeaderlessV3 C
            (k * ZZStage2Leaf.BoostedLeafH
              n (rankHalfH n K) 2) ≤
        (8 - 1) ^ k *
          n ^ (k * ZZStage2Leaf.BoostedLeafH
            n (rankHalfH n K) 2) := by
  exact ZZBlockEscape.alive_tail_v3
    n ψ κ τ
    (ZZStage2Leaf.BoostedLeafH n (rankHalfH n K) 2)
    hψ h2 ring ZZBlockEscape.FinalLeaderlessV3
    (installed_two_stage_block_escape
      (κ := κ) (τ := τ) hψ h2 ring hn
      rank K hBound hMono hDesc hFirst)


/-- `tail_one_over_n` at the exact composed/boosted horizon.
The only extra consumer side condition is `hn : 2 ≤ n`. -/
theorem installed_two_stage_tail_one_over_n
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : ZZFinalCarrierV3.Config n ψ κ τ)
    (hC : ZZBlockEscape.FinalLeaderlessV3 C) :
    n *
        aliveCount
          (ZZFinalCarrierV3.stepConcreteV3
            (κ := κ) (τ := τ) hψ h2 ring)
          ZZBlockEscape.FinalLeaderlessV3 C
          (6 * (Nat.log2 n + 1) *
            ZZStage2Leaf.BoostedLeafH n (rankHalfH n K) 2) ≤
      n ^
        (6 * (Nat.log2 n + 1) *
          ZZStage2Leaf.BoostedLeafH n (rankHalfH n K) 2) := by
  exact ZZBlockEscape.tail_one_over_n_v3
    n ψ κ τ
    (ZZStage2Leaf.BoostedLeafH n (rankHalfH n K) 2)
    hψ h2 ring ZZBlockEscape.FinalLeaderlessV3
    (installed_two_stage_block_escape
      (κ := κ) (τ := τ) hψ h2 ring hn
      rank K hBound hMono hDesc hFirst)
    hn C hC


/-- Publicly reproducible copy of the padding argument used in
`ZZG4Assembly`/`CFinalAssembly2`.  Padding is valid only forward in the horizon. -/
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


/-- Optional numeric-horizon compatibility with `CFinalAssembly2.FinalLeafHV2`.
This needs exactly one additional arithmetic premise: the boosted V3 horizon
must fit below the frozen numeric horizon. -/
theorem installed_two_stage_finalLeaf_block_escape_of_le
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hH : ZZStage2Leaf.BoostedLeafH n (rankHalfH n K) 2 ≤
      CFinalAssembly2.FinalLeafHV2 n ψ) :
    ZZBlockEscape.StateUniformFixedWindowEscapeV3
      n ψ κ τ (CFinalAssembly2.FinalLeafHV2 n ψ)
      hψ h2 ring ZZBlockEscape.FinalLeaderlessV3 := by
  have h0 := installed_two_stage_block_escape
    (κ := κ) (τ := τ) hψ h2 ring hn
    rank K hBound hMono hDesc hFirst
  change UniformEscapeMass
    (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    ZZBlockEscape.FinalLeaderlessV3
    (ZZStage2Leaf.BoostedLeafH n (rankHalfH n K) 2) 8 at h0
  change UniformEscapeMass
    (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    ZZBlockEscape.FinalLeaderlessV3
    (CFinalAssembly2.FinalLeafHV2 n ψ) 8
  exact uniformEscapeMass_pad
    (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    ZZBlockEscape.FinalLeaderlessV3
    (ZZStage2Leaf.BoostedLeafH n (rankHalfH n K) 2)
    (CFinalAssembly2.FinalLeafHV2 n ψ) 8 hH h0


/-- `alive_tail` after optional padding to the frozen numeric final leaf. -/
theorem installed_two_stage_finalLeaf_alive_tail_of_le
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hH : ZZStage2Leaf.BoostedLeafH n (rankHalfH n K) 2 ≤
      CFinalAssembly2.FinalLeafHV2 n ψ) :
    ∀ (k : Nat) (C : ZZFinalCarrierV3.Config n ψ κ τ),
      ZZBlockEscape.FinalLeaderlessV3 C →
      8 ^ k *
          aliveCount
            (ZZFinalCarrierV3.stepConcreteV3
              (κ := κ) (τ := τ) hψ h2 ring)
            ZZBlockEscape.FinalLeaderlessV3 C
            (k * CFinalAssembly2.FinalLeafHV2 n ψ) ≤
        (8 - 1) ^ k *
          n ^ (k * CFinalAssembly2.FinalLeafHV2 n ψ) := by
  exact ZZBlockEscape.alive_tail_v3
    n ψ κ τ (CFinalAssembly2.FinalLeafHV2 n ψ)
    hψ h2 ring ZZBlockEscape.FinalLeaderlessV3
    (installed_two_stage_finalLeaf_block_escape_of_le
      (κ := κ) (τ := τ) hψ h2 ring hn
      rank K hBound hMono hDesc hFirst hH)


/-- Final `1/n` consumer at `FinalLeafHV2`; every premise is visible here. -/
theorem installed_two_stage_finalLeaf_tail_one_over_n_of_le
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank)
    (hFirst : ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (hH : ZZStage2Leaf.BoostedLeafH n (rankHalfH n K) 2 ≤
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
    (installed_two_stage_finalLeaf_block_escape_of_le
      (κ := κ) (τ := τ) hψ h2 ring hn
      rank K hBound hMono hDesc hFirst hH)
    hn C hC


#print axioms ZZInstalledChain.installed_rank_eighth_block_escape
#print axioms ZZInstalledChain.stage2_rank_half_of_installed_rank
#print axioms ZZInstalledChain.installed_two_stage_block_escape
#print axioms ZZInstalledChain.installed_two_stage_tail_one_over_n
#print axioms ZZInstalledChain.installed_two_stage_finalLeaf_tail_one_over_n_of_le


end ZZInstalledChain

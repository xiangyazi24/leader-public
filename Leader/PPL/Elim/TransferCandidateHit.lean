import Leader.PPL.Elim.TransferArith
import Leader.PPL.Elim.LocalDeletionCounting
import Leader.PPL.Elim.PBClosure

/-!
# YSM21 repair transfer: common-block candidate hit

This file implements Lemma 2 of `LDC_TRANSFER.md` in the exact finite-word
language of `design/LDTRANSFER_LEAN_PLAN.md`, and records the exact Prop
signature of Lemma 3 for the next transfer step.
-/

namespace PPL.Convergence.LDTransfer

open PPL.Convergence.LDLocal
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

set_option autoImplicit false
set_option Elab.async false

/-- Generic local-deletion statement LD(c), definitionally matching the
planned transfer interface. -/
def LDStatement (c : Nat) : Prop :=
  ∀ {n : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n),
    PPL.Elim.PB ring C →
    2 ≤ PPL.Elim.leaderCount C →
    ∀ F : TripleFrame ring C, ∀ T : Nat,
      costNumerator (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (c * n * (F.a + F.b))

/-- Number of raw scheduler words whose endpoint satisfies P. -/
noncomputable def hitMass {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) (x : S) (T : Nat) : Nat := by
  classical
  exact wordSum next (fun y => if P y then 1 else 0) x T

/-- Lemma 2: every short block-start candidate is hit by at least half of one
common scheduler block.

The tagged target is absorbing by `taggedDeleted_step`, so no PB-closure or
last-leader hypothesis belongs in this statement. -/
theorem candidate_hit_common_block
    {c : Nat}
    (hLD : LDStatement c) (hc : 1 ≤ c)
    {n s H : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hPB : PPL.Elim.PB ring C)
    (hcount : PPL.Elim.leaderCount C = s) (hs : 2 ≤ s)
    (F : TripleFrame ring C)
    (hspan : s * (F.a + F.b) ≤ 8 * n)
    (hH : 16 * c * n * n ≤ s * H) :
    n ^ H ≤
      2 * hitMass (stepE ring) (TaggedDeleted F) C H := by
  have hleaders : 2 ≤ PPL.Elim.leaderCount C := by
    rw [hcount]
    exact hs
  have hcost :=
    hLD hn ring C hPB hleaders F H
  have hclosed :
      ∀ D : PPL.Convergence.LDLocal.Config n, ∀ edge : Fin n,
        TaggedDeleted F D →
          TaggedDeleted F (stepE ring D edge) := by
    intro D edge hD
    exact taggedDeleted_step F D edge hD
  have hcharge :=
    PPL.Probability.horizon_mul_missCount_le_costNumerator
      (stepE ring) (TaggedDeleted F) hclosed H C

  have hspos : 0 < s := by
    omega
  have hscaled :
      s * (2 * (c * n * (F.a + F.b))) ≤ s * H := by
    calc
      s * (2 * (c * n * (F.a + F.b))) =
          (2 * c * n) * (s * (F.a + F.b)) := by
        ac_rfl
      _ ≤ (2 * c * n) * (8 * n) :=
        Nat.mul_le_mul_left (2 * c * n) hspan
      _ = (2 * 8) * (c * n * n) := by
        ac_rfl
      _ = 16 * (c * n * n) := by
        rfl
      _ = 16 * c * n * n := by
        ac_rfl
      _ ≤ s * H := hH
  have hscale :
      2 * (c * n * (F.a + F.b)) ≤ H :=
    Nat.le_of_mul_le_mul_left hscaled hspos

  have ha : 0 < F.a := by
    simpa [F.A_gap] using F.A.gap_pos
  have hab : 0 < F.a + F.b := by
    omega
  have hcpos : 0 < c := by
    omega
  have hnpos : 0 < n := by
    omega
  have hnumpos : 0 < c * n * (F.a + F.b) :=
    Nat.mul_pos (Nat.mul_pos hcpos hnpos) hab
  have hHpos : 0 < H := by
    omega

  have hdelay :
      1 * costNumerator (stepE ring) (TaggedDeleted F) C H ≤
        (c * n * (F.a + F.b)) * n ^ H := by
    simp only [Nat.one_mul]
    calc
      costNumerator (stepE ring) (TaggedDeleted F) C H ≤
          n ^ H * (c * n * (F.a + F.b)) := hcost
      _ = (c * n * (F.a + F.b)) * n ^ H := by
        exact Nat.mul_comm _ _
  have hscaleMarkov :
      2 * (c * n * (F.a + F.b)) ≤ H * 1 := by
    simpa using hscale
  have hmiss :
      2 * wordSum (stepE ring) (miss (TaggedDeleted F)) C H ≤
        n ^ H :=
    FiniteUniformStoppingTree.two_mul_le_of_scaled_delay
      (L := H)
      (miss := wordSum (stepE ring) (miss (TaggedDeleted F)) C H)
      (delay := costNumerator (stepE ring) (TaggedDeleted F) C H)
      (den := 1)
      (num := c * n * (F.a + F.b))
      (total := n ^ H)
      hHpos (by decide) hcharge hdelay hscaleMarkov

  have hpartition :
      hitMass (stepE ring) (TaggedDeleted F) C H +
          wordSum (stepE ring) (miss (TaggedDeleted F)) C H =
        n ^ H := by
    classical
    unfold hitMass
    rw [← LeaderCountDyadicTail.wordSum_add]
    have hweight :
        (fun D : PPL.Convergence.LDLocal.Config n =>
          (if TaggedDeleted F D then 1 else 0) +
            miss (TaggedDeleted F) D) =
          (fun _ : PPL.Convergence.LDLocal.Config n => 1) := by
      funext D
      by_cases hD : TaggedDeleted F D
      · simp [miss, hD]
      · simp [miss, hD]
    rw [hweight, LeaderCountDyadicTail.wordSum_const]
    simp
  omega

/-- Lemma 3, with the exact signature commissioned in
`design/LDTRANSFER_LEAN_PLAN.md`. -/
def one_block_contract_mass
    {c : Nat}
    (hLD : LDStatement c) (hc : 1 ≤ c)
    {n s H : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hPB : PPL.Elim.PB ring C)
    (hcount : PPL.Elim.leaderCount C = s) (hs : 2 ≤ s)
    (hH : 16 * c * n * n ≤ s * H) : Prop :=
  n ^ H ≤
    3 * hitMass (stepE ring)
      (fun D => 24 * PPL.Elim.leaderCount D < 23 * s) C H

end PPL.Convergence.LDTransfer

#print axioms PPL.Convergence.LDTransfer.candidate_hit_common_block

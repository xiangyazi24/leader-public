import Leader.Wu.Birth.LeaderlessBirthMassRenewal
import Leader.Wu.Safety.CorrectedFormulation
import Leader.Wu.Splice.InstalledCarrier
import Leader.Wu.WriteSeq.WriterProducerRepair

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact block-escape obligation for the repaired final carrier

This file states the R247 / `LDR-CAMPAIGN-MISSING-OBJECT-IS-BLOCK-ESCAPE`
leaf in exactly the currency consumed by
`BirthLeaderlessBirthMassRenewal.alive_tail` and `tail_one_over_n`.

The mathematical missing theorem is a proof of
`StateUniformFixedWindowEscapeV3` for the `Good` predicate and block length `L`
chosen by the terminal consumer.  Nothing in this file assumes a descent rank,
a per-edge service schedule, or a state-dependent horizon.
-/

namespace ZZBlockEscape

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair WriterProducerRepair
open BirthLeaderlessBirthMassRenewal

/--
The exact R247 leaf.

Quantifier order is load-bearing: `L` and `Good` are fixed before the universal
quantifier over current states introduced by `UniformEscapeMass`.

The sample space is the `n^L` length-`L` scheduler words over `Fin n` used by
`aliveCount`; one letter means one service of one of the `n` directed ring
edges.  It is not repeated service of one distinguished edge.
-/
def StateUniformFixedWindowEscapeV3
    (n ψ κ τ L : Nat)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (Good : ZZFinalCarrierV3.Config n ψ κ τ → Prop) : Prop :=
  UniformEscapeMass
    (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    Good L 8

/-- Literal expansion of the R247 leaf. -/
theorem stateUniformFixedWindowEscapeV3_iff
    (n ψ κ τ L : Nat)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (Good : ZZFinalCarrierV3.Config n ψ κ τ → Prop) :
    StateUniformFixedWindowEscapeV3
        n ψ κ τ L hψ h2 ring Good ↔
      ∀ C : ZZFinalCarrierV3.Config n ψ κ τ,
        Good C →
        8 * aliveCount
              (ZZFinalCarrierV3.stepConcreteV3
                (κ := κ) (τ := τ) hψ h2 ring)
              Good C L ≤
          (8 - 1) * n ^ L :=
  Iff.rfl

/--
Literal substitution into `alive_tail`.  This is the exact geometric statement
that the existing consumer proves once R247 is supplied.
-/
theorem alive_tail_v3
    (n ψ κ τ L : Nat)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (Good : ZZFinalCarrierV3.Config n ψ κ τ → Prop)
    (hblock : StateUniformFixedWindowEscapeV3
      n ψ κ τ L hψ h2 ring Good) :
    ∀ (k : Nat) (C : ZZFinalCarrierV3.Config n ψ κ τ),
      Good C →
      8 ^ k * aliveCount
            (ZZFinalCarrierV3.stepConcreteV3
              (κ := κ) (τ := τ) hψ h2 ring)
            Good C (k * L) ≤
        (8 - 1) ^ k * n ^ (k * L) :=
  alive_tail
    (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    Good L 8 hblock

/--
Literal substitution into `tail_one_over_n`.

The total scheduler horizon is exactly
`6 * (Nat.log2 n + 1) * L`: there is no extra factor of `n`, no `+ L`, and no
per-edge service conversion.
-/
theorem tail_one_over_n_v3
    (n ψ κ τ L : Nat)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (Good : ZZFinalCarrierV3.Config n ψ κ τ → Prop)
    (hblock : StateUniformFixedWindowEscapeV3
      n ψ κ τ L hψ h2 ring Good)
    (hn : 2 ≤ n)
    (C : ZZFinalCarrierV3.Config n ψ κ τ)
    (hC : Good C) :
    n * aliveCount
          (ZZFinalCarrierV3.stepConcreteV3
            (κ := κ) (τ := τ) hψ h2 ring)
          Good C (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) :=
  tail_one_over_n
    (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    Good L hblock hn C hC

/--
A strictly weaker qualitative statement: the same fixed window `L` has at
least one scheduler word that leaves `Good` at some prefix, from every `Good`
state.

This does NOT imply the Q=8 R247 leaf at the same `L`: it gives only one
escaping word out of `n^L`, whereas R247 requires at least one eighth of the
word mass to escape.
-/
def StateUniformOneWordEscapeV3
    (n ψ κ τ L : Nat)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (Good : ZZFinalCarrierV3.Config n ψ κ τ → Prop) : Prop :=
  ∀ C : ZZFinalCarrierV3.Config n ψ κ τ,
    Good C →
    ∃ u : List (Fin n),
      u.length = L ∧
      ¬ AliveAlong
          (ZZFinalCarrierV3.stepConcreteV3
            (κ := κ) (τ := τ) hψ h2 ring)
          Good C u

/-!
There is deliberately no theorem

  StateUniformOneWordEscapeV3 ... ->
    StateUniformFixedWindowEscapeV3 ...

at the same block length.  The first predicate is qualitative; the second is
the seven-eighths mass inequality required by `tail_one_over_n`.

Likewise, the existing inner theorem
`ZZV31RowEscapesTokenFreeMixed.stepV3_allEdgesTokenFreeMixed_ne` cannot supply
this file's leaf: it concerns `R2CoherenceV31.stepV3`, while R247 concerns the
outer installed `ZZFinalCarrierV3.stepConcreteV3`; and state movement is not
escape from an arbitrary `Good` predicate.
-/

/-- Observable leader bit on the repaired final carrier. -/
def outputFinalV3 {ψ κ τ : Nat}
    (u : ZZFinalCarrierV3.Cell ψ κ τ) : Bool :=
  u.phys.phys.base.core.core.leader

/--
Natural first-leader `Good` predicate, matching the old final-carrier convention.
This is provided as a concrete non-vacuity check; R247 itself keeps `Good`
explicit because `CorrectedFormulation.UniformFiniteHorizonSSLE` ultimately
uses semantic safety, which is stronger than mere leader existence.
-/
def FinalLeaderlessV3 {n ψ κ τ : Nat}
    (C : ZZFinalCarrierV3.Config n ψ κ τ) : Prop :=
  ∀ i : Fin n, outputFinalV3 (C i) = false

/-- Q=8 R247 specialized to first leader appearance. -/
def LeaderlessBlockEscapeV3
    (n ψ κ τ L : Nat)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  StateUniformFixedWindowEscapeV3
    n ψ κ τ L hψ h2 ring
    (fun C : ZZFinalCarrierV3.Config n ψ κ τ => FinalLeaderlessV3 C)

section NonVacuity

private theorem h3 : 0 < 3 := by decide

/-- Repository-standard concrete follower, copied from the compiled V3 witness style. -/
private def literalFollower (lab : Fin 3) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := .none
      path := .bot
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

private def leaderlessPhys : ZZFinalCarrierV3.P 3 3 48 :=
  ⟨literalFollower 1, ⟨.open, .none⟩⟩

private def leaderlessCell : ZZFinalCarrierV3.Cell 3 3 48 :=
  ⟨leaderlessPhys, .none, false, false⟩

private def leaderlessConfig : ZZFinalCarrierV3.Config 2 3 3 48 :=
  fun _ => leaderlessCell

/-- `FinalLeaderlessV3` is inhabited by a literal final-carrier configuration. -/
theorem finalLeaderlessV3_nonvacuous :
    ∃ C : ZZFinalCarrierV3.Config 2 3 3 48, FinalLeaderlessV3 C := by
  refine ⟨leaderlessConfig, ?_⟩
  intro i
  rfl

end NonVacuity

end ZZBlockEscape

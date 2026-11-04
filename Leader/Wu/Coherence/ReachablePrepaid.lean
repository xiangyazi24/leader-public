import Leader.Wu.Coherence.ReachableOpenNoHazard

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachablePrepaid

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachableSweep

variable {n ψ κ τ : Nat}

private theorem branch_release_conditions_prepaid
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok = .release := by
  unfold branchAtV3 at hb
  by_cases hSeek : r.ctl.tok = .seek
  · rw [if_pos hSeek] at hb
    cases hb
  · rw [if_neg hSeek] at hb
    by_cases hSweep : l.ctl.tok = .sweep
    · rw [if_pos hSweep] at hb
      cases hb
    · rw [if_neg hSweep] at hb
      by_cases hCommit : r.ctl.tok = .commit
      · rw [if_pos hCommit] at hb
        cases hb
      · rw [if_neg hCommit] at hb
        by_cases hRelease : l.ctl.tok = .release
        · exact ⟨hSeek, hSweep, hCommit, hRelease⟩
        · rw [if_neg hRelease] at hb
          by_cases hScrub : r.ctl.tok = .scrubL
          · rw [if_pos hScrub] at hb
            cases hb
          · rw [if_neg hScrub] at hb
            by_cases hOpenR : l.ctl.tok = .openR
            · rw [if_pos hOpenR] at hb
              cases hb
            · rw [if_neg hOpenR] at hb
              by_cases hNone : l.ctl.tok = .none ∧ r.ctl.tok = .none
              · rw [if_pos hNone] at hb
                by_cases hSealed :
                    l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed
                · rw [if_pos hSealed] at hb
                  cases hb
                · rw [if_neg hSealed] at hb
                  by_cases hOpen : l.ctl.mark = .open ∧ r.ctl.mark = .open
                  · rw [if_pos hOpen] at hb
                    by_cases hHaz :
                        pairHazardV3 l.phys r.phys
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb

private theorem branch_scrubL_conditions_prepaid
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .scrubL) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok = .scrubL := by
  unfold branchAtV3 at hb
  by_cases hSeek : r.ctl.tok = .seek
  · rw [if_pos hSeek] at hb
    cases hb
  · rw [if_neg hSeek] at hb
    by_cases hSweep : l.ctl.tok = .sweep
    · rw [if_pos hSweep] at hb
      cases hb
    · rw [if_neg hSweep] at hb
      by_cases hCommit : r.ctl.tok = .commit
      · rw [if_pos hCommit] at hb
        cases hb
      · rw [if_neg hCommit] at hb
        by_cases hRelease : l.ctl.tok = .release
        · rw [if_pos hRelease] at hb
          cases hb
        · rw [if_neg hRelease] at hb
          by_cases hScrub : r.ctl.tok = .scrubL
          · exact ⟨hSeek, hSweep, hCommit, hRelease, hScrub⟩
          · rw [if_neg hScrub] at hb
            by_cases hOpenR : l.ctl.tok = .openR
            · rw [if_pos hOpenR] at hb
              cases hb
            · rw [if_neg hOpenR] at hb
              by_cases hNone : l.ctl.tok = .none ∧ r.ctl.tok = .none
              · rw [if_pos hNone] at hb
                by_cases hSealed :
                    l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed
                · rw [if_pos hSealed] at hb
                  cases hb
                · rw [if_neg hSealed] at hb
                  by_cases hOpen : l.ctl.mark = .open ∧ r.ctl.mark = .open
                  · rw [if_pos hOpen] at hb
                    by_cases hHaz :
                        pairHazardV3 l.phys r.phys
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb

/-- What the current release guard actually prepays at its owner. -/
theorem release_guard_prepays_owner
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    (C e).ctl.mark = .releasing ∧ GroupOwnedClearV31 ring C e := by
  rcases hFacts with ⟨_, _, _, hRelease, _, _⟩
  have hc := branch_release_conditions_prepaid hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  exact hRelease e hc.2.2.2

/-- What the current scrubL guard actually prepays: mark/nonroot/full ownership
at the *responder scrub owner*.  There is no overlap-wide freshness fact for
the predecessor which can become the new openR owner. -/
theorem scrubL_guard_prepays_current_owner
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    (C (ring.rightNeighbor e)).ctl.mark = .releasing ∧
      (raw (C (ring.rightNeighbor e))).label.val ≠ 0 ∧
        GroupOwnedClearV31 ring C (ring.rightNeighbor e) := by
  rcases hFacts with ⟨_, _, _, _, hScrub, _⟩
  have hc := branch_scrubL_conditions_prepaid hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  exact hScrub (ring.rightNeighbor e) hc.2.2.2.2

/-- Exact missing current-state clause for the root-handoff arm of scrubL.
Only that arm installs openR at the predecessor `e`. -/
def ScrubLIncomingOpenRFreshV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ e : Fin n,
    (C (ring.rightNeighbor e)).ctl.tok = .scrubL →
    successorB (C e) (C (ring.rightNeighbor e)) = true →
    atRootB (C e) = true →
      OpenROwnerFreshV3 ring C e

instance scrubLIncomingOpenRFreshV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (ScrubLIncomingOpenRFreshV31 ring C) := by
  unfold ScrubLIncomingOpenRFreshV31
  infer_instance


namespace ScrubLPayloadGap

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring4 : DirectedRing 4 := ⟨by decide⟩

private def literal
    (lab : Fin 3)
    (state : MainState := .none) : R2.Cell 3 3 0 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := state
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
      b_carry := false
  }
  ⟨⟨⟨b', false⟩, 0⟩, 0⟩

private def cell
    (p : R2.Cell 3 3 0)
    (m : R2Coherence.Mark) (t : TokenV3) : Cell 3 3 0 :=
  ⟨p, ⟨m, t⟩⟩

/-- Labels [0,1,2,0].  The scrub owner is site 1, whose own group is
{0,1,2}.  Site 3 is a stale equality in the previous/overlapping label-zero
window and is deliberately outside that owned group. -/
private def pre : FC 4 3 3 0 := fun i =>
  match i.val with
  | 0 => cell (literal 0) .releasing .none
  | 1 => cell (literal 1) .releasing .scrubL
  | 2 => cell (literal 2) .closing .none
  | _ => cell (literal 0 .equal) .open .none

private def after : FC 4 3 3 0 :=
  stepV3 h3 h23 ring4 pre 0

theorem pre_election : ElectionGeometryV31 ring4 pre := by
  decide +kernel

theorem pre_facts : ReachablePhaseFactsV31 ring4 pre := by
  decide +kernel

theorem pre_branch :
    branchAtV3 h3 h23 (pre 0) (pre (ring4.rightNeighbor 0)) = .scrubL := by
  decide +kernel

/-- The root handoff really installs the new openR owner at site 0. -/
theorem after_openR : (after 0).ctl.tok = .openR := by
  decide +kernel

/-- The previous short group's window [3,0,1] contains the new owner 0, so the
stale equal/path=bot cell at 3 witnesses failure of the strengthened freshness
obligation. -/
theorem after_owner_not_fresh :
    ¬ OpenROwnerFreshV3 ring4 after 0 := by
  decide +kernel

/-- Therefore the current B-multi payload is not closed under this scrubL
root-handoff state. -/
theorem after_not_facts :
    ¬ ReachablePhaseFactsV31 ring4 after := by
  decide +kernel

/-- The proposed missing clause rejects the witness already in the pre-state. -/
theorem pre_missing_incoming_fresh :
    ¬ ScrubLIncomingOpenRFreshV31 ring4 pre := by
  decide +kernel

end ScrubLPayloadGap



end R2CoherenceV31ReachablePrepaid

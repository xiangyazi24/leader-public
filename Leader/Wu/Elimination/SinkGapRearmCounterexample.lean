import Leader.Wu.Elimination.SinkGapServiceRank

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapServiceRank
  LDSinkGapDoneInvariant LDSinkGapBlockedPreStep PPLLRepair LDTwoGapFrame
open Classical

namespace LDSinkGapRearmCounterexample

set_option autoImplicit false

variable {n ψ : Nat}

/-!
# The C3 residual is too strong

There is a newly-blocked R7 transition which need not move K2's physical
service rank at all.  The live bullet can already be parked at `pos 1`; an
outside follower-to-victim edge can merely deliver `signal_B = 1` to the
victim.  R7 then changes `gapW` discontinuously to zero because `GapBlocked`
is an old stopping disjunct, whereas K2's `gapWC` remains `d + 1`.

The FIRE-created-bullet scenario is not the issue: initiator FIRE creates its
live bullet on the initiator, not on `pos 1`.

The structures below isolate the exact counterexample certificate without
changing either rank.  The two successor facts in `R7RearmBlockedWitness` are
the local kernel obligations for a concrete fixture; the rank contradiction
which follows from them is completely generic.
-/

/-- Concrete pre-state fields for the rearm-to-blocked edge.

`e` is the outside predecessor of the gap victim.  The gap already contains
exactly the parked live bullet at `pos 1`, but the victim is neither shielded
nor signalled, so the state is not yet `GapBlocked`. -/
structure RearmEntryFields (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) : Prop where
  incoming_to_victim : F.ring.rightNeighbor e = F.pos 0
  incoming_follower : (C e).leader = false
  incoming_signal : (C e).signal_B = (1 : Fin 2)
  incoming_bullet_zero : (C e).bullet = (0 : Fin 3)
  victim_shield_zero : (C (F.pos 0)).shield = false
  victim_signal_zero : (C (F.pos 0)).signal_B = (0 : Fin 2)
  victim_bullet_zero : (C (F.pos 0)).bullet = (0 : Fin 3)
  parked_live : (C (F.pos 1)).bullet = (2 : Fin 3)
  tail_empty : ∀ k, 2 ≤ k → k ≤ F.d →
    (C (F.pos k)).bullet = (0 : Fin 3)

/-- The field pattern is not R7-blocked before the rearm edge: the parked
bullet is present, but the victim has neither of the protection witnesses. -/
theorem rearm_entry_not_blocked (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : RearmEntryFields F C e) :
    ¬ GapBlocked F C := by
  intro hb
  rcases hb.2.2 with hs | hs
  · have hbad : (false : Bool) = true :=
      h.victim_shield_zero.symm.trans hs
    cases hbad
  · have hbad : (0 : Fin 2) = (1 : Fin 2) :=
      h.victim_signal_zero.symm.trans hs
    exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) hbad

/-- Under the gap invariant, the same parked bullet also rules out K2
completion before the rearm edge. -/
theorem rearm_entry_not_doneC (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : RearmEntryFields F C e) (hi : GapInvariant hψ F C) :
    ¬ GapDoneC F C := by
  intro hd
  rcases hd with hc | he
  · have h1d : 1 ≤ F.d := by
      have hlen := F.hd
      omega
    have hz := hc.2 1 (Nat.le_refl 1) h1d
    have hbad : (2 : Fin 3) = (0 : Fin 3) :=
      h.parked_live.symm.trans hz
    exact (by decide : (2 : Fin 3) ≠ (0 : Fin 3)) hbad
  · rcases he with h0 | hd
    · have hbad : (true : Bool) = false :=
        hi.1.1.symm.trans h0
      cases hbad
    · have hbad : (true : Bool) = false :=
        hi.1.2.symm.trans hd
      cases hbad

/-- The C protected guard cannot fire on the incoming edge because its input
initiator is a follower.  This uses C1's input-leader projection rather than
simplifying the complete kernel. -/
theorem rearm_entry_not_guard (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : RearmEntryFields F C e) :
    ¬ ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e)) := by
  intro hg
  have hl :=
    (protectedGuard_input_leaders hψ
      (C e) (C (F.ring.rightNeighbor e)) hg).1
  have hbad : (false : Bool) = true :=
    h.incoming_follower.symm.trans hl
  cases hbad

/-- `topIdx` is exactly one when position one is live and every higher
position is false. -/
private theorem topIdx_eq_one_of_one_true_tail_false
    (P : Nat → Bool) :
    ∀ m : Nat, 1 ≤ m → P 1 = true →
      (∀ k, 2 ≤ k → k ≤ m → P k = false) →
      topIdx P m = 1 := by
  intro m
  induction m with
  | zero =>
      intro hm
      omega
  | succ m ih =>
      intro hm h1 ht
      by_cases hm0 : m = 0
      · subst m
        unfold topIdx
        simp [h1]
      · unfold topIdx
        have hlast : P (m + 1) = false :=
          ht (m + 1) (by omega) (Nat.le_refl _)
        rw [hlast]
        apply ih (by omega) h1
        intro k hk hkm
        exact ht k hk (Nat.le_trans hkm (Nat.le_succ m))

private theorem bulletTop_eq_one_of_parked_tail
    (F : GapFrame n) (C : Fin n → AgentState ψ)
    (h1 : (C (F.pos 1)).bullet = (2 : Fin 3))
    (ht : ∀ k, 2 ≤ k → k ≤ F.d →
      (C (F.pos k)).bullet = (0 : Fin 3)) :
    bulletTop F C = 1 := by
  unfold bulletTop
  apply topIdx_eq_one_of_one_true_tail_false
  · have hlen := F.hd
    omega
  · rw [h1]
    decide
  · intro k hk hkd
    rw [ht k hk hkd]
    decide

private theorem bulletTop_eq_one_of_blocked
    (F : GapFrame n) (C : Fin n → AgentState ψ)
    (hb : GapBlocked F C) :
    bulletTop F C = 1 :=
  bulletTop_eq_one_of_parked_tail F C hb.1 hb.2.1

/-- Exact one-step certificate for the false strict-transfer branch.

For the concrete rearm edge, the two remaining fields are obtained by
unfolding the old FIRE/MOVE/SIGNAL/dummy stages: FIRE is inert, MOVE is inert,
SIGNAL writes `1` to the responder leader, and the dummy sink frames that
signal.  All positive gap cells are framed, so the invariant remains true.
They are kept as named certificate fields here so this rank file does not
repeat C2b's private kernel development. -/
structure R7RearmBlockedWitness (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) : Prop where
  fields : RearmEntryFields F C e
  invariant : GapInvariant hψ F C
  successor_invariant : GapInvariant hψ F (sinkStep hψ F C e)
  successor_blocked : GapBlocked F (sinkStep hψ F C e)

private theorem rearm_stepC_eq_step (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : R7RearmBlockedWitness hψ F C e) :
    sinkStepC hψ F C e = sinkStep hψ F C e :=
  sinkStepC_eq_of_not_guard hψ F C e
    (rearm_entry_not_guard hψ F C e h.fields)

private theorem rearm_pre_gapWC_eq (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : R7RearmBlockedWitness hψ F C e) :
    gapWC F C = F.d + 1 := by
  have hnd := rearm_entry_not_doneC hψ F C e h.fields h.invariant
  have htop := bulletTop_eq_one_of_parked_tail F C
    h.fields.parked_live h.fields.tail_empty
  have h10 : (1 : Nat) ≠ 0 := by omega
  unfold gapWC
  rw [if_neg hnd, htop, if_neg h10]

private theorem rearm_post_gapWC_eq (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : R7RearmBlockedWitness hψ F C e) :
    gapWC F (sinkStepC hψ F C e) = F.d + 1 := by
  have heq := rearm_stepC_eq_step hψ F C e h
  have hbC : GapBlocked F (sinkStepC hψ F C e) := by
    rw [heq]
    exact h.successor_blocked
  have hiC : GapInvariant hψ F (sinkStepC hψ F C e) := by
    rw [heq]
    exact h.successor_invariant
  have hndC : ¬ GapDoneC F (sinkStepC hψ F C e) :=
    gapBlocked_not_doneC hψ F (sinkStepC hψ F C e) hbC hiC
  have htop := bulletTop_eq_one_of_blocked F
    (sinkStepC hψ F C e) hbC
  have h10 : (1 : Nat) ≠ 0 := by omega
  unfold gapWC
  rw [if_neg hndC, htop, if_neg h10]

/-- This is the true rank projection for the newly-blocked rearm branch:
K2's rank is framed, hence certainly nonincreasing.  It is equality, not a
strict drop. -/
theorem r7_land_blocked_rank_le (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : R7RearmBlockedWitness hψ F C e) :
    gapWC F (sinkStepC hψ F C e) ≤ gapWC F C := by
  rw [rearm_post_gapWC_eq hψ F C e h,
    rearm_pre_gapWC_eq hψ F C e h]
  exact Nat.le_refl _

/-- Stronger exact statement: the physical K2 service rank does not change on
this rearm-to-blocked transition. -/
theorem r7_rearm_blocked_rank_frame (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : R7RearmBlockedWitness hψ F C e) :
    gapWC F (sinkStepC hψ F C e) = gapWC F C := by
  rw [rearm_post_gapWC_eq hψ F C e h,
    rearm_pre_gapWC_eq hψ F C e h]

/-- R7 nevertheless reports a strict killed-rank drop, solely because the
successor has entered its old `GapBlocked` stopping set. -/
theorem r7_rearm_old_rank_drop (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : R7RearmBlockedWitness hψ F C e) :
    gapW F (sinkStep hψ F C e) + 1 ≤ gapW F C := by
  have hdone : GapDone F (sinkStep hψ F C e) :=
    Or.inr (Or.inr h.successor_blocked)
  have hz := gapW_done F (sinkStep hψ F C e) hdone
  have hnb := rearm_entry_not_blocked F C e h.fields
  have hpre := gapW_eq_gapWC_of_not_blocked F C hnb
  have hc := rearm_pre_gapWC_eq hψ F C e h
  rw [hz, hpre, hc]
  omega

/-- Therefore the strict-transfer clause used by `CRankResidual` is false on
this one-step pattern. -/
theorem r7_land_blocked_strict_transfer_false
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : R7RearmBlockedWitness hψ F C e) :
    ¬ (gapW F (sinkStep hψ F C e) + 1 ≤ gapW F C →
      gapWC F (sinkStepC hψ F C e) < gapWC F C) := by
  intro hstrict
  have hlt := hstrict (r7_rearm_old_rank_drop hψ F C e h)
  have hframe := r7_rearm_blocked_rank_frame hψ F C e h
  rw [hframe] at hlt
  exact Nat.lt_irrefl _ hlt

/-- The current C3 residual itself is refuted by the same witness.  Its first
(nonincrease) conjunct is compatible with this transition; the second strict
conjunct is the contradiction. -/
theorem rearm_entry_refutes_CRankResidual
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : R7RearmBlockedWitness hψ F C e) :
    ¬ CRankResidual hψ F C := by
  intro hres
  have hnb := rearm_entry_not_blocked F C e h.fields
  have hr := hres e (Or.inr ⟨hnb, Or.inr h.successor_blocked⟩)
  have hlt := hr.2 hnb (r7_rearm_old_rank_drop hψ F C e h)
  have hframe := r7_rearm_blocked_rank_frame hψ F C e h
  rw [hframe] at hlt
  exact Nat.lt_irrefl _ hlt

/-- In particular, the requested universal theorem
`GapInvariant → ¬GapDoneC → CRankResidual` cannot hold on any instantiation of
this concrete rearm certificate. -/
theorem cRankResidual_holds_false_on_rearm
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : R7RearmBlockedWitness hψ F C e) :
    ¬ (GapInvariant hψ F C → ¬ GapDoneC F C →
      CRankResidual hψ F C) := by
  intro hall
  have hnd := rearm_entry_not_doneC hψ F C e h.fields h.invariant
  have hres := hall h.invariant hnd
  exact (rearm_entry_refutes_CRankResidual hψ F C e h) hres

end LDSinkGapRearmCounterexample

#print axioms LDSinkGapRearmCounterexample.rearm_entry_not_blocked
#print axioms LDSinkGapRearmCounterexample.rearm_entry_not_doneC
#print axioms LDSinkGapRearmCounterexample.rearm_entry_not_guard
#print axioms LDSinkGapRearmCounterexample.r7_land_blocked_rank_le
#print axioms LDSinkGapRearmCounterexample.r7_rearm_blocked_rank_frame
#print axioms LDSinkGapRearmCounterexample.r7_rearm_old_rank_drop
#print axioms LDSinkGapRearmCounterexample.r7_land_blocked_strict_transfer_false
#print axioms LDSinkGapRearmCounterexample.rearm_entry_refutes_CRankResidual
#print axioms LDSinkGapRearmCounterexample.cRankResidual_holds_false_on_rearm

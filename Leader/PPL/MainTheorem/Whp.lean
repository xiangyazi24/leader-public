import Leader.PPL.MainTheorem.Skeleton
import Leader.PPL.Modes.MidEntryRetimedSplit
import Leader.PPL.Elim.OneLeaderBoundLeaves
import Leader.PPL.Convergence.QuietWindow
import Leader.PPL.Elim.LiteralBridges
import Leader.PPL.Safety.PeacefulScan
import Leader.Wu.Scheduler.RepeatedBlocks

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/PPL/LogWindow/Whp.lean`, namespace `PPL.Superseded.LogWindow`: `theorem1_countP_four_union_le`, `theorem1_pad_phase_bound`, `theorem1_five_event_constants`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
# Theorem 1 WHP composition skeleton

Current-main audit.

The four requested count bounds have coefficients

  L16 = 12,  L5(i) = 8,  L17 = 1,  L18 = 1.

Their sum is 22.  The arithmetic therefore has ample room under the frozen
Theorem-1 numerator 64.

The protocol-specific four-event composition is nevertheless not closed on
current main.  Lemma 5(i) reaches midPhysicalB at a prefix, whereas the
full-P_PL to P_PL-prime coupling used by L17/L18 requires the subsequent
Construct-only event counted by Lemma 5(ii).  Lemma5iiWordBound has coefficient
4.  There is no theorem charging that fifth bad event to one of the four
requested counts.

The missing protocol-specific event splice is named explicitly below as
Theorem1FourPhaseSplice.  Everything after that splice is finite-list counting
and Nat arithmetic and is proved here.
-/

/-! ## 1. Prefix hitting is monotone under appending a suffix -/

theorem theorem1ReachesSPL_append_of_left
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre suf : DetSchedule n)
    (hpre :
      theorem1ReachesSPL ring C pre = true) :
    theorem1ReachesSPL ring C (pre ++ suf) = true := by
  induction pre generalizing C with
  | nil =>
      cases suf with
      | nil =>
          simpa [theorem1ReachesSPL] using hpre
      | cons e rest =>
          have hhere :
              decide (SPL ring C) = true := by
            simpa [theorem1ReachesSPL] using hpre
          simp [theorem1ReachesSPL, hhere]
  | cons e rest ih =>
      simp only
        [List.cons_append, theorem1ReachesSPL]
        at hpre ⊢
      cases hhere : decide (SPL ring C) with
      | false =>
          simp only [hhere, Bool.false_or] at hpre ⊢
          exact
            ih
              (C :=
                PopulationProtocol.step
                  (protocol psi kappa) ring C e)
              hpre
      | true =>
          simp [hhere]

/-! ## 2. L16 success supplies the L5(i) start condition -/

theorem theorem1_foldlOr_true
    (xs : List Bool) :
    xs.foldl (fun a b => a || b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      simp only [List.foldl_cons]
      simpa using ih

theorem theorem1_foldlOr_true_of_mem
    (xs : List Bool)
    (hmem : true ∈ xs) :
    xs.foldl (fun a b => a || b) false = true := by
  induction xs with
  | nil =>
      simp at hmem
  | cons b xs ih =>
      rcases List.mem_cons.mp hmem with hb | ht
      · subst b
        simp only [List.foldl_cons, Bool.false_or]
        exact theorem1_foldlOr_true xs
      · cases b with
        | false =>
            simp only [List.foldl_cons, Bool.false_or]
            exact ih ht
        | true =>
            simp only [List.foldl_cons, Bool.false_or]
            exact theorem1_foldlOr_true xs

theorem theorem1_leaderPresent_of_exists
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : ∃ i : Fin n, (C i).leader = true) :
    PPL.Probability.leaderPresent C = true := by
  rcases h with ⟨i, hi⟩
  unfold PPL.Probability.leaderPresent
  apply theorem1_foldlOr_true_of_mem
  rw [List.mem_ofFn]
  exact ⟨i, hi⟩

/--
CPB is closed under the full P_PL transition, and its first conjunct contains
a live leader.  Hence every configuration reachable from a CPB start still has
a leader, exactly the neverLeaderless premise consumed by Lemma 5(i).
-/
theorem theorem1CPB_neverLeaderless
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C) :
    PPL.Modes.Lemma5.neverLeaderless ring C := by
  unfold PPL.Modes.Lemma5.neverLeaderless
  intro D hreach
  have hclosed :
      PopulationProtocol.ClosedPred
        (protocol psi kappa) ring (CPB ring) := by
    intro A hA B hstep
    rcases hstep with ⟨e, hB⟩
    subst B
    exact
      PPL.Safety.PeacefulProps.cpb_step_closed_proved
        hn3 hpsi ring A e hA
  have hD : CPB ring D :=
    PopulationProtocol.ClosedPred.reachable
      hclosed hCPB hreach
  unfold CPB CPBCore at hD
  exact theorem1_leaderPresent_of_exists D hD.1

/-! ## 3. Exact schedule product and generic union algebra -/

theorem theorem1_allSchedules_add
    (n a b : Nat) :
    allSchedules n (a + b) =
      (allSchedules n a).flatMap
        (fun pre =>
          (allSchedules n b).map
            (fun suf => pre ++ suf)) :=
  PPLLSchedulerBlocks.allSchedules_add n a b

end PPL

#print axioms PPL.theorem1ReachesSPL_append_of_left
#print axioms PPL.theorem1CPB_neverLeaderless
#print axioms PPL.theorem1_allSchedules_add

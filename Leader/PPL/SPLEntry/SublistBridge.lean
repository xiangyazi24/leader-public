import Leader.PPL.SPLEntry.ForcingWord

/-!
# Lemma 18 ordered-subsequence bridge

The source's Definition 2 uses ordered subsequences, not contiguous blocks.
The exact-word theorem in L18.lean therefore needs an insertion/frame bridge.

This file reduces that bridge to two one-interaction Props:
* L18CPBUniqueStepRow: arbitrary P_PL-prime interaction preserves
  C_PB and the identity of the unique root leader.
* L18SuffixForcingStepRow: for an actual suffix todo of the frozen
  Lemma-18 word, an arbitrary inserted interaction does not destroy the
  exact-suffix forcing property before S_PL is hit.

No scheduler-probability statement remains in either row. The selected
letter advances from e :: todo to todo by unfolding l18HitsSPL.
-/

namespace PPL.Convergence.L18Bridge

set_option autoImplicit false
set_option Elab.async false

open PPL
open PPL.Probability
open PPL.Convergence.L18

/-- One arbitrary P_PL-prime interaction preserves CPB and the root leader. -/
def L18CPBUniqueStepRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n),
    CPB ring C ->
    L18UniqueLeaderAt C root ->
    CPB ring (pprimeStep ring C e) ∧
      L18UniqueLeaderAt (pprimeStep ring C e) root

/--
Backward phase potential for one inserted letter.
The decomposition l18Word = done ++ todo restricts todo to an actual suffix.
-/
def L18SuffixForcingStepRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n)
    (done todo : DetSchedule n),
    CPB ring C ->
    L18UniqueLeaderAt C root ->
    decide (SPLAt ring root C) = false ->
    l18Word ring root psi = done ++ todo ->
    l18HitsSPL ring root C todo = true ->
    l18HitsSPL ring root (pprimeStep ring C e) todo = true

/-- Exact endpoint membership implies that the first-hit Boolean is true. -/
theorem l18HitsSPL_of_endpoint
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (word : DetSchedule n)
    (hend :
      SPLAt ring root
        (runPPrime ring C word)) :
    l18HitsSPL ring root C word = true := by
  induction word generalizing C with
  | nil =>
      simp only [runPPrime] at hend
      simp [l18HitsSPL, hend]
  | cons e rest ih =>
      cases hs : decide (SPLAt ring root C) with
      | false =>
          have hend' :
              SPLAt ring root
                (runPPrime ring
                  (pprimeStep ring C e) rest) := by
            simpa only [runPPrime] using hend
          have htail :=
            ih (C := pprimeStep ring C e) hend'
          simpa [l18HitsSPL, hs] using htail
      | true =>
          simp [l18HitsSPL, hs]

/--
Pure List.Sublist bridge.
In the cons case the scheduler head is an insertion and hMono preserves
the same remaining suffix. In the cons_cons case the scheduler head is the
selected next letter, so unfolding l18HitsSPL consumes it definitionally.
-/
theorem l18HitsSPL_of_sublist_rows
    (hState : L18CPBUniqueStepRow)
    (hMono : L18SuffixForcingStepRow)
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (done word schedule : DetSchedule n)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root)
    (hdecomp :
      l18Word ring root psi = done ++ word)
    (hforce :
      l18HitsSPL ring root C word = true)
    (hsub : word.Sublist schedule) :
    l18HitsSPL ring root C schedule = true := by
  induction hsub generalizing C done with
  | slnil =>
      exact hforce
  | @cons l1 l2 e h ih =>
      cases hs : decide (SPLAt ring root C) with
      | false =>
          have hstate :=
            hState hn3 hpsi ring root C e hCPB hUnique
          have hforce' :=
            hMono hn3 hpsi ring root C e done l1
              hCPB hUnique hs hdecomp hforce
          have htail :
              l18HitsSPL ring root
                (pprimeStep ring C e) l2 = true :=
            ih
              (C := pprimeStep ring C e)
              (done := done)
              hstate.1 hstate.2
              hdecomp hforce'
          simpa [l18HitsSPL, hs] using htail
      | true =>
          simp [l18HitsSPL, hs]
  | @cons_cons l1 l2 e h ih =>
      cases hs : decide (SPLAt ring root C) with
      | false =>
          have hstate :=
            hState hn3 hpsi ring root C e hCPB hUnique
          have hforce' :
              l18HitsSPL ring root
                (pprimeStep ring C e) l1 = true := by
            simpa [l18HitsSPL, hs] using hforce
          have hdecomp' :
              l18Word ring root psi =
                (done ++ [e]) ++ l1 := by
            simpa [List.append_assoc] using hdecomp
          have htail :
              l18HitsSPL ring root
                (pprimeStep ring C e) l2 = true :=
            ih
              (C := pprimeStep ring C e)
              (done := done ++ [e])
              hstate.1 hstate.2
              hdecomp' hforce'
          simpa [l18HitsSPL, hs] using htail
      | true =>
          simp [l18HitsSPL, hs]

/--
The five existing phase contracts seed the exact contiguous word.
The two new rows are precisely the additional bridge to the source-correct
ordered-subsequence occurrence consumed by the fixed-word count.
-/
theorem l18ForcingWordReachesSPL_of_rows
    (hRoot : L18RootResetPhase)
    (hDist : L18DistanceSweepPhase)
    (hLast : L18LastSweepPhase)
    (hRisk : L18RiskyFlushPhase)
    (hBuild : L18Lemma4BuildPhase)
    (hState : L18CPBUniqueStepRow)
    (hMono : L18SuffixForcingStepRow) :
    L18ForcingWordReachesSPL := by
  unfold L18ForcingWordReachesSPL
  intro hlemma4
  intro n psi kappa
  intro hn3 hpsi ring root C schedule
  intro hCPB hUnique hsub
  have hend :
      SPLAt ring root
        (runPPrime ring C
          (l18Word ring root psi)) :=
    l18_exactWord_reachesSPL_of_phases
      hRoot hDist hLast hRisk hBuild hlemma4
      hn3 hpsi ring root C hCPB hUnique
  have hseed :
      l18HitsSPL ring root C
        (l18Word ring root psi) = true :=
    l18HitsSPL_of_endpoint
      ring root C (l18Word ring root psi) hend
  exact
    l18HitsSPL_of_sublist_rows
      hState hMono
      hn3 hpsi ring root C
      [] (l18Word ring root psi) schedule
      hCPB hUnique
      (by simp)
      hseed hsub

#print axioms PPL.Convergence.L18Bridge.l18HitsSPL_of_endpoint
#print axioms PPL.Convergence.L18Bridge.l18HitsSPL_of_sublist_rows
#print axioms PPL.Convergence.L18Bridge.l18ForcingWordReachesSPL_of_rows

end PPL.Convergence.L18Bridge

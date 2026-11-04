import Leader.PPL.SPLEntry.GappedPhases
import Leader.PPL.SPLEntry.RiskyFlushScoped
import Leader.PPL.SPLEntry.SublistBridge
import Leader.PPL.SPLEntry.CountScoped


namespace PPL.Convergence.L18


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL


/-!
# Corrected gapped Lemma-18 composition


The Root / Distance / Last gapped phases come from L18GappedPhases.
The two new contracts below have the same ordered-subsequence shape and add
the explicit first-hit escape needed for arbitrary inserted letters.


Risky remains scoped to psi < n, exactly as in L18RiskyFlushScoped.
-/


/--
Gapped scoped Risky phase.


The phase word only has to occur as an ordered subsequence of schedule.
If an inserted or selected letter hits SPL anywhere inside schedule, the
first disjunct wins. Otherwise the endpoint carries the invariant required
by the Build phase.
-/
def L18GappedRiskyFlushPhaseScoped : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    CDLAt ring root C →
    (l18RiskyFlushWord ring root psi).Sublist schedule →
    l18HitsSPL ring root C schedule = true ∨
      (let D := runPPrime ring C schedule
       CDLAt ring root D ∧
         L18NoRiskyAt ring root D)


/--
Gapped Build phase.


The Build word only has to occur as an ordered subsequence. The escape
disjunct records a first hit inside the chunk; otherwise the endpoint itself
is rooted SPL.
-/
def L18GappedLemma4BuildPhase : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hlemma4 : PPL.lemma4_deterministic_core),
    CDLAt ring root C →
    L18NoRiskyAt ring root C →
    (l18BuildWord ring root psi).Sublist schedule →
    l18HitsSPL ring root C schedule = true ∨
      SPLAt ring root
        (runPPrime ring C schedule)


/-! ## Pure List.Sublist scheduling helpers -/


/--
Split an ordered occurrence of a ++ b at some scheduler cut.
The two target chunks cover the whole scheduler word.
-/
private theorem l18GappedSublistAppendSplit
    {A : Type}
    (a b w : List A)
    (hsub : (a ++ b).Sublist w) :
    ∃ u v : List A,
      w = u ++ v ∧
        a.Sublist u ∧
        b.Sublist v := by
  induction w generalizing a with
  | nil =>
      cases a with
      | nil =>
          refine ⟨[], [], rfl, List.Sublist.slnil, ?_⟩
          simpa using hsub
      | cons x xs =>
          have hlen := hsub.length_le
          simp at hlen
  | cons y ys ih =>
      cases a with
      | nil =>
          refine ⟨[], y :: ys, rfl, List.Sublist.slnil, ?_⟩
          simpa using hsub
      | cons x xs =>
          have hs :
              (x :: (xs ++ b)).Sublist (y :: ys) := by
            simpa only [List.cons_append] using hsub
          rcases List.sublist_cons_iff.mp hs with
            hskip | ⟨tail, heq, htake⟩
          · rcases ih (a := x :: xs) hskip with
              ⟨u, v, hw, hu, hv⟩
            refine ⟨y :: u, v, ?_, ?_, hv⟩
            · simp only [List.cons_append, hw]
            · exact List.Sublist.cons y hu
          · cases heq
            rcases ih (a := xs) htake with
              ⟨u, v, hw, hu, hv⟩
            refine ⟨y :: u, v, ?_, ?_, hv⟩
            · simp only [List.cons_append, hw]
            · exact List.Sublist.cons_cons y hu


/-! ## First-hit append transport -/


/--
A first hit in a prefix remains a first hit after any suffix.
-/
private theorem l18GappedHitsAppendLeft
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (u v : DetSchedule n)
    (hleft :
      l18HitsSPL ring root C u = true) :
    l18HitsSPL ring root C (u ++ v) = true := by
  induction u generalizing C with
  | nil =>
      cases v with
      | nil =>
          simpa using hleft
      | cons e es =>
          have hs :
              decide (SPLAt ring root C) = true := by
            simpa [l18HitsSPL] using hleft
          simp [l18HitsSPL, hs]
  | cons e es ih =>
      cases hs : decide (SPLAt ring root C) with
      | false =>
          have htail :
              l18HitsSPL ring root
                  (pprimeStep ring C e) es =
                true := by
            simpa [l18HitsSPL, hs] using hleft
          have hout :=
            ih (C := pprimeStep ring C e) htail
          simpa [l18HitsSPL, hs] using hout
      | true =>
          simp [l18HitsSPL, hs]


/--
A first hit in the suffix, started from the prefix endpoint, is a first hit
of the concatenated word.
-/
private theorem l18GappedHitsAppendRight
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (u v : DetSchedule n)
    (hright :
      l18HitsSPL ring root
          (runPPrime ring C u) v =
        true) :
    l18HitsSPL ring root C (u ++ v) = true := by
  induction u generalizing C with
  | nil =>
      simpa [runPPrime] using hright
  | cons e es ih =>
      cases hs : decide (SPLAt ring root C) with
      | false =>
          have htail :
              l18HitsSPL ring root
                  (runPPrime ring
                    (pprimeStep ring C e) es) v =
                true := by
            simpa [runPPrime] using hright
          have hout :=
            ih (C := pprimeStep ring C e) htail
          simpa [l18HitsSPL, hs] using hout
      | true =>
          simp [l18HitsSPL, hs]


/-! ## Five-phase ordered-subsequence composition -/


/--
Corrected Lemma-18 ordered-subsequence theorem.


The full scheduler word is cut into five chunks, one for each frozen phase.
Every chunk is allowed arbitrary inserted letters. A first hit in any chunk
is lifted through the remaining suffix; otherwise the phase endpoint invariant
is threaded to the next chunk.
-/
theorem l18ForcingWordReachesSPL_of_gappedPhases
    (hRoot : L18GappedRootResetPhase)
    (hDist : L18GappedDistanceSweepPhase)
    (hLast : L18GappedLastSweepPhase)
    (hRisk : L18GappedRiskyFlushPhaseScoped)
    (hBuild : L18GappedLemma4BuildPhase)
    (hlemma4 : PPL.lemma4_deterministic_core)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root)
    (w : DetSchedule n)
    (hsub :
      (l18Word ring root psi).Sublist w) :
    l18HitsSPL ring root C w = true := by


  have hfull :
      (l18RootResetWord ring root ++
        (l18DistanceWord ring root ++
          (l18LastWord ring root ++
            (l18RiskyFlushWord ring root psi ++
              l18BuildWord ring root psi)))).Sublist w := by
    simpa [l18Word] using hsub


  rcases
      l18GappedSublistAppendSplit
        (l18RootResetWord ring root)
        (l18DistanceWord ring root ++
          (l18LastWord ring root ++
            (l18RiskyFlushWord ring root psi ++
              l18BuildWord ring root psi)))
        w hfull with
    ⟨w1, rest1, hw1, hsub1, hrest1⟩


  rcases
      l18GappedSublistAppendSplit
        (l18DistanceWord ring root)
        (l18LastWord ring root ++
          (l18RiskyFlushWord ring root psi ++
            l18BuildWord ring root psi))
        rest1 hrest1 with
    ⟨w2, rest2, hw2, hsub2, hrest2⟩


  rcases
      l18GappedSublistAppendSplit
        (l18LastWord ring root)
        (l18RiskyFlushWord ring root psi ++
          l18BuildWord ring root psi)
        rest2 hrest2 with
    ⟨w3, rest3, hw3, hsub3, hrest3⟩


  rcases
      l18GappedSublistAppendSplit
        (l18RiskyFlushWord ring root psi)
        (l18BuildWord ring root psi)
        rest3 hrest3 with
    ⟨w4, w5, hw4, hsub4, hsub5⟩


  have hRootOut :=
    hRoot
      hn3 hpsi ring root C w1
      hCPB hUnique hsub1


  rcases hRootOut with hhit1 | hpost1
  · have hall :=
      l18GappedHitsAppendLeft
        ring root C w1
        (w2 ++ (w3 ++ (w4 ++ w5)))
        hhit1
    rw [hw1, hw2, hw3, hw4]
    exact hall


  · dsimp only at hpost1


    let C1 : Config n psi kappa :=
      runPPrime ring C w1


    have hCPB1 : CPB ring C1 := by
      simpa [C1] using hpost1.1


    have hUnique1 :
        L18UniqueLeaderAt C1 root := by
      simpa [C1] using hpost1.2.1


    have hRootDist :
        (C1 root).dist.val = 0 := by
      simpa [C1] using hpost1.2.2


    have hDistOut :=
      hDist
        hn3 hpsi ring root C1 w2
        hCPB1 hUnique1 hRootDist hsub2


    rcases hDistOut with hhit2 | hpost2
    · have htail2 :=
        l18GappedHitsAppendLeft
          ring root C1 w2
          (w3 ++ (w4 ++ w5))
          hhit2
      have hall2 :=
        l18GappedHitsAppendRight
          ring root C w1
          (w2 ++ (w3 ++ (w4 ++ w5)))
          (by simpa [C1] using htail2)
      rw [hw1, hw2, hw3, hw4]
      exact hall2


    · dsimp only at hpost2


      let C2 : Config n psi kappa :=
        runPPrime ring C1 w2


      have hCPB2 : CPB ring C2 := by
        simpa [C2] using hpost2.1


      have hUnique2 :
          L18UniqueLeaderAt C2 root := by
        simpa [C2] using hpost2.2.1


      have hDist2 :
          L18CanonicalDistanceAt ring root C2 := by
        simpa [C2] using hpost2.2.2


      have hLastOut :=
        hLast
          hn3 hpsi ring root C2 w3
          hCPB2 hUnique2 hDist2 hsub3


      rcases hLastOut with hhit3 | hpost3
      · have htail3 :=
          l18GappedHitsAppendLeft
            ring root C2 w3
            (w4 ++ w5)
            hhit3
        have hafter2 :=
          l18GappedHitsAppendRight
            ring root C1 w2
            (w3 ++ (w4 ++ w5))
            (by simpa [C2] using htail3)
        have hall3 :=
          l18GappedHitsAppendRight
            ring root C w1
            (w2 ++ (w3 ++ (w4 ++ w5)))
            (by simpa [C1] using hafter2)
        rw [hw1, hw2, hw3, hw4]
        exact hall3


      · let C3 : Config n psi kappa :=
          runPPrime ring C2 w3


        have hCDL3 :
            CDLAt ring root C3 := by
          simpa [C3] using hpost3


        have hRiskOut :=
          hRisk
            hn3 hpsi hlt
            ring root C3 w4
            hCDL3 hsub4


        rcases hRiskOut with hhit4 | hpost4
        · have htail4 :=
            l18GappedHitsAppendLeft
              ring root C3 w4 w5 hhit4
          have hafter3 :=
            l18GappedHitsAppendRight
              ring root C2 w3
              (w4 ++ w5)
              (by simpa [C3] using htail4)
          have hafter2 :=
            l18GappedHitsAppendRight
              ring root C1 w2
              (w3 ++ (w4 ++ w5))
              (by simpa [C2] using hafter3)
          have hall4 :=
            l18GappedHitsAppendRight
              ring root C w1
              (w2 ++ (w3 ++ (w4 ++ w5)))
              (by simpa [C1] using hafter2)
          rw [hw1, hw2, hw3, hw4]
          exact hall4


        · dsimp only at hpost4


          let C4 : Config n psi kappa :=
            runPPrime ring C3 w4


          have hCDL4 :
              CDLAt ring root C4 := by
            simpa [C4] using hpost4.1


          have hNoRisk4 :
              L18NoRiskyAt ring root C4 := by
            simpa [C4] using hpost4.2


          have hBuildOut :=
            hBuild
              hn3 hpsi ring root C4 w5
              hlemma4
              hCDL4 hNoRisk4 hsub5


          have hhit5 :
              l18HitsSPL ring root C4 w5 = true := by
            rcases hBuildOut with hhit | hend
            · exact hhit
            · exact
                PPL.Convergence.L18Bridge.l18HitsSPL_of_endpoint
                  ring root C4 w5 hend


          have hafter4 :=
            l18GappedHitsAppendRight
              ring root C3 w4 w5
              (by simpa [C4] using hhit5)


          have hafter3 :=
            l18GappedHitsAppendRight
              ring root C2 w3
              (w4 ++ w5)
              (by simpa [C3] using hafter4)


          have hafter2 :=
            l18GappedHitsAppendRight
              ring root C1 w2
              (w3 ++ (w4 ++ w5))
              (by simpa [C2] using hafter3)


          have hall5 :=
            l18GappedHitsAppendRight
              ring root C w1
              (w2 ++ (w3 ++ (w4 ++ w5)))
              (by simpa [C1] using hafter2)


          rw [hw1, hw2, hw3, hw4]
          exact hall5


/-! ## Corrected forcing interface -/


theorem l18ForcingWordReachesSPLScoped_of_gappedPhases
    (hRoot : L18GappedRootResetPhase)
    (hDist : L18GappedDistanceSweepPhase)
    (hLast : L18GappedLastSweepPhase)
    (hRisk : L18GappedRiskyFlushPhaseScoped)
    (hBuild : L18GappedLemma4BuildPhase) :
    L18ForcingWordReachesSPLScoped := by
  unfold L18ForcingWordReachesSPLScoped
  intro hlemma4
  intro n psi kappa
  intro hn3 hpsi hlt
  intro ring root C schedule
  intro hCPB hUnique hsub
  exact
    l18ForcingWordReachesSPL_of_gappedPhases
      hRoot hDist hLast hRisk hBuild hlemma4
      hn3 hpsi hlt
      ring root C hCPB hUnique
      schedule hsub


end PPL.Convergence.L18


#print axioms PPL.Convergence.L18.l18ForcingWordReachesSPL_of_gappedPhases
#print axioms PPL.Convergence.L18.l18ForcingWordReachesSPLScoped_of_gappedPhases

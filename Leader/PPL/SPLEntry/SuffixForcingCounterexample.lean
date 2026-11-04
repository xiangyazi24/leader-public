import Leader.PPL.SPLEntry.SublistBridge


namespace PPL.Convergence.L18Bridge


set_option autoImplicit false
set_option Elab.async false


open PPL
open PPL.Probability
open PPL.Convergence.L18




/-! ## Closed counterexample -/


def q19894Ring : DirectedRing 4 :=
  ⟨by omega⟩


def q19894Root : Fin 4 := 0


def q19894Edge0 : Fin 4 := 0


def q19894Edge1 : Fin 4 := 1


def q19894Cell
    (leader last : Bool) (dist : Fin 4) :
    State 2 0 where
  leader := leader
  id := false
  dist := dist
  last := last
  tokenB := none
  tokenW := none
  mode := false
  clock := 0
  signalR := 0
  hits := 0
  bullet := 0
  shield := false
  signalB := false


def q19894Config : Config 4 2 0 :=
  fun i =>
    if i = (0 : Fin 4) then
      q19894Cell true false 0
    else if i = (1 : Fin 4) then
      q19894Cell false true 1
    else if i = (2 : Fin 4) then
      q19894Cell false true 2
    else
      q19894Cell false true 3


def q19894Done : DetSchedule 4 :=
  [3, 0, 1, 2, 3, 2, 1, 0, 0, 1, 0]


def q19894Todo : DetSchedule 4 :=
  [1]


theorem q19894FinFourCases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hv :
      i.val = 0 ∨ i.val = 1 ∨
        i.val = 2 ∨ i.val = 3 := by
    omega
  rcases hv with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))


theorem q19894BulletZero (i : Fin 4) :
    (q19894Config i).bullet = (0 : Fin 3) := by
  rcases q19894FinFourCases i with h | h | h | h
  · subst i
    simp [q19894Config, q19894Cell]
  · subst i
    simp [q19894Config, q19894Cell]
  · subst i
    simp [q19894Config, q19894Cell]
  · subst i
    simp [q19894Config, q19894Cell]


theorem q19894CPB :
    CPB q19894Ring q19894Config := by
  unfold PPL.CPB PPL.CPBCore
  refine ⟨⟨0, ?_⟩, ?_⟩
  · simp [q19894Config, q19894Cell]
  · intro i hi
    change (q19894Config i).bullet = (2 : Fin 3) at hi
    have h02 : (0 : Fin 3) = (2 : Fin 3) :=
      (q19894BulletZero i).symm.trans hi
    have hv : (0 : Nat) = 2 :=
      congrArg Fin.val h02
    omega


theorem q19894Unique :
    L18UniqueLeaderAt q19894Config q19894Root := by
  intro i
  rcases q19894FinFourCases i with h | h | h | h
  · subst i
    simp [q19894Root, q19894Config, q19894Cell]
  · subst i
    simp [q19894Root, q19894Config, q19894Cell]
  · subst i
    simp [q19894Root, q19894Config, q19894Cell]
  · subst i
    simp [q19894Root, q19894Config, q19894Cell]


theorem q19894WordSplit :
    l18Word q19894Ring q19894Root 2 =
      q19894Done ++ q19894Todo := by
  decide +kernel


theorem q19894InitialNotSPLBool :
    decide
      (SPLAt q19894Ring q19894Root q19894Config) =
        false := by
  decide +kernel


theorem q19894HitsBefore :
    l18HitsSPL
        q19894Ring q19894Root
        q19894Config q19894Todo =
      true := by
  decide +kernel


theorem q19894HitsAfter :
    l18HitsSPL
        q19894Ring q19894Root
        (pprimeStep
          q19894Ring q19894Config q19894Edge0)
        q19894Todo =
      false := by
  decide +kernel


theorem l18SuffixForcingStepRow_false :
    ¬ L18SuffixForcingStepRow := by
  intro hrow
  unfold L18SuffixForcingStepRow at hrow
  have hbad :=
    hrow
      (n := 4) (psi := 2) (kappa := 0)
      (by omega) (by omega)
      q19894Ring q19894Root
      q19894Config q19894Edge0
      q19894Done q19894Todo
      q19894CPB q19894Unique
      q19894InitialNotSPLBool
      q19894WordSplit
      q19894HitsBefore
  rw [q19894HitsAfter] at hbad
  cases hbad




/-! ## Corrected interfaces -/


def L18ProperSegments (n psi : Nat) : Prop :=
  2 ≤ segmentCount n psi


def L18PrefixReachable
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (done : DetSchedule n)
    (C : Config n psi kappa) : Prop :=
  ∃ (C0 : Config n psi kappa) (pref : DetSchedule n),
    CPB ring C0 ∧
      L18UniqueLeaderAt C0 root ∧
      done.Sublist pref ∧
      runPPrime ring C0 pref = C ∧
      l18HitsSPL ring root C0 pref = false


def L18SuffixForcingReachableStepRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n)
    (done todo : DetSchedule n),
    L18ProperSegments n psi →
    CPB ring C →
    L18UniqueLeaderAt C root →
    L18PrefixReachable ring root done C →
    l18Word ring root psi = done ++ todo →
    l18HitsSPL ring root C todo = true →
    decide (SPLAt ring root C) = false →
    decide (SPLAt ring root (pprimeStep ring C e)) = false →
    l18HitsSPL ring root
      (pprimeStep ring C e) todo = true


def L18ForcingWordReachesSPLProper : Prop :=
  PPL.lemma4_deterministic_core →
    ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
      (ring : DirectedRing n) (root : Fin n)
      (C : Config n psi kappa)
      (schedule : DetSchedule n),
      L18ProperSegments n psi →
      CPB ring C →
      L18UniqueLeaderAt C root →
      (l18Word ring root psi).Sublist schedule →
      l18HitsSPL ring root C schedule = true




/-! ## Small first-hit and reachability helpers -/


theorem l18HitsSPL_of_current
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (h : decide (SPLAt ring root C) = true) :
    l18HitsSPL ring root C word = true := by
  cases word <;>
    simp [l18HitsSPL, h]


theorem l18HitsSPL_append_singleton_false
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (pref : DetSchedule n) (e : Fin n)
    (hprefix :
      l18HitsSPL ring root C pref = false)
    (hnext :
      decide
          (SPLAt ring root
            (pprimeStep ring
              (runPPrime ring C pref) e)) =
        false) :
    l18HitsSPL ring root C (pref ++ [e]) = false := by
  induction pref generalizing C with
  | nil =>
      cases hs : decide (SPLAt ring root C) with
      | false =>
          have hn := of_decide_eq_false hnext
          simpa [l18HitsSPL, runPPrime, hs] using hn
      | true =>
          simp [l18HitsSPL, hs] at hprefix
  | cons a rest ih =>
      cases hs : decide (SPLAt ring root C) with
      | false =>
          have htail :
              l18HitsSPL ring root
                  (pprimeStep ring C a) rest =
                false := by
            simpa [l18HitsSPL, hs] using hprefix
          have hnext' :
              decide
                  (SPLAt ring root
                    (pprimeStep ring
                      (runPPrime ring
                        (pprimeStep ring C a) rest)
                      e)) =
                false := by
            apply decide_eq_false
            have h0 := of_decide_eq_false hnext
            simpa only [runPPrime] using h0
          have htailExtended :=
            ih
              (C := pprimeStep ring C a)
              htail hnext'
          simpa [l18HitsSPL, hs] using htailExtended
      | true =>
          simp [l18HitsSPL, hs] at hprefix


theorem l18PrefixReachable_insert
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n)
    (done : DetSchedule n)
    (hreach :
      L18PrefixReachable ring root done C)
    (hnext :
      decide
          (SPLAt ring root
            (pprimeStep ring C e)) =
        false) :
    L18PrefixReachable ring root done
      (pprimeStep ring C e) := by
  unfold L18PrefixReachable at hreach ⊢
  rcases hreach with
    ⟨C0, pref, hCPB0, hUnique0,
      hsub, hrun, hhits⟩
  refine
    ⟨C0, pref ++ [e],
      hCPB0, hUnique0, ?_, ?_, ?_⟩
  · exact
      hsub.trans
        (List.sublist_append_left pref [e])
  · simpa [runPPrime_append, hrun, runPPrime]
  · have hnext' :
        decide
            (SPLAt ring root
              (pprimeStep ring
                (runPPrime ring C0 pref) e)) =
          false := by
      simpa [hrun] using hnext
    exact
      l18HitsSPL_append_singleton_false
        ring root C0 pref e hhits hnext'


theorem l18PrefixReachable_selected
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n)
    (done : DetSchedule n)
    (hreach :
      L18PrefixReachable ring root done C)
    (hnext :
      decide
          (SPLAt ring root
            (pprimeStep ring C e)) =
        false) :
    L18PrefixReachable ring root
      (done ++ [e])
      (pprimeStep ring C e) := by
  unfold L18PrefixReachable at hreach ⊢
  rcases hreach with
    ⟨C0, pref, hCPB0, hUnique0,
      hsub, hrun, hhits⟩
  refine
    ⟨C0, pref ++ [e],
      hCPB0, hUnique0, ?_, ?_, ?_⟩
  · exact List.Sublist.append_right hsub [e]
  · simpa [runPPrime_append, hrun, runPPrime]
  · have hnext' :
        decide
            (SPLAt ring root
              (pprimeStep ring
                (runPPrime ring C0 pref) e)) =
          false := by
      simpa [hrun] using hnext
    exact
      l18HitsSPL_append_singleton_false
        ring root C0 pref e hhits hnext'




/-! ## Corrected sublist consumer -/


theorem l18HitsSPL_of_sublist_reachableRows
    (hState : L18CPBUniqueStepRow)
    (hMono : L18SuffixForcingReachableStepRow)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n)
    (hProper : L18ProperSegments n psi)
    (C : Config n psi kappa)
    (done word schedule : DetSchedule n)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root)
    (hReach :
      L18PrefixReachable ring root done C)
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
      | true =>
          simp [l18HitsSPL, hs]
      | false =>
          have hstate :=
            hState hn3 hpsi
              ring root C e hCPB hUnique
          cases hsNext :
              decide
                (SPLAt ring root
                  (pprimeStep ring C e)) with
          | true =>
              have htail :
                  l18HitsSPL ring root
                      (pprimeStep ring C e) l2 =
                    true :=
                l18HitsSPL_of_current
                  ring root
                  (pprimeStep ring C e)
                  l2 hsNext
              simpa [l18HitsSPL, hs] using htail
          | false =>
              have hforce' :=
                hMono
                  hn3 hpsi ring root
                  C e done l1
                  hProper hCPB hUnique hReach
                  hdecomp hforce hs hsNext
              have hReach' :
                  L18PrefixReachable
                    ring root done
                    (pprimeStep ring C e) :=
                l18PrefixReachable_insert
                  ring root C e done
                  hReach hsNext
              have htail :
                  l18HitsSPL ring root
                      (pprimeStep ring C e) l2 =
                    true :=
                ih
                  (C := pprimeStep ring C e)
                  (done := done)
                  hstate.1 hstate.2
                  hReach' hdecomp hforce'
              simpa [l18HitsSPL, hs] using htail
  | @cons_cons l1 l2 e h ih =>
      cases hs : decide (SPLAt ring root C) with
      | true =>
          simp [l18HitsSPL, hs]
      | false =>
          have hstate :=
            hState hn3 hpsi
              ring root C e hCPB hUnique
          cases hsNext :
              decide
                (SPLAt ring root
                  (pprimeStep ring C e)) with
          | true =>
              have htail :
                  l18HitsSPL ring root
                      (pprimeStep ring C e) l2 =
                    true :=
                l18HitsSPL_of_current
                  ring root
                  (pprimeStep ring C e)
                  l2 hsNext
              simpa [l18HitsSPL, hs] using htail
          | false =>
              have hforce' :
                  l18HitsSPL ring root
                      (pprimeStep ring C e) l1 =
                    true := by
                simpa [l18HitsSPL, hs] using hforce
              have hdecomp' :
                  l18Word ring root psi =
                    (done ++ [e]) ++ l1 := by
                simpa [List.append_assoc] using hdecomp
              have hReach' :
                  L18PrefixReachable
                    ring root (done ++ [e])
                    (pprimeStep ring C e) :=
                l18PrefixReachable_selected
                  ring root C e done
                  hReach hsNext
              have htail :
                  l18HitsSPL ring root
                      (pprimeStep ring C e) l2 =
                    true :=
                ih
                  (C := pprimeStep ring C e)
                  (done := done ++ [e])
                  hstate.1 hstate.2
                  hReach' hdecomp' hforce'
              simpa [l18HitsSPL, hs] using htail


theorem l18ForcingWordReachesSPL_of_reachableRows
    (hRoot : L18RootResetPhase)
    (hDist : L18DistanceSweepPhase)
    (hLast : L18LastSweepPhase)
    (hRisk : L18RiskyFlushPhase)
    (hBuild : L18Lemma4BuildPhase)
    (hState : L18CPBUniqueStepRow)
    (hMono : L18SuffixForcingReachableStepRow) :
    L18ForcingWordReachesSPLProper := by
  unfold L18ForcingWordReachesSPLProper
  intro hlemma4
  intro n psi kappa
  intro hn3 hpsi ring root C schedule
  intro hProper hCPB hUnique hsub
  cases hs : decide (SPLAt ring root C) with
  | true =>
      exact
        l18HitsSPL_of_current
          ring root C schedule hs
  | false =>
      have hend :
          SPLAt ring root
            (runPPrime ring C
              (l18Word ring root psi)) :=
        l18_exactWord_reachesSPL_of_phases
          hRoot hDist hLast hRisk hBuild
          hlemma4
          hn3 hpsi ring root C
          hCPB hUnique
      have hseed :
          l18HitsSPL ring root C
              (l18Word ring root psi) =
            true :=
        l18HitsSPL_of_endpoint
          ring root C
          (l18Word ring root psi)
          hend
      have hReach :
          L18PrefixReachable ring root [] C := by
        unfold L18PrefixReachable
        exact
          ⟨C, [], hCPB, hUnique,
            by simp, rfl,
            by simpa [l18HitsSPL] using hs⟩
      exact
        l18HitsSPL_of_sublist_reachableRows
          hState hMono
          hn3 hpsi ring root hProper
          C [] (l18Word ring root psi) schedule
          hCPB hUnique hReach
          (by simp) hseed hsub




end PPL.Convergence.L18Bridge

#print axioms PPL.Convergence.L18Bridge.q19894FinFourCases
#print axioms PPL.Convergence.L18Bridge.q19894BulletZero
#print axioms PPL.Convergence.L18Bridge.q19894CPB
#print axioms PPL.Convergence.L18Bridge.q19894Unique
#print axioms PPL.Convergence.L18Bridge.q19894WordSplit
#print axioms PPL.Convergence.L18Bridge.q19894InitialNotSPLBool
#print axioms PPL.Convergence.L18Bridge.q19894HitsBefore
#print axioms PPL.Convergence.L18Bridge.q19894HitsAfter
#print axioms PPL.Convergence.L18Bridge.l18SuffixForcingStepRow_false
#print axioms PPL.Convergence.L18Bridge.l18HitsSPL_of_current
#print axioms PPL.Convergence.L18Bridge.l18HitsSPL_append_singleton_false
#print axioms PPL.Convergence.L18Bridge.l18PrefixReachable_insert
#print axioms PPL.Convergence.L18Bridge.l18PrefixReachable_selected
#print axioms PPL.Convergence.L18Bridge.l18HitsSPL_of_sublist_reachableRows
#print axioms PPL.Convergence.L18Bridge.l18ForcingWordReachesSPL_of_reachableRows

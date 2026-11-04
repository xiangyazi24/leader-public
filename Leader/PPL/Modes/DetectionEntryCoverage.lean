import Leader.PPL.Modes.DetectionEntrySplit
import Leader.PPL.Modes.SignalLineageLocal


namespace PPL.Modes.Lemma6


set_option autoImplicit false


open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


private theorem rightNeighbor_ne_self_local
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega


private theorem foldl_or_true
    (xs : List Bool) :
    xs.foldl (fun acc b => acc || b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      simp only [List.foldl_cons, Bool.true_or]
      exact ih


private theorem foldl_or_true_of_mem
    (xs : List Bool)
    (hmem : true ∈ xs) :
    xs.foldl (fun acc b => acc || b) false = true := by
  induction xs with
  | nil =>
      simp at hmem
  | cons b xs ih =>
      rcases List.mem_cons.mp hmem with hb | ht
      · subst b
        simp only [List.foldl_cons, Bool.false_or]
        exact foldl_or_true xs
      · cases b
        · simp only [List.foldl_cons, Bool.false_or]
          exact ih ht
        · simp only [List.foldl_cons, Bool.false_or]
          exact foldl_or_true xs


private theorem leaderless_of_leaderPresent_false
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (hfalse : leaderPresent g.physical = false) :
    Leaderless g := by
  intro i
  cases hi : (g.physical i).leader with
  | false =>
      rfl
  | true =>
      have hmem :
          true ∈
            List.ofFn
              (fun j : Fin n =>
                (g.physical j).leader) := by
        rw [List.mem_ofFn]
        exact ⟨i, hi⟩
      have hor :=
        foldl_or_true_of_mem
          (List.ofFn
            (fun j : Fin n =>
              (g.physical j).leader))
          hmem
      unfold leaderPresent at hfalse
      rw [hor] at hfalse
      contradiction


private theorem leaderPresent_false_of_good_false
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (hgood : lemma6GoodB C = false) :
    leaderPresent C = false := by
  unfold lemma6GoodB at hgood
  cases hl : leaderPresent C with
  | false =>
      rfl
  | true =>
      simp [hl] at hgood


private theorem ownersFrom_refl
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) :
    OwnersFrom g g := by
  intro i t howner
  exact ⟨i, howner⟩


private theorem ghostStep_wellFormed_local
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (hwf : LineageWellFormed g) :
    LineageWellFormed (ghostStep ring g e) := by
  exact
    ⟨ownerMatchesPreserved ring g e hpsi hself hwf,
      noCloningPreserved ring g e hpsi hself hwf,
      issuedPreserved ring g e hpsi hself hwf⟩


private theorem ghostRun_wellFormed_ownersFrom
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (start g : GhostConfig n psi kappa)
    (word : DetSchedule n)
    (hlineage :
      SignalLineageOwnership
        (psi := psi) (kappa := kappa) ring)
    (hwf : LineageWellFormed g)
    (hfrom : OwnersFrom start g)
    (hfail :
      reachesAux ring g.physical word = false) :
    LineageWellFormed (ghostRun ring g word) ∧
      OwnersFrom start (ghostRun ring g word) := by
  have hcoverage :
      LeaderlessCoveragePreserved
        (psi := psi) (kappa := kappa) ring :=
    hlineage.2.2.2.2.2.2.2
  induction word generalizing g with
  | nil =>
      exact ⟨hwf, hfrom⟩
  | cons e rest ih =>
      cases hgood : lemma6GoodB g.physical with
      | true =>
          simp [reachesAux, hgood] at hfail
      | false =>
          have htail0 :
              reachesAux ring
                (pplStep ring g.physical e)
                rest = false := by
            simpa [reachesAux, hgood] using hfail
          have hpresent :
              leaderPresent g.physical = false :=
            leaderPresent_false_of_good_false
              g.physical hgood
          have hleaderless :
              Leaderless g :=
            leaderless_of_leaderPresent_false
              g hpresent
          have hself :
              ring.rightNeighbor e ≠ e :=
            rightNeighbor_ne_self_local
              hn3 ring e
          have hwf' :
              LineageWellFormed
                (ghostStep ring g e) :=
            ghostStep_wellFormed_local
              hpsi ring g e hself hwf
          have hfrom' :
              OwnersFrom start
                (ghostStep ring g e) :=
            hcoverage
              start g e hpsi hself
              hwf hfrom hleaderless
          have hphys :
              (ghostStep ring g e).physical =
                pplStep ring g.physical e := by
            rfl
          have htail :
              reachesAux ring
                (ghostStep ring g e).physical
                rest = false := by
            rw [hphys]
            exact htail0
          exact
            ih
              (g := ghostStep ring g e)
              hwf' hfrom' htail


private theorem ghostRun_physical
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (word : DetSchedule n) :
    (ghostRun ring g word).physical =
      runPPL ring g.physical word := by
  induction word generalizing g with
  | nil =>
      rfl
  | cons e rest ih =>
      have hphys :
          (ghostStep ring g e).physical =
            pplStep ring g.physical e := by
        rfl
      calc
        (ghostRun ring g (e :: rest)).physical =
            (ghostRun ring
              (ghostStep ring g e)
              rest).physical := by
          rfl
        _ =
            runPPL ring
              (ghostStep ring g e).physical
              rest :=
          ih (ghostStep ring g e)
        _ =
            runPPL ring
              (pplStep ring g.physical e)
              rest := by
          rw [hphys]
        _ =
            runPPL ring
              g.physical
              (e :: rest) := by
          rfl


private theorem foldl_and_true_of_all
    (xs : List Bool)
    (hall : ∀ b, b ∈ xs → b = true) :
    xs.foldl (fun acc b => acc && b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      have hb : b = true :=
        hall b (by simp)
      rw [List.foldl_cons, hb, Bool.true_and]
      exact
        ih
          (fun y hy =>
            hall y (by simp [hy]))


private theorem signalFreeB_true_of_forall_zero
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (hzero :
      ∀ i : Fin n,
        (C i).signalR.val = 0) :
    signalFreeB C = true := by
  unfold signalFreeB allAgentsB
  apply foldl_and_true_of_all
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, rfl⟩ := hb
  simp [hzero i]


theorem lemma6LeaderlessSignalCoverage :
    Lemma6LeaderlessSignalCoverage := by
  intro n psi kappa
  intro hn3 hpsi
  intro ring C word
  intro hlineage hfail hgone


  let start := initialGhost C


  have hwf0 :
      LineageWellFormed start := by
    simpa [start] using
      initialGhost_wellFormed C


  have hfrom0 :
      OwnersFrom start start :=
    ownersFrom_refl start


  have hfail0 :
      reachesAux ring start.physical word =
        false := by
    simpa [start, initialGhost] using hfail


  have hcarry :=
    ghostRun_wellFormed_ownersFrom
      hn3 hpsi ring
      start start word
      hlineage hwf0 hfrom0 hfail0


  let current := ghostRun ring start word


  have hgone' :
      StartTagsGone start current := by
    simpa [start, current] using hgone


  have hzeroCurrent :
      ∀ i : Fin n,
        (current.physical i).signalR.val = 0 := by
    exact
      signal_free_of_start_tags_gone
        start current
        hcarry.1.1
        hcarry.2
        hgone'


  have hphys :
      current.physical =
        runPPL ring C word := by
    have h :=
      ghostRun_physical ring start word
    simpa [current, start, initialGhost] using h


  have hzeroRun :
      ∀ i : Fin n,
        (runPPL ring C word i).signalR.val = 0 := by
    intro i
    have hz := hzeroCurrent i
    rw [hphys] at hz
    exact hz


  exact
    signalFreeB_true_of_forall_zero
      (runPPL ring C word)
      hzeroRun


#print axioms rightNeighbor_ne_self_local
#print axioms foldl_or_true
#print axioms foldl_or_true_of_mem
#print axioms leaderless_of_leaderPresent_false
#print axioms leaderPresent_false_of_good_false
#print axioms ownersFrom_refl
#print axioms ghostStep_wellFormed_local
#print axioms ghostRun_wellFormed_ownersFrom
#print axioms ghostRun_physical
#print axioms foldl_and_true_of_all
#print axioms signalFreeB_true_of_forall_zero
#print axioms lemma6LeaderlessSignalCoverage


end PPL.Modes.Lemma6

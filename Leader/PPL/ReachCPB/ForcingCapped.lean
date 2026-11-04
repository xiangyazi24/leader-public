import Leader.PPL.ReachCPB.Capped


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL.Probability


/-!
Capped Lemma-16 forcing.


The uncapped counterexamples in ReachCPBForcing disappear once every clock is
at kappa.  This bounded file closes all schedule/sublist plumbing and leaves
one literal one-interaction row per requested theorem.


The three rows are intentionally stated over PopulationProtocol.step itself.
No shadow kernel is introduced.
-/


def Lemma16DetectPersistenceCappedStepSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (e : Fin n),
    DetectReadyCapped ring C →
      let D : Config n psi kappa :=
        PopulationProtocol.step
          (PPL.protocol psi kappa) ring C e
      Or (PPL.CPB ring D)
        (And
          (DetectReadyCapped ring D)
          (∀ i : Fin n, (D i).dist = (C i).dist))




def Lemma16DistForcingCappedStepSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (e : Fin n),
    DetectReadyCapped ring C →
      let D : Config n psi kappa :=
        PopulationProtocol.step
          (PPL.protocol psi kappa) ring C e
      And
        (Or (PPL.CPB ring D)
          (And
            (DetectReadyCapped ring D)
            (∀ i : Fin n, (D i).dist = (C i).dist)))
        ((C (ring.rightNeighbor e)).dist.val ≠
            ((C e).dist.val + 1) % (2 * psi) →
          PPL.CPB ring D)




def LastClearedCapped
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (base : Fin n)
    (front : Nat)
    (C : Config n psi kappa) : Prop :=
  ∀ d : Nat,
    1 ≤ d →
    d ≤ front →
      (C (PPL.shiftLeft ring base d)).last = false




def Lemma16LastForcingCappedStepSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (base : Fin n)
      (C : Config n psi kappa)
      (front : Nat)
      (e : Fin n),
    front ≤ n →
    DistReadyCapped ring C →
    PPL.IsBorder C base →
    LastClearedCapped ring base front C →
      let D : Config n psi kappa :=
        PopulationProtocol.step
          (PPL.protocol psi kappa) ring C e
      Or (PPL.CPB ring D)
        (And
          (DistReadyCapped ring D)
          (And
            (PPL.IsBorder D base)
            (And
              (LastClearedCapped ring base front D)
              (e = PPL.shiftLeft ring base (front + 1) →
                front < n →
                LastClearedCapped ring base (front + 1) D))))




private def cappedForcing_run_append
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    PPL.Probability.runPPL ring C (u ++ v) =
      PPL.Probability.runPPL ring
        (PPL.Probability.runPPL ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append,
        PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule]
      exact
        ih
          (C :=
            PopulationProtocol.step
              (PPL.protocol psi kappa) ring C e)




private def cappedForcing_shiftRight_zero
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftRight ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt i.isLt]




private def cappedForcing_shiftRight_succ
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (k : Nat) :
    ring.rightNeighbor (PPL.shiftRight ring i k) =
      PPL.shiftRight ring i (k + 1) := by
  apply Fin.ext
  simp only [DirectedRing.rightNeighbor, PPL.shiftRight]
  try dsimp only
  rw [Nat.mod_add_mod, Nat.add_assoc]




private def cappedForcing_shiftRight_n
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftRight ring i n = i := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt]




private def cappedForcing_dist_formula
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hdist :
      ∀ i : Fin n,
        (C (ring.rightNeighbor i)).dist.val =
          ((C i).dist.val + 1) % (2 * psi))
    (base : Fin n) :
    ∀ k : Nat,
      (C (PPL.shiftRight ring base k)).dist.val =
        ((C base).dist.val + k) % (2 * psi) := by
  intro k
  induction k with
  | zero =>
      rw [cappedForcing_shiftRight_zero ring base]
      simpa using
        (Nat.mod_eq_of_lt (C base).dist.isLt).symm
  | succ k ih =>
      have hs :=
        hdist (PPL.shiftRight ring base k)
      rw [cappedForcing_shiftRight_succ ring base k] at hs
      rw [ih] at hs
      calc
        (C (PPL.shiftRight ring base (k + 1))).dist.val
            =
          ((((C base).dist.val + k) % (2 * psi)) + 1) %
            (2 * psi) := hs
        _ =
          ((C base).dist.val + k + 1) % (2 * psi) :=
            mod_succ_eq
              ((C base).dist.val + k) (2 * psi)
        _ =
          ((C base).dist.val + (k + 1)) % (2 * psi) := by
            congr 1
            try omega




private def cappedForcing_exists_border
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hdist :
      ∀ i : Fin n,
        (C (ring.rightNeighbor i)).dist.val =
          ((C i).dist.val + 1) % (2 * psi)) :
    ∃ base : Fin n, PPL.IsBorder C base := by
  let z : Fin n := ⟨0, ring.hn⟩
  have hcycle :=
    cappedForcing_dist_formula ring C hdist z n
  rw [cappedForcing_shiftRight_n ring z] at hcycle
  have hmpos : 0 < 2 * psi := by
    omega
  have hdiv : 2 * psi ∣ n :=
    dvd_of_lt_mod_add_eq
      (C z).dist.val n (2 * psi)
      hmpos (C z).dist.isLt hcycle
  have hmle : 2 * psi ≤ n :=
    Nat.le_of_dvd ring.hn hdiv
  let a : Nat :=
    (2 * psi - (C z).dist.val) % (2 * psi)
  have haM : a < 2 * psi := by
    dsimp [a]
    exact Nat.mod_lt _ hmpos
  have haN : a < n :=
    Nat.lt_of_lt_of_le haM hmle
  let base : Fin n :=
    PPL.shiftRight ring z a
  have hformula :=
    cappedForcing_dist_formula ring C hdist z a
  have hzero :
      ((C z).dist.val + a) % (2 * psi) = 0 := by
    dsimp [a]
    by_cases hz : (C z).dist.val = 0
    · rw [hz]
      simp
    · have hsub :
          2 * psi - (C z).dist.val < 2 * psi := by
        have hlt := (C z).dist.isLt
        omega
      rw [Nat.mod_eq_of_lt hsub]
      have hsum :
          (C z).dist.val +
              (2 * psi - (C z).dist.val) =
            2 * psi := by
        have hlt := (C z).dist.isLt
        omega
      rw [hsum, Nat.mod_self]
  have hbaseZero :
      (C base).dist.val = 0 := by
    dsimp [base]
    rw [hformula, hzero]
  refine ⟨base, ?_⟩
  exact Or.inl hbaseZero




private def cappedForcing_shiftLeft_zero
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftLeft ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftLeft, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt]




private def cappedForcing_shiftLeft_n
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftLeft ring i n = i := by
  apply Fin.ext
  simp [PPL.shiftLeft, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt]




private def cappedForcing_shiftLeft_val_of_le
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (d : Nat)
    (hd : d < n)
    (hle : d ≤ i.val) :
    (PPL.shiftLeft ring i d).val = i.val - d := by
  simp only [PPL.shiftLeft]
  rw [Nat.mod_eq_of_lt hd]
  have heq :
      i.val + n - d =
        n + (i.val - d) := by
    omega
  rw [heq, Nat.add_mod, Nat.mod_self,
    Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt (by omega)]




private def cappedForcing_shiftLeft_val_of_lt
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (d : Nat)
    (hd : d < n)
    (hlt : i.val < d) :
    (PPL.shiftLeft ring i d).val =
      n - (d - i.val) := by
  simp only [PPL.shiftLeft]
  rw [Nat.mod_eq_of_lt hd]
  have hsum :
      i.val + n - d =
        n - (d - i.val) := by
    omega
  rw [hsum]
  exact Nat.mod_eq_of_lt (by omega)




private def cappedForcing_shiftLeft_surjective
    {n : Nat}
    (ring : DirectedRing n)
    (base i : Fin n) :
    ∃ d : Nat,
      And (d < n)
        (PPL.shiftLeft ring base d = i) := by
  by_cases hle : i.val ≤ base.val
  · let d := base.val - i.val
    have hd : d < n := by
      dsimp [d]
      omega
    refine ⟨d, And.intro hd ?_⟩
    apply Fin.ext
    rw [cappedForcing_shiftLeft_val_of_le
      ring base d hd]
    · dsimp [d]
      omega
    · dsimp [d]
      omega
  · let d := base.val + n - i.val
    have hd : d < n := by
      dsimp [d]
      omega
    have hlt : base.val < d := by
      dsimp [d]
      omega
    refine ⟨d, And.intro hd ?_⟩
    apply Fin.ext
    rw [cappedForcing_shiftLeft_val_of_lt
      ring base d hd hlt]
    dsimp [d]
    omega




private def cappedForcing_lastCleared_all
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (base : Fin n)
    (C : Config n psi kappa)
    (hclear : LastClearedCapped ring base n C) :
    ∀ i : Fin n, (C i).last = false := by
  intro i
  obtain ⟨d, hd, hsite⟩ :=
    cappedForcing_shiftLeft_surjective ring base i
  by_cases hd0 : d = 0
  · subst d
    have hbasei : base = i := by
      calc
        base =
            PPL.shiftLeft ring base 0 :=
          (cappedForcing_shiftLeft_zero ring base).symm
        _ = i := hsite
    have hnlast :=
      hclear n (by omega) (Nat.le_refl n)
    rw [cappedForcing_shiftLeft_n ring base, hbasei] at hnlast
    exact hnlast
  · have hdlast :=
      hclear d (by omega) (Nat.le_of_lt hd)
    rw [hsite] at hdlast
    exact hdlast




private def cappedForcing_lastSweepFrom
    {n : Nat}
    (ring : DirectedRing n)
    (base : Fin n) :
    Nat → Nat → DetSchedule n
  | _, 0 => []
  | front, fuel + 1 =>
      PPL.shiftLeft ring base (front + 1) ::
        cappedForcing_lastSweepFrom
          ring base (front + 1) fuel




private def cappedForcing_lastSweepFrom_length
    {n : Nat}
    (ring : DirectedRing n)
    (base : Fin n) :
    ∀ front fuel : Nat,
      (cappedForcing_lastSweepFrom
        ring base front fuel).length = fuel := by
  intro front fuel
  induction fuel generalizing front with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [cappedForcing_lastSweepFrom, ih]




theorem lemma16DetectPersistenceCapped
    (hStep : Lemma16DetectPersistenceCappedStepSpec) :
    Lemma16DetectPersistenceCapped := by
  unfold Lemma16DetectPersistenceCapped
  intro n psi kappa hn3 hpsi ring C word hready
  induction word generalizing C with
  | nil =>
      exact Or.inr hready
  | cons e rest ih =>
      let D : Config n psi kappa :=
        PopulationProtocol.step
          (PPL.protocol psi kappa) ring C e
      have hs :
          Or (PPL.CPB ring D)
            (And
              (DetectReadyCapped ring D)
              (∀ i : Fin n,
                (D i).dist = (C i).dist)) := by
        simpa [D] using
          hStep hn3 hpsi ring C e hready
      rcases hs with hcpb | hnext
      · have hend :=
          cpb_run_closed
            hn3 hpsi ring D rest hcpb
        exact Or.inl (by
          simpa [D,
            PPL.Probability.runPPL,
            PPL.Probability.runPopulationSchedule]
            using hend)
      · have htail :=
          ih D hnext.1
        simpa [D,
          PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule]
          using htail




theorem lemma16DistForcingCapped
    (hStep : Lemma16DistForcingCappedStepSpec) :
    Lemma16DistForcingCappedSpec := by
  classical
  unfold Lemma16DistForcingCappedSpec
  intro n psi kappa hn3 hpsi ring C hready


  have hfreeze :
      ∀ (D : Config n psi kappa)
        (word : DetSchedule n),
        DetectReadyCapped ring D →
          Or
            (PPL.CPB ring
              (PPL.Probability.runPPL ring D word))
            (And
              (DetectReadyCapped ring
                (PPL.Probability.runPPL ring D word))
              (∀ i : Fin n,
                ((PPL.Probability.runPPL
                  ring D word) i).dist =
                  (D i).dist)) := by
    intro D word hD
    induction word generalizing D with
    | nil =>
        exact Or.inr
          (And.intro hD (fun _ => rfl))
    | cons e rest ih =>
        let E : Config n psi kappa :=
          PopulationProtocol.step
            (PPL.protocol psi kappa) ring D e
        have hs :
            And
              (Or (PPL.CPB ring E)
                (And
                  (DetectReadyCapped ring E)
                  (∀ i : Fin n,
                    (E i).dist = (D i).dist)))
              ((D (ring.rightNeighbor e)).dist.val ≠
                  ((D e).dist.val + 1) % (2 * psi) →
                PPL.CPB ring E) := by
          simpa [E] using
            hStep hn3 hpsi ring D e hD
        rcases hs.1 with hcpb | hnext
        · have hend :=
            cpb_run_closed
              hn3 hpsi ring E rest hcpb
          exact Or.inl (by
            simpa [E,
              PPL.Probability.runPPL,
              PPL.Probability.runPopulationSchedule]
              using hend)
        · have htail :=
            ih E hnext.1
          rcases htail with hcpb | htail
          · exact Or.inl (by
              simpa [E,
                PPL.Probability.runPPL,
                PPL.Probability.runPopulationSchedule]
                using hcpb)
          · apply Or.inr
            refine And.intro ?_ ?_
            · simpa [E,
                PPL.Probability.runPPL,
                PPL.Probability.runPopulationSchedule]
                using htail.1
            · intro i
              have h1 := htail.2 i
              have h2 := hnext.2 i
              simpa [E,
                PPL.Probability.runPPL,
                PPL.Probability.runPopulationSchedule]
                using h1.trans h2


  by_cases hbad :
      ∃ bad : Fin n,
        (C (ring.rightNeighbor bad)).dist.val ≠
          ((C bad).dist.val + 1) % (2 * psi)
  · obtain ⟨bad, hbad⟩ := hbad
    refine ⟨[bad], by simp, ?_⟩
    intro schedule hsub
    have hmem : bad ∈ schedule :=
      hsub.subset (by simp)
    obtain ⟨pre, post, hsched⟩ :=
      List.append_of_mem hmem
    subst schedule
    let P : Config n psi kappa :=
      PPL.Probability.runPPL ring C pre
    have hp0 :=
      hfreeze C pre hready
    have hp :
        Or (PPL.CPB ring P)
          (And
            (DetectReadyCapped ring P)
            (∀ i : Fin n,
              (P i).dist = (C i).dist)) := by
      simpa [P] using hp0
    rcases hp with hcpb | hp
    · apply Or.inl
      have hend :=
        cpb_run_closed
          hn3 hpsi ring P (bad :: post) hcpb
      have hrun :
          PPL.Probability.runPPL
              ring C (pre ++ bad :: post) =
            PPL.Probability.runPPL
              ring P (bad :: post) := by
        simpa [P] using
          cappedForcing_run_append
            ring C pre (bad :: post)
      rw [hrun]
      exact hend
    · have hbadP :
          (P (ring.rightNeighbor bad)).dist.val ≠
            ((P bad).dist.val + 1) % (2 * psi) := by
        intro hEq
        rw [hp.2 (ring.rightNeighbor bad),
          hp.2 bad] at hEq
        exact hbad hEq
      let E : Config n psi kappa :=
        PopulationProtocol.step
          (PPL.protocol psi kappa) ring P bad
      have hs :
          And
            (Or (PPL.CPB ring E)
              (And
                (DetectReadyCapped ring E)
                (∀ i : Fin n,
                  (E i).dist = (P i).dist)))
            ((P (ring.rightNeighbor bad)).dist.val ≠
                ((P bad).dist.val + 1) % (2 * psi) →
              PPL.CPB ring E) := by
        simpa [E] using
          hStep hn3 hpsi ring P bad hp.1
      have hborn : PPL.CPB ring E :=
        hs.2 hbadP
      have hend :=
        cpb_run_closed
          hn3 hpsi ring E post hborn
      have hrun1 :
          PPL.Probability.runPPL
              ring C (pre ++ bad :: post) =
            PPL.Probability.runPPL
              ring P (bad :: post) := by
        simpa [P] using
          cappedForcing_run_append
            ring C pre (bad :: post)
      have hrun2 :
          PPL.Probability.runPPL
              ring P (bad :: post) =
            PPL.Probability.runPPL
              ring E post := by
        simp [E,
          PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule] <;> rfl
      apply Or.inl
      rw [hrun1, hrun2]
      exact hend
  · have hdist :
        ∀ i : Fin n,
          (C (ring.rightNeighbor i)).dist.val =
            ((C i).dist.val + 1) % (2 * psi) := by
      intro i
      by_cases hi :
          (C (ring.rightNeighbor i)).dist.val =
            ((C i).dist.val + 1) % (2 * psi)
      · exact hi
      · exact False.elim (hbad ⟨i, hi⟩)
    let e0 : Fin n := ⟨0, ring.hn⟩
    refine ⟨[e0], by simp, ?_⟩
    intro schedule _hsub
    have hend :=
      hfreeze C schedule hready
    rcases hend with hcpb | hend
    · exact Or.inl hcpb
    · apply Or.inr
      refine And.intro hend.1 ?_
      intro i
      rw [hend.2 (ring.rightNeighbor i),
        hend.2 i]
      exact hdist i




theorem lemma16LastForcingCapped
    (hStep : Lemma16LastForcingCappedStepSpec) :
    Lemma16LastForcingCappedSpec := by
  classical
  unfold Lemma16LastForcingCappedSpec
  intro n psi kappa hn3 hpsi ring C hready


  obtain ⟨base, hborder⟩ :=
    cappedForcing_exists_border
      hpsi ring C hready.2


  have hstay :
      ∀ (front : Nat)
        (D : Config n psi kappa)
        (schedule : DetSchedule n),
        front ≤ n →
        DistReadyCapped ring D →
        PPL.IsBorder D base →
        LastClearedCapped ring base front D →
          Or
            (PPL.CPB ring
              (PPL.Probability.runPPL
                ring D schedule))
            (And
              (DistReadyCapped ring
                (PPL.Probability.runPPL
                  ring D schedule))
              (And
                (PPL.IsBorder
                  (PPL.Probability.runPPL
                    ring D schedule) base)
                (LastClearedCapped
                  ring base front
                  (PPL.Probability.runPPL
                    ring D schedule)))) := by
    intro front D schedule hfront hD hbase hclear
    induction schedule generalizing D with
    | nil =>
        exact Or.inr
          (And.intro hD
            (And.intro hbase hclear))
    | cons e rest ih =>
        let E : Config n psi kappa :=
          PopulationProtocol.step
            (PPL.protocol psi kappa) ring D e
        have hs :
            Or (PPL.CPB ring E)
              (And
                (DistReadyCapped ring E)
                (And
                  (PPL.IsBorder E base)
                  (And
                    (LastClearedCapped
                      ring base front E)
                    (e =
                        PPL.shiftLeft
                          ring base (front + 1) →
                      front < n →
                      LastClearedCapped
                        ring base (front + 1) E)))) := by
          simpa [E] using
            hStep hn3 hpsi ring base D front e
              hfront hD hbase hclear
        rcases hs with hcpb | hnext
        · have hend :=
            cpb_run_closed
              hn3 hpsi ring E rest hcpb
          exact Or.inl (by
            simpa [E,
              PPL.Probability.runPPL,
              PPL.Probability.runPopulationSchedule]
              using hend)
        · have htail :=
            ih E hnext.1 hnext.2.1 hnext.2.2.1
          simpa [E,
            PPL.Probability.runPPL,
            PPL.Probability.runPopulationSchedule]
            using htail


  have hone :
      ∀ (front : Nat)
        (D : Config n psi kappa)
        (schedule : DetSchedule n),
        front < n →
        DistReadyCapped ring D →
        PPL.IsBorder D base →
        LastClearedCapped ring base front D →
        ([PPL.shiftLeft
            ring base (front + 1)] :
          DetSchedule n).Sublist schedule →
          Or
            (PPL.CPB ring
              (PPL.Probability.runPPL
                ring D schedule))
            (And
              (DistReadyCapped ring
                (PPL.Probability.runPPL
                  ring D schedule))
              (And
                (PPL.IsBorder
                  (PPL.Probability.runPPL
                    ring D schedule) base)
                (LastClearedCapped
                  ring base (front + 1)
                  (PPL.Probability.runPPL
                    ring D schedule)))) := by
    intro front D schedule hfront hD hbase hclear hsub
    let req : Fin n :=
      PPL.shiftLeft ring base (front + 1)
    have hmem : req ∈ schedule := by
      apply hsub.subset
      simp [req]
    obtain ⟨pre, post, hsched⟩ :=
      List.append_of_mem hmem
    subst schedule
    let P : Config n psi kappa :=
      PPL.Probability.runPPL ring D pre
    have hp0 :=
      hstay front D pre
        (Nat.le_of_lt hfront) hD hbase hclear
    have hp :
        Or (PPL.CPB ring P)
          (And
            (DistReadyCapped ring P)
            (And
              (PPL.IsBorder P base)
              (LastClearedCapped
                ring base front P))) := by
      simpa [P] using hp0
    rcases hp with hcpb | hp
    · apply Or.inl
      have hend :=
        cpb_run_closed
          hn3 hpsi ring P (req :: post) hcpb
      have hrun :
          PPL.Probability.runPPL
              ring D (pre ++ req :: post) =
            PPL.Probability.runPPL
              ring P (req :: post) := by
        simpa [P] using
          cappedForcing_run_append
            ring D pre (req :: post)
      rw [hrun]
      exact hend
    · let E : Config n psi kappa :=
        PopulationProtocol.step
          (PPL.protocol psi kappa) ring P req
      have hs :
          Or (PPL.CPB ring E)
            (And
              (DistReadyCapped ring E)
              (And
                (PPL.IsBorder E base)
                (And
                  (LastClearedCapped
                    ring base front E)
                  (req =
                      PPL.shiftLeft
                        ring base (front + 1) →
                    front < n →
                    LastClearedCapped
                      ring base (front + 1) E)))) := by
        simpa [E] using
          hStep hn3 hpsi ring base P front req
            (Nat.le_of_lt hfront)
            hp.1 hp.2.1 hp.2.2
      rcases hs with hcpb | hs
      · have hend :=
          cpb_run_closed
            hn3 hpsi ring E post hcpb
        have hrun1 :
            PPL.Probability.runPPL
                ring D (pre ++ req :: post) =
              PPL.Probability.runPPL
                ring P (req :: post) := by
          simpa [P] using
            cappedForcing_run_append
              ring D pre (req :: post)
        have hrun2 :
            PPL.Probability.runPPL
                ring P (req :: post) =
              PPL.Probability.runPPL
                ring E post := by
          simp [E,
            PPL.Probability.runPPL,
            PPL.Probability.runPopulationSchedule] <;> rfl
        apply Or.inl
        rw [hrun1, hrun2]
        exact hend
      · have hprogress :
            LastClearedCapped
              ring base (front + 1) E :=
          hs.2.2.2 (by rfl) hfront
        have htail :=
          hstay (front + 1) E post
            (by omega) hs.1 hs.2.1 hprogress
        have hrun1 :
            PPL.Probability.runPPL
                ring D (pre ++ req :: post) =
              PPL.Probability.runPPL
                ring P (req :: post) := by
          simpa [P] using
            cappedForcing_run_append
              ring D pre (req :: post)
        have hrun2 :
            PPL.Probability.runPPL
                ring P (req :: post) =
              PPL.Probability.runPPL
                ring E post := by
          simp [E,
            PPL.Probability.runPPL,
            PPL.Probability.runPopulationSchedule] <;> rfl
        rcases htail with hcpb | htail
        · apply Or.inl
          rw [hrun1, hrun2]
          exact hcpb
        · apply Or.inr
          rw [hrun1, hrun2]
          exact htail


  have hgo :
      ∀ (front fuel : Nat)
        (D : Config n psi kappa)
        (schedule : DetSchedule n),
        front + fuel ≤ n →
        DistReadyCapped ring D →
        PPL.IsBorder D base →
        LastClearedCapped ring base front D →
        (cappedForcing_lastSweepFrom
          ring base front fuel).Sublist schedule →
          Or
            (PPL.CPB ring
              (PPL.Probability.runPPL
                ring D schedule))
            (And
              (DistReadyCapped ring
                (PPL.Probability.runPPL
                  ring D schedule))
              (And
                (PPL.IsBorder
                  (PPL.Probability.runPPL
                    ring D schedule) base)
                (LastClearedCapped
                  ring base (front + fuel)
                  (PPL.Probability.runPPL
                    ring D schedule)))) := by
    intro front fuel
    induction fuel generalizing front with
    | zero =>
        intro D schedule hsum hD hbase hclear _hsub
        have hs :=
          hstay front D schedule
            (by omega) hD hbase hclear
        rcases hs with hcpb | hs
        · exact Or.inl hcpb
        · apply Or.inr
          refine And.intro hs.1
            (And.intro hs.2.1 ?_)
          simpa using hs.2.2
    | succ fuel ih =>
        intro D schedule hsum hD hbase hclear hsub
        let req : Fin n :=
          PPL.shiftLeft ring base (front + 1)
        have hform :
            cappedForcing_lastSweepFrom
                ring base front (fuel + 1) =
              [req] ++
                cappedForcing_lastSweepFrom
                  ring base (front + 1) fuel := by
          rfl
        rw [hform] at hsub
        obtain ⟨pre, suf, hsched, hpre, hsuf⟩ :=
          List.append_sublist_iff.mp hsub
        subst schedule
        have hfirst0 :=
          hone front D pre
            (by omega) hD hbase hclear
            (by simpa [req] using hpre)
        let P : Config n psi kappa :=
          PPL.Probability.runPPL ring D pre
        have hfirst :
            Or (PPL.CPB ring P)
              (And
                (DistReadyCapped ring P)
                (And
                  (PPL.IsBorder P base)
                  (LastClearedCapped
                    ring base (front + 1) P))) := by
          simpa [P] using hfirst0
        rcases hfirst with hcpb | hfirst
        · apply Or.inl
          have hend :=
            cpb_run_closed
              hn3 hpsi ring P suf hcpb
          have hrun :
              PPL.Probability.runPPL
                  ring D (pre ++ suf) =
                PPL.Probability.runPPL
                  ring P suf := by
            simpa [P] using
              cappedForcing_run_append
                ring D pre suf
          rw [hrun]
          exact hend
        · have htail :=
            ih (front := front + 1)
              P suf (by omega)
              hfirst.1 hfirst.2.1 hfirst.2.2 hsuf
          have hrun :
              PPL.Probability.runPPL
                  ring D (pre ++ suf) =
                PPL.Probability.runPPL
                  ring P suf := by
            simpa [P] using
              cappedForcing_run_append
                ring D pre suf
          rcases htail with hcpb | htail
          · apply Or.inl
            rw [hrun]
            exact hcpb
          · apply Or.inr
            rw [hrun]
            refine And.intro htail.1
              (And.intro htail.2.1 ?_)
            have heq :
                front + (fuel + 1) =
                  (front + 1) + fuel := by
              omega
            rw [heq]
            exact htail.2.2


  let word : DetSchedule n :=
    cappedForcing_lastSweepFrom
      ring base 0 n
  have hlen : word.length = n := by
    dsimp [word]
    exact
      cappedForcing_lastSweepFrom_length
        ring base 0 n
  refine ⟨word, hlen, ?_⟩
  intro schedule hsub
  have hclear0 :
      LastClearedCapped ring base 0 C := by
    intro d hd hzero
    omega
  have hfull0 :=
    hgo 0 n C schedule
      (by omega) hready hborder hclear0
      (by simpa [word] using hsub)
  rcases hfull0 with hcpb | hfull
  · exact Or.inl hcpb
  · have hclearN :
        LastClearedCapped
          ring base n
          (PPL.Probability.runPPL
            ring C schedule) := by
      simpa using hfull.2.2
    have hall :=
      cappedForcing_lastCleared_all
        ring base
        (PPL.Probability.runPPL
          ring C schedule)
        hclearN
    apply Or.inr
    exact And.intro hfull.1 hall




end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16DetectPersistenceCapped
#print axioms PPL.Convergence.ReachCPB.lemma16DistForcingCapped
#print axioms PPL.Convergence.ReachCPB.lemma16LastForcingCapped

import Leader.Wu.Elimination.SinkTwoGapReachInvariant
open FiniteUniformStoppingTree PredictableRenewalOverlap LDTwoGapFrame
open LDSinkGapCleanup PPLLRepair LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance LDSinkTwoGapDeletion LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant Classical


set_option autoImplicit false


namespace LDSinkTwoGapWiredInstance


/-! ## Total port completion -/


def totalGood {n : Nat} {S : Type}
    (fallback : Fin n) (good bad : S -> Fin n) (s : S) : Fin n :=
  if good s = bad s then fallback else good s


def totalBad {n : Nat} {S : Type}
    (fallback : Fin n) (good bad : S -> Fin n) (s : S) : Fin n :=
  if good s = bad s then fallback else bad s


theorem total_ne {n : Nat} {S : Type}
    (fallbackGood fallbackBad : Fin n)
    (hfallback : fallbackGood ≠ fallbackBad)
    (good bad : S -> Fin n) (s : S) :
    totalGood fallbackGood good bad s ≠
      totalBad fallbackBad good bad s := by
  by_cases h : good s = bad s
  · simp [totalGood, totalBad, h, hfallback]
  · simp [totalGood, totalBad, h]


/-! ## Weak initial relation -/


def initRel {n psi : Nat} (hpsi : psi > 0) (F : TwoGapFrame n)
    (x s : AState n psi) : Prop :=
  GapPair hpsi F x ∧ GapPair hpsi F s ∧ x.conf = s.conf


/-!
The explicit simulation data.  Restart is deliberately absent: with the weak
initial relation it is proved below by choosing the physical state itself.
The seven remaining proof fields are exactly the one-step simulation seams.
-/
structure PhysPortSpec {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n) where
  fallbackGood : Fin n
  fallbackBad : Fin n
  fallback_ne : fallbackGood ≠ fallbackBad


  firstGoodRaw : AState n psi -> Fin n
  firstBadRaw : AState n psi -> Fin n
  secondGoodRaw : AState n psi -> Fin n
  secondBadRaw : AState n psi -> Fin n


  firstRel : AState n psi -> AState n psi -> Prop
  secondRel : AState n psi -> AState n psi -> Prop


  init_success :
    forall x s e,
      initRel hpsi F x s ->
      NoResetSuccess F (attemptStepConf hpsi F x e) ->
      NoResetSuccess F (attemptStepConf hpsi F s e)


  init_continue :
    forall x s e,
      initRel hpsi F x s ->
      ¬ EntranceSuccess F (attemptStepConf hpsi F x e) ->
      ¬ NoResetSuccess F (attemptStepConf hpsi F s e) ->
      initRel hpsi F
        (postState hpsi F x e)
        (postState hpsi F s e)


  init_handoff :
    forall x s e,
      initRel hpsi F x s ->
      EntranceSuccess F (attemptStepConf hpsi F x e) ->
      ¬ NoResetSuccess F (attemptStepConf hpsi F x e) ->
      ¬ NoResetSuccess F (attemptStepConf hpsi F s e) ->
      firstRel
        (postState hpsi F x e)
        (postState hpsi F s e)


  first_good :
    forall a s,
      firstRel a s ->
      ¬ NoResetSuccess F
        (attemptStepConf hpsi F s
          (totalGood fallbackGood firstGoodRaw firstBadRaw a)) ->
      secondRel
        (postState hpsi F a
          (totalGood fallbackGood firstGoodRaw firstBadRaw a))
        (postState hpsi F s
          (totalGood fallbackGood firstGoodRaw firstBadRaw a))


  first_continue :
    forall a s e,
      firstRel a s ->
      e ≠ totalGood fallbackGood firstGoodRaw firstBadRaw a ->
      e ≠ totalBad fallbackBad firstGoodRaw firstBadRaw a ->
      ¬ NoResetSuccess F (attemptStepConf hpsi F s e) ->
      firstRel
        (postState hpsi F a e)
        (postState hpsi F s e)


  second_good :
    forall b s,
      secondRel b s ->
      NoResetSuccess F
        (attemptStepConf hpsi F s
          (totalGood fallbackGood secondGoodRaw secondBadRaw b))


  second_continue :
    forall b s e,
      secondRel b s ->
      e ≠ totalGood fallbackGood secondGoodRaw secondBadRaw b ->
      e ≠ totalBad fallbackBad secondGoodRaw secondBadRaw b ->
      ¬ NoResetSuccess F (attemptStepConf hpsi F s e) ->
      secondRel
        (postState hpsi F b e)
        (postState hpsi F s e)


def physFirstGood {n psi : Nat} {hpsi : psi > 0}
    {F : TwoGapFrame n} (P : PhysPortSpec hpsi F) :
    AState n psi -> Fin n :=
  totalGood P.fallbackGood P.firstGoodRaw P.firstBadRaw


def physFirstBad {n psi : Nat} {hpsi : psi > 0}
    {F : TwoGapFrame n} (P : PhysPortSpec hpsi F) :
    AState n psi -> Fin n :=
  totalBad P.fallbackBad P.firstGoodRaw P.firstBadRaw


def physSecondGood {n psi : Nat} {hpsi : psi > 0}
    {F : TwoGapFrame n} (P : PhysPortSpec hpsi F) :
    AState n psi -> Fin n :=
  totalGood P.fallbackGood P.secondGoodRaw P.secondBadRaw


def physSecondBad {n psi : Nat} {hpsi : psi > 0}
    {F : TwoGapFrame n} (P : PhysPortSpec hpsi F) :
    AState n psi -> Fin n :=
  totalBad P.fallbackBad P.secondGoodRaw P.secondBadRaw


theorem physD_first_ne {n psi : Nat} {hpsi : psi > 0}
    {F : TwoGapFrame n} (P : PhysPortSpec hpsi F)
    (a : AState n psi) :
    physFirstGood P a ≠ physFirstBad P a := by
  exact total_ne P.fallbackGood P.fallbackBad P.fallback_ne
    P.firstGoodRaw P.firstBadRaw a


theorem physD_second_ne {n psi : Nat} {hpsi : psi > 0}
    {F : TwoGapFrame n} (P : PhysPortSpec hpsi F)
    (b : AState n psi) :
    physSecondGood P b ≠ physSecondBad P b := by
  exact total_ne P.fallbackGood P.fallbackBad P.fallback_ne
    P.secondGoodRaw P.secondBadRaw b


/-! ## Concrete serial race -/


abbrev physD {n psi : Nat} (hpsi : psi > 0) (F : TwoGapFrame n)
    (P : PhysPortSpec hpsi F) : SerialData n where
  A := AState n psi
  B := AState n psi
  firstGood := physFirstGood P
  firstBad := physFirstBad P
  nextA := postState hpsi F
  advance := fun a => postState hpsi F a (physFirstGood P a)
  secondGood := physSecondGood P
  secondBad := physSecondBad P
  nextB := postState hpsi F
  first_ne := physD_first_ne P
  second_ne := physD_second_ne P


def ready {n psi : Nat} (hpsi : psi > 0) (F : TwoGapFrame n) :
    AState n psi -> Fin n -> AState n psi :=
  postState hpsi F


/-! ## Simulation relation -/


def Rel {n psi : Nat} (hpsi : psi > 0) (F : TwoGapFrame n)
    (P : PhysPortSpec hpsi F) :
    StopNode (CompositeState (physD hpsi F P) psi) ->
      StopNode (AState n psi) -> Prop
  | .failure, _ => True
  | _, .success => True
  | .active (.inl x), .active s => initRel hpsi F x s
  | .active (.inr (.first a)), .active s => P.firstRel a s
  | .active (.inr (.second b)), .active s => P.secondRel b s
  | _, _ => False


/-! ## Normal forms for the three active source shapes -/


theorem fullStep_inl_normal_form {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (P : PhysPortSpec hpsi F) (x : AState n psi) (e : Fin n) :
    fullStep hpsi F (physD hpsi F P) (ready hpsi F) (.inl x) e =
      if EntranceSuccess F (attemptStepConf hpsi F x e) then
        if NoResetSuccess F (attemptStepConf hpsi F x e) then
          .success
        else
          .active (.inr (.first (postState hpsi F x e)))
      else
        .active (.inl (postState hpsi F x e)) := by
  simp only [fullStep, sequentialStep, entrance_normal_form, raceHandoff,
    ready, physD, SerialData.start]
  by_cases hEntrance :
      EntranceSuccess F (attemptStepConf hpsi F x e)
  · simp only [if_pos hEntrance]
    by_cases hSuccess : NoResetSuccess F (attemptStepConf hpsi F x e)
    · simp only [if_pos hSuccess, inRace]
    · simp only [if_neg hSuccess, inRace]
  · simp only [if_neg hEntrance]


theorem fullStep_first_normal_form {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (P : PhysPortSpec hpsi F) (a : AState n psi) (e : Fin n) :
    fullStep hpsi F (physD hpsi F P) (ready hpsi F)
        (.inr (.first a)) e =
      if e = physFirstGood P a then
        .active (.inr (.second
          (postState hpsi F a (physFirstGood P a))))
      else if e = physFirstBad P a then
        .failure
      else
        .active (.inr (.first (postState hpsi F a e))) := by
  simp only [fullStep, sequentialStep, physD, SerialData.step,
    serialRaceStep]
  by_cases hgood : e = physFirstGood P a
  · simp only [if_pos hgood, inRace]
  · simp only [if_neg hgood]
    by_cases hbad : e = physFirstBad P a
    · simp only [if_pos hbad, inRace]
    · simp only [if_neg hbad, inRace]


theorem fullStep_second_normal_form {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (P : PhysPortSpec hpsi F) (b : AState n psi) (e : Fin n) :
    fullStep hpsi F (physD hpsi F P) (ready hpsi F)
        (.inr (.second b)) e =
      if e = physSecondGood P b then
        .success
      else if e = physSecondBad P b then
        .failure
      else
        .active (.inr (.second (postState hpsi F b e))) := by
  simp only [fullStep, sequentialStep, physD, SerialData.step,
    serialRaceStep]
  by_cases hgood : e = physSecondGood P b
  · simp only [if_pos hgood, inRace]
  · simp only [if_neg hgood]
    by_cases hbad : e = physSecondBad P b
    · simp only [if_pos hbad, inRace]
    · simp only [if_neg hbad, inRace]


/-! ## Main simulation -/


theorem wired_simulation {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (P : PhysPortSpec hpsi F) :
    SuccessSimulation
      (fullStep hpsi F (physD hpsi F P) (ready hpsi F))
      (physicalBlockStep hpsi F)
      (Rel hpsi F P) := by
  refine { terminal := ?_, next := ?_ }
  · intro u v huv
    cases u with
    | active z =>
        exact Nat.zero_le _
    | failure =>
        exact Nat.zero_le _
    | success =>
        cases v with
        | success =>
            exact Nat.le_refl _
        | active s =>
            change False at huv
            exact False.elim huv
        | failure =>
            change False at huv
            exact False.elim huv
  · intro u v huv e
    cases v with
    | success =>
        cases u with
        | failure =>
            exact True.intro
        | success =>
            exact True.intro
        | active z =>
            simp only [stepNode]
            cases hnext :
                fullStep hpsi F (physD hpsi F P) (ready hpsi F) z e <;>
              exact True.intro
    | failure =>
        cases u with
        | failure =>
            exact True.intro
        | success =>
            change False at huv
            exact False.elim huv
        | active z =>
            change False at huv
            exact False.elim huv
    | active s =>
        cases u with
        | failure =>
            exact True.intro
        | success =>
            change False at huv
            exact False.elim huv
        | active z =>
            cases z with
            | inl x =>
                have hrel : initRel hpsi F x s := by
                  change initRel hpsi F x s at huv
                  exact huv
                simp only [stepNode]
                rw [fullStep_inl_normal_form,
                  physicalBlockStep_normal_form]
                by_cases hEntrance :
                    EntranceSuccess F (attemptStepConf hpsi F x e)
                · by_cases hxSuccess :
                      NoResetSuccess F (attemptStepConf hpsi F x e)
                  · have hsSuccess :
                        NoResetSuccess F (attemptStepConf hpsi F s e) :=
                      P.init_success x s e hrel hxSuccess
                    simp [hEntrance, hxSuccess, hsSuccess, Rel]
                  · by_cases hsSuccess :
                        NoResetSuccess F (attemptStepConf hpsi F s e)
                    · simp [hEntrance, hxSuccess, hsSuccess, Rel]
                    · have hh := P.init_handoff x s e hrel
                        hEntrance hxSuccess hsSuccess
                      simp [hEntrance, hxSuccess, hsSuccess, Rel, hh]
                · by_cases hsSuccess :
                      NoResetSuccess F (attemptStepConf hpsi F s e)
                  · simp [hEntrance, hsSuccess, Rel]
                  · have hc := P.init_continue x s e hrel
                      hEntrance hsSuccess
                    simp [hEntrance, hsSuccess, Rel, hc]
            | inr race =>
                cases race with
                | first a =>
                    have hrel : P.firstRel a s := by
                      change P.firstRel a s at huv
                      exact huv
                    simp only [stepNode]
                    rw [fullStep_first_normal_form,
                      physicalBlockStep_normal_form]
                    by_cases hgood : e = physFirstGood P a
                    · subst e
                      by_cases hsSuccess :
                          NoResetSuccess F
                            (attemptStepConf hpsi F s
                              (physFirstGood P a))
                      · simp [hsSuccess, Rel]
                      · have hn :
                            P.secondRel
                              (postState hpsi F a (physFirstGood P a))
                              (postState hpsi F s (physFirstGood P a)) := by
                          simpa [physFirstGood] using
                            (P.first_good a s hrel
                              (by simpa [physFirstGood] using hsSuccess))
                        simp [hsSuccess, Rel, hn]
                    · by_cases hbad : e = physFirstBad P a
                      · have hne :
                            physFirstBad P a ≠ physFirstGood P a :=
                          (physD_first_ne P a).symm
                        simp [hbad, hne, Rel]
                      · by_cases hsSuccess :
                            NoResetSuccess F (attemptStepConf hpsi F s e)
                        · simp [hgood, hbad, hsSuccess, Rel]
                        · have hn :
                              P.firstRel
                                (postState hpsi F a e)
                                (postState hpsi F s e) := by
                            exact P.first_continue a s e hrel
                              (by simpa [physFirstGood] using hgood)
                              (by simpa [physFirstBad] using hbad)
                              hsSuccess
                          simp [hgood, hbad, hsSuccess, Rel, hn]
                | second b =>
                    have hrel : P.secondRel b s := by
                      change P.secondRel b s at huv
                      exact huv
                    simp only [stepNode]
                    rw [fullStep_second_normal_form,
                      physicalBlockStep_normal_form]
                    by_cases hgood : e = physSecondGood P b
                    · subst e
                      have hsSuccess :
                          NoResetSuccess F
                            (attemptStepConf hpsi F s
                              (physSecondGood P b)) := by
                        simpa [physSecondGood] using
                          (P.second_good b s hrel)
                      simp [hsSuccess, Rel]
                    · by_cases hbad : e = physSecondBad P b
                      · have hne :
                            physSecondBad P b ≠ physSecondGood P b :=
                          (physD_second_ne P b).symm
                        simp [hbad, hne, Rel]
                      · by_cases hsSuccess :
                            NoResetSuccess F (attemptStepConf hpsi F s e)
                        · simp [hgood, hbad, hsSuccess, Rel]
                        · have hn :
                              P.secondRel
                                (postState hpsi F b e)
                                (postState hpsi F s e) := by
                            exact P.second_continue b s e hrel
                              (by simpa [physSecondGood] using hgood)
                              (by simpa [physSecondBad] using hbad)
                              hsSuccess
                          simp [hgood, hbad, hsSuccess, Rel, hn]


/-! ## Weakened restart capstone -/


structure WiredResidualGapPair {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (D : SerialData n)
    (readyFn : AState n psi -> Fin n -> D.A)
    (rel : StopNode (CompositeState D psi) ->
      StopNode (AState n psi) -> Prop) : Prop where
  simulation :
    SuccessSimulation
      (fullStep hpsi F D readyFn)
      (physicalBlockStep hpsi F)
      rel
  restart :
    forall s : AState n psi, GapPair hpsi F s ->
      exists x : AState n psi, GapPair hpsi F x ∧
        rel (.active (.inl x)) (.active s)


theorem wired_restart_gapPair {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (P : PhysPortSpec hpsi F) :
    forall s : AState n psi, GapPair hpsi F s ->
      exists x : AState n psi, GapPair hpsi F x ∧
        Rel hpsi F P (.active (.inl x)) (.active s) := by
  intro s hs
  refine ⟨s, hs, ?_⟩
  change initRel hpsi F s s
  exact ⟨hs, hs, rfl⟩


theorem wired_gapPair {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (P : PhysPortSpec hpsi F) :
    WiredResidualGapPair hpsi F
      (physD hpsi F P) (ready hpsi F) (Rel hpsi F P) := by
  exact {
    simulation := wired_simulation hpsi F P
    restart := wired_restart_gapPair hpsi F P
  }


end LDSinkTwoGapWiredInstance


#print axioms LDSinkTwoGapWiredInstance.total_ne
#print axioms LDSinkTwoGapWiredInstance.physD_first_ne
#print axioms LDSinkTwoGapWiredInstance.physD_second_ne
#print axioms LDSinkTwoGapWiredInstance.fullStep_inl_normal_form
#print axioms LDSinkTwoGapWiredInstance.fullStep_first_normal_form
#print axioms LDSinkTwoGapWiredInstance.fullStep_second_normal_form
#print axioms LDSinkTwoGapWiredInstance.wired_simulation
#print axioms LDSinkTwoGapWiredInstance.wired_restart_gapPair
#print axioms LDSinkTwoGapWiredInstance.wired_gapPair

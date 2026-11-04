import Leader.PPL.Convergence.BulletLineageSweep


namespace PPL.Convergence.BulletLineage


set_option autoImplicit false
set_option Elab.async false


open PPL.Convergence.BulletSweep
open PPL.Safety.PeacefulProps


private theorem rightNeighbor_ne_self_steps
    {n : Nat} (hn3 : 3 <= n)
    (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      have he := e.isLt
      omega
    rw [heq, Nat.mod_self] at hv
    omega


private theorem fin3_cases_steps
    (b : Fin 3) :
    b = (0 : Fin 3) \/
      b = (1 : Fin 3) \/
      b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega


private def BadLive4Steps
    {n : Nat}
    (ring : DirectedRing n)
    (D : Fin n -> Cell4)
    (i : Fin n) : Prop :=
  (D i).bullet = (2 : Fin 3) /\
    ¬ Peaceful4 ring D i


private theorem badLive_iff_four_steps
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n) :
    BadLive ring C i <->
      BadLive4Steps ring (project4 C) i := by
  rfl


private theorem rowE_left_bullet_zero_steps
    (l r : Cell4) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_steps lb with rfl | rfl | rfl <;>
  rcases fin3_cases_steps rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp [PPL.Elim.rowE]


private theorem project_step_case_steps
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    FourFieldStepCase ring
      (project4 C)
      (project4 (step ring C e))
      e := by
  simpa [step] using
    (PPL.Safety.PeacefulProps.step_fourField_cases
      hn3 hpsi ring C e)


private theorem source_bullet_zero4_steps
    {n : Nat}
    (ring : DirectedRing n)
    (D D' : Fin n -> Cell4)
    (e : Fin n)
    (hcase : FourFieldStepCase ring D D' e) :
    (D' e).bullet = (0 : Fin 3) := by
  unfold FourFieldStepCase at hcase
  dsimp only at hcase
  rcases hcase.2 with hrow | hbirth
  · rw [hrow.1]
    exact rowE_left_bullet_zero_steps _ _
  · rw [hbirth.1]
    exact rowE_left_bullet_zero_steps _ _


/--
Exact physical predecessor statement needed by NoNewBadOneStep.


Source: paper Lemmas 11 and 12.  A bad post-bullet is either the same
old bad live bullet or the line-59 descendant of a bad live initiator;
the latter branch records that the responder was not already live.
-/
private theorem bad4_origin_step_steps
    {n : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (D D' : Fin n -> Cell4)
    (e i : Fin n)
    (hcase : FourFieldStepCase ring D D' e)
    (hbad : BadLive4Steps ring D' i) :
    BadLive4Steps ring D i \/
      (i = ring.rightNeighbor e /\
        (D i).bullet ≠ (2 : Fin 3) /\
        BadLive4Steps ring D e) := by
  have hs :=
    PPL.Safety.PeacefulProps.peacefulScanLocality
      hn3 ring D D' e hcase
  by_cases hilive :
      (D i).bullet = (2 : Fin 3)
  · by_cases hipeace : Peaceful4 ring D i
    · have hp :=
        (hs.2.2 i hilive hipeace).1 hbad.1
      exact False.elim (hbad.2 hp)
    · exact Or.inl ⟨hilive, hipeace⟩
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      by_cases helive :
          (D e).bullet = (2 : Fin 3)
      · by_cases hepeace : Peaceful4 ring D e
        · have hp :=
            (hs.2.2 e helive hepeace).2
              rfl hbad.1 hilive
          exact False.elim (hbad.2 hp)
        · exact
            Or.inr ⟨rfl, hilive, helive, hepeace⟩
      · have hp :=
          hs.2.1 (ring.rightNeighbor e)
            hbad.1 hilive (Or.inr helive)
        exact False.elim (hbad.2 hp)
    · have hp :=
        hs.2.1 i hbad.1 hilive (Or.inl hij)
      exact False.elim (hbad.2 hp)


/--
Every owner stored at the responder after ghostStep is exactly one of:
the old responder owner, the advanced initiator owner, or the fresh owner.
This is just the public ghostStep_owner_responder equation, with Option
payloads exposed.
-/
private theorem responder_owner_cases_steps
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (o' : BulletOwner n)
    (howner :
      (ghostStep hpsi ring g e).owner
          (ring.rightNeighbor e) = some o') :
    (exists o : BulletOwner n,
      g.owner (ring.rightNeighbor e) = some o /\
        o' = o) \/
    (exists o : BulletOwner n,
      g.owner e = some o /\
        o' = advanceOwner o) \/
    o' = freshOwner g e := by
  have hr :=
    ghostStep_owner_responder
      hpsi ring g e hself
  rw [hr] at howner
  by_cases hpost :
      ((ghostStep hpsi ring g e).physical
        (ring.rightNeighbor e)).bullet =
          (2 : Fin 3)
  · rw [if_pos hpost] at howner
    by_cases hright :
        (g.physical (ring.rightNeighbor e)).bullet =
          (2 : Fin 3)
    · rw [if_pos hright] at howner
      cases ho : g.owner (ring.rightNeighbor e) with
      | none =>
          rw [ho] at howner
          cases howner
      | some o =>
          rw [ho] at howner
          have heq : o = o' := Option.some.inj howner
          exact Or.inl ⟨o, rfl, heq.symm⟩
    · rw [if_neg hright] at howner
      by_cases hleft :
          (g.physical e).bullet = (2 : Fin 3)
      · rw [if_pos hleft] at howner
        cases ho : g.owner e with
        | none =>
            rw [ho] at howner
            cases howner
        | some o =>
            rw [ho] at howner
            change some (advanceOwner o) = some o' at howner
            have heq : advanceOwner o = o' :=
              Option.some.inj howner
            exact Or.inr (Or.inl ⟨o, rfl, heq.symm⟩)
      · rw [if_neg hleft] at howner
        have heq : freshOwner g e = o' :=
          Option.some.inj howner
        exact Or.inr (Or.inr heq.symm)
  · rw [if_neg hpost] at howner
    cases howner


private theorem freshOwner_tag_ne_old_steps
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (e k : Fin n)
    (o : BulletOwner n)
    (hserial : OwnerSerialBound g)
    (hold : g.owner k = some o) :
    (freshOwner g e).tag ≠ o.tag := by
  intro htag
  have hlt := hserial k o hold
  have hv := congrArg BulletTag.serial htag
  change g.nextBirth = o.tag.serial at hv
  omega


private theorem noCloning_preserved_steps
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hsound : LineageSound ring g) :
    NoCloning (ghostStep hpsi ring g e) := by
  have hself :=
    rightNeighbor_ne_self_steps hn3 ring e
  have hnc := hsound.1
  have hserial := hsound.2.1
  intro i k oi ok hi hk htag
  by_cases hie : i = e
  · subst i
    rw [ghostStep_owner_source] at hi
    cases hi
  by_cases hke : k = e
  · subst k
    rw [ghostStep_owner_source] at hk
    cases hk
  by_cases hir : i = ring.rightNeighbor e
  · subst i
    by_cases hkr : k = ring.rightNeighbor e
    · exact hkr.symm
    · have hkold : g.owner k = some ok := by
        rw [← ghostStep_owner_other
          hpsi ring g e k hke hkr]
        exact hk
      have hcases :=
        responder_owner_cases_steps
          hpsi ring g e hself oi hi
      rcases hcases with hold | hrest
      · rcases hold with ⟨o, ho, hoi⟩
        subst oi
        exact
          hnc (ring.rightNeighbor e) k
            o ok ho hkold htag
      · rcases hrest with hmoved | hfresh
        · rcases hmoved with ⟨o, ho, hoi⟩
          subst oi
          have htagOld : o.tag = ok.tag := by
            simpa [advanceOwner] using htag
          have heq :=
            hnc e k o ok ho hkold htagOld
          exact False.elim (hke heq.symm)
        · subst oi
          have hnot :=
            freshOwner_tag_ne_old_steps
              g e k ok hserial hkold
          exact False.elim (hnot htag)
  · by_cases hkr : k = ring.rightNeighbor e
    · subst k
      have hiold : g.owner i = some oi := by
        rw [← ghostStep_owner_other
          hpsi ring g e i hie hir]
        exact hi
      have hcases :=
        responder_owner_cases_steps
          hpsi ring g e hself ok hk
      rcases hcases with hold | hrest
      · rcases hold with ⟨o, ho, hok⟩
        subst ok
        exact
          hnc i (ring.rightNeighbor e)
            oi o hiold ho htag
      · rcases hrest with hmoved | hfresh
        · rcases hmoved with ⟨o, ho, hok⟩
          subst ok
          have htagOld : oi.tag = o.tag := by
            simpa [advanceOwner] using htag
          have heq :=
            hnc i e oi o hiold ho htagOld
          exact False.elim (hie heq)
        · subst ok
          have hnot :=
            freshOwner_tag_ne_old_steps
              g e i oi hserial hiold
          exact False.elim (hnot htag.symm)
    · have hiold : g.owner i = some oi := by
        rw [← ghostStep_owner_other
          hpsi ring g e i hie hir]
        exact hi
      have hkold : g.owner k = some ok := by
        rw [← ghostStep_owner_other
          hpsi ring g e k hke hkr]
        exact hk
      exact hnc i k oi ok hiold hkold htag


private theorem ownerSerialBound_preserved_steps
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hsound : LineageSound ring g) :
    OwnerSerialBound (ghostStep hpsi ring g e) := by
  have hself :=
    rightNeighbor_ne_self_steps hn3 ring e
  intro k ok hk
  by_cases hke : k = e
  · subst k
    rw [ghostStep_owner_source] at hk
    cases hk
  by_cases hkr : k = ring.rightNeighbor e
  · subst k
    have hcases :=
      responder_owner_cases_steps
        hpsi ring g e hself ok hk
    rcases hcases with hold | hrest
    · rcases hold with ⟨o, ho, hok⟩
      subst ok
      have hlt := hsound.2.1
        (ring.rightNeighbor e) o ho
      change o.tag.serial < g.nextBirth + 1
      omega
    · rcases hrest with hmoved | hfresh
      · rcases hmoved with ⟨o, ho, hok⟩
        subst ok
        have hlt := hsound.2.1 e o ho
        change o.tag.serial < g.nextBirth + 1
        omega
      · subst ok
        change g.nextBirth < g.nextBirth + 1
        omega
  · have hold : g.owner k = some ok := by
      rw [← ghostStep_owner_other
        hpsi ring g e k hke hkr]
      exact hk
    have hlt := hsound.2.1 k ok hold
    change ok.tag.serial < g.nextBirth + 1
    omega


/--
A bad post-bullet is already owned, and its post owner has the same tag as
a bad pre-owner.  This simultaneously supplies post BadOwnerCoverage and the
ancestry conjunct of NoNewBadOneStep.
-/
private theorem bad_post_owned_ancestor_steps
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e i : Fin n)
    (hsound : LineageSound ring g)
    (hbad :
      BadLive ring
        (ghostStep hpsi ring g e).physical i) :
    exists o' : BulletOwner n,
    exists j : Fin n,
    exists o : BulletOwner n,
      (ghostStep hpsi ring g e).owner i = some o' /\
      g.owner j = some o /\
      BadLive ring g.physical j /\
      o'.tag = o.tag := by
  change BadLive ring (step ring g.physical e) i at hbad
  have hcase :=
    project_step_case_steps
      hn3 hpsi ring g.physical e
  have hbad4 :
      BadLive4Steps ring
        (project4 (step ring g.physical e)) i :=
    (badLive_iff_four_steps
      ring (step ring g.physical e) i).1 hbad
  have hie : i ≠ e := by
    intro hieq
    subst i
    have hzero :=
      source_bullet_zero4_steps
        ring
        (project4 g.physical)
        (project4 (step ring g.physical e))
        e hcase
    have hv :=
      congrArg Fin.val
        (hzero.symm.trans hbad4.1)
    omega
  have horigin :=
    bad4_origin_step_steps
      hn3 ring
      (project4 g.physical)
      (project4 (step ring g.physical e))
      e i hcase hbad4
  rcases horigin with hsame | hmoved
  · have hpre :
        BadLive ring g.physical i :=
      (badLive_iff_four_steps
        ring g.physical i).2 hsame
    obtain ⟨o, ho⟩ :=
      hsound.2.2 i hpre
    by_cases hir : i = ring.rightNeighbor e
    · subst i
      have hpost :
          ((ghostStep hpsi ring g e).physical
            (ring.rightNeighbor e)).bullet =
              (2 : Fin 3) := by
        change
          (step ring g.physical e
            (ring.rightNeighbor e)).bullet =
              (2 : Fin 3)
        exact hbad.1
      have howner :
          (ghostStep hpsi ring g e).owner
              (ring.rightNeighbor e) = some o := by
        rw [ghostStep_owner_responder
          hpsi ring g e
          (rightNeighbor_ne_self_steps hn3 ring e)]
        rw [if_pos hpost, if_pos hpre.1, ho]
      exact
        ⟨o, ring.rightNeighbor e, o,
          howner, ho, hpre, rfl⟩
    · have howner :
          (ghostStep hpsi ring g e).owner i = some o := by
        rw [ghostStep_owner_other
          hpsi ring g e i hie hir]
        exact ho
      exact ⟨o, i, o, howner, ho, hpre, rfl⟩
  · rcases hmoved with
      ⟨hir, hdest4, hsource4⟩
    subst i
    have hpre :
        BadLive ring g.physical e :=
      (badLive_iff_four_steps
        ring g.physical e).2 hsource4
    obtain ⟨o, ho⟩ :=
      hsound.2.2 e hpre
    have hdest :
        (g.physical (ring.rightNeighbor e)).bullet ≠
          (2 : Fin 3) := by
      exact hdest4
    have hpost :
        ((ghostStep hpsi ring g e).physical
          (ring.rightNeighbor e)).bullet =
            (2 : Fin 3) := by
      change
        (step ring g.physical e
          (ring.rightNeighbor e)).bullet =
            (2 : Fin 3)
      exact hbad.1
    have howner :
        (ghostStep hpsi ring g e).owner
            (ring.rightNeighbor e) =
          some (advanceOwner o) := by
      rw [ghostStep_owner_responder
        hpsi ring g e
        (rightNeighbor_ne_self_steps hn3 ring e)]
      rw [if_pos hpost, if_neg hdest,
        if_pos hpre.1, ho]
      rfl
    exact
      ⟨advanceOwner o, e, o,
        howner, ho, hpre, rfl⟩


private theorem badOwnerCoverage_preserved_steps
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hsound : LineageSound ring g) :
    BadOwnerCoverage ring
      (ghostStep hpsi ring g e) := by
  intro i hbad
  obtain ⟨o', j, o, hpost, hold, hpre, htag⟩ :=
    bad_post_owned_ancestor_steps
      hn3 hpsi ring g e i hsound hbad
  exact ⟨o', hpost⟩


private theorem bad_post_ancestry_steps
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e i : Fin n)
    (o' : BulletOwner n)
    (hsound : LineageSound ring g)
    (howner :
      (ghostStep hpsi ring g e).owner i =
        some o')
    (hbad :
      BadLive ring
        (ghostStep hpsi ring g e).physical i) :
    exists j : Fin n, exists o : BulletOwner n,
      g.owner j = some o /\
      BadLive ring g.physical j /\
      o'.tag = o.tag := by
  obtain ⟨opost, j, o, hpost, hold, hpre, htag⟩ :=
    bad_post_owned_ancestor_steps
      hn3 hpsi ring g e i hsound hbad
  have hs :
      some opost = some o' :=
    hpost.symm.trans howner
  have hopost : opost = o' :=
    Option.some.inj hs
  subst o'
  exact ⟨j, o, hold, hpre, htag⟩


theorem noNewBadOneStep_proved :
    NoNewBadOneStep := by
  intro n psi kappa hn3 hpsi ring g e hsound
  dsimp only
  constructor
  · exact
      And.intro
        (noCloning_preserved_steps
          hn3 hpsi ring g e hsound)
        (And.intro
          (ownerSerialBound_preserved_steps
            hn3 hpsi ring g e hsound)
          (badOwnerCoverage_preserved_steps
            hn3 hpsi ring g e hsound))
  · intro i o' howner hbad
    exact
      bad_post_ancestry_steps
        hn3 hpsi ring g e i o'
        hsound howner hbad


/-! ## Kernel counterexample to BadSweepProgressOneStep -/


private def sweepCounterRing : DirectedRing 3 :=
  ⟨by decide⟩


private abbrev sweepCounter0 : Fin 3 :=
  ⟨0, by decide⟩


private abbrev sweepCounter1 : Fin 3 :=
  ⟨1, by decide⟩


private abbrev sweepCounter2 : Fin 3 :=
  ⟨2, by decide⟩


private def sweepCounterBase : PPL.State 2 0 :=
  {
    leader := false
    id := false
    dist := ⟨1, by omega⟩
    last := true
    tokenB := none
    tokenW := none
    mode := true
    clock := 0
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false
  }


private def sweepCounterSource : PPL.State 2 0 :=
  {
    leader := false
    id := false
    dist := ⟨0, by omega⟩
    last := true
    tokenB := none
    tokenW := none
    mode := true
    clock := 0
    signalR := 0
    hits := 0
    bullet := 2
    shield := false
    signalB := true
  }


private def sweepCounterConfig : Config 3 2 0 :=
  fun i =>
    if i = sweepCounter2 then
      sweepCounterSource
    else
      sweepCounterBase


private def sweepCounterTag : BulletTag 3 :=
  {
    origin := sweepCounter0
    serial := 0
  }


private def sweepCounterOwner2 : BulletOwner 3 :=
  {
    tag := sweepCounterTag
    swept := 2
  }


private def sweepCounterOwner3 : BulletOwner 3 :=
  advanceOwner sweepCounterOwner2


private def sweepCounterGhost : GhostConfig 3 2 0 :=
  {
    physical := sweepCounterConfig
    owner := fun i =>
      if i = sweepCounter2 then
        some sweepCounterOwner2
      else
        none
    nextBirth := 1
  }


private def sweepCounterPending : DetSchedule 3 :=
  PPL.Convergence.BulletSweep.lemma15SweepWord
    sweepCounterRing


private theorem sweepCounterBadPre :
    BadLive sweepCounterRing
      sweepCounterGhost.physical
      sweepCounter2 := by
  unfold BadLive
  constructor
  · decide
  · decide


private theorem sweepCounterSound :
    LineageSound sweepCounterRing
      sweepCounterGhost := by
  constructor
  · intro i j oi oj hi hj htag
    by_cases hi2 : i = sweepCounter2
    · by_cases hj2 : j = sweepCounter2
      · exact hi2.trans hj2.symm
      · have hnone :
            sweepCounterGhost.owner j = none := by
          simp [sweepCounterGhost, hj2]
        rw [hnone] at hj
        cases hj
    · have hnone :
          sweepCounterGhost.owner i = none := by
        simp [sweepCounterGhost, hi2]
      rw [hnone] at hi
      cases hi
  constructor
  · intro i o ho
    by_cases hi2 : i = sweepCounter2
    · subst i
      have hs :
          some sweepCounterOwner2 = some o := by
        simpa [sweepCounterGhost] using ho
      have heq : sweepCounterOwner2 = o :=
        Option.some.inj hs
      subst o
      change 0 < 1
      omega
    · have hnone :
          sweepCounterGhost.owner i = none := by
        simp [sweepCounterGhost, hi2]
      rw [hnone] at ho
      cases ho
  · intro i hbad
    by_cases hi2 : i = sweepCounter2
    · subst i
      exact
        ⟨sweepCounterOwner2,
          by simp [sweepCounterGhost]⟩
    · have hzero :
          (sweepCounterGhost.physical i).bullet =
            (0 : Fin 3) := by
        simp [sweepCounterGhost,
          sweepCounterConfig, hi2,
          sweepCounterBase]
      have h02 :
          (0 : Fin 3) = (2 : Fin 3) :=
        hzero.symm.trans hbad.1
      have hv := congrArg Fin.val h02
      omega


private theorem sweepCounterProgressPre :
    BadProgressState
      sweepCounterRing
      sweepCounter0
      sweepCounterTag
      sweepCounterPending
      sweepCounterGhost := by
  constructor
  · exact
      ⟨[],
        by simp [sweepCounterPending]⟩
  · refine
      ⟨sweepCounter2, sweepCounterOwner2,
        ?_, rfl, sweepCounterBadPre,
        ?_, ?_, ?_⟩
    · simp [sweepCounterGhost]
    · decide
    · change 2 < 3
      omega
    · simp [sweepCounterPending,
        sweepCounterOwner2,
        sweepCounterTag,
        sweepCounter0]


private theorem sweepCounterPostOwner0 :
    (ghostStep
      (by decide : 2 <= 2)
      sweepCounterRing
      sweepCounterGhost
      sweepCounter2).owner sweepCounter0 =
        some sweepCounterOwner3 := by
  decide


private theorem sweepCounterPostOwner1 :
    (ghostStep
      (by decide : 2 <= 2)
      sweepCounterRing
      sweepCounterGhost
      sweepCounter2).owner sweepCounter1 =
        none := by
  decide


private theorem sweepCounterPostOwner2 :
    (ghostStep
      (by decide : 2 <= 2)
      sweepCounterRing
      sweepCounterGhost
      sweepCounter2).owner sweepCounter2 =
        none := by
  decide


private theorem sweepCounterBadPost :
    BadLive sweepCounterRing
      (ghostStep
        (by decide : 2 <= 2)
        sweepCounterRing
        sweepCounterGhost
        sweepCounter2).physical
      sweepCounter0 := by
  unfold BadLive
  constructor
  · decide
  · decide


private theorem sweepCounterNotRetired :
    ¬ LineageRetired
      sweepCounterRing
      (ghostStep
        (by decide : 2 <= 2)
        sweepCounterRing
        sweepCounterGhost
        sweepCounter2)
      sweepCounterTag := by
  intro hret
  apply hret sweepCounter0
  exact
    ⟨sweepCounterOwner3,
      sweepCounterPostOwner0,
      rfl,
      sweepCounterBadPost⟩


private theorem sweepCounterNoPostProgress
    (pending : DetSchedule 3) :
    ¬ BadProgressState
      sweepCounterRing
      sweepCounter0
      sweepCounterTag
      pending
      (ghostStep
        (by decide : 2 <= 2)
        sweepCounterRing
        sweepCounterGhost
        sweepCounter2) := by
  intro hprogress
  rcases hprogress.2 with
    ⟨i, o, howner, htag, hbad,
      hsite, hlt, hcredit⟩
  rcases fin3_cases_steps i with hi | hi | hi
  · rw [hi] at howner
    have hs :
        some sweepCounterOwner3 = some o := by
      exact
        sweepCounterPostOwner0.symm.trans howner
    have ho : sweepCounterOwner3 = o :=
      Option.some.inj hs
    subst o
    change 3 < 3 at hlt
    omega
  · rw [hi] at howner
    have hnone :
        (ghostStep
          (by decide : 2 <= 2)
          sweepCounterRing
          sweepCounterGhost
          sweepCounter2).owner (1 : Fin 3) =
            none := by
      simpa [sweepCounter1] using
        sweepCounterPostOwner1
    rw [hnone] at howner
    cases howner
  · rw [hi] at howner
    have hnone :
        (ghostStep
          (by decide : 2 <= 2)
          sweepCounterRing
          sweepCounterGhost
          sweepCounter2).owner (2 : Fin 3) =
            none := by
      simpa [sweepCounter2] using
        sweepCounterPostOwner2
    rw [hnone] at howner
    cases howner


/--
Kernel witness that the current one-step historical-cap residual is false.


The witness is an arbitrary but LineageSound ghost whose swept=2 owner was not
obtained by running initialGhost/ghostRun.  Edge 2 moves the bad live bullet
2 -> 0 and advances the owner to swept=3 while the bullet remains bad.
-/
theorem badSweepProgressOneStep_refuted :
    ¬ BadSweepProgressOneStep := by
  intro hprogress
  have hs :=
    hprogress
      (n := 3) (psi := 2) (kappa := 0)
      (by decide) (by decide)
      sweepCounterRing
      sweepCounterGhost
      sweepCounter2
      sweepCounter0
      sweepCounterTag
      sweepCounterPending
      sweepCounterSound
      sweepCounterProgressPre
  dsimp only at hs
  rcases hs with hret | hnext
  · exact sweepCounterNotRetired hret
  · exact
      sweepCounterNoPostProgress
        (sweepPendingStep
          sweepCounterPending
          sweepCounter2)
        hnext




/-! ## Reachable repair of the historical-cap residual -/


/--
Reachable one-step version of BadSweepProgressOneStep.


On the current main API, reachability is exactly
ghostRun hpsi ring (initialGhost C) schedule.
-/
def BadSweepProgressOneStepReachable : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (origin : Fin n)
    (tag : BulletTag n)
    (pending : DetSchedule n),
    (exists C : Config n psi kappa,
      exists schedule : DetSchedule n,
        g = ghostRun hpsi ring (initialGhost C) schedule) ->
    LineageSound ring g ->
    BadProgressState ring origin tag pending g ->
      let g' := ghostStep hpsi ring g e
      let pending' := sweepPendingStep pending e
      Or
        (LineageRetired ring g' tag)
        (BadProgressState ring origin tag pending' g')


private theorem ghostRun_append_steps
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (left right : DetSchedule n) :
    ghostRun hpsi ring g (left ++ right) =
      ghostRun hpsi ring
        (ghostRun hpsi ring g left) right := by
  induction left generalizing g with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append, ghostRun]
      exact ih (g := ghostStep hpsi ring g e)


private theorem ghostRun_append_one_steps
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (pre0 : DetSchedule n)
    (e : Fin n) :
    ghostRun hpsi ring g (pre0 ++ [e]) =
      ghostStep hpsi ring (ghostRun hpsi ring g pre0) e := by
  rw [ghostRun_append_steps]
  rfl


private theorem initial_owner_serial_bound_reachable_steps
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    OwnerSerialBound (initialGhost C) := by
  intro i o howner
  by_cases hlive : (C i).bullet = (2 : Fin 3)
  · let oi : BulletOwner n :=
      { tag := { origin := i, serial := 0 }, swept := 0 }
    have hsome : some oi = some o := by
      simpa [initialGhost, hlive, oi] using howner
    have ho : oi = o := Option.some.inj hsome
    subst o
    simp [initialGhost, oi]
  · simp [initialGhost, hlive] at howner


private theorem initial_bad_owner_coverage_reachable_steps
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    BadOwnerCoverage ring (initialGhost C) := by
  intro i hbad
  refine ⟨
    ({ tag := { origin := i, serial := 0 }, swept := 0 } :
      BulletOwner n), ?_⟩
  have hb : (C i).bullet = (2 : Fin 3) := hbad.1
  simp [initialGhost, hb]


private theorem initial_lineage_sound_reachable_steps
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    LineageSound ring (initialGhost C) := by
  exact And.intro
    (initialGhost_noCloning C)
    (And.intro
      (initial_owner_serial_bound_reachable_steps C)
      (initial_bad_owner_coverage_reachable_steps ring C))


private theorem lineage_sound_run_reachable_steps
    (hnew : NoNewBadOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (hsound : LineageSound ring g) :
    LineageSound ring (ghostRun hpsi ring g schedule) := by
  induction schedule generalizing g with
  | nil =>
      simpa [ghostRun] using hsound
  | cons e rest ih =>
      have hs1 :
          LineageSound ring (ghostStep hpsi ring g e) :=
        (hnew hn3 hpsi ring g e hsound).1
      simpa [ghostRun] using
        (ih (g := ghostStep hpsi ring g e) hs1)


private theorem bad_ancestry_run_reachable_steps
    (hnew : NoNewBadOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (hsound : LineageSound ring g)
    (i : Fin n)
    (ofinal : BulletOwner n)
    (howner :
      (ghostRun hpsi ring g schedule).owner i = some ofinal)
    (hbad :
      BadLive ring (ghostRun hpsi ring g schedule).physical i) :
    exists i0 : Fin n, exists o0 : BulletOwner n,
      And
        (g.owner i0 = some o0)
        (And
          (BadLive ring g.physical i0)
          (ofinal.tag = o0.tag)) := by
  induction schedule generalizing g i ofinal with
  | nil =>
      exact ⟨i, ofinal, howner, hbad, rfl⟩
  | cons e rest ih =>
      let g1 := ghostStep hpsi ring g e
      have hstep := hnew hn3 hpsi ring g e hsound
      have hs1 : LineageSound ring g1 := by
        simpa [g1] using hstep.1
      have hownerTail :
          (ghostRun hpsi ring g1 rest).owner i = some ofinal := by
        simpa [ghostRun, g1] using howner
      have hbadTail :
          BadLive ring (ghostRun hpsi ring g1 rest).physical i := by
        simpa [ghostRun, g1] using hbad
      obtain ⟨j, o1, hj, hbadj, htag1⟩ :=
        ih (g := g1) (i := i) (ofinal := ofinal)
          hs1 hownerTail hbadTail
      have hback := hstep.2 j o1
        (by simpa [g1] using hj)
        (by simpa [g1] using hbadj)
      obtain ⟨i0, o0, hi0, hbadi0, htag0⟩ := hback
      exact
        ⟨i0, o0, hi0, hbadi0, htag1.trans htag0⟩


private theorem lineage_retired_run_reachable_steps
    (hnew : NoNewBadOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (hsound : LineageSound ring g)
    (tag : BulletTag n)
    (hret : LineageRetired ring g tag) :
    LineageRetired ring (ghostRun hpsi ring g schedule) tag := by
  intro i htagged
  rcases htagged with ⟨ofinal, howner, htag, hbad⟩
  obtain ⟨i0, o0, hi0, hbadi0, hback⟩ :=
    bad_ancestry_run_reachable_steps hnew hn3 hpsi ring
      g schedule hsound i ofinal howner hbad
  apply hret i0
  exact
    ⟨o0, hi0, hback.symm.trans htag, hbadi0⟩


private theorem sweepPendingRun_nil_reachable_steps
    {n : Nat}
    (schedule : DetSchedule n) :
    sweepPendingRun ([] : DetSchedule n) schedule = [] := by
  induction schedule with
  | nil =>
      rfl
  | cons e rest ih =>
      simpa [sweepPendingRun, sweepPendingStep] using ih


private theorem sweepPendingRun_nil_of_sublist_reachable_steps
    {n : Nat}
    (pending schedule : DetSchedule n)
    (hsub : pending.Sublist schedule) :
    sweepPendingRun pending schedule = [] := by
  induction schedule generalizing pending with
  | nil =>
      have hlength : pending.length <= 0 := by
        simpa using hsub.length_le
      have hpending : pending = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst pending
      rfl
  | cons fired rest ih =>
      cases pending with
      | nil =>
          exact sweepPendingRun_nil_reachable_steps (fired :: rest)
      | cons requested tail =>
          by_cases hfire : fired = requested
          · subst fired
            have htail : tail.Sublist rest := by
              rcases List.sublist_cons_iff.mp hsub with
                hskip | ⟨tail', heq, ht⟩
              · exact
                  (List.sublist_cons_self requested tail).trans hskip
              · cases heq
                exact ht
            simp only [sweepPendingRun]
            rw [show
              sweepPendingStep (requested :: tail) requested = tail by
                simp [sweepPendingStep]]
            exact ih tail htail
          · have htail : (requested :: tail).Sublist rest := by
              rcases List.sublist_cons_iff.mp hsub with
                hskip | ⟨tail', heq, ht⟩
              · exact hskip
              · have hhead : requested = fired :=
                  (List.cons.inj heq).1
                exact False.elim (hfire hhead.symm)
            simp only [sweepPendingRun]
            rw [show
              sweepPendingStep (requested :: tail) fired =
                  requested :: tail by
                simp [sweepPendingStep, hfire]]
            exact ih (requested :: tail) htail


private theorem bad_progress_run_reachable_steps
    (hnew : NoNewBadOneStep)
    (hprogress : BadSweepProgressOneStepReachable)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (origin : Fin n)
    (tag : BulletTag n)
    (pending : DetSchedule n)
    (hreach :
      exists C : Config n psi kappa,
        exists pre0 : DetSchedule n,
          g = ghostRun hpsi ring (initialGhost C) pre0)
    (hsound : LineageSound ring g)
    (hstate : BadProgressState ring origin tag pending g) :
    Or
      (LineageRetired ring
        (ghostRun hpsi ring g schedule) tag)
      (BadProgressState ring origin tag
        (sweepPendingRun pending schedule)
        (ghostRun hpsi ring g schedule)) := by
  induction schedule generalizing g pending with
  | nil =>
      exact Or.inr
        (by simpa [ghostRun, sweepPendingRun] using hstate)
  | cons e rest ih =>
      have hone :=
        hprogress hn3 hpsi ring g e
          origin tag pending hreach hsound hstate
      have hs1 :
          LineageSound ring (ghostStep hpsi ring g e) :=
        (hnew hn3 hpsi ring g e hsound).1
      have hreach1 :
          exists C : Config n psi kappa,
            exists pre0 : DetSchedule n,
              ghostStep hpsi ring g e =
                ghostRun hpsi ring (initialGhost C) pre0 := by
        rcases hreach with ⟨C, pre0, hg⟩
        refine ⟨C, pre0 ++ [e], ?_⟩
        rw [hg]
        exact
          (ghostRun_append_one_steps
            hpsi ring (initialGhost C) pre0 e).symm
      rcases hone with hret | hnext
      · apply Or.inl
        have htail :=
          lineage_retired_run_reachable_steps
            hnew hn3 hpsi ring
            (ghostStep hpsi ring g e) rest hs1 tag hret
        simpa [ghostRun] using htail
      · have htail :=
          ih
            (g := ghostStep hpsi ring g e)
            (pending := sweepPendingStep pending e)
            hreach1 hs1 hnext
        simpa [ghostRun, sweepPendingRun] using htail


private theorem shiftRight_zero_reachable_steps
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftRight ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt i.isLt]


private theorem initial_bad_progress_state_reachable_steps
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (o : BulletOwner n)
    (howner : (initialGhost C).owner i = some o)
    (hbad : BadLive ring C i) :
    BadProgressState ring i o.tag
      (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
      (initialGhost C) := by
  let oi : BulletOwner n :=
    { tag := { origin := i, serial := 0 }, swept := 0 }
  have hsome : some oi = some o := by
    simpa [initialGhost, hbad.1, oi] using howner
  have ho : oi = o := Option.some.inj hsome
  subst o
  unfold BadProgressState
  refine And.intro ?_ ?_
  · exact ⟨[], by simp⟩
  · refine ⟨i, oi, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [oi] using howner
    · rfl
    · simpa [initialGhost] using hbad
    · simpa [oi] using
        (shiftRight_zero_reachable_steps ring i).symm
    · dsimp [oi]
      omega
    · simp


private theorem orderedSubsequenceBulletSweep_reachable_steps
    (hnew : NoNewBadOneStep)
    (hprogress : BadSweepProgressOneStepReachable) :
    OrderedSubsequenceBulletSweep := by
  intro n psi kappa hn3 hpsi ring C schedule hsub
  dsimp only
  have hs0 :
      LineageSound ring (initialGhost C) :=
    initial_lineage_sound_reachable_steps ring C
  have hsFinal :
      LineageSound ring
        (ghostRun hpsi ring (initialGhost C) schedule) :=
    lineage_sound_run_reachable_steps hnew hn3 hpsi ring
      (initialGhost C) schedule hs0
  constructor
  · intro i o howner hbad
    have hstate0 :=
      initial_bad_progress_state_reachable_steps
        hn3 ring C i o howner hbad
    have hrun :=
      bad_progress_run_reachable_steps hnew hprogress
        hn3 hpsi ring
        (initialGhost C) schedule i o.tag
        (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
        ⟨C, [], rfl⟩ hs0 hstate0
    rcases hrun with hret | hsurvive
    · exact hret
    · have hdone :
          sweepPendingRun
              (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
              schedule = [] :=
        sweepPendingRun_nil_of_sublist_reachable_steps
          (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
          schedule hsub
      unfold BadProgressState at hsurvive
      rcases hsurvive with
        ⟨hsuffix, j, o1, hj, htag, hbad1,
          hsite, hswept, hcredit⟩
      rw [hdone] at hcredit
      simp only [List.length_nil, Nat.sub_zero] at hcredit
      rw [PPL.Convergence.BulletSweep.lemma15SweepWord_length ring]
        at hcredit
      have hi := i.isLt
      omega
  · intro i hbad
    obtain ⟨o1, howner1⟩ :=
      hsFinal.2.2 i hbad
    obtain ⟨i0, o0, howner0, hbad0, htag⟩ :=
      bad_ancestry_run_reachable_steps hnew hn3 hpsi ring
        (initialGhost C) schedule hs0
        i o1 howner1 hbad
    exact
      ⟨i0, o0, o1, howner0, hbad0, howner1, htag⟩


theorem lemma15SublistSweep_of_reachable
    (hnew : NoNewBadOneStep)
    (hprog : BadSweepProgressOneStepReachable) :
    PPL.Convergence.BulletSweep.Lemma15SublistSweep :=
  lemma15SublistSweep
    (orderedSubsequenceBulletSweep_reachable_steps hnew hprog)


end PPL.Convergence.BulletLineage


#print axioms PPL.Convergence.BulletLineage.noNewBadOneStep_proved
#print axioms PPL.Convergence.BulletLineage.badSweepProgressOneStep_refuted
#print axioms PPL.Convergence.BulletLineage.lemma15SublistSweep_of_reachable



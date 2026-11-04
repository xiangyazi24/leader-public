import Leader.Wu.Birth.SeedRenewal

set_option autoImplicit false

namespace BirthCloseRenewal

open BirthSweepSpec BirthRenewalBridge BirthSeedRenewal FiniteUniformStoppingTree

/-! ## Physical entry through a matching probe/erase pair

An adjacent matching pair cannot be destroyed by another scheduler edge:
the probe is not a writable idle/erase target, and only its own incoming edge
can write the erase cell.  Its service creates an echo.  This adds the actual
close service to the two-service producer, with no normalization assumption
on the rest of the ring and no new protocol fields.
-/

/-- A local matching probe/erase pair enables the physical close service. -/
def HasClose {m : Nat} (hm : 0 < m) (x : Config m) : Prop :=
  ∃ i, closeGuard (x i) (x (nextSite hm i)) = true

/-- Either a commit/echo seed or an enabled close service exists. -/
def Ready {m : Nat} (hm : 0 < m) (x : Config m) : Prop :=
  Seeded x ∨ HasClose hm x

/-- Three-service rank: commit, echo, and close carry ranks zero, one, and
two respectively; the region outside all three is excluded explicitly. -/
noncomputable def closeRank {m : Nat} (hm : 0 < m) (x : Config m) : Nat := by
  classical
  exact if HasCommit x then 0 else if HasEcho x then 1 else if HasClose hm x then 2 else 0

/-- The clockwise ring successor is injective, including the one-site case. -/
theorem nextSite_injective {m : Nat} (hm : 0 < m)
    (i j : Fin m) (h : nextSite hm i = nextSite hm j) : i = j := by
  have hv := congrArg Fin.val h
  change (i.val + 1) % m = (j.val + 1) % m at hv
  apply Fin.ext
  by_cases hi : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hi] at hv
    by_cases hj : j.val + 1 < m
    · rw [Nat.mod_eq_of_lt hj] at hv
      omega
    · have hjm : j.val + 1 = m := by omega
      rw [hjm, Nat.mod_self] at hv
      omega
  · have him : i.val + 1 = m := by omega
    rw [him, Nat.mod_self] at hv
    by_cases hj : j.val + 1 < m
    · rw [Nat.mod_eq_of_lt hj] at hv
      omega
    · omega

/-- Every physical sweep clause writes only its two incident sites. -/
theorem sweep_preserves_untouched
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e i : Fin m) (hie : i ≠ e)
    (hir : i ≠ nextSite hm e) : sweepStep M hm x e i = x i := by
  unfold sweepStep
  split
  · simp [invalidateStep, setAt, hie, hir]
  · split
    · simp [commitStep, setAt, hie]
    · split
      · simp [launchStep, launchRaw, setAt, hie, hir]
      · unfold serviceStep
        split
        · simp [setAt, hie, hir]
        · split
          · simp [setAt, hie, hir]
          · split <;> simp [setAt, hie]

/-- An erase source has no service, commit, or launch branch of its own. -/
theorem erase_source_fixed
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (i : Fin m)
    (hquiet : invalidateGuard M hm i = false)
    (hi : (x i).phase = .erase) : sweepStep M hm x i = x := by
  simp [sweepStep, hquiet, commitGuard, launchGuard, serviceStep,
    moveGuard, closeGuard, echoGuard, hi]

/-- Servicing the matching pair creates an echo at its erase endpoint. -/
theorem close_creates_echo
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (i : Fin m)
    (hquiet : invalidateGuard M hm i = false)
    (hi : closeGuard (x i) (x (nextSite hm i)) = true) :
    HasEcho (sweepStep M hm x i) := by
  have hp : (x i).phase = .probe ∧
      (x (nextSite hm i)).phase = .erase ∧
      (x i).color = (x (nextSite hm i)).color := by
    simpa only [closeGuard, decide_eq_true_eq] using hi
  refine ⟨nextSite hm i, ?_⟩
  simp [sweepStep, hquiet, commitGuard, launchGuard, serviceStep,
    moveGuard, hi, hp.1, hp.2.1, echoControl]

/-- A non-birth edge either services a matching pair into an echo or preserves
both cells of that pair.  All other initial controls remain unrestricted. -/
theorem close_preserved_or_seeded
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (x : Config m) (e : Fin m)
    (hbirth : ¬ BirthEvent M hm x e) (hx : HasClose hm x) :
    Ready hm (sweepStep M hm x e) := by
  obtain ⟨i, hi⟩ := hx
  have hp : (x i).phase = .probe ∧
      (x (nextSite hm i)).phase = .erase ∧
      (x i).color = (x (nextSite hm i)).color := by
    simpa only [closeGuard, decide_eq_true_eq] using hi
  by_cases hie : i = e
  · subst i
    exact Or.inl (Or.inr (close_creates_echo M hm x e (hquiet e) hi))
  · have hleft := sweep_preserves_other M hm x e i (hquiet e) hbirth hie
      (by simp [hp.1]) (by simp [hp.1])
    have hright : sweepStep M hm x e (nextSite hm i) = x (nextSite hm i) := by
      by_cases hre : nextSite hm i = e
      · subst e
        rw [erase_source_fixed M hm x _ (hquiet _) hp.2.1]
      · apply sweep_preserves_untouched M hm x e _ hre
        intro heq
        exact hie (nextSite_injective hm i e heq)
    exact Or.inr ⟨i, by simpa only [hleft, hright] using hi⟩

/-- The three-service live region is closed until the birth stopping event. -/
theorem ready_preserved
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (x : Config m) (e : Fin m)
    (hbirth : ¬ BirthEvent M hm x e) (hx : Ready hm x) :
    Ready hm (sweepStep M hm x e) := by
  rcases hx with hs | hc
  · exact Or.inl (seeded_preserved M hm x e (hquiet e) hbirth hs)
  · exact close_preserved_or_seeded M hm hquiet x e hbirth hc

/-- The global rank cap is three, independent of population size. -/
theorem closeRank_lt_three {m : Nat} (hm : 0 < m) (x : Config m) :
    closeRank hm x < 3 := by
  classical
  unfold closeRank
  split
  · omega
  · split
    · omega
    · split <;> omega

/-- An existing commit/echo seed already has rank at most one. -/
theorem closeRank_le_one_of_seeded
    {m : Nat} (hm : 0 < m) (x : Config m) (hx : Seeded x) :
    closeRank hm x ≤ 1 := by
  classical
  rcases hx with hc | he
  · simp [closeRank, hc]
  · unfold closeRank
    split
    · omega
    · simp

/-- Each live state's lowest available stage persists or advances under any
non-birth edge, so its concrete rank cannot increase. -/
theorem closeRank_nonincrease
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (x : Config m) (e : Fin m)
    (hbirth : ¬ BirthEvent M hm x e) (hx : Ready hm x) :
    closeRank hm (sweepStep M hm x e) ≤ closeRank hm x := by
  classical
  by_cases hc : HasCommit x
  · have hc' := hasCommit_preserved M hm x e (hquiet e) hbirth hc
    simp [closeRank, hc, hc']
  · by_cases he : HasEcho x
    · have hs' := seeded_preserved M hm x e (hquiet e) hbirth (Or.inr he)
      simpa [closeRank, hc, he] using closeRank_le_one_of_seeded hm _ hs'
    · have hcl : HasClose hm x := by
        rcases hx with (hs | hs) | hcl
        · exact False.elim (hc hs)
        · exact False.elim (he hs)
        · exact hcl
      have hb := closeRank_lt_three hm (sweepStep M hm x e)
      simpa [closeRank, hc, he, hcl] using
        (show closeRank hm (sweepStep M hm x e) ≤ 2 by omega)

/-- The earliest available physical stage supplies a predictable birth or
strict rank drop, with no selected-edge progress assumption. -/
theorem ready_progress
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (x : Config m) (hx : Ready hm x) :
    ∃ e, BirthEvent M hm x e ∨
      DesignatedService M hm (closeRank hm) x e := by
  classical
  by_cases hc : HasCommit x
  · obtain ⟨i, hi⟩ := hc
    exact ⟨i, Or.inl (birthEvent_of_commit M hm x i
      (commitEvent_of_parts M hm x i (hquiet i) hi))⟩
  · by_cases he : HasEcho x
    · obtain ⟨i, hi⟩ := he
      have he' : HasEcho x := ⟨i, hi⟩
      have hc' : HasCommit (sweepStep M hm x i) :=
        ⟨i, echo_becomes_commit M hm x i (hquiet i) hi⟩
      exact ⟨i, Or.inr (by simp [DesignatedService, closeRank, hc, he', hc'])⟩
    · have hcl : HasClose hm x := by
        rcases hx with (hs | hs) | hcl
        · exact False.elim (hc hs)
        · exact False.elim (he hs)
        · exact hcl
      obtain ⟨i, hi⟩ := hcl
      have hcl' : HasClose hm x := ⟨i, hi⟩
      have he' := close_creates_echo M hm x i (hquiet i) hi
      have hr' := closeRank_le_one_of_seeded hm _ (Or.inr he')
      exact ⟨i, Or.inr (by
        unfold DesignatedService
        rw [show closeRank hm x = 2 by simp [closeRank, hc, he, hcl']]
        omega)⟩

/-- The concrete three-service rank excludes precisely the region without a
commit, echo, or adjacent matching close pair when the second path is off. -/
theorem nonplateau_iff_ready
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (hsecond : ∀ x e, M.secondBirth x e = false) (x : Config m) :
    ¬ RankPlateau M hm (closeRank hm) x ↔ Ready hm x := by
  classical
  constructor
  · intro hnp
    apply Classical.byContradiction
    intro hx
    have hc : ¬ HasCommit x := fun h => hx (Or.inl (Or.inl h))
    have he : ¬ HasEcho x := fun h => hx (Or.inl (Or.inr h))
    have hcl : ¬ HasClose hm x := fun h => hx (Or.inr h)
    apply hnp
    intro e
    have hcommit : commitGuard x e = false := by
      cases h : commitGuard x e with
      | false => rfl
      | true => exact False.elim (hc ⟨e, h⟩)
    constructor
    · simp [BirthEvent, birthGuard, commitEventGuard, hsecond, hcommit]
    · simp [DesignatedService, closeRank, hc, he, hcl]
  · intro hx hplateau
    obtain ⟨e, hb | hd⟩ := ready_progress M hm hquiet x hx
    · exact (hplateau e).1 hb
    · exact (hplateau e).2 hd

/-- The actual transition supplies every field of the rank-three certificate. -/
noncomputable def closeResidual
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (hsecond : ∀ x e, M.secondBirth x e = false) : BirthRenewalResidual M hm where
  rank := closeRank hm
  bound := 3
  law := by
    intro x hx
    have hr := (nonplateau_iff_ready M hm hquiet hsecond x).mp hx
    refine ⟨closeRank_lt_three hm x, ?_⟩
    intro e hbirth
    exact ⟨(nonplateau_iff_ready M hm hquiet hsecond _).mpr
      (ready_preserved M hm hquiet x e hbirth hr),
      closeRank_nonincrease M hm hquiet x e hbirth hr⟩

/-- An adjacent matching probe/erase pair, echo, or permitted commit anywhere
in an arbitrary quiet configuration gives half birth mass within `6*m`
interactions.  Any additional host birth path is allowed. -/
theorem ready_birth_half_mass
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (x : Config m) (hx : Ready hm x) :
    m ^ (6 * m) ≤ 2 * successCount (birthStep M hm) (.active x) (6 * m) := by
  let N := withoutSecondBirth M
  have hsecond : ∀ x e, N.secondBirth x e = false := fun _ _ => rfl
  have hnp := (nonplateau_iff_ready N hm hquiet hsecond x).mpr hx
  have hbase := BirthRenewalBridge.birth_mass N hm
    (closeResidual N hm hquiet hsecond) x hnp
  have hH : birthHorizon (closeResidual N hm hquiet hsecond) = 6 * m := by
    simp only [birthHorizon, birthBudget, closeResidual]
    omega
  rw [hH] at hbase
  exact Nat.le_trans hbase (Nat.mul_le_mul_left 2
    (successCount_withoutSecondBirth_le M hm (6 * m) x))

end BirthCloseRenewal

#print axioms BirthCloseRenewal.close_preserved_or_seeded
#print axioms BirthCloseRenewal.ready_preserved
#print axioms BirthCloseRenewal.nonplateau_iff_ready
#print axioms BirthCloseRenewal.ready_birth_half_mass

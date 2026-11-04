import Leader.Wu.Birth.RenewalBridge

set_option autoImplicit false

namespace BirthSeedRenewal

open BirthSweepSpec BirthRenewalBridge FiniteUniformStoppingTree

/-! ## A concrete bounded-rank producer for the physical birth sweep

An echo or a permitted commit is sufficient for fast birth even when every
other control cell is arbitrary.  Non-birth transitions cannot overwrite such
a cell: launches and probe moves write only idle/erase targets.  An echo's own
edge promotes it to commit; a permitted commit's own edge is birth.

This module proves those transition facts and constructs the renewal residual
from them.  It does not establish that every arbitrary configuration contains
such a seed, or that a forged echo has valid traversal provenance.
-/

/-- A physically enabled commit exists somewhere in the control ring. -/
def HasCommit {m : Nat} (x : Config m) : Prop :=
  ∃ i, commitGuard x i = true

/-- An echo control exists, with no restriction on its color or permission. -/
def HasEcho {m : Nat} (x : Config m) : Prop :=
  ∃ i, (x i).phase = .echo

/-- The concrete live region for the two-service birth argument. -/
def Seeded {m : Nat} (x : Config m) : Prop :=
  HasCommit x ∨ HasEcho x

/-- Zero at a commit, one at an echo without a commit, and zero outside the
seeded region.  This is proof data and adds no physical protocol state. -/
noncomputable def seedRank {m : Nat} (x : Config m) : Nat := by
  classical
  exact if HasCommit x then 0 else if HasEcho x then 1 else 0

/-- Every seed rank is strictly below the constant bound two. -/
theorem seedRank_lt_two {m : Nat} (x : Config m) : seedRank x < 2 := by
  classical
  unfold seedRank
  split
  · omega
  · split <;> omega

/-- A service edge cannot overwrite an echo/commit cell at another site,
because its two-site writes require an idle or erase right endpoint. -/
theorem service_preserves_other
    {m : Nat} (hm : 0 < m) (x : Config m) (e i : Fin m)
    (hie : i ≠ e) (hidle : (x i).phase ≠ .idle)
    (herase : (x i).phase ≠ .erase) :
    serviceStep hm x e i = x i := by
  by_cases hir : i = nextSite hm e
  · subst i
    have hmove : moveGuard (x e) (x (nextSite hm e)) = false := by
      simp [moveGuard, hidle]
    have hclose : closeGuard (x e) (x (nextSite hm e)) = false := by
      simp [closeGuard, herase]
    unfold serviceStep
    simp only [hmove, hclose, Bool.false_eq_true, ↓reduceIte]
    split <;> simp [setAt, hie]
  · unfold serviceStep
    split
    · simp [setAt, hie, hir]
    · split
      · simp [setAt, hie, hir]
      · split <;> simp [setAt, hie]

/-- A launch cannot overwrite an echo/commit cell away from its source,
because a successful launch requires an idle right endpoint. -/
theorem launch_preserves_other
    {m : Nat} (hm : 0 < m) (x : Config m) (e i : Fin m)
    (hlaunch : launchGuard hm x e = true)
    (hie : i ≠ e) (hidle : (x i).phase ≠ .idle) :
    launchStep hm x e i = x i := by
  have hparts : (x e).phase = .idle ∧ (x e).permit = true ∧
      (x (nextSite hm e)).phase = .idle := by
    simpa only [launchGuard, decide_eq_true_eq] using hlaunch
  have hir : i ≠ nextSite hm e := by
    intro heq
    subst i
    exact hidle hparts.2.2
  simp [launchStep, launchRaw, setAt, hie, hir]

/-- Under quiet host guards, a non-birth edge preserves every protected
echo/commit cell outside the edge source. -/
theorem sweep_preserves_other
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e i : Fin m)
    (hquiet : invalidateGuard M hm e = false)
    (hbirth : ¬ BirthEvent M hm x e)
    (hie : i ≠ e) (hidle : (x i).phase ≠ .idle)
    (herase : (x i).phase ≠ .erase) :
    sweepStep M hm x e i = x i := by
  have hcommit : commitGuard x e = false := by
    cases hc : commitGuard x e with
    | false => rfl
    | true =>
        exact False.elim (hbirth (birthEvent_of_commit M hm x e
          (commitEvent_of_parts M hm x e hquiet hc)))
  by_cases hlaunch : launchGuard hm x e = true
  · rw [sweepStep_launch M hm x e hquiet hcommit hlaunch]
    exact launch_preserves_other hm x e i hlaunch hie hidle
  · have hl : launchGuard hm x e = false := by
      cases h : launchGuard hm x e <;> simp_all
    rw [sweepStep_service M hm x e hquiet hcommit hl]
    exact service_preserves_other hm x e i hie hidle herase

/-- The echo's own scheduler edge installs a permitted commit in one physical
interaction, with no assumption on any other cell. -/
theorem echo_becomes_commit
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (i : Fin m)
    (hquiet : invalidateGuard M hm i = false)
    (hecho : (x i).phase = .echo) :
    commitGuard (sweepStep M hm x i) i = true := by
  simp [sweepStep, hquiet, commitGuard, launchGuard, serviceStep,
    moveGuard, closeGuard, echoGuard, hecho, commitControl]

/-- A permitted commit survives every non-birth edge. -/
theorem hasCommit_preserved
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hquiet : invalidateGuard M hm e = false)
    (hbirth : ¬ BirthEvent M hm x e) (hx : HasCommit x) :
    HasCommit (sweepStep M hm x e) := by
  obtain ⟨i, hi⟩ := hx
  have hparts : (x i).phase = .commit ∧ (x i).permit = true := by
    simpa only [commitGuard, decide_eq_true_eq] using hi
  have hie : i ≠ e := by
    intro heq
    subst i
    exact hbirth (birthEvent_of_commit M hm x e
      (commitEvent_of_parts M hm x e hquiet hi))
  have hkeep := sweep_preserves_other M hm x e i hquiet hbirth hie
    (by simp [hparts.1]) (by simp [hparts.1])
  refine ⟨i, ?_⟩
  simpa only [commitGuard, hkeep] using hi

/-- An echo remains present unless its own edge promotes it to commit; hence
the concrete seeded region is closed under every non-birth scheduler edge. -/
theorem seeded_preserved
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hquiet : invalidateGuard M hm e = false)
    (hbirth : ¬ BirthEvent M hm x e) (hx : Seeded x) :
    Seeded (sweepStep M hm x e) := by
  rcases hx with hc | ⟨i, hi⟩
  · exact Or.inl (hasCommit_preserved M hm x e hquiet hbirth hc)
  · by_cases hie : i = e
    · subst i
      exact Or.inl ⟨e, echo_becomes_commit M hm x e hquiet hi⟩
    · have hkeep := sweep_preserves_other M hm x e i hquiet hbirth hie
        (by simp [hi]) (by simp [hi])
      exact Or.inr ⟨i, by rw [hkeep]; exact hi⟩

/-- The rank cannot increase from a seeded state on a non-birth edge.  At
rank zero the existing commit persists; rank one is already the global cap. -/
theorem seedRank_nonincrease
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hquiet : invalidateGuard M hm e = false)
    (hbirth : ¬ BirthEvent M hm x e) (hx : Seeded x) :
    seedRank (sweepStep M hm x e) ≤ seedRank x := by
  classical
  by_cases hc : HasCommit x
  · have hc' := hasCommit_preserved M hm x e hquiet hbirth hc
    simp [seedRank, hc, hc']
  · have he : HasEcho x := hx.resolve_left hc
    have hb := seedRank_lt_two (sweepStep M hm x e)
    simpa [seedRank, hc, he] using (show seedRank (sweepStep M hm x e) ≤ 1 by omega)

/-- Every seed has either an immediate physical birth edge or an echo edge
that strictly lowers the concrete rank. -/
theorem seeded_progress
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (x : Config m) (hx : Seeded x) :
    ∃ e, BirthEvent M hm x e ∨
      DesignatedService M hm seedRank x e := by
  classical
  by_cases hc : HasCommit x
  · obtain ⟨i, hi⟩ := hc
    exact ⟨i, Or.inl (birthEvent_of_commit M hm x i
      (commitEvent_of_parts M hm x i (hquiet i) hi))⟩
  · have he : HasEcho x := hx.resolve_left hc
    obtain ⟨i, hi⟩ := he
    have hc' : HasCommit (sweepStep M hm x i) :=
      ⟨i, echo_becomes_commit M hm x i (hquiet i) hi⟩
    have he' : HasEcho x := ⟨i, hi⟩
    exact ⟨i, Or.inr (by simp [DesignatedService, seedRank, hc, hc', he'])⟩

/-- With the host's second birth path disabled, the rank plateau is exactly
the absence of any echo/permitted-commit seed.  This supplies a concrete
interpretation of the bridge's previously free exclusion predicate. -/
theorem nonplateau_iff_seeded
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (hsecond : ∀ x e, M.secondBirth x e = false)
    (x : Config m) :
    ¬ RankPlateau M hm seedRank x ↔ Seeded x := by
  classical
  constructor
  · intro hnp
    apply Classical.byContradiction
    intro hseed
    have hc : ¬ HasCommit x := fun h => hseed (Or.inl h)
    have he : ¬ HasEcho x := fun h => hseed (Or.inr h)
    apply hnp
    intro e
    have hcommit : commitGuard x e = false := by
      cases h : commitGuard x e with
      | false => rfl
      | true => exact False.elim (hc ⟨e, h⟩)
    constructor
    · simp [BirthEvent, birthGuard, commitEventGuard, hsecond, hcommit]
    · simp [DesignatedService, seedRank, hc, he]
  · intro hseed hplateau
    obtain ⟨e, hb | hd⟩ := seeded_progress M hm hquiet x hseed
    · exact (hplateau e).1 hb
    · exact (hplateau e).2 hd

/-- Concrete producer of the linear-horizon renewal certificate.  All rank,
closure and nonincrease facts are proved from the physical transition above;
only the host's operational quietness is assumed. -/
noncomputable def seedResidual
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (hsecond : ∀ x e, M.secondBirth x e = false) :
    BirthRenewalResidual M hm where
  rank := seedRank
  bound := 2
  law := by
    intro x hx
    have hseed := (nonplateau_iff_seeded M hm hquiet hsecond x).mp hx
    refine ⟨seedRank_lt_two x, ?_⟩
    intro e hbirth
    exact ⟨(nonplateau_iff_seeded M hm hquiet hsecond _).mpr
      (seeded_preserved M hm x e (hquiet e) hbirth hseed),
      seedRank_nonincrease M hm x e (hquiet e) hbirth hseed⟩

/-- A seed anywhere in an otherwise arbitrary control ring gives at least
half birth mass in `4*m` interactions.  No rank, progress, or closure residual
remains in the theorem type; there is no additional protocol state. -/
theorem seeded_birth_half_mass_disabled
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (hsecond : ∀ x e, M.secondBirth x e = false)
    (x : Config m) (hx : Seeded x) :
    m ^ (4 * m) ≤
      2 * successCount (birthStep M hm) (.active x) (4 * m) := by
  have hnp := (nonplateau_iff_seeded M hm hquiet hsecond x).mpr hx
  have hmass := BirthRenewalBridge.birth_mass M hm
    (seedResidual M hm hquiet hsecond) x hnp
  have hH : birthHorizon (seedResidual M hm hquiet hsecond) = 4 * m := by
    simp only [birthHorizon, birthBudget, seedResidual]
    omega
  simpa only [hH] using hmass

/-- Turn off only the host's second success guard.  The physical sweep
transition is definitionally identical to the original host's transition. -/
def withoutSecondBirth {m : Nat} (M : SweepModel m) : SweepModel m :=
  { M with secondBirth := fun _ _ => false }

/-- Re-enabling the secondary birth path can only increase the stopped
process's successful leaf count.  The proof compares every scheduler child;
it does not require independence or persistence of the extra birth guard. -/
theorem successCount_withoutSecondBirth_le
    {m : Nat} (M : SweepModel m) (hm : 0 < m) :
    ∀ T x,
      successCount (birthStep (withoutSecondBirth M) hm) (.active x) T ≤
        successCount (birthStep M hm) (.active x) T := by
  intro T
  induction T with
  | zero => intros; exact Nat.le_refl 0
  | succ T ih =>
      intro x
      rw [successCount_active_succ, successCount_active_succ]
      apply FiniteUniformStoppingTree.ofFn_sum_le
      intro e
      by_cases hfull : BirthEvent M hm x e
      · rw [birthStep_success M hm x e hfull, successCount_success]
        have hpart := node_count_partition
          (birthStep (withoutSecondBirth M) hm)
          (birthStep (withoutSecondBirth M) hm x e) T
        omega
      · have hsmall : ¬ BirthEvent (withoutSecondBirth M) hm x e := by
          intro h
          have hc : commitEventGuard M hm x e = true := by
            change (commitEventGuard M hm x e || false) = true at h
            simpa only [Bool.or_false] using h
          exact hfull (birthEvent_of_commit M hm x e hc)
        rw [birthStep_active M hm x e hfull,
          birthStep_active (withoutSecondBirth M) hm x e hsmall]
        exact ih (sweepStep M hm x e)

/-- A seed anywhere in an otherwise arbitrary quiet control ring gives at
least half birth mass in `4*m` interactions, even when the host enables an
additional birth path.  Every progress and closure law is derived above. -/
theorem seeded_birth_half_mass
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (hquiet : ∀ e, invalidateGuard M hm e = false)
    (x : Config m) (hx : Seeded x) :
    m ^ (4 * m) ≤
      2 * successCount (birthStep M hm) (.active x) (4 * m) := by
  have hbase := seeded_birth_half_mass_disabled (withoutSecondBirth M) hm
    hquiet (fun _ _ => rfl) x hx
  exact Nat.le_trans hbase (Nat.mul_le_mul_left 2
    (successCount_withoutSecondBirth_le M hm (4 * m) x))

end BirthSeedRenewal

#print axioms BirthSeedRenewal.sweep_preserves_other
#print axioms BirthSeedRenewal.seeded_preserved
#print axioms BirthSeedRenewal.nonplateau_iff_seeded
#print axioms BirthSeedRenewal.seeded_birth_half_mass

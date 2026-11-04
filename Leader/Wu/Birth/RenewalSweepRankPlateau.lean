import Leader.Wu.Birth.RenewalBridge

set_option autoImplicit false

namespace BirthRenewalBridge2

open BirthSweepSpec
open FiniteUniformStoppingTree
open PredictableTwoTargetFiniteTree

abbrev SweepRank (m : Nat) := Config m → Nat

/-- No immediate terminal birth edge. -/
def NoBirthEdge {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) : Prop :=
  ∀ e, ¬ BirthEvent M hm x e

/-- Exact deterministic-rank plateau: no physical scheduler edge lowers the
rank. -/
def RankPlateau {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (x : Config m) : Prop :=
  ∀ e, rank x ≤ rank (sweepStep M hm x e)

/-- Renewal plateau: no immediate birth and no rank-decreasing service. -/
def Plateau {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (x : Config m) : Prop :=
  NoBirthEdge M hm x ∧ RankPlateau M hm rank x

/-- The separated no-birth and rank-flat predicates describe exactly the
obstruction excluded by the linear-horizon bridge.  The two files use distinct
namespaces because their rank-only plateau predicates have different types. -/
theorem plateau_iff_renewalPlateau
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (x : Config m) :
    Plateau M hm rank x ↔ BirthRenewalBridge.RankPlateau M hm rank x := by
  constructor
  · rintro ⟨hbirth, hrank⟩ e
    refine ⟨hbirth e, ?_⟩
    have hle := hrank e
    unfold BirthRenewalBridge.DesignatedService
    omega
  · intro h
    constructor
    · exact fun e => (h e).1
    · intro e
      have hdrop := (h e).2
      unfold BirthRenewalBridge.DesignatedService at hdrop
      omega

/-- Rank-independent physical fixed-point family. -/
def StaticSweepPlateau {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) : Prop :=
  ∀ e,
    invalidateGuard M hm e = false ∧
    commitGuard x e = false ∧
    launchGuard hm x e = false ∧
    moveGuard (x e) (x (nextSite hm e)) = false ∧
    closeGuard (x e) (x (nextSite hm e)) = false ∧
    echoGuard (x e) = false

/-- A static physical fixed point with no birth edge. -/
def DeadSweepPlateau {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) : Prop :=
  StaticSweepPlateau M hm x ∧ NoBirthEdge M hm x

/-- Presence of a physical probe. -/
def HasProbe {m : Nat} (x : Config m) : Prop :=
  ∃ i, (x i).phase = .probe

/-- Abstract form of the new obstruction.  The concrete two-site instance is
`(probe,idle) <-> (idle,probe)` under quiet host guards. -/
def OrphanProbeCarousel {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (a b : Config m) : Prop :=
  NoBirthEdge M hm a ∧
  NoBirthEdge M hm b ∧
  HasProbe a ∧
  HasProbe b ∧
  (∀ e, sweepStep M hm a e = a ∨ sweepStep M hm a e = b) ∧
  (∀ e, sweepStep M hm b e = a ∨ sweepStep M hm b e = b)

/-- Every edge of a static sweep plateau is literally identity. -/
theorem staticSweepPlateau_fixed
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (hstatic : StaticSweepPlateau M hm x)
    (e : Fin m) :
    sweepStep M hm x e = x := by
  obtain ⟨hinvalid, hcommit, hlaunch, hmove, hclose, hecho⟩ :=
    hstatic e
  rw [sweepStep_service M hm x e hinvalid hcommit hlaunch]
  simp [serviceStep, hmove, hclose, hecho]

/-- A static physical fixed point is a rank plateau for every natural-valued
rank. -/
theorem staticSweepPlateau_rankPlateau
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (x : Config m)
    (hstatic : StaticSweepPlateau M hm x) :
    RankPlateau M hm rank x := by
  intro e
  rw [staticSweepPlateau_fixed M hm x hstatic e]
  exact Nat.le_refl _

/-- Therefore every dead static sweep state is a renewal plateau for every
rank. -/
theorem deadSweepPlateau_plateau
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (x : Config m)
    (hdead : DeadSweepPlateau M hm x) :
    Plateau M hm rank x := by
  exact ⟨hdead.2,
    staticSweepPlateau_rankPlateau M hm rank x hdead.1⟩

/-- Any closed two-state component forces at least one state to have no
rank-decreasing outgoing edge. -/
theorem closed_pair_has_rankPlateau
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (a b : Config m)
    (ha : ∀ e,
      sweepStep M hm a e = a ∨ sweepStep M hm a e = b)
    (hb : ∀ e,
      sweepStep M hm b e = a ∨ sweepStep M hm b e = b) :
    RankPlateau M hm rank a ∨ RankPlateau M hm rank b := by
  by_cases hab : rank a ≤ rank b
  · left
    intro e
    rcases ha e with hself | hother
    · rw [hself]
      exact Nat.le_refl _
    · rw [hother]
      exact hab
  · right
    have hba : rank b ≤ rank a := by
      omega
    intro e
    rcases hb e with hother | hself
    · rw [hother]
      exact hba
    · rw [hself]
      exact Nat.le_refl _

/-- The orphan-probe carousel forces a no-birth plateau containing a probe.
Hence the physical plateau family is strictly larger than a probe-free family. -/
theorem orphanProbeCarousel_has_probe_plateau
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (a b : Config m)
    (hcycle : OrphanProbeCarousel M hm a b) :
    (Plateau M hm rank a ∧ HasProbe a) ∨
      (Plateau M hm rank b ∧ HasProbe b) := by
  obtain ⟨hnoA, hnoB, hprobeA, hprobeB, ha, hb⟩ := hcycle
  rcases closed_pair_has_rankPlateau M hm rank a b ha hb with hA | hB
  · exact Or.inl ⟨⟨hnoA, hA⟩, hprobeA⟩
  · exact Or.inr ⟨⟨hnoB, hB⟩, hprobeB⟩

/-! ## Concrete physical obstructions

The predicates above do not themselves produce a carousel.  The following
states instantiate the unmodified physical transition and keep the host's
second birth path disabled.  They witness the missing arbitrary-state case;
they do not refute a host protocol that supplies a separate birth mechanism.
-/

/-- A fixed leaderless, reset-free host with no secondary birth mechanism.
The arbitrary aligned projection is set to false. -/
def quietModel (m : Nat) : SweepModel m where
  leaderAt := fun _ => false
  resetAt := fun _ => false
  aligned := fun _ => false
  secondBirth := fun _ _ => false

/-- An all-erase ring with no permissions; every site may be arbitrary initial
junk of this form, independently of the host's aligned projection. -/
def eraseTombstone (m : Nat) : Config m := fun _ => eraseControl 0

/-- The all-erase obstruction is a concrete dead fixed point for every
nonempty ring size, rather than a premise of the fixed-point theorem. -/
theorem eraseTombstone_dead (m : Nat) (hm : 0 < m) :
    DeadSweepPlateau (quietModel m) hm (eraseTombstone m) := by
  constructor
  · intro e
    simp [quietModel, eraseTombstone, invalidateGuard, leaderContactGuard,
      resetContactGuard, commitGuard, launchGuard, moveGuard, closeGuard,
      echoGuard, eraseControl]
  · intro e
    simp [BirthEvent, birthGuard, commitEventGuard, quietModel,
      eraseTombstone, commitGuard, eraseControl]

/-- One orphan probe on a two-site ring; the other site is idle. -/
def orphanA : Config 2 :=
  fun i => if i = 0 then probeControl 0 else idleControl 0

/-- The same orphan probe after its clockwise move. -/
def orphanB : Config 2 :=
  fun i => if i = 0 then idleControl 0 else probeControl 0

/-- The claimed two-state carousel is an actual instance of `sweepStep`,
including all clause priorities and every possible scheduler edge. -/
theorem orphan_carousel :
    OrphanProbeCarousel (quietModel 2) (by decide) orphanA orphanB := by
  refine ⟨by unfold NoBirthEdge BirthEvent; decide,
    by unfold NoBirthEdge BirthEvent; decide, ⟨0, rfl⟩, ⟨1, rfl⟩, ?_, ?_⟩
  · intro e
    have he : e = 0 ∨ e = 1 := by omega
    rcases he with rfl | rfl
    · right
      apply funext
      decide
    · left
      apply funext
      decide
  · intro e
    have he : e = 0 ∨ e = 1 := by omega
    rcases he with rfl | rfl
    · right
      apply funext
      decide
    · left
      apply funext
      decide

/-- A no-birth component closed under every physical scheduler edge has zero
successful leaves at every finite horizon.  This rules out probabilistic
renewal as well as deterministic rank descent on such a component. -/
theorem successCount_zero_of_closed_noBirth
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (P : Config m → Prop)
    (hbirth : ∀ x, P x → NoBirthEdge M hm x)
    (hstep : ∀ x, P x → ∀ e, P (sweepStep M hm x e)) :
    ∀ T x, P x → successCount (birthStep M hm) (.active x) T = 0 := by
  intro T
  induction T with
  | zero => intros; rfl
  | succ T ih =>
      intro x hx
      rw [BirthRenewalBridge.successCount_active_succ]
      have hzero : (List.ofFn (fun _ : Fin m => 0)).sum = 0 := by
        rw [FiniteUniformStoppingTree.ofFn_sum_const]
        exact Nat.mul_zero m
      rw [← hzero]
      apply ofFn_sum_eq
      intro e
      rw [birthStep_active M hm x e (hbirth x hx e)]
      exact ih _ (hstep x hx e)

/-- The concrete orphan carousel cannot birth with any finite scheduler
budget, even though both configurations contain a probe. -/
theorem orphan_successCount_zero (T : Nat) :
    successCount (birthStep (quietModel 2) (by decide)) (.active orphanA) T = 0 ∧
    successCount (birthStep (quietModel 2) (by decide)) (.active orphanB) T = 0 := by
  obtain ⟨hna, hnb, _, _, hsa, hsb⟩ := orphan_carousel
  have hzero := successCount_zero_of_closed_noBirth (quietModel 2) (by decide)
    (fun x => x = orphanA ∨ x = orphanB)
    (by rintro x (rfl | rfl); exact hna; exact hnb)
    (by rintro x (rfl | rfl) e; exact hsa e; exact hsb e)
  exact ⟨hzero T orphanA (Or.inl rfl), hzero T orphanB (Or.inr rfl)⟩

/-- Every finite birth probability is zero at the concrete all-erase state. -/
theorem eraseTombstone_successCount_zero (m : Nat) (hm : 0 < m) (T : Nat) :
    successCount (birthStep (quietModel m) hm) (.active (eraseTombstone m)) T = 0 := by
  have hd := eraseTombstone_dead m hm
  exact successCount_zero_of_closed_noBirth (quietModel m) hm
    (fun x => x = eraseTombstone m)
    (by rintro x rfl; exact hd.2)
    (by rintro x rfl e; exact staticSweepPlateau_fixed _ _ _ hd.1 e)
    T _ rfl

/-- No finite horizon and inverse-mass coefficient can give a positive
state-uniform birth bound for the isolated sweep with its second path off.
The missing arbitrary-state producer therefore requires physical input beyond
this sweep, not a different rank or a larger scheduler budget. -/
theorem quietModel_no_uniform_birth_mass
    (m : Nat) (hm : 0 < m) (H c : Nat) :
    ¬ (∀ x, m ^ H ≤ c * successCount (birthStep (quietModel m) hm) (.active x) H) := by
  intro h
  have hbad := h (eraseTombstone m)
  rw [eraseTombstone_successCount_zero m hm H, Nat.mul_zero] at hbad
  have hp := Nat.pow_pos (n := H) hm
  omega

/-- The all-state `BirthResidual.renewalCore` has no inhabitant for the quiet
host without its secondary birth mechanism.  This checks the actual carried
premise of `BirthSweepSpec`, not merely a chosen rank function. -/
theorem quietModel_no_birthResidual
    (m : Nat) (hm : 0 < m)
    (washed : TaggedConfig m → Prop) (rank : Config m → Nat)
    (target : Config m → Fin m) (bound : Nat) :
    ¬ Nonempty (BirthResidual (quietModel m) hm washed rank target bound) := by
  rintro ⟨R⟩
  have hl : Leaderless (quietModel m) := fun _ => rfl
  have hd := eraseTombstone_dead m hm
  rcases renewal_target_progress R hl (eraseTombstone m) with hb | hdrop
  · exact hd.2 _ hb
  · rw [staticSweepPlateau_fixed _ _ _ hd.1] at hdrop
    omega

/-- The orphan obstruction is outside every probe-free family and applies to
the exact plateau predicate consumed by the linear-horizon bridge. -/
theorem orphan_has_renewalPlateau (rank : SweepRank 2) :
    (BirthRenewalBridge.RankPlateau (quietModel 2) (by decide) rank orphanA ∧
      HasProbe orphanA) ∨
    (BirthRenewalBridge.RankPlateau (quietModel 2) (by decide) rank orphanB ∧
      HasProbe orphanB) := by
  rcases orphanProbeCarousel_has_probe_plateau (quietModel 2) (by decide)
    rank orphanA orphanB orphan_carousel with ha | hb
  · exact Or.inl ⟨(plateau_iff_renewalPlateau _ _ _ _).mp ha.1, ha.2⟩
  · exact Or.inr ⟨(plateau_iff_renewalPlateau _ _ _ _).mp hb.1, hb.2⟩

/-- The single residual proof object.  `rank` and `bound` are explicit proof
parameters, not protocol state.  A non-plateau state has bounded rank and one
predictable progress edge.  A non-birth rank drop must stay outside the
plateau; otherwise an initial `¬ Plateau` premise would not support iteration. -/
structure BirthRankResidual
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (bound : Nat) : Prop where
  progress :
    ∀ x, ¬ Plateau M hm rank x →
      rank x < bound ∧
      ∃ e : Fin m,
        BirthEvent M hm x e ∨
          (¬ BirthEvent M hm x e ∧
            rank (sweepStep M hm x e) < rank x ∧
            ¬ Plateau M hm rank (sweepStep M hm x e))

/-- Diagnostic witness: the weaker designated-word residual has
an instance for every host by assigning rank zero and excluding every state
without immediate birth.  Its mere inhabitation therefore proves no plateau
escape.  The linear-horizon bridge additionally requires all-edge closure. -/
theorem zeroRank_residual
    {m : Nat} (M : SweepModel m) (hm : 0 < m) :
    BirthRankResidual M hm (fun _ => 0) 1 := by
  refine ⟨?_⟩
  intro x hx
  refine ⟨Nat.zero_lt_one, ?_⟩
  have hex : ∃ e, BirthEvent M hm x e := by
    apply Classical.byContradiction
    intro hnone
    apply hx
    refine ⟨?_, fun _ => Nat.zero_le _⟩
    intro e hb
    exact hnone ⟨e, hb⟩
  obtain ⟨e, he⟩ := hex
  exact ⟨e, Or.inl he⟩

/-- Common scheduler horizon. -/
def birthH (bound : Nat) : Nat := bound

/-- Division-free inverse-mass constant. -/
def birthC (m bound : Nat) : Nat := m ^ bound

/-- Once success has been reached, all depth-`T` scheduler extensions remain
successful.  There are exactly `m ^ T` such extensions. -/
theorem absorbing_success_extensions
    {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (T : Nat) :
    successCount step (.success) T = m ^ T := by
  unfold successCount
  simpa [successWeight] using
    (treeWeight_success step successWeight T)

/-- Literal one-more-level form: every successful leaf has all `m` one-edge
extensions successful. -/
theorem absorbing_success_one_more
    {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (T : Nat) :
    successCount step (.success) (T + 1) =
      m * successCount step (.success) T := by
  rw [absorbing_success_extensions, absorbing_success_extensions]
  simp [Nat.pow_succ, Nat.mul_comm]

/-- One proof-selected scheduler child contributes no more than the complete
uniform sum over all `m` children.  This is the division-free counting form of
selecting that service with probability `1/m`. -/
private theorem one_term_le_ofFn_sum
    {m : Nat} (f : Fin m → Nat) (e : Fin m) :
    f e ≤ (List.ofFn f).sum := by
  let g : Fin m → Nat := fun i => if i = e then f e else 0
  have hpoint : ∀ i, g i ≤ f i := by
    intro i
    by_cases hie : i = e
    · subst i
      simp [g]
    · simp [g, hie]
  have hsum : (List.ofFn g).sum ≤ (List.ofFn f).sum :=
    ofFn_sum_le g f hpoint
  have hg : (List.ofFn g).sum = f e := by
    calc
      (List.ofFn g).sum = g e + (m - 1) * 0 := by
        apply ofFn_sum_one_value_else_const e g 0
        intro i hie
        simp [g, hie]
      _ = f e := by
        simp [g]
  rw [hg] at hsum
  exact hsum

/-- At rank zero, a certified non-plateau state cannot take a strict service
rank drop, so its predictable progress edge is an immediate birth. -/
theorem rankZero_nonplateau_birth
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (bound : Nat)
    (R : BirthRankResidual M hm rank bound)
    (x : Config m) (hx : ¬ Plateau M hm rank x)
    (hz : rank x = 0) :
    ∃ e, BirthEvent M hm x e := by
  have hprogress := (R.progress x hx).2
  obtain ⟨e, hbirth | hservice⟩ := hprogress
  · exact ⟨e, hbirth⟩
  · have hdrop := hservice.2.1
    rw [hz] at hdrop
    omega

/-- Bounded deterministic descent gives at least one successful depth-`k`
scheduler word.  Strict rank decrease can occur at most `rank x` times; at
rank zero the preceding theorem forces birth.  Absorbing success pads an
earlier birth to the common depth. -/
theorem designated_successCount_one
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (bound : Nat)
    (R : BirthRankResidual M hm rank bound) :
    ∀ k x, rank x < k → ¬ Plateau M hm rank x →
      1 ≤ successCount (birthStep M hm) (.active x) k := by
  intro k
  induction k with
  | zero =>
      intro x hrank hx
      omega
  | succ k ih =>
      intro x hrank hx
      have hcertificate := R.progress x hx
      obtain ⟨e, hcase⟩ := hcertificate.2
      have hchild :
          1 ≤ successCount (birthStep M hm)
            (birthStep M hm x e) k := by
        rcases hcase with hbirth | hservice
        · rw [birthStep_success M hm x e hbirth]
          rw [absorbing_success_extensions]
          have hpow : 0 < m ^ k := Nat.pow_pos hm
          omega
        · obtain ⟨hnoBirth, hdrop, hstay⟩ := hservice
          rw [birthStep_active M hm x e hnoBirth]
          apply ih (sweepStep M hm x e)
          · omega
          · exact hstay
      have hterm :=
        one_term_le_ofFn_sum
          (fun j : Fin m =>
            successCount (birthStep M hm)
              (birthStep M hm x j) k) e
      have hsum :
          1 ≤
            (List.ofFn (fun j : Fin m =>
              successCount (birthStep M hm)
                (birthStep M hm x j) k)).sum :=
        Nat.le_trans hchild hterm
      simpa only [successCount, treeWeight, stepNode] using hsum

/-- Outside the plateau, the common horizon is positive. -/
theorem birthH_pos
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (bound : Nat)
    (R : BirthRankResidual M hm rank bound)
    (x : Config m) (hx : ¬ Plateau M hm rank x) :
    0 < birthH bound := by
  have hrank := (R.progress x hx).1
  unfold birthH
  omega

/-- The inverse-mass constant is positive because `m > 0`. -/
theorem birthC_pos
    {m : Nat} (hm : 0 < m) (bound : Nat) :
    0 < birthC m bound := by
  unfold birthC
  exact Nat.pow_pos hm

/-- Non-vacuity: every certified non-plateau state has a positive successful
leaf count at the common horizon. -/
theorem birth_successCount_pos
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (bound : Nat)
    (R : BirthRankResidual M hm rank bound)
    (x : Config m) (hx : ¬ Plateau M hm rank x) :
    0 < successCount (birthStep M hm) (.active x) (birthH bound) := by
  have hrank := (R.progress x hx).1
  have hone :=
    designated_successCount_one M hm rank bound R
      bound x hrank hx
  unfold birthH
  omega

/-- State-uniform renewal mass on the non-plateau region.

`H = bound` and `c = m ^ bound`.  The proof-selected strict-service word has
length at most `H`; every selected service costs one factor `1/m`, and an
earlier success has all remaining extensions successful. -/
theorem birth_mass
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : SweepRank m) (bound : Nat)
    (R : BirthRankResidual M hm rank bound)
    (x : Config m) (hx : ¬ Plateau M hm rank x) :
    m ^ birthH bound ≤
      birthC m bound *
        successCount (birthStep M hm) (.active x) (birthH bound) := by
  have hrank := (R.progress x hx).1
  have hone :=
    designated_successCount_one M hm rank bound R
      bound x hrank hx
  change
    m ^ bound ≤
      m ^ bound *
        successCount (birthStep M hm) (.active x) bound
  have hmul := Nat.mul_le_mul_left (m ^ bound) hone
  simpa using hmul

end BirthRenewalBridge2

#print axioms BirthRenewalBridge2.staticSweepPlateau_fixed
#print axioms BirthRenewalBridge2.plateau_iff_renewalPlateau
#print axioms BirthRenewalBridge2.eraseTombstone_dead
#print axioms BirthRenewalBridge2.orphan_carousel
#print axioms BirthRenewalBridge2.orphan_successCount_zero
#print axioms BirthRenewalBridge2.orphan_has_renewalPlateau
#print axioms BirthRenewalBridge2.quietModel_no_uniform_birth_mass
#print axioms BirthRenewalBridge2.quietModel_no_birthResidual
#print axioms BirthRenewalBridge2.zeroRank_residual
#print axioms BirthRenewalBridge2.staticSweepPlateau_rankPlateau
#print axioms BirthRenewalBridge2.deadSweepPlateau_plateau
#print axioms BirthRenewalBridge2.closed_pair_has_rankPlateau
#print axioms BirthRenewalBridge2.orphanProbeCarousel_has_probe_plateau
#print axioms BirthRenewalBridge2.absorbing_success_extensions
#print axioms BirthRenewalBridge2.absorbing_success_one_more
#print axioms BirthRenewalBridge2.rankZero_nonplateau_birth
#print axioms BirthRenewalBridge2.designated_successCount_one
#print axioms BirthRenewalBridge2.birthH_pos
#print axioms BirthRenewalBridge2.birthC_pos
#print axioms BirthRenewalBridge2.birth_successCount_pos
#print axioms BirthRenewalBridge2.birth_mass

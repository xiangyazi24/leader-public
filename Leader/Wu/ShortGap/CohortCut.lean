import Leader.Wu.ShortGap.GenerationMask

/-!
# The predecessor cut and receipt provenance after epoch replacement

The accounting cut is the literal lower bound r-1 on every generation.
The two provenance clauses below refer to the actual retained epoch field,
not an extra archive of overwritten epochs. The forward clause requires a
right-clear qualification. Here a round-q right
receipt has been cleared once the right root's generation exceeds q.

Even with this qualification, the proposed reverse clause is not closed:
a successor launch overwrites the sole delivered epoch while the receiver
still holds its old denial. The witness is reached from the clean uniform
start and lies on the predecessor cut, on both sides of the failing step.
Thus the cut repairs the earlier future-cohort example but does not supply
the missing archive or a closed Bellman state type.
-/
namespace ShortGapCohortCut
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapCurrentCohort ShortGapLineage ShortGapLineageRetained
open ShortGapDenialTransportLiteral ShortGapGenerationMask
open ShortGapJoinedIncidenceBalance FiniteUniformStoppingTree
set_option autoImplicit false

/-- Entry into the predecessor cohort, including the vacuous round-zero cut. -/
def CohortEntered (R : RFrame) (r : Nat) (s : GhostRing R) : Prop :=
  ∀ i, r - 1 ≤ s.k i

theorem cohortEntered_iff (R : RFrame) (r : Nat) (s : GhostRing R) :
    CohortEntered R r s ↔ ShortGapGenerationMask.CohortEntered R r s := by
  cases r with
  | zero => exact ⟨fun _ => trivial, fun _ _ => Nat.zero_le _⟩
  | succ q => rfl

/-- Physical JOIN only increments counters, so every accounting cut persists. -/
theorem cohortEntered_step (R : RFrame) (r : Nat) (s : GhostRing R)
    (e : Vtx R) (hs : CohortEntered R r s) :
    CohortEntered R r (ghostStep' R s e) := by
  intro i
  exact Nat.le_trans (hs i) (Nat.le_add_right _ _)

theorem cohortEntered_start (R : RFrame) : CohortEntered R 1 (ghostStart R) :=
  fun _ => Nat.zero_le _

/-- The cut excludes the previous clean-start round-2 counterexample. -/
theorem old_counterexample_outside_cut : ¬ CohortEntered D 2 cold := by
  intro hc
  exact missing_cohort_entry ((cohortEntered_iff D 2 cold).mp hc)

/-- A comparison result physically present in the single retained epoch field. -/
def ResultEpoch (E : GapEpoch) (q : Nat) (c d : Choice) : Prop :=
  E = .returning q c d ∨ E = .delivered q c d

/-- The right root has JOINed beyond this receipt's departing generation.
This is a ghost-counter predicate; it introduces no physical protocol bit. -/
def RightCleared (R : RFrame) (s : GhostRing R) (g : Fin R.m) (q : Nat) : Prop :=
  q < s.k (next R g)

/-- Lineage' with incomingCurrent replaced by the two provenance
directions. All other fields are unchanged. The reverse witness is an actual
returning/delivered epoch, with current or previous right-root generation;
immutable history alone is not declared to be a retained epoch. -/
structure Lineage'' (R : RFrame) (s : GhostRing R) : Prop where
  coherent : Lineage R (prefixView R s)
  idleReady : ∀ g, s.epoch g = .idle → s.k g = s.k (next R g) ∧
    (s.cfg (rootV R g)).cwPort = some .toSend ∧
    (s.cfg (rootV R (next R g))).ccwPort = some .free
  resultRight : ∀ g q c d, ResultEpoch (s.epoch g) q c d →
    ¬ RightCleared R s g q →
    (s.cfg (rootV R (next R g))).ccwPort = some (resCcw c d)
  rightResult : ∀ g, CcwHeld (s.cfg (rootV R (next R g))).ccwPort →
    ∃ q c d, ResultEpoch (s.epoch g) q c d ∧
      (q = s.k (next R g) ∨ q + 1 = s.k (next R g)) ∧
      (s.cfg (rootV R (next R g))).ccwPort = some (resCcw c d)

theorem lineage''_start (R : RFrame) : Lineage'' R (ghostStart R) := by
  refine ⟨lineage_start R, (lineage'_start R).idleReady, ?_, ?_⟩
  · intro g q c d h
    rcases h with h | h <;> cases h
  · intro g h; exact False.elim h

/-- Raw receipt provenance is still derived from the unchanged coherent
prefix; it is not a field of the repaired structure. -/
theorem provenance_of_lineage'' (R : RFrame) (s : GhostRing R)
    (hs : Lineage'' R s) (e : Vtx R) : RawReceiptProvenance R (physical R s) e :=
  provenance_of_lineage R (prefixView R s) hs.coherent e

theorem neighborSkew_of_lineage'' (R : RFrame) (s : GhostRing R)
    (hs : Lineage'' R s) : NeighborSkew R (physical R s) :=
  neighborSkew_of_lineage R (prefixView R s) hs.coherent

/-- The generation-masked word simulation only uses the coherent prefix,
so it survives this change to receipt provenance. -/
theorem wordOf''_step (R : RFrame) (r : Nat) (s : GhostRing R)
    (hs : Lineage'' R s) (e : Vtx R) :
    wordOf R r (ghostStep' R s e) = joinedIncidenceStep (placement R)
      (genMask R r s) (wordOf R r s) (encode R e) :=
  wordOf_step R r (prefixView R s) e hs.coherent

/-- Keeping the coherent prefix means the proposed previous-generation
alternative adds no states: a held port and a result in the single epoch
field force that result to have the right root's current generation.
This implication exposes the surviving strictness of the proposed repair. -/
theorem lineage''_to_lineage' (R : RFrame) (s : GhostRing R) (hs : Lineage'' R s) :
    Lineage' R s := by
  refine ⟨hs.coherent, hs.idleReady, ?_⟩
  intro g
  constructor
  · intro hp
    obtain ⟨q,c,d,he,hq,_⟩ := hs.rightResult g hp
    have hc := (hs.coherent.incoming g).mp hp
    rcases he with he | he
    all_goals
      simp only [prefixView, he, ComparedAt] at hc
      have hq' : q = s.k (next R g) := by omega
      simpa only [he, CurrentResult] using hq'
  · intro hc
    apply (hs.coherent.incoming g).mpr
    cases he : s.epoch g <;> simp only [he,CurrentResult] at hc
    · simp only [prefixView,he,ComparedAt]; omega
    · simp only [prefixView,he,ComparedAt]; omega

/-- The earlier positive-debt existence result transfers without assuming
simulation, and does not need a Race premise or the stronger entry cut. -/
theorem unjoined_gen_has_debt (R : RFrame) (r : Nat) (s : GhostRing R)
    (hs : Lineage'' R s) (hd : DenialOnly R r s) (i : Fin R.m) (hi : s.k i < r) :
    0 < latentDebt R r s :=
  ShortGapGenerationMask.unjoined_gen_has_debt R r s (lineage''_to_lineage' R s hs) hd i hi

/-- The zero-debt part of nonincrease is unconditional in the physical edge.
Positive-debt nonincrease is a separate, unresolved carrier obligation. -/
theorem latentDebt_zero_step (R : RFrame) (r : Nat) (s : GhostRing R)
    (hs : Lineage'' R s) (hd : DenialOnly R r s)
    (hz : latentDebt R r s = 0) (e : Vtx R) :
    latentDebt R r (ghostStep' R s e) = 0 :=
  ShortGapGenerationMask.latentDebt_zero_step R r s (lineage''_to_lineage' R s hs) hd hz e

private theorem forall_three {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ i, P i := by
  intro i
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hv with h | h | h
  · have he : i = 0 := Fin.ext h; exact he ▸ h0
  · have he : i = 1 := Fin.ext h; exact he ▸ h1
  · have he : i = 2 := Fin.ext h; exact he ▸ h2

/-- The known five-event reachable state satisfies both new provenance
directions. Its gap-0 reply has already been cleared at the right root. -/
theorem launchReady_lineage'' : Lineage'' T launchReady := by
  refine ⟨launchReady_lineage.coherent, launchReady_lineage.idleReady, ?_, ?_⟩
  · apply forall_three
    · intro q c d he hc
      rcases he with he | he
      · cases he
        exact False.elim (hc (show 0 < 1 from by decide))
      · cases he
    · intro q c d he _
      rcases he with he | he
      · cases he
      · cases he; rfl
    · intro q c d he
      rcases he with he | he <;> cases he
  · apply forall_three
    · intro h; exact False.elim h
    · intro _; exact ⟨0,.out1,.out1,Or.inr rfl,Or.inl rfl,rfl⟩
    · intro h; exact False.elim h

/-- The cut holds before and after relaunch; it cannot exclude this trace. -/
theorem launchReady_cut : CohortEntered T 1 launchReady ∧
    CohortEntered T 1 (ghostStep' T launchReady (E 1)) :=
  ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

/-- COUNTEREXAMPLE to closure on the requested cut and denial-only domain.
The retained epoch is outbound 1; the right root is still generation 0
with its old denial. Neither current nor previous returning/delivered
epoch exists in the single field, regardless of the allowed generation skew. -/
theorem lineage''_step : Reachable' T launchReady ∧ Lineage'' T launchReady ∧
    DenialOnly T 1 launchReady ∧ CohortEntered T 1 launchReady ∧
    DenialOnly T 1 (ghostStep' T launchReady (E 1)) ∧
    CohortEntered T 1 (ghostStep' T launchReady (E 1)) ∧
    ¬ Lineage'' T (ghostStep' T launchReady (E 1)) := by
  refine ⟨launchReady_reachable, launchReady_lineage'',
    lineage_denialOnly_not_closed.2.2.1, launchReady_cut.1,
    lineage_denialOnly_not_closed.2.2.2.1, launchReady_cut.2, ?_⟩
  intro hs
  obtain ⟨q,c,d,he,_⟩ := hs.rightResult 1 (show CcwHeld
    ((ghostStep' T launchReady (E 1)).cfg (rootV T (next T 1))).ccwPort from trivial)
  rcases he with he | he <;> cases he

/-- Omitting the right-clear guard already fails one event earlier, for
a returning epoch, not only for a retained delivered record. -/
theorem returning_after_right_clear : Reachable' T launchReady ∧
    ResultEpoch (launchReady.epoch 0) 0 .out1 .out1 ∧
    RightCleared T launchReady 0 0 ∧
    (launchReady.cfg (rootV T (next T 0))).ccwPort = some .free :=
  ⟨launchReady_reachable, Or.inl rfl, (show 0 < 1 from by decide), rfl⟩

/-- Both endpoints of the closure counterexample still have unresolved
round-1 roots. Neither round 0 nor round 1 has a virtual candidate. Thus
the stipulated success/failure stops cannot hide the bad successor. -/
theorem relaunch_is_active :
    PeriodHIncidenceChoice.HasRace (wordOf T 1 launchReady) ∧
    PeriodHIncidenceChoice.HasRace (wordOf T 1 (ghostStep' T launchReady (E 1))) ∧
    ¬ VirtualCandidate T 1 launchReady ∧
    ¬ VirtualCandidate T 0 launchReady ∧
    ¬ VirtualCandidate T 1 (ghostStep' T launchReady (E 1)) ∧
    ¬ VirtualCandidate T 0 (ghostStep' T launchReady (E 1)) := by
  have no_in0_before : ∀ i, wordOf T 1 launchReady i ≠ .in0 := by
    apply forall_three <;> decide
  have no_in0_after : ∀ i, wordOf T 1 (ghostStep' T launchReady (E 1)) i ≠ .in0 := by
    apply forall_three <;> decide
  have old_before : ∀ i, wordOf T 0 launchReady i ≠ .in0 := by
    apply forall_three <;> decide
  have old_after : ∀ i, wordOf T 0 (ghostStep' T launchReady (E 1)) i ≠ .in0 := by
    apply forall_three <;> decide
  exact ⟨⟨0,rfl⟩,⟨0,rfl⟩,
    fun ⟨g,hg⟩ => no_in0_before _ hg.2,
    fun ⟨g,hg⟩ => old_before _ hg.2,
    fun ⟨g,hg⟩ => no_in0_after _ hg.2,
    fun ⟨g,hg⟩ => old_after _ hg.2⟩

/-- The invariant subtype requested for the round-r stopped process.
Reachability is not added as a substitute for the failed closure property. -/
def RoundState (R : RFrame) (r : Nat) :=
  {s : GhostRing R // Lineage'' R s ∧ DenialOnly R r s ∧ CohortEntered R r s}

/-- A necessary property of the requested stopped physical refinement:
when neither candidate stop applies and the word remains unresolved, the
next node must contain precisely the actual physical/ghost successor. -/
def PhysicalStoppedRefinement (R : RFrame) (r : Nat)
    (step : RoundState R r → Fin R.n → StopNode (RoundState R r)) : Prop :=
  ∀ s e,
    ¬ VirtualCandidate R r (ghostStep' R s.val (edgeVtx R e)) →
    ¬ VirtualCandidate R (r-1) (ghostStep' R s.val (edgeVtx R e)) →
    PeriodHIncidenceChoice.HasRace (wordOf R r (ghostStep' R s.val (edgeVtx R e))) →
    ∃ t, step s e = .active t ∧ t.val = ghostStep' R s.val (edgeVtx R e)

/-- COUNTEREXAMPLE to forming the stipulated stopped process on this
subtype. This refutes its physical carrier, not a statewise numerical
child-sum inequality or a differently archived invariant. -/
theorem no_cut_stopped_refinement : ¬ ∃ step, PhysicalStoppedRefinement T 1 step := by
  rintro ⟨step, hs⟩
  let s : RoundState T 1 := ⟨launchReady, launchReady_lineage'',
    lineage''_step.2.2.1, launchReady_cut.1⟩
  have he : edgeVtx T (encode T (E 1)) = E 1 := edgeVtx_encE T 1 0
  have hc := hs s (encode T (E 1))
  change (¬ VirtualCandidate T 1 (ghostStep' T launchReady _)) → _ at hc
  rw [he] at hc
  obtain ⟨t,_,ht⟩ := hc relaunch_is_active.2.2.2.2.1
    relaunch_is_active.2.2.2.2.2 relaunch_is_active.2.1
  have hl := t.property.1
  rw [ht] at hl
  exact lineage''_step.2.2.2.2.2.2 hl

/-! The remaining statewise accounting reduces to two explicit debt laws.
Neither law is included in Lineage'', and neither is asserted below as a
general theorem about the literal rows. -/

private theorem sum_strict {n : Nat} (f g : Fin n → Nat) (i : Fin n)
    (hle : ∀ j, f j ≤ g j) (hlt : f i < g i) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons,List.ofFn_succ,List.sum_cons]
    by_cases hi : i = 0
    · subst i
      have ht := ofFn_sum_le (fun j : Fin n => f j.succ) (fun j => g j.succ)
        (fun j => hle j.succ)
      omega
    · have hip : 0 < i.val := by
        have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      let j : Fin n := ⟨i.val-1,by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have ht := ih (fun j : Fin n => f j.succ) (fun j => g j.succ) j
        (fun j => hle j.succ) (by simpa only [hj] using hlt)
      have h0 := hle 0
      omega

/-- Conditional algebraic capstone. A joined Race root supplies reserve
progress; otherwise an unjoined Race root supplies positive debt and the
explicit progress premise supplies the useful physical edge. The two debt
premises remain proof obligations, not a hidden TokenSimulation assumption
or an unconditional result for the cut domain. -/
theorem genPipelined_childSum_of_debt_laws (R : RFrame) (r : Nat) (s : GhostRing R)
    (hs : Lineage'' R s) (hd : DenialOnly R r s)
    (hr : PeriodHIncidenceChoice.HasRace (wordOf R r s))
    (hnoninc : ∀ e, latentDebt R r (ghostStep' R s e) ≤ latentDebt R r s)
    (hprogress : 0 < latentDebt R r s →
      ∃ e, latentDebt R r (ghostStep' R s e) + 1 = latentDebt R r s) :
    1 + (List.ofFn (fun e : Fin R.n => roundDebt R r (ghostStep' R s (edgeVtx R e)))).sum ≤
      R.n * roundDebt R r s := by
  classical
  by_cases hj : ∃ i, wordOf R r s i = .race ∧ genMask R r s i = true
  · exact genPipelined_childSum_of_joined R r s (lineage''_to_lineage' R s hs) hj hnoninc
  · obtain ⟨i,hi⟩ := hr
    have hk : s.k i < r := by
      have hn : ¬ r ≤ s.k i := by
        intro hk
        exact hj ⟨i,hi,by simp [genMask,hk]⟩
      omega
    obtain ⟨e,he⟩ := hprogress (unjoined_gen_has_debt R r s hs hd i hk)
    have hw : ∀ a : Fin R.n,
        PeriodHIncidenceChoice.choiceRaceReserve (wordOf R r (ghostStep' R s (edgeVtx R a))) ≤
          PeriodHIncidenceChoice.choiceRaceReserve (wordOf R r s) := by
      intro a
      rw [wordOf''_step R r s hs]
      exact choiceRaceReserve_joinedIncidenceStep_le _ _ _ _
    have he' : edgeVtx R (encode R e) = e := edgeVtx_encE R e.1 e.2
    have hl := sum_strict
      (fun a : Fin R.n => roundDebt R r (ghostStep' R s (edgeVtx R a)))
      (fun _ => roundDebt R r s) (encode R e)
      (fun a => Nat.add_le_add (hw a) (hnoninc (edgeVtx R a))) (by
        have hv := hw (encode R e)
        rw [he'] at hv ⊢
        unfold roundDebt
        omega)
    rw [ofFn_sum_const] at hl
    omega

/-- The failing invariant transition is not a debt counterexample. At
this reachable cut state all six edges are nonincreasing, and edge E 0
lowers the debt exactly once. This is a finite regression, not the general
arbitrary-gap progress theorem requested in the spec. -/
theorem launchReady_debt_laws :
    (∀ e, latentDebt T 1 (ghostStep' T launchReady e) ≤ latentDebt T 1 launchReady) ∧
    latentDebt T 1 (ghostStep' T launchReady (E 0)) + 1 = latentDebt T 1 launchReady := by
  constructor
  · intro e
    exact latentDebt_step_le_of_simulation T 1 launchReady e (token_steps_launchReady e).1
  · decide

theorem launchReady_childSum :
    1 + (List.ofFn (fun e : Fin T.n =>
      roundDebt T 1 (ghostStep' T launchReady (edgeVtx T e)))).sum ≤
        T.n * roundDebt T 1 launchReady :=
  genPipelined_childSum_of_debt_laws T 1 launchReady launchReady_lineage''
    lineage''_step.2.2.1 relaunch_is_active.1 launchReady_debt_laws.1
    (fun _ => ⟨E 0,launchReady_debt_laws.2⟩)

/-! The numerical cut budget does not depend on the failed closure claim. -/

/-- Every bounded literal carrier has at most 2h-1 remaining firings. -/
theorem token_hops_le {h : Nat} (t : LitGapState h) : t.hops ≤ 2*h-1 := by
  cases t with
  | declareAt j hj => change 2*h-1-j ≤ 2*h-1; omega
  | replyAt j hj => change j ≤ 2*h-1; omega
  | delivered => exact Nat.zero_le _

/-- The service bound holds for every token view, hence also at the cut;
it needs neither a simulation premise nor a receipt invariant. -/
theorem latentDebt_le (R : RFrame) (r : Nat) (s : GhostRing R) :
    latentDebt R r s ≤ R.m * (2*R.h-1) := by
  have he := ofFn_sum_le (fun g => (tokensOf' R r s g).hops)
    (fun _ => 2*R.h-1) (fun g => token_hops_le (tokensOf' R r s g))
  simpa only [latentDebt,litTotalHops,ofFn_sum_const] using he

/-- The requested cut budget has exact factor 2h. This is a numerical
bound, not an expected-time theorem without a Bellman certificate. -/
theorem cut_budget_le (R : RFrame) (r : Nat) (s : GhostRing R) :
    R.n * (R.m + latentDebt R r s) ≤ R.n * R.m * (2*R.h) := by
  have hd := latentDebt_le R r s
  have hh : (2*R.h-1)+1 = 2*R.h := by have hp := R.hh; omega
  have he : R.m + R.m * (2*R.h-1) = R.m * (2*R.h) := by
    calc
      R.m + R.m * (2*R.h-1) = R.m * ((2*R.h-1)+1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ = R.m * (2*R.h) := congrArg (R.m * ·) hh
  have hb : R.m + latentDebt R r s ≤ R.m * (2*R.h) := by omega
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left R.n hb

/-- At a cut the word may already be partially played. Thus n*(m+debt)
is an upper bound for the proposed potential, not necessarily its value. -/
theorem potential_le_cut_budget (R : RFrame) (r : Nat) (s : GhostRing R) :
    R.n * roundDebt R r s ≤ R.n * (R.m + latentDebt R r s) := by
  have hr := ShortGapChoiceStopping.choiceRaceReserve_le (wordOf R r s)
  apply Nat.mul_le_mul_left
  unfold roundDebt
  omega

theorem potential_le_literal_budget (R : RFrame) (r : Nat) (s : GhostRing R) :
    R.n * roundDebt R r s ≤ R.n * R.m * (2*R.h) :=
  Nat.le_trans (potential_le_cut_budget R r s) (cut_budget_le R r s)

/-- With an entirely unresolved word, the cut upper bound is the actual
potential. A general accounting cut alone does not imply this premise. -/
theorem potential_eq_of_all_race (R : RFrame) (r : Nat) (s : GhostRing R)
    (hr : ∀ i, wordOf R r s i = .race) :
    R.n * roundDebt R r s = R.n * (R.m + latentDebt R r s) := by
  simp [roundDebt,PeriodHIncidenceChoice.choiceRaceReserve,hr,ofFn_sum_const]

/-- At the initial round-1 cut every predecessor token is latent, so
the service part attains its m*(2h-1) bound exactly. -/
theorem latentDebt_start (R : RFrame) :
    latentDebt R 1 (ghostStart R) = R.m * (2*R.h-1) := by
  simp [latentDebt,litTotalHops,tokensOf'_start,LitGapState.hops,ofFn_sum_const]

/-- The clean uniform start realizes the numerical literal budget exactly.
This remains a potential identity, not a claimed stopping-time bound. -/
theorem potential_start (R : RFrame) :
    R.n * roundDebt R 1 (ghostStart R) = R.n * R.m * (2*R.h) := by
  rw [potential_eq_of_all_race R 1 (ghostStart R) (fun _ => rfl),latentDebt_start]
  have hh : (2*R.h-1)+1 = 2*R.h := by have hp := R.hh; omega
  have he : R.m + R.m*(2*R.h-1) = R.m*(2*R.h) := by
    calc
      R.m + R.m*(2*R.h-1) = R.m*((2*R.h-1)+1) := by
        rw [Nat.mul_add,Nat.mul_one,Nat.add_comm]
      _ = R.m*(2*R.h) := congrArg (R.m * ·) hh
  rw [he,Nat.mul_assoc]

/-!
Status of the requested general headlines:

* lineage''_step above is a reachable counterexample, not closure.
* latentDebt_step_le and advancing_edge_lowers_latentDebt are not declared:
  the positive-debt, arbitrary-gap physical-row proof remains unresolved.
  Entry monotonicity and a positive token count alone do not prove either.
* genPipelined_childSum is not declared as unconditional; the theorem with
  suffix of_debt_laws proves both algebraic branches with explicit premises.
* genPipelined_natBellmanSuperSolution is not declared: the requested
  physical stopped process on RoundState cannot satisfy even the necessary
  refinement property, as no_cut_stopped_refinement proves. No terminal
  classification was enlarged to discard the offending successor.

In particular, imported names from ShortGapGenerationMask are not reprinted
as if they established the corresponding new cut-domain obligations.
-/

/-- Compared with the abstract 2*n*m*(1+h), the numerical literal bound
2*n*m*h saves exactly 2*n*m. No restart-insurance conclusion is inferred. -/
theorem cut_budget_comparison (R : RFrame) :
    R.n * R.m * (2*R.h) + 2*R.n*R.m = 2*R.n*R.m*(1+R.h) := by
  simp only [Nat.mul_add, Nat.mul_one]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]

#print axioms cohortEntered_step
#print axioms lineage''_start
#print axioms lineage''_step
#print axioms provenance_of_lineage''
#print axioms neighborSkew_of_lineage''
#print axioms wordOf''_step
#print axioms lineage''_to_lineage'
#print axioms unjoined_gen_has_debt
#print axioms latentDebt_zero_step
#print axioms no_cut_stopped_refinement
#print axioms genPipelined_childSum_of_debt_laws
#print axioms launchReady_debt_laws
#print axioms launchReady_childSum
#print axioms latentDebt_le
#print axioms cut_budget_le
#print axioms potential_le_literal_budget
#print axioms potential_start
#print axioms cut_budget_comparison
end ShortGapCohortCut

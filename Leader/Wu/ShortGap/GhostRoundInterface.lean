import Leader.Wu.ShortGap.TwoEpochJoinEffects
import Leader.Wu.ShortGap.PipelinedRearmSpec

/-!
# Literal ghost round interface and service-index audit

The round certificate is instantiated without an additional closure premise.
The service domain below is exactly the one requested by the composition
specification. Its word index and exit cut are audited before any restart
certificate is constructed: word2 r observes history r, whereas the entry
cut CohortEntered2 r requires only generation r-1.
-/
namespace ShortGapGhostComposition
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapLineage ShortGapLineageRetained ShortGapTwoEpoch
open ShortGapDenialTransportLiteral ShortGapGenerationMask
open ShortGapLineage2Closure ShortGapLineage2ClosureB
open FiniteUniformStoppingTree BalancedFailureRestartPartialExitEntry
open ShortGapPipelinedRearmSpec
set_option autoImplicit false

private theorem failureWeight_indicator {S : Type} (x : StopNode S) :
    failureWeight x = @ite Nat (x = .failure) (Classical.propDecidable _) 1 0 := by
  classical
  cases x <;> simp [failureWeight]

private theorem successWeight_indicator {S : Type} (x : StopNode S) :
    successWeight x = @ite Nat (x = .success) (Classical.propDecidable _) 1 0 := by
  classical
  cases x <;> simp [successWeight]

/-- The already proved local balance counts precisely the two stopped
round ports, rather than a different candidate or uniformity predicate. -/
theorem ghostRound_balance (R : RFrame) (r : Nat) (s : Active R r) :
    (List.ofFn (fun e : Fin R.n => failureWeight (ShortGapLineage2ClosureB.stoppedStep R r s e))).sum ≤
      (List.ofFn (fun e : Fin R.n => successWeight (ShortGapLineage2ClosureB.stoppedStep R r s e))).sum := by
  classical
  simp only [failureWeight_indicator,successWeight_indicator,
    ShortGapLineage2ClosureB.stoppedStep_failure_iff,ShortGapLineage2ClosureB.stoppedStep_success_iff]
  exact ShortGapLineage2Closure.genPipelined2_localBalance R r s.val s.property.1 s.property.2

/-- The literal accounting round, with HasRace included in its active
subtype exactly as required by the stopped kernel. -/
noncomputable def ghostRoundSpec (R : RFrame) (r : Nat) : PipelinedRoundSpec R.n where
  Round := Active R r
  step := ShortGapLineage2ClosureB.stoppedStep R r
  potential := stoppedPotential R r
  bellman := genPipelined2_natBellmanSuperSolution R r
  balance := ghostRound_balance R r

/-- The actual round base costs 2nmh, not nm. -/
theorem ghostRound_start (R : RFrame) :
    (ghostRoundSpec R 1).potential (.active (startActive R)) = 2*R.n*R.m*R.h :=
  ShortGapLineage2ClosureB.stoppedPotential_start R

/-- This is the proved single-round bound. It is not a cross-round
bound and does not stop at physical candidate latches. -/
theorem ghostRound_truncatedCost_le (R : RFrame) (T : Nat) :
    truncatedActiveCostNumerator (ghostRoundSpec R 1).step (.active (startActive R)) T ≤
      R.n^T * (2*R.n*R.m*R.h) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (ghostRoundSpec R 1).step 1 (ghostRoundSpec R 1).potential
    (ghostRoundSpec R 1).bellman (.active (startActive R)) T
  simpa only [Nat.one_mul,ghostRound_start] using h

/-- A resolved history word cannot precede its own generation cut.
The proof uses the future-domain clause of lineage, with no reachability
assumption and no uniformity assumption. -/
theorem frozen_word_entered (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (r : Nat) (hf : PeriodHIncidenceChoice.Frozen (word2 R r s)) :
    ∀ i, r ≤ s.k i := by
  intro i
  by_cases h : r ≤ s.k i
  · exact h
  · have hh := hs.coherent.histFuture i r (by change s.k i < r; omega)
    change s.hist i r = none at hh
    have hn := hf i
    exact False.elim (hn (by simp [word2,wordOf,curView,hh,choiceToWord]))

/-- A genuine round failure has already reached the service exit cut
specified in the task. This is stronger than uniformity alone. -/
theorem stopped_failure_next_cut (R : RFrame) (r : Nat) (s : Active R r) (e : Fin R.n)
    (hf : ShortGapLineage2ClosureB.stoppedStep R r s e = .failure) :
    ∀ i, r ≤ (ghostStep2 R s.val (edgeVtx R e)).k i :=
  frozen_word_entered R _ (lineage2_step R s.val s.property.1.1 _ ) r
    ((ShortGapLineage2ClosureB.stoppedStep_failure_iff R r s e).mp hf).1

/-- Exact service domain from the task, retaining Constant as written.
Constant permits the all-Race word; Frozen is a separate predicate. -/
def ServiceDom (R : RFrame) (r : Nat) (s : GhostRing2 R) : Prop :=
  Lineage2 R s ∧ CohortEntered2 R r s ∧ PeriodHIncidenceChoice.Constant (word2 R r s) ∧
    ¬ VirtualSuccess R r s ∧ ∃ i, s.k i < r

/-- Adding the prose's resolved-word requirement makes the requested
service domain empty, because its not-yet-exited condition uses cut r. -/
theorem serviceDom_not_frozen (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : ServiceDom R r s) : ¬ PeriodHIncidenceChoice.Frozen (word2 R r s) := by
  intro hf
  obtain ⟨i,hi⟩ := hs.2.2.2.2
  have hb := frozen_word_entered R s hs.1 r hf i
  omega

/-- Consequently the post-state of a genuine round failure cannot be
the requested service entry state, for any ring or round. -/
theorem stopped_failure_not_serviceDom (R : RFrame) (r : Nat) (s : Active R r) (e : Fin R.n)
    (hf : ShortGapLineage2ClosureB.stoppedStep R r s e = .failure) :
    ¬ ServiceDom R r (ghostStep2 R s.val (edgeVtx R e)) := by
  intro h
  exact serviceDom_not_frozen R r _ h
    ((ShortGapLineage2ClosureB.stoppedStep_failure_iff R r s e).mp hf).1

/-! A reachable test of the domain as literally written. There are two
gaps of length three. Round 0 is the clean uniform out1 round, and history
word 1 is all Race. Debt at index 2 measures round-1 tokens, so it cannot
pay for the first interactions of round 0. -/

def testFrame : RFrame := ⟨2,3,by decide,by decide,.out1,Or.inl rfl⟩

local instance : NeZero testFrame.m := ⟨by decide⟩
local instance : NeZero testFrame.n := ⟨by decide⟩

def testStart : GhostRing2 testFrame := ghostStart2 testFrame

/-- Finite physical scheduler alphabet used by both the trace and tests. -/
def testStep (s : GhostRing2 testFrame) (e : Fin testFrame.n) : GhostRing2 testFrame :=
  ghostStep2 testFrame s (edgeVtx testFrame e)

theorem testStart_reachable : Reachable2 testFrame testStart := ⟨[],rfl⟩

theorem testStart_serviceDom : ServiceDom testFrame 1 testStart := by
  have h := ShortGapLineage2Closure.dom_start testFrame
  exact ⟨h.1,h.2.1,⟨.race,by decide⟩,h.2.2,⟨0,by decide⟩⟩

theorem testStart_debt : latentDebt2 testFrame 2 testStart = 10 := by decide

theorem testStart_child_debt : ∀ e : Fin testFrame.n,
    latentDebt2 testFrame 2 (testStep testStart e) = 10 := by decide

theorem testStart_child_maxGen : ∀ e : Fin testFrame.n,
    maxGen testFrame (testStep testStart e) = 0 := by decide

theorem testStart_child_no_success (e : Fin testFrame.n) :
    ¬ VirtualSuccess testFrame 1 (testStep testStart e) := by
  rintro ⟨q,hq,g,hg⟩
  rw [testStart_child_maxGen e] at hq
  have he : q = 0 := by omega
  subst q
  have hn : ∀ (a : Fin testFrame.n) (i : Fin testFrame.m),
      ¬ PeriodHIncidenceChoice.Candidate10 (ring testFrame) (word2 testFrame 0 (testStep testStart a)) i := by unfold PeriodHIncidenceChoice.Candidate10; decide
  exact hn e g hg

theorem testStart_child_not_exit : ∀ e : Fin testFrame.n,
    ¬ (∀ i, 1 ≤ (testStep testStart e).k i) := by decide

/-- Every immediate child remains in the literal service domain. Thus
neither a sidecar success nor the specified cut can erase this debt. -/
theorem testStart_child_serviceDom (e : Fin testFrame.n) :
    ServiceDom testFrame 1 (testStep testStart e) := by
  refine ⟨lineage2_step testFrame testStart testStart_serviceDom.1 _,
    cohortEntered2_step testFrame 1 testStart _ testStart_serviceDom.2.1,?_,
    testStart_child_no_success e,?_⟩
  · exact ⟨.race,(by decide : ∀ a : Fin testFrame.n, ∀ i,
      word2 testFrame 1 (testStep testStart a) i = .race) e⟩
  · exact (by decide : ∀ a : Fin testFrame.n, ∃ i, (testStep testStart a).k i < 1) e

/-- The advertised service potential violates the required child sum:
6 + 6*60 = 366, while 6*60 = 360. -/
theorem testStart_service_bellman_false :
    ¬ (testFrame.n + (List.ofFn (fun e : Fin testFrame.n =>
      testFrame.n * latentDebt2 testFrame 2 (testStep testStart e))).sum ≤
        testFrame.n * (testFrame.n * latentDebt2 testFrame 2 testStart)) := by decide

abbrev ServiceState (R : RFrame) (r : Nat) := {s : GhostRing2 R // ServiceDom R r s}

/-- Exact potential requested for service at accounting index r. -/
def servicePotential (R : RFrame) (r : Nat) (s : ServiceState R r) : Nat :=
  R.n * latentDebt2 R (r+1) s.val

/-- Necessary properties of the specified literal service kernel.
Continuation preserves the actual ghost child; exit requires the stated
cut; the success port requires the actual virtual candidate. -/
def LiteralServiceOutcome {Round : Type} (R : RFrame) (r : Nat)
    (s : ServiceState R r) (e : Fin R.n) : ServiceOutcome (ServiceState R r) Round → Prop
  | .cont t => t.val = ghostStep2 R s.val (edgeVtx R e)
  | .exit _ => ∀ i, r ≤ (ghostStep2 R s.val (edgeVtx R e)).k i
  | .succeed => VirtualSuccess R r (ghostStep2 R s.val (edgeVtx R e))

/-- No kernel satisfying even these necessary physical outcome rules
can have the advertised service Bellman certificate on ServiceDom.
The witness is the reachable clean start, not a fabricated ghost state. -/
theorem literal_service_bellman_impossible {Round : Type}
    (step : ServiceState testFrame 1 → Fin testFrame.n → ServiceOutcome (ServiceState testFrame 1) Round)
    (hstep : ∀ e, LiteralServiceOutcome testFrame 1 ⟨testStart,testStart_serviceDom⟩ e
      (step ⟨testStart,testStart_serviceDom⟩ e)) :
    ¬ ServiceBellman step 1 (servicePotential testFrame 1) := by
  intro hb
  let s : ServiceState testFrame 1 := ⟨testStart,testStart_serviceDom⟩
  have hp : ∀ e : Fin testFrame.n,
      serviceOutcomePotential (servicePotential testFrame 1) (step s e) =
        testFrame.n * latentDebt2 testFrame 2 (testStep testStart e) := by
    intro e
    have hh := hstep e
    cases he : step s e with
    | succeed =>
      exact False.elim (testStart_child_no_success e (by simpa only [he,LiteralServiceOutcome,s,testStep] using hh))
    | exit t =>
      exact False.elim (testStart_child_not_exit e (by simpa only [he,LiteralServiceOutcome,s,testStep] using hh))
    | cont t =>
      have ht : t.val = testStep testStart e := by simpa only [he,LiteralServiceOutcome,s,testStep] using hh
      change testFrame.n * latentDebt2 testFrame 2 t.val = _
      rw [ht]
  have heq := FiniteUniformStoppingTree.ofFn_sum_eq _ _ hp
  have hh := hb s
  rw [Nat.one_mul,heq] at hh
  exact testStart_service_bellman_false hh

/-! A second reachable witness: the literal Constant-only service
domain is not even closed under the required continuation transition. -/

def testTrace : List (Vtx testFrame) :=
  [edgeVtx testFrame 0,edgeVtx testFrame 1,edgeVtx testFrame 2,
   edgeVtx testFrame 3,edgeVtx testFrame 4,edgeVtx testFrame 5,
   edgeVtx testFrame 4,edgeVtx testFrame 3]

def testBeforeResolve : GhostRing2 testFrame := run2 testFrame testStart testTrace

/-- Closure B transports genuine lineage along every finite literal trace. -/
theorem lineage2_run (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (es : List (Vtx R)) :
    Lineage2 R (run2 R s es) := by
  induction es generalizing s with
  | nil => exact hs
  | cons e es ih => exact ih _ (lineage2_step R s hs e)

theorem testBeforeResolve_reachable : Reachable2 testFrame testBeforeResolve := ⟨testTrace,rfl⟩

theorem testBeforeResolve_counters :
    testBeforeResolve.k 0 = 0 ∧ testBeforeResolve.k 1 = 1 := by decide

private theorem testResolve_no_success (a : Bool) :
    ¬ VirtualSuccess testFrame 1 (if a then testStep testBeforeResolve 3 else testBeforeResolve) := by
  rintro ⟨q,hq,g,hg⟩
  have hm : maxGen testFrame (if a then testStep testBeforeResolve 3 else testBeforeResolve) = 1 := by
    cases a <;> decide
  rw [hm] at hq
  have hn : ∀ (b : Bool) (j : Fin 2) (i : Fin testFrame.m),
      ¬ PeriodHIncidenceChoice.Candidate10 (ring testFrame)
        (word2 testFrame j.val (if b then testStep testBeforeResolve 3 else testBeforeResolve)) i := by unfold PeriodHIncidenceChoice.Candidate10; decide
  exact hn a ⟨q,by omega⟩ g hg

theorem testBeforeResolve_serviceDom : ServiceDom testFrame 1 testBeforeResolve :=
  ⟨lineage2_run testFrame testStart testStart_serviceDom.1 testTrace,
    (by intro i; exact Nat.zero_le _),⟨.race,by decide⟩,
    testResolve_no_success false,⟨0,by decide⟩⟩

/-- Resolving the joined root makes word 1 mixed Race/out1, while the
other root remains at generation 0 and no virtual candidate exists. -/
theorem testResolve_no_legal_outcome :
    ¬ VirtualSuccess testFrame 1 (testStep testBeforeResolve 3) ∧
    ¬ (∀ i, 1 ≤ (testStep testBeforeResolve 3).k i) ∧
    ¬ ServiceDom testFrame 1 (testStep testBeforeResolve 3) := by
  refine ⟨testResolve_no_success true,by decide,?_⟩
  intro h
  obtain ⟨c,hc⟩ := h.2.2.1
  have hn : word2 testFrame 1 (testStep testBeforeResolve 3) 0 ≠
      word2 testFrame 1 (testStep testBeforeResolve 3) 1 := by decide
  exact hn ((hc 0).trans (hc 1).symm)

/-- The reachable mixed-word child rules out every literal service
kernel on the exact domain, independently of its potential. -/
theorem literal_service_kernel_impossible {Round : Type}
    (step : ServiceState testFrame 1 → Fin testFrame.n → ServiceOutcome (ServiceState testFrame 1) Round)
    (hstep : ∀ s e, LiteralServiceOutcome testFrame 1 s e (step s e)) : False := by
  let s : ServiceState testFrame 1 := ⟨testBeforeResolve,testBeforeResolve_serviceDom⟩
  have hh := hstep s 3
  have hn := testResolve_no_legal_outcome
  cases he : step s 3 with
  | succeed => exact hn.1 (by simpa only [he,LiteralServiceOutcome,s,testStep] using hh)
  | exit t => exact hn.2.1 (by simpa only [he,LiteralServiceOutcome,s,testStep] using hh)
  | cont t =>
    have ht : t.val = testStep testBeforeResolve 3 := by
      simpa only [he,LiteralServiceOutcome,s,testStep] using hh
    exact hn.2.2 (ht ▸ t.property)

/-- This explicitly corrected cut drains round r until generation r+1.
It is recorded as a repair lemma, not substituted for ServiceDom. -/
theorem frozen_service_debt_laws (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (hf : PeriodHIncidenceChoice.Frozen (word2 R r s))
    (hn : ¬ VirtualSuccess R r s) (hwait : ∃ i, s.k i < r+1) :
    (∀ e, latentDebt2 R (r+1) (ghostStep2 R s e) ≤ latentDebt2 R (r+1) s) ∧
    ∃ e, latentDebt2 R (r+1) (ghostStep2 R s e) + 1 = latentDebt2 R (r+1) s := by
  have hd : Dom R (r+1) s := ⟨hs,by
    intro i
    simpa only [Nat.add_sub_cancel] using frozen_word_entered R s hs r hf i,hn⟩
  have ho := dom_accounting R (r+1) s hd
  obtain ⟨i,hi⟩ := hwait
  exact ⟨ShortGapTwoEpochLaws.latentDebt2_step_le R (r+1) s ho,
    ShortGapTwoEpochLaws.advancing_edge_lowers_latentDebt2 R (r+1) s ho
      (ShortGapTwoEpochLaws.unjoined_debt_on_dom R (r+1) s ho i hi)⟩

/-! A genuine reachable failure also witnesses the service-entry mismatch. -/

def testFailureTrace : List (Vtx testFrame) := testTrace ++
  [edgeVtx testFrame 3,edgeVtx testFrame 1,edgeVtx testFrame 0]

def testFailureBefore : GhostRing2 testFrame := run2 testFrame testStart testFailureTrace

private theorem no_success_at_max_one (s : GhostRing2 testFrame)
    (hm : maxGen testFrame s = 1)
    (hc : ∀ (q : Fin 2) (g : Fin testFrame.m),
      ¬ PeriodHIncidenceChoice.Candidate10 (ring testFrame) (word2 testFrame q.val s) g) :
    ¬ VirtualSuccess testFrame 1 s := by
  rintro ⟨q,hq,g,hg⟩
  rw [hm] at hq
  exact hc ⟨q,by omega⟩ g hg

def testFailureActive : Active testFrame 1 :=
  ⟨testFailureBefore,
    ⟨lineage2_run testFrame testStart testStart_serviceDom.1 testFailureTrace,
      (by intro i; exact Nat.zero_le _),no_success_at_max_one _ (by decide)
        (by unfold PeriodHIncidenceChoice.Candidate10; decide)⟩,
    ⟨0,by decide⟩⟩

theorem testFailureBefore_reachable : Reachable2 testFrame testFailureBefore := ⟨testFailureTrace,rfl⟩

/-- This actual failing round edge is reachable from the clean start. -/
theorem testFailure_is_failure :
    ShortGapLineage2ClosureB.stoppedStep testFrame 1 testFailureActive 0 = .failure := by
  apply (ShortGapLineage2ClosureB.stoppedStep_failure_iff testFrame 1 testFailureActive 0).mpr
  exact ⟨(by unfold PeriodHIncidenceChoice.Frozen; decide),
    no_success_at_max_one _ (by decide) (by unfold PeriodHIncidenceChoice.Candidate10; decide)⟩

/-- Its physical child cannot be used as the requested service entry. -/
theorem testFailure_entry_impossible :
    ¬ ServiceDom testFrame 1 (testStep testFailureBefore 0) :=
  stopped_failure_not_serviceDom testFrame 1 testFailureActive 0 testFailure_is_failure

/-!
STALL REPORT: the requested Stage A service is refuted, not merely missing
a proof. A Frozen word2 r forces all counters to be at least r, contradicting
the specified pending-service condition. Constant alone admits the reachable
clean start where the proposed Bellman inequality is 366 <= 360, and a
reachable continuation can leave Constant without reaching either port.

The actual round interface and its single-round bound 2*n*m*h are proved.
No ghostRearmSpec, cross-round cost bound, or realization/end-to-end bound
is asserted. Stage B is not started because the task requires Stage A first.

The service-index repair indicated by the checked debt laws is: require
Frozen word2 r and wait for all k >= r+1, using latentDebt2 (r+1). A full
composition also needs a round state carrying its accounting index, since
the restart interface returns to the same Round type while the next index
changes. Neither repair is silently installed as the requested theorem.
-/

#print axioms ghostRoundSpec
#print axioms ghostRound_balance
#print axioms ghostRound_start
#print axioms ghostRound_truncatedCost_le
#print axioms frozen_word_entered
#print axioms stopped_failure_next_cut
#print axioms stopped_failure_not_serviceDom
#print axioms serviceDom_not_frozen
#print axioms testStart_reachable
#print axioms testStart_service_bellman_false
#print axioms literal_service_bellman_impossible
#print axioms testBeforeResolve_reachable
#print axioms testResolve_no_legal_outcome
#print axioms literal_service_kernel_impossible
#print axioms frozen_service_debt_laws
#print axioms testFailureBefore_reachable
#print axioms testFailure_is_failure
#print axioms testFailure_entry_impossible

end ShortGapGhostComposition

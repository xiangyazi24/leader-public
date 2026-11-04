import Leader.L3.CleanTargetClosure
import Leader.L3.Headline.Rendezvous
import Leader.L3.Grant.LeaderlessShort

/-!
The clean-target reduction of L3Headline.

Scope: first-hit producer contracts are intended only for
(compileAdvice (ceilLogTwo n)).t <= 17.
The old monitor-based rooted renewal clock is NOT assumed to imply
the clean rooted-renewal clock.  No all-Cartesian first-hit producer
is manufactured in this file.

Every hitting-time assertion concerns the SAME real uniform Fin n
physical scheduler. The old endpoint may be reused as a *physical
intermediate milestone*, never as a clean accepted word.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Clean six-factor terminal class on headline physical states.
Consumer: every clean stage and l3HeadlineOfCleanFirstHit. -/
def headlineCleanTarget {n : Nat}
    (ring : DirectedRing n) : HeadlineConfiguration n → Prop :=
  Gclean (q := ceilLogTwo n) ring

/-- Clean form of the generated closure stage, discharged by
cleanTargetClosed. Consumer: headline first-hit assembly. -/
def StageCleanGeneratedClosure {n : Nat}
    (ring : DirectedRing n) : Prop :=
  PopulationProtocol.ClosedPred
    (protocol (ceilLogTwo n)) ring (headlineCleanTarget ring)

/-- Clean form of the generated safety stage, discharged by
cleanTargetSafe. Consumer: headline first-hit assembly. -/
def StageCleanGeneratedSafety {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n,
    headlineCleanTarget ring C →
    PopulationProtocol.IsSafe
      (protocol (ceilLogTwo n)) ring C (fun b => b)

/-- The unchanged alphabet budget and an all-Cartesian clean first-hit
certificate give the actual existential G of L3Headline.
Consumer: l3HeadlineOfCleanStages. -/
theorem l3HeadlineOfCleanFirstHit {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbudget : StageAlphabetBudget n)
    (hfirst : ∀ C0 : HeadlineConfiguration n,
      UniformFirstHit.ExpectedHittingTimeAtMost
        (headlinePhysicalNext ring)
        (headlineCleanTarget ring) C0
        ((linearLeaseBound n : Nat) : Rat)) :
    L3Headline ring := by
  unfold L3Headline
  refine ⟨hbudget, headlineCleanTarget ring,
    cleanTargetClosed hn ring, ?_, hfirst⟩
  intro C hC
  exact cleanTargetSafe hn ring C hC

/-! Five physical timing stages with the clean target replacing
the previous monitor endpoint. Their intermediate physical cuts,
budgets, and scheduler remain the same. -/

/-- First purified cut or clean target. -/
def StageCleanNativePurification {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n,
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlinePurified ring D ∨ headlineCleanTarget ring D)
      C ((2 * n ^ 2 : Nat) : Rat)

/-- First grant-ready cut or clean target. -/
def StageCleanFirstGrant {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlinePurified ring C →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineGrantReady ring D ∨ headlineCleanTarget ring D)
      C ((headlinePermitRate n * n ^ 2 : Nat) : Rat)

/-- First request-ready cut or clean target. -/
def StageCleanRequestChecker {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlineGrantReady ring C →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineRequestReady ring D ∨ headlineCleanTarget ring D)
      C (((headlineCheckerRate n + 1) * n ^ 2 : Nat) : Rat)

/-- First rooted protected cut or clean target. -/
def StageCleanFirstProtectedBirth {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlineRequestReady ring C →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineRooted ring D ∨ headlineCleanTarget ring D)
      C ((n ^ 2 : Nat) : Rat)

/-- Rooted renewal to the clean terminal class, not AcceptedWord. -/
def StageCleanRootedRenewal {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlineRooted ring C →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring) (headlineCleanTarget ring) C
      ((headlineRenewalRate n * n ^ 2 : Nat) : Rat)

/-- The Q9 residual, changing only its terminal clean disjunct. -/
def StageCleanRequestMissingClock {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n,
    headlineGrantReady ring C →
    (∀ i : Fin n, (C i).l = false) →
    (∀ i : Fin n, (C i).req = false) →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineRequestReady ring D ∨ headlineCleanTarget ring D)
      C (((headlineCheckerRate n + 1) * n ^ 2 : Nat) : Rat)

/-- The R14 residual: an exact costNumerator bound for the
physical first hit of Gclean. This is not the old R14 premise. -/
def StageCleanRootedRenewalCost {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlineRooted ring C →
    ∀ T : Nat,
      costNumerator (headlinePhysicalNext ring)
        (headlineCleanTarget ring) C T ≤
        n ^ T * (headlineRenewalRate n * n ^ 2)

/-! An accepted old-monitor target is *already physically rooted*.
This is sufficient to migrate the earlier-stage union clocks by
target monotonicity, without claiming AcceptedWord -> CleanWord. -/

/-- Existing old target entails an actual protected root.
Consumer: migration of purification/grant/checker/birth clocks. -/
theorem headlineMonitorTargetRooted {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (h : headlineGeneratedTarget ring C) :
    headlineRooted ring C := by
  change Closure.targetSet (q := ceilLogTwo n) ring C at h
  change Protected ring (nativeProjection C) ∧
    (∃ i : Fin n, (C i).l = true)
  refine ⟨h.1.2.1, ?_⟩
  obtain ⟨root, hroot, _⟩ := h.1.1
  exact ⟨root, hroot⟩

/-- Old target is also purified. Consumer: clean purification. -/
theorem headlineMonitorTargetPurified {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (h : headlineGeneratedTarget ring C) :
    headlinePurified ring C := by
  have hroot := headlineMonitorTargetRooted ring C h
  change P ring (nativeProjection C) ∧
    ((∃ i : Fin n, (C i).l = true) →
      Protected ring (nativeProjection C))
  exact ⟨hroot.1.2, fun _ => hroot.1⟩

/-- Old target is grant-ready by its native leader.
Consumer: clean grant stage. -/
theorem headlineMonitorTargetGrantReady {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (h : headlineGeneratedTarget ring C) :
    headlineGrantReady ring C := by
  have hroot := headlineMonitorTargetRooted ring C h
  obtain ⟨root, hr⟩ := hroot.2
  exact Or.inl ⟨root, hr, hroot.1⟩

/-- Old target is request-ready via the protected-root disjunct,
even when OLD req is zero. Consumer: Q9 legacy-to-clean bridge. -/
theorem headlineMonitorTargetRequestReady {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (h : headlineGeneratedTarget ring C) :
    headlineRequestReady ring C := by
  have hroot := headlineMonitorTargetRooted ring C h
  obtain ⟨root, hr⟩ := hroot.2
  exact Or.inl ⟨root, hr, hroot.1⟩

/-- Target inclusion on the real physical chain.
Consumer: four old-to-clean milestone stage transports. -/
private theorem headlineCleanStageTargetMono {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (A B : HeadlineConfiguration n → Prop)
    (hAB : ∀ D, A D → B D)
    (C : HeadlineConfiguration n) (bound : Nat)
    (h : UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring) A C (bound : Rat)) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring) B C (bound : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) B
    (by omega : 0 < n) C bound).2
  intro T
  exact Nat.le_trans
    (Prob.costNumerator_target_mono
      (headlinePhysicalNext ring) A B hAB C T)
    ((UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (headlinePhysicalNext ring) A
      (by omega : 0 < n) C bound).1 h T)

/-- Any initially satisfied physical terminal predicate has
zero waiting cost. Consumer: checker-stage zero cases. -/
private theorem headlineCleanStageAtTarget {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (P : HeadlineConfiguration n → Prop)
    (C : HeadlineConfiguration n) (hP : P C) (bound : Nat) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring) P C (bound : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) P
    (by omega : 0 < n) C bound).2
  intro T
  cases T with
  | zero =>
      simp only [costNumerator_zero]
      exact Nat.zero_le _
  | succ T =>
      rw [costNumerator_terminal
        (headlinePhysicalNext ring) P C hP (T + 1)]
      exact Nat.zero_le _

/-- The already-green purification clock transfers unchanged,
since old monitor target implies purified. Consumer:
l3HeadlineOfCleanRequestAndRenewal. -/
theorem stageCleanNativePurificationProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    StageCleanNativePurification ring := by
  intro C
  apply headlineCleanStageTargetMono ring hn
    (fun D => headlinePurified ring D ∨ headlineGeneratedTarget ring D)
    (fun D => headlinePurified ring D ∨ headlineCleanTarget ring D)
    (fun D hd => hd.elim Or.inl
      (fun hold => Or.inl (headlineMonitorTargetPurified ring D hold)))
    C (2 * n ^ 2)
  exact (stageNativePurification_proved ring hn) C

/-- The already-green grant clock transfers unchanged,
since old monitor target implies grant-ready. Consumer:
l3HeadlineOfCleanRequestAndRenewal. -/
theorem stageCleanFirstGrantProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    StageCleanFirstGrant ring := by
  intro C hpurified
  apply headlineCleanStageTargetMono ring hn
    (fun D => headlineGrantReady ring D ∨ headlineGeneratedTarget ring D)
    (fun D => headlineGrantReady ring D ∨ headlineCleanTarget ring D)
    (fun D hd => hd.elim Or.inl
      (fun hold => Or.inl (headlineMonitorTargetGrantReady ring D hold)))
    C (headlinePermitRate n * n ^ 2)
  exact (stageFirstGrantAll ring hn) C hpurified

/-- The already-green physical protected-birth clock transfers
unchanged, since old target implies rooted. Consumer:
l3HeadlineOfCleanRequestAndRenewal. -/
theorem stageCleanFirstProtectedBirthProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    StageCleanFirstProtectedBirth ring := by
  intro C hready
  apply headlineCleanStageTargetMono ring hn
    (fun D => headlineRooted ring D ∨ headlineGeneratedTarget ring D)
    (fun D => headlineRooted ring D ∨ headlineCleanTarget ring D)
    (fun D hd => hd.elim Or.inl
      (fun hold => Or.inl (headlineMonitorTargetRooted ring D hold)))
    C (n ^ 2)
  exact (stageFirstProtectedBirth_of_rendezvous ring hn
    (stageBirthTokenRendezvous_proved ring hn)) C hready

/-- Q9 itself needs no clean-word mathematics: its old target
already ends the checker phase at request-ready. This is a
conditional transport, NOT a proof of missing Q9. Consumer:
l3HeadlineOfRequestAndCleanRenewal. -/
theorem stageCleanRequestMissingClockOfMonitor {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hclock : StageRequestMissingClock ring) :
    StageCleanRequestMissingClock ring := by
  intro C hgrant hnoLeader hnoRequest
  apply headlineCleanStageTargetMono ring hn
    (fun D => headlineRequestReady ring D ∨ headlineGeneratedTarget ring D)
    (fun D => headlineRequestReady ring D ∨ headlineCleanTarget ring D)
    (fun D hd => hd.elim Or.inl
      (fun hold => Or.inl (headlineMonitorTargetRequestReady ring D hold)))
    C ((headlineCheckerRate n + 1) * n ^ 2)
  exact hclock C hgrant hnoLeader hnoRequest

/-- Clean Q9 gives the whole checker stage; an already-rooted or
already-requested cut costs zero. Consumer:
l3HeadlineOfCleanRequestAndRenewal. -/
theorem stageCleanRequestCheckerOfMissingClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hclock : StageCleanRequestMissingClock ring) :
    StageCleanRequestChecker ring := by
  intro C hgrantReady
  by_cases hleader : ∃ i : Fin n, (C i).l = true
  · have hprotected :
        ∃ i : Fin n, (C i).l = true ∧
          Protected ring (nativeProjection C) := by
      rcases hgrantReady with hroot | htokens
      · exact hroot
      · obtain ⟨hpurified, _⟩ := htokens
        obtain ⟨i, hi⟩ := hleader
        exact ⟨i, hi, hpurified.2 ⟨i, hi⟩⟩
    exact headlineCleanStageAtTarget ring hn
      (fun D => headlineRequestReady ring D ∨ headlineCleanTarget ring D)
      C (Or.inl (Or.inl hprotected))
      ((headlineCheckerRate n + 1) * n ^ 2)
  · by_cases hrequest : ∃ i : Fin n, (C i).req = true
    · have hready : headlineRequestReady ring C := by
        rcases hgrantReady with hroot | htokens
        · exact Or.inl hroot
        · exact Or.inr ⟨htokens.1, htokens.2, hrequest⟩
      exact headlineCleanStageAtTarget ring hn
        (fun D => headlineRequestReady ring D ∨ headlineCleanTarget ring D)
        C (Or.inl hready)
        ((headlineCheckerRate n + 1) * n ^ 2)
    · have hnoLeader : ∀ i : Fin n, (C i).l = false := by
        intro i
        cases hi : (C i).l with
        | false => rfl
        | true => exact False.elim (hleader ⟨i, hi⟩)
      have hnoRequest : ∀ i : Fin n, (C i).req = false := by
        intro i
        cases hi : (C i).req with
        | false => rfl
        | true => exact False.elim (hrequest ⟨i, hi⟩)
      exact hclock C hgrantReady hnoLeader hnoRequest

/-- A clean R14 finite-horizon numerator certificate gives the
corresponding almost-sure rooted entrance. Consumer:
l3HeadlineOfCleanRequestAndRenewal. -/
theorem stageCleanRootedRenewalOfCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hcost : StageCleanRootedRenewalCost ring) :
    StageCleanRootedRenewal ring := by
  intro C hroot
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) (headlineCleanTarget ring)
    (by omega : 0 < n) C
    (headlineRenewalRate n * n ^ 2)).2
  exact hcost C hroot

/-- Actual-scheduler Markov composition of a physical stage
and its clean-target continuation. Consumer:
l3HeadlineOfCleanStages, paper renewal first-hit composition. -/
private theorem headlineCleanComposeRates {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (A B : HeadlineConfiguration n → Prop) (a b : Nat)
    (hfirst : ∀ C : HeadlineConfiguration n, A C →
      UniformFirstHit.ExpectedHittingTimeAtMost
        (headlinePhysicalNext ring)
        (fun D => B D ∨ headlineCleanTarget ring D)
        C ((a * n ^ 2 : Nat) : Rat))
    (hsecond : ∀ C : HeadlineConfiguration n, B C →
      UniformFirstHit.ExpectedHittingTimeAtMost
        (headlinePhysicalNext ring) (headlineCleanTarget ring)
        C ((b * n ^ 2 : Nat) : Rat)) :
    ∀ C : HeadlineConfiguration n, A C →
      UniformFirstHit.ExpectedHittingTimeAtMost
        (headlinePhysicalNext ring) (headlineCleanTarget ring)
        C (((a + b) * n ^ 2 : Nat) : Rat) := by
  intro C hA
  have hstage := Prob.expectedHittingTimeAtMost_stage_le
    (headlinePhysicalNext ring) (by omega : 0 < n)
    C B (headlineCleanTarget ring) (a * n ^ 2) (b * n ^ 2)
    (hfirst C hA) hsecond
  simpa only [Nat.add_mul] using hstage

/-- Analogue of l3Headline_of_stages using only target-swapped
stage interfaces plus merged Gclean closure/safety.
Consumer: the clean Q9/R14 reduction. -/
theorem l3HeadlineOfCleanStages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hpurify : StageCleanNativePurification ring)
    (hgrant : StageCleanFirstGrant ring)
    (hrequest : StageCleanRequestChecker ring)
    (hbirth : StageCleanFirstProtectedBirth ring)
    (hrenew : StageCleanRootedRenewal ring) :
    L3Headline ring := by
  have hready :
      ∀ C : HeadlineConfiguration n,
        headlineRequestReady ring C →
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineCleanTarget ring)
          C (((1 + headlineRenewalRate n) * n ^ 2 : Nat) : Rat) := by
    exact headlineCleanComposeRates ring hn
      (headlineRequestReady ring) (headlineRooted ring)
      1 (headlineRenewalRate n)
      (fun C hC => by simpa only [Nat.one_mul] using hbirth C hC) hrenew
  have hgrantReady :
      ∀ C : HeadlineConfiguration n,
        headlineGrantReady ring C →
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineCleanTarget ring)
          C ((((headlineCheckerRate n + 1) +
            (1 + headlineRenewalRate n)) * n ^ 2 : Nat) : Rat) := by
    exact headlineCleanComposeRates ring hn
      (headlineGrantReady ring) (headlineRequestReady ring)
      (headlineCheckerRate n + 1) (1 + headlineRenewalRate n)
      hrequest hready
  have hpurified :
      ∀ C : HeadlineConfiguration n,
        headlinePurified ring C →
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineCleanTarget ring)
          C (((headlinePermitRate n +
            ((headlineCheckerRate n + 1) +
              (1 + headlineRenewalRate n))) * n ^ 2 : Nat) : Rat) := by
    exact headlineCleanComposeRates ring hn
      (headlinePurified ring) (headlineGrantReady ring)
      (headlinePermitRate n)
      ((headlineCheckerRate n + 1) + (1 + headlineRenewalRate n))
      hgrant hgrantReady
  have hall :
      ∀ C : HeadlineConfiguration n,
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineCleanTarget ring)
          C (((2 + (headlinePermitRate n +
            ((headlineCheckerRate n + 1) +
              (1 + headlineRenewalRate n)))) * n ^ 2 : Nat) : Rat) := by
    intro C
    exact headlineCleanComposeRates ring hn
      (fun _ => True) (headlinePurified ring)
      2 (headlinePermitRate n +
        ((headlineCheckerRate n + 1) +
          (1 + headlineRenewalRate n)))
      (fun D _ => hpurify D) hpurified C True.intro
  have hrate :
      2 + (headlinePermitRate n +
        ((headlineCheckerRate n + 1) +
          (1 + headlineRenewalRate n))) =
        headlineStageRate n := by
    unfold headlineStageRate
    omega
  have hfirst :
      ∀ C0 : HeadlineConfiguration n,
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineCleanTarget ring)
          C0 ((linearLeaseBound n : Nat) : Rat) := by
    intro C0
    have htotal :
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineCleanTarget ring)
          C0 ((headlineStageCost n : Nat) : Rat) := by
      simpa only [headlineStageCost, hrate] using hall C0
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (headlinePhysicalNext ring) (headlineCleanTarget ring)
      (by omega : 0 < n) C0 (linearLeaseBound n)).2
    have hraw := (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (headlinePhysicalNext ring) (headlineCleanTarget ring)
      (by omega : 0 < n) C0 (headlineStageCost n)).1 htotal
    intro T
    exact Nat.le_trans (hraw T)
      (Nat.mul_le_mul_left (n ^ T)
        (headlineStageCost_le_linearLeaseBound n hn))
  exact l3HeadlineOfCleanFirstHit ring hn
    (stageAlphabetBudget_of_stateCount n hn) hfirst

/-- Two clean timing hypotheses suffice after the green physical
purification, grant, and protected-birth producer theorems.
This is conditional, not a proof of the clean R14 clock. -/
theorem l3HeadlineOfCleanRequestAndRenewal {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hrequest : StageCleanRequestMissingClock ring)
    (hcost : StageCleanRootedRenewalCost ring) :
    L3Headline ring :=
  l3HeadlineOfCleanStages ring hn
    (stageCleanNativePurificationProved ring hn)
    (stageCleanFirstGrantProved ring hn)
    (stageCleanRequestCheckerOfMissingClock ring hn hrequest)
    (stageCleanFirstProtectedBirthProved ring hn)
    (stageCleanRootedRenewalOfCost ring hn hcost)

/-- The original Q9 contract itself suffices for the clean path,
since a hit of the old monitor endpoint already hits the physical
request-ready cut. The R14 endpoint remains genuinely changed. -/
theorem l3HeadlineOfRequestAndCleanRenewal {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hrequest : StageRequestMissingClock ring)
    (hcost : StageCleanRootedRenewalCost ring) :
    L3Headline ring :=
  l3HeadlineOfCleanRequestAndRenewal ring hn
    (stageCleanRequestMissingClockOfMonitor ring hn hrequest) hcost

end L3

#print axioms L3.l3HeadlineOfCleanFirstHit
#print axioms L3.headlineMonitorTargetRooted
#print axioms L3.headlineMonitorTargetPurified
#print axioms L3.headlineMonitorTargetGrantReady
#print axioms L3.headlineMonitorTargetRequestReady
#print axioms L3.stageCleanNativePurificationProved
#print axioms L3.stageCleanFirstGrantProved
#print axioms L3.stageCleanFirstProtectedBirthProved
#print axioms L3.stageCleanRequestMissingClockOfMonitor
#print axioms L3.stageCleanRequestCheckerOfMissingClock
#print axioms L3.stageCleanRootedRenewalOfCost
#print axioms L3.l3HeadlineOfCleanStages
#print axioms L3.l3HeadlineOfCleanRequestAndRenewal
#print axioms L3.l3HeadlineOfRequestAndCleanRenewal

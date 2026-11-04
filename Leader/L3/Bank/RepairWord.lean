import Leader.L3.Bank.FinishRepair

/-!
A protected BANK finish word-phase route audit.

The first W clock is reduced to an accepted-W first-hit estimate
on the true projected phiW chain. The reference successor remains
the original stamped, masked BANK chain; no generated epoch or
accepted receipt is fabricated by an unproved definition.

No existing file is modified.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! E.G17, with the concrete accepted decoration and QWord
safety conjunct; legacy WZero alone is not this endpoint. -/

def BankWordProjectedTarget {n : Nat}
    (ring : DirectedRing n)
    (p : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  AcceptedReceipts.AcceptedWord ring
    (BlockA.wordT ring) (BlockA.wordValidated ring) p

/-- The genuinely missing projected-phiW P.1-style first-hit
producer. It includes hard validation, canonical worker completion,
finite-monitor acceptance, and the closed safety certificate.
The rate is 5 * 11 * (8*s+5) = 440*s+275. -/
def BankWordProjectedClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankPreparedAtSomeRoot ring hbank z →
    ∀ T : Nat,
      costNumerator (phiW ring)
        (BankWordProjectedTarget ring) (piW z.val.1) T ≤
      n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2)

/-! Masking changes only req/grant; the two old W endpoints
are the same as those of the ordinary full protocol. -/

private theorem bankWordMaskedPairFrame (c : Compiled)
    (suppress : Bool) (x y : Agent c) :
    ProjW.ofAgent (renewalMaskedPair c suppress x y).1 =
      ProjW.ofAgent (transition c x y).1 ∧
    ProjW.ofAgent (renewalMaskedPair c suppress x y).2 =
      ProjW.ofAgent (transition c x y).2 := by
  cases suppress <;> exact ⟨rfl, rfl⟩

private theorem bankWordMaskedFrame {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (suppress : Bool) :
    piW (renewalMaskedStep ring C e suppress) =
      piW (headlinePhysicalNext ring C e) := by
  cases suppress with
  | false =>
      exact congrArg piW (renewalMaskedStepOff ring C e)
  | true =>
      have hpair := bankWordMaskedPairFrame
        (compileAdvice (ceilLogTwo n)) true
        (C e) (C (ring.rightNeighbor e))
      have hmasked :
          piW (renewalMaskedStep ring C e true) =
            piW (renewalMaskedStep ring C e false) := by
        funext i
        change
          ProjW.ofAgent
            (if i = e then
              (renewalMaskedPair (compileAdvice (ceilLogTwo n))
                true (C e) (C (ring.rightNeighbor e))).1
             else if i = ring.rightNeighbor e then
              (renewalMaskedPair (compileAdvice (ceilLogTwo n))
                true (C e) (C (ring.rightNeighbor e))).2
             else C i) =
          ProjW.ofAgent
            (if i = e then
              (renewalMaskedPair (compileAdvice (ceilLogTwo n))
                false (C e) (C (ring.rightNeighbor e))).1
             else if i = ring.rightNeighbor e then
              (renewalMaskedPair (compileAdvice (ceilLogTwo n))
                false (C e) (C (ring.rightNeighbor e))).2
             else C i)
        by_cases h1 : i = e
        · rw [if_pos h1, if_pos h1]
          exact hpair.1
        · by_cases h2 : i = ring.rightNeighbor e
          · exact (congrArg ProjW.ofAgent ((if_neg h1).trans (if_pos h2))).trans
              (hpair.2.trans
                (congrArg ProjW.ofAgent ((if_neg h1).trans (if_pos h2))).symm)
          · exact congrArg ProjW.ofAgent
              (((if_neg h1).trans (if_neg h2)).trans
                ((if_neg h1).trans (if_neg h2)).symm)
      exact hmasked.trans
        (congrArg piW (renewalMaskedStepOff ring C e))

/-- Exact projected-W step for the original valid BANK reference
when the OLD physical grants vanish. Inherited BANK success,
all other token fields and masked/unmasked private behavior
are retained; no full physical equality is claimed. -/
theorem bankWordReferenceProjectedStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hgrant : NativeLiftGrantFree z.val.1)
    (e : Fin n) :
    piW ((bankRepairNext ring hbank z e).val.1) =
      phiW ring (piW z.val.1) e := by
  have hnofire : oldFire
      (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) = none := by
    have h := native_lift_no_fire_of_pair_grant_free
      ring z.val.1 e (hgrant e)
      (hgrant (ring.rightNeighbor e))
    change oldFire
      (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) = none at h
    exact h
  have hreal : piW (headlinePhysicalNext ring z.val.1 e) =
      phiW ring (piW z.val.1) e := by
    exact stepW_noFire (q := ceilLogTwo n) hn
      ring z.val.1 e hnofire
  calc
    piW ((bankRepairNext ring hbank z e).val.1) =
        piW (headlinePhysicalNext ring z.val.1 e) := by
          change piW
            (renewalMaskedStep ring z.val.1 e
              (renewalBankCut ring z.val.1 z.val.2 e)) =
            piW (headlinePhysicalNext ring z.val.1 e)
          exact bankWordMaskedFrame ring z.val.1 e
            (renewalBankCut ring z.val.1 z.val.2 e)
    _ = phiW ring (piW z.val.1) e := hreal

/-- The installed post-inherited/grant-drained domain is
closed on the original masked BANK reference. -/
theorem bankWordPostInheritedDomainStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedGrantDrain ring hbank z)
    (e : Fin n) :
    BankPostInheritedGrantDrain ring hbank
      (bankRepairNext ring hbank z e) := by
  exact bankPostInheritedGrantDrainClosed ring hn hbank z hz e

/-- E.G18 in the masked BANK reference, with the full accepted
W decoration carried forward, under the actual post-inherited
no-grant suffix condition. -/
theorem bankWordAcceptedReferenceStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hpost : BankPostInheritedGrantDrain ring hbank z)
    (hword : BankRepairWord ring hbank z)
    (e : Fin n) :
    BankRepairWord ring hbank
      (bankRepairNext ring hbank z e) := by
  have hstep := bankWordReferenceProjectedStep ring
    (by omega : 2 ≤ n) hbank z hpost.1.2 e
  have hproj : BankWordProjectedTarget ring (piW z.val.1) := hword
  change BankWordProjectedTarget ring
    (piW ((bankRepairNext ring hbank z e).val.1))
  rw [hstep]
  exact AcceptedReceipts.accepted_word_phi_step
    ring (piW z.val.1) e hproj

def BankWordPostInheritedAccepted {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedGrantDrain ring hbank z ∧
    BankRepairWord ring hbank z

theorem bankWordPostInheritedAcceptedStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankWordPostInheritedAccepted ring hbank z)
    (e : Fin n) :
    BankWordPostInheritedAccepted ring hbank
      (bankRepairNext ring hbank z e) := by
  exact ⟨bankWordPostInheritedDomainStep ring hn hbank z hz.1 e,
    bankWordAcceptedReferenceStep ring hn hbank z hz.1 hz.2 e⟩

/-- The actual prepared native/candidate cut retains all
original inherited-extinction and grant-free certificates. -/
theorem bankWordPreparedPostInherited {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPreparedAtSomeRoot ring hbank z) :
    BankPostInheritedGrantDrain ring hbank z := by
  obtain ⟨root, hroot, _⟩ := hz
  exact hroot.1

/-- Equality of every truncated first-hit numerator: the
reference's W endpoint is a faithful phiW projection all the
way to its first accepted word, not just on one chosen edge.
The original IID Fin n scheduler and actual masked state are used. -/
theorem bankWordReferenceCostProjection {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ T : Nat, ∀ z : BankReferenceState ring hbank,
      BankPostInheritedGrantDrain ring hbank z →
      costNumerator (bankRepairNext ring hbank)
        (BankRepairWord ring hbank) z T =
      costNumerator (phiW ring)
        (BankWordProjectedTarget ring) (piW z.val.1) T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro z hz
      by_cases hw : BankRepairWord ring hbank z
      · have hp : BankWordProjectedTarget ring (piW z.val.1) := hw
        rw [costNumerator_terminal
          (bankRepairNext ring hbank)
          (BankRepairWord ring hbank) z hw (T + 1),
          costNumerator_terminal
            (phiW ring) (BankWordProjectedTarget ring)
            (piW z.val.1) hp (T + 1)]
      · have hp : ¬ BankWordProjectedTarget ring (piW z.val.1) := hw
        rw [costNumerator_succ
          (bankRepairNext ring hbank)
          (BankRepairWord ring hbank) z hw T,
          costNumerator_succ
            (phiW ring) (BankWordProjectedTarget ring)
            (piW z.val.1) hp T]
        congr 1
        exact ofFn_sum_eq _ _ (fun e => by
          have hh := ih (bankRepairNext ring hbank z e)
            (bankWordPostInheritedDomainStep ring hn hbank z hz e)
          rw [bankWordReferenceProjectedStep ring
            (by omega : 2 ≤ n) hbank z hz.1.2 e] at hh
          exact hh)

/-- Already accepted W has zero finite-horizon hitting cost even
when other real private work and masked BANK token fields continue. -/
theorem bankWordAlreadyAcceptedCostZero {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairWord ring hbank z)
    (T : Nat) :
    costNumerator (bankRepairNext ring hbank)
      (BankRepairWord ring hbank) z T = 0 := by
  exact costNumerator_terminal (bankRepairNext ring hbank)
    (BankRepairWord ring hbank) z hz T

/-- The missing projected W acceptance-clock estimate entails
BOTH existing R10 WordStage components, ordinary first hit and
the exact doubled-cost half-unit statement. It incurs no new
conditioning, rounding, or reference/physical stopwatch. -/
theorem bankRepairWordStageOfProjectedClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hclock : BankWordProjectedClock ring hbank) :
    BankRepairWordStage ring hbank := by
  constructor
  · intro z hz
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (bankRepairNext ring hbank) (BankRepairWord ring hbank)
      (by omega : 0 < n) z
      ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2)).2
    intro T
    rw [bankWordReferenceCostProjection ring hn hbank T z
      (bankWordPreparedPostInherited ring hbank z hz)]
    exact hclock z hz T
  · intro z hz T
    have hprojection := bankWordReferenceCostProjection
      ring hn hbank T z
      (bankWordPreparedPostInherited ring hbank z hz)
    have hcost := hclock z hz T
    rw [← hprojection] at hcost
    have hscaled := Nat.mul_le_mul_left 2 hcost
    have hfactor :
        2 * (n ^ T *
          ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2)) =
        n ^ T *
          ((2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) *
            n ^ 2) := by
      ac_rfl
    rw [hfactor] at hscaled
    exact hscaled

end L3.RenewalReferenceClock


/-!
A true projected S1 serializer episode and geometric epochs.

The old W serializer fields are unrestricted. The first bound counts
real Fin n scheduler services on a phiW stop-latch kernel. Its
fixed-root closure excludes lost-root exits without resetting any
physical bytes. The second bound uses the same-word failure numerator
of a valid retry kernel and its actual physical simulation.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Exact projected W class represented by a reachable
post-inherited BANK reference with one specified native root. -/
def BankWordSerializerRootClass {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∃ z : BankReferenceState ring hbank,
    BankPostInheritedSingleton ring hbank root z ∧
      piW z.val.1 = s

/-- The root certificate of the actual native view is exactly the
physical W fixed-root condition. -/
private theorem bankWordRootedNativeToWFixed {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (hroot : ReferencePreparationTrail.Rooted ring root
      (renewalBankValidNativeView ring hbank z)) :
    WFixedRoot ring root (piW z.val.1) := by
  change WFixedRoot ring root (piW z.val.1) at hroot
  exact hroot

/-- The represented W class is closed on every true phiW edge.
No full physical state equality is assumed: only the already
proved BANK W projection and same-root singleton closure. -/
theorem bankWordSerializerRootClassClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) :
    ClockSerializerNoRootLossFromG ring root
      (BankWordSerializerRootClass ring hbank root) := by
  constructor
  · intro s hs
    obtain ⟨z, hz, heq⟩ := hs
    rw [← heq]
    exact bankWordRootedNativeToWFixed ring hbank
      root z hz.2
  · intro s hs e
    obtain ⟨z, hz, heq⟩ := hs
    have hclosed := bankPostInheritedSingletonClosed
      ring hn hbank root z hz e
    have hstep := bankWordReferenceProjectedStep
      ring (by omega : 2 ≤ n) hbank z hz.1.1.2 e
    rw [heq] at hstep
    constructor
    · exact ⟨bankRepairNext ring hbank z e, hclosed, hstep⟩
    · rw [← hstep]
      exact bankWordRootedNativeToWFixed ring hbank
        root (bankRepairNext ring hbank z e) hclosed.2

/-- Every true prepared BANK reference starts in one such
fixed-root W class; serializer contents need not be canonical. -/
theorem bankWordPreparedSerializerRootClass {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPreparedAtSomeRoot ring hbank z) :
    ∃ root : Fin n,
      BankWordSerializerRootClass ring hbank root
        (piW z.val.1) := by
  obtain ⟨root, hroot, _⟩ := hz
  exact ⟨root, z, hroot, rfl⟩

/-- S1 alone, not the weaker S1-or-lost-root exit, is reached
within n*(5*n-4) expected services. The chain uses real phiW
on its active states and latches the first S1 service.
This is the first serializer normalization milestone, not yet
the final accepted recurrence word. -/
theorem bankWordPreparedSerializerSOneCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPreparedAtSomeRoot ring hbank z) :
    ∃ root : Fin n, ∀ T : Nat,
      costNumerator (clockSerializerSOneOnlyNext ring root)
        clockSerializerIsStopped
        (.active (piW z.val.1) :
          ClockSerializerStopNode n
            (compileAdvice (ceilLogTwo n))) T ≤
      n ^ T * (n * (5 * n - 4)) := by
  obtain ⟨root, hclass⟩ :=
    bankWordPreparedSerializerRootClass ring hbank z hz
  refine ⟨root, ?_⟩
  exact clockSerializerSOneCostFromG ring root
    (BankWordSerializerRootClass ring hbank root)
    (bankWordSerializerRootClassClosed ring hn hbank root)
    (piW z.val.1) hclass (by omega : 4 ≤ n)

/-- Its first-hitting-time formulation, including almost-sure
S1 termination, follows from the installed SerClockCost theorem. -/
theorem bankWordPreparedSerializerSOneExpected {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPreparedAtSomeRoot ring hbank z) :
    ∃ root : Fin n,
      UniformFirstHit.ExpectedHittingTimeAtMost
        (clockSerializerSOneOnlyNext ring root)
        clockSerializerIsStopped
        (.active (piW z.val.1) :
          ClockSerializerStopNode n
            (compileAdvice (ceilLogTwo n)))
        ((n * (5 * n - 4) : Nat) : Rat) := by
  obtain ⟨root, hclass⟩ :=
    bankWordPreparedSerializerRootClass ring hbank z hz
  refine ⟨root, ?_⟩
  exact clockSerializerSOneExpectedFromG ring root
    (BankWordSerializerRootClass ring hbank root)
    (bankWordSerializerRootClassClosed ring hn hbank root)
    (piW z.val.1) hclass (by omega : 4 ≤ n)

/-- Exact natural ceiling of B/(1-3/4): it is 4B, with
no rounding overhead for the quarter-success bound. -/
theorem bankWordQuarterRetryCeiling (B : Nat) :
    L3.Prob.renewalCeiling B 3 4 = 4 * B := by
  simp [L3.Prob.renewalCeiling, L3.Prob.ceilNat,
    Nat.mul_comm] <;> omega

/-- Geometric epochs for a genuine related physical chain.

Every valid epoch has first-hit cost B to success-or-retry.
The exact first-retry mass, under the SAME Fin n word, satisfies
4 * retryCount <= 3 * n^T for every horizon. Kernel.valid
ensures legal restarts and RetrySimulation ensures each retry
relates to the actual reached physical state. Thus the true
physical Good first-hit numerator is <= 4B, hence <= 5B.
No independence of epoch durations or success events is used. -/
theorem bankWordAbstractQuarterEpochCost
    {X A Seed : Type} {n : Nat}
    (next : X → Fin n → X)
    (Good EpochClass : X → Prop)
    (K : PPL.Convergence.LDLocal.RetryKernel A Seed n)
    (Rel : X → A → Prop)
    (start : ∀ x : X, EpochClass x → Seed)
    (hsim : L3.Prob.RetrySimulation K next Good Rel)
    (hvalid : ∀ x (hx : EpochClass x),
      K.valid (start x hx))
    (hrel : ∀ x (hx : EpochClass x),
      Rel x (K.start (start x hx)))
    (B : Nat)
    (hcost : ∀ s : Seed, K.valid s → ∀ T : Nat,
      costNumerator (L3.Prob.attemptStepper K)
        (fun q => L3.Prob.attemptGood q ∨
          L3.Prob.attemptFail q)
        (.active (K.start s)) T ≤ n ^ T * B)
    (hfail : ∀ s : Seed, K.valid s → ∀ T : Nat,
      4 * PPL.Convergence.LDLocal.retryCount K
        (.active (K.start s)) T ≤ 3 * n ^ T)
    (x : X) (hx : EpochClass x) (T : Nat) :
    costNumerator next Good x T ≤ n ^ T * (5 * B) := by
  have hcostPhysical :=
    L3.Prob.costNumerator_renewal_le
      next Good K Rel hsim B 3 4
      (by omega : 3 < 4) hcost hfail
      x (start x hx) (hvalid x hx) (hrel x hx) T
  rw [bankWordQuarterRetryCeiling] at hcostPhysical
  exact Nat.le_trans hcostPhysical
    (Nat.mul_le_mul_left (n ^ T) (by omega : 4 * B ≤ 5 * B))

/-- The same bound on the non-truncated expectation. -/
theorem bankWordAbstractQuarterEpochExpected
    {X A Seed : Type} {n : Nat}
    (next : X → Fin n → X)
    (Good EpochClass : X → Prop)
    (K : PPL.Convergence.LDLocal.RetryKernel A Seed n)
    (Rel : X → A → Prop)
    (start : ∀ x : X, EpochClass x → Seed)
    (hsim : L3.Prob.RetrySimulation K next Good Rel)
    (hvalid : ∀ x (hx : EpochClass x),
      K.valid (start x hx))
    (hrel : ∀ x (hx : EpochClass x),
      Rel x (K.start (start x hx)))
    (B : Nat)
    (hcost : ∀ s : Seed, K.valid s → ∀ T : Nat,
      costNumerator (L3.Prob.attemptStepper K)
        (fun q => L3.Prob.attemptGood q ∨
          L3.Prob.attemptFail q)
        (.active (K.start s)) T ≤ n ^ T * B)
    (hfail : ∀ s : Seed, K.valid s → ∀ T : Nat,
      4 * PPL.Convergence.LDLocal.retryCount K
        (.active (K.start s)) T ≤ 3 * n ^ T)
    (x : X) (hx : EpochClass x)
    (hn : 0 < n) :
    UniformFirstHit.ExpectedHittingTimeAtMost next Good x
      ((5 * B : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next Good hn x (5 * B)).2
  intro T
  exact bankWordAbstractQuarterEpochCost next Good EpochClass
    K Rel start hsim hvalid hrel B hcost hfail x hx T

/-- Paper's 5B coefficient, with L=8s+4 and
B=11*(L+1)*n^2. This arithmetic identity does not itself
prove the epoch cost or its conditional success probability. -/
theorem bankWordEpochFiveCoefficient (s n : Nat) :
    5 * (11 * ((8 * s + 4) + 1) * n ^ 2) =
      (440 * s + 275) * n ^ 2 := by
  have hcoef :
      5 * (11 * ((8 * s + 4) + 1)) =
        440 * s + 275 := by omega
  calc
    5 * (11 * ((8 * s + 4) + 1) * n ^ 2) =
        (5 * (11 * ((8 * s + 4) + 1))) * n ^ 2 := by
          ac_rfl
    _ = (440 * s + 275) * n ^ 2 := by
      rw [hcoef]

end L3.RenewalReferenceClock


/-!
One actual projected-W epoch, followed by one named missing
post-S1 worker/serializer budget.

The paper's first genuine hard acceptance is history-sensitive:
repair.tex, main branch, lines 3030--3042 and 3238--3295. Consequently
the first-hit target below reads a proof-only WOriginGhost started
from wOriginInitial, not arbitrary completion-looking physical bytes.
The physical component is still exactly the phiW chain, which is
the actual masked BANK reference projection after grant drain.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A serializer S1 stop latch and an independent full physical
W state, accompanied by the exact origin observer from Target.
The latch remembers S1 without freezing subsequent worker services. -/
abbrev BankWordEpochState (n : Nat) :=
  ClockSerializerStopNode n (compileAdvice (ceilLogTwo n)) ×
    ((Fin n → ProjW (compileAdvice (ceilLogTwo n))) ×
      WOriginGhost n (compileAdvice (ceilLogTwo n)))

/-- One true Fin n service. The first component is the *stopped*
S1 observer; the second component always performs phiW and
advances only the already installed W provenance observer. -/
noncomputable def bankWordEpochNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    BankWordEpochState n :=
  (clockSerializerSOneOnlyNext ring root z.1 e,
    (phiW ring z.2.1 e,
      wOriginGhostStep ring root z.2.1 z.2.2 e))

/-- At the epoch entrance, inherited physical serializer/worker
fields are arbitrary. Only proof-side provenance starts empty. -/
def bankWordEpochStart {n : Nat}
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :
    BankWordEpochState n :=
  (.active s, (s, wOriginInitial))

/-- The true physical W projection never stops moving when S1
has been observed. -/
theorem bankWordEpochPhysicalNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    (bankWordEpochNext ring root z e).2.1 =
      phiW ring z.2.1 e := by
  rfl

/-- This is the first *observed* genuine hard-launch worker
receipt, not a predicate recognizing inherited local bytes.
The observer creates a worker only through wGenuineAcceptance. -/
def BankWordEpochWorkerLaunched {n : Nat}
    (z : BankWordEpochState n) : Prop :=
  ∃ w : WWorkerTrail n, z.2.2.worker = some w

/-- Actual first S1 service has already occurred.
Its latch is absorbing, though the W component continues. -/
def BankWordEpochSOneReached {n : Nat}
    (z : BankWordEpochState n) : Prop :=
  clockSerializerIsStopped z.1

/-- The S1 numerator of the augmented real-phiW process is
exactly the installed stopped serializer numerator.
No independence of ghost and physical fields is assumed. -/
theorem bankWordEpochSOneCostEq {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordEpochSOneReached z T =
    costNumerator (clockSerializerSOneOnlyNext ring root)
      clockSerializerIsStopped z.1 T := by
  change costNumerator (bankWordEpochNext ring root)
      (fun w : BankWordEpochState n =>
        clockSerializerIsStopped w.1) z T =
    costNumerator (clockSerializerSOneOnlyNext ring root)
      clockSerializerIsStopped z.1 T
  exact L3.Prob.costNumerator_ghost_eq
    (clockSerializerSOneOnlyNext ring root)
    (bankWordEpochNext ring root)
    (by intro w e; rfl) clockSerializerIsStopped z T

/-- The true S1 first-hit numerator is at most n(5n-4)
from ANY physical W configuration represented by a genuine
fixed-root post-inherited BANK reference. -/
theorem bankWordEpochSOneCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordEpochSOneReached (bankWordEpochStart s) T ≤
    n ^ T * (n * (5 * n - 4)) := by
  rw [bankWordEpochSOneCostEq]
  change costNumerator
      (clockSerializerSOneOnlyNext ring root)
      clockSerializerIsStopped
      (.active s : ClockSerializerStopNode n
        (compileAdvice (ceilLogTwo n))) T ≤
    n ^ T * (n * (5 * n - 4))
  exact clockSerializerSOneCostFromG ring root
    (BankWordSerializerRootClass ring hbank root)
    (bankWordSerializerRootClassClosed ring hn hbank root)
    s hs (by omega : 4 ≤ n) T

/-- The actual projected epoch process along an arbitrary fixed
Fin n scheduling word. This is ONLY an observer, not an alternative
reference transition. -/
noncomputable def bankWordEpochRun {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) :
    List (Fin n) → BankWordEpochState n
  | [] => z
  | e :: word =>
      bankWordEpochRun ring root
        (bankWordEpochNext ring root z e) word

theorem bankWordEpochRunSnoc {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (word : List (Fin n)) (e : Fin n) :
    bankWordEpochRun ring root z (word ++ [e]) =
      bankWordEpochNext ring root
        (bankWordEpochRun ring root z word) e := by
  induction word generalizing z with
  | nil =>
      rfl
  | cons f tail ih =>
      change bankWordEpochRun ring root
          (bankWordEpochNext ring root z f) (tail ++ [e]) =
        bankWordEpochNext ring root
          (bankWordEpochRun ring root
            (bankWordEpochNext ring root z f) tail) e
      exact ih (bankWordEpochNext ring root z f)

/-- A proof-only reachable epoch state includes the actual W
evolution, S1 latch and full causal W-origin records. It cannot
be forged by postulating arbitrary current worker bytes. -/
def BankWordEpochReachable {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n) : Prop :=
  ∃ word : List (Fin n),
    bankWordEpochRun ring root (bankWordEpochStart s) word = z

theorem bankWordEpochReachableNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) :
    BankWordEpochReachable ring root s
      (bankWordEpochNext ring root z e) := by
  obtain ⟨word, hw⟩ := hz
  refine ⟨word ++ [e], ?_⟩
  rw [bankWordEpochRunSnoc, hw]

/-- Along reachable epoch states, requiring a valid history
witness in the S1-stop predicate changes no first-hit cost. -/
theorem bankWordEpochReachableSOneCostEq {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :
    ∀ (T : Nat) (z : BankWordEpochState n),
      BankWordEpochReachable ring root s z →
      costNumerator (bankWordEpochNext ring root)
        (fun y => BankWordEpochSOneReached y ∧
          BankWordEpochReachable ring root s y) z T =
      costNumerator (bankWordEpochNext ring root)
        BankWordEpochSOneReached z T := by
  intro T
  induction T with
  | zero =>
      intro z _
      rfl
  | succ T ih =>
      intro z hz
      by_cases hstop : BankWordEpochSOneReached z
      · have hboth : BankWordEpochSOneReached z ∧
            BankWordEpochReachable ring root s z :=
          ⟨hstop, hz⟩
        rw [costNumerator_terminal
          (bankWordEpochNext ring root)
          (fun y => BankWordEpochSOneReached y ∧
            BankWordEpochReachable ring root s y)
          z hboth (T + 1),
          costNumerator_terminal
            (bankWordEpochNext ring root)
            BankWordEpochSOneReached z hstop (T + 1)]
      · have hnot : ¬ (BankWordEpochSOneReached z ∧
            BankWordEpochReachable ring root s z) := by
          intro h
          exact hstop h.1
        rw [costNumerator_succ
          (bankWordEpochNext ring root)
          (fun y => BankWordEpochSOneReached y ∧
            BankWordEpochReachable ring root s y)
          z hnot T,
          costNumerator_succ
            (bankWordEpochNext ring root)
            BankWordEpochSOneReached z hstop T]
        have hsum :=
          ofFn_sum_eq _ _ (fun e =>
            ih (bankWordEpochNext ring root z e)
              (bankWordEpochReachableNext
                ring root s z hz e))
        exact congrArg (fun k : Nat => n ^ (T + 1) + k) hsum

/-- EXACT missing worker/serializer component of the one-epoch
bound, isolated for subsequent row and clock proofs.

Source: repair.tex (main) lines 3000-3156 for hard validation,
worker rows and the C*n^2 nomination clock; lines 3178-3207 for
lease/soft-lap destruction; lines 3238-3295 for arbitrary initial
bytes and the first genuine hard acceptance.

From EVERY *actually reachable* S1-completed epoch state, under
the same projected W process and causal receipt observer, the
remaining first-hit cost to a genuinely launched hard worker
is bounded by 6*n^2+(L+1)*(5*n^2+2*n), L=8*s+4.

The initial 6*n^2 pays the extra fresh episode after an inherited
S1 (< 5*n^2+2*n), and the L+1 remaining episodes cover the
lease/soft-lap barrier. This is NOT currently an established producer. -/
def BankWordEpochPostSOneWorkerClock {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z →
    BankWordEpochSOneReached z →
    ∀ T : Nat,
      costNumerator (bankWordEpochNext ring root)
        BankWordEpochWorkerLaunched z T ≤
      n ^ T *
        (6 * n ^ 2 +
          (8 * ceilLogTwo (ceilLogTwo n) + 5) *
            (5 * n ^ 2 + 2 * n))

/-- Integer-cost arithmetic of the paper's E.B bound, with the
true n(5n-4) first S1 cost charged separately. -/
theorem bankWordEpochBudgetArithmetic
    (n s : Nat) (hn : 5 ≤ n) :
    n * (5 * n - 4) +
        (6 * n ^ 2 +
          (8 * s + 5) * (5 * n ^ 2 + 2 * n)) ≤
      11 * (8 * s + 5) * n ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hsq : n ≤ n ^ 2 := by
    calc
      n = n * 1 := by omega
      _ ≤ n * n := Nat.mul_le_mul_left n hn1
      _ = n ^ 2 := by rw [Nat.pow_two]
  have hfirst : n * (5 * n - 4) ≤ 5 * n ^ 2 := by
    calc
      n * (5 * n - 4) ≤ n * (5 * n) :=
        Nat.mul_le_mul_left n (Nat.sub_le _ _)
      _ = 5 * n ^ 2 := by rw [Nat.pow_two]; ac_rfl
  have hper : 5 * n ^ 2 + 2 * n ≤ 7 * n ^ 2 := by
    omega
  have hscaled :=
    Nat.mul_le_mul_left (8 * s + 5) hper
  have hupper :
      n * (5 * n - 4) +
          (6 * n ^ 2 +
            (8 * s + 5) * (5 * n ^ 2 + 2 * n)) ≤
      5 * n ^ 2 +
          (6 * n ^ 2 + (8 * s + 5) * (7 * n ^ 2)) := by
    omega
  have hrearrange :
      (8 * s + 5) * (7 * n ^ 2) =
        (7 * (8 * s + 5)) * n ^ 2 := by
    ac_rfl
  have hcombine :
      5 * n ^ 2 +
          (6 * n ^ 2 + (8 * s + 5) * (7 * n ^ 2)) =
      (11 + 7 * (8 * s + 5)) * n ^ 2 := by
    rw [hrearrange]
    calc
      5 * n ^ 2 + (6 * n ^ 2 +
          7 * (8 * s + 5) * n ^ 2) =
        (5 * n ^ 2 + 6 * n ^ 2) +
          7 * (8 * s + 5) * n ^ 2 := by
            ac_rfl
      _ = (5 + 6) * n ^ 2 +
            7 * (8 * s + 5) * n ^ 2 := by
            rw [Nat.add_mul]
      _ = (11 + 7 * (8 * s + 5)) * n ^ 2 := by
            rw [Nat.add_mul 11 (7 * (8 * s + 5)) (n ^ 2)]
  have hcoeff :
      11 + 7 * (8 * s + 5) ≤ 11 * (8 * s + 5) := by
    omega
  calc
    n * (5 * n - 4) +
        (6 * n ^ 2 +
          (8 * s + 5) * (5 * n ^ 2 + 2 * n)) ≤
      5 * n ^ 2 +
        (6 * n ^ 2 + (8 * s + 5) * (7 * n ^ 2)) := hupper
    _ = (11 + 7 * (8 * s + 5)) * n ^ 2 := hcombine
    _ ≤ 11 * (8 * s + 5) * n ^ 2 :=
      Nat.mul_le_mul_right (n ^ 2) hcoeff

/-- First genuine hard worker launch of this actual projected
epoch, from arbitrary inherited W bytes with a rooted BANK
representation, within paper B=11*(L+1)*n^2, L=8*s+4.

Only the exact post-S1 worker/serializer clock above is an
unproved input; the entire first-S1 phase is already paid by
SerClockCost, with equality of stopped cost numerators. -/
theorem bankWordProjectedOneEpochCostOfWorkerClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hworker : BankWordEpochPostSOneWorkerClock ring root s)
    (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordEpochWorkerLaunched
      (bankWordEpochStart s) T ≤
    n ^ T *
      (11 * (8 * ceilLogTwo (ceilLogTwo n) + 5) * n ^ 2) := by
  have hinit : BankWordEpochReachable ring root s
      (bankWordEpochStart s) :=
    ⟨[], rfl⟩
  have hfirst : ∀ U : Nat,
      costNumerator (bankWordEpochNext ring root)
        (fun z =>
          (BankWordEpochSOneReached z ∧
            BankWordEpochReachable ring root s z) ∨
          BankWordEpochWorkerLaunched z)
        (bankWordEpochStart s) U ≤
      n ^ U * (n * (5 * n - 4)) := by
    intro U
    calc
      costNumerator (bankWordEpochNext ring root)
          (fun z =>
            (BankWordEpochSOneReached z ∧
              BankWordEpochReachable ring root s z) ∨
            BankWordEpochWorkerLaunched z)
          (bankWordEpochStart s) U ≤
        costNumerator (bankWordEpochNext ring root)
          (fun z => BankWordEpochSOneReached z ∧
            BankWordEpochReachable ring root s z)
          (bankWordEpochStart s) U :=
        L3.Prob.costNumerator_target_mono
          (bankWordEpochNext ring root)
          (fun z => BankWordEpochSOneReached z ∧
            BankWordEpochReachable ring root s z)
          (fun z =>
            (BankWordEpochSOneReached z ∧
              BankWordEpochReachable ring root s z) ∨
            BankWordEpochWorkerLaunched z)
          (by intro z h; exact Or.inl h)
          (bankWordEpochStart s) U
      _ = costNumerator (bankWordEpochNext ring root)
          BankWordEpochSOneReached
          (bankWordEpochStart s) U :=
        bankWordEpochReachableSOneCostEq ring root s U
          (bankWordEpochStart s) hinit
      _ ≤ n ^ U * (n * (5 * n - 4)) :=
        bankWordEpochSOneCost ring hn hbank root s hs U
  have hsecond : ∀ z : BankWordEpochState n,
      (BankWordEpochSOneReached z ∧
        BankWordEpochReachable ring root s z) →
      ∀ U : Nat,
        costNumerator (bankWordEpochNext ring root)
          BankWordEpochWorkerLaunched z U ≤
        n ^ U * (6 * n ^ 2 +
          (8 * ceilLogTwo (ceilLogTwo n) + 5) *
            (5 * n ^ 2 + 2 * n)) := by
    intro z hz U
    exact hworker z hz.2 hz.1 U
  have hstaged :=
    L3.Prob.costNumerator_stage_le
      (bankWordEpochNext ring root)
      (bankWordEpochStart s)
      (fun z => BankWordEpochSOneReached z ∧
        BankWordEpochReachable ring root s z)
      BankWordEpochWorkerLaunched
      (n * (5 * n - 4))
      (6 * n ^ 2 +
        (8 * ceilLogTwo (ceilLogTwo n) + 5) *
          (5 * n ^ 2 + 2 * n))
      hfirst hsecond T
  exact Nat.le_trans hstaged
    (Nat.mul_le_mul_left (n ^ T)
      (bankWordEpochBudgetArithmetic n
        (ceilLogTwo (ceilLogTwo n)) hn))

/-- The same conditional epoch bound in the true
first-hit expectation API, not just its truncation numerator.
It begins at any represented BANK projected W epoch entrance. -/
theorem bankWordProjectedOneEpochExpectedOfWorkerClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hworker : BankWordEpochPostSOneWorkerClock ring root s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (bankWordEpochNext ring root)
      BankWordEpochWorkerLaunched
      (bankWordEpochStart s)
      ((11 * (8 * ceilLogTwo (ceilLogTwo n) + 5) *
        n ^ 2 : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankWordEpochNext ring root)
    BankWordEpochWorkerLaunched
    (by omega : 0 < n)
    (bankWordEpochStart s)
    (11 * (8 * ceilLogTwo (ceilLogTwo n) + 5) * n ^ 2)).2
  intro T
  exact bankWordProjectedOneEpochCostOfWorkerClock
    ring hn hbank root s hs hworker T

/-- Physical projection of the masked BANK reference and this
epoch observer use the same real W successor at every edge from
the post-inherited domain. No service is resampled or replaced. -/
theorem bankWordEpochReferencePhysicalAgreement {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedGrantDrain ring hbank z)
    (q : BankWordEpochState n)
    (hq : q.2.1 = piW z.val.1)
    (e : Fin n) :
    (bankWordEpochNext ring root q e).2.1 =
      piW ((bankRepairNext ring hbank z e).val.1) := by
  rw [bankWordEpochPhysicalNext, hq]
  exact (bankWordReferenceProjectedStep
    ring (by omega : 2 ≤ n) hbank z hz.1.2 e).symm

end L3.RenewalReferenceClock


/-!
Post-S1 audit: next-S1 restart, a single causal
lease/validation drift gap, and the conditional W worker clock.

No theorem asserts the drift certificate without proof.

Paper: research/paper/l3/appendices/repair.tex (main),
2889--2966, 2998--3042, 3178--3206, 3238--3295.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The S1 latch is persistent; after S1 the actual W component
continues to move, but the historical milestone never disappears. -/
theorem bankWordEpochSOneReachedNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hz : BankWordEpochSOneReached z)
    (e : Fin n) :
    BankWordEpochSOneReached
      (bankWordEpochNext ring root z e) := by
  change clockSerializerIsStopped
    (clockSerializerSOneOnlyNext ring root z.1 e)
  cases hnode : z.1 with
  | stopped =>
      exact True.intro
  | active p =>
      change clockSerializerIsStopped z.1 at hz
      rw [hnode] at hz
      cases hz

/-- A real epoch run preserves the same protected singleton
representation at every physical edge, even after the S1 latch
stops. This does not inspect or reset private serializer bytes. -/
theorem bankWordEpochRunPhysicalRootClass {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (word : List (Fin n)) :
    BankWordSerializerRootClass ring hbank root
      (bankWordEpochRun ring root (bankWordEpochStart s) word).2.1 := by
  have hrun :
      ∀ (w : List (Fin n)) (z : BankWordEpochState n),
        BankWordSerializerRootClass ring hbank root z.2.1 →
        BankWordSerializerRootClass ring hbank root
          (bankWordEpochRun ring root z w).2.1 := by
    intro w
    induction w with
    | nil =>
        intro z hz
        exact hz
    | cons e rest ih =>
        intro z hz
        change BankWordSerializerRootClass ring hbank root
          (bankWordEpochRun ring root
            (bankWordEpochNext ring root z e) rest).2.1
        apply ih
        have hstep :=
          (bankWordSerializerRootClassClosed
            ring hn hbank root).2 z.2.1 hz e
        rw [bankWordEpochPhysicalNext]
        exact hstep.1
  exact hrun word (bankWordEpochStart s) hs

/-- Reachability in the causal W epoch implies that the true
projected physical configuration is still in the root class. -/
theorem bankWordEpochReachablePhysicalRootClass {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordSerializerRootClass ring hbank root z.2.1 := by
  obtain ⟨word, hword⟩ := hz
  have hrun := bankWordEpochRunPhysicalRootClass
    ring hn hbank root s hs word
  rw [hword] at hrun
  exact hrun

/-- A fresh S1-only observer can be started from ANY reachable
post-S1 real W configuration. The old stopped latch is not used
as a clock for a later episode. This is SerClockCost's
n(5n-4) clock, transferred using physical root-class closure. -/
theorem bankWordEpochRestartSOneCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (T : Nat) :
    costNumerator (clockSerializerSOneOnlyNext ring root)
      clockSerializerIsStopped
      (.active z.2.1 : ClockSerializerStopNode n
        (compileAdvice (ceilLogTwo n))) T ≤
    n ^ T * (n * (5 * n - 4)) := by
  exact clockSerializerSOneCostFromG ring root
    (BankWordSerializerRootClass ring hbank root)
    (bankWordSerializerRootClassClosed ring hn hbank root)
    z.2.1
    (bankWordEpochReachablePhysicalRootClass
      ring hn hbank root s hs z hz)
    (by omega : 4 ≤ n) T

/-- THE ONE MISSING SOURCE INPUT.

A natural Bellman potential for the full real-phiW / causal
WOriginGhost process, AFTER the first observed S1 service.
The cap charges at most 6*n^2 for the inherited/untrusted
post-S1 episode and at most L+1 additional request/start/
completion episodes at 5*n^2+2*n each, L=8*s+4.

The drift is required at EVERY reachable, non-launched,
S1-latched state, on ALL actual Fin n successors, not only
on a favorable edge and not only on canonical worker bytes.
It must be proved from the serializer, validation and lease
owner rows. Neither wGenuineAcceptance nor workerW by itself
establishes this Bellman inequality.

Paper lines 2998--3042 (hard validation and I0 launch),
3178--3206 (lease and soft laps), 3238--3287 (arbitrary
inherited bytes, at most one fake acceptance, episode budget).
-/
def BankWordEpochLeaseValidationDrift {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∃ potential : BankWordEpochState n → Nat,
    (∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochSOneReached z →
      potential z ≤
        6 * n ^ 2 +
          (8 * ceilLogTwo (ceilLogTwo n) + 5) *
            (5 * n ^ 2 + 2 * n)) ∧
    (∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochSOneReached z →
      ¬ BankWordEpochWorkerLaunched z →
      n + (List.ofFn (fun e : Fin n =>
        potential (bankWordEpochNext ring root z e))).sum ≤
          n * potential z)

/-- The missing source step above is SUFFICIENT for the exact
post-S1 first-hit cost. This is a LOCAL Bellman proof: only
reachable, S1-latched states require the drift, and both
properties are maintained under the true epoch successor.
No assertion of the source step is hidden in this theorem. -/
theorem bankWordEpochPostSOneWorkerClockOfDrift {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hprogress : BankWordEpochLeaseValidationDrift ring root s) :
    BankWordEpochPostSOneWorkerClock ring root s := by
  classical
  obtain ⟨potential, hcap, hdrift⟩ := hprogress
  have hlocal :
      ∀ T : Nat, ∀ z : BankWordEpochState n,
        BankWordEpochReachable ring root s z →
        BankWordEpochSOneReached z →
        costNumerator (bankWordEpochNext ring root)
          BankWordEpochWorkerLaunched z T ≤
          n ^ T * potential z := by
    intro T
    induction T with
    | zero =>
        intro z hz hS
        simp only [costNumerator_zero]
        exact Nat.zero_le _
    | succ T ih =>
        intro z hz hS
        by_cases hwork : BankWordEpochWorkerLaunched z
        · rw [costNumerator_terminal
            (bankWordEpochNext ring root)
            BankWordEpochWorkerLaunched z hwork (T + 1)]
          exact Nat.zero_le _
        · rw [costNumerator_succ
            (bankWordEpochNext ring root)
            BankWordEpochWorkerLaunched z hwork T]
          have hsum := ofFn_sum_le
            (fun e : Fin n =>
              costNumerator (bankWordEpochNext ring root)
                BankWordEpochWorkerLaunched
                (bankWordEpochNext ring root z e) T)
            (fun e : Fin n =>
              n ^ T * potential (bankWordEpochNext ring root z e))
            (fun e => ih (bankWordEpochNext ring root z e)
              (bankWordEpochReachableNext ring root s z hz e)
              (bankWordEpochSOneReachedNext ring root z hS e))
          calc
            n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  costNumerator (bankWordEpochNext ring root)
                    BankWordEpochWorkerLaunched
                    (bankWordEpochNext ring root z e) T)).sum ≤
              n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  n ^ T * potential
                    (bankWordEpochNext ring root z e))).sum :=
              Nat.add_le_add_left hsum _
            _ = n ^ T * (n +
                (List.ofFn (fun e : Fin n =>
                  potential (bankWordEpochNext ring root z e))).sum) := by
              rw [ofFn_sum_mul_left, Nat.mul_add, Nat.pow_succ]
            _ ≤ n ^ T * (n * potential z) :=
              Nat.mul_le_mul_left _ (hdrift z hz hS hwork)
            _ = n ^ (T + 1) * potential z := by
              rw [Nat.pow_succ]
              ac_rfl
  intro z hz hS T
  exact Nat.le_trans (hlocal T z hz hS)
    (Nat.mul_le_mul_left (n ^ T) (hcap z hz hS))

end L3.RenewalReferenceClock


/-!
Source-level post-S1 clock decomposition audit.

The first mechanical component is the installed startPsi rank,
which clocks the next S1, NOT the end of the current episode.
Thus only the non-S1 componentwise drift is proved below.
The S1-to-terminal rank bridge is isolated by the precise
mechanical terminal first-hit statement at the end.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Causal accounting derived from selected, OLD-row W receipts.
The services list is newest-first, so foldr scans chronologically. -/
structure BankWordEpochChargeLedger where
  sawSOne : Bool
  normalized : Bool
  softLaps : Nat

/-- This is an actual selected root S1 row, not a local lookalike. -/
def bankWordEpochChargeIsSOne {n : Nat}
    (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n))) : Bool :=
  (r.edge == root) && (r.serializer.row == "S1")

/-- An actual root S6 terminal is an episode boundary. -/
def bankWordEpochChargeIsTerminal {n : Nat}
    (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n))) : Bool :=
  (r.edge == root) && (r.serializer.row == "S6")

/-- S6 without hardAccept is a soft lease-lap terminal.
This classifies the literal serializer owner output. -/
def bankWordEpochChargeIsSoft {n : Nat}
    (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n))) : Bool :=
  bankWordEpochChargeIsTerminal root r &&
    (!r.serializer.hard.hardAccept)

/-- The first post-S1 root terminal normalizes the inherited
mechanical suffix for accounting. Subsequent soft S6 rows count
completed laps; no state counter is invented. -/
def bankWordEpochChargeLedgerStep {n : Nat}
    (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n)))
    (a : BankWordEpochChargeLedger) :
    BankWordEpochChargeLedger :=
  { sawSOne := a.sawSOne || bankWordEpochChargeIsSOne root r
    normalized := a.normalized ||
      (a.sawSOne && bankWordEpochChargeIsTerminal root r)
    softLaps := a.softLaps +
      (if a.sawSOne && bankWordEpochChargeIsSoft root r
       then 1 else 0) }

/-- All three ledger values are deterministic functions of
the actual WOriginGhost service history, not additional bytes. -/
def bankWordEpochChargeLedger {n : Nat}
    (root : Fin n) (z : BankWordEpochState n) :
    BankWordEpochChargeLedger :=
  z.2.2.services.foldr (bankWordEpochChargeLedgerStep root)
    { sawSOne := false, normalized := false, softLaps := 0 }

/-- The exact selected source receipt appended by Target's
wOriginGhostStep. -/
def bankWordEpochSelectedReceipt {n : Nat}
    (ring : DirectedRing n)
    (z : BankWordEpochState n) (e : Fin n) :
    WEdgeReceipt n (compileAdvice (ceilLogTwo n)) :=
  { service := z.2.2.clock + 1
    edge := e
    oldSource := z.2.1 e
    oldDestination := z.2.1 (ring.rightNeighbor e)
    serializer := serW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    worker := workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) }

/-- The ledger really follows the same physical Fin n edge. -/
theorem bankWordEpochChargeLedgerNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    bankWordEpochChargeLedger root
      (bankWordEpochNext ring root z e) =
    bankWordEpochChargeLedgerStep root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordEpochChargeLedger root z) := by
  rfl

/-- Mechanical S1 budget: n*startPsi plus two possible root-port
waits. Its cap is B=5n²+2n. The rank is NOT a terminal rank. -/
def bankWordEpochMechanicalBudget {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Nat :=
  n * startPsi ring root z.2.1 + 2 * n

/-- L+1 soft-lap slots with the currently charged episode
excluded. This subtraction is truncated in Nat and requires
no assumption about inherited lease bytes. -/
def bankWordEpochSoftLapRemaining {n : Nat}
    (root : Fin n) (z : BankWordEpochState n) : Nat :=
  (8 * ceilLogTwo (ceilLogTwo n) + 5) -
    ((bankWordEpochChargeLedger root z).softLaps + 1)

/-- A single 6n² inherited/apparent-validation allowance, present
until the first actual root S6 after the first witnessed S1. -/
def bankWordEpochInheritedUnnormalized {n : Nat}
    (root : Fin n) (z : BankWordEpochState n) : Nat :=
  if (bankWordEpochChargeLedger root z).normalized
    then 0 else 1

/-- The requested explicit accounting expression.
B=5n²+2n, L=8s+4:
Phi = current mechanical budget + B*remaining soft lap slots
      + 6n²*[inherited suffix not yet normalized].

This is an explicit capped candidate, NOT yet a Bellman potential:
startPsi can jump on S1 while the S6 ledger remains unchanged. -/
def bankWordEpochExplicitPotential {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Nat :=
  bankWordEpochMechanicalBudget ring root z +
    (5 * n ^ 2 + 2 * n) *
      bankWordEpochSoftLapRemaining root z +
    6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z

theorem bankWordEpochMechanicalBudgetCap {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n) (z : BankWordEpochState n) :
    bankWordEpochMechanicalBudget ring root z ≤
      5 * n ^ 2 + 2 * n := by
  have hrank := clockStartPsiCap ring root z.2.1
    (by omega : 4 ≤ n)
  change n * startPsi ring root z.2.1 + 2 * n ≤
    5 * n ^ 2 + 2 * n
  calc
    n * startPsi ring root z.2.1 + 2 * n ≤
        n * (5 * n - 4) + 2 * n :=
      Nat.add_le_add_right (Nat.mul_le_mul_left n hrank) (2 * n)
    _ ≤ n * (5 * n) + 2 * n :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left n (Nat.sub_le _ _)) (2 * n)
    _ = 5 * n ^ 2 + 2 * n := by
      rw [Nat.pow_two]
      ac_rfl

theorem bankWordEpochSoftLapRemainingCap {n : Nat}
    (root : Fin n) (z : BankWordEpochState n) :
    bankWordEpochSoftLapRemaining root z ≤
      8 * ceilLogTwo (ceilLogTwo n) + 4 := by
  unfold bankWordEpochSoftLapRemaining
  omega

theorem bankWordEpochInheritedUnnormalizedCap {n : Nat}
    (root : Fin n) (z : BankWordEpochState n) :
    bankWordEpochInheritedUnnormalized root z ≤ 1 := by
  unfold bankWordEpochInheritedUnnormalized
  split <;> omega

/-- Completely unconditional numeric R cap, on the actual
epoch state. No normalization or lease-progress theorem is used. -/
theorem bankWordEpochExplicitPotentialCap {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n) (z : BankWordEpochState n) :
    bankWordEpochExplicitPotential ring root z ≤
      6 * n ^ 2 +
        (8 * ceilLogTwo (ceilLogTwo n) + 5) *
          (5 * n ^ 2 + 2 * n) := by
  have hmech := bankWordEpochMechanicalBudgetCap ring root hn z
  have hsoft := Nat.mul_le_mul_left
    (5 * n ^ 2 + 2 * n)
    (bankWordEpochSoftLapRemainingCap root z)
  have hnorm := Nat.mul_le_mul_left (6 * n ^ 2)
    (bankWordEpochInheritedUnnormalizedCap root z)
  change
    bankWordEpochMechanicalBudget ring root z +
        (5 * n ^ 2 + 2 * n) *
          bankWordEpochSoftLapRemaining root z +
        6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z ≤
      6 * n ^ 2 +
        (8 * ceilLogTwo (ceilLogTwo n) + 5) *
          (5 * n ^ 2 + 2 * n)
  calc
    bankWordEpochMechanicalBudget ring root z +
        (5 * n ^ 2 + 2 * n) *
          bankWordEpochSoftLapRemaining root z +
        6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z ≤
      (5 * n ^ 2 + 2 * n) +
        (5 * n ^ 2 + 2 * n) *
          (8 * ceilLogTwo (ceilLogTwo n) + 4) +
        6 * n ^ 2 :=
      Nat.add_le_add (Nat.add_le_add hmech hsoft)
        (Nat.le_trans hnorm (Nat.le_of_eq (Nat.mul_one _)))
    _ = 6 * n ^ 2 +
        (8 * ceilLogTwo (ceilLogTwo n) + 5) *
          (5 * n ^ 2 + 2 * n) := by
      have hslot :
          8 * ceilLogTwo (ceilLogTwo n) + 5 =
            (8 * ceilLogTwo (ceilLogTwo n) + 4) + 1 := by
        omega
      rw [hslot,
        Nat.add_mul (8 * ceilLogTwo (ceilLogTwo n) + 4) 1
          (5 * n ^ 2 + 2 * n),
        Nat.one_mul (5 * n ^ 2 + 2 * n),
        Nat.mul_comm (8 * ceilLogTwo (ceilLogTwo n) + 4)
          (5 * n ^ 2 + 2 * n)]
      omega

/-- The owner-row theorem implies physical mechanical
weak monotonicity on every NON-S1 service preserving the fixed
native root. At S1 it explicitly supplies no such conclusion. -/
theorem bankWordEpochMechanicalNoSOneWeak {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 4 ≤ n) (z : BankWordEpochState n)
    (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hnon : ¬ clockSerializerSOneService ring root z.2.1 e) :
    bankWordEpochMechanicalBudget ring root
      (bankWordEpochNext ring root z e) ≤
    bankWordEpochMechanicalBudget ring root z := by
  have hrow :
      e = root →
        (serW (z.2.1 root)
          (z.2.1 (ring.rightNeighbor root))).row ≠ "S1" := by
    intro he hs
    exact hnon ⟨he, hs⟩
  have hweak := clockPhiEveryNonterminalPsiWeak
    ring root z.2.1 hn e hfixed hrow
  change n * startPsi ring root
      (bankWordEpochNext ring root z e).2.1 + 2 * n ≤
    n * startPsi ring root z.2.1 + 2 * n
  rw [bankWordEpochPhysicalNext]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left n hweak) (2 * n)

/-- Actual soft-terminal receipts never decrement the historical
completed-lap count; it increments precisely at a witnessed soft
S6 after the first witnessed S1. -/
theorem bankWordEpochSoftLapsNondecreasing {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    (bankWordEpochChargeLedger root z).softLaps ≤
    (bankWordEpochChargeLedger root
      (bankWordEpochNext ring root z e)).softLaps := by
  rw [bankWordEpochChargeLedgerNext]
  change (bankWordEpochChargeLedger root z).softLaps ≤
    (bankWordEpochChargeLedger root z).softLaps +
      (if (bankWordEpochChargeLedger root z).sawSOne &&
        bankWordEpochChargeIsSoft root
          (bankWordEpochSelectedReceipt ring z e)
        then 1 else 0)
  split <;> omega

theorem bankWordEpochSoftLapsRemainingWeak {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    bankWordEpochSoftLapRemaining root
      (bankWordEpochNext ring root z e) ≤
    bankWordEpochSoftLapRemaining root z := by
  have hcount := bankWordEpochSoftLapsNondecreasing
    ring root z e
  unfold bankWordEpochSoftLapRemaining
  omega

/-- After the first witnessed S1, the normalization flag is
monotone and is cleared exactly on an actual root S6. -/
theorem bankWordEpochNormalizationFlagWeak {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    bankWordEpochInheritedUnnormalized root
      (bankWordEpochNext ring root z e) ≤
    bankWordEpochInheritedUnnormalized root z := by
  unfold bankWordEpochInheritedUnnormalized
  rw [bankWordEpochChargeLedgerNext]
  change
    (if (bankWordEpochChargeLedger root z).normalized ||
      ((bankWordEpochChargeLedger root z).sawSOne &&
        bankWordEpochChargeIsTerminal root
          (bankWordEpochSelectedReceipt ring z e))
      then 0 else 1) ≤
    (if (bankWordEpochChargeLedger root z).normalized
      then 0 else 1)
  cases h : (bankWordEpochChargeLedger root z).normalized <;>
    cases ht : ((bankWordEpochChargeLedger root z).sawSOne &&
      bankWordEpochChargeIsTerminal root
        (bankWordEpochSelectedReceipt ring z e)) <;>
    simp [h, ht]

/-- The entire explicit candidate Phi is nonincreasing on
non-S1 selected edges of the original physical W process. -/
theorem bankWordEpochExplicitPotentialNoSOneWeak {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 4 ≤ n) (z : BankWordEpochState n) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hnon : ¬ clockSerializerSOneService ring root z.2.1 e) :
    bankWordEpochExplicitPotential ring root
      (bankWordEpochNext ring root z e) ≤
    bankWordEpochExplicitPotential ring root z := by
  have hmech := bankWordEpochMechanicalNoSOneWeak
    ring root hn z e hfixed hnon
  have hsoft := Nat.mul_le_mul_left (5 * n ^ 2 + 2 * n)
    (bankWordEpochSoftLapsRemainingWeak ring root z e)
  have hnorm := Nat.mul_le_mul_left (6 * n ^ 2)
    (bankWordEpochNormalizationFlagWeak ring root z e)
  change
    bankWordEpochMechanicalBudget ring root
        (bankWordEpochNext ring root z e) +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root
          (bankWordEpochNext ring root z e) +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root
        (bankWordEpochNext ring root z e) ≤
    bankWordEpochMechanicalBudget ring root z +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root z +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z
  exact Nat.add_le_add (Nat.add_le_add hmech hsoft) hnorm

/-- A genuine root S6 service AFTER the specified time cut,
recognized only from the actual stored OLD-row service receipt. -/
def BankWordEpochNewRootTerminal {n : Nat}
    (root : Fin n) (cut : Nat)
    (z : BankWordEpochState n) : Prop :=
  ∃ receipt : WEdgeReceipt n (compileAdvice (ceilLogTwo n)),
    receipt ∈ z.2.2.services ∧
      cut < receipt.service ∧ receipt.edge = root ∧
      receipt.serializer.row = "S6"

/-- FIRST MISSING COMPONENT, not the entire W worker-clock claim:
a post-S1 episode's first subsequent actual root S6 terminal
must have a finite-horizon B = 5n²+2n first-hit bound.

SerClockCost proves next S1 with the rank startPsi,
whereas this target is terminal S6 after an already observed
S1. An S1 can reset startPsi upwards. This bridge needs the
paper's *completed* mechanical-episode tickets, inherited
suffix recovery, and root terminal rows (repair.tex main,
2889--2998 and 3238--3276). It has NOT been proved here. -/
def BankWordEpochMechanicalTerminalClock {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z →
    BankWordEpochSOneReached z →
    ∀ T : Nat,
      costNumerator (bankWordEpochNext ring root)
        (BankWordEpochNewRootTerminal root z.2.2.clock) z T ≤
      n ^ T * (5 * n ^ 2 + 2 * n)

end L3.RenewalReferenceClock


/-!
Prepaid S1-start accounting on the same real W/receipt
epoch carrier.

In particular
the existing cap and non-S1 rank lemmas remain unchanged.

The closed mechanical reserve has B=5*n^2+2*n in IDLE and B-n
in REQUESTED; opening the episode at S1 switches to
n*startPsi+2*n. Thus both incoming S0 and outgoing S1 can pay
an n-unit Bellman ticket without increasing the B-slot cap.

An SR reset of a RUNNING root is not S6: the existing soft-lap
ledger does not release B on it. The final named Prop records
the first outstanding edge class; it is not a theorem.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Prepaid mechanical slot: IDLE has B, REQUESTED B-n;
RUNNING is ranked by the actual physical startPsi. -/
def bankWordEpochPrepaidMechanical {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Nat :=
  if (z.2.1 root).ser.cert = .RUNNING then
    bankWordEpochMechanicalBudget ring root z
  else if (z.2.1 root).ser.cert = .REQUESTED then
    5 * n ^ 2 + n
  else
    5 * n ^ 2 + 2 * n

theorem bankWordEpochPrepaidMechanicalCap {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n) (z : BankWordEpochState n) :
    bankWordEpochPrepaidMechanical ring root z ≤
      5 * n ^ 2 + 2 * n := by
  unfold bankWordEpochPrepaidMechanical
  split
  · exact bankWordEpochMechanicalBudgetCap ring root hn z
  · split <;> omega

/-- The old causal soft-lap and inherited allowances are
preserved; only the mechanical slot changes. -/
def bankWordEpochPrepaidPotential {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Nat :=
  bankWordEpochPrepaidMechanical ring root z +
    (5 * n ^ 2 + 2 * n) *
      bankWordEpochSoftLapRemaining root z +
    6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z

theorem bankWordEpochPrepaidPotentialCap {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n) (z : BankWordEpochState n) :
    bankWordEpochPrepaidPotential ring root z ≤
      6 * n ^ 2 +
        (8 * ceilLogTwo (ceilLogTwo n) + 5) *
          (5 * n ^ 2 + 2 * n) := by
  have hmech := bankWordEpochPrepaidMechanicalCap ring root hn z
  have hsoft := Nat.mul_le_mul_left
    (5 * n ^ 2 + 2 * n)
    (bankWordEpochSoftLapRemainingCap root z)
  have hnorm := Nat.mul_le_mul_left (6 * n ^ 2)
    (bankWordEpochInheritedUnnormalizedCap root z)
  change
    bankWordEpochPrepaidMechanical ring root z +
        (5 * n ^ 2 + 2 * n) *
          bankWordEpochSoftLapRemaining root z +
        6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z ≤
      6 * n ^ 2 +
        (8 * ceilLogTwo (ceilLogTwo n) + 5) *
          (5 * n ^ 2 + 2 * n)
  calc
    _ ≤ (5 * n ^ 2 + 2 * n) +
        (5 * n ^ 2 + 2 * n) *
          (8 * ceilLogTwo (ceilLogTwo n) + 4) +
        6 * n ^ 2 :=
      Nat.add_le_add (Nat.add_le_add hmech hsoft)
        (Nat.le_trans hnorm (Nat.le_of_eq (Nat.mul_one _)))
    _ = 6 * n ^ 2 +
          (8 * ceilLogTwo (ceilLogTwo n) + 5) *
            (5 * n ^ 2 + 2 * n) := by
      have hslot :
          8 * ceilLogTwo (ceilLogTwo n) + 5 =
            (8 * ceilLogTwo (ceilLogTwo n) + 4) + 1 := by
        omega
      rw [hslot,
        Nat.add_mul (8 * ceilLogTwo (ceilLogTwo n) + 4) 1
          (5 * n ^ 2 + 2 * n),
        Nat.one_mul (5 * n ^ 2 + 2 * n),
        Nat.mul_comm (8 * ceilLogTwo (ceilLogTwo n) + 4)
          (5 * n ^ 2 + 2 * n)]
      omega

/-- S1 is precisely an outgoing REQUESTED root, and on the
true physical successor the root certificate becomes RUNNING. -/
theorem bankWordEpochPrepaidSOneCertificates {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n) (z : BankWordEpochState n) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hSOne : clockSerializerSOneService ring root z.2.1 e) :
    (z.2.1 root).ser.cert = .REQUESTED ∧
      ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
        .RUNNING := by
  have he : e = root := by
    unfold clockSerializerSOneService at hSOne
    exact hSOne.1
  have hfixedRoot : WFixedRoot ring root (phiW ring z.2.1 root) := by
    have h := hfixed
    rw [he] at h
    exact h
  have hreq := (clockSerializerSOneIffRequested
    ring root z.2.1 (by omega : 2 ≤ n) hfixedRoot e).mp hSOne
  have hpost := clockPostOutgoing ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hreq.1
  have hold : (z.2.1 e).ser.cert = .REQUESTED := by
    rw [hreq.1]
    exact hreq.2
  have hrow := serRootOutgoingStart
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.1 hpost.2 hold
  have hsource :
      ((phiW ring z.2.1 e) e).ser.cert = .RUNNING := by
    rw [phiW_ser_source]
    exact hrow.2.1
  constructor
  · exact hreq.2
  · rw [bankWordEpochPhysicalNext, ← hreq.1]
    exact hsource

/-- The S1 mechanical transition is strict by at least n:
the old slot is 5*n^2+n, while the new RUNNING slot is bounded
by n*(5*n-4)+2*n. -/
theorem bankWordEpochPrepaidSOneMechanicalStrict {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n) (z : BankWordEpochState n) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hSOne : clockSerializerSOneService ring root z.2.1 e) :
    bankWordEpochPrepaidMechanical ring root
        (bankWordEpochNext ring root z e) + n ≤
      bankWordEpochPrepaidMechanical ring root z := by
  have hcert := bankWordEpochPrepaidSOneCertificates
    ring root hn z e hfixed hSOne
  have hrank := clockStartPsiCap ring root
    (bankWordEpochNext ring root z e).2.1
    (by omega : 4 ≤ n)
  have hmul := Nat.mul_le_mul_left n hrank
  have hidentity :
      n * (5 * n - 4) + 4 * n = 5 * n ^ 2 := by
    calc
      n * (5 * n - 4) + 4 * n =
          n * ((5 * n - 4) + 4) := by
        rw [Nat.mul_add, Nat.mul_comm n 4]
      _ = n * (5 * n) := by
        rw [Nat.sub_add_cancel (by omega : 4 ≤ 5 * n)]
      _ = 5 * n ^ 2 := by
        rw [Nat.pow_two]
        ac_rfl
  have hmech :
      bankWordEpochMechanicalBudget ring root
          (bankWordEpochNext ring root z e) + n ≤
        5 * n ^ 2 + n := by
    change n * startPsi ring root
        (bankWordEpochNext ring root z e).2.1 +
        2 * n + n ≤ 5 * n ^ 2 + n
    omega
  have hbefore :
      bankWordEpochPrepaidMechanical ring root z =
        5 * n ^ 2 + n := by
    simp [bankWordEpochPrepaidMechanical, hcert.1]
  have hafter :
      bankWordEpochPrepaidMechanical ring root
          (bankWordEpochNext ring root z e) =
        bankWordEpochMechanicalBudget ring root
          (bankWordEpochNext ring root z e) := by
    simp [bankWordEpochPrepaidMechanical, hcert.2]
  rw [hafter, hbefore]
  exact hmech

/-- The historical ledger terms are both weak, so the same
strict n-unit drop holds for the full prepaid potential on S1. -/
theorem bankWordEpochPrepaidSOneStrict {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n) (z : BankWordEpochState n) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hSOne : clockSerializerSOneService ring root z.2.1 e) :
    bankWordEpochPrepaidPotential ring root
        (bankWordEpochNext ring root z e) + n ≤
      bankWordEpochPrepaidPotential ring root z := by
  have hmech := bankWordEpochPrepaidSOneMechanicalStrict
    ring root hn z e hfixed hSOne
  have hsoft := Nat.mul_le_mul_left (5 * n ^ 2 + 2 * n)
    (bankWordEpochSoftLapsRemainingWeak ring root z e)
  have hnorm := Nat.mul_le_mul_left (6 * n ^ 2)
    (bankWordEpochNormalizationFlagWeak ring root z e)
  change
    bankWordEpochPrepaidMechanical ring root
        (bankWordEpochNext ring root z e) +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root
          (bankWordEpochNext ring root z e) +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root
        (bankWordEpochNext ring root z e) + n ≤
    bankWordEpochPrepaidMechanical ring root z +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root z +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z
  omega

/-- Every IDLE-root successor fits the old prepaid mechanical
cap, so the whole potential is weak on all physical edges. -/
theorem bankWordEpochPrepaidIdleWeak {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n) (z : BankWordEpochState n) (e : Fin n)
    (hidle : (z.2.1 root).ser.cert = .IDLE) :
    bankWordEpochPrepaidPotential ring root
        (bankWordEpochNext ring root z e) ≤
      bankWordEpochPrepaidPotential ring root z := by
  have hcap := bankWordEpochPrepaidMechanicalCap
    ring root hn (bankWordEpochNext ring root z e)
  have hold :
      bankWordEpochPrepaidMechanical ring root z =
        5 * n ^ 2 + 2 * n := by
    simp [bankWordEpochPrepaidMechanical, hidle]
  have hmech :
      bankWordEpochPrepaidMechanical ring root
          (bankWordEpochNext ring root z e) ≤
        bankWordEpochPrepaidMechanical ring root z := by
    rw [hold]
    exact hcap
  have hsoft := Nat.mul_le_mul_left (5 * n ^ 2 + 2 * n)
    (bankWordEpochSoftLapsRemainingWeak ring root z e)
  have hnorm := Nat.mul_le_mul_left (6 * n ^ 2)
    (bankWordEpochNormalizationFlagWeak ring root z e)
  change
    bankWordEpochPrepaidMechanical ring root
        (bankWordEpochNext ring root z e) +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root
          (bankWordEpochNext ring root z e) +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root
        (bankWordEpochNext ring root z e) ≤
    bankWordEpochPrepaidMechanical ring root z +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root z +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z
  omega

/-- On incoming S0 the old IDLE root becomes REQUESTED;
the mechanical slot releases exactly n. -/
theorem bankWordEpochPrepaidIncomingIdleStrict {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n) (z : BankWordEpochState n) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hin : ring.rightNeighbor e = root)
    (hidle : (z.2.1 root).ser.cert = .IDLE) :
    bankWordEpochPrepaidPotential ring root
        (bankWordEpochNext ring root z e) + n ≤
      bankWordEpochPrepaidPotential ring root z := by
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hin
  have hold : (z.2.1 (ring.rightNeighbor e)).ser.cert =
      .IDLE := by
    rw [hin]
    exact hidle
  have hrow := serRootIncomingIdle
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.1 hpost.2 hold
  have hnext :
      ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
        .REQUESTED := by
    rw [bankWordEpochPhysicalNext]
    rw [← hin]
    rw [phiW_ser_target ring z.2.1 e
      (clockNeighborDifferent ring (by omega : 2 ≤ n) e)]
    exact hrow.2
  have hbefore :
      bankWordEpochPrepaidMechanical ring root z =
        5 * n ^ 2 + 2 * n := by
    simp [bankWordEpochPrepaidMechanical, hidle]
  have hafter :
      bankWordEpochPrepaidMechanical ring root
          (bankWordEpochNext ring root z e) =
        5 * n ^ 2 + n := by
    simp [bankWordEpochPrepaidMechanical, hnext]
  have hmech :
      bankWordEpochPrepaidMechanical ring root
          (bankWordEpochNext ring root z e) + n ≤
        bankWordEpochPrepaidMechanical ring root z := by
    rw [hafter, hbefore]
    omega
  have hsoft := Nat.mul_le_mul_left (5 * n ^ 2 + 2 * n)
    (bankWordEpochSoftLapsRemainingWeak ring root z e)
  have hnorm := Nat.mul_le_mul_left (6 * n ^ 2)
    (bankWordEpochNormalizationFlagWeak ring root z e)
  change
    bankWordEpochPrepaidMechanical ring root
        (bankWordEpochNext ring root z e) +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root
          (bankWordEpochNext ring root z e) +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root
        (bankWordEpochNext ring root z e) + n ≤
    bankWordEpochPrepaidMechanical ring root z +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root z +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z
  omega

/-- The running non-S1 row remains weak when the successor
also stays RUNNING, directly by the installed rank lemma. -/
theorem bankWordEpochPrepaidRunningNoSOneWeak {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 4 ≤ n) (z : BankWordEpochState n) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hnon : ¬ clockSerializerSOneService ring root z.2.1 e)
    (hold : (z.2.1 root).ser.cert = .RUNNING)
    (hnext : ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
      .RUNNING) :
    bankWordEpochPrepaidPotential ring root
        (bankWordEpochNext ring root z e) ≤
      bankWordEpochPrepaidPotential ring root z := by
  have hmech := bankWordEpochMechanicalNoSOneWeak
    ring root hn z e hfixed hnon
  have hbefore :
      bankWordEpochPrepaidMechanical ring root z =
        bankWordEpochMechanicalBudget ring root z := by
    simp [bankWordEpochPrepaidMechanical, hold]
  have hafter :
      bankWordEpochPrepaidMechanical ring root
          (bankWordEpochNext ring root z e) =
        bankWordEpochMechanicalBudget ring root
          (bankWordEpochNext ring root z e) := by
    simp [bankWordEpochPrepaidMechanical, hnext]
  have hsoft := Nat.mul_le_mul_left (5 * n ^ 2 + 2 * n)
    (bankWordEpochSoftLapsRemainingWeak ring root z e)
  have hnorm := Nat.mul_le_mul_left (6 * n ^ 2)
    (bankWordEpochNormalizationFlagWeak ring root z e)
  change
    bankWordEpochPrepaidMechanical ring root
        (bankWordEpochNext ring root z e) +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root
          (bankWordEpochNext ring root z e) +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root
        (bankWordEpochNext ring root z e) ≤
    bankWordEpochPrepaidMechanical ring root z +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root z +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z
  rw [hbefore, hafter]
  omega

/-- The corresponding REQUESTED-to-REQUESTED edge is weak. -/
theorem bankWordEpochPrepaidRequestedPreservedWeak {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hold : (z.2.1 root).ser.cert = .REQUESTED)
    (hnext : ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
      .REQUESTED) :
    bankWordEpochPrepaidPotential ring root
        (bankWordEpochNext ring root z e) ≤
      bankWordEpochPrepaidPotential ring root z := by
  have hbefore :
      bankWordEpochPrepaidMechanical ring root z =
        5 * n ^ 2 + n := by
    simp [bankWordEpochPrepaidMechanical, hold]
  have hafter :
      bankWordEpochPrepaidMechanical ring root
          (bankWordEpochNext ring root z e) =
        5 * n ^ 2 + n := by
    simp [bankWordEpochPrepaidMechanical, hnext]
  have hsoft := Nat.mul_le_mul_left (5 * n ^ 2 + 2 * n)
    (bankWordEpochSoftLapsRemainingWeak ring root z e)
  have hnorm := Nat.mul_le_mul_left (6 * n ^ 2)
    (bankWordEpochNormalizationFlagWeak ring root z e)
  change
    bankWordEpochPrepaidMechanical ring root
        (bankWordEpochNext ring root z e) +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root
          (bankWordEpochNext ring root z e) +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root
        (bankWordEpochNext ring root z e) ≤
    bankWordEpochPrepaidMechanical ring root z +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root z +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z
  rw [hbefore, hafter]
  omega

/-- Simple Fin-indexed weak sum bound in core Lean. -/
private theorem bankWordEpochPrepaidFinSumWeak :
    ∀ (m : Nat) (f : Fin m → Nat) (V : Nat),
      (∀ e, f e ≤ V) →
      (List.ofFn f).sum ≤ m * V := by
  intro m
  induction m with
  | zero =>
      intro f V _
      simp
  | succ m ih =>
      intro f V hweak
      rw [List.ofFn_succ, List.sum_cons]
      have hz : f 0 ≤ V := hweak 0
      have ht := ih (fun e : Fin m => f e.succ) V
        (fun e => hweak e.succ)
      calc
        f 0 + (List.ofFn (fun e : Fin m => f e.succ)).sum ≤
            V + m * V := Nat.add_le_add hz ht
        _ = Nat.succ m * V := by
          rw [Nat.succ_mul]
          omega

/-- A strict ticket from one nominated Fin edge, plus weak
edges elsewhere, suffices for the exact uniform Bellman sum. -/
private theorem bankWordEpochPrepaidFinSumStrict :
    ∀ (m : Nat) (f : Fin m → Nat) (chosen : Fin m)
        (V ticket : Nat),
      (∀ e, f e ≤ V) →
      f chosen + ticket ≤ V →
      ticket + (List.ofFn f).sum ≤ m * V := by
  intro m
  induction m with
  | zero =>
      intro f chosen V ticket _ _
      exact Fin.elim0 chosen
  | succ m ih =>
      intro f chosen V ticket hweak hstrict
      rw [List.ofFn_succ, List.sum_cons]
      cases chosen using Fin.cases with
      | zero =>
          have hz : f 0 + ticket ≤ V := hstrict
          have ht := bankWordEpochPrepaidFinSumWeak m
            (fun e : Fin m => f e.succ) V
            (fun e => hweak e.succ)
          calc
            ticket +
                (f 0 + (List.ofFn
                  (fun e : Fin m => f e.succ)).sum) =
              (f 0 + ticket) +
                (List.ofFn (fun e : Fin m => f e.succ)).sum := by
                  omega
            _ ≤ V + m * V := Nat.add_le_add hz ht
            _ = Nat.succ m * V := by
              rw [Nat.succ_mul]
              omega
      | succ i =>
          have hz : f 0 ≤ V := hweak 0
          have ht := ih (fun e : Fin m => f e.succ) i V ticket
            (fun e => hweak e.succ) hstrict
          calc
            ticket +
                (f 0 + (List.ofFn
                  (fun e : Fin m => f e.succ)).sum) =
              f 0 + (ticket +
                (List.ofFn (fun e : Fin m => f e.succ)).sum) := by
                  omega
            _ ≤ V + m * V := Nat.add_le_add hz ht
            _ = Nat.succ m * V := by
              rw [Nat.succ_mul]
              omega

/-- The new cap and one strict physical nominee close the
original drift statement, conditional on the remaining all-row
weakness and nomination premises. No fake clock is introduced. -/
theorem bankWordEpochLeaseValidationDriftOfPrepaidRows {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hweak : ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochSOneReached z →
      ¬ BankWordEpochWorkerLaunched z →
      ∀ e : Fin n,
        bankWordEpochPrepaidPotential ring root
          (bankWordEpochNext ring root z e) ≤
        bankWordEpochPrepaidPotential ring root z)
    (hstrict : ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochSOneReached z →
      ¬ BankWordEpochWorkerLaunched z →
      ∃ e : Fin n,
        bankWordEpochPrepaidPotential ring root
          (bankWordEpochNext ring root z e) + n ≤
        bankWordEpochPrepaidPotential ring root z) :
    BankWordEpochLeaseValidationDrift ring root s := by
  refine ⟨bankWordEpochPrepaidPotential ring root, ?_, ?_⟩
  · intro z _ _
    exact bankWordEpochPrepaidPotentialCap ring root hn z
  · intro z hz hs hnwork
    obtain ⟨chosen, hdrop⟩ := hstrict z hz hs hnwork
    exact bankWordEpochPrepaidFinSumStrict n
      (fun e : Fin n =>
        bankWordEpochPrepaidPotential ring root
          (bankWordEpochNext ring root z e))
      chosen (bankWordEpochPrepaidPotential ring root z) n
      (hweak z hz hs hnwork) hdrop

/-- FIRST UNSETTLED OWNER CLASS: on a reachable post-S1,
not-yet-launched RUNNING-root SR recovery row, the full
prepaid potential must release n units of real reserve credit.
SR is not counted by the current S6-only soft-lap ledger. -/
def BankWordEpochRunningRecoveryStrictCharge {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z →
    BankWordEpochSOneReached z →
    ¬ BankWordEpochWorkerLaunched z →
    (z.2.1 root).ser.cert = .RUNNING →
    ∀ e : Fin n,
      e = root →
      (bankWordEpochSelectedReceipt ring z e).serializer.row = "SR" →
      bankWordEpochPrepaidPotential ring root
        (bankWordEpochNext ring root z e) + n ≤
        bankWordEpochPrepaidPotential ring root z

/-!
Explicit small LOCAL-row configuration (reachability unproved):

n=5, root=0; existing S1 latch=true, normalized=true,
softLaps=0; root cert RUNNING, phase C, root shape 0 so
startPsi=3. A root outgoing SR row with POST-E bits
(true,false) changes cert to IDLE, not S6.
Old mechanical charge: 5*3+2*5 = 25.
New closed reserve: 5*5^2+2*5 = 135.
The ledger terms do not change on SR, so the candidate
potential increases by 110 and misses a strict 5-unit drop by
115. The installed serRootOutgoingRecovery proves the literal
SR transition from those local root inputs; the question of
reachability from a represented clean epoch remains open.
-/

/-- The numerical configuration is exact but does not assert
the existence of a globally reachable physical SR state. -/
theorem bankWordEpochRunningRecoverySmallGap :
    (5 * 3 + 2 * 5 : Nat) = 25 ∧
    (5 * 5 ^ 2 + 2 * 5 : Nat) = 135 ∧
    ¬ ((135 : Nat) + 5 ≤ 25) := by
  omega

end L3.RenewalReferenceClock


/-!
Causal post-S1 RUNNING-root shape invariant.

The SR recovery of an OLD RUNNING root requires root phase C or F.
In the actual represented fixed-root BANK class, its first S1 resets
the physical root to RUNNING/B. While the designated physical root
remains the unique leader, an incoming root service preserves that
nonidle root's serializer; an outgoing root service either remains B
when its certificate remains RUNNING, or makes the certificate IDLE.
Remote edges frame it. Consequently an actual post-S1 RUNNING-root
SR receipt cannot occur in that class.

The proof below tracks the equality between the active S1 observer
and the *actual* physical W configuration until the latch stops.
This equality is essential: BankWordEpochState is a product type,
so merely inspecting a syntactically stopped observer would be
unsound. After it stops, the RUNNING/B invariant is propagated by
the real phiW step and the represented fixed-root closure.

CAUTION: BankWordEpochLeaseValidationDrift itself quantifies over
arbitrary initial W configurations s, not just a represented BANK
root class. No unrestricted SR impossibility is claimed.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- After a literal ROOT_OUT row, a RUNNING root can only
have phase B. The relevant finite split is on the source's
certificate, phase/out and the responder's phase, not on
the other W, SI, or native coordinates. In the SR and S6
branches the new root is IDLE instead of RUNNING. -/
private theorem bankWordEpochRootOutRunningB
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hrun : (serW x y).x.cert = .RUNNING) :
    (serW x y).x.phase = .B := by
  cases hc : x.ser.cert <;>
    cases hp : x.ser.phase <;>
      cases ho : x.ser.out <;>
        cases hpy : y.ser.phase <;>
          simp [serW, serializerStep, ProjW.lift,
            hx, hy, hc, hp, ho, hpy,
            serTbStar, serChallengeWrite,
            serEnterB, serEnterF, serCanonicalC] at hrun ⊢ <;>
            (repeat' split at hrun) <;> simp_all

/-- The nonidle ROOT_IN S5 row frames the complete old root
serializer. An IDLE root becomes REQUESTED under S0, never
RUNNING; hence incoming services preserve RUNNING/B. -/
private theorem bankWordEpochRootInRunningB
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true)
    (hold : y.ser.cert = .RUNNING → y.ser.phase = .B)
    (hrun : (serW x y).y.cert = .RUNNING) :
    (serW x y).y.phase = .B := by
  by_cases hidle : y.ser.cert = .IDLE
  · have hrow := serRootIncomingIdle x y hx hy hidle
    rw [hrow.2] at hrun
    cases hrun
  · have hrow := serRootIncomingNonidle x y hx hy hidle
    have holdRun : y.ser.cert = .RUNNING := by
      rw [hrow.2] at hrun
      exact hrun
    have hframe : (serW x y).y = y.ser := by
      simp [serW, serializerStep, ProjW.lift, hx, hy, hidle]
    rw [hframe]
    exact hold holdRun

/-- The old RUNNING/B invariant survives any physical edge whose
successor has the same fixed native root. This is the only use
of the native root-class hypothesis in the local row argument. -/
private theorem bankWordEpochRunningBNextOfFixed
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (w : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring w e))
    (hold :
      (w root).ser.cert = .RUNNING →
      (w root).ser.phase = .B)
    (hrun : ((phiW ring w e) root).ser.cert = .RUNNING) :
    ((phiW ring w e) root).ser.phase = .B := by
  rcases clockPostTrichotomy ring root w e hn hfixed with
    hOut | hIn | hRemote
  · rcases hOut with ⟨he, hx, hy⟩
    subst e
    rw [phiW_ser_source] at hrun ⊢
    exact bankWordEpochRootOutRunningB
      (w root) (w (ring.rightNeighbor root)) hx hy hrun
  · rcases hIn with ⟨hj, hx, hy⟩
    have htarget := phiW_ser_target ring w e
      (clockNeighborDifferent ring hn e)
    rw [hj] at htarget
    rw [htarget] at hrun ⊢
    rw [hj] at hx hy
    exact bankWordEpochRootInRunningB
      (w e) (w root) hx hy hold hrun
  · rcases hRemote with ⟨he, hj, _, _⟩
    have hframe := phiW_ser_remote ring w e root
      (Ne.symm he) (Ne.symm hj)
    rw [hframe] at hrun ⊢
    exact hold hrun

/-- At the actual S1 service, the physical root becomes
RUNNING/B, not merely a stopped observer. -/
private theorem bankWordEpochSOnePhysicalRunningB
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (w : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring w e))
    (hSOne : clockSerializerSOneService ring root w e) :
    ((phiW ring w e) root).ser.cert = .RUNNING ∧
    ((phiW ring w e) root).ser.phase = .B := by
  have heRoot : e = root := by
    unfold clockSerializerSOneService at hSOne
    exact hSOne.1
  have hfixedRoot : WFixedRoot ring root (phiW ring w root) := by
    have h := hfixed
    rw [heRoot] at h
    exact h
  have hreq :=
    (clockSerializerSOneIffRequested ring root w hn hfixedRoot e).mp hSOne
  have he : e = root := hreq.1
  subst e
  have hpost :=
    clockPostOutgoing ring root w root hn hfixed rfl
  have hrow := serRootOutgoingStart
    (w root) (w (ring.rightNeighbor root))
    hpost.1 hpost.2 hreq.2
  rw [phiW_ser_source]
  exact ⟨hrow.2.1,
    bankWordEpochRootOutRunningB
      (w root) (w (ring.rightNeighbor root))
      hpost.1 hpost.2 hrow.2.1⟩

/-- The causal proof state: before the first S1, the active
latch contains exactly the physical W configuration; once
S1 is latched, a RUNNING root must be broadcasting in B.
The second clause alone would be invalid on arbitrary
synthetic epoch product states. -/
def BankWordEpochSOneRunningBInvariant {n : Nat}
    (root : Fin n) (z : BankWordEpochState n) : Prop :=
  (∀ w : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
    z.1 = .active w → w = z.2.1) ∧
  (BankWordEpochSOneReached z →
    (z.2.1 root).ser.cert = .RUNNING →
    (z.2.1 root).ser.phase = .B)

/-- No observed S1 is present at the initial active cut, and
the active observer and actual physical state agree. -/
theorem bankWordEpochSOneRunningBInitial
    {n : Nat} (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :
    BankWordEpochSOneRunningBInvariant root
      (bankWordEpochStart s) := by
  constructor
  · intro w h
    change
      (ClockSerializerStopNode.active s :
        ClockSerializerStopNode n (compileAdvice (ceilLogTwo n))) =
          .active w at h
    exact (ClockSerializerStopNode.active.inj h).symm
  · intro hStop
    change clockSerializerIsStopped
      (ClockSerializerStopNode.active s :
        ClockSerializerStopNode n (compileAdvice (ceilLogTwo n))) at hStop
    exact False.elim hStop

/-- The entire mixed latch/physical invariant has a one-edge
inductive step as soon as the same root is physically fixed
on the actual successor. The stopped latch remains stopped;
an active latch stops exactly at the real S1 service. -/
theorem bankWordEpochSOneRunningBStep
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (z : BankWordEpochState n) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hInv : BankWordEpochSOneRunningBInvariant root z) :
    BankWordEpochSOneRunningBInvariant root
      (bankWordEpochNext ring root z e) := by
  constructor
  · intro w hactive
    have hnode : clockSerializerSOneOnlyNext ring root z.1 e =
        .active w := by
      exact hactive
    cases hz : z.1 with
    | stopped =>
        rw [hz] at hnode
        simp [clockSerializerSOneOnlyNext] at hnode
    | active old =>
        have hsync : old = z.2.1 := hInv.1 old hz
        have hzreal : z.1 = .active z.2.1 := by
          rw [← hsync]
          exact hz
        rw [hzreal] at hnode
        by_cases hSOne :
            clockSerializerSOneService ring root z.2.1 e
        · simp [clockSerializerSOneOnlyNext, hSOne] at hnode
        · have heq :
              ClockSerializerStopNode.active
                  (phiW ring z.2.1 e) =
                (ClockSerializerStopNode.active w :
                  ClockSerializerStopNode n
                    (compileAdvice (ceilLogTwo n))) := by
            simpa [clockSerializerSOneOnlyNext, hSOne]
              using hnode
          have hw : w = phiW ring z.2.1 e :=
            (ClockSerializerStopNode.active.inj heq).symm
          rw [bankWordEpochPhysicalNext]
          exact hw
  · intro hnewStop hnewRun
    cases hz : z.1 with
    | stopped =>
        have holdStop : BankWordEpochSOneReached z := by
          change clockSerializerIsStopped z.1
          rw [hz]
          exact True.intro
        have holdSafe := hInv.2 holdStop
        have hphiRun :
            ((phiW ring z.2.1 e) root).ser.cert = .RUNNING := by
          change ((phiW ring z.2.1 e) root).ser.cert = .RUNNING
            at hnewRun
          exact hnewRun
        change ((phiW ring z.2.1 e) root).ser.phase = .B
        exact bankWordEpochRunningBNextOfFixed
          ring root hn z.2.1 e hfixed holdSafe hphiRun
    | active old =>
        have hsync : old = z.2.1 := hInv.1 old hz
        have hStopSource :
            clockSerializerSOneService ring root z.2.1 e := by
          have hStopNode :
              clockSerializerIsStopped
                (clockSerializerSOneOnlyNext ring root
                  (.active old) e) := by
            change clockSerializerIsStopped
              (clockSerializerSOneOnlyNext ring root z.1 e)
              at hnewStop
            rw [hz] at hnewStop
            exact hnewStop
          have hService :=
            (clockSerializerSOneOnlyStopIff
              ring root old e).mp hStopNode
          rw [hsync] at hService
          exact hService
        have hphysical := bankWordEpochSOnePhysicalRunningB
          ring root hn z.2.1 e hfixed hStopSource
        change ((phiW ring z.2.1 e) root).ser.phase = .B
        exact hphysical.2

/-- The invariant is preserved by every finite physical word
in a class with fixed-root closure. This is a real-word induction,
not a Markov surrogate or an assumption on the stopped observer. -/
theorem bankWordEpochSOneRunningBReachable
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordEpochSOneRunningBInvariant root z := by
  obtain ⟨word, hword⟩ := hz
  have hrun :
      ∀ word : List (Fin n), ∀ q : BankWordEpochState n,
        BankWordSerializerRootClass ring hbank root q.2.1 →
        BankWordEpochSOneRunningBInvariant root q →
        BankWordEpochSOneRunningBInvariant root
          (bankWordEpochRun ring root q word) := by
    intro word
    induction word with
    | nil =>
        intro q _ hsafe
        exact hsafe
    | cons e rest ih =>
        intro q hclass hsafe
        have hnext :=
          (bankWordSerializerRootClassClosed
            ring hn hbank root).2 q.2.1 hclass e
        apply ih (bankWordEpochNext ring root q e)
        · rw [bankWordEpochPhysicalNext]
          exact hnext.1
        · exact bankWordEpochSOneRunningBStep ring root
            (by omega : 2 ≤ n) q e hnext.2 hsafe
  have hinv := hrun word (bankWordEpochStart s) hs
    (bankWordEpochSOneRunningBInitial root s)
  rw [hword] at hinv
  exact hinv

/-- The literal root SR recovery discriminator is incompatible
with a RUNNING/B old root and post-E bits (true,false).
Only source certificate, source phase/out and responder phase
are enumerated, leaving other W fields arbitrary. -/
private theorem bankWordEpochRunningBNoSR
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hrun : x.ser.cert = .RUNNING)
    (hphase : x.ser.phase = .B) :
    (serW x y).row ≠ "SR" := by
  intro hSR
  cases ho : x.ser.out <;>
    cases hpy : y.ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hrun, hphase, ho, hpy] at hSR

/-- SR is impossible for a reachable post-S1 RUNNING root
in the actual *represented* fixed-root BANK class. Hence the
previously named SR strict-charge Prop holds vacuously there.
The representation hypothesis must not silently be dropped:
the original drift predicate quantifies over all initial s. -/
theorem bankWordEpochRunningRecoveryStrictChargeOfRootClass
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s) :
    BankWordEpochRunningRecoveryStrictCharge ring root s := by
  intro z hz hSOne hNotLaunched hRun e he hSR
  subst e
  have hinv := bankWordEpochSOneRunningBReachable
    ring root hn hbank s hs z hz
  have hPhase : (z.2.1 root).ser.phase = .B :=
    hinv.2 hSOne hRun
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hNoSR := bankWordEpochRunningBNoSR
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hRun hPhase
  have hRealSR :
      (serW (z.2.1 root)
        (z.2.1 (ring.rightNeighbor root))).row = "SR" := by
    exact hSR
  exact False.elim (hNoSR hRealSR)

/-- The next distinct debtor row: a post-S1, non-launched
RUNNING root completes on an actual root S6. The old
prepaid mechanical slot is ranked by startPsi, while
the successor IDLE slot is B. This requires a historical
soft-lap debit or release of the inherited reserve, unless
the worker is already launched. The existing ledger counts
soft S6 only, and its remaining-slot subtraction may
already be zero. This is a named proposition, NOT a theorem. -/
def BankWordEpochRunningS6PrepaidDebit {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z →
    BankWordEpochSOneReached z →
    ¬ BankWordEpochWorkerLaunched z →
    (z.2.1 root).ser.cert = .RUNNING →
    ∀ e : Fin n,
      e = root →
      (bankWordEpochSelectedReceipt ring z e).serializer.row = "S6" →
      bankWordEpochPrepaidPotential ring root
          (bankWordEpochNext ring root z e) ≤
        bankWordEpochPrepaidPotential ring root z

/-- The literal local S6 row is distinct from the impossible
RUNNING-root SR. The post-root certificate is IDLE. -/
theorem bankWordEpochRunningS6LocalRow
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hrun : x.ser.cert = .RUNNING)
    (hphase : x.ser.phase = .B)
    (hdone : x.ser.out = .DONE)
    (hreturn : y.ser.phase = .F) :
    (serW x y).row = "S6" ∧
    (serW x y).x.cert = .IDLE := by
  have hnot : x.ser.cert ≠ .REQUESTED := by
    intro h
    rw [hrun] at h
    cases h
  have hrow := serRootOutgoingDone
    x y hx hy hnot hphase hdone hreturn
  exact ⟨hrow.1, hrow.2.1⟩

/-- A five-site local terminal reset with no free B credit
has the same numerical obstruction as the earlier SR row:
old RUNNING root B/DONE, immediate F responder gives
word shapes (6,7), so startPsi = 3; old mechanical =
5*3+10=25. The new IDLE reserve is 5*25+10=135.
If normalization is already true and the soft-lap slot
is exhausted, neither of the remaining ledger terms
decreases. This arithmetic does NOT assert that such a
physical/history state is reachable without worker launch. -/
theorem bankWordEpochRunningS6UnpaidSmallGap :
    (5 * 3 + 2 * 5 : Nat) = 25 ∧
    (5 * 5 ^ 2 + 2 * 5 : Nat) = 135 ∧
    ¬ ((135 : Nat) ≤ 25) := by
  omega

/-!
The earlier SR obstruction is removed FOR THE REPRESENTED
BANK root class: after S1, RUNNING root phase C/F is unreachable,
so BankWordEpochRunningRecoveryStrictChargeOfRootClass proves the
existing strict-charge Prop with an explicit BankWordSerializerRootClass
premise and no additional reserve budget.

The original BankWordEpochLeaseValidationDrift ring root s does NOT
have that class premise. Neither unconditional hweak nor hstrict is
proved here. Even within the represented class the next remaining
RUNNING-to-IDLE debit is the genuine S6 terminal, recorded precisely
as BankWordEpochRunningS6PrepaidDebit. The no-credit local S6
configuration illustrates why the old S6-only soft-lap and
normalization terms cannot be assumed to pay an arbitrary reset.
Reachability of the exhausted-credit configuration was not proved.

No theorem asserts unconditional Drift or changes the original
6n²+(8s+5)(5n²+2n) cap.
-/

end L3.RenewalReferenceClock


/-!
Actual soft-S6 ledger debit on the ORIGINAL Fin n W edge.

The crucial distinction in the literal serializer is that
S6 is NOT synonymous with a soft acceptance:
bankWordEpochChargeIsSoft tests !hard.hardAccept.
Moreover, the remaining-slot Nat subtraction saturates at zero.
An S6 can spend one of two credits:
  * before the first post-S1 S6, the 6*n^2 inherited reserve
    clears on the terminal receipt, even on a hard S6;
  * after normalization, a soft S6 spends one remaining
    B=5*n^2+2*n slot, provided softLaps < L=8*s+4.
Either source pays an n-unit STRICT prepaid-potential drop.

One named open reachability proposition below asks precisely
for availability of one of these real credits at a reachable
post-S1, not-currently-launched RUNNING S6 cut. The case of
normalized=true and exhausted softLaps (or a later hard S6
without a spendable soft slot) is not discharged by arithmetic
and is NOT silently claimed impossible.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The selected literal root S6 receipt is an actual
terminal receipt, with no reinterpretation of the scheduler. -/
theorem bankWordEpochS6ReceiptTerminal {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (he : e = root)
    (hS6 :
      (bankWordEpochSelectedReceipt ring z e).serializer.row = "S6") :
    bankWordEpochChargeIsTerminal root
      (bankWordEpochSelectedReceipt ring z e) = true := by
  change ((e == root) &&
    ((bankWordEpochSelectedReceipt ring z e).serializer.row ==
      "S6")) = true
  subst he
  simp [hS6]

/-- A hard acceptance NEVER consumes the soft-lap ledger.
A separate reserve, or a stopped-worker potential, is required
on such an edge. -/
theorem bankWordEpochS6HardNotSoft {n : Nat}
    (root : Fin n)
    (receipt : WEdgeReceipt n
      (compileAdvice (ceilLogTwo n)))
    (hhard : receipt.serializer.hard.hardAccept = true) :
    bankWordEpochChargeIsSoft root receipt = false := by
  unfold bankWordEpochChargeIsSoft
  rw [hhard]
  cases bankWordEpochChargeIsTerminal root receipt <;> rfl

/-- The causal foldr ledger counts exactly one additional
soft lap on an actual post-S1 soft root terminal. -/
theorem bankWordEpochS6SoftLapIncrements {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hsaw :
      (bankWordEpochChargeLedger root z).sawSOne = true)
    (hsoft :
      bankWordEpochChargeIsSoft root
        (bankWordEpochSelectedReceipt ring z e) = true) :
    (bankWordEpochChargeLedger root
        (bankWordEpochNext ring root z e)).softLaps =
      (bankWordEpochChargeLedger root z).softLaps + 1 := by
  rw [bankWordEpochChargeLedgerNext]
  change (bankWordEpochChargeLedger root z).softLaps +
    (if (bankWordEpochChargeLedger root z).sawSOne &&
      bankWordEpochChargeIsSoft root
        (bankWordEpochSelectedReceipt ring z e)
     then 1 else 0) =
       (bankWordEpochChargeLedger root z).softLaps + 1
  simp [hsaw, hsoft]

/-- Exact debit: if the OLD soft-lap count is strictly below
L=8*s+4, a genuine post-S1 soft S6 decreases the available
whole-episode slot count by exactly ONE, even at its last slot. -/
theorem bankWordEpochS6SoftSlotDecreases {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hsaw :
      (bankWordEpochChargeLedger root z).sawSOne = true)
    (hsoft :
      bankWordEpochChargeIsSoft root
        (bankWordEpochSelectedReceipt ring z e) = true)
    (hlaps :
      (bankWordEpochChargeLedger root z).softLaps <
        8 * ceilLogTwo (ceilLogTwo n) + 4) :
    bankWordEpochSoftLapRemaining root
        (bankWordEpochNext ring root z e) + 1 =
      bankWordEpochSoftLapRemaining root z := by
  have hstep := bankWordEpochS6SoftLapIncrements
    ring root z e hsaw hsoft
  change
    ((8 * ceilLogTwo (ceilLogTwo n) + 5) -
      ((bankWordEpochChargeLedger root
        (bankWordEpochNext ring root z e)).softLaps + 1)) + 1 =
    (8 * ceilLogTwo (ceilLogTwo n) + 5) -
      ((bankWordEpochChargeLedger root z).softLaps + 1)
  rw [hstep]
  omega

/-- The hard/soft distinction is irrelevant for the FIRST S6
after observed S1: it exhausts the inherited normalization flag
and releases 6*n^2 of causal reserve. -/
theorem bankWordEpochS6FirstNormalizationRelease {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hsaw :
      (bankWordEpochChargeLedger root z).sawSOne = true)
    (hfirst :
      (bankWordEpochChargeLedger root z).normalized = false)
    (hterminal :
      bankWordEpochChargeIsTerminal root
        (bankWordEpochSelectedReceipt ring z e) = true) :
    bankWordEpochInheritedUnnormalized root z = 1 ∧
      bankWordEpochInheritedUnnormalized root
        (bankWordEpochNext ring root z e) = 0 := by
  constructor
  · unfold bankWordEpochInheritedUnnormalized
    rw [hfirst]
    rfl
  · unfold bankWordEpochInheritedUnnormalized
    rw [bankWordEpochChargeLedgerNext]
    change
      (if (bankWordEpochChargeLedger root z).normalized ||
        ((bankWordEpochChargeLedger root z).sawSOne &&
          bankWordEpochChargeIsTerminal root
            (bankWordEpochSelectedReceipt ring z e))
       then 0 else 1) = 0
    simp [hfirst, hsaw, hterminal]

/-- First actual post-S1 S6: 6n^2 normalizing credit pays
the full new B slot PLUS the n-unit progress ticket. This
works even if that first S6 is hard rather than soft. -/
theorem bankWordEpochS6FirstPrepaidStrict {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (z : BankWordEpochState n) (e : Fin n)
    (hsaw :
      (bankWordEpochChargeLedger root z).sawSOne = true)
    (hfirst :
      (bankWordEpochChargeLedger root z).normalized = false)
    (hterminal :
      bankWordEpochChargeIsTerminal root
        (bankWordEpochSelectedReceipt ring z e) = true) :
    bankWordEpochPrepaidPotential ring root
        (bankWordEpochNext ring root z e) + n ≤
      bankWordEpochPrepaidPotential ring root z := by
  have hnormal := bankWordEpochS6FirstNormalizationRelease
    ring root z e hsaw hfirst hterminal
  have hmechanical := bankWordEpochPrepaidMechanicalCap
    ring root hn (bankWordEpochNext ring root z e)
  have hslots := Nat.mul_le_mul_left (5 * n ^ 2 + 2 * n)
    (bankWordEpochSoftLapsRemainingWeak ring root z e)
  have hsq : 3 * n ≤ n ^ 2 := by
    calc
      3 * n = n * 3 := by ac_rfl
      _ ≤ n * n := Nat.mul_le_mul_left n (by omega : 3 ≤ n)
      _ = n ^ 2 := by rw [Nat.pow_two]
  have hcredit : (5 * n ^ 2 + 2 * n) + n ≤ 6 * n ^ 2 := by
    omega
  change
    bankWordEpochPrepaidMechanical ring root
        (bankWordEpochNext ring root z e) +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root
          (bankWordEpochNext ring root z e) +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root
        (bankWordEpochNext ring root z e) + n ≤
    bankWordEpochPrepaidMechanical ring root z +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root z +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z
  rw [hnormal.1, hnormal.2]
  omega

/-- A later genuine soft S6 buys back a whole mechanical B
slot from the causally recorded soft-lap reserve. Because the
old RUNNING mechanical slot already contains 2n, this debit
pays a STRICT n-unit drop, not just weak monotonicity. -/
theorem bankWordEpochS6SoftPrepaidStrict {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (z : BankWordEpochState n) (e : Fin n)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (hsaw :
      (bankWordEpochChargeLedger root z).sawSOne = true)
    (hsoft :
      bankWordEpochChargeIsSoft root
        (bankWordEpochSelectedReceipt ring z e) = true)
    (hlaps :
      (bankWordEpochChargeLedger root z).softLaps <
        8 * ceilLogTwo (ceilLogTwo n) + 4) :
    bankWordEpochPrepaidPotential ring root
        (bankWordEpochNext ring root z e) + n ≤
      bankWordEpochPrepaidPotential ring root z := by
  have hslot := bankWordEpochS6SoftSlotDecreases
    ring root z e hsaw hsoft hlaps
  have hscaled := congrArg
    (fun v : Nat => (5 * n ^ 2 + 2 * n) * v) hslot
  rw [Nat.mul_add, Nat.mul_one] at hscaled
  have hmechanical := bankWordEpochPrepaidMechanicalCap
    ring root hn (bankWordEpochNext ring root z e)
  have hbefore :
      bankWordEpochPrepaidMechanical ring root z =
        bankWordEpochMechanicalBudget ring root z := by
    simp [bankWordEpochPrepaidMechanical, hrun]
  have hmin : n ≤ bankWordEpochPrepaidMechanical ring root z := by
    rw [hbefore]
    change n ≤ n * startPsi ring root z.2.1 + 2 * n
    omega
  have hpay :
      bankWordEpochPrepaidMechanical ring root
          (bankWordEpochNext ring root z e) +
        (5 * n ^ 2 + 2 * n) *
          bankWordEpochSoftLapRemaining root
            (bankWordEpochNext ring root z e) + n ≤
      bankWordEpochPrepaidMechanical ring root z +
        (5 * n ^ 2 + 2 * n) *
          bankWordEpochSoftLapRemaining root z := by
    omega
  have hnormal := Nat.mul_le_mul_left (6 * n ^ 2)
    (bankWordEpochNormalizationFlagWeak ring root z e)
  change
    bankWordEpochPrepaidMechanical ring root
        (bankWordEpochNext ring root z e) +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root
          (bankWordEpochNext ring root z e) +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root
        (bankWordEpochNext ring root z e) + n ≤
    bankWordEpochPrepaidMechanical ring root z +
      (5 * n ^ 2 + 2 * n) *
        bankWordEpochSoftLapRemaining root z +
      6 * n ^ 2 * bankWordEpochInheritedUnnormalized root z
  omega

/-- ONE named missing causal-reachability debit, at exactly
the proposed old RUNNING-root S6 state. It includes the
observation/ledger synchronization (sawSOne), and says that
EITHER the first post-S1 S6 may release the inherited 6n^2
reserve OR a genuinely SOFT S6 has a spendable lap (<L).

In particular, an already normalized HARD S6 is not counted
as a soft lap, and an already normalized SOFT S6 at lap=L has
zero remaining-slot debit. Both cases require a source-level
lease/frontier or worker-terminal argument, not arithmetic. -/
def BankWordEpochRunningS6SpendableCredit {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z →
    BankWordEpochSOneReached z →
    ¬ BankWordEpochWorkerLaunched z →
    (z.2.1 root).ser.cert = .RUNNING →
    ∀ e : Fin n,
      e = root →
      (bankWordEpochSelectedReceipt ring z e).serializer.row = "S6" →
      (bankWordEpochChargeLedger root z).sawSOne = true ∧
        ((bankWordEpochChargeLedger root z).normalized = false ∨
          (bankWordEpochChargeIsSoft root
             (bankWordEpochSelectedReceipt ring z e) = true ∧
           (bankWordEpochChargeLedger root z).softLaps <
             8 * ceilLogTwo (ceilLogTwo n) + 4))

/-- The S6 strict ticket follows if the ONE outstanding
reachable-credit proposition is available; it is not asserted
unconditionally. -/
theorem bankWordEpochRunningS6StrictOfSpendableCredit {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hcredit : BankWordEpochRunningS6SpendableCredit ring root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hSOne : BankWordEpochSOneReached z)
    (hnot : ¬ BankWordEpochWorkerLaunched z)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (e : Fin n)
    (he : e = root)
    (hS6 :
      (bankWordEpochSelectedReceipt ring z e).serializer.row = "S6") :
    bankWordEpochPrepaidPotential ring root
        (bankWordEpochNext ring root z e) + n ≤
      bankWordEpochPrepaidPotential ring root z := by
  obtain ⟨hsaw, hcase⟩ :=
    hcredit z hz hSOne hnot hrun e he hS6
  have hterminal :=
    bankWordEpochS6ReceiptTerminal ring root z e he hS6
  rcases hcase with hfirst | ⟨hsoft, hlaps⟩
  · exact bankWordEpochS6FirstPrepaidStrict
      ring root hn z e hsaw hfirst hterminal
  · exact bankWordEpochS6SoftPrepaidStrict
      ring root hn z e hrun hsaw hsoft hlaps

/-- The exact original proposition follows conditionally
from the spendable credit. The statement of
BankWordEpochRunningS6PrepaidDebit itself is unchanged. -/
theorem bankWordEpochRunningS6PrepaidDebitOfSpendableCredit
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hcredit : BankWordEpochRunningS6SpendableCredit ring root s) :
    BankWordEpochRunningS6PrepaidDebit ring root s := by
  intro z hz hSOne hnot hrun e he hS6
  have hstrict := bankWordEpochRunningS6StrictOfSpendableCredit
    ring root hn s hcredit z hz hSOne hnot hrun e he hS6
  omega

/-- A saturated historical ledger: n=5 has s=2, L=20,
and the old + new available slots are both zero.
This is a numerical/local-row configuration, NOT a proof that
a corresponding full WOriginGhost is reachable from its start. -/
def bankWordEpochS6ExhaustedLedgerSmall : BankWordEpochChargeLedger :=
  { sawSOne := true, normalized := true, softLaps := 20 }

theorem bankWordEpochS6ExhaustedLedgerSmallSaturation :
    ((8 * 2 + 5 : Nat) -
        (bankWordEpochS6ExhaustedLedgerSmall.softLaps + 1) = 0) ∧
    ((8 * 2 + 5 : Nat) -
        ((bankWordEpochS6ExhaustedLedgerSmall.softLaps + 1) + 1) = 0) ∧
    ¬ (bankWordEpochS6ExhaustedLedgerSmall.softLaps <
        8 * 2 + 4) := by
  change ((21 : Nat) - (20 + 1) = 0) ∧
    ((21 : Nat) - ((20 + 1) + 1) = 0) ∧
    ¬ (20 < 20)
  omega

/-- The previous five-site S6 local root can have
RUNNING/B/DONE, an F responder, startPsi=3 and old mechanical
charge 25; if its normalized soft reserve is saturated,
the new IDLE charge is 135 and no B debit remains.
This checks the scalar obstruction, not global reachability. -/
theorem bankWordEpochS6ExhaustedLocalCostGap :
    (25 + (135 : Nat) * (21 - (20 + 1))) <
      (135 + (135 : Nat) * (21 - ((20 + 1) + 1))) := by
  omega

/-- Partial Drift assembly: S6 now supplies both weak monotonicity
and a possible strict nominated physical root edge. Remaining
non-S6 edge weakness and other-state nomination are explicit
premises, not hidden theorems. In particular no unconditional
Drift for arbitrary initial s is claimed. -/
theorem bankWordEpochLeaseValidationDriftOfS6AndOtherRows {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hcredit : BankWordEpochRunningS6SpendableCredit ring root s)
    (hother : ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochSOneReached z →
      ¬ BankWordEpochWorkerLaunched z →
      ∀ e : Fin n,
        ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
          e = root ∧
          (bankWordEpochSelectedReceipt ring z e).serializer.row =
            "S6") →
        bankWordEpochPrepaidPotential ring root
          (bankWordEpochNext ring root z e) ≤
        bankWordEpochPrepaidPotential ring root z)
    (hnomOther : ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochSOneReached z →
      ¬ BankWordEpochWorkerLaunched z →
      ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
        (bankWordEpochSelectedReceipt ring z root).serializer.row =
          "S6") →
      ∃ e : Fin n,
        bankWordEpochPrepaidPotential ring root
            (bankWordEpochNext ring root z e) + n ≤
          bankWordEpochPrepaidPotential ring root z) :
    BankWordEpochLeaseValidationDrift ring root s := by
  have hweak : ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochSOneReached z →
      ¬ BankWordEpochWorkerLaunched z →
      ∀ e : Fin n,
        bankWordEpochPrepaidPotential ring root
          (bankWordEpochNext ring root z e) ≤
        bankWordEpochPrepaidPotential ring root z := by
    intro z hz hSOne hnot e
    by_cases hrow :
        (z.2.1 root).ser.cert = .RUNNING ∧
        e = root ∧
        (bankWordEpochSelectedReceipt ring z e).serializer.row =
          "S6"
    · exact (bankWordEpochRunningS6PrepaidDebitOfSpendableCredit
        ring root hn s hcredit)
        z hz hSOne hnot hrow.1 e hrow.2.1 hrow.2.2
    · exact hother z hz hSOne hnot e hrow
  have hstrict : ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochSOneReached z →
      ¬ BankWordEpochWorkerLaunched z →
      ∃ e : Fin n,
        bankWordEpochPrepaidPotential ring root
          (bankWordEpochNext ring root z e) + n ≤
        bankWordEpochPrepaidPotential ring root z := by
    intro z hz hSOne hnot
    by_cases hrow :
        (z.2.1 root).ser.cert = .RUNNING ∧
        (bankWordEpochSelectedReceipt ring z root).serializer.row =
          "S6"
    · refine ⟨root, ?_⟩
      exact bankWordEpochRunningS6StrictOfSpendableCredit
        ring root hn s hcredit z hz hSOne hnot hrow.1
        root rfl hrow.2
    · exact hnomOther z hz hSOne hnot hrow
  exact bankWordEpochLeaseValidationDriftOfPrepaidRows
    ring root s hn hweak hstrict

end L3.RenewalReferenceClock

/-!
Serializer lease audit and hard-to-hard epoch correction.

The historical softLaps field in the
source above NEVER resets on hard acceptance, whereas the
literal physical siLease DOES reset to siLeaseMax. Consequently
the proposed across-history sum softLaps+siLease <= L is not a
preserved invariant, and a normalized hard S6 is not paid by a
soft S6 slot. The paper counts soft completions PER hard-to-hard
epoch and stops when the next genuine hard worker is launched.

The explicit five-site word below is a reproducible
witness for the historical-credit defect. Its physical old-row
observations are kept in one named, not-yet-kernel-proved Prop;
the finite-word reachability assertion itself is proved.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The *physical* serializer lease lives in ProjW.siLease.
Its hard-success transition is an unconditional reload to
c.siLeaseMax = 8*c.t+4, not a debit from historical softLaps. -/
theorem bankWordEpochHardAcceptanceReloadsLease
    (c : Compiled)
    (x y : Fin (c.siLeaseMax + 1))
    (soft done : Bool) :
    (leasePair c x y true soft done).1.val = c.siLeaseMax := by
  simp [leasePair]

/-- A soft acceptance subtracts one from the source lease,
with Nat saturation, as long as a simultaneous hard
acceptance and worker completion are absent. -/
theorem bankWordEpochSoftAcceptanceLeaseRow
    (c : Compiled)
    (x y : Fin (c.siLeaseMax + 1)) :
    (leasePair c x y false true false).1.val = x.val - 1 := by
  simp [leasePair]

/-- The actual source pairW uses precisely the same hard
reload, not a separately defined lease process. -/
theorem bankWordEpochPairWHardReload
    {c : Compiled} (x y : ProjW c)
    (hhard : (serW x y).hard.hardAccept = true) :
    (pairW x y).1.siLease.val = c.siLeaseMax := by
  simp [pairW, leasePair, hhard]

/-- A selected physical root hard acceptance reloads the
physical lease on the ORIGINAL phiW successor. -/
theorem bankWordEpochSelectedHardReload
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (he : e = root)
    (hhard :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
        true) :
    ((bankWordEpochNext ring root z e).2.1 root).siLease.val =
      (compileAdvice (ceilLogTwo n)).siLeaseMax := by
  subst e
  have hrow :
      (serW (z.2.1 root)
        (z.2.1 (ring.rightNeighbor root))).hard.hardAccept =
          true := hhard
  change ((phiW ring z.2.1 root) root).siLease.val =
    (compileAdvice (ceilLogTwo n)).siLeaseMax
  have hsource :
      (phiW ring z.2.1 root) root =
        (pairW (z.2.1 root)
          (z.2.1 (ring.rightNeighbor root))).1 := by
    simp [phiW, projectedEdge]
  rw [hsource]
  exact bankWordEpochPairWHardReload _ _ hrow

/-- A hard receipt does NOT reset the proof-only cumulative
softLaps counter. This is the exact foldr accounting row. -/
theorem bankWordEpochHardReceiptPreservesHistoricalSoftLaps
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hhard :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
        true) :
    (bankWordEpochChargeLedger root
      (bankWordEpochNext ring root z e)).softLaps =
      (bankWordEpochChargeLedger root z).softLaps := by
  have hsoft := bankWordEpochS6HardNotSoft root
    (bankWordEpochSelectedReceipt ring z e) hhard
  rw [bankWordEpochChargeLedgerNext]
  change (bankWordEpochChargeLedger root z).softLaps +
      (if (bankWordEpochChargeLedger root z).sawSOne &&
          bankWordEpochChargeIsSoft root
            (bankWordEpochSelectedReceipt ring z e)
        then 1 else 0) =
      (bankWordEpochChargeLedger root z).softLaps
  rw [hsoft]
  simp

/-- A positive historical soft count together with a hard
lease reload is strictly larger than the raw physical lease
cap. Thus the proposed cross-epoch invariant cannot be
preserved at such a row. -/
theorem bankWordEpochHardReloadBreaksHistoricalLeaseSum
    (c : Compiled) (laps : Nat)
    (x y : Fin (c.siLeaseMax + 1))
    (soft done : Bool)
    (hlaps : 0 < laps) :
    c.siLeaseMax <
      laps + (leasePair c x y true soft done).1.val := by
  rw [bankWordEpochHardAcceptanceReloadsLease]
  omega

/-- A correct PER-EPOCH ledger resets its soft count on any
hard acceptance, rather than retaining the entire historical
S1-to-present number of completed soft laps. -/
def bankWordEpochPerHardSoftCountStep
    (old : Nat) (hard soft : Bool) : Nat :=
  if hard then 0 else if soft then old + 1 else old

theorem bankWordEpochPerHardHardReset
    (old : Nat) (soft : Bool) :
    bankWordEpochPerHardSoftCountStep old true soft = 0 := by
  rfl

theorem bankWordEpochPerHardSoftIncrement
    (old : Nat) :
    bankWordEpochPerHardSoftCountStep old false true = old + 1 := by
  rfl

/-- Row-level lease conservation after a hard acceptance:
new epoch count zero plus newly reloaded physical lease L. -/
theorem bankWordEpochPerHardReloadBudget
    (c : Compiled) (old : Nat)
    (x y : Fin (c.siLeaseMax + 1))
    (soft done : Bool) :
    bankWordEpochPerHardSoftCountStep old true soft +
      (leasePair c x y true soft done).1.val = c.siLeaseMax := by
  rw [bankWordEpochPerHardHardReset,
    bankWordEpochHardAcceptanceReloadsLease]
  omega

/-- When a soft acceptance consumes a POSITIVE physical lease,
the per-hard-epoch count plus remaining lease stays constant.
The extra positivity hypothesis matters: a concurrent worker
completion at the incoming root can already have cleared the
lease, while a previously prepared CURRENT serializer still
soft-accepts on its later S6 row. -/
theorem bankWordEpochPerHardSoftConservation
    (c : Compiled) (old : Nat)
    (x y : Fin (c.siLeaseMax + 1))
    (hpositive : 0 < x.val)
    (hbudget : old + x.val = c.siLeaseMax) :
    bankWordEpochPerHardSoftCountStep old false true +
      (leasePair c x y false true false).1.val =
        c.siLeaseMax := by
  rw [bankWordEpochPerHardSoftIncrement,
    bankWordEpochSoftAcceptanceLeaseRow]
  omega

/-- Selected soft S6 does NOT inspect the old source lease.
The literal ROOT_OUT serializer guard reads only the RUNNING
phase, CURRENT validation mode, DONE output and F responder.
This small local example has source lease zero and soft S6. -/
theorem bankWordEpochSoftS6ZeroLeaseLocal
    (c : Compiled) :
    (serW
      (ProjW.ofAgent
        { Agent.blank c with
          l := true
          ser := { phase := .B, out := .DONE, probe := .NONE,
                   cert := .RUNNING, wphase := .CURRENT } })
      (ProjW.ofAgent
        { Agent.blank c with
          ser := { phase := .F, out := .DONE, probe := .NONE,
                   cert := .IDLE, wphase := .CURRENT } })).hard.softAccept =
      true ∧
    (serW
      (ProjW.ofAgent
        { Agent.blank c with
          l := true
          ser := { phase := .B, out := .DONE, probe := .NONE,
                   cert := .RUNNING, wphase := .CURRENT } })
      (ProjW.ofAgent
        { Agent.blank c with
          ser := { phase := .F, out := .DONE, probe := .NONE,
                   cert := .IDLE, wphase := .CURRENT } })).row =
      "S6" := by
  constructor <;> rfl

/-- Exact small arithmetic of the first pre-hard S6 after
three completed soft laps. The normalized soft-lap slot does
not move on a hard S6; a RUNNING B old mechanical 25 becomes
IDLE B=135 and the purported weak/strict ticket fails. -/
theorem bankWordEpochHardAfterSoftSmallCostGap :
    (25 + (135 : Nat) * (21 - (3 + 1))) + 5 <
      (135 + (135 : Nat) * (21 - (3 + 1))) ∧
    ¬ (3 + 20 ≤ (20 : Nat)) := by
  omega

/-! Finite source-scope scheduler witness. -/

private def bankWordEpochFiveRootRing : DirectedRing 5 :=
  ⟨by decide⟩

/-- The physical W entrance is deliberately arbitrary:
its root begins REQUESTED with zero lease, BEFORE a
provenance-generated S0 ticket. Every other agent is blank.
The sole protected native root is at physical site zero. -/
private def bankWordEpochFiveInitial
    (i : Fin 5) :
    ProjW (compileAdvice (ceilLogTwo 5)) :=
  if i = (0 : Fin 5) then
    ProjW.ofAgent
      { Agent.blank (compileAdvice (ceilLogTwo 5)) with
        l := true
        sh := true
        ser := { phase := .C, out := .NEW, probe := .NONE,
                 cert := .REQUESTED, wphase := .OFF } }
  else
    ProjW.ofAgent (Agent.blank (compileAdvice (ceilLogTwo 5)))

/-- First S1 with no inherited request ticket, followed by the
literal root hard S6. The selected edges are in chronological
order; each is an actual Fin 5 scheduler edge. -/
private def bankWordEpochFiveInitialLap : List (Fin 5) :=
  [0, 1, 0, 1, 2, 1, 2, 3, 2, 3, 4, 3, 3, 2, 1, 0]

/-- Another root S0/S1 and complete broadcast/return lap.
A new request ticket exists, but a positive source lease
makes S1 CURRENT, so the S6 terminal is soft. -/
private def bankWordEpochFiveSubsequentLap : List (Fin 5) :=
  [4, 0, 1, 1, 0, 1, 2, 2, 1, 2,
   3, 3, 2, 3, 4, 3, 3, 2, 1, 0]

/-- After initial hard and three soft S6s, begin the next
lap but stop one edge BEFORE its final hard root S6.
The next selected physical edge is root=0. -/
private def bankWordEpochFiveBeforeHardWord : List (Fin 5) :=
  bankWordEpochFiveInitialLap ++
  bankWordEpochFiveSubsequentLap ++
  bankWordEpochFiveSubsequentLap ++
  bankWordEpochFiveSubsequentLap ++
  (bankWordEpochFiveSubsequentLap.take 19)

private noncomputable def bankWordEpochFiveBeforeHardState :
    BankWordEpochState 5 :=
  bankWordEpochRun bankWordEpochFiveRootRing (0 : Fin 5)
    (bankWordEpochStart bankWordEpochFiveInitial)
    bankWordEpochFiveBeforeHardWord

/-- The finite-word proof of reachability itself is exact:
no fabricated WOriginGhost or artificial stopped latch. -/
theorem bankWordEpochFiveBeforeHardReachable :
    BankWordEpochReachable bankWordEpochFiveRootRing
      (0 : Fin 5) bankWordEpochFiveInitial
      bankWordEpochFiveBeforeHardState := by
  exact ⟨bankWordEpochFiveBeforeHardWord, rfl⟩

/-- Full physically checkable evidence for the 95-edge word.
The source-row replay indicates these values; verifying the
entire closed 95-edge ghost computation in Lean is kept
separate from the elementary reachability proof above. -/
structure BankWordEpochFiveBeforeHardEvidence : Prop where
  reached : BankWordEpochSOneReached bankWordEpochFiveBeforeHardState
  noWorker : ¬ BankWordEpochWorkerLaunched bankWordEpochFiveBeforeHardState
  running :
    (bankWordEpochFiveBeforeHardState.2.1 (0 : Fin 5)).ser.cert =
      .RUNNING
  s6 :
    (bankWordEpochSelectedReceipt bankWordEpochFiveRootRing
      bankWordEpochFiveBeforeHardState (0 : Fin 5)).serializer.row =
      "S6"
  hard :
    (bankWordEpochSelectedReceipt bankWordEpochFiveRootRing
      bankWordEpochFiveBeforeHardState
        (0 : Fin 5)).serializer.hard.hardAccept = true
  saw :
    (bankWordEpochChargeLedger (0 : Fin 5)
      bankWordEpochFiveBeforeHardState).sawSOne = true
  normalized :
    (bankWordEpochChargeLedger (0 : Fin 5)
      bankWordEpochFiveBeforeHardState).normalized = true
  laps :
    (bankWordEpochChargeLedger (0 : Fin 5)
      bankWordEpochFiveBeforeHardState).softLaps = 3
  sourceLease :
    (bankWordEpochFiveBeforeHardState.2.1
      (0 : Fin 5)).siLease.val = 0

/-- Under the explicit closed replay observations, the ORIGINAL
spendable-credit proposition is false. No physical row is
silently treated as a ghost terminal: hardAccept is taken from
the selected true serializer receipt. -/
theorem bankWordEpochFiveCreditRefutedOfEvidence
    (h : BankWordEpochFiveBeforeHardEvidence) :
    ¬ BankWordEpochRunningS6SpendableCredit
      bankWordEpochFiveRootRing (0 : Fin 5)
      bankWordEpochFiveInitial := by
  intro hcredit
  obtain ⟨hsaw, hcases⟩ :=
    hcredit bankWordEpochFiveBeforeHardState
      bankWordEpochFiveBeforeHardReachable
      h.reached h.noWorker h.running
      (0 : Fin 5) rfl h.s6
  rcases hcases with hfirst | ⟨hsoft, hlaps⟩
  · rw [h.normalized] at hfirst
    cases hfirst
  · have hnotSoft := bankWordEpochS6HardNotSoft
      (0 : Fin 5)
      (bankWordEpochSelectedReceipt
        bankWordEpochFiveRootRing
        bankWordEpochFiveBeforeHardState (0 : Fin 5))
      h.hard
    rw [hnotSoft] at hsoft
    cases hsoft

/-! A corrected statement: a hard S6 may LAUNCH the worker.
Such a successor is terminal for the first-worker first-hit
problem; it is not required to pay an old soft-lap ticket. -/

/-- The actual first worker launch is treated as an absorbing
stop for credit accounting. This is the physical prepaid
potential everywhere else, and zero at a stopped child. -/
def bankWordEpochWorkerStoppedPrepaid {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Nat :=
  if z.2.2.worker.isSome then 0
  else bankWordEpochPrepaidPotential ring root z

theorem bankWordEpochWorkerStoppedPrepaidOfLaunched
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (h : BankWordEpochWorkerLaunched z) :
    bankWordEpochWorkerStoppedPrepaid ring root z = 0 := by
  obtain ⟨worker, hworker⟩ := h
  simp [bankWordEpochWorkerStoppedPrepaid, hworker]

theorem bankWordEpochWorkerStoppedPrepaidOfNotLaunched
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (h : ¬ BankWordEpochWorkerLaunched z) :
    bankWordEpochWorkerStoppedPrepaid ring root z =
      bankWordEpochPrepaidPotential ring root z := by
  cases hworker : z.2.2.worker with
  | none =>
      simp [bankWordEpochWorkerStoppedPrepaid, hworker]
  | some worker =>
      exact False.elim (h ⟨worker, hworker⟩)

theorem bankWordEpochWorkerStoppedPrepaidLe
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) :
    bankWordEpochWorkerStoppedPrepaid ring root z ≤
      bankWordEpochPrepaidPotential ring root z := by
  unfold bankWordEpochWorkerStoppedPrepaid
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- Every old RUNNING mechanical charge contains at least 2n,
hence at least the n-unit nominated strict ticket. -/
theorem bankWordEpochRunningPrepaidAtLeastN
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hrun : (z.2.1 root).ser.cert = .RUNNING) :
    n ≤ bankWordEpochPrepaidPotential ring root z := by
  have hmechanical :
      bankWordEpochPrepaidMechanical ring root z =
        bankWordEpochMechanicalBudget ring root z := by
    simp [bankWordEpochPrepaidMechanical, hrun]
  unfold bankWordEpochPrepaidPotential
  rw [hmechanical]
  unfold bankWordEpochMechanicalBudget
  omega

/-- Corrected paper interface: either a genuine hard terminal
LAUNCHES the W-origin worker, or this actual S6 has a
spendable first-terminal/soft-lap slot. A historical hard S6
does not have to be a soft receipt. -/
def BankWordEpochRunningS6SpendableOrWorkerLaunch
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z →
    BankWordEpochSOneReached z →
    ¬ BankWordEpochWorkerLaunched z →
    (z.2.1 root).ser.cert = .RUNNING →
    ∀ e : Fin n,
      e = root →
      (bankWordEpochSelectedReceipt ring z e).serializer.row = "S6" →
      BankWordEpochWorkerLaunched
        (bankWordEpochNext ring root z e) ∨
      ((bankWordEpochChargeLedger root z).sawSOne = true ∧
        ((bankWordEpochChargeLedger root z).normalized = false ∨
          (bankWordEpochChargeIsSoft root
            (bankWordEpochSelectedReceipt ring z e) = true ∧
           (bankWordEpochChargeLedger root z).softLaps <
             8 * ceilLogTwo (ceilLogTwo n) + 4)))

/-- The old proposition implies the corrected one, but not
conversely: a genuine hard S6 is allowed to win immediately. -/
theorem bankWordEpochCorrectedCreditOfOriginal
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (h : BankWordEpochRunningS6SpendableCredit ring root s) :
    BankWordEpochRunningS6SpendableOrWorkerLaunch
      ring root s := by
  intro z hz hs hnot hrun e he hS6
  exact Or.inr (h z hz hs hnot hrun e he hS6)

/-- If the child starts a genuine worker, the stopped potential
pays the strict n-unit ticket even when the old cumulative
soft-lap ledger has no spendable slot. -/
theorem bankWordEpochWorkerLaunchStoppedStrict
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hnot : ¬ BankWordEpochWorkerLaunched z)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (hlaunch :
      BankWordEpochWorkerLaunched
        (bankWordEpochNext ring root z e)) :
    bankWordEpochWorkerStoppedPrepaid ring root
        (bankWordEpochNext ring root z e) + n ≤
      bankWordEpochWorkerStoppedPrepaid ring root z := by
  rw [bankWordEpochWorkerStoppedPrepaidOfLaunched
    ring root (bankWordEpochNext ring root z e) hlaunch]
  rw [bankWordEpochWorkerStoppedPrepaidOfNotLaunched
    ring root z hnot]
  simpa only [Nat.zero_add] using
    bankWordEpochRunningPrepaidAtLeastN ring root z hrun

/-- This replaces the false unstopped S6 strict ticket:
under the corrected causal interface, EVERY continuing S6
either pays its old physical credit or enters the actual
worker-launch stopping set. -/
theorem bankWordEpochRunningS6StoppedStrictOfCorrected
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hcorrect :
      BankWordEpochRunningS6SpendableOrWorkerLaunch
        ring root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hs : BankWordEpochSOneReached z)
    (hnot : ¬ BankWordEpochWorkerLaunched z)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (e : Fin n) (he : e = root)
    (hS6 :
      (bankWordEpochSelectedReceipt ring z e).serializer.row = "S6") :
    bankWordEpochWorkerStoppedPrepaid ring root
        (bankWordEpochNext ring root z e) + n ≤
      bankWordEpochWorkerStoppedPrepaid ring root z := by
  rcases hcorrect z hz hs hnot hrun e he hS6 with
    hlaunch | ⟨hsaw, hcase⟩
  · exact bankWordEpochWorkerLaunchStoppedStrict
      ring root z e hnot hrun hlaunch
  · have hterminal := bankWordEpochS6ReceiptTerminal
      ring root z e he hS6
    have hstrict :
        bankWordEpochPrepaidPotential ring root
            (bankWordEpochNext ring root z e) + n ≤
          bankWordEpochPrepaidPotential ring root z := by
      rcases hcase with hfirst | ⟨hsoft, hlaps⟩
      · exact bankWordEpochS6FirstPrepaidStrict
          ring root hn z e hsaw hfirst hterminal
      · exact bankWordEpochS6SoftPrepaidStrict
          ring root hn z e hrun hsaw hsoft hlaps
    have hnext := bankWordEpochWorkerStoppedPrepaidLe
      ring root (bankWordEpochNext ring root z e)
    rw [bankWordEpochWorkerStoppedPrepaidOfNotLaunched
      ring root z hnot]
    exact Nat.le_trans (Nat.add_le_add_right hnext n)
      hstrict

end L3.RenewalReferenceClock


/-!
Per-genuine-hard-acceptance ghost ledger.

The cumulative historical softLaps
ledger above is deliberately preserved only as history.
This new observer counts soft S1 starts and matched soft S6
finishes separately in each causally witnessed hard epoch.
The selected old-row receipt, validation provenance and worker
provenance are never replaced by guessed physical state.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The ticket and worker fields mirror the existing origin
observer. hardEpochs counts genuinely witnessed hard S6
acceptances, rather than every physical hardAccept byte pattern.
workerDone is sticky until the following genuine acceptance.
rootLease is the most recently observed result of leasePair on
a service incident to root; after the first genuine acceptance
it has been initialized by the hard lease reload. -/
structure BankWordHardEpochLedger (n : Nat) where
  validation : Fin n → Option WValidationTicket
  worker : Option (WWorkerTrail n)
  hardEpochs : Nat
  softStarts : Nat
  softFinishes : Nat
  pendingSoft : Bool
  workerDone : Bool
  rootLease : Nat

def bankWordHardEpochInitial {n : Nat} :
    BankWordHardEpochLedger n :=
  { validation := fun _ => none
    worker := none
    hardEpochs := 0
    softStarts := 0
    softFinishes := 0
    pendingSoft := false
    workerDone := false
    rootLease := 0 }

/-- This predicate is historical: it uses actual validation
tickets, not just hardAccept on a physical S6 lookalike. -/
def bankWordHardEpochGenuine {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n)))
    (a : BankWordHardEpochLedger n) : Bool :=
  (wGenuineAcceptance root r.edge r.oldSource
    r.oldDestination (a.validation r.edge)
    (a.validation (ring.rightNeighbor r.edge))).isSome

/-- An S1 starts softly exactly when the selected old-row
transaction is S1 without hardS1. -/
def bankWordHardEpochSoftStart {n : Nat}
    (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n))) : Bool :=
  (r.edge == root) && (r.serializer.row == "S1") &&
    (!r.serializer.hard.hardS1)

/-- A counted soft finish is a selected S6 with softAccept;
the inherited pre-hard interval is excluded by the active
epoch test in bankWordHardEpochStep. -/
def bankWordHardEpochSoftFinish {n : Nat}
    (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n))) : Bool :=
  (r.edge == root) && (r.serializer.row == "S6") &&
    r.serializer.hard.softAccept

def bankWordHardEpochActive {n : Nat}
    (a : BankWordHardEpochLedger n) : Bool :=
  (a.hardEpochs != 0) && (!a.workerDone)

/-- One selected old-row edge. The validation and worker
provenance updates use the same old arguments and priority as
wOriginGhostStep. The physical lease reducer is the literal
leasePair; counters do not use its floored decrement as proof
that an old lease was positive. -/
def bankWordHardEpochStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n)))
    (a : BankWordHardEpochLedger n) :
    BankWordHardEpochLedger n :=
  let next := ring.rightNeighbor r.edge
  let stamp := r.service
  let tickets := wValidationPair stamp
    r.oldSource r.oldDestination
    (a.validation r.edge) (a.validation next)
  let accept := wGenuineAcceptance root r.edge
    r.oldSource r.oldDestination
    (a.validation r.edge) (a.validation next)
  let worker := wWorkerReceiptStep root r.edge next stamp
    r.oldSource r.oldDestination accept a.worker
  let lease := leasePair (compileAdvice (ceilLogTwo n))
    r.oldSource.siLease r.oldDestination.siLease
    r.serializer.hard.hardAccept
    r.serializer.hard.softAccept r.worker.done
  let fresh := bankWordHardEpochActive a
  let started := fresh && bankWordHardEpochSoftStart root r
  let finished := fresh && bankWordHardEpochSoftFinish root r
  let reset := accept.isSome
  { validation := fun i =>
      if i = r.edge then tickets.1
      else if i = next then tickets.2 else a.validation i
    worker := worker.1
    hardEpochs := if reset then a.hardEpochs + 1 else a.hardEpochs
    softStarts := if reset then 0
      else if started then a.softStarts + 1 else a.softStarts
    softFinishes := if reset then 0
      else if finished then a.softFinishes + 1 else a.softFinishes
    pendingSoft := if reset then false
      else if finished then false
      else if started then true else a.pendingSoft
    workerDone := if reset then false
      else a.workerDone || (fresh && worker.2.isSome)
    rootLease :=
      if r.edge = root then lease.1.val
      else if next = root then lease.2.val
      else a.rootLease }

/-- Chronological fold over the stored newest-first receipt list. -/
def bankWordHardEpochLedger {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : BankWordHardEpochLedger n :=
  z.2.2.services.foldr (bankWordHardEpochStep ring root)
    bankWordHardEpochInitial

/-- All epoch events are read from the actual selected phiW
service; the ledger is only a ghost and changes no transition. -/
theorem bankWordHardEpochLedgerNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e) =
      bankWordHardEpochStep ring root
        (bankWordEpochSelectedReceipt ring z e)
        (bankWordHardEpochLedger ring root z) := by
  rfl

/-- At a genuine acceptance, both soft counters, the pending
bit and workerDone reset. This holds independent of earlier
inherited or expired soft receipt counts. -/
theorem bankWordHardEpochGenuineReset {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n)))
    (a : BankWordHardEpochLedger n)
    (hgen : bankWordHardEpochGenuine ring root r a = true) :
    (bankWordHardEpochStep ring root r a).hardEpochs =
        a.hardEpochs + 1 ∧
    (bankWordHardEpochStep ring root r a).softStarts = 0 ∧
    (bankWordHardEpochStep ring root r a).softFinishes = 0 ∧
    (bankWordHardEpochStep ring root r a).pendingSoft = false ∧
    (bankWordHardEpochStep ring root r a).workerDone = false := by
  unfold bankWordHardEpochGenuine at hgen
  simp [bankWordHardEpochStep, hgen]

/-- After a witnessed hard epoch starts, a soft S1 increments
only softStarts. The causal matching obligation is recorded by
pendingSoft, not inferred from the lease value. -/
theorem bankWordHardEpochSoftStartCount {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n)))
    (a : BankWordHardEpochLedger n)
    (hgen : bankWordHardEpochGenuine ring root r a = false)
    (hactive : bankWordHardEpochActive a = true)
    (hstart : bankWordHardEpochSoftStart root r = true) :
    (bankWordHardEpochStep ring root r a).softStarts =
      a.softStarts + 1 := by
  simp [bankWordHardEpochStep, bankWordHardEpochGenuine,
    bankWordHardEpochActive] at hgen hactive ⊢
  simp [hgen, hactive, hstart]

/-- Similarly a soft S6 is counted once, but its spendability
requires a separate causal matching fact. -/
theorem bankWordHardEpochSoftFinishCount {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n)))
    (a : BankWordHardEpochLedger n)
    (hgen : bankWordHardEpochGenuine ring root r a = false)
    (hactive : bankWordHardEpochActive a = true)
    (hfinish : bankWordHardEpochSoftFinish root r = true) :
    (bankWordHardEpochStep ring root r a).softFinishes =
      a.softFinishes + 1 := by
  simp [bankWordHardEpochStep, bankWordHardEpochGenuine,
    bankWordHardEpochActive] at hgen hactive ⊢
  simp [hgen, hactive, hfinish]

/-- The actual target invariant, rather than a false universal
assertion about arbitrary initial local S6. The conditional here
means that it is asserted only inside a witnessed hard epoch and
before that witnessed worker's completion. -/
def BankWordHardEpochCleanInvariant {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  let a := bankWordHardEpochLedger ring root z
  (0 < a.hardEpochs ∧ a.workerDone = false) →
    a.softFinishes ≤ a.softStarts ∧
    a.softStarts ≤ 8 * ceilLogTwo (ceilLogTwo n) + 4 ∧
    a.softStarts - a.softFinishes =
      (if a.pendingSoft then 1 else 0) ∧
    (z.2.1 root).siLease.val =
      (8 * ceilLogTwo (ceilLogTwo n) + 4) - a.softFinishes ∧
    ((z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .CURRENT →
      a.pendingSoft = true)

/-- The arithmetic consequence which the old cumulative
softLaps proof did not have: a pending matched soft start
has a positive spendable root lease, including at the last
positive slot. -/
theorem bankWordHardEpochPendingSpendable
    (L starts finishes lease : Nat) (pending : Bool)
    (horder : finishes ≤ starts)
    (hcap : starts ≤ L)
    (hbalance : starts - finishes =
      (if pending then 1 else 0))
    (hpending : pending = true)
    (hlease : lease = L - finishes) :
    0 < lease := by
  rw [hpending, if_pos rfl] at hbalance
  omega

/-- The real clean-epoch invariant implies the nonvacuous
positive-lease assertion at every RUNNING/CURRENT root. -/
theorem bankWordHardEpochRunningCurrentSpendable {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hclean : BankWordHardEpochCleanInvariant ring root z)
    (hactive : 0 <
      (bankWordHardEpochLedger ring root z).hardEpochs)
    (hnotdone :
      (bankWordHardEpochLedger ring root z).workerDone = false)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (hcurrent : (z.2.1 root).ser.wphase = .CURRENT) :
    (bankWordHardEpochLedger ring root z).pendingSoft = true ∧
      0 < (z.2.1 root).siLease.val := by
  have h := hclean ⟨hactive, hnotdone⟩
  have hpending : (bankWordHardEpochLedger ring root z).pendingSoft =
      true := h.2.2.2.2 ⟨hrun, hcurrent⟩
  refine ⟨hpending, ?_⟩
  exact bankWordHardEpochPendingSpendable
    (8 * ceilLogTwo (ceilLogTwo n) + 4)
    (bankWordHardEpochLedger ring root z).softStarts
    (bankWordHardEpochLedger ring root z).softFinishes
    (z.2.1 root).siLease.val
    (bankWordHardEpochLedger ring root z).pendingSoft
    h.1 h.2.1 h.2.2.1 hpending h.2.2.2.1

/-- The literal row-level S1 reads the zero lease and starts
VALIDATING; this does not use a global historical credit sum. -/
theorem bankWordHardEpochZeroLeaseHardStart
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hreq : x.ser.cert = .REQUESTED)
    (hzero : x.siLease.val = 0) :
    (serW x y).row = "S1" ∧
    (serW x y).hard.hardS1 = true ∧
    (serW x y).x.wphase = .VALIDATING := by
  have hrow := serRootOutgoingStart x y hx hy hreq
  refine ⟨hrow.1, ?_, ?_⟩
  · change ((postW x y).eX.l &&
        (x.ser.cert == .REQUESTED) &&
        (x.siLease.val == 0)) = true
    simp [hx, hreq, hzero]
  · simp [serW, serializerStep, ProjW.lift,
      hx, hy, hreq, hzero, serTbStar]

/-- If the clean-epoch count has reached L, the next actual
requested root S1 has zero source lease and is hard. -/
theorem bankWordHardEpochLastSlotNextHard {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hclean : BankWordHardEpochCleanInvariant ring root z)
    (hactive : 0 <
      (bankWordHardEpochLedger ring root z).hardEpochs)
    (hnotdone :
      (bankWordHardEpochLedger ring root z).workerDone = false)
    (hexhausted :
      (bankWordHardEpochLedger ring root z).softFinishes =
        8 * ceilLogTwo (ceilLogTwo n) + 4)
    (hx : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eY.l = false)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED) :
    (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).hard.hardS1 = true ∧
    (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).x.wphase =
        .VALIDATING := by
  have h := hclean ⟨hactive, hnotdone⟩
  have hzero : (z.2.1 root).siLease.val = 0 := by
    rw [h.2.2.2.1, hexhausted]
    omega
  have hrow := bankWordHardEpochZeroLeaseHardStart
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hx hy hreq hzero
  exact ⟨hrow.2.1, hrow.2.2⟩

/-- A new charge replaces historical softLaps by the count
since the latest genuine hard acceptance. Its first epoch
is not used to pay the inherited initial interval. -/
def bankWordHardEpochPrepaid {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Nat :=
  bankWordEpochPrepaidMechanical ring root z +
    (5 * n ^ 2 + 2 * n) *
      ((8 * ceilLogTwo (ceilLogTwo n) + 4) -
        (bankWordHardEpochLedger ring root z).softFinishes)

/-- This potential stops either when the current worker
finishes or when a later genuine hard acceptance starts a
different epoch. It must not be reused with a new epoch index. -/
def bankWordHardEpochStoppedPrepaid {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (epoch : Nat) (z : BankWordEpochState n) : Nat :=
  if (bankWordHardEpochLedger ring root z).hardEpochs = epoch ∧
      (bankWordHardEpochLedger ring root z).workerDone = false
  then bankWordHardEpochPrepaid ring root z else 0

/-- Strict n-ticket at a matched soft S6, using the new
per-hard-epoch finish count rather than the cumulative ledger.
The two premises are the precise event synchronization and
remaining positive lease-slot consequences of the invariant. -/
theorem bankWordHardEpochSoftStrictTicket {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n) (z : BankWordEpochState n)
    (e : Fin n)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (hfinish :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).softFinishes =
      (bankWordHardEpochLedger ring root z).softFinishes + 1)
    (hslot :
      (bankWordHardEpochLedger ring root z).softFinishes <
        8 * ceilLogTwo (ceilLogTwo n) + 4) :
    bankWordHardEpochPrepaid ring root
      (bankWordEpochNext ring root z e) + n ≤
    bankWordHardEpochPrepaid ring root z := by
  have hnext := bankWordEpochPrepaidMechanicalCap
    ring root hn (bankWordEpochNext ring root z e)
  have hbefore :
      bankWordEpochPrepaidMechanical ring root z =
        bankWordEpochMechanicalBudget ring root z := by
    simp [bankWordEpochPrepaidMechanical, hrun]
  have hold : n ≤ bankWordEpochPrepaidMechanical ring root z := by
    rw [hbefore]
    change n ≤ n * startPsi ring root z.2.1 + 2 * n
    omega
  have hremaining :
      ((8 * ceilLogTwo (ceilLogTwo n) + 4) -
          ((bankWordHardEpochLedger ring root z).softFinishes + 1)) + 1 =
      (8 * ceilLogTwo (ceilLogTwo n) + 4) -
          (bankWordHardEpochLedger ring root z).softFinishes := by
    omega
  have hpaid := congrArg
    (fun k : Nat => (5 * n ^ 2 + 2 * n) * k) hremaining
  rw [Nat.mul_add, Nat.mul_one] at hpaid
  change bankWordEpochPrepaidMechanical ring root
      (bankWordEpochNext ring root z e) +
    (5 * n ^ 2 + 2 * n) *
      ((8 * ceilLogTwo (ceilLogTwo n) + 4) -
        (bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root z e)).softFinishes) + n ≤
    bankWordEpochPrepaidMechanical ring root z +
    (5 * n ^ 2 + 2 * n) *
      ((8 * ceilLogTwo (ceilLogTwo n) + 4) -
        (bankWordHardEpochLedger ring root z).softFinishes)
  rw [hfinish]
  omega

end L3.RenewalReferenceClock

/-!
Source-scope progress: selected genuine reset, physical
frame, and local S1 lease discrimination.

The requested global BankWordHardEpochCleanInvariant reachability
theorem is not asserted here: a proof must establish preservation of
physical root/provenance coupling after arbitrary genuine hard
acceptance, physical-worker completion synchrony, and exclusion of
unwitnessed post-hard hardAccept rows. The existing
bankWordEpochSOneRunningBReachable requires an independently supplied
BankWordSerializerRootClass, whereas BankWordEpochReachable alone
does not include that hypothesis. No invented premise is introduced.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The ticket-checked genuine receipt necessarily selects the
old ROOT_OUT hard S6. The conclusion mentions the actual owner
row rather than arbitrary diagnostic fields of WEdgeReceipt. -/
theorem bankWordHardEpochGenuineOwnerFlags {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n)))
    (a : BankWordHardEpochLedger n)
    (h : bankWordHardEpochGenuine ring root r a = true) :
    r.edge = root ∧
      (serW r.oldSource r.oldDestination).row = "S6" ∧
      (serW r.oldSource r.oldDestination).hard.hardAccept = true := by
  unfold bankWordHardEpochGenuine at h
  unfold wGenuineAcceptance at h
  split at h
  · rename_i hguard
    exact hguard
  · simp at h

/-- At a genuinely selected hard S6, the receipt's owner flags
are the ones used by phiW and leasePair. -/
theorem bankWordHardEpochSelectedGenuineOwnerFlags {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (h : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    e = root ∧
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S6" ∧
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
        true := by
  exact bankWordHardEpochGenuineOwnerFlags ring root
    (bankWordEpochSelectedReceipt ring z e)
    (bankWordHardEpochLedger ring root z) h

/-- On the same selected genuine event, both the observed epoch
counters and the physical root lease reset. This does not
assume anything about inherited S6s before the first ticket. -/
theorem bankWordHardEpochSelectedGenuineResetAndLease {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (h : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).hardEpochs =
        (bankWordHardEpochLedger ring root z).hardEpochs + 1 ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).softStarts = 0 ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).softFinishes = 0 ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).pendingSoft = false ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).workerDone = false ∧
    ((bankWordEpochNext ring root z e).2.1 root).siLease.val =
      (compileAdvice (ceilLogTwo n)).siLeaseMax := by
  have hreset := bankWordHardEpochGenuineReset
    ring root (bankWordEpochSelectedReceipt ring z e)
    (bankWordHardEpochLedger ring root z) h
  have hflags := bankWordHardEpochSelectedGenuineOwnerFlags
    ring root z e h
  have hlease := bankWordEpochSelectedHardReload
    ring root z e hflags.1 hflags.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, hlease⟩
  · rw [bankWordHardEpochLedgerNext]
    exact hreset.1
  · rw [bankWordHardEpochLedgerNext]
    exact hreset.2.1
  · rw [bankWordHardEpochLedgerNext]
    exact hreset.2.2.1
  · rw [bankWordHardEpochLedgerNext]
    exact hreset.2.2.2.1
  · rw [bankWordHardEpochLedgerNext]
    exact hreset.2.2.2.2

/-- The invariant is vacuous at the genuine-history-free
entrance, including an arbitrary physical serializer and SI. -/
theorem bankWordHardEpochInitialClean {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :
    BankWordHardEpochCleanInvariant ring root
      (bankWordEpochStart s) := by
  intro h
  have hzero :
      (bankWordHardEpochLedger ring root
        (bankWordEpochStart s)).hardEpochs = 0 := rfl
  rw [hzero] at h
  exact False.elim (Nat.not_lt_zero 0 h.1)

/-- A true root-outgoing requested S1 that is not hard cannot
read a zero lease. This uses the old-row hardS1 guard only. -/
theorem bankWordHardEpochSoftSOneSourcePositive
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hreq : x.ser.cert = .REQUESTED)
    (hsoft : (serW x y).hard.hardS1 = false) :
    0 < x.siLease.val := by
  by_cases hz : x.siLease.val = 0
  · have hguard :
        ((postW x y).eX.l &&
          (x.ser.cert == .REQUESTED) &&
          (x.siLease.val == 0)) = false := by
        exact hsoft
    simp [hx, hreq, hz] at hguard
  · omega

/-- On an unrelated edge, the ORIGINAL phiW projection leaves
the entire root W state unchanged. This fact is independent
of all ghost histories. -/
theorem bankWordHardEpochRootRemoteFrame {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hleft : root ≠ e)
    (hright : root ≠ ring.rightNeighbor e) :
    (bankWordEpochNext ring root z e).2.1 root =
      z.2.1 root := by
  change (phiW ring z.2.1 e) root = z.2.1 root
  exact AcceptedReceipts.WordEntrance.CleanWorker.cwPhiWFrame ring z.2.1 e root hleft hright

/-- In the reducer, a non-accepting and non-hard source with no
soft accept keeps its lease, regardless of responder completion.
Therefore the root as source has no hidden done debit. -/
theorem bankWordHardEpochSourceLeaseQuiet
    (c : Compiled)
    (x y : Fin (c.siLeaseMax + 1))
    (done : Bool) :
    (leasePair c x y false false done).1 = x := by
  cases done <;> rfl

end L3.RenewalReferenceClock


/-!
Restricted BANK-entrance truth test and
first-genuine-hard reset on the exact projected W chain.

The claimed all-word clean-epoch invariant
is NOT asserted without proving the required physical/worker
origin coupling for continuing genuine hard epochs.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The requested n=5 counterexample domain is empty in the
actual BANK branch. At n=5 production compiles SMALL, even
though an n=5 projected-W diagnostic is meaningful. -/
theorem bankWordHardEpochFiveUsesSmall :
    (compileAdvice (ceilLogTwo 5)).useSmall = true := by
  change decide (ceilLogTwo 5 ≤ qStar) = true
  decide

theorem bankWordHardEpochFiveNotBank
    (hbank : (compileAdvice (ceilLogTwo 5)).useSmall = false) :
    False := by
  rw [bankWordHardEpochFiveUsesSmall] at hbank
  cases hbank

/-- In the true BANK branch, q=ceilLogTwo n is at least 80.
This is a property of production compileAdvice, not a
different source-width convention for the proof. -/
theorem bankWordHardEpochBankAdviceLower
    {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    80 ≤ ceilLogTwo n := by
  by_cases hsmall : ceilLogTwo n ≤ qStar
  · have htrue :
        (compileAdvice (ceilLogTwo n)).useSmall = true := by
      change decide (ceilLogTwo n ≤ qStar) = true
      simp [hsmall]
    rw [htrue] at hbank
    cases hbank
  · unfold qStar at hsmall
    omega

/-- BANK excludes both finite-width compiler overrides. The
actual compiled serializer source width equals the width
used in the existing epoch invariant. -/
theorem bankWordHardEpochBankSourceWidth
    {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (compileAdvice (ceilLogTwo n)).t =
      ceilLogTwo (ceilLogTwo n) := by
  have hq : 80 ≤ ceilLogTwo n :=
    bankWordHardEpochBankAdviceLower hbank
  have hspec :
      ceilLogTwo n ≤ 2 ^ ceilLogTwo (ceilLogTwo n) :=
    (ceilLogTwo_spec (ceilLogTwo n)
      (by omega : 2 ≤ ceilLogTwo n)).2
  have hwidth : 7 ≤ ceilLogTwo (ceilLogTwo n) := by
    by_cases hle : ceilLogTwo (ceilLogTwo n) ≤ 6
    · have hp : (2 : Nat) ^ ceilLogTwo (ceilLogTwo n) ≤
          2 ^ 6 :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hle
      have h64 : (2 : Nat) ^ 6 = 64 := by decide
      rw [h64] at hp
      omega
    · omega
  have hnotOne : ¬ ceilLogTwo (ceilLogTwo n) = 1 := by
    omega
  have hnotFinite : ¬ ceilLogTwo n ≤ 32 := by
    omega
  change
    (if sourceTOfQ (ceilLogTwo n) = 1 then 2
     else if ceilLogTwo n ≤ 32 then
       finiteCertWidth (ceilLogTwo n)
     else sourceTOfQ (ceilLogTwo n)) =
      ceilLogTwo (ceilLogTwo n)
  simp [sourceTOfQ, hnotOne, hnotFinite]

/-- The lease equality requested by BankWordHardEpochCleanInvariant
is correct on the actual spatial BANK band. It would not hold
uniformly for every finite SMALL compilation. -/
theorem bankWordHardEpochBankLeaseMaximum
    {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (compileAdvice (ceilLogTwo n)).siLeaseMax =
      8 * ceilLogTwo (ceilLogTwo n) + 4 := by
  change 8 * (compileAdvice (ceilLogTwo n)).t + 4 =
    8 * ceilLogTwo (ceilLogTwo n) + 4
  rw [bankWordHardEpochBankSourceWidth hbank]

/-- A literal hardAccept guard has the actual S6 endpoint
effect, regardless of other projected-W fields: the initiator
root becomes IDLE/CURRENT. This is a local serializer row
fact, not a claimed global origin invariant. -/
theorem bankWordHardEpochHardAcceptLocalIdle
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hhard : (serW x y).hard.hardAccept = true) :
    (serW x y).x.cert = .IDLE ∧
      (serW x y).x.wphase = .CURRENT := by
  have hflags :
      (((((postW x y).eX.l &&
          (x.ser.cert == .RUNNING)) &&
          (x.ser.wphase == .VALIDATING)) &&
          (x.ser.phase == .B)) &&
          (x.ser.out == .DONE) &&
          (y.ser.phase == .F)) = true := by
    exact hhard
  simp only [Bool.and_eq_true] at hflags
  obtain ⟨⟨⟨⟨⟨_, hcertFlag⟩, hphaseFlag⟩,
      hshapeFlag⟩, houtFlag⟩, htailFlag⟩ := hflags
  have hcert : x.ser.cert = .RUNNING := by
    cases hc : x.ser.cert <;> simp [hc] at hcertFlag ⊢
  have hvalid : x.ser.wphase = .VALIDATING := by
    cases hw : x.ser.wphase <;> simp [hw] at hphaseFlag ⊢
  have hphase : x.ser.phase = .B := by
    cases hp : x.ser.phase <;> simp [hp] at hshapeFlag ⊢
  have hout : x.ser.out = .DONE := by
    cases ho : x.ser.out <;> simp [ho] at houtFlag ⊢
  have htail : y.ser.phase = .F := by
    cases hf : y.ser.phase <;> simp [hf] at htailFlag ⊢
  constructor <;>
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hcert, hvalid, hphase, hout, htail]

/-- The genuine ticket receipt in a represented fixed-root BANK
execution has an actual IDLE root in the physical successor.
This uses the existing all-word singleton/root-class closure,
not a fabricated source of physical leader information. -/
theorem bankWordHardEpochSelectedGenuineRootIdle
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
      .IDLE := by
  obtain ⟨he, _, hhard⟩ :=
    bankWordHardEpochSelectedGenuineOwnerFlags
      ring root z e hgen
  subst e
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hlocal := bankWordHardEpochHardAcceptLocalIdle
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hhard
  change ((phiW ring z.2.1 root) root).ser.cert = .IDLE
  rw [phiW_ser_source]
  exact hlocal.1

/-- Immediate post-genuine-hard base case of the desired clean
invariant, now with the actual BANK cap equality and root S6
certificate. This theorem is about the ORIGINAL bankWordEpochNext
successor, not a separately manufactured epoch state. -/
theorem bankWordHardEpochGenuineEstablishesClean
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    BankWordHardEpochCleanInvariant ring root
      (bankWordEpochNext ring root z e) := by
  have hreset := bankWordHardEpochSelectedGenuineResetAndLease
    ring root z e hgen
  obtain ⟨_, hstart, hfinish, hpending, _, hlease⟩ := hreset
  have hidle := bankWordHardEpochSelectedGenuineRootIdle
    ring hn hbank root s hs z hz e hgen
  have hcap := bankWordHardEpochBankLeaseMaximum hbank
  unfold BankWordHardEpochCleanInvariant
  dsimp
  intro _
  constructor
  · rw [hfinish, hstart]
    exact Nat.le_refl 0
  constructor
  · rw [hstart]
    omega
  constructor
  · rw [hstart, hfinish, hpending]
    rfl
  constructor
  · rw [hfinish, hlease, hcap]
    omega
  · intro hr
    rw [hidle] at hr
    cases hr.1

end L3.RenewalReferenceClock

/-!
The joined validation ticket at a selected genuine root
acceptance, EWord's genuine-history scrub, and worker I0 provenance.

This section makes two logically distinct facts
explicit: a joined done/returned ticket is a timestamped local
receipt, whereas EWord.WValidationHistory is a complete suffix of
real, nonaccepting transitions from its actual hard S1.

No lemma here silently identifies those two representations.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A genuine joined receipt contains an actually recorded pair
of tickets with equal request/start stamps. This is the exact
information supplied by Target.wGenuineAcceptance, and is
weaker than EWord.WValidationHistory. -/
theorem bankWordHardEpochGenuineJoinedStamps
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (r : WEdgeReceipt n (compileAdvice (ceilLogTwo n)))
    (a : BankWordHardEpochLedger n)
    (hgen : bankWordHardEpochGenuine ring root r a = true) :
    ∃ p q : WValidationTicket,
      wTicketAt .done (a.validation r.edge) = some p ∧
      wTicketAt .returned
        (a.validation (ring.rightNeighbor r.edge)) = some q ∧
      p.requestedAt = q.requestedAt ∧
      p.startedAt = q.startedAt := by
  have hflags := bankWordHardEpochGenuineOwnerFlags
    ring root r a hgen
  have hguard :
      r.edge = root ∧
        (serW r.oldSource r.oldDestination).row = "S6" ∧
        (serW r.oldSource r.oldDestination).hard.hardAccept = true :=
    hflags
  have hjoined :
      (wJoinTickets
        (wTicketAt .done (a.validation r.edge))
        (wTicketAt .returned
          (a.validation (ring.rightNeighbor r.edge)))).isSome =
        true := by
    unfold bankWordHardEpochGenuine wGenuineAcceptance at hgen
    simpa only [if_pos hguard] using hgen
  cases hp : wTicketAt .done (a.validation r.edge) with
  | none =>
      simp [wJoinTickets, hp] at hjoined
  | some p =>
      cases hq : wTicketAt .returned
          (a.validation (ring.rightNeighbor r.edge)) with
      | none =>
          simp [wJoinTickets, hp, hq] at hjoined
      | some q =>
          by_cases hsame :
              p.requestedAt = q.requestedAt ∧
                p.startedAt = q.startedAt
          · exact ⟨p, q, rfl, rfl, hsame.1, hsame.2⟩
          · simp [wJoinTickets, hp, hq, hsame] at hjoined

/-- The actual S6 observation clears the initiator's ticket
but preserves the responder's ticket, including a returned
ticket from the completed hard pass. A later fresh hard S1
must overwrite that responder ticket with a new start stamp;
mere persistence at the responder is not a forged acceptance. -/
theorem bankWordHardEpochSsixTicketFrame
    {c : Compiled}
    (stamp : Nat) (x y : ProjW c)
    (gx gy : Option WValidationTicket)
    (hrow : (serW x y).row = "S6") :
    (wValidationPair stamp x y gx gy).1 = none ∧
      (wValidationPair stamp x y gx gy).2 = gy := by
  simp [wValidationPair, hrow]

/-- The literal hard-I0 worker row preserves a previously free
responder SI, even when hardRight is false. This is exactly
the missing accepting-edge frame needed after EWord's
pre-acceptance validation scrub. -/
theorem bankWordHardEpochHardAcceptResponderFree
    {c : Compiled} (x y : ProjW c)
    (ha : (serW x y).hard.hardAccept = true)
    (hy : freeSI y.si = true) :
    freeSI (pairW x y).2.si = true := by
  change freeSI (workerW x y).y = true
  simp [workerW, siStep, ha, freeSI, offSI, hy]
  have hy' : y.si.kind = SIKind.OFF ∧ y.si.cur = SICur.NONE := by
    simpa [freeSI] using hy
  split
  · exact ⟨rfl, rfl⟩
  · exact hy'

/-- Convert EWord's rotated indices to arbitrary physical
nonroot indices. The cited EWord result has ALREADY proved
the genuine hard-S1 to pre-acceptance validation transport. -/
theorem bankWordHardEpochHistoryPreacceptFree
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : L3.EWord.ValidationGhost)
    (history : L3.EWord.WValidationHistory ring root s g)
    (ha : (serW (s root)
      (s (ring.rightNeighbor root))).hard.hardAccept = true) :
    ∀ i : Fin n, i ≠ root → freeSI (s i).si = true := by
  intro i hi
  have hpos : 0 < PPL.cyclicOffset ring root i := by
    by_cases hz : PPL.cyclicOffset ring root i = 0
    · have heq := L3.EWord.validationOffsetRepresentative
        ring root i
      rw [hz, L3.EWord.siteZero ring root] at heq
      exact False.elim (hi heq.symm)
    · omega
  have hpre := L3.EWord.validationReachableHardAcceptClean
    ring root history ha
    (⟨PPL.cyclicOffset ring root i,
      L3.EWord.validationOffsetBound ring root i⟩ : Fin n)
    hpos
  change freeSI
      (s (L3.EWord.site ring root
        (PPL.cyclicOffset ring root i))).si = true at hpre
  rw [L3.EWord.validationOffsetRepresentative ring root i] at hpre
  exact hpre

/-- The post-I0 projected W state has all nonroot SI free.
This is a genuine consequence of an EWord.WValidationHistory:
the unique accepting pair either frames or scrubs its responder;
all other nonroots frame. No foreign SI survivor is assumed
away, and the root itself is allowed to launch PREFIX. -/
theorem bankWordHardEpochHistoryPostacceptFree
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : L3.EWord.ValidationGhost)
    (history : L3.EWord.WValidationHistory ring root s g)
    (ha : (serW (s root)
      (s (ring.rightNeighbor root))).hard.hardAccept = true) :
    ∀ i : Fin n, i ≠ root →
      freeSI ((phiW ring s root) i).si = true := by
  have hwidth :
      2 ≤ n := by
    have hw := (L3.EWord.validationReachableShape
      ring root history).width
    omega
  intro i hi
  have hpre := bankWordHardEpochHistoryPreacceptFree
    ring root s g history ha i hi
  by_cases hj : i = ring.rightNeighbor root
  · subst i
    rw [L3.EWord.phiResponder ring s root
      (L3.EWord.rightNeighborDifferent ring hwidth root)]
    exact bankWordHardEpochHardAcceptResponderFree
      (s root) (s (ring.rightNeighbor root)) ha hpre
  · rw [L3.EWord.remoteFrame ring s root i hi hj]
    exact hpre

/-- The accepting edge itself launches the literal canonical
root prefix. This source fact needs only hardAccept, while
the foreign-worker scrub additionally needs EWord history. -/
theorem bankWordHardEpochHardAcceptRootLaunch
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (ha : (serW (s root)
      (s (ring.rightNeighbor root))).hard.hardAccept = true) :
    ((phiW ring s root) root).si = launchPrefix c.t := by
  rw [L3.EWord.phiSource]
  change (workerW (s root)
    (s (ring.rightNeighbor root))).x = launchPrefix c.t
  simp [workerW, siStep, ha]

/-- The actual selected post-state cleanup, conditioned on the
very history whose construction from joined tickets is the
first outstanding source-level implication. -/
theorem bankWordHardEpochSelectedHistoryClean
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (g : L3.EWord.ValidationGhost)
    (history : L3.EWord.WValidationHistory ring root z.2.1 g)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    ∀ i : Fin n, i ≠ root →
      freeSI ((bankWordEpochNext ring root z e).2.1 i).si =
        true := by
  have hflags := bankWordHardEpochSelectedGenuineOwnerFlags
    ring root z e hgen
  obtain ⟨he, _, ha⟩ := hflags
  subst e
  change ∀ i : Fin n, i ≠ root →
    freeSI ((phiW ring z.2.1 root) i).si = true
  exact bankWordHardEpochHistoryPostacceptFree
    ring root z.2.1 g history ha

/-- An actual hardAccept selects SI I0. This is independent
of the provenance ticket; the ticket determines whether the
observer regards the ensuing physical launch as genuine. -/
theorem bankWordHardEpochHardAcceptIzeroRow
    {c : Compiled} (x y : ProjW c)
    (ha : (serW x y).hard.hardAccept = true) :
    (workerW x y).row = "I0" := by
  simp [workerW, siStep, ha]

/-- With a joined accepting ticket, Target.wWorkerReceiptStep
creates the expected worker provenance in its prefixRun phase.
This is the launch-direction correspondence (not the still-open
converse physical SI done => witnessed worker completion). -/
theorem bankWordHardEpochJoinedWorkerLaunch
    {n : Nat} {c : Compiled}
    (root e j : Fin n) (clock : Nat)
    (x y : ProjW c)
    (old : Option (WWorkerTrail n))
    (ticket : WValidationTicket)
    (ha : (serW x y).hard.hardAccept = true) :
    (wWorkerReceiptStep root e j clock x y (some ticket) old).1.isSome =
      true := by
  have hi := bankWordHardEpochHardAcceptIzeroRow x y ha
  simp [wWorkerReceiptStep, hi]

end L3.RenewalReferenceClock

/-!
Ticket-stamp/history bridge, source-scope decomposition.

A physical hard S1 is not automatically
TICKETED: wValidationPair requires an old .requested ticket.
Consequently the proof below distinguishes hard S1 histories
from the smaller class of ticketed histories.

The missing global implication is that a joined terminal ticket
necessarily identifies the most recent actual hard S1 and its
entire intervening nonaccepting physical word. The finite-word
EWord transport and timestamp non-join rows are proved here;
the global backward origin implication is not asserted.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A causal EWord validation shape, together with the exact
two physical properties required of a current-stamp ticket:
.done denotes a genuinely completed validating parent and
.returned denotes an F responder. Older stamps are excluded
from this implication. The proof-only EWord ghost has no
per-site tickets, so this is a relation, not an equality
between incompatible ghost records. -/
def BankWordEpochTicketHistory
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (startedAt : Nat) : Prop :=
  ∃ g : L3.EWord.ValidationGhost,
    L3.EWord.WValidationHistory ring root z.2.1 g ∧
    ∀ i : Fin n, ∀ ticket : WValidationTicket,
      (bankWordHardEpochLedger ring root z).validation i =
        some ticket →
      ticket.startedAt = startedAt →
      (ticket.stage = .done →
        L3.EWord.doneParent ring root z.2.1
          (PPL.cyclicOffset ring root i)) ∧
      (ticket.stage = .returned →
        (z.2.1 i).ser.phase = .F)

/-- An old-stamp ticket cannot be joined to a ticket from a
new hard start: Target.wJoinTickets tests the two start
timestamps (and also the request timestamp) literally. -/
theorem bankWordTicketDifferentStartCannotJoin
    (p q : WValidationTicket)
    (hdifferent : p.startedAt ≠ q.startedAt) :
    wJoinTickets (some p) (some q) = none := by
  have hno :
      ¬ (p.requestedAt = q.requestedAt ∧
        p.startedAt = q.startedAt) := by
    intro h
    exact hdifferent h.2
  simp [wJoinTickets, hno]

/-- A different request timestamp likewise blocks the join,
even if the start timestamps happen to agree. -/
theorem bankWordTicketDifferentRequestCannotJoin
    (p q : WValidationTicket)
    (hdifferent : p.requestedAt ≠ q.requestedAt) :
    wJoinTickets (some p) (some q) = none := by
  have hno :
      ¬ (p.requestedAt = q.requestedAt ∧
        p.startedAt = q.startedAt) := by
    intro h
    exact hdifferent h.1
  simp [wJoinTickets, hno]

/-- A physical hard S1 without an old .requested ticket DOES
NOT create a validation stamp in Target.wValidationPair.
This is the inherited-REQUESTED boundary case that prevents
the unqualified claim "every hard S1 starts both ghosts." -/
theorem bankWordTicketlessHardStart
    {c : Compiled} (stamp : Nat)
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hreq : x.ser.cert = .REQUESTED)
    (hzero : x.siLease.val = 0) :
    (serW x y).hard.hardS1 = true ∧
      wValidationPair stamp x y none none = (none, none) := by
  have hflags := L3.EWord.freshStartFlags
    x y hx hy hreq hzero
  constructor
  · exact hflags.2.1
  · simp [wValidationPair, hflags.1, wTicketAt]

/-- A genuinely ticketed hard S1 writes one waiting ticket at
the root and one pending ticket at its first follower, both
with the selected service clock, regardless of old follower
scratch. The witness has the actual old requestedAt field. -/
theorem bankWordTicketedHardStartWrites
    {c : Compiled}
    (stamp : Nat) (x y : ProjW c)
    (gx gy : Option WValidationTicket)
    (request : WValidationTicket)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hreq : x.ser.cert = .REQUESTED)
    (hzero : x.siLease.val = 0)
    (hrequest : wTicketAt .requested gx = some request) :
    wValidationPair stamp x y gx gy =
      (some { requestedAt := request.requestedAt
              startedAt := stamp
              stage := .waiting },
       some { requestedAt := request.requestedAt
              startedAt := stamp
              stage := .pending }) := by
  have hflags := L3.EWord.freshStartFlags
    x y hx hy hreq hzero
  simp [wValidationPair, hflags.1, hrequest, hzero]

/-- Actual represented BANK closure supplies WFixedRoot on
the successor of the selected hard S1. EWord.start then
constructs a complete physical history, independent of
whether that S1 had an origin-observer requested ticket. -/
theorem bankWordTicketPhysicalHardStartHistory
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0) :
    L3.EWord.WValidationHistory ring root
      (bankWordEpochNext ring root z root).2.1
      L3.EWord.freshGhost := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed :
      WFixedRoot ring root (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  change L3.EWord.WValidationHistory ring root
    (phiW ring z.2.1 root) L3.EWord.freshGhost
  exact L3.EWord.WValidationHistory.start z.2.1
    (by omega : 3 ≤ n) hpost.1 hpost.2 hreq hzero
    hfixed

/-- Combining the two independent conditions at one actual
ticketed hard S1: EWord's physical history begins AND the
Target observer records its fresh timestamp. -/
theorem bankWordTicketedHardStartJoint
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (request : WValidationTicket)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0)
    (hrequest :
      wTicketAt .requested
        ((bankWordHardEpochLedger ring root z).validation root) =
        some request) :
    L3.EWord.WValidationHistory ring root
      (bankWordEpochNext ring root z root).2.1
      L3.EWord.freshGhost ∧
    wValidationPair (z.2.2.clock + 1)
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
      ((bankWordHardEpochLedger ring root z).validation root)
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor root)) =
        (some { requestedAt := request.requestedAt
                startedAt := z.2.2.clock + 1
                stage := .waiting },
         some { requestedAt := request.requestedAt
                startedAt := z.2.2.clock + 1
                stage := .pending }) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed :
      WFixedRoot ring root (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  constructor
  · exact bankWordTicketPhysicalHardStartHistory
      ring hn hbank root s hs z hz hreq hzero
  · exact bankWordTicketedHardStartWrites
      (z.2.2.clock + 1)
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
      ((bankWordHardEpochLedger ring root z).validation root)
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor root))
      request hpost.1 hpost.2 hreq hzero hrequest

/-- The actual old-row predicate that every intervening
service is nonaccepting. It is read from the exact chosen
physical edge; no new or frozen transition is substituted. -/
def bankWordTicketNoHardAcceptWord
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) :
    List (Fin n) → Prop
  | [] => True
  | e :: rest =>
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
        false ∧
      bankWordTicketNoHardAcceptWord ring root
        (bankWordEpochNext ring root z e) rest

/-- EWord.next applies on each nonaccepting actual edge.
The fixed-root premise is supplied by the same represented
BANK class used by the projected one-epoch cost theorem. -/
theorem bankWordTicketPhysicalHistoryNext
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (g : L3.EWord.ValidationGhost)
    (history : L3.EWord.WValidationHistory ring root z.2.1 g)
    (e : Fin n)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
        false) :
    L3.EWord.WValidationHistory ring root
      (bankWordEpochNext ring root z e).2.1
      (L3.EWord.validationGhostStep ring root z.2.1 g e) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed :
      WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass e).2
  change (serW (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e))).hard.hardAccept = false
    at hno
  change L3.EWord.WValidationHistory ring root
    (phiW ring z.2.1 e)
    (L3.EWord.validationGhostStep ring root z.2.1 g e)
  exact L3.EWord.WValidationHistory.next history e hno
    hfixed

/-- A genuine finite-word induction: EWord's full physical
validation history survives every actual nonaccepting edge
in a represented BANK run. The proof does not assume anything
about the (possibly older) Target ticket values. -/
theorem bankWordTicketPhysicalHistoryRun
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (word : List (Fin n)) :
    ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      ∀ g : L3.EWord.ValidationGhost,
        L3.EWord.WValidationHistory ring root z.2.1 g →
        bankWordTicketNoHardAcceptWord ring root z word →
        ∃ g' : L3.EWord.ValidationGhost,
          L3.EWord.WValidationHistory ring root
            (bankWordEpochRun ring root z word).2.1 g' := by
  induction word with
  | nil =>
      intro z hz g history hno
      exact ⟨g, history⟩
  | cons e rest ih =>
      intro z hz g history hno
      have hfirst :
          (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
            false := hno.1
      have hstep := bankWordTicketPhysicalHistoryNext
        ring hn hbank root s hs z hz g history e hfirst
      have hreach := bankWordEpochReachableNext
        ring root s z hz e
      exact ih (bankWordEpochNext ring root z e) hreach
        (L3.EWord.validationGhostStep ring root z.2.1 g e)
        hstep hno.2

/-- A real zero-lease hard start followed by a finite
nonaccepting word therefore has the complete EWord history
immediately before its first physical accepting edge. -/
theorem bankWordTicketHardStartThroughWord
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0)
    (word : List (Fin n))
    (hno : bankWordTicketNoHardAcceptWord ring root
      (bankWordEpochNext ring root z root) word) :
    ∃ g : L3.EWord.ValidationGhost,
      L3.EWord.WValidationHistory ring root
        (bankWordEpochRun ring root
          (bankWordEpochNext ring root z root) word).2.1 g := by
  have hstart := bankWordTicketPhysicalHardStartHistory
    ring hn hbank root s hs z hz hreq hzero
  have hreach := bankWordEpochReachableNext
    ring root s z hz root
  exact bankWordTicketPhysicalHistoryRun
    ring hn hbank root s hs word
    (bankWordEpochNext ring root z root) hreach
    L3.EWord.freshGhost hstart hno

/-- Hence the entire hard-S1/word/S6 segment has the exact
post-I0 nonroot scrub certificate, using EWord's already
validating traversal and the literal accepting edge.
There is NO new named premise: hno is a finite physical
receipt test on the displayed word. -/
theorem bankWordTicketHardStartThroughAcceptClean
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0)
    (word : List (Fin n))
    (hno : bankWordTicketNoHardAcceptWord ring root
      (bankWordEpochNext ring root z root) word)
    (e : Fin n)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring
        (bankWordEpochRun ring root
          (bankWordEpochNext ring root z root) word) e)
      (bankWordHardEpochLedger ring root
        (bankWordEpochRun ring root
          (bankWordEpochNext ring root z root) word)) = true) :
    ∀ i : Fin n, i ≠ root →
      freeSI
        ((bankWordEpochNext ring root
          (bankWordEpochRun ring root
            (bankWordEpochNext ring root z root) word) e).2.1 i).si =
        true := by
  obtain ⟨g, history⟩ :=
    bankWordTicketHardStartThroughWord
      ring hn hbank root s hs z hz hreq hzero word hno
  exact bankWordHardEpochSelectedHistoryClean
    ring root
    (bankWordEpochRun ring root
      (bankWordEpochNext ring root z root) word)
    e g history hgen

/-- A genuine accepting ticket together with a verified
TicketHistory relation yields the requested postacceptance
cleanup. The still-unproved direction is that the joined
ticket creates this relation on EVERY represented run. -/
theorem bankWordTicketHistoryGenuineClean
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (stamp : Nat)
    (hhistory : BankWordEpochTicketHistory ring root z stamp)
    (e : Fin n)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    ∀ i : Fin n, i ≠ root →
      freeSI ((bankWordEpochNext ring root z e).2.1 i).si =
        true := by
  obtain ⟨g, history, _⟩ := hhistory
  exact bankWordHardEpochSelectedHistoryClean
    ring root z e g history hgen

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The real projected epoch runner respects word concatenation. -/
theorem bankWordRootRunAppend {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (left right : List (Fin n)) :
    bankWordEpochRun ring root z (left ++ right) =
      bankWordEpochRun ring root
        (bankWordEpochRun ring root z left) right := by
  induction left generalizing z with
  | nil =>
      rfl
  | cons e tail ih =>
      change
        bankWordEpochRun ring root
          (bankWordEpochNext ring root z e) (tail ++ right) =
        bankWordEpochRun ring root
          (bankWordEpochRun ring root
            (bankWordEpochNext ring root z e) tail) right
      exact ih (bankWordEpochNext ring root z e)

/-- A genuinely nonaccepting last edge extends the finite
    physical no-hard-accept certificate. -/
theorem bankWordRootNoAcceptSnoc {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (word : List (Fin n)) (e : Fin n) :
    bankWordTicketNoHardAcceptWord ring root z word →
    (bankWordEpochSelectedReceipt ring
      (bankWordEpochRun ring root z word) e).serializer.hard.hardAccept =
        false →
    bankWordTicketNoHardAcceptWord ring root z (word ++ [e]) := by
  induction word generalizing z with
  | nil =>
      intro _ hlast
      exact ⟨hlast, True.intro⟩
  | cons f tail ih =>
      intro hno hlast
      change
        (bankWordEpochSelectedReceipt ring z f).serializer.hard.hardAccept =
          false ∧
        bankWordTicketNoHardAcceptWord ring root
          (bankWordEpochNext ring root z f) tail at hno
      change
        (bankWordEpochSelectedReceipt ring z f).serializer.hard.hardAccept =
          false ∧
        bankWordTicketNoHardAcceptWord ring root
          (bankWordEpochNext ring root z f) (tail ++ [e])
      exact ⟨hno.1,
        ih (bankWordEpochNext ring root z f) hno.2 hlast⟩

/-- A selected edge incident to neither endpoint at root cannot
    alter the root's observed validation ticket. -/
theorem bankWordRootTicketRemoteFrame {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (he : root ≠ e)
    (hj : root ≠ ring.rightNeighbor e) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation root =
    (bankWordHardEpochLedger ring root z).validation root := by
  rw [bankWordHardEpochLedgerNext]
  simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt, he, hj]

/-- At an actual S6 owned by root, the root-side ticket is
    erased, even though the responder's ticket may survive. -/
theorem bankWordRootTicketClearedAtSsix {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hrow : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).row = "S6") :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation root =
        none := by
  rw [bankWordHardEpochLedgerNext]
  simp only [bankWordHardEpochStep, bankWordEpochSelectedReceipt]
  rw [if_pos trivial]
  exact (bankWordHardEpochSsixTicketFrame
    (z.2.2.clock + 1)
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    ((bankWordHardEpochLedger ring root z).validation root)
    ((bankWordHardEpochLedger ring root z).validation
      (ring.rightNeighbor root)) hrow).1

/-- A ticketed zero-lease root S1 writes the fresh root waiting
    stamp on the actual ledger successor and is physically hard. -/
theorem bankWordRootTicketedHardStartObserved {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (request : WValidationTicket)
    (hx : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eY.l = false)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0)
    (hrequest : wTicketAt .requested
      ((bankWordHardEpochLedger ring root z).validation root) =
        some request) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation root =
      some { requestedAt := request.requestedAt
             startedAt := z.2.2.clock + 1
             stage := .waiting } ∧
    (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardS1 =
      true := by
  constructor
  · rw [bankWordHardEpochLedgerNext]
    simp only [bankWordHardEpochStep, bankWordEpochSelectedReceipt]
    rw [if_pos trivial]
    rw [bankWordTicketedHardStartWrites
      (z.2.2.clock + 1)
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
      ((bankWordHardEpochLedger ring root z).validation root)
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor root))
      request hx hy hreq hzero hrequest]
  · change
      (serW (z.2.1 root)
        (z.2.1 (ring.rightNeighbor root))).hard.hardS1 = true
    exact (bankWordHardEpochZeroLeaseHardStart
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
      hx hy hreq hzero).2.1

/-- Backward source certificate for one ticket. In particular,
    'mid' is an actual nonaccepting suffix of the represented
    word, not a word reconstructed from ticket timestamps. -/
def BankWordRootTicketOrigin {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (ticket : WValidationTicket) : Prop :=
  ∃ pre mid : List (Fin n),
    ∃ request : WValidationTicket,
      z = bankWordEpochRun ring root (bankWordEpochStart s)
        (pre ++ [root] ++ mid) ∧
      ((bankWordEpochRun ring root
        (bankWordEpochStart s) pre).2.1 root).ser.cert = .REQUESTED ∧
      ((bankWordEpochRun ring root
        (bankWordEpochStart s) pre).2.1 root).siLease.val = 0 ∧
      wTicketAt .requested
        ((bankWordHardEpochLedger ring root
          (bankWordEpochRun ring root
            (bankWordEpochStart s) pre)).validation root) =
        some request ∧
      request.requestedAt = ticket.requestedAt ∧
      (bankWordEpochRun ring root
        (bankWordEpochStart s) pre).2.2.clock + 1 =
        ticket.startedAt ∧
      (bankWordEpochSelectedReceipt ring
        (bankWordEpochRun ring root
          (bankWordEpochStart s) pre) root).serializer.hard.hardS1 =
        true ∧
      bankWordTicketNoHardAcceptWord ring root
        (bankWordEpochNext ring root
          (bankWordEpochRun ring root
            (bankWordEpochStart s) pre) root) mid

/-- The missing all-reachable source claim has this precise
    root-side form: only the .done ticket used at acceptance
    needs a backward root hard-S1 origin. -/
def BankWordRootDoneOrigin {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n) : Prop :=
  ∀ ticket : WValidationTicket,
    wTicketAt .done
      ((bankWordHardEpochLedger ring root z).validation root) =
        some ticket →
    BankWordRootTicketOrigin ring root s z ticket

/-- At a represented ticketed hard S1, its newly created
    waiting ticket really does have a root-origin certificate. -/
theorem bankWordRootTicketOriginAtHardStart {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (request : WValidationTicket)
    (hx : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eY.l = false)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0)
    (hrequest : wTicketAt .requested
      ((bankWordHardEpochLedger ring root z).validation root) =
        some request) :
    BankWordRootTicketOrigin ring root s
      (bankWordEpochNext ring root z root)
      { requestedAt := request.requestedAt
        startedAt := z.2.2.clock + 1
        stage := .waiting } := by
  obtain ⟨pre, hpre⟩ := hz
  subst z
  refine ⟨pre, [], request, ?_, hreq, hzero,
    hrequest, rfl, rfl, ?_, True.intro⟩
  · simpa only [List.append_nil] using
      (bankWordEpochRunSnoc ring root
        (bankWordEpochStart s) pre root).symm
  · change
      (serW
        ((bankWordEpochRun ring root
          (bankWordEpochStart s) pre).2.1 root)
        ((bankWordEpochRun ring root
          (bankWordEpochStart s) pre).2.1
            (ring.rightNeighbor root))).hard.hardS1 = true
    exact (bankWordHardEpochZeroLeaseHardStart
      ((bankWordEpochRun ring root
        (bankWordEpochStart s) pre).2.1 root)
      ((bankWordEpochRun ring root
        (bankWordEpochStart s) pre).2.1
          (ring.rightNeighbor root))
      hx hy hreq hzero).2.1

/-- Any truly nonaccepting edge extends an existing witness
    to its new state; the statement does not assert that the
    current root-side ticket still has this stamp. -/
theorem bankWordRootTicketOriginNonacceptNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (ticket : WValidationTicket) (e : Fin n)
    (horigin : BankWordRootTicketOrigin ring root s z ticket)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
      false) :
    BankWordRootTicketOrigin ring root s
      (bankWordEpochNext ring root z e) ticket := by
  obtain ⟨pre, mid, request, hz, hreq, hzero,
    hrequested, hrequestStamp, hstartStamp, hhard, hmid⟩ := horigin
  refine ⟨pre, mid ++ [e], request, ?_, hreq, hzero,
    hrequested, hrequestStamp, hstartStamp, hhard, ?_⟩
  · rw [hz]
    have happ :
        pre ++ [root] ++ (mid ++ [e]) =
          (pre ++ [root] ++ mid) ++ [e] := by
      simp only [List.append_assoc]
    rw [happ]
    exact (bankWordEpochRunSnoc ring root
      (bankWordEpochStart s)
      (pre ++ [root] ++ mid) e).symm
  · have hreal :
        bankWordEpochRun ring root
          (bankWordEpochNext ring root
            (bankWordEpochRun ring root
              (bankWordEpochStart s) pre) root) mid = z := by
      rw [hz, bankWordRootRunAppend, bankWordEpochRunSnoc]
    have hlast :
        (bankWordEpochSelectedReceipt ring
          (bankWordEpochRun ring root
            (bankWordEpochNext ring root
              (bankWordEpochRun ring root
                (bankWordEpochStart s) pre) root) mid)
          e).serializer.hard.hardAccept = false := by
      rw [hreal]
      exact hno
    exact bankWordRootNoAcceptSnoc ring root
      (bankWordEpochNext ring root
        (bankWordEpochRun ring root
          (bankWordEpochStart s) pre) root)
      mid e hmid hlast

/-- The .done-origin implication transports through any
    nonaccepting edge disjoint from the root. -/
theorem bankWordRootDoneOriginRemoteNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n) (e : Fin n)
    (hinv : BankWordRootDoneOrigin ring root s z)
    (he : root ≠ e)
    (hj : root ≠ ring.rightNeighbor e)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
      false) :
    BankWordRootDoneOrigin ring root s
      (bankWordEpochNext ring root z e) := by
  intro ticket ht
  have hframe := bankWordRootTicketRemoteFrame
    ring root z e he hj
  rw [hframe] at ht
  exact bankWordRootTicketOriginNonacceptNext
    ring root s z ticket e (hinv ticket ht) hno

/-- Any root S6 makes the .done-origin implication vacuous,
    independently of whether that S6 is genuine. -/
theorem bankWordRootDoneOriginSsixNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hrow : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).row = "S6") :
    BankWordRootDoneOrigin ring root s
      (bankWordEpochNext ring root z root) := by
  intro ticket ht
  have hclear := bankWordRootTicketClearedAtSsix ring root z hrow
  rw [hclear] at ht
  simp [wTicketAt] at ht

/-- Fresh ticketed hard S1 writes waiting, not done; hence
    this particular root-side .done obligation is empty. -/
theorem bankWordRootDoneOriginTicketedStartNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (request : WValidationTicket)
    (hx : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eY.l = false)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0)
    (hrequest : wTicketAt .requested
      ((bankWordHardEpochLedger ring root z).validation root) =
        some request) :
    BankWordRootDoneOrigin ring root s
      (bankWordEpochNext ring root z root) := by
  have hwrite := (bankWordRootTicketedHardStartObserved
    ring root z request hx hy hreq hzero hrequest).1
  intro ticket ht
  rw [hwrite] at ht
  simp [wTicketAt] at ht

/-- Once the literal root origin decomposition has been proved,
    the installed EWord bridge gives post-acceptance nonroot SI
    cleanup on the original projected physical successor. -/
theorem bankWordRootTicketOriginGenuineClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (ticket : WValidationTicket)
    (horigin : BankWordRootTicketOrigin ring root s z ticket)
    (e : Fin n)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    ∀ i : Fin n, i ≠ root →
      freeSI ((bankWordEpochNext ring root z e).2.1 i).si =
        true := by
  obtain ⟨pre, mid, request, hz, hreq, hzero,
    hrequested, hrequestStamp, hstartStamp, hhard, hmid⟩ := horigin
  have hprefix : BankWordEpochReachable ring root s
      (bankWordEpochRun ring root
        (bankWordEpochStart s) pre) :=
    ⟨pre, rfl⟩
  have hdecomp :
      bankWordEpochRun ring root (bankWordEpochStart s)
        (pre ++ [root] ++ mid) =
      bankWordEpochRun ring root
        (bankWordEpochNext ring root
          (bankWordEpochRun ring root
            (bankWordEpochStart s) pre) root) mid := by
    rw [bankWordRootRunAppend, bankWordEpochRunSnoc]
  rw [hz, hdecomp] at hgen ⊢
  exact bankWordTicketHardStartThroughAcceptClean
    ring hn hbank root s hs
    (bankWordEpochRun ring root
      (bankWordEpochStart s) pre)
    hprefix hreq hzero mid hmid e hgen

/-- The joined-stamps theorem now supplies the exact ticket to
    which the root .done-origin relation must be applied. The
    still-missing premise is *only* the global production of
    BankWordRootDoneOrigin on represented reachable runs. -/
theorem bankWordRootDoneOriginGenuineClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hinv : BankWordRootDoneOrigin ring root s z)
    (e : Fin n)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    ∀ i : Fin n, i ≠ root →
      freeSI ((bankWordEpochNext ring root z e).2.1 i).si =
        true := by
  obtain ⟨p, q, hp, hq, hrequestStamp, hstartStamp⟩ :=
    bankWordHardEpochGenuineJoinedStamps ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) hgen
  have he := (bankWordHardEpochSelectedGenuineOwnerFlags
    ring root z e hgen).1
  subst e
  exact bankWordRootTicketOriginGenuineClean
    ring hn hbank root s hs z p (hinv p hp) root hgen

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- All root-side non-request tickets have an actual root hard-S1
    source and a nonaccepting suffix. A requested ticket is tracked
    separately as a request, not incorrectly assigned an S1 source.
    This predicate is stronger than BankWordRootDoneOrigin. -/
def BankWordRootTicketOriginAll {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n) : Prop :=
  ∀ ticket : WValidationTicket,
    (bankWordHardEpochLedger ring root z).validation root =
      some ticket →
    ticket.stage = .requested ∨
      BankWordRootTicketOrigin ring root s z ticket

theorem bankWordRootTicketOriginAllInitial {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochStart s) := by
  intro ticket ht
  change (none : Option WValidationTicket) = some ticket at ht
  cases ht

theorem bankWordRootTicketOriginAllDone {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hinv : BankWordRootTicketOriginAll ring root s z) :
    BankWordRootDoneOrigin ring root s z := by
  intro ticket ht
  cases hv :
      (bankWordHardEpochLedger ring root z).validation root with
  | none =>
      simp [wTicketAt, hv] at ht
  | some old =>
      by_cases hs : old.stage = .done
      · have heq : old = ticket := by
          simpa [wTicketAt, hv, hs] using ht
        rcases hinv old hv with hrequest | horigin
        · cases hrequest.symm.trans hs
        · rw [heq] at horigin
          exact horigin
      · simp [wTicketAt, hv, hs] at ht

/-- The physically incoming-root second output has only two
    possibilities. S0 creates a request; S5 keeps the old ticket.
    In particular neither branch manufactures .done or .waiting. -/
theorem bankWordIncomingSecondTicketLocal {c : Compiled}
    (stamp : Nat) (x y : ProjW c)
    (gx gy : Option WValidationTicket)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true) :
    (wValidationPair stamp x y gx gy).2 =
      if y.ser.cert = .IDLE then
        some { requestedAt := stamp, startedAt := stamp,
               stage := .requested }
      else gy := by
  by_cases hc : y.ser.cert = .IDLE
  · have hrow := (serRootIncomingIdle x y hx hy hc).1
    simp [wValidationPair, hrow, hc]
  · have hrow := (serRootIncomingNonidle x y hx hy hc).1
    simp [wValidationPair, hrow, hc]

/-- This equality is for the *selected* chronological receipt,
    not a fabricated second component of an arbitrary pair. -/
theorem bankWordRootIncomingTicketExact {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hj : ring.rightNeighbor e = root) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation root =
      if (z.2.1 root).ser.cert = .IDLE then
        some { requestedAt := z.2.2.clock + 1,
               startedAt := z.2.2.clock + 1,
               stage := .requested }
      else (bankWordHardEpochLedger ring root z).validation root := by
  have he : root ≠ e := by
    intro h
    apply clockNeighborDifferent ring hn e
    calc
      ring.rightNeighbor e = root := hj
      _ = e := h
  have hpost := clockPostIncoming
    ring root z.2.1 e hn hfixed hj
  have hlocal := bankWordIncomingSecondTicketLocal
    (z.2.2.clock + 1)
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    ((bankWordHardEpochLedger ring root z).validation e)
    ((bankWordHardEpochLedger ring root z).validation
      (ring.rightNeighbor e)) hpost.1 hpost.2
  rw [bankWordHardEpochLedgerNext]
  calc
    (bankWordHardEpochStep ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z)).validation root =
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).2 := by
              simp [bankWordHardEpochStep,
                bankWordEpochSelectedReceipt, he, hj]
    _ = if (z.2.1 root).ser.cert = .IDLE then
          some { requestedAt := z.2.2.clock + 1,
                 startedAt := z.2.2.clock + 1,
                 stage := .requested }
        else (bankWordHardEpochLedger ring root z).validation root := by
          simpa only [hj] using hlocal

/-- On a represented fixed-root epoch, every nonroot source
    is nonaccepting. This includes the incoming-root edge. -/
theorem bankWordRootNonrootHardAcceptFalse {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (he : e ≠ root) :
    (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
      false := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass e).2
  have hx := L3.EWord.validationPostSourceNonroot
    ring root z.2.1 e hfixed he
  change (serW (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e))).hard.hardAccept = false
  exact L3.EWord.nonrootNoAccept
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hx

/-- Every remote nonaccepting edge preserves the ALL-stage
    invariant: ticket equality comes from the ledger frame,
    source-history extension from the actual selected receipt. -/
theorem bankWordRootTicketOriginAllRemoteNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n) (e : Fin n)
    (hinv : BankWordRootTicketOriginAll ring root s z)
    (he : root ≠ e)
    (hj : root ≠ ring.rightNeighbor e)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
      false) :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochNext ring root z e) := by
  intro ticket ht
  have hframe := bankWordRootTicketRemoteFrame ring root z e he hj
  rw [hframe] at ht
  rcases hinv ticket ht with hrequest | horigin
  · exact Or.inl hrequest
  · exact Or.inr
      (bankWordRootTicketOriginNonacceptNext
        ring root s z ticket e horigin hno)

/-- The incoming-root S0 branch creates .requested, and S5
    leaves the old root ticket untouched. Both are covered
    without a foreign-stamp exception. -/
theorem bankWordRootTicketOriginAllIncomingNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (hj : ring.rightNeighbor e = root)
    (hinv : BankWordRootTicketOriginAll ring root s z) :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochNext ring root z e) := by
  have he : e ≠ root := by
    intro h
    apply clockNeighborDifferent ring (by omega : 2 ≤ n) e
    calc
      ring.rightNeighbor e = root := hj
      _ = e := h.symm
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass e).2
  have hframe := bankWordRootIncomingTicketExact
    ring root z e (by omega : 2 ≤ n) hfixed hj
  have hno := bankWordRootNonrootHardAcceptFalse
    ring hn hbank root s hs z hz e he
  intro ticket ht
  rw [hframe] at ht
  by_cases hc : (z.2.1 root).ser.cert = .IDLE
  · rw [if_pos hc] at ht
    have heq : ticket =
        { requestedAt := z.2.2.clock + 1,
          startedAt := z.2.2.clock + 1,
          stage := .requested } := (Option.some.inj ht).symm
    left
    rw [heq]
  · rw [if_neg hc] at ht
    rcases hinv ticket ht with hrequest | horigin
    · exact Or.inl hrequest
    · exact Or.inr
        (bankWordRootTicketOriginNonacceptNext
          ring root s z ticket e horigin hno)

/-- The analogous incoming-root preservation of the old .done
    statement, not requiring the stronger all-stage hypothesis. -/
theorem bankWordRootDoneOriginIncomingNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (hj : ring.rightNeighbor e = root)
    (hinv : BankWordRootDoneOrigin ring root s z) :
    BankWordRootDoneOrigin ring root s
      (bankWordEpochNext ring root z e) := by
  have he : e ≠ root := by
    intro h
    apply clockNeighborDifferent ring (by omega : 2 ≤ n) e
    calc
      ring.rightNeighbor e = root := hj
      _ = e := h.symm
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass e).2
  have hframe := bankWordRootIncomingTicketExact
    ring root z e (by omega : 2 ≤ n) hfixed hj
  have hno := bankWordRootNonrootHardAcceptFalse
    ring hn hbank root s hs z hz e he
  intro ticket ht
  rw [hframe] at ht
  by_cases hc : (z.2.1 root).ser.cert = .IDLE
  · rw [if_pos hc] at ht
    simp [wTicketAt] at ht
  · rw [if_neg hc] at ht
    exact bankWordRootTicketOriginNonacceptNext
      ring root s z ticket e (hinv ticket ht) hno

/-- Root S6 erases the full outstanding source obligation. -/
theorem bankWordRootTicketOriginAllSsixNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hrow : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).row = "S6") :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochNext ring root z root) := by
  intro ticket ht
  have hclear := bankWordRootTicketClearedAtSsix ring root z hrow
  rw [hclear] at ht
  cases ht

/-- Fresh ticketed hard S1 establishes the ALL-stage predicate,
    not just the old .done-vacuity lemma. -/
theorem bankWordRootTicketOriginAllTicketedStartNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (request : WValidationTicket)
    (hx : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eY.l = false)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0)
    (hrequest : wTicketAt .requested
      ((bankWordHardEpochLedger ring root z).validation root) =
        some request) :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochNext ring root z root) := by
  have hw := (bankWordRootTicketedHardStartObserved
    ring root z request hx hy hreq hzero hrequest).1
  have horigin := bankWordRootTicketOriginAtHardStart
    ring root s z hz request hx hy hreq hzero hrequest
  intro ticket ht
  rw [hw] at ht
  have heq : ticket =
      { requestedAt := request.requestedAt,
        startedAt := z.2.2.clock + 1,
        stage := .waiting } := (Option.some.inj ht).symm
  subst ticket
  exact Or.inr horigin

/-- A hard accepting root service always has the physical S6
    row; this does not require a genuine ghost acceptance. -/
theorem bankWordRootHardAcceptRowSsix {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hhard : (serW x y).hard.hardAccept = true) :
    (serW x y).row = "S6" := by
  have hflags :
      (((((postW x y).eX.l &&
          (x.ser.cert == .RUNNING)) &&
          (x.ser.wphase == .VALIDATING)) &&
          (x.ser.phase == .B)) &&
          (x.ser.out == .DONE) &&
          (y.ser.phase == .F)) = true := by
    exact hhard
  simp only [Bool.and_eq_true] at hflags
  obtain ⟨⟨⟨⟨⟨_, hcertFlag⟩, _⟩,
      hphaseFlag⟩, houtFlag⟩, htailFlag⟩ := hflags
  have hcert : x.ser.cert = .RUNNING := by
    cases hc : x.ser.cert <;> simp [hc] at hcertFlag ⊢
  have hphase : x.ser.phase = .B := by
    cases hp : x.ser.phase <;> simp [hp] at hphaseFlag ⊢
  have hout : x.ser.out = .DONE := by
    cases ho : x.ser.out <;> simp [ho] at houtFlag ⊢
  have htail : y.ser.phase = .F := by
    cases hf : y.ser.phase <;> simp [hf] at htailFlag ⊢
  have hnotreq : x.ser.cert ≠ .REQUESTED := by
    intro hc
    rw [hcert] at hc
    cases hc
  exact (serRootOutgoingDone x y hx hy hnotreq hphase hout htail).1

theorem bankWordRootTicketOriginAllHardAcceptNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hx : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eY.l = false)
    (hhard : (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
      true) :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochNext ring root z root) := by
  change (serW (z.2.1 root)
    (z.2.1 (ring.rightNeighbor root))).hard.hardAccept = true
    at hhard
  have hrow := bankWordRootHardAcceptRowSsix
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hx hy hhard
  exact bankWordRootTicketOriginAllSsixNext
    ring root s z hrow

/-- A genuine hard-S1 source certificate survives a change of
    ticket stage whenever both chronological stamps are unchanged. -/
theorem bankWordRootTicketOriginRetag {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (old fresh : WValidationTicket)
    (horigin : BankWordRootTicketOrigin ring root s z old)
    (hrequested : old.requestedAt = fresh.requestedAt)
    (hstarted : old.startedAt = fresh.startedAt) :
    BankWordRootTicketOrigin ring root s z fresh := by
  obtain ⟨pre, mid, request, hz, hreq, hzero,
    ht, hrequestedAt, hstartedAt, hhard, hmid⟩ := horigin
  exact ⟨pre, mid, request, hz, hreq, hzero,
    ht, hrequestedAt.trans hrequested,
    hstartedAt.trans hstarted, hhard, hmid⟩

/-- A precise reduction of the global bridge to the remaining
    nonaccepting root-outgoing step. No new axiom is declared:
    the missing closure is an explicit theorem parameter. -/
theorem bankWordRootTicketOriginAllWordOfOutgoing {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hout :
      ∀ z : BankWordEpochState n,
        BankWordEpochReachable ring root s z →
        BankWordRootTicketOriginAll ring root s z →
        (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
          false →
        BankWordRootTicketOriginAll ring root s
          (bankWordEpochNext ring root z root))
    (word : List (Fin n)) :
    ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordRootTicketOriginAll ring root s z →
      BankWordRootTicketOriginAll ring root s
        (bankWordEpochRun ring root z word) := by
  induction word with
  | nil =>
      intro z hz hinv
      exact hinv
  | cons e rest ih =>
      intro z hz hinv
      have hzstep := bankWordEpochReachableNext
        ring root s z hz e
      have hstep : BankWordRootTicketOriginAll ring root s
          (bankWordEpochNext ring root z e) := by
        by_cases he : e = root
        · subst e
          by_cases hhard :
              (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
                true
          · have hclass := bankWordEpochReachablePhysicalRootClass
              ring hn hbank root s hs z hz
            have hfixed : WFixedRoot ring root
                (phiW ring z.2.1 root) :=
              ((bankWordSerializerRootClassClosed
                ring hn hbank root).2 z.2.1 hclass root).2
            have hpost := clockPostOutgoing
              ring root z.2.1 root (by omega : 2 ≤ n) hfixed rfl
            exact bankWordRootTicketOriginAllHardAcceptNext
              ring root s z hpost.1 hpost.2 hhard
          · have hno :
                (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
                  false := by
              cases h :
                (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept
              · rfl
              · exact False.elim (hhard h)
            exact hout z hz hinv hno
        · by_cases hj : ring.rightNeighbor e = root
          · exact bankWordRootTicketOriginAllIncomingNext
              ring hn hbank root s hs z hz e hj hinv
          · have hno := bankWordRootNonrootHardAcceptFalse
              ring hn hbank root s hs z hz e he
            exact bankWordRootTicketOriginAllRemoteNext
              ring root s z e hinv (Ne.symm he) (Ne.symm hj) hno
      exact ih (bankWordEpochNext ring root z e) hzstep hstep

theorem bankWordRootDoneOriginReachableOfOutgoing {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hout :
      ∀ z : BankWordEpochState n,
        BankWordEpochReachable ring root s z →
        BankWordRootTicketOriginAll ring root s z →
        (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
          false →
        BankWordRootTicketOriginAll ring root s
          (bankWordEpochNext ring root z root))
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordRootDoneOrigin ring root s z := by
  obtain ⟨word, hword⟩ := hz
  subst z
  apply bankWordRootTicketOriginAllDone
  exact bankWordRootTicketOriginAllWordOfOutgoing
    ring hn hbank root s hs hout word
    (bankWordEpochStart s) ⟨[], rfl⟩
    (bankWordRootTicketOriginAllInitial ring root s)

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

private theorem bankWordTicketAtSome
    (stage : WValidationStage)
    (old : Option WValidationTicket)
    (ticket : WValidationTicket)
    (h : wTicketAt stage old = some ticket) :
    old = some ticket ∧ ticket.stage = stage := by
  cases old with
  | none => simp [wTicketAt] at h
  | some previous =>
      by_cases hs : previous.stage = stage
      · have hh : some previous = some ticket := by
          simpa [wTicketAt, hs] using h
        have he := Option.some.inj hh
        subst ticket
        exact ⟨rfl, hs⟩
      · simp [wTicketAt, hs] at h

private theorem bankWordTicketJoinSomeLeft
    (left right : Option WValidationTicket)
    (ticket : WValidationTicket)
    (h : wJoinTickets left right = some ticket) :
    ∃ previous : WValidationTicket,
      left = some previous ∧ previous = ticket := by
  cases left with
  | none => simp [wJoinTickets] at h
  | some previous =>
      cases right with
      | none => simp [wJoinTickets] at h
      | some sibling =>
          by_cases hs :
              previous.requestedAt = sibling.requestedAt ∧
                previous.startedAt = sibling.startedAt
          · have hh : some previous = some ticket := by
              simpa [wJoinTickets, hs] using h
            exact ⟨previous, rfl, Option.some.inj hh⟩
          · simp [wJoinTickets, hs] at h

private theorem bankWordTicketStageSome
    (stage : WValidationStage)
    (old : Option WValidationTicket)
    (ticket : WValidationTicket)
    (h : wTicketStage stage old = some ticket) :
    ∃ previous : WValidationTicket,
      old = some previous ∧
      previous.requestedAt = ticket.requestedAt ∧
      previous.startedAt = ticket.startedAt := by
  cases old with
  | none => simp [wTicketStage] at h
  | some previous =>
      have hh :
          some ({ previous with stage := stage } : WValidationTicket) =
            some ticket := by
        simpa [wTicketStage] using h
      have he := Option.some.inj hh
      refine ⟨previous, rfl, ?_, ?_⟩
      · rw [← he]
      · rw [← he]

private theorem bankWordTicketParentSome
    (old : Option WValidationTicket)
    (ticket : WValidationTicket)
    (h : wParentTicket old = some ticket) :
    old = some ticket ∧ ticket.stage ≠ .requested := by
  cases old with
  | none => simp [wParentTicket] at h
  | some previous =>
      by_cases hp :
          previous.stage = .broadcaster ∨
            previous.stage = .waiting ∨ previous.stage = .done
      · have hh : some previous = some ticket := by
          simpa [wParentTicket, hp] using h
        have he := Option.some.inj hh
        subst ticket
        refine ⟨rfl, ?_⟩
        intro hr
        rcases hp with hb | hw | hd
        · rw [hr] at hb
          cases hb
        · rw [hr] at hw
          cases hw
        · rw [hr] at hd
          cases hd
      · simp [wParentTicket, hp] at h

/-- An S2R admission inherits both stamps from the old
waiting ticket at the source/root. -/
theorem bankWordTicketAdmitParentSome
    (stage : WValidationStage)
    (gx gy : Option WValidationTicket)
    (ticket : WValidationTicket)
    (h : wAdmitTickets stage gx gy = some ticket) :
    ∃ previous : WValidationTicket,
      gx = some previous ∧
      previous.stage ≠ .requested ∧
      previous.requestedAt = ticket.requestedAt ∧
      previous.startedAt = ticket.startedAt := by
  unfold wAdmitTickets at h
  obtain ⟨previous, hp, heq⟩ :=
    bankWordTicketJoinSomeLeft
      (wTicketAt .waiting gx) (wTicketAt stage gy) ticket h
  obtain ⟨hroot, hstage⟩ :=
    bankWordTicketAtSome .waiting gx previous hp
  refine ⟨previous, hroot, ?_,
    congrArg WValidationTicket.requestedAt heq,
    congrArg WValidationTicket.startedAt heq⟩
  intro hr
  rw [hr] at hstage
  cases hstage

/-- An S2R challenge retags a parent and never introduces
new request or start timestamps. -/
theorem bankWordTicketChallengeParentSome
    (gx : Option WValidationTicket)
    (ticket : WValidationTicket)
    (h : (wChallengeTickets gx).1 = some ticket) :
    ∃ previous : WValidationTicket,
      gx = some previous ∧
      previous.stage ≠ .requested ∧
      previous.requestedAt = ticket.requestedAt ∧
      previous.startedAt = ticket.startedAt := by
  change wTicketStage .waiting (wParentTicket gx) =
    some ticket at h
  obtain ⟨previous, hp, hr, hs⟩ :=
    bankWordTicketStageSome .waiting (wParentTicket gx) ticket h
  obtain ⟨hroot, hstage⟩ :=
    bankWordTicketParentSome gx previous hp
  exact ⟨previous, hroot, hstage, hr, hs⟩

/-- Retag an old root ticket with the same two stamps, then
extend the nonaccepting suffix by the literal root edge. -/
theorem bankWordRootAllParentNonacceptNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (old fresh : WValidationTicket)
    (hinv : BankWordRootTicketOriginAll ring root s z)
    (hold : (bankWordHardEpochLedger ring root z).validation root =
      some old)
    (hnonreq : old.stage ≠ .requested)
    (hreq : old.requestedAt = fresh.requestedAt)
    (hstart : old.startedAt = fresh.startedAt)
    (hno : (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
      false) :
    BankWordRootTicketOrigin ring root s
      (bankWordEpochNext ring root z root) fresh := by
  rcases hinv old hold with hrequested | horigin
  · exact False.elim (hnonreq hrequested)
  · exact bankWordRootTicketOriginNonacceptNext
      ring root s z fresh root
      (bankWordRootTicketOriginRetag
        ring root s z old fresh horigin hreq hstart) hno

theorem bankWordRootAllCarryNonacceptNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (ticket : WValidationTicket)
    (hinv : BankWordRootTicketOriginAll ring root s z)
    (hroot : (bankWordHardEpochLedger ring root z).validation root =
      some ticket)
    (hno : (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
      false) :
    ticket.stage = .requested ∨
      BankWordRootTicketOrigin ring root s
        (bankWordEpochNext ring root z root) ticket := by
  rcases hinv ticket hroot with hrequested | horigin
  · exact Or.inl hrequested
  · exact Or.inr (bankWordRootTicketOriginNonacceptNext
      ring root s z ticket root horigin hno)

theorem bankWordRootAllAdmitNonacceptNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (stage : WValidationStage)
    (gy : Option WValidationTicket)
    (ticket : WValidationTicket)
    (hinv : BankWordRootTicketOriginAll ring root s z)
    (hno : (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
      false)
    (hnew : wTicketStage .done
      (wAdmitTickets stage
        ((bankWordHardEpochLedger ring root z).validation root) gy) =
          some ticket) :
    BankWordRootTicketOrigin ring root s
      (bankWordEpochNext ring root z root) ticket := by
  obtain ⟨parent, hp, hreq, hstart⟩ :=
    bankWordTicketStageSome .done
      (wAdmitTickets stage
        ((bankWordHardEpochLedger ring root z).validation root) gy)
      ticket hnew
  obtain ⟨old, hold, hnonreq, hpReq, hpStart⟩ :=
    bankWordTicketAdmitParentSome stage
      ((bankWordHardEpochLedger ring root z).validation root)
      gy parent hp
  exact bankWordRootAllParentNonacceptNext
    ring root s z old ticket hinv hold hnonreq
    (hpReq.trans hreq) (hpStart.trans hstart) hno

theorem bankWordRootAllChallengeNonacceptNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (ticket : WValidationTicket)
    (hinv : BankWordRootTicketOriginAll ring root s z)
    (hno : (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
      false)
    (hnew :
      (wChallengeTickets
        ((bankWordHardEpochLedger ring root z).validation root)).1 =
          some ticket) :
    BankWordRootTicketOrigin ring root s
      (bankWordEpochNext ring root z root) ticket := by
  obtain ⟨old, hold, hnonreq, hreq, hstart⟩ :=
    bankWordTicketChallengeParentSome
      ((bankWordHardEpochLedger ring root z).validation root)
      ticket hnew
  exact bankWordRootAllParentNonacceptNext
    ring root s z old ticket hinv hold hnonreq hreq hstart hno

/-- The first ticket output on the selected root edge is
literally the next root ticket in the chronological ledger. -/
theorem bankWordRootOutgoingTicketExact {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation root =
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
        ((bankWordHardEpochLedger ring root z).validation root)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root))).1 := by
  rw [bankWordHardEpochLedgerNext]
  simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt]

/-- Exact S2R first-component ticket action. -/
theorem bankWordS2RRootTicketExact {c : Compiled}
    (stamp : Nat) (x y : ProjW c)
    (gx gy : Option WValidationTicket)
    (hrow : (serW x y).row = "S2R") :
    (wValidationPair stamp x y gx gy).1 =
      if y.ser.phase == .C then
        if x.ser.out == .WAIT && y.ser.probe == .PENDING then gx
        else if x.ser.out == .WAIT &&
            y.ser.probe == .INTERNAL_OK then
          wTicketStage .done
            (wAdmitTickets .observedInternal gx gy)
        else if x.ser.out == .WAIT &&
            y.ser.probe == .LEAF_OK then
          wTicketStage .done (wAdmitTickets .observedLeaf gx gy)
        else (wChallengeTickets gx).1
      else if y.ser.phase == .B then
        if x.ser.out == .DONE then gx
        else (wChallengeTickets gx).1
      else if y.ser.phase == .F then (wChallengeTickets gx).1
      else gx := by
  simp [wValidationPair, hrow]

/-- S2R: frame, observedInternal/observedLeaf join,
or challenge; no synthetic origin. -/
theorem bankWordRootTicketOriginAllS2RNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hinv : BankWordRootTicketOriginAll ring root s z)
    (hrow : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).row = "S2R")
    (hno : (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
      false) :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochNext ring root z root) := by
  intro ticket ht
  rw [bankWordRootOutgoingTicketExact ring root z] at ht
  rw [bankWordS2RRootTicketExact
    (z.2.2.clock + 1)
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    ((bankWordHardEpochLedger ring root z).validation root)
    ((bankWordHardEpochLedger ring root z).validation
      (ring.rightNeighbor root)) hrow] at ht
  split at ht
  · split at ht
    · exact bankWordRootAllCarryNonacceptNext
        ring root s z ticket hinv ht hno
    · split at ht
      · exact Or.inr (bankWordRootAllAdmitNonacceptNext
          ring root s z .observedInternal
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor root))
          ticket hinv hno ht)
      · split at ht
        · exact Or.inr (bankWordRootAllAdmitNonacceptNext
            ring root s z .observedLeaf
            ((bankWordHardEpochLedger ring root z).validation
              (ring.rightNeighbor root))
            ticket hinv hno ht)
        · exact Or.inr (bankWordRootAllChallengeNonacceptNext
            ring root s z ticket hinv hno ht)
  · split at ht
    · split at ht
      · exact bankWordRootAllCarryNonacceptNext
          ring root s z ticket hinv ht hno
      · exact Or.inr (bankWordRootAllChallengeNonacceptNext
          ring root s z ticket hinv hno ht)
    · split at ht
      · exact Or.inr (bankWordRootAllChallengeNonacceptNext
          ring root s z ticket hinv hno ht)
      · exact bankWordRootAllCarryNonacceptNext
          ring root s z ticket hinv ht hno

/-- ROOT_OUT row enumeration from the literal serializerStep
under the post-E leader/follower orientation. -/
theorem bankWordRootOutgoingRowClass {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false) :
    (serW x y).row = "S1" ∨
      (serW x y).row = "SR" ∨
      (serW x y).row = "S6" ∨
      (serW x y).row = "S2R" := by
  cases hc : x.ser.cert <;>
    cases hp : x.ser.phase <;>
    cases ho : x.ser.out <;>
    cases hf : y.ser.phase <;>
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hc, hp, ho, hf]

/-- S1 has OLD cert REQUESTED; zero lease is an independent
condition for the hard-start provenance. -/
theorem bankWordRootSOneRequested {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hrow : (serW x y).row = "S1") :
    x.ser.cert = .REQUESTED := by
  cases hc : x.ser.cert with
  | REQUESTED => rfl
  | IDLE =>
      cases hp : x.ser.phase <;>
        cases ho : x.ser.out <;>
        cases hf : y.ser.phase <;>
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hc, hp, ho, hf] at hrow
  | RUNNING =>
      cases hp : x.ser.phase <;>
        cases ho : x.ser.out <;>
        cases hf : y.ser.phase <;>
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hc, hp, ho, hf] at hrow

/-- S1 writes waiting only from a requested ticket and
zero lease; ticketless or positive-lease starts have none. -/
theorem bankWordRootTicketOriginAllSOneNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hx : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eY.l = false)
    (hrow : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).row = "S1") :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochNext ring root z root) := by
  have hreq := bankWordRootSOneRequested
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hx hy hrow
  by_cases hzero : (z.2.1 root).siLease.val = 0
  · cases hr :
        wTicketAt .requested
          ((bankWordHardEpochLedger ring root z).validation root) with
    | none =>
        intro ticket ht
        rw [bankWordRootOutgoingTicketExact ring root z] at ht
        simp [wValidationPair, hrow, hr] at ht
    | some request =>
        exact bankWordRootTicketOriginAllTicketedStartNext
          ring root s z hz request hx hy hreq hzero hr
  · intro ticket ht
    rw [bankWordRootOutgoingTicketExact ring root z] at ht
    cases hr :
        wTicketAt .requested
          ((bankWordHardEpochLedger ring root z).validation root) <;>
      simp [wValidationPair, hrow, hzero, hr] at ht

/-- All ROOT_OUT rows, completing the earlier hout premise. -/
theorem bankWordRootTicketOriginAllOutgoingNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hinv : BankWordRootTicketOriginAll ring root s z)
    (hno : (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
      false) :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochNext ring root z root) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing
    ring root z.2.1 root (by omega : 2 ≤ n) hfixed rfl
  have hrows := bankWordRootOutgoingRowClass
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2
  rcases hrows with hstart | hreset | haccept | hroute
  · exact bankWordRootTicketOriginAllSOneNext
      ring root s z hz hpost.1 hpost.2 hstart
  · intro ticket ht
    rw [bankWordRootOutgoingTicketExact ring root z] at ht
    simp [wValidationPair, hreset] at ht
  · intro ticket ht
    rw [bankWordRootOutgoingTicketExact ring root z] at ht
    simp [wValidationPair, haccept] at ht
  · exact bankWordRootTicketOriginAllS2RNext
      ring root s z hinv hroute hno

/-- Final unconditional represented-epoch origin bridge. -/
theorem bankWordRootDoneOriginReachable {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordRootDoneOrigin ring root s z := by
  exact bankWordRootDoneOriginReachableOfOutgoing
    ring hn hbank root s hs
    (bankWordRootTicketOriginAllOutgoingNext
      ring hn hbank root s hs) z hz

end L3.RenewalReferenceClock

import Leader.L3.Headline.Stages

/-!
Request-clock entry and the precise stopped coupling
needed to transfer a frozen coupon scanner to the real protocol.

The coupon simulation controls FreshReference.step, which restores
OLD public U/beta and native fields after each edge; it does not
simulate headlinePhysicalNext. A raw rejection alone does not prove
that grant and request coexist at a real physical cut.
-/

namespace L3
namespace HeadlineRequest

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Grant-ready and leaderless implies an actual physical GRANT. -/
theorem grantAtLeaderlessEntrance {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (hgrant : headlineGrantReady ring C)
    (hnoleader : ∀ i : Fin n, (C i).l = false) :
    headlinePurified ring C ∧
      ∃ i : Fin n, (C i).grant = true := by
  rcases hgrant with hroot | htokens
  · obtain ⟨i, hi, _⟩ := hroot
    have hf : (C i).l = false := hnoleader i
    rw [hf] at hi
    cases hi
  · exact htokens

/-- At a still-leaderless request-ready cut, GRANT and REQ
must exist simultaneously on the actual physical configuration. -/
theorem requestReadyHasBothTokens {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (hnoleader : ∀ i : Fin n, (C i).l = false)
    (hready : headlineRequestReady ring C) :
    (∃ i : Fin n, (C i).grant = true) ∧
      (∃ j : Fin n, (C j).req = true) := by
  rcases hready with hroot | htokens
  · obtain ⟨i, hi, _⟩ := hroot
    have hf : (C i).l = false := hnoleader i
    rw [hf] at hi
    cases hi
  · exact ⟨htokens.2.1, htokens.2.2⟩

/-- F.11 gives precisely the width assumptions for the
installed general-width frozen raw coupon estimates. -/
theorem requestWidthAdmissible (n : Nat) (hn : 5 ≤ n) :
    2 ≤ (compileAdvice (ceilLogTwo n)).t ∧
      (compileAdvice (ceilLogTwo n)).t + 3 ≤ n := by
  exact ⟨compileAdvice_t_ge_two (ceilLogTwo n)
      (ceilLogTwo_ge_three n hn),
    (ClosureFull.headlineWidthAdmissible n hn).1⟩

/-- The native leader field in the certificate word is the
same OLD physical leader field as in the headline state. -/
theorem rootlessCertificateOfNoLeader {n : Nat}
    (C : HeadlineConfiguration n)
    (hnoleader : ∀ i : Fin n, (C i).l = false) :
    RootlessCertificate
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) := by
  intro i
  exact hnoleader i

/-- The rootless exclusion at every ring size, from the primitive
compiled tap table. -/
theorem rootlessRelationsImpossibleSupported {n : Nat}
    (C : HeadlineConfiguration n)
    (hn : 5 ≤ n)
    (hnoleader : ∀ i : Fin n, (C i).l = false) :
    ¬ CertificateRelations
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) := by
  exact certificate_rootless_exclusion n hn
    (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C)
    (rootlessCertificateOfNoLeader C hnoleader)

/-- A chosen false relation of the OLD public certificate word.
The last case is NOT measured by the raw R0b/R0c scanner. -/
def RequestRelationFailure {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n) : Prop :=
  ¬ NonzeroRelation
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s ∨
  ¬ RecurrenceRelation
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s ∨
  ¬ MarkerRelation
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s ∨
  ¬ BlockIncrementRelation
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s

/-- Obtain a bad static site in the currently certified range.
This is independent of all inherited scanner/checker scratch. -/
theorem rootlessFailedSiteSupported {n : Nat}
    (C : HeadlineConfiguration n)
    (hn : 5 ≤ n)
    (hnoleader : ∀ i : Fin n, (C i).l = false) :
    ∃ s : Fin n, RequestRelationFailure C s := by
  classical
  have hnot :
      ¬ ∀ s : Fin n,
        RecurrenceRelation
          (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s ∧
        NonzeroRelation
          (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s ∧
        MarkerRelation
          (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s ∧
        BlockIncrementRelation
          (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s :=
    rootlessRelationsImpossibleSupported C hn hnoleader
  obtain ⟨s, hs⟩ := Classical.not_forall.mp hnot
  refine ⟨s, ?_⟩
  unfold RequestRelationFailure
  by_cases hnonzero :
      NonzeroRelation
        (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s
  · by_cases hrec :
        RecurrenceRelation
          (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s
    · by_cases hmark :
          MarkerRelation
            (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s
      · right
        right
        right
        intro hinc
        exact hs ⟨hrec, hnonzero, hmark, hinc⟩
      · exact Or.inr (Or.inr (Or.inl hmark))
    · exact Or.inr (Or.inl hrec)
  · exact Or.inl hnonzero

/-- Exactly the three failures consumed by FreshFixed/CouponClear;
BlockIncrementRelation needs the separate strict digit checker. -/
def RequestRawFailure {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n) : Prop :=
  ¬ NonzeroRelation
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s ∨
  ¬ RecurrenceRelation
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s ∨
  ¬ MarkerRelation
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C) s

/-- All-width joint coupon budget on the FROZEN shadow.
No conclusion about real physical request publication follows. -/
theorem frozenRawCouponBound {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hnoleader : ∀ i : Fin n, (C i).l = false)
    (hbad : RequestRawFailure C s) :
    ∀ T : Nat,
      (CouponClear.couponGPair
        (compileAdvice (ceilLogTwo n)).t).2 *
        costNumerator
          (FreshReference.freshGhostStep ring C s)
          FreshReference.freshGhostGood
          (C, FreshReference.freshGhostInitial n) T ≤
      n ^ T *
        (n * (CouponClear.couponGPair
          (compileAdvice (ceilLogTwo n)).t).1) := by
  have hwidth := requestWidthAdmissible n hn
  have hfrozen : FreshReference.Frozen C C := by
    intro i
    rfl
  have hbudget : CouponClear.CouponJointBudget ring C s :=
    CouponClear.couponJointBudgetOnFailure_elim ring C s
      hwidth.1 hwidth.2 hnoleader hbad
      (CouponClear.couponNodeJointBudgetOnFailureAll ring C s)
  exact CouponClear.couponGhost_scaled_of_joint_budget ring C s
    (C, FreshReference.freshGhostInitial n) hfrozen hbudget

/-- The independent fixed-attempt shadow bound has no additional
genealogy hypothesis and uses precisely the same OLD raw owner. -/
theorem frozenRawFixedAttemptsBound {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hnoleader : ∀ i : Fin n, (C i).l = false)
    (hbad : RequestRawFailure C s) :
    ∀ T : Nat,
      costNumerator
        (FreshReference.freshGhostStep ring C s)
        FreshReference.freshGhostGood
        (C, FreshReference.freshGhostInitial n) T ≤
      n ^ T *
        FreshFixed.attemptCeiling n
          (compileAdvice (ceilLogTwo n)).t := by
  have hwidth := requestWidthAdmissible n hn
  have hfrozen : FreshReference.Frozen C C := by
    intro i
    rfl
  exact FreshFixed.freshGhost_cost_fixedAttempts_paper
    ring C s hwidth.1 hwidth.2 hnoleader hbad
    (C, FreshReference.freshGhostInitial n) hfrozen

/-- The installed projection is to the data-restoring
FreshReference.step, NOT the unmodified real protocol step. -/
theorem frozenRawGhostProjectsToReference {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (z : FreshReference.FreshGhostConfig n (ceilLogTwo n))
    (e : Fin n) :
    (FreshReference.freshGhostStep ring C s z e).1 =
      FreshReference.step ring C z.1 e := by
  exact FreshReference.freshGhost_projection ring C s z e

/-- Real physical evolution on a fixed chronological edge word. -/
def realRequestRun {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) :
    List (Fin n) → HeadlineConfiguration n
  | [] => C
  | e :: tail =>
      realRequestRun ring (headlinePhysicalNext ring C e) tail

/-- A prefix of the selected edges has already reached the
REAL simultaneous request/grant target or the generated target.
The witness is a first-hit cut, not necessarily the final cut. -/
def realRequestHitBy {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) : Prop :=
  ∃ (before after : List (Fin n)),
    word = before ++ after ∧
      (headlineRequestReady ring (realRequestRun ring C before) ∨
        headlineGeneratedTarget ring (realRequestRun ring C before))

theorem realRequestHitBy_of_end {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n))
    (h : headlineRequestReady ring (realRequestRun ring C word) ∨
      headlineGeneratedTarget ring (realRequestRun ring C word)) :
    realRequestHitBy ring C word := by
  exact ⟨word, [], by simp, h⟩

/-- THE MISSING STOPPED COUPLING, NOT A PROVED THEOREM.

For every COMMON scheduler word, a genuine freshly tagged R0c
success in the coupon/frozen ghost must entail that a prefix of
the ACTUAL unmodified headline run has already hit
headlineRequestReady OR headlineGeneratedTarget.

To establish this one must:
(1) couple OLD reader records before first committed public change,
(2) issue a real request on the earlier report/change service,
(3) prove it survives that service (birth reads OLD requests),
(4) preserve or renew some physical grant up to that SAME cut,
    unless the generated target was already reached.

couponTrialSimulation only relates the coupon retry observer to
freshGhostStep; it does not imply this real-process statement. -/
def RequestCouponStoppedCoupling {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : Prop :=
  ∀ word : List (Fin n),
    FreshReference.freshGhostGood
      (LDSinkBoundedKernel.run
        (FreshReference.freshGhostStep ring C s)
        (C, FreshReference.freshGhostInitial n) word) →
    realRequestHitBy ring C word

/-! STOP. Neither this coupling, the independent strict TOP
comparison, nor the all-width certificate exclusion beyond t=17
has been proved. Consequently no unconditional
StageRequestMissingClock is declared in this file. -/

end HeadlineRequest
end L3


namespace L3.HeadlineRequest

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
The comparison does NOT assert equality of the full frozen data:
native b/sh/sg may evolve without a DCC request. The raw owner reads
only rawTok, responder rawKick/u/beta, and the post-E responder
leader bit. Both leader bits remain zero before the first request.
-/

private def requestBankBit (c : Compiled) (x y : Agent c) : Bool :=
  if c.useSmall then (smallPair x y c.K).2.2
  else bankSuccess (bankCell x x.pack.val) (bankCell y y.pack.val)
    (packNext x.pack.val y.pack.val c.b) c.b

private def requestTokenOutputs (c : Compiled) (ev : CertEvent)
    (x y : Agent c) : TokPair × TokPair × TokMeta :=
  tokenStep x y
    (if fireAtSite (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) .siteX
      then firedNative else (certLiteralEPair x.certNative y.certNative).1)
    (if fireAtSite (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) .siteY
      then firedNative else (certLiteralEPair x.certNative y.certNative).2)
    (fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2)
    (dccStep x y ev).request (requestBankBit c x y)

/-- Local field bridge, repeated here to keep the import prefix unchanged. -/
private theorem requestBaseTokenFrame (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.grant = (requestTokenOutputs c ev x y).1.grant ∧
    (baseStep c ev x y).2.grant = (requestTokenOutputs c ev x y).2.1.grant ∧
    (baseStep c ev x y).2.req = (requestTokenOutputs c ev x y).2.1.req := by
  unfold baseStep requestTokenOutputs requestBankBit
  cases c.useSmall <;> exact ⟨rfl, rfl, rfl⟩

private theorem requestTransitionTokenFrame (c : Compiled)
    (x y : Agent c) :
    (transition c x y).1.grant =
        (requestTokenOutputs c (certificateStep c x y).2.2 x y).1.grant ∧
    (transition c x y).2.grant =
        (requestTokenOutputs c (certificateStep c x y).2.2 x y).2.1.grant ∧
    (transition c x y).2.req =
        (requestTokenOutputs c (certificateStep c x y).2.2 x y).2.1.req := by
  exact requestBaseTokenFrame c (certificateStep c x y).2.2 x y

private theorem requestNoOldRequestFire {c : Compiled}
    (x y : Agent c) (hx : x.req = false) (hy : y.req = false) :
    oldFire x y = none := by
  simp [oldFire, fireSelect, hx, hy]

private theorem requestTokenOutputsNoFire (c : Compiled)
    (ev : CertEvent) (x y : Agent c) (h : oldFire x y = none) :
    requestTokenOutputs c ev x y =
      tokenStep x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2
        none (dccStep x y ev).request (requestBankBit c x y) := by
  change fireSelect x y
    (certLiteralEPair x.certNative y.certNative).1
    (certLiteralEPair x.certNative y.certNative).2 = none at h
  simp [requestTokenOutputs, h, fireAtSite]

/-- OLD requests are absent: T0 and HOLD cannot consume a new request;
    rootlessness excludes every T1 sink. The grant producer only adds. -/
private theorem requestTokenLocal {c : Compiled}
    (x y : Agent c) (fx fy : CertNative) (demand bank : Bool)
    (hx : x.req = false) (hy : y.req = false)
    (hfx : fx.l = false) (hfy : fy.l = false) :
    (tokenStep x y fx fy none demand bank).2.1.req = demand ∧
    ((x.grant = true ∨ y.grant = true) →
      (tokenStep x y fx fy none demand bank).1.grant = true ∨
      (tokenStep x y fx fy none demand bank).2.1.grant = true) := by
  cases hgx : x.grant <;> cases hgy : y.grant <;>
    cases demand <;> cases bank <;>
    simp [tokenStep, hx, hy, hfx, hfy, hgx, hgy]

/-- The actual full pair publishes the DCC demand, and retains an OLD
    grant, on the same service. No successful BANK event is assumed. -/
theorem requestPairNoOldRequest (c : Compiled) (x y : Agent c)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxr : x.req = false) (hyr : y.req = false) :
    (transition c x y).2.req =
        (dccStep x y (certificateStep c x y).2.2).request ∧
    ((x.grant = true ∨ y.grant = true) →
      (transition c x y).1.grant = true ∨
      (transition c x y).2.grant = true) := by
  have hp := headlineRendezvousLeaderlessPostE x.certNative y.certNative
    (by exact hxl) (by exact hyl)
  have ht := requestTokenLocal x y
    (certLiteralEPair x.certNative y.certNative).1
    (certLiteralEPair x.certNative y.certNative).2
    (dccStep x y (certificateStep c x y).2.2).request
    (requestBankBit c x y) hxr hyr hp.1 hp.2.1
  have he := requestTokenOutputsNoFire c
    (certificateStep c x y).2.2 x y
    (requestNoOldRequestFire x y hxr hyr)
  rw [← he] at ht
  have hf := requestTransitionTokenFrame c x y
  constructor
  · exact hf.2.2.trans ht.1
  · intro hold
    rcases ht.2 hold with hsource | htarget
    · exact Or.inl (hf.1.trans hsource)
    · exact Or.inr (hf.2.1.trans htarget)

private theorem requestAtSource {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n) :
    headlinePhysicalNext ring C e e =
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).1 := by
  have h : (protocol (ceilLogTwo n)).step ring C e e =
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).1 := by
    simp [PopulationProtocol.step, protocol]
  exact h

private theorem requestAtTarget {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (C : HeadlineConfiguration n) (e : Fin n) :
    headlinePhysicalNext ring C e (ring.rightNeighbor e) =
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).2 := by
  have hne : ring.rightNeighbor e ≠ e :=
    Ne.symm (ring_neighbor_distinct ring hn e)
  have h : (protocol (ceilLogTwo n)).step ring C e
      (ring.rightNeighbor e) =
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).2 := by
    simp [PopulationProtocol.step, protocol, hne]
  exact h

private theorem requestAway {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e i : Fin n)
    (he : i ≠ e) (hy : i ≠ ring.rightNeighbor e) :
    headlinePhysicalNext ring C e i = C i := by
  have h : (protocol (ceilLogTwo n)).step ring C e i = C i := by
    simp [PopulationProtocol.step, he, hy]
  exact h

/-- No grant-loss edge exists in the leaderless no-OLD-request scope. -/
theorem requestGrantSurvives {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (C : HeadlineConfiguration n) (e : Fin n)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (hg : ∃ i : Fin n, (C i).grant = true) :
    ∃ i : Fin n, (headlinePhysicalNext ring C e i).grant = true := by
  have hp := (requestPairNoOldRequest
    (compileAdvice (ceilLogTwo n)) (C e) (C (ring.rightNeighbor e))
    (hl e) (hl (ring.rightNeighbor e))
    (hr e) (hr (ring.rightNeighbor e))).2
  obtain ⟨i, hi⟩ := hg
  by_cases hpair : i = e ∨ i = ring.rightNeighbor e
  · have hold : (C e).grant = true ∨
        (C (ring.rightNeighbor e)).grant = true := by
      rcases hpair with hs | ht
      · exact Or.inl (by simpa only [hs] using hi)
      · exact Or.inr (by simpa only [ht] using hi)
    rcases hp hold with hs | ht
    · refine ⟨e, ?_⟩
      exact (congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.grant) (requestAtSource ring C e)).trans hs
    · refine ⟨ring.rightNeighbor e, ?_⟩
      exact (congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.grant) (requestAtTarget ring hn C e)).trans ht
  · have he : i ≠ e := fun h => hpair (Or.inl h)
    have hy : i ≠ ring.rightNeighbor e := fun h => hpair (Or.inr h)
    refine ⟨i, ?_⟩
    exact (congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
      a.grant) (requestAway ring C e i he hy)).trans hi

private theorem requestDccEvent {c : Compiled}
    (x y : Agent c) (ev : CertEvent)
    (h : ev.d1Reject = true ∨ ev.duX = true ∨ ev.duY = true) :
    (dccStep x y ev).request = true := by
  rcases h with hraw | hx | hy
  · simp [dccStep, hraw]
  · unfold dccStep
    dsimp only
    split <;> simp [hx]
  · unfold dccStep
    dsimp only
    split <;> simp [hy]

private theorem requestDccQuiet {c : Compiled}
    (x y : Agent c) (ev : CertEvent)
    (h : (dccStep x y ev).request = false) :
    ev.d1Reject = false ∧ ev.duX = false ∧ ev.duY = false := by
  have hraw : ev.d1Reject = false := by
    cases hh : ev.d1Reject with
    | false => rfl
    | true =>
      have hb := requestDccEvent x y ev (Or.inl hh)
      rw [h] at hb
      cases hb
  have hx : ev.duX = false := by
    cases hh : ev.duX with
    | false => rfl
    | true =>
      have hb := requestDccEvent x y ev (Or.inr (Or.inl hh))
      rw [h] at hb
      cases hb
  have hy : ev.duY = false := by
    cases hh : ev.duY with
    | false => rfl
    | true =>
      have hb := requestDccEvent x y ev (Or.inr (Or.inr hh))
      rw [h] at hb
      cases hb
  exact ⟨hraw, hx, hy⟩

private theorem requestBoolPairQuiet (a b c d : Bool)
    (h : ((a != b) || (c != d)) = false) : a = b ∧ c = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp at h ⊢

/-- The visible writes and event use the same resolved SI outputs. -/
private theorem requestPairVisibleEvents (c : Compiled) (x y : Agent c) :
    (certificateStep c x y).2.2.duX =
      (((transition c x y).1.u != x.u) ||
        ((transition c x y).1.beta != x.beta)) ∧
    (certificateStep c x y).2.2.duY =
      (((transition c x y).2.u != y.u) ||
        ((transition c x y).2.beta != y.beta)) := by
  exact ⟨rfl, rfl⟩

private theorem requestPairQuiet (c : Compiled) (x y : Agent c)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxr : x.req = false) (hyr : y.req = false)
    (hn : (transition c x y).2.req = false) :
    (rawD1Step c x y (postEInfo x y)).reject = false ∧
    ((transition c x y).1.u = x.u ∧
      (transition c x y).1.beta = x.beta) ∧
    ((transition c x y).2.u = y.u ∧
      (transition c x y).2.beta = y.beta) := by
  have hd : (dccStep x y (certificateStep c x y).2.2).request = false :=
    (requestPairNoOldRequest c x y hxl hyl hxr hyr).1.symm.trans hn
  have hq := requestDccQuiet x y (certificateStep c x y).2.2 hd
  have hv := requestPairVisibleEvents c x y
  have hx := requestBoolPairQuiet
    (transition c x y).1.u x.u (transition c x y).1.beta x.beta
    (hv.1.symm.trans hq.2.1)
  have hy := requestBoolPairQuiet
    (transition c x y).2.u y.u (transition c x y).2.beta y.beta
    (hv.2.symm.trans hq.2.2)
  exact ⟨hq.1, hx, hy⟩

/-- Absence of a successor request implies no public u/beta change and
    no raw rejection on the actual served pair. -/
theorem requestQuietPhysical {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (C : HeadlineConfiguration n) (e : Fin n)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (hafter : ∀ i : Fin n,
      (headlinePhysicalNext ring C e i).req = false) :
    (∀ i : Fin n,
      (headlinePhysicalNext ring C e i).u = (C i).u ∧
      (headlinePhysicalNext ring C e i).beta = (C i).beta) ∧
    (FreshReference.rawResult ring C e).reject = false := by
  have hat := congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
    a.req) (requestAtTarget ring hn C e)
  have hnew : (transition (compileAdvice (ceilLogTwo n))
      (C e) (C (ring.rightNeighbor e))).2.req = false :=
    hat.symm.trans (hafter (ring.rightNeighbor e))
  have hp := requestPairQuiet (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
    (hl e) (hl (ring.rightNeighbor e))
    (hr e) (hr (ring.rightNeighbor e)) hnew
  constructor
  · intro i
    by_cases hs : i = e
    · subst i
      exact ⟨(congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.u) (requestAtSource ring C e)).trans hp.2.1.1,
        (congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.beta) (requestAtSource ring C e)).trans hp.2.1.2⟩
    · by_cases ht : i = ring.rightNeighbor e
      · subst i
        exact ⟨(congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
            a.u) (requestAtTarget ring hn C e)).trans hp.2.2.1,
          (congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
            a.beta) (requestAtTarget ring hn C e)).trans hp.2.2.2⟩
      · exact ⟨congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
            a.u) (requestAway ring C e i hs ht),
          congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
            a.beta) (requestAway ring C e i hs ht)⟩
  · exact hp.1

/-- The real first-hit target; never a frozen-state target. -/
def requestStoppedTarget {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) : Prop :=
  headlineRequestReady ring C ∨ headlineGeneratedTarget ring C

structure RequestBeforeStop {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) : Prop where
  purified : headlinePurified ring C
  grant : ∃ i : Fin n, (C i).grant = true
  rootless : ∀ i : Fin n, (C i).l = false
  noRequest : ∀ i : Fin n, (C i).req = false

private theorem requestBeforeStopStart {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false) :
    RequestBeforeStop ring C := by
  have h := grantAtLeaderlessEntrance ring C hg hl
  exact ⟨h.1, h.2, hl, hr⟩

/-- The grant is retained even on the first request-producing edge.
    On a nonterminal successor this also forces all requests to be zero. -/
theorem requestBeforeStopStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (h : RequestBeforeStop ring C)
    (hstop : ¬ requestStoppedTarget ring (headlinePhysicalNext ring C e)) :
    RequestBeforeStop ring (headlinePhysicalNext ring C e) := by
  have hp := headlineStagesPurifiedStep ring hn C e h.purified
  have hg := requestGrantSurvives ring (by omega) C e
    h.rootless h.noRequest h.grant
  have hl := headlineRendezvousNoFireRemainsRootless ring C e
    (by omega) h.rootless
    (requestNoOldRequestFire (C e) (C (ring.rightNeighbor e))
      (h.noRequest e) (h.noRequest (ring.rightNeighbor e)))
  have hr : ∀ i : Fin n,
      (headlinePhysicalNext ring C e i).req = false := by
    intro i
    cases hh : (headlinePhysicalNext ring C e i).req with
    | false => rfl
    | true =>
      exact False.elim (hstop (Or.inl (Or.inr ⟨hp, hg, ⟨i, hh⟩⟩)))
  exact ⟨hp, hg, hl, hr⟩

/-- A visible read-field change or an actual raw rejection gives a real
    request-ready cut on that very edge, with the OLD grant surviving. -/
theorem requestChangeOrRejectHitsTarget {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (h : RequestBeforeStop ring C)
    (hevent :
      (∃ i : Fin n,
        (headlinePhysicalNext ring C e i).u ≠ (C i).u ∨
        (headlinePhysicalNext ring C e i).beta ≠ (C i).beta) ∨
      (FreshReference.rawResult ring C e).reject = true) :
    requestStoppedTarget ring (headlinePhysicalNext ring C e) := by
  classical
  by_cases hs : requestStoppedTarget ring (headlinePhysicalNext ring C e)
  · exact hs
  · have hnxt := requestBeforeStopStep ring hn C e h hs
    have hq := requestQuietPhysical ring (by omega) C e
      h.rootless h.noRequest hnxt.noRequest
    rcases hevent with hc | hr
    · obtain ⟨i, hi⟩ := hc
      rcases hi with hu | hb
      · exact False.elim (hu (hq.1 i).1)
      · exact False.elim (hb (hq.1 i).2)
    · have hbad : (false : Bool) = true := hq.2.symm.trans hr
      cases hbad

/-- Exactly the physical fields read by the rootless raw owner. -/
def RequestScannerAgreement {n q : Nat}
    (C R : (protocol q).Configuration n) : Prop :=
  ∀ i : Fin n,
    (C i).u = (R i).u ∧ (C i).beta = (R i).beta ∧
    (C i).rawTok = (R i).rawTok ∧ (C i).rawKick = (R i).rawKick

private theorem requestRawPairEq (c : Compiled)
    (x y v w : Agent c)
    (hxt : x.rawTok = v.rawTok) (hyt : y.rawTok = w.rawTok)
    (hyk : y.rawKick = w.rawKick)
    (hyu : y.u = w.u) (hyb : y.beta = w.beta)
    (hxl : x.l = false) (hyl : y.l = false)
    (hvl : v.l = false) (hwl : w.l = false) :
    rawD1Step c x y (postEInfo x y) =
      rawD1Step c v w (postEInfo v w) := by
  have hl := raw_postY_rootless x y hxl hyl
  have hr := raw_postY_rootless v w hvl hwl
  simp only [rawD1Step, hxt, hyt, hyk, hyu, hyb, hl, hr]

theorem requestRawResultsAgree {n : Nat} (ring : DirectedRing n)
    (C R : HeadlineConfiguration n) (e : Fin n)
    (ha : RequestScannerAgreement C R)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (R i).l = false) :
    FreshReference.rawResult ring C e =
      FreshReference.rawResult ring R e := by
  exact requestRawPairEq (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
    (R e) (R (ring.rightNeighbor e))
    (ha e).2.2.1 (ha (ring.rightNeighbor e)).2.2.1
    (ha (ring.rightNeighbor e)).2.2.2
    (ha (ring.rightNeighbor e)).1 (ha (ring.rightNeighbor e)).2.1
    (hl e) (hl (ring.rightNeighbor e))
    (hr e) (hr (ring.rightNeighbor e))

/-- One same-edge scanner comparison. All other protocol owners may
    evolve; the native scratch fields are deliberately not equated. -/
theorem requestScannerStep {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (fixed C R : HeadlineConfiguration n)
    (e : Fin n)
    (hfroot : ∀ i : Fin n, (fixed i).l = false)
    (hcroot : ∀ i : Fin n, (C i).l = false)
    (hf : FreshReference.Frozen fixed R)
    (ha : RequestScannerAgreement C R)
    (hq : ∀ i : Fin n,
      (headlinePhysicalNext ring C e i).u = (C i).u ∧
      (headlinePhysicalNext ring C e i).beta = (C i).beta) :
    RequestScannerAgreement (headlinePhysicalNext ring C e)
      (FreshReference.step ring fixed R e) := by
  have hrf : FreshReference.Frozen fixed (FreshReference.step ring fixed R e) :=
    FreshReference.step_frozen ring fixed R hf e
  have hrroot : ∀ i : Fin n, (R i).l = false :=
    FreshReference.frozen_rootless fixed R hfroot hf
  have hraw := requestRawResultsAgree ring C R e ha hcroot hrroot
  have hframe := fresh_raw_pair_projection (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
  have hne : ring.rightNeighbor e ≠ e :=
    Ne.symm (ring_neighbor_distinct ring hn e)
  intro i
  have hu : (headlinePhysicalNext ring C e i).u =
      (FreshReference.step ring fixed R e i).u :=
    (hq i).1.trans ((ha i).1.trans
      ((FreshReference.frozen_fields fixed R hf i).1.trans
        (FreshReference.frozen_fields fixed
          (FreshReference.step ring fixed R e) hrf i).1.symm))
  have hb : (headlinePhysicalNext ring C e i).beta =
      (FreshReference.step ring fixed R e i).beta :=
    (hq i).2.trans ((ha i).2.1.trans
      ((FreshReference.frozen_fields fixed R hf i).2.1.trans
        (FreshReference.frozen_fields fixed
          (FreshReference.step ring fixed R e) hrf i).2.1.symm))
  refine ⟨hu, hb, ?_⟩
  by_cases hs : i = e
  · subst i
    have hret := raw_source_retires (compileAdvice (ceilLogTwo n))
      (C e) (C (ring.rightNeighbor e))
      (postEInfo (C e) (C (ring.rightNeighbor e)))
    have href := FreshReference.source_clears ring fixed R e
    exact ⟨(congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.rawTok) (requestAtSource ring C e)).trans
          (hframe.1.trans (hret.1.trans href.1.symm)),
      (congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.rawKick) (requestAtSource ring C e)).trans
          (hframe.2.2.1.trans (hret.2.trans href.2.symm))⟩
  · by_cases ht : i = ring.rightNeighbor e
    · subst i
      have href := FreshReference.target_raw ring fixed R e hne
      have htok := congrArg (fun a : RawResult
        (compileAdvice (ceilLogTwo n)).t => a.tokY) hraw
      have hkick := congrArg (fun a : RawResult
        (compileAdvice (ceilLogTwo n)).t => a.kickY) hraw
      exact ⟨(congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.rawTok) (requestAtTarget ring hn C e)).trans
            (hframe.2.1.trans (htok.trans href.1.symm)),
        (congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.rawKick) (requestAtTarget ring hn C e)).trans
            (hframe.2.2.2.trans (hkick.trans href.2.symm))⟩
    · have href := FreshReference.other ring fixed R e i hs ht
      exact ⟨(congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.rawTok) (requestAway ring C e i hs ht)).trans
            ((ha i).2.2.1.trans (congrArg
              (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.rawTok)
              href).symm),
        (congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.rawKick) (requestAway ring C e i hs ht)).trans
            ((ha i).2.2.2.trans (congrArg
              (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.rawKick)
              href).symm)⟩

/-- A reference rejection flag is still false on every real pre-target
    prefix. The entire reference genealogy is kept, not restarted. -/
structure RequestCoupled {n : Nat} (ring : DirectedRing n)
    (fixed C : HeadlineConfiguration n)
    (z : FreshReference.FreshGhostConfig n (ceilLogTwo n)) : Prop where
  live : RequestBeforeStop ring C
  frozen : FreshReference.Frozen fixed z.1
  same : RequestScannerAgreement C z.1
  unseen : z.2.seen = false

private theorem requestCoupledStart {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false) :
    RequestCoupled ring C C (C, FreshReference.freshGhostInitial n) := by
  refine ⟨requestBeforeStopStart ring C hg hl hr, ?_, ?_, rfl⟩
  · intro i
    rfl
  · intro i
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The stopped comparison is closed under a common scheduler letter.
    The only excluded child is the real desired first-hit target. -/
theorem requestCoupledStep {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (fixed C : HeadlineConfiguration n)
    (s e : Fin n)
    (z : FreshReference.FreshGhostConfig n (ceilLogTwo n))
    (hfroot : ∀ i : Fin n, (fixed i).l = false)
    (h : RequestCoupled ring fixed C z)
    (hstop : ¬ requestStoppedTarget ring (headlinePhysicalNext ring C e)) :
    RequestCoupled ring fixed (headlinePhysicalNext ring C e)
      (FreshReference.freshGhostStep ring fixed s z e) := by
  have hlive := requestBeforeStopStep ring hn C e h.live hstop
  have hquiet := requestQuietPhysical ring (by omega) C e
    h.live.rootless h.live.noRequest hlive.noRequest
  have hrroot : ∀ i : Fin n, (z.1 i).l = false :=
    FreshReference.frozen_rootless fixed z.1 hfroot h.frozen
  have hraw := requestRawResultsAgree ring C z.1 e
    h.same h.live.rootless hrroot
  have hrquiet : (FreshReference.rawResult ring z.1 e).reject = false :=
    (congrArg (fun a : RawResult
      (compileAdvice (ceilLogTwo n)).t => a.reject) hraw).symm.trans hquiet.2
  have hselected : FreshReference.freshSelectedReject ring z.1 z.2 e = false := by
    cases hh : FreshReference.freshSelectedReject ring z.1 z.2 e with
    | false => rfl
    | true =>
      have hb := FreshReference.freshSelectedReject_implies_raw
        ring z.1 z.2 e hh
      rw [hrquiet] at hb
      cases hb
  refine ⟨hlive, ?_, ?_, ?_⟩
  · exact FreshReference.step_frozen ring fixed z.1 h.frozen e
  · exact requestScannerStep ring (by omega) fixed C z.1 e
      hfroot h.live.rootless h.frozen h.same hquiet.1
  · rw [FreshReference.freshGhost_flag_step, h.unseen, hselected]
    rfl

/-- Shared finite-word alternative: a real target prefix was reached,
    or all scanner coordinates still agree and the reference has not
    recorded a fresh rejection. No conditioning on a future event. -/
theorem requestCoupledRun {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (fixed : HeadlineConfiguration n) (s : Fin n)
    (hfroot : ∀ i : Fin n, (fixed i).l = false) :
    ∀ (word : List (Fin n)) (C : HeadlineConfiguration n)
      (z : FreshReference.FreshGhostConfig n (ceilLogTwo n)),
      RequestCoupled ring fixed C z →
      realRequestHitBy ring C word ∨
      RequestCoupled ring fixed (realRequestRun ring C word)
        (LDSinkBoundedKernel.run
          (FreshReference.freshGhostStep ring fixed s) z word) := by
  classical
  intro word
  induction word with
  | nil =>
    intro C z h
    exact Or.inr h
  | cons e tail ih =>
    intro C z h
    by_cases hs : requestStoppedTarget ring (headlinePhysicalNext ring C e)
    · exact Or.inl ⟨[e], tail, rfl, hs⟩
    · have hc := requestCoupledStep ring hn fixed C s e z hfroot h hs
      rcases ih (headlinePhysicalNext ring C e)
          (FreshReference.freshGhostStep ring fixed s z e) hc with hh | hh
      · obtain ⟨before, after, hword, htarget⟩ := hh
        refine Or.inl ⟨e :: before, after, ?_, htarget⟩
        simpa only [List.cons_append] using congrArg (List.cons e) hword
      · exact Or.inr hh

/-- The requested named coupling, with no false-relation or numerical
    premise. A reference fresh report always entails a real earlier hit. -/
theorem requestCouponStoppedCoupling {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false) :
    RequestCouponStoppedCoupling ring C s := by
  intro word hgood
  rcases requestCoupledRun ring hn C s hl word C
      (C, FreshReference.freshGhostInitial n)
      (requestCoupledStart ring C hg hl hr) with hhit | hsame
  · exact hhit
  · have hb : (false : Bool) = true := hsame.unseen.symm.trans hgood
    cases hb

/-- An explicit finite-prefix scanner agreement corollary. -/
theorem requestScannerAgreementBeforeHit {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (word : List (Fin n)) (hmiss : ¬ realRequestHitBy ring C word) :
    RequestScannerAgreement (realRequestRun ring C word)
      (LDSinkBoundedKernel.run
        (FreshReference.freshGhostStep ring C s)
        (C, FreshReference.freshGhostInitial n) word).1 := by
  rcases requestCoupledRun ring hn C s hl word C
      (C, FreshReference.freshGhostInitial n)
      (requestCoupledStart ring C hg hl hr) with hhit | hsame
  · exact False.elim (hmiss hhit)
  · exact hsame.same

/-- Direct finite-horizon transfer. Early real reports or public changes
    only shorten the clock; reference success is not conditioned away. -/
theorem requestCoupledCost {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (fixed : HeadlineConfiguration n) (s : Fin n)
    (hfroot : ∀ i : Fin n, (fixed i).l = false) :
    ∀ (T : Nat) (C : HeadlineConfiguration n)
      (z : FreshReference.FreshGhostConfig n (ceilLogTwo n)),
      RequestCoupled ring fixed C z →
      costNumerator (headlinePhysicalNext ring)
        (requestStoppedTarget ring) C T ≤
      costNumerator (FreshReference.freshGhostStep ring fixed s)
        FreshReference.freshGhostGood z T := by
  classical
  intro T
  induction T with
  | zero =>
    intro C z h
    exact Nat.le_refl _
  | succ T ih =>
    intro C z h
    by_cases htarget : requestStoppedTarget ring C
    · rw [costNumerator_terminal (headlinePhysicalNext ring)
        (requestStoppedTarget ring) C htarget (T + 1)]
      exact Nat.zero_le _
    · have hnot : ¬ FreshReference.freshGhostGood z := by
        intro hh
        have hb : (false : Bool) = true := h.unseen.symm.trans hh
        cases hb
      rw [costNumerator_succ (headlinePhysicalNext ring)
          (requestStoppedTarget ring) C htarget T,
        costNumerator_succ (FreshReference.freshGhostStep ring fixed s)
          FreshReference.freshGhostGood z hnot T]
      apply Nat.add_le_add_left
      apply ofFn_sum_le
      intro e
      by_cases hs : requestStoppedTarget ring (headlinePhysicalNext ring C e)
      · rw [costNumerator_terminal (headlinePhysicalNext ring)
          (requestStoppedTarget ring) (headlinePhysicalNext ring C e) hs T]
        exact Nat.zero_le _
      · exact ih (headlinePhysicalNext ring C e)
          (FreshReference.freshGhostStep ring fixed s z e)
          (requestCoupledStep ring hn fixed C s e z hfroot h hs)

/-- The all-width CouponJointBudgetOnFailure now bounds the REAL
    request-ready-or-generated first-hit cost, at its exact scale. -/
theorem requestRawCouponScaledCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (hbad : RequestRawFailure C s) (T : Nat) :
    (CouponClear.couponGPair (compileAdvice (ceilLogTwo n)).t).2 *
      costNumerator (headlinePhysicalNext ring)
        (requestStoppedTarget ring) C T ≤
    n ^ T * (n *
      (CouponClear.couponGPair (compileAdvice (ceilLogTwo n)).t).1) := by
  have hc := requestCoupledCost ring hn C s hl T C
    (C, FreshReference.freshGhostInitial n)
    (requestCoupledStart ring C hg hl hr)
  exact Nat.le_trans
    (Nat.mul_le_mul_left
      (CouponClear.couponGPair (compileAdvice (ceilLogTwo n)).t).2 hc)
    (frozenRawCouponBound ring C s hn hl hbad T)

/-- An unconditional raw-failure clock at the installed fixed-attempt
    coefficient, independent of the remaining headline ledger check. -/
theorem requestRawFixedCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (hbad : RequestRawFailure C s) (T : Nat) :
    costNumerator (headlinePhysicalNext ring)
      (requestStoppedTarget ring) C T ≤
      n ^ T * FreshFixed.attemptCeiling n
        (compileAdvice (ceilLogTwo n)).t := by
  exact Nat.le_trans
    (requestCoupledCost ring hn C s hl T C
      (C, FreshReference.freshGhostInitial n)
      (requestCoupledStart ring C hg hl hr))
    (frozenRawFixedAttemptsBound ring C s hn hl hbad T)

theorem requestRawFixedExpected {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (hbad : RequestRawFailure C s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring) (requestStoppedTarget ring) C
      ((FreshFixed.attemptCeiling n
        (compileAdvice (ceilLogTwo n)).t : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) (requestStoppedTarget ring)
    (by omega) C
    (FreshFixed.attemptCeiling n (compileAdvice (ceilLogTwo n)).t)).2
  intro T
  exact requestRawFixedCost ring hn C s hg hl hr hbad T

/-- Abstract arithmetic only: no compiled constants are normalized. -/
theorem requestScaledCostToHeadline (D X mass n B rate : Nat)
    (hD : 0 < D)
    (hcost : D * X ≤ mass * (n * B))
    (hcoefficient : B ≤ D * ((rate + 1) * n)) :
    X ≤ mass * ((rate + 1) * n ^ 2) := by
  apply Nat.le_of_mul_le_mul_left (c := D) ?_ hD
  calc
    D * X ≤ mass * (n * B) := hcost
    _ ≤ mass * (n * (D * ((rate + 1) * n))) :=
      Nat.mul_le_mul_left mass (Nat.mul_le_mul_left n hcoefficient)
    _ = D * (mass * ((rate + 1) * n ^ 2)) := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl

/-- Conditional numerical endpoint, not a claim that the required
    coefficient inequality has been checked for the selected ledger. -/
theorem requestRawExpectedOfCoefficient {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (hbad : RequestRawFailure C s)
    (hpositive :
      0 < (CouponClear.couponGPair (compileAdvice (ceilLogTwo n)).t).2)
    (hcoefficient :
      (CouponClear.couponGPair (compileAdvice (ceilLogTwo n)).t).1 ≤
      (CouponClear.couponGPair (compileAdvice (ceilLogTwo n)).t).2 *
        ((headlineCheckerRate n + 1) * n)) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring) (requestStoppedTarget ring) C
      (((headlineCheckerRate n + 1) * n ^ 2 : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) (requestStoppedTarget ring)
    (by omega) C ((headlineCheckerRate n + 1) * n ^ 2)).2
  intro T
  exact requestScaledCostToHeadline
    (CouponClear.couponGPair (compileAdvice (ceilLogTwo n)).t).2
    (costNumerator (headlinePhysicalNext ring) (requestStoppedTarget ring) C T)
    (n ^ T) n
    (CouponClear.couponGPair (compileAdvice (ceilLogTwo n)).t).1
    (headlineCheckerRate n) hpositive
    (requestRawCouponScaledCost ring hn C s hg hl hr hbad T)
    hcoefficient

end L3.HeadlineRequest

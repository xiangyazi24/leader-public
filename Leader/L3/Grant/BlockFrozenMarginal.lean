import Leader.L3.Grant.BlockFirstFailure
import Leader.L3.Headline.Stages

/-!
G16 physical-to-frozen marginal audit, actual G18 target.

The quantitative theorem below retains the exact, unbounded
non-defect term for physical cold-proxy hits not seen by the
initial-carrier frozen latch.  No G13 theorem supplies that
missing correspondence.  Both G14 defect charges are explicit.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Purification is preserved along the SAME real scheduler word. -/
theorem grantBlockMarginalPurifiedWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    ∀ (word : List (Fin n)) (C : HeadlineConfiguration n),
      headlinePurified ring C →
      headlinePurified ring (Counter.Word ring word C) := by
  intro word
  induction word with
  | nil =>
      intro C hp
      exact hp
  | cons edge rest ih =>
      intro C hp
      change headlinePurified ring
        (Counter.Word ring rest
          (headlinePhysicalNext ring C edge))
      exact ih _ (headlineStagesPurifiedStep ring hn C edge hp)

/-- A native leader following a physical service is already G18
success, because the same physical service preserves purification. -/
theorem grantBlockG18VetoLeaderReady {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (edge root : Fin n)
    (hp : headlinePurified ring C)
    (hl : ((headlinePhysicalNext ring C edge) root).l = true) :
    headlineGrantReady ring (headlinePhysicalNext ring C edge) ∨
      headlineGeneratedTarget ring (headlinePhysicalNext ring C edge) := by
  have hpur := headlineStagesPurifiedStep ring hn C edge hp
  have hprotect : Protected ring
      (nativeProjection (headlinePhysicalNext ring C edge)) :=
    hpur.2 ⟨root, hl⟩
  exact Or.inl (Or.inl ⟨root, hl, hprotect⟩)

/-- Migration or new production of a physical grant is likewise
a G18 success at the POST-service cut, provided the entrance
was purified.  No assumption that the grant was newly minted. -/
theorem grantBlockG18MigratedGrantReady {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (edge root : Fin n)
    (hp : headlinePurified ring C)
    (hg : ¬ Counter.GrantFree
      (headlinePhysicalNext ring C edge) root) :
    headlineGrantReady ring (headlinePhysicalNext ring C edge) ∨
      headlineGeneratedTarget ring (headlinePhysicalNext ring C edge) := by
  have hpur := headlineStagesPurifiedStep ring hn C edge hp
  have hgrant :
      ((headlinePhysicalNext ring C edge) root).grant = true := by
    cases hh : ((headlinePhysicalNext ring C edge) root).grant with
    | false =>
        exact False.elim (hg hh)
    | true =>
        rfl
  exact Or.inl (Or.inr ⟨hpur, ⟨root, hgrant⟩⟩)

/-- Before the G18 first target on a purified physical path,
neither a leader nor a grant may be present anywhere. -/
theorem grantBlockG18PendingRootlessGrantless {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (hp : headlinePurified ring C)
    (hnot : ¬ (headlineGrantReady ring C ∨
      headlineGeneratedTarget ring C)) :
    (∀ i : Fin n, (C i).l = false) ∧
      (∀ i : Fin n, (C i).grant = false) := by
  constructor
  · intro i
    cases hh : (C i).l with
    | false =>
        rfl
    | true =>
        have hprotected : Protected ring (nativeProjection C) :=
          hp.2 ⟨i, hh⟩
        exact False.elim (hnot
          (Or.inl (Or.inl ⟨i, hh, hprotected⟩)))
  · intro i
    cases hh : (C i).grant with
    | false =>
        rfl
    | true =>
        exact False.elim (hnot
          (Or.inl (Or.inr ⟨hp, ⟨i, hh⟩⟩)))

/-- On the G18 pretarget branch, a BANK producer cannot see an
OLD grant or OLD native leader.  The other native fields and
request bits remain completely arbitrary. -/
theorem grantBlockG18PendingPrefix {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n)
    (hp : headlinePurified ring C)
    (pre : List (Fin n))
    (hnot : ¬ (headlineGrantReady ring (Counter.Word ring pre C) ∨
      headlineGeneratedTarget ring (Counter.Word ring pre C))) :
    (∀ i : Fin n,
      ((Counter.Word ring pre C) i).l = false) ∧
    (∀ i : Fin n,
      ((Counter.Word ring pre C) i).grant = false) := by
  exact grantBlockG18PendingRootlessGrantless ring
    (Counter.Word ring pre C)
    (grantBlockMarginalPurifiedWord ring hn pre C hp) hnot

/-- A supposed pretarget physical service whose final native X
is a leader is impossible; the leader would already satisfy
G18 through the preserved Protected/P purification receipt. -/
theorem grantBlockG18RejectsLeaderVetoBeforeTarget {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (edge root : Fin n)
    (hp : headlinePurified ring C)
    (hnot : ¬ (headlineGrantReady ring
        (headlinePhysicalNext ring C edge) ∨
      headlineGeneratedTarget ring
        (headlinePhysicalNext ring C edge))) :
    ((headlinePhysicalNext ring C edge) root).l = false := by
  have hpost := headlineStagesPurifiedStep ring hn C edge hp
  exact (grantBlockG18PendingRootlessGrantless ring
    (headlinePhysicalNext ring C edge) hpost hnot).1 root

/-- Same classification for any migrated (or BANK-produced) grant:
it cannot coexist with a pretarget G18 POST cut. -/
theorem grantBlockG18RejectsGrantMigrationBeforeTarget {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (edge root : Fin n)
    (hp : headlinePurified ring C)
    (hnot : ¬ (headlineGrantReady ring
        (headlinePhysicalNext ring C edge) ∨
      headlineGeneratedTarget ring
        (headlinePhysicalNext ring C edge))) :
    ((headlinePhysicalNext ring C edge) root).grant = false := by
  have hpost := headlineStagesPurifiedStep ring hn C edge hp
  exact (grantBlockG18PendingRootlessGrantless ring
    (headlinePhysicalNext ring C edge) hpost hnot).2 root

/-- The exact first-GRANT SafeWord failure is an
actual G18 target on its witnessing POST step. -/
theorem grantBlockG18FirstGrantFailureReady {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n)
    (hp : headlinePurified ring C)
    (root : Fin n) (word : List (Fin n))
    (h : GrantBlockFirstGrantFailure ring root C word) :
    ∃ pre : List (Fin n), ∃ edge : Fin n,
      ∃ suffix : List (Fin n),
        word = pre ++ edge :: suffix ∧
        (headlineGrantReady ring
            (headlinePhysicalNext ring
              (Counter.Word ring pre C) edge) ∨
         headlineGeneratedTarget ring
            (headlinePhysicalNext ring
              (Counter.Word ring pre C) edge)) := by
  obtain ⟨pre, edge, suffix, hword, _, hgrant⟩ := h
  refine ⟨pre, edge, suffix, hword, ?_⟩
  exact grantBlockG18MigratedGrantReady ring hn
    (Counter.Word ring pre C) edge root
    (grantBlockMarginalPurifiedWord ring hn pre C hp) hgrant

/-- The remaining candidate 'veto without a G18 hit' can
neither have a native leader nor a grant at the POST cut.
Thus the token-sink veto row with finalX.l = true is
credited by G18; the unresolved case is BANK success with
both POST flags false, not an unprotected native leader. -/
theorem grantBlockG18FirstBankFailureClassification {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n)
    (hp : headlinePurified ring C)
    (root : Fin n) (word : List (Fin n))
    (h : GrantBlockFirstBankFailure ring root C word) :
    ∃ pre : List (Fin n), ∃ edge : Fin n,
      ∃ suffix : List (Fin n),
        word = pre ++ edge :: suffix ∧
        ((headlineGrantReady ring
            (headlinePhysicalNext ring
              (Counter.Word ring pre C) edge) ∨
          headlineGeneratedTarget ring
            (headlinePhysicalNext ring
              (Counter.Word ring pre C) edge)) ∨
         (((headlinePhysicalNext ring
              (Counter.Word ring pre C) edge) root).l = false ∧
          ((headlinePhysicalNext ring
              (Counter.Word ring pre C) edge) root).grant = false)) := by
  obtain ⟨pre, edge, suffix, hword, _, _⟩ := h
  refine ⟨pre, edge, suffix, hword, ?_⟩
  by_cases ht :
      headlineGrantReady ring
          (headlinePhysicalNext ring
            (Counter.Word ring pre C) edge) ∨
        headlineGeneratedTarget ring
          (headlinePhysicalNext ring
            (Counter.Word ring pre C) edge)
  · exact Or.inl ht
  · have hpre : headlinePurified ring
        (Counter.Word ring pre C) :=
      grantBlockMarginalPurifiedWord ring hn pre C hp
    have hpost := headlineStagesPurifiedStep ring hn
      (Counter.Word ring pre C) edge hpre
    have hnone := grantBlockG18PendingRootlessGrantless ring
      (headlinePhysicalNext ring
        (Counter.Word ring pre C) edge) hpost ht
    exact Or.inr ⟨hnone.1 root, hnone.2 root⟩

/-- The earlier same-OLD-agent BANK-success/leader-sink row.
The sink has finalX.l = true, so it cannot be a pretarget
physical step with an unprotected leader on a purified path.
This is the literal T1/T2 row, not a fabricated G18 state. -/
theorem grantBlockG18VetoRowCertificate (c : Compiled) :
    bankSuccess
      (bankCell (grantBlockNativeVetoRoot c) 0)
      (bankCell (grantBlockNativeVetoDigit c) 1)
      1 c.b = true ∧
    (tokenStep
      (grantBlockNativeVetoRoot c)
      (grantBlockNativeVetoDigit c)
      firedNative firedNative none false true).1.grant =
        false ∧
    firedNative.l = true := by
  exact ⟨(grantBlockNativeVetoSamePair c).1,
    (grantBlockNativeVetoSamePair c).2, rfl⟩

/-- The literal native T2 GRANT transfer survives:
OLD source GrantFree alone does NOT imply future GrantFree.
At any purified real POST cut this migrated grant is handled
by grantBlockG18MigratedGrantReady, not counted as a loss. -/
theorem grantBlockG18MigrationRowCertificate (c : Compiled) :
    (Agent.blank c).grant = false ∧
    (tokenStep
      (Agent.blank c)
      { Agent.blank c with grant := true }
      ({ l := false, b := 0, sh := false, sg := false } :
        CertNative)
      ({ l := false, b := 0, sh := false, sg := false } :
        CertNative)
      none false false).1.grant = true := by
  exact ⟨rfl, grantBlockIncomingGrantTransferPossible c⟩

/-- At a G18 pretarget cut, no OLD grant exists anywhere.
Hence the literal FIRE selector cannot consume a BANK producer's
new grant on this service. -/
theorem grantBlockNoFireWithoutOldGrants {c : Compiled}
    (x y : Agent c) (eX eY : CertNative)
    (hx : x.grant = false) (hy : y.grant = false) :
    fireSelect x y eX eY = none := by
  cases hreqX : x.req <;>
    cases hreqY : y.req <;>
    simp [fireSelect, hx, hy, hreqX, hreqY]

/-- Exact no-FIRE T2 producer row, with arbitrary OLD private
scratch and DCC request. If both final native leader bits are
false, BANK success puts a grant on x. This complements the
finalX.l=true sink-veto row, but is a token-owner statement;
the full Protocol.transition field projection is not assumed. -/
theorem grantBlockTokenBankProducesGrant {c : Compiled}
    (x y : Agent c) (finalX finalY : CertNative)
    (dccRequest : Bool)
    (hx : x.grant = false) (hy : y.grant = false)
    (hfx : finalX.l = false) (hfy : finalY.l = false) :
    (tokenStep x y finalX finalY none
      dccRequest true).1.grant = true := by
  cases hreqX : x.req <;>
    cases hreqY : y.req <;>
    cases dccRequest <;>
    simp [tokenStep, hx, hy, hfx, hfy,
      hreqX, hreqY] <;>
    (repeat' split) <;> simp

/-- Safe physical OLD root BANK success is a frozen hit on the
same edge. Unlike bankTrialRenewalFrozenFirstPhysicalSuccess,
this version only needs the carrier's Complete+GrantFree and
the physical SafeWord certificate, not an initial CLEAN. -/
private theorem grantBlockMarginalGrantFreeEnd {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n))
      (C : Counter.Config q n),
      Counter.GrantFreeWord ring root C word →
      Counter.GrantFree (Counter.Word ring word C) root := by
  intro word
  induction word with
  | nil =>
      intro C h
      exact h
  | cons edge tail ih =>
      intro C h
      exact ih ((protocol q).step ring C edge) h.2

theorem grantBlockFirstPhysicalBankToFrozen
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (W : Nat) (word : List (Fin n))
    (hbank : GrantBlockFirstBankFailure ring member.1
      member.2.val (word.take W)) :
    grantBlockFrozenProxyHit ring member (word.take W) = true := by
  obtain ⟨pre, edge, suffix, hword, hsafe, hwin⟩ := hbank
  have hstart :
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val).success = false := rfl
  have hcouple :=
    GrantBankReference.bankLocalReferenceNoSuccessWordCouplingClamped
      ring member.1 hsp pre member.2.val
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)
      member.2.property.1 hsafe.1 hsafe.2.1
      (GrantBankReference.bankLocalReferenceStartAgrees
        ring member.2.val member.1)
      hstart hsafe.2.2
  have hfree :
      Counter.GrantFree
        (Counter.Word ring pre member.2.val) member.1 :=
    grantBlockMarginalGrantFreeEnd ring member.1 pre
      member.2.val hsafe.1
  have hstep :=
    GrantBankReference.bankLocalReferenceLatchStepMatchesRealClamped
      ring (Counter.Word ring pre member.2.val)
      member.1 edge
      (GrantBankReference.bankLocalReferenceWordClamped ring member.1
        pre (GrantBankReference.bankLocalReferenceStart
          ring member.1 member.2.val))
      hcouple.2.1 hfree hcouple.1 hcouple.2.2
  have hlocal :
      grantBlockFrozenProxyHit ring member (pre ++ [edge]) =
        true := by
    unfold grantBlockFrozenProxyHit
    rw [GrantBankReference.bankLocalReferenceWordLocalityClamped
      ring member.1 (pre ++ [edge])
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)]
    rw [GrantBankReference.bankLocalReferenceWordAppendClamped
      ring member.1 pre [edge]
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)]
    change
      (GrantBankReference.bankLocalReferenceStepClamped
        ring member.1
        (GrantBankReference.bankLocalReferenceWordClamped
          ring member.1 pre
          (GrantBankReference.bankLocalReferenceStart
            ring member.1 member.2.val)) edge).success = true
    exact hstep.trans hwin
  rw [hword]
  have hprefix := grantBlockFrozenProxyHitPrefix
    ring member (pre ++ [edge]) suffix hlocal
  simpa only [List.append_assoc, List.singleton_append]
    using hprefix

/-- True certified first physical BANK success has original
uniform-scheduler numerator at most the frozen-hit numerator.
This exact inclusion is useful, but it is NOT the G13 cold
proxy mass lower bound, whose CLEAN suffix uses a different
renewal scanner and whose initial carrier need not be CLEAN. -/
noncomputable def grantBlockFirstPhysicalBankMass
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if GrantBlockFirstBankFailure
        ring member.1 member.2.val (word.take W)
      then 1 else 0)

theorem grantBlockFirstPhysicalBankMassLeFrozen
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) :
    grantBlockFirstPhysicalBankMass ring member T W ≤
      grantBlockFrozenProxyMass ring member T W := by
  unfold grantBlockFirstPhysicalBankMass
    grantBlockFrozenProxyMass
  apply Density.schedule_sum_mono T
  intro word
  by_cases hb : GrantBlockFirstBankFailure
      ring member.1 member.2.val (word.take W)
  · have hf := grantBlockFirstPhysicalBankToFrozen
      ring hsp member W word hb
    simp [hb, hf]
  · simp [hb]

/-- Physical-only cold proxy mass means: the stopped global proxy
reports success, but the ONE frozen latch started at the original
carrier has not succeeded; no first physical supported defect is
available to charge to G14.  This is the reverse comparison error.
It must NOT be confused with the earlier frozen-only nondefect loss. -/
def GrantBlockPhysicalOnlyNondefect
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n)) : Prop :=
  grantBlockFamilyProxyHit ring hsp member T W word = true ∧
  grantBlockFrozenProxyHit ring member (word.take W) = false ∧
  ¬ GrantBlockFirstDefectFailure
    ring member.1 member.2.val (word.take W)

noncomputable def grantBlockPhysicalOnlyNondefectMass
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if GrantBlockPhysicalOnlyNondefect
       ring hsp member T W word then 1 else 0)

/-- An actual safe-prefix first BANK success cannot belong to
the physical-only residual, by the proved one-word coupling. -/
theorem grantBlockPhysicalOnlyNoCertifiedBank
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n))
    (h : GrantBlockPhysicalOnlyNondefect
      ring hsp member T W word) :
    ¬ GrantBlockFirstBankFailure
      ring member.1 member.2.val (word.take W) := by
  intro hb
  have hf := grantBlockFirstPhysicalBankToFrozen
    ring hsp member W word hb
  rw [h.2.1] at hf
  cases hf

/-- The exact surviving first-failure cases of a physical-only
proxy hit: first actual GRANT (hence G18 target on a purified
path) or physical SafeWord through the entire W-prefix.
The OLD defect case is excluded by definition; the OLD BANK
case would force a frozen latch and is also excluded. -/
theorem grantBlockPhysicalOnlyFirstGrantOrSafe
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n))
    (h : GrantBlockPhysicalOnlyNondefect
      ring hsp member T W word) :
    GrantBlockFirstGrantFailure ring member.1
        member.2.val (word.take W) ∨
    GrantBankReference.bankLocalReferenceSafeWord
        ring member.1 member.2.val (word.take W) := by
  by_cases hs : GrantBankReference.bankLocalReferenceSafeWord
      ring member.1 member.2.val (word.take W)
  · exact Or.inr hs
  · have hfirst := grantBlockSafeWordFirstFailure
      ring member.1 (word.take W) member.2.val
      member.2.property.2 hs
    rcases grantBlockSafeFirstFailureCases
        ring member.1 member.2.val (word.take W)
        hfirst with hg | hd | hb
    · exact Or.inl hg
    · exact False.elim (h.2.2 hd)
    · exact False.elim
        ((grantBlockPhysicalOnlyNoCertifiedBank
          ring hsp member T W word h) hb)

/-- In the second case there has been NO actual OLD root BANK
success in any prefix through W. The CLEAN remaining-window
renewal scanner can still be positive; no merged theorem says
that such a positive surrogate requires an authentic BANK hit. -/
theorem grantBlockPhysicalOnlySafeBeforeBank
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (W : Nat) (word : List (Fin n))
    (hs : GrantBankReference.bankLocalReferenceSafeWord
      ring member.1 member.2.val (word.take W)) :
    GrantBankReference.bankLocalReferenceNoRootSuccessWord
      ring member.1 member.2.val (word.take W) :=
  hs.2.2

/-- Under G18 purified entry, the first GRANT residual already
hit the physical target; only the full-W SafeWord / CLEAN
surrogate mismatch can remain before the first G18 target. -/
theorem grantBlockPhysicalOnlyG18OrSafe
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (hp : headlinePurified ring member.2.val)
    (T W : Nat) (word : List (Fin n))
    (h : GrantBlockPhysicalOnlyNondefect
      ring hsp member T W word) :
    (∃ pre : List (Fin n), ∃ edge : Fin n,
      ∃ suffix : List (Fin n),
        word.take W = pre ++ edge :: suffix ∧
        (headlineGrantReady ring
            (headlinePhysicalNext ring
              (Counter.Word ring pre member.2.val) edge) ∨
         headlineGeneratedTarget ring
            (headlinePhysicalNext ring
              (Counter.Word ring pre member.2.val) edge))) ∨
    (GrantBankReference.bankLocalReferenceSafeWord
       ring member.1 member.2.val (word.take W) ∧
     GrantBankReference.bankLocalReferenceNoRootSuccessWord
       ring member.1 member.2.val (word.take W)) := by
  rcases grantBlockPhysicalOnlyFirstGrantOrSafe
      ring hsp member T W word h with hg | hs
  · exact Or.inl
      (grantBlockG18FirstGrantFailureReady
        ring hn member.2.val hp member.1
        (word.take W) hg)
  · exact Or.inr ⟨hs,
      grantBlockPhysicalOnlySafeBeforeBank
        ring member W word hs⟩

/-- Original-scheduler additivity using only core finite-word sums.
Private predecessor lemmas are not visible across modules. -/
private theorem grantBlockMarginalScheduleAdd
    (n T : Nat) (f g : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun word => f word + g word) =
      Prob.scheduleSum n T f + Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T
      (fun word => f word + g word) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum,
      ← FixedSpanRenewalPayload.rawWord_sum,
      ← FixedSpanRenewalPayload.rawWord_sum]
  exact ofFn_sum_add _ _

/-- EXACT physical-to-frozen word count: every physical proxy hit
is either a frozen hit, a first physical supported OLD defect,
or the specifically named physical-only nondefect surrogate.
This is the inclusion required by the direction of G13. -/
theorem grantBlockPhysicalProxyToFrozenClassified
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) :
    bankTrialRenewalColdProxyMass
       ring member.1 hsp member.2 T W ≤
    grantBlockFrozenProxyMass ring member T W +
      (grantBlockFirstDefectFailureMass ring member T W +
       grantBlockPhysicalOnlyNondefectMass
         ring hsp member T W) := by
  classical
  have hpoint (word : List (Fin n)) :
      (if grantBlockFamilyProxyHit
          ring hsp member T W word then 1 else 0) ≤
      (if grantBlockFrozenProxyHit
          ring member (word.take W) then 1 else 0) +
      ((if GrantBlockFirstDefectFailure
          ring member.1 member.2.val (word.take W)
        then 1 else 0) +
       (if GrantBlockPhysicalOnlyNondefect
          ring hsp member T W word then 1 else 0)) := by
    cases hp : grantBlockFamilyProxyHit
        ring hsp member T W word with
    | false =>
        change (0 : Nat) ≤ _
        exact Nat.zero_le _
    | true =>
        change (1 : Nat) ≤ _
        cases hf : grantBlockFrozenProxyHit
            ring member (word.take W) with
        | true =>
            have hone :
                (if grantBlockFrozenProxyHit
                  ring member (word.take W) then
                    (1 : Nat) else 0) = 1 := by
              simp [hf]
            rw [if_pos rfl]
            omega
        | false =>
            by_cases hd : GrantBlockFirstDefectFailure
                ring member.1 member.2.val (word.take W)
            · have hone :
                  (if GrantBlockFirstDefectFailure
                    ring member.1 member.2.val (word.take W)
                    then (1 : Nat) else 0) = 1 := by
                    simp [hd]
              rw [hone]
              omega
            · have hr : GrantBlockPhysicalOnlyNondefect
                  ring hsp member T W word :=
                ⟨hp, hf, hd⟩
              have hone :
                  (if GrantBlockPhysicalOnlyNondefect
                    ring hsp member T W word then
                    (1 : Nat) else 0) = 1 := by
                  simp [hr]
              rw [hone]
              omega
  have hsum := Density.schedule_sum_mono T
    (fun word =>
      if grantBlockFamilyProxyHit
        ring hsp member T W word then 1 else 0)
    (fun word =>
      (if grantBlockFrozenProxyHit
        ring member (word.take W) then 1 else 0) +
      ((if GrantBlockFirstDefectFailure
          ring member.1 member.2.val (word.take W)
        then 1 else 0) +
       (if GrantBlockPhysicalOnlyNondefect
          ring hsp member T W word then 1 else 0)))
    hpoint
  rw [grantBlockMarginalScheduleAdd] at hsum
  rw [grantBlockMarginalScheduleAdd] at hsum
  change
    Prob.scheduleSum n T (fun word =>
      if grantBlockFamilyProxyHit
        ring hsp member T W word then 1 else 0) ≤
    grantBlockFrozenProxyMass ring member T W +
      (grantBlockFirstDefectFailureMass ring member T W +
       grantBlockPhysicalOnlyNondefectMass
         ring hsp member T W) at hsum
  rw [grantBlockFamilyProxyMassEq
    ring hsp member T W] at hsum
  exact hsum

/-- Integer accounting over opaque variables only. There are
TWO distinct G14 charges: the G13 cold .defect exit and the
first SafeWord supported OLD defect in the physical/frozen
comparison. Both are bounded by the SAME crossing budget.
No multiplication of compiler-sized powers occurs in omega. -/
private theorem grantBlockFrozenMarginalArithmetic
    (A B G D N P ECold EFirst F X : Nat)
    (hbase : A * N ≤ B * (P + ECold))
    (htransfer : P ≤ F + EFirst + X)
    (hcold : G * ECold ≤ D * N)
    (hfirst : G * EFirst ≤ D * N) :
    (G * A - 2 * B * D) * N ≤ B * G * (F + X) := by
  have hcover :
      A * N ≤ B * (F + EFirst + X + ECold) := by
    calc
      A * N ≤ B * (P + ECold) := hbase
      _ ≤ B * ((F + EFirst + X) + ECold) :=
        Nat.mul_le_mul_left B
          (Nat.add_le_add_right htransfer ECold)
  have hscaled := Nat.mul_le_mul_left G hcover
  have hfirstScaled := Nat.mul_le_mul_left B hfirst
  have hcoldScaled := Nat.mul_le_mul_left B hcold
  have hexpand :
      G * (B * (F + EFirst + X + ECold)) =
        B * G * (F + X) + B * (G * EFirst) +
          B * (G * ECold) := by
    simp only [Nat.mul_add, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm]
    omega
  have htwice :
      B * (D * N) + B * (D * N) =
        (2 * B * D) * N := by
    calc
      B * (D * N) + B * (D * N) =
          2 * (B * (D * N)) := by omega
      _ = (2 * B * D) * N := by
          simp only [Nat.mul_assoc,
            Nat.mul_comm, Nat.mul_left_comm]
  have htotal :
      (G * A) * N ≤
        B * G * (F + X) + (2 * B * D) * N := by
    calc
      (G * A) * N = G * (A * N) := by
        rw [Nat.mul_assoc]
      _ ≤ G * (B * (F + EFirst + X + ECold)) :=
        hscaled
      _ = B * G * (F + X) + B * (G * EFirst) +
            B * (G * ECold) := hexpand
      _ ≤ B * G * (F + X) + B * (D * N) +
            B * (D * N) := by
          omega
      _ = B * G * (F + X) + (2 * B * D) * N := by
          rw [Nat.add_assoc, htwice]
  by_cases hsmall : 2 * B * D ≤ G * A
  · have hsub :
        (G * A - 2 * B * D) + 2 * B * D =
          G * A := Nat.sub_add_cancel hsmall
    have hscaledSub :=
      congrArg (fun k : Nat => k * N) hsub
    rw [Nat.add_mul] at hscaledSub
    omega
  · have hzero : G * A - 2 * B * D = 0 := by omega
    rw [hzero, Nat.zero_mul]
    exact Nat.zero_le _

/-- Strongest G13-to-frozen marginal transfer proved by the
merged APIs, with no invented simulation leaf. It has exactly
the original G13 cold .defect G14 charge, ONE further G14
charge for first physical SafeWord defect, and the exposed
non-defect physical-only CLEAN/renewal mismatch mass.

If the last mass were bounded separately, this would produce
the desired numerical frozen marginal. It is NOT currently zero
or G14-controlled by any imported theorem. -/
theorem grantBlockFrozenProxyMassLower
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (member : GrantBlockFamilyMember ring)
    (R L T W radius : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hWT : W ≤ T)
    (hbudget :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T)
    (hBuffered : HeadlineGrantBufferedCounter
      ring member.2.val radius member.1)
    (hcrossWindow : W ≤ radius * n / 8) :
    ((8 ^ radius) * (51279921 * W) -
      2 * grantBlockFamilyScale n *
        (Density.N (badSet ring member.2.val) * 3 ^ radius)) *
      n ^ T ≤
    grantBlockFamilyScale n * (8 ^ radius) *
      (grantBlockFrozenProxyMass ring member T W +
       grantBlockPhysicalOnlyNondefectMass
         ring hsp member T W) := by
  have hbase :
      (51279921 * W) * n ^ T ≤
      grantBlockFamilyScale n *
        (bankTrialRenewalColdProxyMass
          ring member.1 hsp member.2 T W +
         bankTrialRenewalColdDefectMass
          ring member.1 hsp member.2 T W) := by
    unfold grantBlockFamilyScale
    exact bankTrialRenewalColdSuccessMassLower
      ring member.1 hn hsp hw hlarge member.2
      R L T W hradius hW hL hWT hbudget
  have htransfer := grantBlockPhysicalProxyToFrozenClassified
    ring hsp member T W
  have hcold := bankTrialRenewalColdDefectCrossingBound
    hn ring member.1 hsp member.2 radius W T
    hBuffered hWT hcrossWindow
  have hfirst := grantBlockFirstDefectFailureMassBound
    (by omega : 2 ≤ n)
    ring member radius W T hBuffered hWT hcrossWindow
  exact grantBlockFrozenMarginalArithmetic
    (51279921 * W)
    (grantBlockFamilyScale n)
    (8 ^ radius)
    (Density.N (badSet ring member.2.val) * 3 ^ radius)
    (n ^ T)
    (bankTrialRenewalColdProxyMass
      ring member.1 hsp member.2 T W)
    (bankTrialRenewalColdDefectMass
      ring member.1 hsp member.2 T W)
    (grantBlockFirstDefectFailureMass ring member T W)
    (grantBlockFrozenProxyMass ring member T W)
    (grantBlockPhysicalOnlyNondefectMass
      ring hsp member T W)
    hbase (by rw [Nat.add_assoc]; exact htransfer) hcold hfirst

end L3

#print axioms L3.grantBlockG18VetoLeaderReady
#print axioms L3.grantBlockG18MigratedGrantReady
#print axioms L3.grantBlockG18FirstBankFailureClassification
#print axioms L3.grantBlockFirstPhysicalBankMassLeFrozen
#print axioms L3.grantBlockPhysicalOnlyG18OrSafe
#print axioms L3.grantBlockPhysicalProxyToFrozenClassified
#print axioms L3.grantBlockFrozenProxyMassLower


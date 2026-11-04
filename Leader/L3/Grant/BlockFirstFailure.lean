import Leader.L3.Grant.BlockNegCorr

/-!
First failing SafeWord clause for the frozen support proxy.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
set_option autoImplicit false
set_option Elab.async false

theorem grantBlockSafeWordNil
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Counter.Config q n)
    (hg : Counter.GrantFree C root) :
    GrantBankReference.bankLocalReferenceSafeWord
      ring root C [] := by
  change Counter.GrantFree C root ∧ True ∧ True
  exact ⟨hg, True.intro, True.intro⟩

theorem grantBlockSafeWordConsIff
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Counter.Config q n)
    (edge : Fin n) (tail : List (Fin n)) :
    GrantBankReference.bankLocalReferenceSafeWord
      ring root C (edge :: tail) ↔
    Counter.GrantFree C root ∧
    ¬ Counter.ResetClockBankDefectEntry ring C root edge ∧
    GrantBankReference.bankLocalReferenceRealSuccessEvent
      ring root C edge = false ∧
    GrantBankReference.bankLocalReferenceSafeWord
      ring root ((protocol q).step ring C edge) tail := by
  change
    (Counter.GrantFree C root ∧
      Counter.GrantFreeWord ring root
        ((protocol q).step ring C edge) tail) ∧
    (¬ Counter.ResetClockBankDefectEntry ring C root edge ∧
      HeadlineGrantClock.NoSupportedDefectWord
        ring root ((protocol q).step ring C edge) tail) ∧
    (GrantBankReference.bankLocalReferenceRealSuccessEvent
        ring root C edge = false ∧
      GrantBankReference.bankLocalReferenceNoRootSuccessWord
        ring root ((protocol q).step ring C edge) tail) ↔
    (Counter.GrantFree C root ∧
      ¬ Counter.ResetClockBankDefectEntry ring C root edge ∧
      GrantBankReference.bankLocalReferenceRealSuccessEvent
        ring root C edge = false ∧
      GrantBankReference.bankLocalReferenceSafeWord
        ring root ((protocol q).step ring C edge) tail)
  constructor
  · rintro ⟨⟨hg, hgt⟩, ⟨hd, hdt⟩, ⟨hb, hbt⟩⟩
    exact ⟨hg, hd, hb, ⟨hgt, hdt, hbt⟩⟩
  · rintro ⟨hg, hd, hb, ⟨hgt, hdt, hbt⟩⟩
    exact ⟨⟨hg, hgt⟩, ⟨hd, hdt⟩, ⟨hb, hbt⟩⟩

/-- A genuinely FIRST failure, with a SafeWord proper prefix.
The three failing clauses are: successor grant, supported OLD
defect, and OLD root BANK success. No cold-stop conclusion is
silently attached to the BANK success clause. -/
def GrantBlockSafeFirstFailure
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Counter.Config q n)
    (word : List (Fin n)) : Prop :=
  ∃ pre : List (Fin n), ∃ edge : Fin n,
    ∃ suffix : List (Fin n),
      word = pre ++ edge :: suffix ∧
      GrantBankReference.bankLocalReferenceSafeWord
        ring root C pre ∧
      (¬ Counter.GrantFree
        ((protocol q).step ring
          (Counter.Word ring pre C) edge) root ∨
       Counter.ResetClockBankDefectEntry ring
         (Counter.Word ring pre C) root edge ∨
       GrantBankReference.bankLocalReferenceRealSuccessEvent
         ring root (Counter.Word ring pre C) edge = true)

theorem grantBlockSafeWordFirstFailure
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) :
    ∀ (word : List (Fin n)) (C : Counter.Config q n),
      Counter.GrantFree C root →
      ¬ GrantBankReference.bankLocalReferenceSafeWord
        ring root C word →
      GrantBlockSafeFirstFailure ring root C word := by
  intro word
  induction word with
  | nil =>
      intro C hg hb
      exact False.elim
        (hb (grantBlockSafeWordNil ring root C hg))
  | cons edge tail ih =>
      intro C hg hb
      by_cases hd :
          Counter.ResetClockBankDefectEntry ring C root edge
      · exact ⟨[], edge, tail, rfl,
          grantBlockSafeWordNil ring root C hg,
          Or.inr (Or.inl hd)⟩
      · by_cases hs :
          GrantBankReference.bankLocalReferenceRealSuccessEvent
            ring root C edge = true
        · exact ⟨[], edge, tail, rfl,
            grantBlockSafeWordNil ring root C hg,
            Or.inr (Or.inr hs)⟩
        · have hfalse :
            GrantBankReference.bankLocalReferenceRealSuccessEvent
              ring root C edge = false := by
            cases he :
                GrantBankReference.bankLocalReferenceRealSuccessEvent
                  ring root C edge with
            | false => rfl
            | true => exact False.elim (hs he)
          by_cases hgrant :
              Counter.GrantFree
                ((protocol q).step ring C edge) root
          · have htail :
                ¬ GrantBankReference.bankLocalReferenceSafeWord
                  ring root ((protocol q).step ring C edge) tail := by
              intro hsafe
              exact hb ((grantBlockSafeWordConsIff
                ring root C edge tail).2
                ⟨hg, hd, hfalse, hsafe⟩)
            obtain ⟨pre, last, suffix, hword, hsafe, hwhy⟩ :=
              ih ((protocol q).step ring C edge) hgrant htail
            refine ⟨edge :: pre, last, suffix, ?_, ?_, ?_⟩
            · rw [hword]
              rfl
            · exact (grantBlockSafeWordConsIff
                ring root C edge pre).2
                  ⟨hg, hd, hfalse, hsafe⟩
            · exact hwhy
          · exact ⟨[], edge, tail, rfl,
              grantBlockSafeWordNil ring root C hg,
              Or.inl hgrant⟩

theorem grantBlockRealAfterEqWord
    {n q : Nat} (ring : DirectedRing n) :
    ∀ (word : List (Fin n)) (C : Counter.Config q n),
      densityRealAfter ring C word = Counter.Word ring word C := by
  intro word
  induction word with
  | nil =>
      intro C
      rfl
  | cons edge tail ih =>
      intro C
      change
        densityRealAfter ring
          ((protocol q).step ring C edge) tail =
        Counter.Word ring tail
          ((protocol q).step ring C edge)
      exact ih _

theorem grantBlockFirstDefectCrossing
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Counter.Config q n)
    (word pre suffix : List (Fin n)) (edge : Fin n)
    (hword : word = pre ++ edge :: suffix)
    (hd : Counter.ResetClockBankDefectEntry ring
      (Counter.Word ring pre C) root edge) :
    DefectCrossingEntryWithin ring C root word := by
  refine ⟨pre, edge, suffix, hword, ?_⟩
  rw [grantBlockRealAfterEqWord ring pre C]
  exact hd

/-- OLD BANK success is a local BANK row, independent of the
native leader sink that later controls grant production. -/
theorem grantBlockLiteralBankSuccessRow (b : Nat) :
    bankSuccess
      ({ role := 0, mode := .CWAIT, bit := false,
         tok := .E, lease := 0, grant := false } : BankCell)
      ({ role := 1, mode := .RESET, bit := false,
         tok := .CL1, lease := 0, grant := false } : BankCell)
      1 b = true := by
  rfl

/-- The literal T1/final sink vetoes T2 BANK-grant production.
The relevant source row is Base.lean tokenStep:
if bankSuccessX && !finalX.l && !grantConsumedX then gx := true;
the final if finalX.l then gx := false is decisive as well. -/
theorem grantBlockTokenLeaderSinkVeto (c : Compiled) :
    (tokenStep (Agent.blank c) (Agent.blank c)
      firedNative firedNative none false true).1.grant =
        false := by
  rfl

/-- One literal OLD root with a private BANK success poised, but
already a final native leader. ColdCarrier does not constrain l. -/
def grantBlockNativeVetoRoot (c : Compiled) : Agent c :=
  { Agent.blank c with l := true, mode := .CWAIT }

def grantBlockNativeVetoDigit (c : Compiled) : Agent c :=
  { Agent.blank c with
    pack := ⟨1, by omega⟩, tok := .CL1 }

/-- The SAME two OLD Agent records give BANK success and no
new root grant under the T1 native leader sink. This directly
refutes the attempted inference from BANK latch to physical grant
even before any stochastic mass calculation. -/
theorem grantBlockNativeVetoSamePair (c : Compiled) :
    bankSuccess
      (bankCell (grantBlockNativeVetoRoot c) 0)
      (bankCell (grantBlockNativeVetoDigit c) 1)
      1 c.b = true ∧
    (tokenStep
      (grantBlockNativeVetoRoot c)
      (grantBlockNativeVetoDigit c)
      firedNative firedNative none false true).1.grant =
        false := by
  exact ⟨rfl, rfl⟩

theorem grantBlockFrozenSingleLetterFirstHit
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (edge : Fin n)
    (hbank :
      GrantBankReference.bankLocalReferenceRealSuccessEvent
        ring member.1 member.2.val edge = true) :
    GrantBlockFrozenSafeFirstHit ring member 1 [edge] := by
  have hstep :=
    GrantBankReference.bankLocalReferenceLatchStepMatchesRealClamped
      ring member.2.val member.1 edge
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)
      member.2.property.1 member.2.property.2
      (GrantBankReference.bankLocalReferenceStartAgrees
        ring member.2.val member.1) rfl
  have hhit : grantBlockFrozenProxyHit
      ring member [edge] = true := by
    unfold grantBlockFrozenProxyHit
    rw [GrantBankReference.bankLocalReferenceWordLocalityClamped
      ring member.1 [edge]
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)]
    change
      (GrantBankReference.bankLocalReferenceStepClamped
        ring member.1
        (GrantBankReference.bankLocalReferenceStart
          ring member.1 member.2.val) edge).success = true
    exact hstep.trans hbank
  refine ⟨[], edge, [], rfl,
    grantBlockSafeWordNil ring member.1 member.2.val
      member.2.property.2, ?_, hhit⟩
  unfold grantBlockFrozenProxyHit
  rfl

/-- Exact length-one physical cold-window failure: a real BANK
success may leave the root grant-free but reset. The cold observer
then enters recovery (not a CLEAN/GRANT terminal) and its
stopped proxy returns zero at W = T = 1. -/
theorem grantBlockColdProxyOneLetterNoStop
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (edge : Fin n)
    (hmode : (member.2.val member.1).mode ≠ .RESET)
    (hdefect : ¬ Counter.ResetClockBankDefectEntry
      ring member.2.val member.1 edge)
    (hgrant : Counter.GrantFree
      ((protocol (ceilLogTwo n)).step ring
        member.2.val edge) member.1)
    (hreset :
      (((protocol (ceilLogTwo n)).step ring
        member.2.val edge) member.1).mode = .RESET) :
    grantBlockFamilyProxyHit ring hsp member 1 1 [edge] =
      false := by
  have hcomplete := Counter.resetClockBankColdCompleteStep
    ring member.1 member.2 edge hdefect
  have hnext :
      Counter.resetClockBankColdNext ring member.1 hsp
        (.inl member.2) edge =
      .inr (.inl (.inr
        ⟨((protocol (ceilLogTwo n)).step ring member.2.val edge),
          ⟨hcomplete, hgrant, hreset⟩⟩)) := by
    rw [Counter.resetClockBankColdNextContinue
      ring member.1 hsp member.2 edge hdefect hgrant]
    exact Counter.resetClockBankColdLiftReset ring member.1
      ((protocol (ceilLogTwo n)).step ring member.2.val edge)
      hcomplete hgrant hreset
  unfold grantBlockFamilyProxyHit grantBlockFamilyProxyWord
  rw [bankTrialRenewalColdStartNonReset
    ring member.1 member.2 hmode]
  simp [bankTrialSuccessNatStoppedWord,
    bankTrialRenewalColdStop, hnext]

/-- An explicit conditional ONE-LETTER obstruction to the
unconditional hbridge. None of these hypotheses is an axiom:
they describe testable OLD BANK and genuine post-Protocol rows.
The native leader sink supplies the concrete mechanism for
hgrant while BANK success is true. -/
theorem grantBlockFrozenBridgeSingleEdgeObstruction
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (edge : Fin n)
    (hbank :
      GrantBankReference.bankLocalReferenceRealSuccessEvent
        ring member.1 member.2.val edge = true)
    (hmode : (member.2.val member.1).mode ≠ .RESET)
    (hdefect : ¬ Counter.ResetClockBankDefectEntry
      ring member.2.val member.1 edge)
    (hgrant : Counter.GrantFree
      ((protocol (ceilLogTwo n)).step ring
        member.2.val edge) member.1)
    (hreset :
      (((protocol (ceilLogTwo n)).step ring
        member.2.val edge) member.1).mode = .RESET) :
    GrantBlockFrozenSafeFirstHit ring member 1 [edge] ∧
    grantBlockFamilyProxyHit ring hsp member 1 1 [edge] =
      false := by
  exact ⟨grantBlockFrozenSingleLetterFirstHit
      ring member edge hbank,
    grantBlockColdProxyOneLetterNoStop
      ring hsp member edge hmode hdefect hgrant hreset⟩

def GrantBlockFirstGrantFailure
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Counter.Config q n)
    (word : List (Fin n)) : Prop :=
  ∃ pre : List (Fin n), ∃ edge : Fin n,
    ∃ suffix : List (Fin n),
      word = pre ++ edge :: suffix ∧
      GrantBankReference.bankLocalReferenceSafeWord
        ring root C pre ∧
      ¬ Counter.GrantFree
        ((protocol q).step ring (Counter.Word ring pre C) edge)
        root

def GrantBlockFirstDefectFailure
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Counter.Config q n)
    (word : List (Fin n)) : Prop :=
  ∃ pre : List (Fin n), ∃ edge : Fin n,
    ∃ suffix : List (Fin n),
      word = pre ++ edge :: suffix ∧
      GrantBankReference.bankLocalReferenceSafeWord
        ring root C pre ∧
      Counter.ResetClockBankDefectEntry ring
        (Counter.Word ring pre C) root edge

def GrantBlockFirstBankFailure
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Counter.Config q n)
    (word : List (Fin n)) : Prop :=
  ∃ pre : List (Fin n), ∃ edge : Fin n,
    ∃ suffix : List (Fin n),
      word = pre ++ edge :: suffix ∧
      GrantBankReference.bankLocalReferenceSafeWord
        ring root C pre ∧
      GrantBankReference.bankLocalReferenceRealSuccessEvent
        ring root (Counter.Word ring pre C) edge = true

theorem grantBlockSafeFirstFailureCases
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Counter.Config q n)
    (word : List (Fin n))
    (h : GrantBlockSafeFirstFailure ring root C word) :
    GrantBlockFirstGrantFailure ring root C word ∨
    GrantBlockFirstDefectFailure ring root C word ∨
    GrantBlockFirstBankFailure ring root C word := by
  obtain ⟨pre, edge, suffix, hw, hsafe, hwhy⟩ := h
  rcases hwhy with hg | hd | hb
  · exact Or.inl ⟨pre, edge, suffix, hw, hsafe, hg⟩
  · exact Or.inr (Or.inl
      ⟨pre, edge, suffix, hw, hsafe, hd⟩)
  · exact Or.inr (Or.inr
      ⟨pre, edge, suffix, hw, hsafe, hb⟩)

theorem grantBlockFrozenHitNotSafeWord
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (word : List (Fin n))
    (hhit : grantBlockFrozenProxyHit ring member word = true) :
    ¬ GrantBankReference.bankLocalReferenceSafeWord
      ring member.1 member.2.val word := by
  intro hsafe
  have hc :=
    GrantBankReference.bankLocalReferenceNoSuccessWordCouplingClamped
      ring member.1 hsp word member.2.val
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)
      member.2.property.1 hsafe.1 hsafe.2.1
      (GrantBankReference.bankLocalReferenceStartAgrees
        ring member.2.val member.1) rfl hsafe.2.2
  have hh := hhit
  unfold grantBlockFrozenProxyHit at hh
  rw [GrantBankReference.bankLocalReferenceWordLocalityClamped
    ring member.1 word
    (GrantBankReference.bankLocalReferenceStart
      ring member.1 member.2.val)] at hh
  rw [hc.2.2] at hh
  cases hh

theorem grantBlockFrozenHitFirstFailureCases
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (W : Nat) (word : List (Fin n))
    (hhit : grantBlockFrozenProxyHit
      ring member (word.take W) = true) :
    GrantBlockFirstGrantFailure
        ring member.1 member.2.val (word.take W) ∨
    GrantBlockFirstDefectFailure
        ring member.1 member.2.val (word.take W) ∨
    GrantBlockFirstBankFailure
        ring member.1 member.2.val (word.take W) := by
  have hnot := grantBlockFrozenHitNotSafeWord
    ring hsp member (word.take W) hhit
  have hfirst := grantBlockSafeWordFirstFailure
    ring member.1 (word.take W) member.2.val
    member.2.property.2 hnot
  exact grantBlockSafeFirstFailureCases
    ring member.1 member.2.val (word.take W) hfirst

theorem grantBlockFirstDefectFailureCrossing
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Counter.Config q n)
    (word : List (Fin n))
    (h : GrantBlockFirstDefectFailure ring root C word) :
    DefectCrossingEntryWithin ring C root word := by
  obtain ⟨pre, edge, suffix, hw, _, hd⟩ := h
  exact grantBlockFirstDefectCrossing
    ring root C word pre suffix edge hw hd

noncomputable def grantBlockFirstDefectFailureMass
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) : Nat := by
  classical
  exact Prob.scheduleSum n T (fun word =>
    if GrantBlockFirstDefectFailure ring member.1
      member.2.val (word.take W) then 1 else 0)

theorem grantBlockFirstDefectFailureMassBound
    {n : Nat} (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (radius W T : Nat)
    (hBuffered : HeadlineGrantBufferedCounter
      ring member.2.val radius member.1)
    (hWT : W ≤ T)
    (hwindow : W ≤ radius * n / 8) :
    8 ^ radius *
      grantBlockFirstDefectFailureMass ring member T W ≤
    Density.N (badSet ring member.2.val) *
      3 ^ radius * n ^ T := by
  classical
  have hpoint (word : List (Fin n)) :
      (if GrantBlockFirstDefectFailure ring member.1
          member.2.val (word.take W) then 1 else 0) ≤
      (if DefectCrossingEntryWithin ring member.2.val
          member.1 (word.take W) then 1 else 0) := by
    by_cases hd : GrantBlockFirstDefectFailure
        ring member.1 member.2.val (word.take W)
    · have hc := grantBlockFirstDefectFailureCrossing
        ring member.1 member.2.val (word.take W) hd
      simp [hd, hc]
    · simp [hd]
  have hm := Density.schedule_sum_mono T
    (fun word =>
      if GrantBlockFirstDefectFailure ring member.1
        member.2.val (word.take W) then 1 else 0)
    (fun word =>
      if DefectCrossingEntryWithin ring member.2.val
        member.1 (word.take W) then 1 else 0)
    hpoint
  change grantBlockFirstDefectFailureMass
      ring member T W ≤
    Prob.scheduleSum n T (fun word =>
      if DefectCrossingEntryWithin ring member.2.val
        member.1 (word.take W) then 1 else 0) at hm
  exact Nat.le_trans
    (Nat.mul_le_mul_left (8 ^ radius) hm)
    (defectCrossingMass hn ring member.2.val
      member.1 radius W T hBuffered hWT hwindow)

/-- An actual frozen-hit loss attributed to the first GRANT or
BANK clause, only when the physical cold proxy misses. The BANK
part cannot be erased: native token sinks may veto a BANK grant. -/
def GrantBlockNondefectLost
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n)) : Prop :=
  (GrantBlockFirstGrantFailure
      ring member.1 member.2.val (word.take W) ∨
   GrantBlockFirstBankFailure
      ring member.1 member.2.val (word.take W)) ∧
  grantBlockFamilyProxyHit ring hsp member T W word = false

noncomputable def grantBlockNondefectLostMass
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) : Nat := by
  classical
  exact Prob.scheduleSum n T (fun word =>
    if GrantBlockNondefectLost ring hsp member T W word
      then 1 else 0)

private theorem grantBlockDownstreamScheduleAdd
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

/-- The unconditional first-failure comparison actually justified
by the merged APIs. G14 pays the FIRST DEFECT component, but a
separate non-defect BANK/GRANT loss remains. No assumed leaf. -/
theorem grantBlockPhysicalProxyMassGeFrozenMinusClassified
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) :
    grantBlockFrozenProxyMass ring member T W -
      (grantBlockFirstDefectFailureMass ring member T W +
        grantBlockNondefectLostMass ring hsp member T W) ≤
    bankTrialRenewalColdProxyMass
      ring member.1 hsp member.2 T W := by
  classical
  have hpoint (word : List (Fin n)) :
      (if grantBlockFrozenProxyHit
          ring member (word.take W) then 1 else 0) ≤
      (if grantBlockFamilyProxyHit
          ring hsp member T W word then 1 else 0) +
      ((if GrantBlockFirstDefectFailure
          ring member.1 member.2.val (word.take W)
        then 1 else 0) +
       (if GrantBlockNondefectLost
          ring hsp member T W word then 1 else 0)) := by
    cases hf : grantBlockFrozenProxyHit
        ring member (word.take W) with
    | false =>
        change (0 : Nat) ≤ _
        exact Nat.zero_le _
    | true =>
        change (1 : Nat) ≤ _
        rcases grantBlockFrozenHitFirstFailureCases
            ring hsp member W word hf with hg | hd | hb
        · by_cases hp :
              grantBlockFamilyProxyHit
                ring hsp member T W word = true
          · have hphys :
                (if grantBlockFamilyProxyHit
                  ring hsp member T W word then (1 : Nat)
                  else 0) = 1 := by simp [hp]
            rw [hphys]
            omega
          · have hpf :
                grantBlockFamilyProxyHit
                  ring hsp member T W word = false := by
              cases hc :
                  grantBlockFamilyProxyHit
                    ring hsp member T W word with
              | false => rfl
              | true => exact False.elim (hp hc)
            have hn : GrantBlockNondefectLost
                ring hsp member T W word :=
              ⟨Or.inl hg, hpf⟩
            have hunit :
                (if GrantBlockNondefectLost
                  ring hsp member T W word then (1 : Nat)
                  else 0) = 1 := by simp [hn]
            rw [hunit]
            omega
        · have hunit :
              (if GrantBlockFirstDefectFailure
                ring member.1 member.2.val (word.take W)
                then (1 : Nat) else 0) = 1 := by simp [hd]
          rw [hunit]
          omega
        · by_cases hp :
              grantBlockFamilyProxyHit
                ring hsp member T W word = true
          · have hphys :
                (if grantBlockFamilyProxyHit
                  ring hsp member T W word then (1 : Nat)
                  else 0) = 1 := by simp [hp]
            rw [hphys]
            omega
          · have hpf :
                grantBlockFamilyProxyHit
                  ring hsp member T W word = false := by
              cases hc :
                  grantBlockFamilyProxyHit
                    ring hsp member T W word with
              | false => rfl
              | true => exact False.elim (hp hc)
            have hn : GrantBlockNondefectLost
                ring hsp member T W word :=
              ⟨Or.inr hb, hpf⟩
            have hunit :
                (if GrantBlockNondefectLost
                  ring hsp member T W word then (1 : Nat)
                  else 0) = 1 := by simp [hn]
            rw [hunit]
            omega
  have hsum := Density.schedule_sum_mono T
    (fun word =>
      if grantBlockFrozenProxyHit ring member (word.take W)
      then 1 else 0)
    (fun word =>
      (if grantBlockFamilyProxyHit
        ring hsp member T W word then 1 else 0) +
      ((if GrantBlockFirstDefectFailure ring member.1
          member.2.val (word.take W) then 1 else 0) +
       (if GrantBlockNondefectLost
          ring hsp member T W word then 1 else 0)))
    hpoint
  rw [grantBlockDownstreamScheduleAdd] at hsum
  rw [grantBlockDownstreamScheduleAdd] at hsum
  change
    grantBlockFrozenProxyMass ring member T W ≤
    Prob.scheduleSum n T (fun word =>
      if grantBlockFamilyProxyHit ring hsp member T W word
      then 1 else 0) +
      (grantBlockFirstDefectFailureMass ring member T W +
        grantBlockNondefectLostMass ring hsp member T W) at hsum
  rw [grantBlockFamilyProxyMassEq
    ring hsp member T W] at hsum
  omega

/-- All power/exponential factors are opaque Nat variables.
No omega call sees n ^ T or 8 ^ radius. -/
private theorem grantBlockScaledMassSubtraction
    (scale frozen physical defect other damage : Nat)
    (hmain : frozen ≤ physical + defect + other)
    (hdef : scale * defect ≤ damage) :
    scale * frozen ≤ scale * (physical + other) + damage := by
  calc
    scale * frozen ≤
      scale * (physical + defect + other) :=
        Nat.mul_le_mul_left scale hmain
    _ = scale * (physical + other) +
        scale * defect := by
          simp only [Nat.mul_add]
          omega
    _ ≤ scale * (physical + other) + damage :=
      Nat.add_le_add_left hdef _

/-- The exact unconditional G14 defect-budget consequence.
The nondefect term is essential under the existing ColdCarrier
type: it includes native-token-sink suppression of BANK grants and
cold-stop-versus-latch mismatch. -/
theorem grantBlockFrozenMassGePhysicalWithClassifiedLoss
    {n : Nat} (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (radius W T : Nat)
    (hBuffered : HeadlineGrantBufferedCounter
      ring member.2.val radius member.1)
    (hWT : W ≤ T)
    (hwindow : W ≤ radius * n / 8) :
    8 ^ radius * grantBlockFrozenProxyMass
      ring member T W ≤
    8 ^ radius *
      (bankTrialRenewalColdProxyMass
        ring member.1 hsp member.2 T W +
       grantBlockNondefectLostMass
        ring hsp member T W) +
    Density.N (badSet ring member.2.val) *
      3 ^ radius * n ^ T := by
  have hcompare :=
    grantBlockPhysicalProxyMassGeFrozenMinusClassified
      ring hsp member T W
  have hplain :
      grantBlockFrozenProxyMass ring member T W ≤
      bankTrialRenewalColdProxyMass
        ring member.1 hsp member.2 T W +
      grantBlockFirstDefectFailureMass ring member T W +
      grantBlockNondefectLostMass ring hsp member T W := by
    omega
  have hcross := grantBlockFirstDefectFailureMassBound
    hn ring member radius W T hBuffered hWT hwindow
  exact grantBlockScaledMassSubtraction
    (8 ^ radius)
    (grantBlockFrozenProxyMass ring member T W)
    (bankTrialRenewalColdProxyMass
      ring member.1 hsp member.2 T W)
    (grantBlockFirstDefectFailureMass ring member T W)
    (grantBlockNondefectLostMass ring hsp member T W)
    (Density.N (badSet ring member.2.val) *
      3 ^ radius * n ^ T)
    hplain hcross

/-- Another literal token-owner row: even when OLD x.grant is
false, an OLD responder grant can move counterclockwise into x.
Thus ColdCarrier's initial GrantFree does not establish
GrantFreeWord, and clause (c) is not logically impossible. -/
theorem grantBlockIncomingGrantTransferPossible (c : Compiled) :
    (tokenStep
      (Agent.blank c)
      { Agent.blank c with grant := true }
      ({ l := false, b := 0, sh := false, sg := false } :
        CertNative)
      ({ l := false, b := 0, sh := false, sg := false } :
        CertNative)
      none false false).1.grant = true := by
  rfl

/-- Exact EXTRA budget needed in addition to C.11/G14.
It is a named Prop, not a theorem or silently assumed bound.
The module currently has no bound of this shape. -/
def GrantBlockNondefectLossBudget
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W budget : Nat) : Prop :=
  grantBlockNondefectLostMass ring hsp member T W ≤ budget

end L3
#print axioms L3.grantBlockSafeWordFirstFailure
#print axioms L3.grantBlockFrozenHitFirstFailureCases
#print axioms L3.grantBlockFirstDefectFailureMassBound
#print axioms L3.grantBlockPhysicalProxyMassGeFrozenMinusClassified
#print axioms L3.grantBlockFrozenMassGePhysicalWithClassifiedLoss
#print axioms L3.grantBlockFrozenBridgeSingleEdgeObstruction
#print axioms L3.grantBlockIncomingGrantTransferPossible

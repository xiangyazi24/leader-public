import Leader.L3.Grant.BlockFrozenMarginal

/-!
G16 C.17, exact G13 local renewal versus frozen BANK latch.

The regenerative scanner and the clamped reference are not the
same *state*: the scanner additionally records LIVE/RECOVERY,
LOST and WON, and its clock/failures. They do use the identical
BANK transition on every active scheduler letter. The successful
latch is absorbing in the standalone clamped reference.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The observation stored by a renewal advance is the actual
clamped local next-state, independently of the LOST bookkeeping. -/
private theorem grantBlockSurrogateAdvanceObserver {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q)
    (trial : BankTrialLocalState q) (age : Nat) :
    (bankTrialRenewalAdvance ring root z trial age e).observer =
      bankTrialLocalNext ring root trial e := by
  unfold bankTrialRenewalAdvance
  split <;> rfl

/-- An active local observer reaches WON only through its
own updated reference success latch. -/
private theorem grantBlockSurrogateLocalActiveWonBank {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hactive :
      (∃ begun : Bool, z.phase = .live begun) ∨
        z.phase = .recovery)
    (hwon : (bankTrialLocalNext ring root z e).phase = .won) :
    (bankTrialLocalNext ring root z e).bank.success = true := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          have hbank := bankTrialLocalNextLiveBank
            ring root e B begun
          rw [hbank]
          cases hs :
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B e).success with
          | true =>
              rfl
          | false =>
              have hnot :
                  (bankTrialLocalNext ring root
                    (⟨B, .live begun⟩ : BankTrialLocalState q)
                    e).phase ≠ .won := by
                simp [bankTrialLocalNext, hs] <;>
                  (repeat' split) <;> simp
              exact False.elim (hnot hwon)
      | recovery =>
          have hbank := bankTrialLocalNextRecoveryBank
            ring root e B
          rw [hbank]
          cases hs :
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B e).success with
          | true =>
              rfl
          | false =>
              have hnot :
                  (bankTrialLocalNext ring root
                    (⟨B, .recovery⟩ : BankTrialLocalState q)
                    e).phase ≠ .won := by
                simp [bankTrialLocalNext, hs] <;>
                  (repeat' split) <;> simp
              exact False.elim (hnot hwon)
      | won =>
          rcases hactive with ⟨begun, hh⟩ | hh
          · cases hh
          · cases hh
      | lost =>
          rcases hactive with ⟨begun, hh⟩ | hh
          · cases hh
          · cases hh

/-- One renewal step updates exactly the same BANK state as the
standalone clamped reference, even across a LOST restart.
WON absorption requires the genuine latch-success invariant. -/
private theorem grantBlockSurrogateNextBank {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q)
    (hwon : z.observer.phase = .won →
      z.observer.bank.success = true) :
    (bankTrialRenewalNext ring root z e).observer.bank =
      GrantBankReference.bankLocalReferenceStepClamped
        ring root z.observer.bank e := by
  cases hp : z.observer.phase with
  | won =>
      rw [bankTrialRenewalNextWon ring root e z hp]
      exact (GrantBankReference.bankLocalReferenceLatchedStepClamped
        ring root e z.observer.bank (hwon hp)).symm
  | lost =>
      have hh :
          (bankTrialRenewalNext ring root z e).observer =
          bankTrialLocalNext ring root
            (bankTrialLocalStart z.observer.bank) e := by
        simp only [bankTrialRenewalNext, hp]
        exact grantBlockSurrogateAdvanceObserver ring root e
          z (bankTrialLocalStart z.observer.bank) 0
      rw [hh]
      exact bankTrialLocalNextLiveBank
        ring root e z.observer.bank false
  | recovery =>
      have hh :
          (bankTrialRenewalNext ring root z e).observer =
            bankTrialLocalNext ring root z.observer e := by
        simp only [bankTrialRenewalNext, hp]
        exact grantBlockSurrogateAdvanceObserver
          ring root e z z.observer z.age
      rw [hh]
      exact bankTrialLocalActiveStepBank
        ring root e z.observer (Or.inr hp)
  | live begun =>
      have hh :
          (bankTrialRenewalNext ring root z e).observer =
            bankTrialLocalNext ring root z.observer e := by
        simp only [bankTrialRenewalNext, hp]
        exact grantBlockSurrogateAdvanceObserver
          ring root e z z.observer z.age
      rw [hh]
      exact bankTrialLocalActiveStepBank
        ring root e z.observer (Or.inl ⟨begun, hp⟩)

/-- A WON phase in the regenerative observer implies the stored
clamped BANK success latch. No assumed trial-success invariant. -/
private theorem grantBlockSurrogateNextWonBank {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q)
    (hwon : z.observer.phase = .won →
      z.observer.bank.success = true) :
    (bankTrialRenewalNext ring root z e).observer.phase = .won →
      (bankTrialRenewalNext ring root z e).observer.bank.success =
        true := by
  cases hp : z.observer.phase with
  | won =>
      rw [bankTrialRenewalNextWon ring root e z hp]
      exact fun _ => hwon hp
  | lost =>
      have hh :
          (bankTrialRenewalNext ring root z e).observer =
            bankTrialLocalNext ring root
              (bankTrialLocalStart z.observer.bank) e := by
        simp only [bankTrialRenewalNext, hp]
        exact grantBlockSurrogateAdvanceObserver ring root e
          z (bankTrialLocalStart z.observer.bank) 0
      rw [hh]
      exact grantBlockSurrogateLocalActiveWonBank
        ring root e (bankTrialLocalStart z.observer.bank)
        (Or.inl ⟨false, rfl⟩)
  | recovery =>
      have hh :
          (bankTrialRenewalNext ring root z e).observer =
            bankTrialLocalNext ring root z.observer e := by
        simp only [bankTrialRenewalNext, hp]
        exact grantBlockSurrogateAdvanceObserver
          ring root e z z.observer z.age
      rw [hh]
      exact grantBlockSurrogateLocalActiveWonBank
        ring root e z.observer (Or.inr hp)
  | live begun =>
      have hh :
          (bankTrialRenewalNext ring root z e).observer =
            bankTrialLocalNext ring root z.observer e := by
        simp only [bankTrialRenewalNext, hp]
        exact grantBlockSurrogateAdvanceObserver
          ring root e z z.observer z.age
      rw [hh]
      exact grantBlockSurrogateLocalActiveWonBank
        ring root e z.observer (Or.inl ⟨begun, hp⟩)

/-- Synchronization for the whole regenerative scanner:
after every actual scheduler word its stored BANK equals the
standalone clamped reference on the SAME word. -/
theorem grantBlockSurrogateRenewalBankSync {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankTrialRenewalState q),
      (z.observer.phase = .won →
        z.observer.bank.success = true) →
      (bankTrialRenewalRunFrom ring root word z).observer.bank =
        GrantBankReference.bankLocalReferenceWordClamped
          ring root word z.observer.bank ∧
      ((bankTrialRenewalRunFrom ring root word z).observer.phase =
        .won →
        (bankTrialRenewalRunFrom ring root word z).observer.bank.success =
          true) := by
  intro word
  induction word with
  | nil =>
      intro z hwon
      exact ⟨rfl, hwon⟩
  | cons e rest ih =>
      intro z hwon
      have hstep := grantBlockSurrogateNextBank
        ring root e z hwon
      have hnext := grantBlockSurrogateNextWonBank
        ring root e z hwon
      have htail := ih (bankTrialRenewalNext ring root z e) hnext
      constructor
      · calc
          (bankTrialRenewalRunFrom ring root
            (e :: rest) z).observer.bank =
            (bankTrialRenewalRunFrom ring root rest
              (bankTrialRenewalNext ring root z e)).observer.bank := rfl
          _ = GrantBankReference.bankLocalReferenceWordClamped
                ring root rest
                (bankTrialRenewalNext ring root z e).observer.bank :=
              htail.1
          _ = GrantBankReference.bankLocalReferenceWordClamped
                ring root rest
                (GrantBankReference.bankLocalReferenceStepClamped
                  ring root z.observer.bank e) := by rw [hstep]
          _ = GrantBankReference.bankLocalReferenceWordClamped
                ring root (e :: rest) z.observer.bank := rfl
      · exact htail.2

/-- The local G13 renewal success implies success of the
IDENTICAL clamped reference started from the SAME BANK state.
The observer's restart counters do not change its BANK update. -/
theorem grantBlockSurrogateRenewalWinImpliesLatch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (W : Nat) (suffix : List (Fin n))
    (h : bankTrialRenewalSuccessBy ring root S W suffix = true) :
    (GrantBankReference.bankLocalReferenceWordClamped
      ring root (suffix.take W) S).success = true := by
  have hrun := grantBlockSurrogateRenewalBankSync
    ring root (suffix.take W) (bankTrialRenewalStart S)
    (by intro hp; cases hp)
  have hphase :
      (bankTrialRenewalRun ring root S
        (suffix.take W)).observer.phase = .won := by
    rw [bankTrialRenewalSuccessByRun] at h
    exact of_decide_eq_true h
  have hwin :
      (bankTrialRenewalRun ring root S
        (suffix.take W)).observer.bank.success = true := by
    exact hrun.2 hphase
  have hsync :
      (bankTrialRenewalRun ring root S (suffix.take W)).observer.bank =
        GrantBankReference.bankLocalReferenceWordClamped
          ring root (suffix.take W) S := hrun.1
  rw [← hsync]
  exact hwin

/-- On the support subword, the same implication holds:
only clamped BANK letters can make the renewal observer WON. -/
theorem grantBlockSurrogateRenewalWinSupport {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (W : Nat) (suffix : List (Fin n))
    (h : bankTrialRenewalSuccessBy ring root S W suffix = true) :
    (GrantBankReference.bankLocalReferenceWordClamped
      ring root
      (GrantBankReference.bankLocalReferenceSupportSubword
        (q := q) ring root (suffix.take W)) S).success = true := by
  rw [GrantBankReference.bankLocalReferenceWordLocalityClamped
    ring root (suffix.take W) S]
  exact grantBlockSurrogateRenewalWinImpliesLatch
    ring root S W suffix h

/-- Equality of two clamped BANK references when their four BANK
coordinates agree at all protected sites, and both have the
canonical false success latch. -/
private theorem grantBlockSurrogateReferenceStartOfFields
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (D : Counter.Config q n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfalse : B.success = false)
    (hfields :
      GrantBankReference.bankLocalReferenceFieldsAgree
        ring D root B) :
    B = GrantBankReference.bankLocalReferenceStart ring root D := by
  cases B with
  | mk fields success =>
      change success = false at hfalse
      subst success
      have hf :
          fields =
            (GrantBankReference.bankLocalReferenceStart
              ring root D).fields := by
        funext i
        have hi : i.val ≤ (compileAdvice q).b := by
          have hb := i.isLt
          omega
        have heq := hfields i.val hi
        have hindex :
            (⟨i.val, Nat.lt_succ_of_le hi⟩ :
              Fin ((compileAdvice q).b + 1)) = i := Fin.ext rfl
        rw [hindex] at heq
        change fields i =
          (GrantBankReference.bankLocalReferenceStart
            ring root D).fields i
        exact heq.symm
      change
        (⟨fields, false⟩ :
          GrantBankReference.BankLocalReference
            (compileAdvice q).b) =
        GrantBankReference.bankLocalReferenceStart ring root D
      rw [hf]
      rfl

/-- The genuine physical SafeWord certificate keeps the original
carrier's clamped BANK reference synchronized through the CLEAN
cut. This includes both initial arbitrary private scratch and
any loss/recovery during the cold prefix. -/
theorem grantBlockSurrogateSafeCutReference
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (cut : List (Fin n))
    (hsafe : GrantBankReference.bankLocalReferenceSafeWord
      ring member.1 member.2.val cut) :
    GrantBankReference.bankLocalReferenceWordClamped
      ring member.1 cut
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val) =
    GrantBankReference.bankLocalReferenceStart
      ring member.1
      (Counter.Word ring cut member.2.val) := by
  have hcouple :=
    GrantBankReference.bankLocalReferenceNoSuccessWordCouplingClamped
      ring member.1 hsp cut member.2.val
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)
      member.2.property.1
      hsafe.1 hsafe.2.1
      (GrantBankReference.bankLocalReferenceStartAgrees
        ring member.2.val member.1)
      rfl hsafe.2.2
  exact grantBlockSurrogateReferenceStartOfFields
    ring member.1 (Counter.Word ring cut member.2.val)
    (GrantBankReference.bankLocalReferenceWordClamped
      ring member.1 cut
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val))
    hcouple.2.2 hcouple.1

/-- Exact CLEAN-handoff implication on the original scheduler.
The observer starts from the *physical* CLEAN cut D, not from
an independently sampled reference.  The local G13 success by
the remaining wall-clock window implies the original-carrier
frozen BANK success, provided cut was physically safe. -/
theorem grantBlockSurrogateSafeCleanSuffixHit
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (W : Nat) (cut suffix : List (Fin n))
    (D : Counter.Config (ceilLogTwo n) n)
    (hcut : GrantBankReference.bankLocalReferenceSafeWord
      ring member.1 member.2.val cut)
    (hphysical : D = Counter.Word ring cut member.2.val)
    (hwin : bankTrialRenewalSuccessBy ring member.1
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 D)
      (W - cut.length) suffix = true) :
    grantBlockFrozenProxyHit ring member
      (cut ++ suffix.take (W - cut.length)) = true := by
  rw [hphysical] at hwin
  have hlocal := grantBlockSurrogateRenewalWinImpliesLatch
    ring member.1
    (GrantBankReference.bankLocalReferenceStart
      ring member.1 (Counter.Word ring cut member.2.val))
    (W - cut.length) suffix hwin
  have hcutRef := grantBlockSurrogateSafeCutReference
    ring hsp member cut hcut
  have hfull :
      (GrantBankReference.bankLocalReferenceWordClamped
        ring member.1
        (cut ++ suffix.take (W - cut.length))
        (GrantBankReference.bankLocalReferenceStart
          ring member.1 member.2.val)).success = true := by
    rw [GrantBankReference.bankLocalReferenceWordAppendClamped
      ring member.1 cut (suffix.take (W - cut.length))
      (GrantBankReference.bankLocalReferenceStart
        ring member.1 member.2.val)]
    rw [hcutRef]
    exact hlocal
  unfold grantBlockFrozenProxyHit
  rw [GrantBankReference.bankLocalReferenceWordLocalityClamped
    ring member.1
    (cut ++ suffix.take (W - cut.length))
    (GrantBankReference.bankLocalReferenceStart
      ring member.1 member.2.val)]
  exact hfull

/-- The specific CLEAN suffix witness that the G13 stopped proxy
must expose if its hit is to be credited to the initial BANK
latch. This is a *data definition*, not a new success hypothesis.
The joint word is still the original physical scheduler. -/
def GrantBlockSurrogateSafeCleanCertificate
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (W : Nat) (word : List (Fin n)) : Prop :=
  ∃ cut : List (Fin n), ∃ suffix : List (Fin n),
    ∃ D : Counter.Config (ceilLogTwo n) n,
      word.take W = cut ++ suffix.take (W - cut.length) ∧
      GrantBankReference.bankLocalReferenceSafeWord
        ring member.1 member.2.val cut ∧
      D = Counter.Word ring cut member.2.val ∧
      bankTrialRenewalSuccessBy ring member.1
        (GrantBankReference.bankLocalReferenceStart ring member.1 D)
        (W - cut.length) suffix = true

/-- Each certified G13 CLEAN success is necessarily a success of
the initial frozen support-only latch. -/
theorem grantBlockSurrogateSafeCleanCertificateImpliesFrozen
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (W : Nat) (word : List (Fin n))
    (h : GrantBlockSurrogateSafeCleanCertificate
      ring member W word) :
    grantBlockFrozenProxyHit ring member (word.take W) = true := by
  obtain ⟨cut, suffix, D, hword, hsafe, hphysical, hwin⟩ := h
  rw [hword]
  exact grantBlockSurrogateSafeCleanSuffixHit
    ring hsp member W cut suffix D hsafe hphysical hwin

/-- A physical cold-proxy hit without the initial frozen latch
cannot have any safe CLEAN handoff witness. Consequently the
remaining obstruction is an *uncertified first-stop witness*,
not a mismatch of the two local BANK transition functions. -/
theorem grantBlockSurrogatePhysicalOnlyNoSafeClean
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n))
    (h : GrantBlockPhysicalOnlyNondefect
      ring hsp member T W word) :
    ¬ GrantBlockSurrogateSafeCleanCertificate
        ring member W word := by
  intro hcert
  have hf := grantBlockSurrogateSafeCleanCertificateImpliesFrozen
    ring hsp member W word hcert
  rw [h.2.1] at hf
  cases hf

/-- On a purified G18 path, every physical-only G13 proxy hit is
either a G18 hit at the first physical grant or belongs to the
safe-W, no-BANK-success branch with no certified CLEAN cut. -/
theorem grantBlockSurrogatePhysicalOnlyG18OrUncertified
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
     ¬ GrantBlockSurrogateSafeCleanCertificate
        ring member W word) := by
  rcases grantBlockPhysicalOnlyG18OrSafe
      ring hn hsp member hp T W word h with hhit | hsafe
  · exact Or.inl hhit
  · exact Or.inr ⟨hsafe.1,
      grantBlockSurrogatePhysicalOnlyNoSafeClean
        ring hsp member T W word h⟩

/-- Physical finite-word concatenation, needed to retain the
actual G18 first-hit cut rather than a target at terminal time. -/
private theorem grantBlockSurrogatePhysicalWordAppend
    {n q : Nat} (ring : DirectedRing n) :
    ∀ (pre suffix : List (Fin n))
      (C : Counter.Config q n),
      Counter.Word ring (pre ++ suffix) C =
        Counter.Word ring suffix (Counter.Word ring pre C) := by
  intro pre
  induction pre with
  | nil =>
      intro suffix C
      rfl
  | cons e rest ih =>
      intro suffix C
      change Counter.Word ring (rest ++ suffix)
          ((protocol q).step ring C e) =
        Counter.Word ring suffix
          (Counter.Word ring rest
            ((protocol q).step ring C e))
      exact ih suffix _

/-- Genuine first target of G18 somewhere in the first W global
scheduler letters. This is a prefix-hit event, not merely a
terminal-state predicate. -/
def GrantBlockSurrogateG18HitWithin
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (W : Nat) (word : List (Fin n)) : Prop :=
  ∃ pre suffix : List (Fin n),
    word.take W = pre ++ suffix ∧
      (headlineGrantReady ring (Counter.Word ring pre C) ∨
        headlineGeneratedTarget ring (Counter.Word ring pre C))

noncomputable def grantBlockSurrogateG18HitMass
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if GrantBlockSurrogateG18HitWithin ring C W word then 1 else 0)

/-- Exact still-uncontrolled branch: a G13 physical cold-proxy
success, no original-carrier frozen latch, no prior OLD defect,
and an entirely safe actual W-prefix. A certified CLEAN handoff
would make this branch impossible, as proved above. -/
def GrantBlockSurrogateSafeProxyMismatch
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n)) : Prop :=
  GrantBlockPhysicalOnlyNondefect ring hsp member T W word ∧
  GrantBankReference.bankLocalReferenceSafeWord
    ring member.1 member.2.val (word.take W)

noncomputable def grantBlockSurrogateSafeMismatchMass
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if GrantBlockSurrogateSafeProxyMismatch
       ring hsp member T W word then 1 else 0)

/-- On a purified G18 path, the nondefect physical-only residual
is a G18 first hit OR an explicitly named safe CLEAN surrogate
mismatch. The first grant cannot disappear into a defect charge. -/
theorem grantBlockSurrogatePhysicalOnlyG18OrMismatch
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (hp : headlinePurified ring member.2.val)
    (T W : Nat) (word : List (Fin n))
    (h : GrantBlockPhysicalOnlyNondefect
      ring hsp member T W word) :
    GrantBlockSurrogateG18HitWithin
        ring member.2.val W word ∨
      GrantBlockSurrogateSafeProxyMismatch
        ring hsp member T W word := by
  rcases grantBlockSurrogatePhysicalOnlyG18OrUncertified
      ring hn hsp member hp T W word h with hg | hs
  · obtain ⟨pre, edge, suffix, hword, htarget⟩ := hg
    left
    refine ⟨pre ++ [edge], suffix, ?_, ?_⟩
    · rw [hword]
      simp only [List.append_assoc, List.singleton_append]
    · have hstate :
          Counter.Word ring (pre ++ [edge]) member.2.val =
            headlinePhysicalNext ring
              (Counter.Word ring pre member.2.val) edge := by
        rw [grantBlockSurrogatePhysicalWordAppend
          ring pre [edge] member.2.val]
        rfl
      rw [hstate]
      exact htarget
  · exact Or.inr ⟨h, hs.1⟩

/-- Original-scheduler Nat-valued finite-sum additivity. -/
private theorem grantBlockSurrogateScheduleAdd
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

/-- The entire nondefect residual is covered by the G18-hit
numerator plus the precisely identified safe-CLEAN mismatch. -/
theorem grantBlockSurrogatePhysicalOnlyMassCover
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (hp : headlinePurified ring member.2.val)
    (T W : Nat) :
    grantBlockPhysicalOnlyNondefectMass
      ring hsp member T W ≤
    grantBlockSurrogateG18HitMass
      ring member.2.val T W +
    grantBlockSurrogateSafeMismatchMass
      ring hsp member T W := by
  have hpoint (word : List (Fin n)) :
      (if GrantBlockPhysicalOnlyNondefect
        ring hsp member T W word then 1 else 0) ≤
      (if GrantBlockSurrogateG18HitWithin
        ring member.2.val W word then 1 else 0) +
      (if GrantBlockSurrogateSafeProxyMismatch
        ring hsp member T W word then 1 else 0) := by
    by_cases h : GrantBlockPhysicalOnlyNondefect
        ring hsp member T W word
    · rcases grantBlockSurrogatePhysicalOnlyG18OrMismatch
        ring hn hsp member hp T W word h with hg | hs
      · simp [h, hg]
      · simp [h, hs]
    · simp [h]
  have hmass := Density.schedule_sum_mono T
    (fun word =>
      if GrantBlockPhysicalOnlyNondefect
        ring hsp member T W word then 1 else 0)
    (fun word =>
      (if GrantBlockSurrogateG18HitWithin
        ring member.2.val W word then 1 else 0) +
      (if GrantBlockSurrogateSafeProxyMismatch
        ring hsp member T W word then 1 else 0))
    hpoint
  rw [grantBlockSurrogateScheduleAdd] at hmass
  exact hmass

/-- The G13/G14 lower bound can now be charged to the physical
G18 first-hit event, plus ONLY the remaining safe-CLEAN
handoff mismatch. No independence or additional assumption. -/
theorem grantBlockSurrogateFrozenMarginalG18Cover
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (member : GrantBlockFamilyMember ring)
    (hp : headlinePurified ring member.2.val)
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
       (grantBlockSurrogateG18HitMass
          ring member.2.val T W +
        grantBlockSurrogateSafeMismatchMass
          ring hsp member T W)) := by
  have hbase := grantBlockFrozenProxyMassLower
    ring hn hsp hw hlarge member R L T W radius
    hradius hW hL hWT hbudget hBuffered hcrossWindow
  have hcover := grantBlockSurrogatePhysicalOnlyMassCover
    ring hn hsp member hp T W
  have hsum :
      grantBlockFrozenProxyMass ring member T W +
        grantBlockPhysicalOnlyNondefectMass
          ring hsp member T W ≤
      grantBlockFrozenProxyMass ring member T W +
        (grantBlockSurrogateG18HitMass
          ring member.2.val T W +
        grantBlockSurrogateSafeMismatchMass
          ring hsp member T W) :=
    Nat.add_le_add_left hcover _
  exact Nat.le_trans hbase
    (Nat.mul_le_mul_left
      (grantBlockFamilyScale n * (8 ^ radius)) hsum)

/-- Plain finite-word fold of the actual cold observer. No
independent scheduler, stopwatch or probabilistic product. -/
private def grantBlockSurrogateColdFold {X : Type} {n : Nat}
    (next : X → Fin n → X) :
    List (Fin n) → X → X
  | [], z => z
  | e :: tail, z =>
      grantBlockSurrogateColdFold next tail (next z e)

/-- Before the FIRST stopped prefix each observer state has
stop=false. Unlike a global SafeWord condition this predicate
records the observer's own cut chronology. -/
private def grantBlockSurrogateNoStopBefore
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool) :
    List (Fin n) → List (Fin n) → X → Prop
  | _, [], _ => True
  | pre, e :: tail, z =>
      stop pre z = false ∧
        grantBlockSurrogateNoStopBefore next stop
          (pre ++ [e]) tail (next z e)

/-- A positive Nat stopped observer weight HAS a genuine
first terminal cut. This generic theorem is pure recursion;
it neither declares nor assumes any terminal event. -/
private theorem grantBlockSurrogateStoppedWordWitness
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat) :
    ∀ (word : List (Fin n)) (t : Nat)
      (pre : List (Fin n)) (z : X),
      0 < bankTrialSuccessNatStoppedWord
        next stop A t pre z word →
      ∃ used suffix : List (Fin n),
        word = used ++ suffix ∧
        grantBlockSurrogateNoStopBefore
          next stop pre used z ∧
        stop (pre ++ used)
          (grantBlockSurrogateColdFold next used z) = true ∧
        0 < A (pre ++ used)
          (grantBlockSurrogateColdFold next used z)
          (t - used.length) suffix := by
  intro word
  induction word with
  | nil =>
      intro t pre z hp
      cases hs : stop pre z with
      | false =>
          have hzero :
              bankTrialSuccessNatStoppedWord
                next stop A t pre z [] = 0 := by
            simp [bankTrialSuccessNatStoppedWord, hs]
          rw [hzero] at hp
          omega
      | true =>
          refine ⟨[], [], rfl, True.intro, ?_, ?_⟩
          · simpa only [List.append_nil,
              grantBlockSurrogateColdFold] using hs
          · simpa [bankTrialSuccessNatStoppedWord, hs,
              grantBlockSurrogateColdFold] using hp
  | cons e tail ih =>
      intro t pre z hp
      cases hs : stop pre z with
      | true =>
          refine ⟨[], e :: tail, rfl, True.intro, ?_, ?_⟩
          · simpa only [List.append_nil,
              grantBlockSurrogateColdFold] using hs
          · simpa [bankTrialSuccessNatStoppedWord, hs,
              grantBlockSurrogateColdFold] using hp
      | false =>
          have ht :
              0 < bankTrialSuccessNatStoppedWord
                next stop A (t - 1) (pre ++ [e])
                  (next z e) tail := by
            simpa [bankTrialSuccessNatStoppedWord, hs] using hp
          obtain ⟨used, suffix, htail, hno, hstop, hweight⟩ :=
            ih (t - 1) (pre ++ [e]) (next z e) ht
          have hpre :
              pre ++ (e :: used) = (pre ++ [e]) ++ used := by
            simp only [List.append_assoc, List.singleton_append]
          have hclock :
              t - (e :: used).length =
                (t - 1) - used.length := by
            simp only [List.length_cons]
            omega
          refine ⟨e :: used, suffix, ?_, ?_, ?_, ?_⟩
          · rw [htail]
            rfl
          · exact ⟨hs, hno⟩
          · rw [hpre]
            exact hstop
          · rw [hpre, hclock]
            exact hweight

/-- SafeWord is prefix closed; no post-success SafeWord is
silently required at the letter producing the success. -/
private theorem grantBlockSurrogateSafePrefix
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (pre suffix : List (Fin n))
      (C : Counter.Config q n),
      GrantBankReference.bankLocalReferenceSafeWord
        ring root C (pre ++ suffix) →
      GrantBankReference.bankLocalReferenceSafeWord
        ring root C pre := by
  intro pre
  induction pre with
  | nil =>
      intro suffix C hsafe
      have hg : Counter.GrantFree C root := by
        cases suffix with
        | nil =>
            exact hsafe.1
        | cons e tail =>
            exact hsafe.1.1
      exact grantBlockSafeWordNil ring root C hg
  | cons e rest ih =>
      intro suffix C hsafe
      have hfirst :=
        (grantBlockSafeWordConsIff ring root C e
          (rest ++ suffix)).1 hsafe
      have htail := ih suffix ((protocol q).step ring C e)
        hfirst.2.2.2
      exact (grantBlockSafeWordConsIff
        ring root C e rest).2
        ⟨hfirst.1, hfirst.2.1, hfirst.2.2.1, htail⟩

/-- The first-stop witness's entire proper prefix is authentic
physical evolution, using the real Counter.resetClockBankColdNext,
with no deleted scheduler letters. -/
private theorem grantBlockSurrogateColdFoldPhysical
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (used : List (Fin n))
      (pre : List (Fin n))
      (z : Counter.ResetClockBankColdState (q := q) ring root),
      grantBlockSurrogateNoStopBefore
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root) pre used z →
      Counter.resetClockBankColdConfig ring root
        (grantBlockSurrogateColdFold
          (Counter.resetClockBankColdNext ring root hsp)
          used z) =
      Counter.Word ring used
        (Counter.resetClockBankColdConfig ring root z) := by
  intro used
  induction used with
  | nil =>
      intro pre z _
      rfl
  | cons e tail ih =>
      intro pre z hno
      have hz : ¬ Counter.resetClockBankColdTerminal ring root z := by
        intro ht
        have htrue :=
          (bankTrialRenewalColdStopCorrect ring root pre z).2 ht
        have hfalse :
            bankTrialRenewalColdStop ring root pre z = false := hno.1
        rw [htrue] at hfalse
        cases hfalse
      have hphys := Counter.resetClockBankColdPhysical
        ring root hsp z hz e
      have htail := ih (pre ++ [e])
        (Counter.resetClockBankColdNext ring root hsp z e) hno.2
      calc
        Counter.resetClockBankColdConfig ring root
          (grantBlockSurrogateColdFold
            (Counter.resetClockBankColdNext ring root hsp)
            (e :: tail) z) =
        Counter.resetClockBankColdConfig ring root
          (grantBlockSurrogateColdFold
            (Counter.resetClockBankColdNext ring root hsp)
            tail
            (Counter.resetClockBankColdNext ring root hsp z e)) := rfl
        _ = Counter.Word ring tail
              (Counter.resetClockBankColdConfig ring root
                (Counter.resetClockBankColdNext
                  ring root hsp z e)) := htail
        _ = Counter.Word ring tail
              ((protocol q).step ring
                (Counter.resetClockBankColdConfig ring root z)
                e) :=
          congrArg (Counter.Word ring tail) hphys
        _ = Counter.Word ring (e :: tail)
              (Counter.resetClockBankColdConfig ring root z) := rfl

/-- The physical observer's STOP label remains sound along the
actual plain fold. The first-stop induction never forges a
CLEAN/GRANT/DEFECT constructor. -/
private theorem grantBlockSurrogateColdFoldSound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (used : List (Fin n))
      (z : Counter.ResetClockBankColdState (q := q) ring root),
      Counter.resetColdObserverSound ring root z →
      Counter.resetColdObserverSound ring root
        (grantBlockSurrogateColdFold
          (Counter.resetClockBankColdNext ring root hsp)
          used z) := by
  intro used
  induction used with
  | nil =>
      intro z hz
      exact hz
  | cons e tail ih =>
      intro z hz
      exact ih (Counter.resetClockBankColdNext ring root hsp z e)
        (Counter.resetColdObserverSoundStep ring root hsp z hz e)

/-- The ordinary list.take of an already-shorter word is itself. -/
private theorem grantBlockSurrogateTakeOfLengthLe
    {α : Type} :
    ∀ (word : List α) (W : Nat),
      word.length ≤ W → word.take W = word := by
  intro word
  induction word with
  | nil =>
      intro W _
      cases W <;> rfl
  | cons e rest ih =>
      intro W h
      cases W with
      | zero =>
          simp only [List.length_cons] at h
          omega
      | succ k =>
          have ht : rest.length ≤ k := by
            simp only [List.length_cons] at h
            omega
          change e :: rest.take k = e :: rest
          rw [ih k ht]

/-- The time-limited prefix has at most W letters, even for
a shorter word. -/
private theorem grantBlockSurrogateTakeLengthLe
    {α : Type} :
    ∀ (word : List α) (W : Nat),
      (word.take W).length ≤ W := by
  intro word W
  induction W generalizing word with
  | zero =>
      simp
  | succ k ih =>
      cases word with
      | nil =>
          simp
      | cons e tail =>
          change (tail.take k).length + 1 ≤ k + 1
          exact Nat.succ_le_succ (ih tail)

/-- A positive physical G13 stopped proxy on an entirely safe word
forces the initial-carrier frozen latch to succeed. This is the
unconditional synchronized CLEAN-handoff proof, not an assumed
observer-to-reference correspondence.

An authentic GRANT cut contradicts SafeWord's final GrantFree;
a DEFECT cut has zero proxy weight; a CLEAN cut has the exact
physical D = Counter.Word cut C and its renewal suffix uses the
same clamped BANK transition as the initial frozen reference. -/
theorem grantBlockSurrogateSafeProxyImpliesFrozen
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (W : Nat) (word : List (Fin n))
    (hlen : word.length ≤ W)
    (hsafe : GrantBankReference.bankLocalReferenceSafeWord
      ring member.1 member.2.val word)
    (hproxy :
      0 < grantBlockFamilyProxyWord
        ring hsp member W W word) :
    grantBlockFrozenProxyHit ring member word = true := by
  change
    0 < bankTrialSuccessNatStoppedWord
      (Counter.resetClockBankColdNext ring member.1 hsp)
      (bankTrialRenewalColdStop ring member.1)
      (fun cut z _ suffix =>
        bankTrialRenewalColdProxyWeight
          ring member.1 W cut z suffix)
      W []
      (Counter.resetClockBankColdStart ring member.1 member.2)
      word at hproxy
  obtain ⟨cut, suffix, hword, hno, hstop, hweight⟩ :=
    grantBlockSurrogateStoppedWordWitness
      (Counter.resetClockBankColdNext ring member.1 hsp)
      (bankTrialRenewalColdStop ring member.1)
      (fun cut z _ suffix =>
        bankTrialRenewalColdProxyWeight
          ring member.1 W cut z suffix)
      word W []
      (Counter.resetClockBankColdStart ring member.1 member.2)
      hproxy
  have hlenEq := congrArg List.length hword
  simp only [List.length_append] at hlenEq
  have hcutLength : cut.length ≤ W := by omega
  have hremLength : suffix.length ≤ W - cut.length := by omega
  have hsafeCut :
      GrantBankReference.bankLocalReferenceSafeWord
        ring member.1 member.2.val cut := by
    have hsafeFull :
        GrantBankReference.bankLocalReferenceSafeWord
          ring member.1 member.2.val (cut ++ suffix) := by
      rw [←hword]
      exact hsafe
    exact grantBlockSurrogateSafePrefix
      ring member.1 cut suffix member.2.val hsafeFull
  have hphysical := grantBlockSurrogateColdFoldPhysical
    ring member.1 hsp cut []
    (Counter.resetClockBankColdStart ring member.1 member.2) hno
  rw [Counter.resetClockBankColdStartPhysical
    ring member.1 member.2] at hphysical
  have hsound := grantBlockSurrogateColdFoldSound
    ring member.1 hsp cut
    (Counter.resetClockBankColdStart ring member.1 member.2)
    (Counter.resetColdObserverSoundStart
      ring member.1 member.2)
  have hterminal : Counter.resetClockBankColdTerminal
      ring member.1
      (grantBlockSurrogateColdFold
        (Counter.resetClockBankColdNext ring member.1 hsp)
        cut
        (Counter.resetClockBankColdStart
          ring member.1 member.2)) := by
    apply (bankTrialRenewalColdStopCorrect ring member.1 cut
      (grantBlockSurrogateColdFold
        (Counter.resetClockBankColdNext ring member.1 hsp)
        cut
        (Counter.resetClockBankColdStart
          ring member.1 member.2))).1
    simpa only [List.nil_append] using hstop
  obtain ⟨D, reason, hshape⟩ :=
    bankTrialRenewalColdTerminalShape ring member.1
      (grantBlockSurrogateColdFold
        (Counter.resetClockBankColdNext ring member.1 hsp)
        cut
        (Counter.resetClockBankColdStart
          ring member.1 member.2)) hterminal
  rw [hshape] at hphysical hsound
  have hD : D = Counter.Word ring cut member.2.val := by
    exact hphysical
  have hfree : Counter.GrantFree D member.1 := by
    have hf := bankTrialLocalGrantFreeAtWordEnd
      ring member.1 cut member.2.val hsafeCut.1
    rw [←hD] at hf
    exact hf
  change 0 < bankTrialRenewalColdProxyWeight
    ring member.1 W cut
    (grantBlockSurrogateColdFold
      (Counter.resetClockBankColdNext ring member.1 hsp)
      cut
      (Counter.resetClockBankColdStart
        ring member.1 member.2))
    suffix at hweight
  rw [hshape] at hweight
  cases reason with
  | grant =>
      have hg : (D member.1).grant = true := hsound
      have hfg : (D member.1).grant = false := hfree
      rw [hg] at hfg
      cases hfg
  | defect =>
      simp [bankTrialRenewalColdProxyWeight] at hweight
  | clean =>
      have hwin :
          bankTrialRenewalSuccessBy ring member.1
            (GrantBankReference.bankLocalReferenceStart
              ring member.1 D)
            (W - cut.length) suffix = true := by
        rw [bankTrialRenewalColdCleanRemainingWindow
          ring member.1 D W cut suffix
          hcutLength hfree] at hweight
        cases hs :
            bankTrialRenewalSuccessBy ring member.1
              (GrantBankReference.bankLocalReferenceStart
                ring member.1 D)
              (W - cut.length) suffix with
        | true =>
            rfl
        | false =>
            simp [Prob.indicator, hs] at hweight
      have hh := grantBlockSurrogateSafeCleanSuffixHit
        ring hsp member W cut suffix D hsafeCut hD hwin
      have ht :
          suffix.take (W - cut.length) = suffix :=
        grantBlockSurrogateTakeOfLengthLe
          suffix (W - cut.length) hremLength
      rw [ht] at hh
      rw [←hword] at hh
      exact hh

/-- The safe-W surrogate mismatch is impossible. In particular
G13's local CLEAN/restart scanner cannot manufacture a win
when the original-carrier frozen BANK latch stays false and
every actual letter through W is SafeWord. -/
theorem grantBlockSurrogateSafeMismatchImpossible
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n))
    (h : GrantBlockSurrogateSafeProxyMismatch
      ring hsp member T W word) : False := by
  have hphys := h.1.1
  have hhit :
      grantBlockFamilyProxyHit
        ring hsp member W W (word.take W) = true := by
    rw [←grantBlockFamilyProxyHitPrefixWord
      ring hsp member T W word]
    exact hphys
  have hpositive :
      0 < grantBlockFamilyProxyWord
        ring hsp member W W (word.take W) := by
    unfold grantBlockFamilyProxyHit at hhit
    exact of_decide_eq_true hhit
  have hlength := grantBlockSurrogateTakeLengthLe word W
  have hfrozen := grantBlockSurrogateSafeProxyImpliesFrozen
    ring hsp member W (word.take W) hlength h.2 hpositive
  rw [h.1.2.1] at hfrozen
  cases hfrozen

/-- An unconditional ZERO mass, not an unproved numerical budget.
The only extra condition is the literal physical SafeWord which
is already part of the residual's definition. -/
theorem grantBlockSurrogateSafeMismatchMassZero
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) :
    grantBlockSurrogateSafeMismatchMass
      ring hsp member T W = 0 := by
  have hzero (word : List (Fin n)) :
      (if GrantBlockSurrogateSafeProxyMismatch
        ring hsp member T W word then (1 : Nat) else 0) = 0 := by
    by_cases h : GrantBlockSurrogateSafeProxyMismatch
        ring hsp member T W word
    · exact False.elim
        (grantBlockSurrogateSafeMismatchImpossible
          ring hsp member T W word h)
    · simp [h]
  have hfun :
      (fun word : List (Fin n) =>
        if GrantBlockSurrogateSafeProxyMismatch
          ring hsp member T W word then 1 else 0) =
      (fun _ : List (Fin n) => 0) := by
    funext word
    exact hzero word
  unfold grantBlockSurrogateSafeMismatchMass
  rw [hfun]
  change FixedSpanRenewalPayload.wordSum n T
      (fun _ : List (Fin n) => 0) = 0
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  simp only [ofFn_sum_const, Nat.mul_zero]

/-- Only first actual G18 hits remain: all defect-free
physical-only surplus beyond the initial frozen marginal is
already counted by the target being proved. -/
theorem grantBlockPhysicalOnlyMassLeG18Hit
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (hp : headlinePurified ring member.2.val)
    (T W : Nat) :
    grantBlockPhysicalOnlyNondefectMass
      ring hsp member T W ≤
    grantBlockSurrogateG18HitMass
      ring member.2.val T W := by
  have hcover := grantBlockSurrogatePhysicalOnlyMassCover
    ring hn hsp member hp T W
  rw [grantBlockSurrogateSafeMismatchMassZero
    ring hsp member T W] at hcover
  simpa only [Nat.add_zero] using hcover

/-- CLEAN G16 marginal with the genuine G18 first-hit credit.
The physical cold proxy's lower bound now transfers into
the frozen support-only event OR an already-terminal G18 path;
there is NO residual surrogate mismatch term.

A bound for the frozen mass ALONE, without the G18 term, would
be false for words where another root receives a grant first.
Such paths are successes of StageGrantLeaderlessClock, not losses. -/
theorem grantBlockFrozenProxyMassLowerClean
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (member : GrantBlockFamilyMember ring)
    (hp : headlinePurified ring member.2.val)
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
        grantBlockSurrogateG18HitMass
          ring member.2.val T W) := by
  have hbase := grantBlockFrozenProxyMassLower
    ring hn hsp hw hlarge member R L T W radius
    hradius hW hL hWT hbudget hBuffered hcrossWindow
  have hcover := grantBlockPhysicalOnlyMassLeG18Hit
    ring hn hsp member hp T W
  have hsum :
      grantBlockFrozenProxyMass ring member T W +
        grantBlockPhysicalOnlyNondefectMass
          ring hsp member T W ≤
      grantBlockFrozenProxyMass ring member T W +
        grantBlockSurrogateG18HitMass
          ring member.2.val T W :=
    Nat.add_le_add_left hcover _
  exact Nat.le_trans hbase
    (Nat.mul_le_mul_left
      (grantBlockFamilyScale n * (8 ^ radius)) hsum)

end L3

#print axioms L3.grantBlockSurrogateRenewalBankSync
#print axioms L3.grantBlockSurrogateRenewalWinImpliesLatch
#print axioms L3.grantBlockSurrogateSafeCleanSuffixHit
#print axioms L3.grantBlockSurrogateSafeProxyImpliesFrozen
#print axioms L3.grantBlockSurrogateSafeMismatchMassZero
#print axioms L3.grantBlockPhysicalOnlyMassLeG18Hit
#print axioms L3.grantBlockFrozenProxyMassLowerClean


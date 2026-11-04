import Leader.L3.Bank.WordPass
import Leader.L3.Bank.WordRenewalSoftClose

/-!
R10 W: the fresh-seed three-quarter retry estimate (hfail).

Paper: repair.tex 1054-1084 (lease and a successful worker epoch).
For a fresh genuine hard-S6 seed and horizon
H = 2Cn², every length-H word on which the first attempt has not
succeeded lies in one of two events:

* (A*) a hard S1 occurs before the attempt stops.  On the prefix
  before it the clean-worker pass holds, so no lease reload and no
  stray done occur; the root lease is spent only by counted soft S6,
  each paying n-1 soft-nominated hits.  A hard S1 reads lease zero,
  hence L finishes and at least L(n-1) soft-nominated hits.
* (C*) no hard S1 and no completion: fewer than Cn worker-nominated
  hits (`bankWordPassFreshWorkerHitsBelowQuota`).

The binomial laws give masses at most 1/4 and 1/2, so
4·(unfinished by H) ≤ 3n^H, and absorbing-attempt padding transfers
this to every horizon T.
-/

namespace L3.RenewalReferenceClock

open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! ## Single-attempt words -/

/-- Indicator that a single attempt has NOT succeeded by the end of
the word: it is still active or it has ended in retry.
Consumer: the first-H cover of `bankWordRenewalFreshRetryEstimate`. -/
def bankWordAttemptUnfinished {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    AttemptNode A Seed → List (Fin n) → Nat
  | .success, _ => 0
  | .retry _, _ => 1
  | .active _, [] => 1
  | .active a, e :: w => bankWordAttemptUnfinished K (K.step a e) w

/-- The unfinished indicator is at most one.
Consumer: `bankWordRenewalFreshRetryCover`. -/
theorem bankWordAttemptUnfinishedLeOne {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    ∀ (w : List (Fin n)) (x : AttemptNode A Seed),
      bankWordAttemptUnfinished K x w ≤ 1 := by
  intro w
  induction w with
  | nil =>
      intro x
      cases x <;> simp [bankWordAttemptUnfinished]
  | cons e w ih =>
      intro x
      cases x with
      | active a => exact ih (K.step a e)
      | success => simp [bankWordAttemptUnfinished]
      | retry s => simp [bankWordAttemptUnfinished]

/-- The retry indicator is at most one.
Consumer: `bankWordAttemptRetryLeUnfinishedTake`. -/
theorem bankWordAttemptRetryLeOne {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    ∀ (w : List (Fin n)) (x : AttemptNode A Seed),
      L3.Prob.retryFirstWord K x w ≤ 1 := by
  intro w
  induction w with
  | nil =>
      intro x
      cases x <;> simp [L3.Prob.retryFirstWord]
  | cons e w ih =>
      intro x
      cases x with
      | active a => exact ih (K.step a e)
      | success => simp [L3.Prob.retryFirstWord]
      | retry s => simp [L3.Prob.retryFirstWord]

/-- A retry on a long word means that no prefix has succeeded.
Consumer: the horizon transfer `bankWordAttemptRetryAllHorizons`
(T > H branch). -/
theorem bankWordAttemptRetryLeUnfinishedTake {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    ∀ (w : List (Fin n)) (x : AttemptNode A Seed) (m : Nat),
      L3.Prob.retryFirstWord K x w ≤
        bankWordAttemptUnfinished K x (w.take m) := by
  intro w
  induction w with
  | nil =>
      intro x m
      cases x <;> simp [L3.Prob.retryFirstWord, bankWordAttemptUnfinished]
  | cons e w ih =>
      intro x m
      cases x with
      | success => simp [L3.Prob.retryFirstWord]
      | retry s => simp [L3.Prob.retryFirstWord, bankWordAttemptUnfinished]
      | active a =>
          cases m with
          | zero =>
              have h := bankWordAttemptRetryLeOne K (e :: w) (.active a)
              simpa [bankWordAttemptUnfinished] using h
          | succ m =>
              change L3.Prob.retryFirstWord K (K.step a e) w ≤
                bankWordAttemptUnfinished K (K.step a e) (w.take m)
              exact ih (K.step a e) m

/-- A retry on a prefix persists to the whole word.
Consumer: the horizon transfer `bankWordAttemptRetryAllHorizons`
(T ≤ H branch). -/
theorem bankWordAttemptRetryTakeLeUnfinished {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    ∀ (w : List (Fin n)) (x : AttemptNode A Seed) (m : Nat),
      L3.Prob.retryFirstWord K x (w.take m) ≤
        bankWordAttemptUnfinished K x w := by
  intro w
  induction w with
  | nil =>
      intro x m
      cases x <;> simp [L3.Prob.retryFirstWord, bankWordAttemptUnfinished]
  | cons e w ih =>
      intro x m
      cases x with
      | success => simp [L3.Prob.retryFirstWord]
      | retry s => simp [L3.Prob.retryFirstWord, bankWordAttemptUnfinished]
      | active a =>
          cases m with
          | zero => simp [L3.Prob.retryFirstWord]
          | succ m =>
              change L3.Prob.retryFirstWord K (K.step a e) (w.take m) ≤
                bankWordAttemptUnfinished K (K.step a e) w
              exact ih (K.step a e) m

/-! ## Word-sum arithmetic -/

/-- Additivity of the uniform word sum.
Consumer: `bankWordAttemptUnionQuarter`. -/
private theorem bankWordRetrySumAdd {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat) :
    L3.Prob.scheduleSum n T (fun w => f w + g w) =
      L3.Prob.scheduleSum n T f + L3.Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T (fun w => f w + g w) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun w => f w + g w),
    ← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_add _ _

/-- Monotonicity of the uniform word sum.
Consumer: `bankWordAttemptUnionQuarter` and the horizon transfer. -/
private theorem bankWordRetrySumMono {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat) (h : ∀ w, f w ≤ g w) :
    L3.Prob.scheduleSum n T f ≤ L3.Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T f ≤
    FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_le _ _ (fun i => h _)

/-- Union of a quarter event and a half event: if every unfinished
word is covered by the two events, the unfinished mass is at most
three quarters.  Consumer: `bankWordRenewalFreshRetryEstimate`. -/
theorem bankWordAttemptUnionQuarter {n : Nat} (H : Nat)
    (u fa fb : List (Fin n) → Nat)
    (hcover : ∀ w, u w ≤ fa w + fb w)
    (ha : 4 * L3.Prob.scheduleSum n H fa ≤ n ^ H)
    (hb : 2 * L3.Prob.scheduleSum n H fb ≤ n ^ H) :
    4 * L3.Prob.scheduleSum n H u ≤ 3 * n ^ H := by
  have h1 := bankWordRetrySumMono H u (fun w => fa w + fb w) hcover
  rw [bankWordRetrySumAdd] at h1
  omega

/-- Horizon transfer: a three-quarter bound on the words whose single
attempt is unfinished at one horizon H bounds the retry count at
every horizon.  Short words: a retry persists to length H.  Long
words: a retry implies the attempt was unfinished at H.
Consumer: `bankWordRenewalFreshRetryEstimate`. -/
theorem bankWordAttemptRetryAllHorizons {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (x : AttemptNode A Seed)
    (H : Nat) (hn : 0 < n)
    (hH : 4 * L3.Prob.scheduleSum n H
      (bankWordAttemptUnfinished K x) ≤ 3 * n ^ H)
    (T : Nat) :
    4 * retryCount K x T ≤ 3 * n ^ T := by
  rw [L3.Prob.retryCount_eq_wordSum K x T]
  by_cases hle : T ≤ H
  · obtain ⟨k, hk⟩ : ∃ k, H = T + k := ⟨H - T, by omega⟩
    subst hk
    have hcount := bankWordRenewalFreshPrefixCount T k
      (L3.Prob.retryFirstWord K x)
    have hmono := bankWordRetrySumMono (T + k)
      (fun w => L3.Prob.retryFirstWord K x (w.take T))
      (bankWordAttemptUnfinished K x)
      (fun w => bankWordAttemptRetryTakeLeUnfinished K w x T)
    rw [hcount] at hmono
    have hpow : 0 < n ^ k := Nat.pow_pos hn
    have hmul : n ^ k * (4 * L3.Prob.scheduleSum n T
        (L3.Prob.retryFirstWord K x)) ≤ n ^ k * (3 * n ^ T) := by
      have h3 : 3 * n ^ (T + k) = n ^ k * (3 * n ^ T) := by
        rw [Nat.pow_add, Nat.mul_comm (n ^ T) (n ^ k), Nat.mul_left_comm]
      rw [← h3, Nat.mul_left_comm]
      exact Nat.le_trans (Nat.mul_le_mul_left 4 hmono) hH
    exact Nat.le_of_mul_le_mul_left hmul hpow
  · obtain ⟨k, hk⟩ : ∃ k, T = H + k := ⟨T - H, by omega⟩
    subst hk
    have hcount := bankWordRenewalFreshPrefixCount H k
      (bankWordAttemptUnfinished K x)
    have hmono := bankWordRetrySumMono (H + k)
      (L3.Prob.retryFirstWord K x)
      (fun w => bankWordAttemptUnfinished K x (w.take H))
      (fun w => bankWordAttemptRetryLeUnfinishedTake K w x H)
    rw [hcount] at hmono
    have h3 : 3 * n ^ (H + k) = n ^ k * (3 * n ^ H) := by
      rw [Nat.pow_add, Nat.mul_comm (n ^ H) (n ^ k), Nat.mul_left_comm]
    rw [h3]
    calc 4 * L3.Prob.scheduleSum n (H + k) (L3.Prob.retryFirstWord K x)
        ≤ 4 * (n ^ k * L3.Prob.scheduleSum n H
            (bankWordAttemptUnfinished K x)) :=
          Nat.mul_le_mul_left 4 hmono
      _ = n ^ k * (4 * L3.Prob.scheduleSum n H
            (bankWordAttemptUnfinished K x)) := Nat.mul_left_comm _ _ _
      _ ≤ n ^ k * (3 * n ^ H) := Nat.mul_le_mul_left _ hH

/-! ## Serializer rows at the root -/

/-- A hard S1 is a ROOT_OUT service at a REQUESTED source with zero
lease.  Consumer: the hard-S1 branch of `bankWordRetryPrefixWord`. -/
theorem bankWordRetryHardStartFields {c : Compiled} (x y : ProjW c)
    (h : (serW x y).hard.hardS1 = true) :
    (postW x y).eX.l = true ∧ x.siLease.val = 0 := by
  have h' : ((postW x y).eX.l && (x.ser.cert == .REQUESTED) &&
      (x.siLease.val == 0)) = true := h
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  exact ⟨h'.1.1, h'.2⟩

/-- A ROOT_OUT S1 that is not hard reads a positive lease.
Consumer: the spendable clause of `bankWordRetryRootLeaseStep`. -/
theorem bankWordRetrySoftStartPositive {c : Compiled} (x y : ProjW c)
    (h : (serW x y).hard.hardS1 = false)
    (hx : (postW x y).eX.l = true)
    (hc : x.ser.cert = .REQUESTED) :
    0 < x.siLease.val := by
  have h' : ((postW x y).eX.l && (x.ser.cert == .REQUESTED) &&
      (x.siLease.val == 0)) = false := h
  rw [hx, hc] at h'
  by_cases hz : x.siLease.val = 0
  · simp [hz] at h'
  · omega

/-- ROOT_OUT soft acceptance is exactly the S6 row from a
RUNNING/B/CURRENT/DONE root with a returning child, and it resets the
root to IDLE.  Consumer: `bankWordRetryRootLeaseStep` and the counted
finish branch of `bankWordRetryPrefixStep`. -/
theorem bankWordRetryRootOutSoftAccept {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true) (hy : (postW x y).eY.l = false)
    (ha : (serW x y).hard.softAccept = true) :
    (serW x y).row = "S6" ∧ (serW x y).x.cert = .IDLE ∧
      x.ser.cert = .RUNNING ∧ x.ser.phase = .B ∧
      x.ser.wphase = .CURRENT ∧ x.ser.out = .DONE ∧
      y.ser.phase = .F := by
  have h : ((postW x y).eX.l && (x.ser.cert == .RUNNING) &&
      (x.ser.wphase == .CURRENT) && (x.ser.phase == .B) &&
      (x.ser.out == .DONE) && (y.ser.phase == .F)) = true := ha
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨?_, ?_, h2, h4, h3, h5, h6⟩
  · simp [serW, serializerStep, ProjW.lift, hx, hy, h2, h3, h4, h5, h6]
  · simp [serW, serializerStep, ProjW.lift, hx, hy, h2, h3, h4, h5, h6]

/-- On ROOT_OUT, a RUNNING/CURRENT root after the service was either
REQUESTED (an S1) or already RUNNING/CURRENT (an S2R frame).
Consumer: the spendable clause of `bankWordRetryRootLeaseStep`. -/
theorem bankWordRetryRootOutRunningCurrent {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true) (hy : (postW x y).eY.l = false)
    (h : (serW x y).x.cert = .RUNNING ∧
      (serW x y).x.wphase = .CURRENT) :
    x.ser.cert = .REQUESTED ∨
      (x.ser.cert = .RUNNING ∧ x.ser.wphase = .CURRENT) := by
  cases hc : x.ser.cert with
  | REQUESTED => exact Or.inl rfl
  | IDLE =>
      exfalso
      cases hp : x.ser.phase <;> cases ho : x.ser.out <;>
        cases hq : y.ser.phase <;> cases hpr : y.ser.probe <;>
        simp [serW, serializerStep, ProjW.lift, serTbStar,
          serChallengeWrite, hx, hy, hc, hp, ho, hq, hpr] at h
  | RUNNING =>
      right
      refine ⟨rfl, ?_⟩
      cases hp : x.ser.phase <;> cases ho : x.ser.out <;>
        cases hq : y.ser.phase <;> cases hpr : y.ser.probe <;>
        simp [serW, serializerStep, ProjW.lift, serTbStar,
          serChallengeWrite, hx, hy, hc, hp, ho, hq, hpr] at h <;>
        exact h

/-- On ROOT_IN the responder root's serializer is unchanged except
for IDLE → REQUESTED (S0).  Consumer: the incoming branch of
`bankWordRetryRootLeaseStep`. -/
theorem bankWordRetryRootInRunningCurrent {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false) (hy : (postW x y).eY.l = true)
    (h : (serW x y).y.cert = .RUNNING ∧
      (serW x y).y.wphase = .CURRENT) :
    y.ser.cert = .RUNNING ∧ y.ser.wphase = .CURRENT := by
  cases hc : y.ser.cert <;>
    simp [serW, serializerStep, ProjW.lift, hx, hy, hc] at h <;>
    simp [h]

/-- The lease reducer with no hard acceptance, no soft acceptance and
no done keeps both leases.  Consumer: `bankWordRetryRootLeaseStep`. -/
theorem bankWordRetryLeaseKeep (c : Compiled)
    (a b : Fin (c.siLeaseMax + 1)) :
    (leasePair c a b false false false).1 = a := by
  simp [leasePair]

/-- The lease reducer on soft acceptance without hard acceptance or
done decrements the source lease.  Consumer:
`bankWordRetryRootLeaseStep`. -/
theorem bankWordRetryLeaseSpend (c : Compiled)
    (a b : Fin (c.siLeaseMax + 1)) :
    (leasePair c a b false true false).1.val = a.val - 1 := by
  simp [leasePair]

/-- Without hard acceptance or done the responder lease is kept.
Consumer: the ROOT_IN branch of `bankWordRetryRootLeaseStep`. -/
theorem bankWordRetryLeaseResponder (c : Compiled)
    (a b : Fin (c.siLeaseMax + 1)) (sa : Bool) :
    (leasePair c a b false sa false).2 = b := by
  cases sa <;> simp [leasePair]

/-! ## The hard-epoch ledger on the pass -/

/-- On a service without hard acceptance and without a completion
receipt, the hard-epoch ledger keeps its epoch count and its
workerDone bit, and counts a soft finish exactly at the selected
soft S6.  Consumer: `bankWordRetryPrefixStep`. -/
theorem bankWordRetryLedgerStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hfa : (serW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
      false)
    (hnc : ¬ BankWordRenewalCompleted (bankWordEpochNext ring root z e))
    (hep : 0 < (bankWordHardEpochLedger ring root z).hardEpochs)
    (hwd : (bankWordHardEpochLedger ring root z).workerDone = false) :
    (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).hardEpochs =
      (bankWordHardEpochLedger ring root z).hardEpochs ∧
    (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).workerDone = false ∧
    (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).softFinishes =
      (if bankWordHardEpochSoftFinish root
          (bankWordEpochSelectedReceipt ring z e) = true
        then (bankWordHardEpochLedger ring root z).softFinishes + 1
        else (bankWordHardEpochLedger ring root z).softFinishes) := by
  obtain ⟨_, hwork⟩ :=
    bankWordRenewalFrontierLedgerGhostCoherence ring root s z hz
  have hacc : ∀ gx gy : Option WValidationTicket,
      wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        gx gy = none := by
    intro gx gy
    unfold wGenuineAcceptance
    rw [hfa]
    simp
  have hcomp :
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        none z.2.2.worker).2 = none := by
    have h1 : (bankWordEpochNext ring root z e).2.2.completion = none := by
      cases hc : (bankWordEpochNext ring root z e).2.2.completion with
      | none => rfl
      | some r => exact absurd ⟨r, hc⟩ hnc
    rw [bankWordPassGhostCompletion, hacc] at h1
    exact h1
  have hact : bankWordHardEpochActive
      (bankWordHardEpochLedger ring root z) = true := by
    unfold bankWordHardEpochActive
    rw [hwd]
    have hne : (bankWordHardEpochLedger ring root z).hardEpochs ≠ 0 := by
      omega
    simp [hne]
  rw [bankWordHardEpochLedgerNext]
  refine ⟨?_, ?_, ?_⟩
  · simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt, hacc]
  · simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt, hacc,
      hwd, hwork, hcomp]
  · simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt, hacc,
      hact]
    split <;> simp_all

/-! ## The prefix invariant -/

/-- The prefix invariant of the fresh attempt before its first hard S1:
the clean-worker pass, the rooted soft shape, a live epoch with no
recorded completion, the lease ledger `lease + softFinishes = L`, and
a spendable lease during a soft episode.
Consumer: `bankWordRetryPrefixWord`. -/
def BankWordRetryPrefixInvariant {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s) : Prop :=
  BankWordPassShape ring root z.1 ∧
  BankWordRenewalSoftShape ring root z.1 ∧
  0 < (bankWordHardEpochLedger ring root z.1).hardEpochs ∧
  (bankWordHardEpochLedger ring root z.1).workerDone = false ∧
  (z.1.2.1 root).siLease.val +
      (bankWordHardEpochLedger ring root z.1).softFinishes =
    bankWordRenewalLease n ∧
  ((z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.wphase = .CURRENT →
    0 < (z.1.2.1 root).siLease.val)

/-- The invariant at every actual fresh seed, with zero soft finishes
and zero rooted position.  Consumer: `bankWordRenewalFreshRetryCover`. -/
theorem bankWordRetryPrefixInvariantSeed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRetryPrefixInvariant ring root s seed.1 ∧
    (bankWordHardEpochLedger ring root seed.1.1).softFinishes = 0 ∧
    bankWordRenewalSoftRootedPosition ring root seed.1.1 = 0 := by
  have hfields :=
    bankWordRenewalFreshHardFields ring root s seed.1 seed.2
  have hsoft := bankWordRenewalSoftShapeSeed ring root s hn hbank hs seed
  have hidle :=
    bankWordRenewalFrontierFreshRootIdle ring root s hn hbank hs seed
  have hlease :=
    (bankWordRenewalFrontierFreshBankPrepared ring root s hbank seed).2
  have hv := hfields.2.2.2
  unfold bankWordRenewalHardValid bankWordHardEpochActive at hv
  have hep : 0 < (bankWordHardEpochLedger ring root seed.1.1).hardEpochs := by
    rcases Nat.eq_zero_or_pos
        (bankWordHardEpochLedger ring root seed.1.1).hardEpochs with h0 | h0
    · rw [h0] at hv
      simp at hv
    · exact h0
  have hwd : (bankWordHardEpochLedger ring root seed.1.1).workerDone =
      false := by
    cases hw : (bankWordHardEpochLedger ring root seed.1.1).workerDone with
    | false => rfl
    | true =>
        rw [hw] at hv
        simp at hv
  refine ⟨⟨bankWordPassShapeAtFreshSeed ring hn hbank root s hs seed,
    hsoft.1, hep, hwd, ?_, ?_⟩, hfields.2.1, hsoft.2⟩
  · rw [hlease, hfields.2.1, Nat.add_zero]
  · intro h
    rw [hidle] at h
    cases h.1

/-- The lease ledger and the spendable clause across one service of
the pass that is neither a hard S1 nor a completion.  Remote services
frame the root; ROOT_IN cannot debit the root (its only done is the
completing A0); ROOT_OUT debits exactly at soft acceptance, which is
the counted soft S6.  Consumer: `bankWordRetryPrefixStep`. -/
theorem bankWordRetryRootLeaseStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s) (e : Fin n)
    (hpass : BankWordPassShape ring root z.1)
    (hno : (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1 =
      false)
    (hnc : ¬ BankWordRenewalCompleted (bankWordRenewalNext ring root s z e).1)
    (hfa : (serW (z.1.2.1 e) (z.1.2.1 (ring.rightNeighbor e))).hard.hardAccept =
      false)
    (hfl : (serW (z.1.2.1 e) (z.1.2.1 (ring.rightNeighbor e))).hard.hardLeft =
      false)
    (hfr : (serW (z.1.2.1 e) (z.1.2.1 (ring.rightNeighbor e))).hard.hardRight =
      false)
    (hlease : (z.1.2.1 root).siLease.val +
        (bankWordHardEpochLedger ring root z.1).softFinishes =
      bankWordRenewalLease n)
    (hK : (z.1.2.1 root).ser.cert = .RUNNING ∧
        (z.1.2.1 root).ser.wphase = .CURRENT →
      0 < (z.1.2.1 root).siLease.val)
    (hf : (bankWordHardEpochLedger ring root
        (bankWordRenewalNext ring root s z e).1).softFinishes =
      (if bankWordHardEpochSoftFinish root
          (bankWordEpochSelectedReceipt ring z.1 e) = true
        then (bankWordHardEpochLedger ring root z.1).softFinishes + 1
        else (bankWordHardEpochLedger ring root z.1).softFinishes)) :
    ((bankWordRenewalNext ring root s z e).1.2.1 root).siLease.val +
        (bankWordHardEpochLedger ring root
          (bankWordRenewalNext ring root s z e).1).softFinishes =
      bankWordRenewalLease n ∧
    (((bankWordRenewalNext ring root s z e).1.2.1 root).ser.cert = .RUNNING ∧
        ((bankWordRenewalNext ring root s z e).1.2.1 root).ser.wphase =
          .CURRENT →
      0 < ((bankWordRenewalNext ring root s z e).1.2.1 root).siLease.val) := by
  have hn2 : 2 ≤ n := by omega
  have hne := clockNeighborDifferent ring hn2 e
  rcases bankWordRenewalSoftOwnerFlags ring root s hn hbank hs z e with
    ⟨he, hx, hy⟩ | ⟨he, hpred, hx, hy⟩ | ⟨he, hj, hx, hy⟩
  · -- ROOT_OUT at the root
    have hdone : (workerW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).done = false := by
      cases hd : (workerW (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e))).done with
      | false => rfl
      | true =>
          exfalso
          rcases bankWordPassDoneClassify _ _ hfa hfl hfr hd with h | h
          · have h2 := h.2
            rw [hy] at h2
            cases h2
          · have h2 := h.2.2.2.1
            rw [hy] at h2
            cases h2
    rw [he] at hx hy hfa hdone
    have hrec := bankWordPassSourceRecord ring root z.1 root
    change ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val + _ = _ ∧
      (((bankWordEpochNext ring root z.1 e).2.1 root).ser.cert = .RUNNING ∧
        ((bankWordEpochNext ring root z.1 e).2.1 root).ser.wphase = .CURRENT →
        0 < ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val)
    rw [he] at hf ⊢
    rw [hrec]
    have hleaseEq :
        (pairW (z.1.2.1 root) (z.1.2.1 (ring.rightNeighbor root))).1.siLease =
          (leasePair (compileAdvice (ceilLogTwo n))
            (z.1.2.1 root).siLease
            (z.1.2.1 (ring.rightNeighbor root)).siLease
            (serW (z.1.2.1 root)
              (z.1.2.1 (ring.rightNeighbor root))).hard.hardAccept
            (serW (z.1.2.1 root)
              (z.1.2.1 (ring.rightNeighbor root))).hard.softAccept
            (workerW (z.1.2.1 root)
              (z.1.2.1 (ring.rightNeighbor root))).done).1 := rfl
    rw [hleaseEq, pairW_ser_left, hfa, hdone]
    cases hsa : (serW (z.1.2.1 root)
        (z.1.2.1 (ring.rightNeighbor root))).hard.softAccept with
    | false =>
        have hsf : bankWordHardEpochSoftFinish root
            (bankWordEpochSelectedReceipt ring z.1 root) = false := by
          simp [bankWordHardEpochSoftFinish, bankWordEpochSelectedReceipt, hsa]
        rw [hsf, if_neg (by decide)] at hf
        rw [bankWordRetryLeaseKeep, hf]
        refine ⟨hlease, ?_⟩
        intro hrc
        rcases bankWordRetryRootOutRunningCurrent _ _ hx hy hrc with hreq | hold
        · exact bankWordRetrySoftStartPositive _ _
            (by rw [he] at hno; exact hno) hx hreq
        · exact hK hold
    | true =>
        obtain ⟨hrow, hidle, hrun, _, hcur, _, _⟩ :=
          bankWordRetryRootOutSoftAccept _ _ hx hy hsa
        have hsf : bankWordHardEpochSoftFinish root
            (bankWordEpochSelectedReceipt ring z.1 root) = true := by
          have h' : ((root == root) &&
              ((serW (z.1.2.1 root) (z.1.2.1 (ring.rightNeighbor root))).row ==
                "S6") &&
              (serW (z.1.2.1 root)
                (z.1.2.1 (ring.rightNeighbor root))).hard.softAccept) = true := by
            rw [hrow, hsa]
            simp
          exact h'
        rw [hsf, if_pos rfl] at hf
        have hpos := hK ⟨hrun, hcur⟩
        rw [bankWordRetryLeaseSpend, hf]
        refine ⟨by omega, ?_⟩
        intro hrc
        rw [hidle] at hrc
        cases hrc.1
  · -- ROOT_IN: the root is the responder
    have hdone : (workerW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).done = false := by
      cases hd : (workerW (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e))).done with
      | false => rfl
      | true =>
          exact absurd
            (bankWordPassIncomingDoneCompletes ring hn hbank root s hs
              z.1 z.2.1 hpass e hpred hno hd) hnc
    have hsf : bankWordHardEpochSoftFinish root
        (bankWordEpochSelectedReceipt ring z.1 e) = false := by
      simp [bankWordHardEpochSoftFinish, bankWordEpochSelectedReceipt, he]
    rw [hsf, if_neg (by decide)] at hf
    have hrec := bankWordPassTargetRecord ring root z.1 e hne
    rw [hpred] at hrec hx hy hfa hdone
    change ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val + _ = _ ∧
      (((bankWordEpochNext ring root z.1 e).2.1 root).ser.cert = .RUNNING ∧
        ((bankWordEpochNext ring root z.1 e).2.1 root).ser.wphase = .CURRENT →
        0 < ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val)
    rw [hrec, hf]
    have hleaseEq :
        (pairW (z.1.2.1 e) (z.1.2.1 root)).2.siLease =
          (leasePair (compileAdvice (ceilLogTwo n))
            (z.1.2.1 e).siLease (z.1.2.1 root).siLease
            (serW (z.1.2.1 e) (z.1.2.1 root)).hard.hardAccept
            (serW (z.1.2.1 e) (z.1.2.1 root)).hard.softAccept
            (workerW (z.1.2.1 e) (z.1.2.1 root)).done).2 := rfl
    rw [hleaseEq, pairW_ser_right, hfa, hdone, bankWordRetryLeaseResponder]
    refine ⟨hlease, ?_⟩
    intro hrc
    exact hK (bankWordRetryRootInRunningCurrent _ _ hx hy hrc)
  · -- remote service: the root record and the counter frame
    have hsf : bankWordHardEpochSoftFinish root
        (bankWordEpochSelectedReceipt ring z.1 e) = false := by
      simp [bankWordHardEpochSoftFinish, bankWordEpochSelectedReceipt, he]
    rw [hsf, if_neg (by decide)] at hf
    have hrec := bankWordPassRemoteRecord ring root z.1 e root
      (fun h => he h.symm) (fun h => hj h.symm)
    change ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val + _ = _ ∧
      (((bankWordEpochNext ring root z.1 e).2.1 root).ser.cert = .RUNNING ∧
        ((bankWordEpochNext ring root z.1 e).2.1 root).ser.wphase = .CURRENT →
        0 < ((bankWordEpochNext ring root z.1 e).2.1 root).siLease.val)
    rw [hrec, hf]
    exact ⟨hlease, hK⟩

/-- One service of the fresh attempt before its first hard S1 that does
not complete the worker: it is not a genuine retry, the prefix invariant
persists, and the soft potential `(n-1)·finishes + position` grows by at
most the soft-nomination hit.  Consumer: `bankWordRetryPrefixWord`. -/
theorem bankWordRetryPrefixStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s) (e : Fin n)
    (hI : BankWordRetryPrefixInvariant ring root s z)
    (hno : (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1 =
      false)
    (hnc : ¬ BankWordRenewalCompleted (bankWordRenewalNext ring root s z e).1) :
    ¬ bankWordRenewalGenuine ring root z.1 e ∧
    BankWordRetryPrefixInvariant ring root s (bankWordRenewalNext ring root s z e) ∧
    (n - 1) * (bankWordHardEpochLedger ring root
        (bankWordRenewalNext ring root s z e).1).softFinishes +
      bankWordRenewalSoftRootedPosition ring root
        (bankWordRenewalNext ring root s z e).1 ≤
    (n - 1) * (bankWordHardEpochLedger ring root z.1).softFinishes +
      bankWordRenewalSoftRootedPosition ring root z.1 +
      (if e = bankWordRenewalSoftRootedChosen ring root s z then 1 else 0) := by
  obtain ⟨hpass, hsoft, hep, hwd, hlease, hK⟩ := hI
  obtain ⟨hfa, hfl, hfr⟩ := bankWordPassFlagsQuiet (z.1.2.1 e)
    (z.1.2.1 (ring.rightNeighbor e)) (hpass.1 e) (hpass.1 _) hno
  have hgen : ¬ bankWordRenewalGenuine ring root z.1 e := by
    intro hg
    unfold bankWordRenewalGenuine bankWordHardEpochGenuine at hg
    simp [wGenuineAcceptance, bankWordEpochSelectedReceipt, hfa] at hg
  have hstep := bankWordPassStep ring hn hbank root s hs z.1 z.2.1 e hpass hno
  have hpass' : BankWordPassShape ring root
      (bankWordRenewalNext ring root s z e).1 := by
    by_cases hnom : e = bankWordPassNomination ring root z.1
    · rcases hstep.2 hnom with h | h
      · exact h.1
      · exact absurd h.2.2.1 hnc
    · exact (hstep.1 hnom).1
  have hsoft' :=
    (bankWordRenewalSoftShapeStep ring root s hn hbank hs z e hsoft).1
  obtain ⟨hep0, hwd0, hf0⟩ :=
    bankWordRetryLedgerStep ring root s z.1 z.2.1 e hfa hnc hep hwd
  have hep' : 0 < (bankWordHardEpochLedger ring root
      (bankWordRenewalNext ring root s z e).1).hardEpochs :=
    Nat.lt_of_lt_of_eq hep hep0.symm
  have hwd' : (bankWordHardEpochLedger ring root
      (bankWordRenewalNext ring root s z e).1).workerDone = false := hwd0
  have hf : (bankWordHardEpochLedger ring root
      (bankWordRenewalNext ring root s z e).1).softFinishes =
      (if bankWordHardEpochSoftFinish root
          (bankWordEpochSelectedReceipt ring z.1 e) = true
        then (bankWordHardEpochLedger ring root z.1).softFinishes + 1
        else (bankWordHardEpochLedger ring root z.1).softFinishes) := hf0
  have hLK := bankWordRetryRootLeaseStep ring hn hbank root s hs z e hpass
    hno hnc hfa hfl hfr hlease hK hf
  have hhit := bankWordRenewalSoftRootedPositionHitStep
    ring root s hn hbank hs z e hsoft
  refine ⟨hgen, ⟨hpass', hsoft', hep', hwd', hLK.1, hLK.2⟩,
    ?_⟩
  cases hsf : bankWordHardEpochSoftFinish root
      (bankWordEpochSelectedReceipt ring z.1 e) with
  | false =>
      rw [hsf, if_neg (by decide)] at hf
      rw [hf]
      omega
  | true =>
      rw [hsf, if_pos rfl] at hf
      have hsf' : ((e == root) &&
          ((serW (z.1.2.1 e) (z.1.2.1 (ring.rightNeighbor e))).row == "S6") &&
          (serW (z.1.2.1 e)
            (z.1.2.1 (ring.rightNeighbor e))).hard.softAccept) = true := hsf
      simp only [Bool.and_eq_true, beq_iff_eq] at hsf'
      obtain ⟨⟨he, _⟩, hsa⟩ := hsf'
      rw [he] at hsa hf ⊢
      obtain ⟨hx, hy⟩ := bankWordRenewalSoftOutgoingFlags ring root s hn hbank hs z
      obtain ⟨_, _, hrun, hb, hcur, hout, hchild⟩ :=
        bankWordRetryRootOutSoftAccept _ _ hx hy hsa
      have hret := bankWordRenewalFreshSoftEpisodePairing ring root s z hsoft
        hrun hb hcur hout hchild
      obtain ⟨_, hpos', hpos, _, _⟩ :=
        bankWordRenewalSoftRootOutgoingFinishStep ring root s z hn hret hx hy
      change (n - 1) * (bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root z.1 root)).softFinishes +
        bankWordRenewalSoftRootedPosition ring root
          (bankWordEpochNext ring root z.1 root) ≤ _
      rw [hpos', hpos]
      change (n - 1) * (bankWordHardEpochLedger ring root
          (bankWordRenewalNext ring root s z root).1).softFinishes + 0 ≤ _
      rw [hf, Nat.mul_add, Nat.mul_one]
      omega

/-! ## The word cover -/

/-- Along any word from a state satisfying the prefix invariant, if
the fresh attempt has not succeeded by the end of the word, then
either no hard S1 occurred and the pass did not complete, or the soft
potential has reached L(n-1): a hard S1 reads lease zero, so all L
soft finishes were counted, each paid by n-1 soft-nominated hits.
Consumer: `bankWordRenewalFreshRetryCover`. -/
theorem bankWordRetryPrefixWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s) :
    ∀ (w : List (Fin n)) (z : BankWordRenewalPostSOne ring root s),
      BankWordRetryPrefixInvariant ring root s z →
      bankWordAttemptUnfinished (bankWordRenewalFreshKernel ring root s)
        (.active z) w = 1 →
      (BankWordPassNoHardStart ring root z.1 w ∧
          ¬ BankWordPassCompletes ring root z.1 w) ∨
        (n - 1) * bankWordRenewalLease n ≤
          (n - 1) * (bankWordHardEpochLedger ring root z.1).softFinishes +
            bankWordRenewalSoftRootedPosition ring root z.1 +
            grantDrainLabelHits (bankWordRenewalNext ring root s)
              (bankWordRenewalSoftRootedChosen ring root s) z w := by
  intro w
  induction w with
  | nil =>
      intro z _ _
      exact Or.inl ⟨trivial, fun h => h⟩
  | cons e es ih =>
      intro z hI hU
      by_cases hhard :
          (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1 = true
      · right
        have hfields := bankWordRetryHardStartFields (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e)) hhard
        have he : e = root := by
          rcases bankWordRenewalSoftOwnerFlags ring root s hn hbank hs z e with
            ⟨he, _, _⟩ | ⟨_, _, hx, _⟩ | ⟨_, _, hx, _⟩
          · exact he
          · rw [hfields.1] at hx
            cases hx
          · rw [hfields.1] at hx
            cases hx
        have hzero := hfields.2
        rw [he] at hzero
        have hfL : (bankWordHardEpochLedger ring root z.1).softFinishes =
            bankWordRenewalLease n := by
          have := hI.2.2.2.2.1
          omega
        rw [hfL]
        omega
      · have hno :
            (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1 =
              false := by
          cases hb : (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1
          · rfl
          · exact absurd hb hhard
        change bankWordAttemptUnfinished (bankWordRenewalFreshKernel ring root s)
          (bankWordRenewalFreshStep ring root s z e) es = 1 at hU
        by_cases hd : BankWordRenewalCompleted
            (bankWordRenewalNext ring root s z e).1
        · exfalso
          have hst : bankWordRenewalFreshStep ring root s z e = .success := by
            simp [bankWordRenewalFreshStep, hd]
          rw [hst] at hU
          simp [bankWordAttemptUnfinished] at hU
        · obtain ⟨hg, hI', hpot⟩ :=
            bankWordRetryPrefixStep ring hn hbank root s hs z e hI hno hd
          have hst : bankWordRenewalFreshStep ring root s z e =
              .active (bankWordRenewalNext ring root s z e) := by
            simp [bankWordRenewalFreshStep, hd, hg]
          rw [hst] at hU
          rcases ih _ hI' hU with ⟨hnh, hnc⟩ | hq
          · left
            refine ⟨(And.intro hno hnh :
              BankWordPassNoHardStart ring root z.1 (e :: es)), ?_⟩
            intro hc
            rcases hc with hr | hc
            · exact hd hr.2.2.1
            · exact hnc hc
          · right
            change _ ≤ _ + _ +
              ((if e = bankWordRenewalSoftRootedChosen ring root s z then 1 else 0) +
                grantDrainLabelHits (bankWordRenewalNext ring root s)
                  (bankWordRenewalSoftRootedChosen ring root s)
                  (bankWordRenewalNext ring root s z e) es)
            omega

/-- Worker hits on the post-S1 subtype equal worker hits on the
underlying epoch chain.  Consumer: `bankWordRenewalFreshRetryCover`. -/
theorem bankWordRetryHitsProjection {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (f : BankWordEpochState n → Fin n) :
    ∀ (w : List (Fin n)) (z : BankWordRenewalPostSOne ring root s),
      grantDrainLabelHits (bankWordRenewalNext ring root s)
          (fun v => f v.1) z w =
        grantDrainLabelHits (bankWordEpochNext ring root) f z.1 w := by
  intro w
  induction w with
  | nil => intro z; rfl
  | cons e es ih =>
      intro z
      change (if e = f z.1 then 1 else 0) +
          grantDrainLabelHits (bankWordRenewalNext ring root s)
            (fun v => f v.1) (bankWordRenewalNext ring root s z e) es =
        (if e = f z.1 then 1 else 0) +
          grantDrainLabelHits (bankWordEpochNext ring root) f
            (bankWordEpochNext ring root z.1 e) es
      rw [ih]
      rfl

/-- The pointwise first-H cover at an actual fresh seed: an unfinished
attempt has at least L(n-1) soft-nominated hits (A*) or fewer than Cn
worker-nominated hits (C*).  Consumer:
`bankWordRenewalFreshRetryEstimate`. -/
theorem bankWordRenewalFreshRetryCover {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (w : List (Fin n)) :
    bankWordAttemptUnfinished (bankWordRenewalFreshKernel ring root s)
        (.active seed.1) w ≤
      (if bankWordRenewalLease n * (n - 1) ≤
          grantDrainLabelHits (bankWordRenewalNext ring root s)
            (bankWordRenewalSoftRootedChosen ring root s) seed.1 w
        then 1 else 0) +
      (if grantDrainLabelHits (bankWordRenewalNext ring root s)
            (fun v => bankWordPassNomination ring root v.1) seed.1 w <
          bankWordRenewalWorkerQuota n * n
        then 1 else 0) := by
  have hle := bankWordAttemptUnfinishedLeOne
    (bankWordRenewalFreshKernel ring root s) w (.active seed.1)
  by_cases hU : bankWordAttemptUnfinished
      (bankWordRenewalFreshKernel ring root s) (.active seed.1) w = 1
  · obtain ⟨hI, hf0, hp0⟩ :=
      bankWordRetryPrefixInvariantSeed ring hn hbank root s hs seed
    rcases bankWordRetryPrefixWord ring hn hbank root s hs w seed.1 hI hU with
      ⟨hnh, hnc⟩ | hq
    · have hb := bankWordPassFreshWorkerHitsBelowQuota
        ring hn hbank root s hs seed w hnh hnc
      rw [← bankWordRetryHitsProjection ring root s
        (bankWordPassNomination ring root) w seed.1] at hb
      have ht : (compileAdvice (ceilLogTwo n)).t =
          ceilLogTwo (ceilLogTwo n) :=
        compileAdvice_t_large _ (by have := bankRepairBankBand hbank; omega)
      rw [ht] at hb
      have hb' : grantDrainLabelHits (bankWordRenewalNext ring root s)
            (fun v => bankWordPassNomination ring root v.1) seed.1 w <
          bankWordRenewalWorkerQuota n * n := hb
      rw [if_pos hb']
      omega
    · rw [hf0, hp0] at hq
      have hq' : bankWordRenewalLease n * (n - 1) ≤
          grantDrainLabelHits (bankWordRenewalNext ring root s)
            (bankWordRenewalSoftRootedChosen ring root s) seed.1 w := by
        rw [Nat.mul_comm]
        simpa using hq
      rw [if_pos hq']
      omega
  · omega

/-! ## The three-quarter retry estimate -/

/-- R10 hfail at every actual fresh seed: four times the number of
words on which the fresh first attempt has ended in a genuine retry by
T is at most 3 n^T, for every horizon T.  This is exactly the hfail
premise of `bankWordRenewalFreshFourCostHoldsOfFailure`.
Consumer: `bankWordRenewalFreshFourCostHolds`. -/
theorem bankWordRenewalFreshRetryEstimate {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s) :
    ∀ seed : BankWordRenewalFreshSeed ring root s, ∀ T,
      4 * PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s) (.active seed.1) T ≤
        3 * n ^ T := by
  intro seed T
  have hn0 : 0 < n := by omega
  apply bankWordAttemptRetryAllHorizons _ _ (bankWordRenewalHorizon n) hn0 _ T
  apply bankWordAttemptUnionQuarter (bankWordRenewalHorizon n) _ _ _
    (bankWordRenewalFreshRetryCover ring hn hbank root s hs seed)
  · rw [bankWordRenewalNominatedUpperTailLaw (bankWordRenewalNext ring root s)
      (bankWordRenewalSoftRootedChosen ring root s) seed.1
      (bankWordRenewalHorizon n) (bankWordRenewalLease n * (n - 1)) hn0]
    exact L3.BinomialUpperTail.bankUpperBankBandInterruptionQuarter n hbank
  · exact bankWordRenewalWorkerNominationHalf ring root s seed.1
      (fun v => bankWordPassNomination ring root v.1) hn0

/-- The fresh genuine completion costs at most four blocks, with no
remaining premise: hcost is `bankWordRenewalFreshAttemptCostHolds` and
hfail is `bankWordRenewalFreshRetryEstimate`.
Consumer: the 1B + 4B staging budget of the R10 W projected clock. -/
theorem bankWordRenewalFreshFourCostHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      seed.1 T ≤ n ^ T * (4 * bankWordRenewalBlock n) :=
  bankWordRenewalFreshFourCostHoldsOfFailure ring hn hbank root s hs
    (bankWordRenewalFreshRetryEstimate ring hn hbank root s hs) seed T

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordAttemptRetryAllHorizons
#print axioms L3.RenewalReferenceClock.bankWordRetryLedgerStep
#print axioms L3.RenewalReferenceClock.bankWordRetryRootLeaseStep
#print axioms L3.RenewalReferenceClock.bankWordRetryPrefixStep
#print axioms L3.RenewalReferenceClock.bankWordRetryPrefixWord
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshRetryCover
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshRetryEstimate
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshFourCostHolds

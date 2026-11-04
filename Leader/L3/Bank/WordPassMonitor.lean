import Leader.L3.Bank.WordPassValues
import Leader.L3.Bank.WordRenewalRetryClock

/-!
# R10 W: completion provenance and the monitor coupling

Every reachable completion of the original projected W epoch is the
first completion of a no-hard-S1 scheduler word from an actual fresh
seed (the successor of the last genuine hard S6 / worker launch), so
the clean-worker pass of BankWordPass / BankWordPassValues applies to
it: the completed visible word satisfies CleanWorkerWordValues and
every SI is free.  Consumer: the hcompletion premise of
bankWordProjectedClockOfCompletionBridge (BankWordRenewalRetryClock).
-/

namespace L3.RenewalReferenceClock

open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-! ## Ghost receipt inversions -/

/-- A live ghost worker after one service is either a fresh I0
launch or the continuation of the previous live worker on a service
without hard S1. Consumer: bankWordEpochLiveTrailStep. -/
theorem bankWordPassGhostWorkerSomeCases {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket)
    (old : Option (WWorkerTrail n)) (w' : WWorkerTrail n)
    (h : (wWorkerReceiptStep root edge next clock x y accept old).1 =
      some w') :
    ((workerW x y).row = "I0" ∧ ∃ t, accept = some t) ∨
      ((workerW x y).row ≠ "I0" ∧
        (serW x y).hard.hardS1 = false ∧
        ∃ w : WWorkerTrail n, old = some w) := by
  by_cases hi : (workerW x y).row = "I0"
  · left
    refine ⟨hi, ?_⟩
    cases ha : accept with
    | none =>
        rw [ha] at h
        simp [wWorkerReceiptStep, hi] at h
    | some t => exact ⟨t, rfl⟩
  · right
    refine ⟨hi, ?_⟩
    cases hs : (serW x y).hard.hardS1
    · cases ho : old with
      | none =>
          rw [ho] at h
          simp [wWorkerReceiptStep, hi, hs] at h
      | some w => exact ⟨rfl, w, rfl⟩
    · simp [wWorkerReceiptStep, hi, hs] at h

/-- A ghost receipt never carries both a live worker and a
completion. Consumer: bankWordPassGhostCompletionCases. -/
theorem bankWordPassGhostReceiptExclusive {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket)
    (old : Option (WWorkerTrail n)) :
    (wWorkerReceiptStep root edge next clock x y accept old).2 = none ∨
      (wWorkerReceiptStep root edge next clock x y accept old).1 =
        none := by
  have key : ∀ {q : Prop} [Decidable q]
      (a b : Option (WWorkerTrail n) × Option (WCompletionReceipt n)),
      (a.2 = none ∨ a.1 = none) → (b.2 = none ∨ b.1 = none) →
      ((if q then a else b).2 = none ∨ (if q then a else b).1 = none) := by
    intro q _ a b ha hb
    by_cases hq : q
    · rw [if_pos hq]
      exact ha
    · rw [if_neg hq]
      exact hb
  cases accept <;> cases old <;> unfold wWorkerReceiptStep <;>
    dsimp only <;>
    repeat' (first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | apply key)

/-- A completion receipt is written only by a service without hard
S1 on a live old worker, and it retires that worker.
Consumer: bankWordEpochCompletedClean. -/
theorem bankWordPassGhostCompletionCases {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket)
    (old : Option (WWorkerTrail n)) (r : WCompletionReceipt n)
    (h : (wWorkerReceiptStep root edge next clock x y accept old).2 =
      some r) :
    (wWorkerReceiptStep root edge next clock x y accept old).1 = none ∧
      (serW x y).hard.hardS1 = false ∧
      ∃ w : WWorkerTrail n, old = some w := by
  have hexcl := bankWordPassGhostReceiptExclusive
    root edge next clock x y accept old
  have hnone :
      (wWorkerReceiptStep root edge next clock x y accept old).1 =
        none := by
    rcases hexcl with h2 | h1
    · rw [h2] at h
      cases h
    · exact h1
  by_cases hi : (workerW x y).row = "I0"
  · exfalso
    cases ha : accept with
    | none =>
        rw [ha] at h
        simp [wWorkerReceiptStep, hi] at h
    | some t =>
        rw [ha] at h
        simp [wWorkerReceiptStep, hi] at h
  · cases hs : (serW x y).hard.hardS1
    · cases ho : old with
      | none =>
          exfalso
          rw [ho] at h
          simp [wWorkerReceiptStep, hi, hs] at h
      | some w =>
          rw [ho] at hnone
          exact ⟨hnone, rfl, w, rfl⟩
    · exfalso
      simp [wWorkerReceiptStep, hi, hs] at h

/-! ## Live trails along a word -/

/-- The ghost worker is live after every letter of the word.
Consumer: bankWordPassCleanAtLastLetter. -/
def BankWordPassLive {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankWordEpochState n → List (Fin n) → Prop
  | _, [] => True
  | z, e :: es =>
      (∃ w : WWorkerTrail n,
        (bankWordEpochNext ring root z e).2.2.worker = some w) ∧
      BankWordPassLive ring root (bankWordEpochNext ring root z e) es

/-- Consumer: bankWordEpochLiveTrailStep. -/
theorem bankWordPassLiveSnoc {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankWordEpochState n) (e : Fin n),
      BankWordPassLive ring root z word →
      (∃ w : WWorkerTrail n,
        (bankWordEpochNext ring root
          (bankWordEpochRun ring root z word) e).2.2.worker = some w) →
      BankWordPassLive ring root z (word ++ [e]) := by
  intro word
  induction word with
  | nil =>
      intro z e _ hw
      exact ⟨hw, trivial⟩
  | cons f es ih =>
      intro z e hlive hw
      exact ⟨hlive.1, ih _ e hlive.2 hw⟩

/-- Consumer: bankWordEpochLiveTrailStep. -/
theorem bankWordPassNoHardStartSnoc {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankWordEpochState n) (e : Fin n),
      BankWordPassNoHardStart ring root z word →
      (bankWordEpochSelectedReceipt ring
        (bankWordEpochRun ring root z word) e).serializer.hard.hardS1 =
          false →
      BankWordPassNoHardStart ring root z (word ++ [e]) := by
  intro word
  induction word with
  | nil =>
      intro z e _ hno
      exact ⟨hno, trivial⟩
  | cons f es ih =>
      intro z e hnh hno
      exact ⟨hnh.1, ih _ e hnh.2 hno⟩

/-- The label run of the pass is the epoch run.
Consumer: bankWordEpochCompletedClean. -/
theorem bankWordPassLabelRunEq {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankWordEpochState n),
      L3.GrantDrainEntrance.grantDrainLabelRun
          (bankWordEpochNext ring root) z word =
        bankWordEpochRun ring root z word := by
  intro word
  induction word with
  | nil => intro z; rfl
  | cons e es ih =>
      intro z
      exact ih (bankWordEpochNext ring root z e)

/-- If the trail is live after every letter of `word`, the first
clean completion along `word ++ [e]` is its last letter.
Consumer: bankWordEpochCompletedClean. -/
theorem bankWordPassCleanAtLastLetter {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankWordEpochState n) (e : Fin n),
      BankWordPassLive ring root z word →
      BankWordPassCleanCompletes ring root z (word ++ [e]) →
      BankWordPassRetired ring root
          (bankWordEpochRun ring root z (word ++ [e])) ∧
        CleanWorkerWordValues ring root
          (bankWordEpochRun ring root z (word ++ [e])).2.1 := by
  intro word
  induction word with
  | nil =>
      intro z e _ hc
      have hc' :
          (BankWordPassRetired ring root
              (bankWordEpochNext ring root z e) ∧
            CleanWorkerWordValues ring root
              (bankWordEpochNext ring root z e).2.1) ∨
          (¬ BankWordPassRetired ring root
              (bankWordEpochNext ring root z e) ∧ False) := hc
      rcases hc' with h | h
      · exact h
      · exact False.elim h.2
  | cons f es ih =>
      intro z e hlive hc
      have hc' :
          (BankWordPassRetired ring root
              (bankWordEpochNext ring root z f) ∧
            CleanWorkerWordValues ring root
              (bankWordEpochNext ring root z f).2.1) ∨
          (¬ BankWordPassRetired ring root
              (bankWordEpochNext ring root z f) ∧
            BankWordPassCleanCompletes ring root
              (bankWordEpochNext ring root z f) (es ++ [e])) := hc
      rcases hc' with h | h
      · exfalso
        obtain ⟨w, hw⟩ := hlive.1
        rw [h.1.2.1] at hw
        cases hw
      · exact ih _ e hlive.2 h.2

/-! ## Every live trail comes from the last fresh seed -/

/-- The live-trail provenance predicate: a live ghost worker is the
trail of an actual fresh seed, reached along a no-hard-S1 word on
which the trail stayed live. Consumer: bankWordEpochCompletedClean. -/
def BankWordEpochLiveFromSeed {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n) : Prop :=
  ∀ w : WWorkerTrail n, z.2.2.worker = some w →
    ∃ (seed : BankWordRenewalFreshSeed ring root s)
      (word : List (Fin n)),
      bankWordEpochRun ring root seed.1.1 word = z ∧
      BankWordPassNoHardStart ring root seed.1.1 word ∧
      BankWordPassLive ring root seed.1.1 word

/-- One service keeps the provenance: a fresh I0 launch starts a new
seed (the launch is genuine by ledger/ghost coherence and comes after
the first S1); otherwise the old trail continues without hard S1.
Consumer: bankWordEpochLiveFromSeedReachable. -/
theorem bankWordEpochLiveTrailStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hlive : BankWordEpochLiveFromSeed ring root s z)
    (e : Fin n) :
    BankWordEpochLiveFromSeed ring root s
      (bankWordEpochNext ring root z e) := by
  intro w' hw'
  have hw'' :
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        z.2.2.worker).1 = some w' := hw'
  rcases bankWordPassGhostWorkerSomeCases _ _ _ _ _ _ _ _ w' hw'' with
    ⟨_, t, ht⟩ | ⟨_, hno, w, hw⟩
  · have hcoh :=
      (bankWordRenewalFrontierLedgerGhostCoherence
        ring root s z hz).1
    have hg : bankWordRenewalGenuine ring root z e := by
      unfold bankWordRenewalGenuine bankWordHardEpochGenuine
      change
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).isSome = true
      rw [hcoh, ht] <;> rfl
    have hone :=
      bankWordEpochSOneReachedOfGenuine ring hn hbank root s hs z hz e hg
    let pre : BankWordRenewalPostSOne ring root s := ⟨z, hz, hone⟩
    let seed : BankWordRenewalFreshSeed ring root s :=
      ⟨bankWordRenewalNext ring root s pre e,
        bankWordRenewalFreshAfterGenuine ring root s pre e hg⟩
    exact ⟨seed, [], rfl, trivial, trivial⟩
  · obtain ⟨seed, word, hrun, hnh, hl⟩ := hlive w hw
    refine ⟨seed, word ++ [e], ?_, ?_, ?_⟩
    · rw [bankWordEpochRunAppend, hrun]
      rfl
    · apply bankWordPassNoHardStartSnoc ring root word seed.1.1 e hnh
      rw [hrun]
      exact hno
    · apply bankWordPassLiveSnoc ring root word seed.1.1 e hl
      rw [hrun]
      exact ⟨w', hw'⟩

/-- Every reachable epoch state satisfies the live-trail provenance.
Consumer: bankWordEpochCompletedClean. -/
theorem bankWordEpochLiveFromSeedReachable {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordEpochLiveFromSeed ring root s z := by
  have hall : ∀ (word : List (Fin n)) (a : BankWordEpochState n),
      BankWordEpochReachable ring root s a →
      BankWordEpochLiveFromSeed ring root s a →
      BankWordEpochLiveFromSeed ring root s
        (bankWordEpochRun ring root a word) := by
    intro word
    induction word with
    | nil => intro a _ h; exact h
    | cons e es ih =>
        intro a ha h
        exact ih _ (bankWordEpochReachableNext ring root s a ha e)
          (bankWordEpochLiveTrailStep ring hn hbank root s hs a ha h e)
  obtain ⟨word, hword⟩ := hz
  have hbase : BankWordEpochLiveFromSeed ring root s
      (bankWordEpochStart s) := by
    intro w hw
    cases hw
  rw [← hword]
  exact hall word (bankWordEpochStart s) ⟨[], rfl⟩ hbase

/-! ## Item 1: every reachable completion is a clean first completion -/

/-- Every reachable completed state of the original projected W
epoch is the first completion of a no-hard-S1 word from an actual
fresh seed; hence (every compiled width) its visible word
satisfies CleanWorkerWordValues and every SI is free.
Consumer: the hcompletion premise of
bankWordProjectedClockOfCompletionBridge (QWord base and monitor
endpoint of BankWordProjectedTarget). -/
theorem bankWordEpochCompletedClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcomp : BankWordRenewalCompleted z) :
    CleanWorkerWordValues ring root z.2.1 ∧
      ∀ i : Fin n, freeSI (z.2.1 i).si = true := by
  obtain ⟨word, hword⟩ := hz
  obtain ⟨r, hr⟩ := hcomp
  -- split off the completing letter
  cases hrev : word.reverse with
  | nil =>
      have hnil : word = [] := List.reverse_eq_nil_iff.mp hrev
      subst hnil
      rw [← hword] at hr
      cases hr
  | cons e rest =>
      have hsplit : word = rest.reverse ++ [e] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst hsplit
      rw [bankWordEpochRunAppend] at hword
      let y := bankWordEpochRun ring root (bankWordEpochStart s)
        rest.reverse
      have hy : BankWordEpochReachable ring root s y :=
        ⟨rest.reverse, rfl⟩
      have hzy : bankWordEpochNext ring root y e = z := hword
      have hr' :
          (wWorkerReceiptStep root e (ring.rightNeighbor e)
            (y.2.2.clock + 1)
            (y.2.1 e) (y.2.1 (ring.rightNeighbor e))
            (wGenuineAcceptance root e
              (y.2.1 e) (y.2.1 (ring.rightNeighbor e))
              (y.2.2.validation e)
              (y.2.2.validation (ring.rightNeighbor e)))
            y.2.2.worker).2 = some r := by
        have h2 : (bankWordEpochNext ring root y e).2.2.completion =
            some r := by
          rw [hzy]
          exact hr
        exact h2
      obtain ⟨hnone, hno, w, hw⟩ :=
        bankWordPassGhostCompletionCases _ _ _ _ _ _ _ _ r hr'
      obtain ⟨seed, word0, hrun, hnh, hl⟩ :=
        bankWordEpochLiveFromSeedReachable ring hn hbank root s hs y hy
          w hw
      have hnh' : BankWordPassNoHardStart ring root seed.1.1
          (word0 ++ [e]) := by
        apply bankWordPassNoHardStartSnoc ring root word0 seed.1.1 e hnh
        rw [hrun]
        exact hno
      have hend :
          bankWordEpochRun ring root seed.1.1 (word0 ++ [e]) = z := by
        rw [bankWordEpochRunAppend, hrun]
        exact hzy
      have hworkerNone : z.2.2.worker = none := by
        have h2 : (bankWordEpochNext ring root y e).2.2.worker = none :=
          hnone
        rw [hzy] at h2
        exact h2
      rcases bankWordPassValuesRun ring hn hbank root s hs
          (word0 ++ [e]) seed.1.1 seed.1.2.1
          (bankWordPassShapeAtFreshSeed ring hn hbank root s hs seed)
          (bankWordPassValuesBase ring hn hbank root s hs seed) hnh' with
        ⟨hshape, _, _⟩ | hclean
      · exfalso
        rw [bankWordPassLabelRunEq, hend] at hshape
        obtain ⟨v, hv, _⟩ := hshape.2.1
        rw [hworkerNone] at hv
        cases hv
      · obtain ⟨hret, hcw⟩ :=
          bankWordPassCleanAtLastLetter ring root word0 seed.1.1 e hl hclean
        rw [hend] at hret hcw
        exact ⟨hcw, hret.2.2.2⟩

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordPassGhostWorkerSomeCases
#print axioms L3.RenewalReferenceClock.bankWordPassGhostReceiptExclusive
#print axioms L3.RenewalReferenceClock.bankWordPassGhostCompletionCases
#print axioms L3.RenewalReferenceClock.bankWordPassCleanAtLastLetter
#print axioms L3.RenewalReferenceClock.bankWordEpochLiveTrailStep
#print axioms L3.RenewalReferenceClock.bankWordEpochLiveFromSeedReachable
#print axioms L3.RenewalReferenceClock.bankWordEpochCompletedClean

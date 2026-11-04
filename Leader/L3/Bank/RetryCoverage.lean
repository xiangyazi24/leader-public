import Leader.L3.RenewalReferenceClock

namespace L3.BankRetryCoverage

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open PPL.Convergence.LDLocal (AttemptNode RetryKernel)

set_option autoImplicit false
set_option Elab.async false

/-! The literal source, kernel, and event belong to the valid BANK
reference. No new transition or independent scheduler is introduced. -/

/-- The valid reference at the end of the actual BANK edge word. -/
private def bankRefAfter {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (bankValidRootedReferenceData ring hbank).Reference →
    List (Fin n) →
    (bankValidRootedReferenceData ring hbank).Reference
  | r, [] => r
  | r, e :: es =>
      bankRefAfter ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext r e) es

/-- The reference target has not been visited, including at the
end of the prefix. This is the same open-word convention as SMALL. -/
private def bankRefOpen {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (bankValidRootedReferenceData ring hbank).Reference →
    List (Fin n) → Prop
  | r, [] =>
      ¬ (bankValidRootedReferenceData ring hbank).referenceStop r
  | r, e :: es =>
      ¬ (bankValidRootedReferenceData ring hbank).referenceStop r ∧
      bankRefOpen ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext r e) es

private theorem bankRefOpenPrefix {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (u v : List (Fin n))
      (r : (bankValidRootedReferenceData ring hbank).Reference),
      bankRefOpen ring hbank r (u ++ v) →
      bankRefOpen ring hbank r u := by
  intro u
  induction u with
  | nil =>
      intro v r hh
      cases v with
      | nil => exact hh
      | cons e es => exact hh.1
  | cons e es ih =>
      intro v r hh
      exact ⟨hh.1, ih v
        ((bankValidRootedReferenceData ring hbank).referenceNext r e)
        hh.2⟩

/-- Valid-state projection has the exact unrestricted BANK history.
In particular validity never restarts the source, receipt, or clock. -/
private theorem bankRefAfterProjection {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n))
      (r : (bankValidRootedReferenceData ring hbank).Reference),
      (bankRefAfter ring hbank r word).val =
        rbRun ring r.val word := by
  intro word
  induction word with
  | nil =>
      intro r
      rfl
  | cons e es ih =>
      intro r
      change (bankRefAfter ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext r e)
        es).val =
        rbRun ring (renewalBankNext ring r.val e) es
      exact ih ((bankValidRootedReferenceData ring hbank).referenceNext r e)

/-- The precise BANK source-history statement. At a first retry cut
after an open prefix u, a *genuinely spawned* earlier completed
origin for the successful root must win on the authentic intervening
suffix, including the success edge. The birth is an actual old-state
renewalBankSpawn, not a post-hoc receipt identifier. -/
def BankRunSourceWitness {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ (seed : RootedSeed ring) (u : List (Fin n)) (e : Fin n),
    bankRefOpen ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceStart seed) u →
    renewalBankCut ring
      (bankRefAfter ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceStart seed) u).val.1
      (bankRefAfter ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceStart seed) u).val.2
      e = true →
    ∃ (p : List (Fin n)) (f : Fin n) (tail : List (Fin n))
      (born : RenewalBankBorn n),
      u = p ++ f :: tail ∧
      born ∈ renewalBankSpawn ring
        (bankRefAfter ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceStart seed) p).val f ∧
      born.identity.root = e ∧
      renewalBankWin ring born (tail ++ [e]) = true

private theorem bankFreshPayerOrigin {n : Nat}
    (c : RenewalBankController n) (w : RenewalBankWorker n)
    (h : renewalBankFreshPayer c w = true) :
    ∃ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      w = .payload p ∧ p.origin = some o := by
  cases hc : c with
  | empty =>
      simp [renewalBankFreshPayer, hc] at h
  | active a =>
      simp [renewalBankFreshPayer, hc] at h
  | waiting atoms =>
      cases hw : w with
      | empty =>
          simp [renewalBankFreshPayer, hc, hw] at h
      | pending rho =>
          simp [renewalBankFreshPayer, hc, hw] at h
      | payload p =>
          have hbits :
              (atoms.isEmpty && p.atoms.isEmpty &&
                p.origin.isSome) = true := by
            simpa [renewalBankFreshPayer, hc, hw] using h
          have hsome := (Bool.and_eq_true_iff.mp hbits).2
          cases ho : p.origin with
          | none =>
              simp [ho] at hsome
          | some o =>
              exact ⟨p, o, rfl, ho⟩

/-- At any genuine BANK cut the old right responder has PACK one.
This is the exact post-role guard in Base.bankSuccess. -/
private theorem bankCutResponderRoleOne {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hcut : renewalBankCut ring r.1 r.2 e = true) :
    (r.1 (ring.rightNeighbor e)).pack.val = 1 := by
  have hsuccess :
      bankSuccess
        (bankCell (r.1 e) (r.1 e).pack.val)
        (bankCell (r.1 (ring.rightNeighbor e))
          (r.1 (ring.rightNeighbor e)).pack.val)
        (packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b = true :=
    (Bool.and_eq_true_iff.mp hcut).1
  simp [bankSuccess, bankCell] at hsuccess
  omega

theorem bankFreshCutLoggedOrigin {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hcut : renewalBankCut ring
      (rbRun ring (renewalBankStart ring seed) pre).1
      (rbRun ring (renewalBankStart ring seed) pre).2 e = true) :
    ∃ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites
        (ring.rightNeighbor e)).worker = .payload p ∧
      p.origin = some o ∧
      o ∈ rbBirths ring (renewalBankStart ring seed) pre ∧
      o.root = e ∧
      p.heads =
        rbHeadCount ring o (renewalBankStart ring seed) pre := by
  have hi := rbReceiptInvBankWordOfInv
    ring (by omega : 2 ≤ n) seed hbank pre
  have hborn := (Bool.and_eq_true_iff.mp hcut).2
  obtain ⟨p, o, hworker, horigin⟩ :=
    bankFreshPayerOrigin
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites
        (ring.rightNeighbor e)).worker hborn
  have hlocal :
      p ∈ rbSiteLivePayloads
        ((rbRun ring (renewalBankStart ring seed) pre).2.sites
          (ring.rightNeighbor e)) := by
    simp [rbSiteLivePayloads, hworker]
  have hglobal := rbReceiptSiteLiveGlobal
    (rbRun ring (renewalBankStart ring seed) pre).2
    (ring.rightNeighbor e) p hlocal
  have hprovenance := (hi.payload p hglobal).2 o horigin
  have hpack := bankCutResponderRoleOne ring
    (rbRun ring (renewalBankStart ring seed) pre) e hcut
  have hb : 1 ≤ (compileAdvice (ceilLogTwo n)).b := by
    have hw := rbBankWidthPositive (ceilLogTwo n)
    omega
  have hsite := hi.workerSite
    (ring.rightNeighbor e) p o hworker horigin
    (by rw [hpack]; omega)
    (by rw [hpack]; omega)
  have hneighbor :
      ring.rightNeighbor e = ring.rightNeighbor o.root := by
    rw [hpack] at hsite
    change ring.rightNeighbor e = ring.rightNeighbor o.root at hsite
    exact hsite
  have hroot :=
    Counter.resetTrialNeighborInjective ring hneighbor
  exact ⟨p, o, hworker, horigin, hprovenance.1,
    hroot.symm, hprovenance.2.2.2.2.2⟩

/-- A completed origin in the exact OLD birth log has a
literal creating BANK edge and an authentic scheduler suffix.
No existential time stamp or fabricated post-state is used. -/
private theorem bankBirthHistoryDecomposes {n : Nat}
    (ring : DirectedRing n) :
    ∀ (word : List (Fin n)) (r : RenewalBankReference n)
      (o : RenewalBankOrigin n),
      o ∈ rbBirths ring r word →
      ∃ (pre : List (Fin n)) (f : Fin n)
        (tail : List (Fin n)),
        word = pre ++ f :: tail ∧
        renewalBankBirth ring
          (rbRun ring r pre).1 (rbRun ring r pre).2 f = some o := by
  intro word
  induction word with
  | nil =>
      intro r o hmem
      cases hmem
  | cons e es ih =>
      intro r o hmem
      change o ∈
        (match renewalBankBirth ring r.1 r.2 e with
         | none => []
         | some x => [x]) ++
        rbBirths ring (renewalBankNext ring r e) es at hmem
      rcases List.mem_append.mp hmem with hnow | hlater
      · cases hb : renewalBankBirth ring r.1 r.2 e with
        | none =>
            simp [hb] at hnow
        | some x =>
            have hx : o = x := by
              simpa [hb] using hnow
            subst o
            exact ⟨[], e, es, rfl, hb⟩
      · obtain ⟨p, f, tail, hwords, hbirth⟩ :=
          ih (renewalBankNext ring r e) o hlater
        refine ⟨e :: p, f, tail, ?_, ?_⟩
        · rw [hwords]
          rfl
        · change renewalBankBirth ring
            (rbRun ring (renewalBankNext ring r e) p).1
            (rbRun ring (renewalBankNext ring r e) p).2 f = some o
          exact hbirth

/-- At every actual BANK cut, all nonnumeric causal work for
the source witness is complete: the successful root has a
recorded previous accepted reset return at a concrete edge,
with the exact source reference at that creating edge. This
theorem does not claim the born payload has reached K heads. -/
theorem bankFreshCutHasBirthEdge {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (word : List (Fin n))
    (e : Fin n)
    (hcut : renewalBankCut ring
      (rbRun ring (renewalBankStart ring seed) word).1
      (rbRun ring (renewalBankStart ring seed) word).2 e = true) :
    ∃ (pre : List (Fin n)) (f : Fin n)
      (tail : List (Fin n)) (o : RenewalBankOrigin n),
      word = pre ++ f :: tail ∧
      renewalBankBirth ring
        (rbRun ring (renewalBankStart ring seed) pre).1
        (rbRun ring (renewalBankStart ring seed) pre).2 f = some o ∧
      o.root = e := by
  obtain ⟨p, o, hworker, horigin, hmem, hroot, hheads⟩ :=
    bankFreshCutLoggedOrigin ring hn hbank seed word e hcut
  obtain ⟨pre, f, tail, hdecomp, hbirth⟩ :=
    bankBirthHistoryDecomposes ring word
      (renewalBankStart ring seed) o hmem
  exact ⟨pre, f, tail, o, hdecomp, hbirth, hroot⟩

/-- The FIRST unproved physical/ghost synchronization fact for
BANK retry coverage. At any genuine successful fresh-payer cut,
the specific completed origin carried by its old responder payload
must have accumulated at least K actual ARMED head services since
its authenticated birth. ReceiptInv proves the equality
p.heads = rbHeadCount for that origin; it does not provide this
lower bound from the literal CWAIT/CL1 physical success test.
This is a Prop, NOT a theorem or an assumed proof leaf. -/
def BankCutGenuineHeadThreshold {n : Nat}
    (ring : DirectedRing n)
    (_hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n),
    renewalBankCut ring
      (rbRun ring (renewalBankStart ring seed) pre).1
      (rbRun ring (renewalBankStart ring seed) pre).2 e = true →
    ((rbRun ring (renewalBankStart ring seed) pre).2.sites
      (ring.rightNeighbor e)).worker = .payload p →
    p.origin = some o →
    (compileAdvice (ceilLogTwo n)).K ≤
      rbHeadCount ring o (renewalBankStart ring seed) pre

/-- A payload with the recorded origin and at least K heads at
one actual worker site makes the broad BANK reachability flag true. -/
private theorem bankReachedOfWorker {n : Nat}
    (m : RenewalBankMemory n) (o : RenewalBankOrigin n)
    (K : Nat) (i : Fin n) (p : RenewalBankPayload n)
    (hw : (m.sites i).worker = .payload p)
    (ho : p.origin = some o)
    (hK : K ≤ p.heads) :
    renewalBankReached o K m = true := by
  have hsite :
      renewalBankSiteReached o K (m.sites i) = true := by
    simp [renewalBankSiteReached, renewalBankPayloadReached,
      hw, ho, hK]
  unfold renewalBankReached
  rw [List.any_eq_true]
  refine ⟨true, ?_, rfl⟩
  exact List.mem_ofFn.mpr ⟨i, hsite⟩

/-- If the actual memory has reached K heads after a word, that
word has a true BANK origin win, even if an earlier cut already won. -/
private theorem bankWinWordOfEndReached {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (K : Nat) :
    ∀ (word : List (Fin n)) (r : RenewalBankReference n),
      renewalBankReached o K (rbRun ring r word).2 = true →
      renewalBankWinWord ring o K word r = true := by
  intro word
  induction word with
  | nil =>
      intro r hh
      exact hh
  | cons e es ih =>
      intro r hh
      have ht := ih (renewalBankNext ring r e) hh
      change (renewalBankReached o K r.2 ||
        renewalBankWinWord ring o K es
          (renewalBankNext ring r e)) = true
      rw [ht]
      cases renewalBankReached o K r.2 <;> rfl

private theorem bankWinAppendTrue {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (K : Nat) :
    ∀ (u v : List (Fin n)) (r : RenewalBankReference n),
      renewalBankWinWord ring o K u r = true →
      renewalBankWinWord ring o K (u ++ v) r = true := by
  intro u
  induction u with
  | nil =>
      intro v r hh
      cases v with
      | nil => exact hh
      | cons e es =>
          change renewalBankReached o K r.2 = true at hh
          change (renewalBankReached o K r.2 ||
            renewalBankWinWord ring o K es
              (renewalBankNext ring r e)) = true
          rw [hh]
          rfl
  | cons e es ih =>
      intro v r hh
      change (renewalBankReached o K r.2 ||
        renewalBankWinWord ring o K es
          (renewalBankNext ring r e)) = true at hh
      change (renewalBankReached o K r.2 ||
        renewalBankWinWord ring o K (es ++ v)
          (renewalBankNext ring r e)) = true
      have hdisj :
          renewalBankReached o K r.2 = true ∨
          renewalBankWinWord ring o K es
            (renewalBankNext ring r e) = true := by
        simpa only [Bool.or_eq_true] using hh
      rcases hdisj with hfront | htail
      · rw [hfront]
        rfl
      · have hafter := ih v (renewalBankNext ring r e) htail
        rw [hafter]
        simp

private theorem bankValidReferenceStartVal {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    ((bankValidRootedReferenceData ring hbank).referenceStart seed).val =
      renewalBankStart ring seed := by
  rfl

theorem bankRunSourceWitness_of_headThreshold {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hthreshold : BankCutGenuineHeadThreshold ring hbank) :
    BankRunSourceWitness ring hbank := by
  intro seed u e hopen hcut
  have hstart := bankValidReferenceStartVal ring hbank seed
  have hprojection := bankRefAfterProjection ring hbank u
    ((bankValidRootedReferenceData ring hbank).referenceStart seed)
  rw [hstart] at hprojection
  have hraw : renewalBankCut ring
      (rbRun ring (renewalBankStart ring seed) u).1
      (rbRun ring (renewalBankStart ring seed) u).2 e = true := by
    rw [← hprojection]
    exact hcut
  obtain ⟨p, o, hworker, horigin, hborn, hroot, hheads⟩ :=
    bankFreshCutLoggedOrigin ring hn hbank seed u e hraw
  obtain ⟨pfx, f, tail, hword, hbirth⟩ :=
    bankBirthHistoryDecomposes ring u
      (renewalBankStart ring seed) o hborn
  have hKcount :=
    hthreshold seed u e p o hraw hworker horigin
  have hK : (compileAdvice (ceilLogTwo n)).K ≤ p.heads := by
    rw [hheads]
    exact hKcount
  have hReached : renewalBankReached o
      (compileAdvice (ceilLogTwo n)).K
      (rbRun ring (renewalBankStart ring seed) u).2 = true :=
    bankReachedOfWorker
      (rbRun ring (renewalBankStart ring seed) u).2
      o (compileAdvice (ceilLogTwo n)).K
      (ring.rightNeighbor e) p hworker horigin hK
  have hRunTail :
      rbRun ring
        (renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pfx) f)
        tail =
      rbRun ring (renewalBankStart ring seed) u := by
    rw [hword, rbRunAppend]
    rfl
  have hWinTail : renewalBankWinWord ring o
      (compileAdvice (ceilLogTwo n)).K tail
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pfx) f) = true := by
    apply bankWinWordOfEndReached
    rw [hRunTail]
    exact hReached
  have hWinSuffix : renewalBankWin ring
      { identity := o
        afterBirth := renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pfx) f }
      (tail ++ [e]) = true := by
    exact bankWinAppendTrue ring o
      (compileAdvice (ceilLogTwo n)).K
      tail [e]
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pfx) f)
      hWinTail
  refine ⟨pfx, f, tail,
    { identity := o
      afterBirth := renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pfx) f },
    hword, ?_, hroot, hWinSuffix⟩
  have hpreProj := bankRefAfterProjection ring hbank pfx
    ((bankValidRootedReferenceData ring hbank).referenceStart seed)
  rw [hpreProj, hstart]
  simp [renewalBankSpawn, hbirth]

/-- A single genuine born identity with a passing win test
contributes a positive summand, regardless of other births. -/
private theorem bankBornListPositive {A : Type}
    (os : List A) (f : A → Bool) (a : A)
    (hmem : a ∈ os) (hwin : f a = true) :
    0 < (os.map (fun o => Prob.indicator (f o))).sum := by
  induction os with
  | nil => cases hmem
  | cons x xs ih =>
      rcases List.mem_cons.mp hmem with he | ht
      · subst x
        simp only [List.map_cons, List.sum_cons]
        have hh : Prob.indicator (f a) = 1 := by
          simp [Prob.indicator, hwin]
        omega
      · simp only [List.map_cons, List.sum_cons]
        have hh := ih ht
        omega

private theorem bankSuccessfulOrigin {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (born : RenewalBankBorn n) :
    ∀ (u : List (Fin n))
      (r : (bankValidRootedReferenceData ring hbank).Reference)
      (e : Fin n) (v : List (Fin n)),
      bankRefOpen ring hbank r u →
      born ∈ (bankValidRootedReferenceData ring hbank).spawn
        (bankRefAfter ring hbank r u) e →
      (bankValidRootedReferenceData ring hbank).win born v = true →
      0 < Prob.successfulOriginsWord
        (bankValidRootedReferenceData ring hbank).referenceNext
        (bankValidRootedReferenceData ring hbank).referenceStop
        (bankValidRootedReferenceData ring hbank).spawn
        (bankValidRootedReferenceData ring hbank).win
        r (u ++ e :: v) := by
  intro u
  induction u with
  | nil =>
      intro r e v hopen hmem hwin
      have hh := bankBornListPositive
        ((bankValidRootedReferenceData ring hbank).spawn r e)
        (fun o => (bankValidRootedReferenceData ring hbank).win o v)
        born hmem hwin
      change 0 < (if (bankValidRootedReferenceData ring hbank).referenceStop r
        then 0
        else (((bankValidRootedReferenceData ring hbank).spawn r e).map
          (fun o => Prob.indicator
            ((bankValidRootedReferenceData ring hbank).win o v))).sum +
          Prob.successfulOriginsWord
            (bankValidRootedReferenceData ring hbank).referenceNext
            (bankValidRootedReferenceData ring hbank).referenceStop
            (bankValidRootedReferenceData ring hbank).spawn
            (bankValidRootedReferenceData ring hbank).win
            ((bankValidRootedReferenceData ring hbank).referenceNext r e) v)
      rw [if_neg hopen]
      omega
  | cons f fs ih =>
      intro r e v hopen hmem hwin
      have hh := ih
        ((bankValidRootedReferenceData ring hbank).referenceNext r f)
        e v hopen.2 hmem hwin
      change 0 < (if (bankValidRootedReferenceData ring hbank).referenceStop r
        then 0
        else (((bankValidRootedReferenceData ring hbank).spawn r f).map
          (fun o => Prob.indicator
            ((bankValidRootedReferenceData ring hbank).win o
              (fs ++ e :: v)))).sum +
          Prob.successfulOriginsWord
            (bankValidRootedReferenceData ring hbank).referenceNext
            (bankValidRootedReferenceData ring hbank).referenceStop
            (bankValidRootedReferenceData ring hbank).spawn
            (bankValidRootedReferenceData ring hbank).win
            ((bankValidRootedReferenceData ring hbank).referenceNext r f)
            (fs ++ e :: v))
      rw [if_neg hopen.1]
      omega

/-- The actual rooted BANK retry shell, not an invented trial step. -/
private noncomputable def bankRetryKernel {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    RetryKernel (RootedSeed ring × RenewalBankMemory n)
      (RootedSeed ring) n :=
  referenceKernel ring hn (bankValidRootedReferenceData ring hbank)

private theorem bankRetryFirstLeOne {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    ∀ (word : List (Fin n)) (z : AttemptNode A Seed),
      Prob.retryFirstWord K z word ≤ 1 := by
  intro word
  induction word with
  | nil =>
      intro z
      cases z <;> simp [Prob.retryFirstWord]
  | cons e es ih =>
      intro z
      cases z with
      | success => simp [Prob.retryFirstWord]
      | retry seed => simp [Prob.retryFirstWord]
      | active a =>
          change Prob.retryFirstWord K (K.step a e) es ≤ 1
          exact ih (K.step a e)

/-- Cut extraction, as for SMALL: the first retry has a literal
pre-edge BANK cut, a stop-free earlier reference pfx, and no
physical/ref memory divergence before that cut. -/
private theorem bankRetryFirstHasCut {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n))
      (a : RootedSeed ring × RenewalBankMemory n)
      (r : (bankValidRootedReferenceData ring hbank).Reference),
      r.val = (a.1.val, a.2) →
      ¬ (bankValidRootedReferenceData ring hbank).referenceStop r →
      Prob.retryFirstWord (bankRetryKernel ring hn hbank)
        (.active a) word = 1 →
      ∃ (u : List (Fin n)) (e : Fin n) (v : List (Fin n)),
        word = u ++ e :: v ∧
        bankRefOpen ring hbank r u ∧
        renewalBankCut ring
          (bankRefAfter ring hbank r u).val.1
          (bankRefAfter ring hbank r u).val.2 e = true := by
  intro word
  induction word with
  | nil =>
      intro a r hre hnot hretry
      change (0 : Nat) = 1 at hretry
      cases hretry
  | cons e es ih =>
      intro a r hre hnot hretry
      change Prob.retryFirstWord
        (bankRetryKernel ring hn hbank)
        ((bankRetryKernel ring hn hbank).step a e) es = 1 at hretry
      cases hs : (bankRetryKernel ring hn hbank).step a e with
      | success =>
          rw [hs] at hretry
          simp [Prob.retryFirstWord] at hretry
      | retry seed =>
          have hs' : rootedTrialStep ring hn
              (renewalBankTrialAdvance ring)
              (renewalBankTrialCut ring) a e = .retry seed := hs
          unfold rootedTrialStep at hs'
          split at hs'
          · cases hs'
          · rename_i hnext
            split at hs'
            · rename_i hcut
              have hc : renewalBankCut ring r.val.1 r.val.2 e =
                  true := by
                rw [hre]
                change renewalBankTrialCut ring a e = true
                exact hcut
              exact ⟨[], e, es, rfl, hnot, hc⟩
            · cases hs'
      | active b =>
          rw [hs] at hretry
          have hs' : rootedTrialStep ring hn
              (renewalBankTrialAdvance ring)
              (renewalBankTrialCut ring) a e = .active b := hs
          unfold rootedTrialStep at hs'
          split at hs'
          · cases hs'
          · rename_i hnext
            split at hs'
            · cases hs'
            · rename_i hnocut
              cases hs'
              have hc : renewalBankTrialCut ring a e = false := by
                cases htest : renewalBankTrialCut ring a e with
                | false => rfl
                | true => exact False.elim (hnocut htest)
              have href :
                  ((bankValidRootedReferenceData ring hbank).referenceNext r e).val =
                    ((rootedSuccessor ring hn a.1 e).val,
                      renewalBankTrialAdvance ring a e) := by
                change renewalBankNext ring r.val e = _
                rw [hre]
                apply Prod.ext
                · exact renewalBankPhysicalBeforeCut ring
                    (a.1.val, a.2) e hc
                · rfl
              have hstay :
                  ¬ (bankValidRootedReferenceData ring hbank).referenceStop
                    ((bankValidRootedReferenceData ring hbank).referenceNext r e) := by
                change ¬ renewalBankStop ring
                  (((bankValidRootedReferenceData ring hbank).referenceNext r e).val)
                rw [href]
                exact hnext
              obtain ⟨u, f, v, hword, hopen, hcut⟩ :=
                ih (rootedSuccessor ring hn a.1 e,
                    renewalBankTrialAdvance ring a e)
                  ((bankValidRootedReferenceData ring hbank).referenceNext r e)
                  href hstay hretry
              refine ⟨e :: u, f, v, ?_, ?_, ?_⟩
              · exact congrArg (List.cons e) hword
              · exact ⟨hnot, hopen⟩
              · exact hcut

theorem bankReferenceRetryCoverageOfSourceWitness {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hsource : BankRunSourceWitness ring hbank) :
    ReferenceRetryCoverage ring hn
      (bankValidRootedReferenceData ring hbank) := by
  intro seed hnot word
  change Prob.retryFirstWord (bankRetryKernel ring hn hbank)
      (.active (seed, renewalBankInitialMemory ring seed)) word ≤
    Prob.originEventWord
      (bankValidRootedReferenceData ring hbank).referenceNext
      (bankValidRootedReferenceData ring hbank).referenceStop
      (bankValidRootedReferenceData ring hbank).spawn
      (bankValidRootedReferenceData ring hbank).win
      ((bankValidRootedReferenceData ring hbank).referenceStart seed) word
  by_cases hz :
      Prob.retryFirstWord (bankRetryKernel ring hn hbank)
        (.active (seed, renewalBankInitialMemory ring seed)) word = 0
  · rw [hz]
    exact Nat.zero_le _
  · have hle :=
      bankRetryFirstLeOne (bankRetryKernel ring hn hbank)
        word (.active (seed, renewalBankInitialMemory ring seed))
    have hretry :
        Prob.retryFirstWord (bankRetryKernel ring hn hbank)
          (.active (seed, renewalBankInitialMemory ring seed)) word = 1 := by
      omega
    have hstart :
        ¬ (bankValidRootedReferenceData ring hbank).referenceStop
          ((bankValidRootedReferenceData ring hbank).referenceStart seed) := hnot
    obtain ⟨u, e, v, hword, hopen, hcut⟩ :=
      bankRetryFirstHasCut ring hn hbank word
        (seed, renewalBankInitialMemory ring seed)
        ((bankValidRootedReferenceData ring hbank).referenceStart seed)
        rfl hstart hretry
    obtain ⟨p, f, tail, born, hp, hbirth, hroot, hwin⟩ :=
      hsource seed u e hopen hcut
    have hpopen :
        bankRefOpen ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceStart seed)
          p := by
      have hfull : bankRefOpen ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceStart seed)
          (p ++ f :: tail) := by
        rw [← hp]
        exact hopen
      exact bankRefOpenPrefix ring hbank p (f :: tail)
        ((bankValidRootedReferenceData ring hbank).referenceStart seed)
        hfull
    have hmem :
        born ∈ (bankValidRootedReferenceData ring hbank).spawn
          (bankRefAfter ring hbank
            ((bankValidRootedReferenceData ring hbank).referenceStart seed)
            p) f := hbirth
    have hwinLong :
        renewalBankWin ring born (tail ++ e :: v) = true := by
      have hh := bankWinAppendTrue ring born.identity
        (compileAdvice (ceilLogTwo n)).K
        (tail ++ [e]) v born.afterBirth hwin
      change renewalBankWinWord ring born.identity
        (compileAdvice (ceilLogTwo n)).K
        (tail ++ e :: v) born.afterBirth = true
      simpa only [List.append_assoc, List.singleton_append] using hh
    have hpos := bankSuccessfulOrigin ring hbank born p
      ((bankValidRootedReferenceData ring hbank).referenceStart seed)
      f (tail ++ e :: v) hpopen hmem hwinLong
    have hlist :
        u ++ e :: v = p ++ f :: (tail ++ e :: v) := by
      rw [hp]
      simp only [List.append_assoc, List.cons_append]
    have hpositive :
        0 < Prob.successfulOriginsWord
          (bankValidRootedReferenceData ring hbank).referenceNext
          (bankValidRootedReferenceData ring hbank).referenceStop
          (bankValidRootedReferenceData ring hbank).spawn
          (bankValidRootedReferenceData ring hbank).win
          ((bankValidRootedReferenceData ring hbank).referenceStart seed)
          word := by
      rw [hword, hlist]
      exact hpos
    have hevent :
        Prob.originEventWord
          (bankValidRootedReferenceData ring hbank).referenceNext
          (bankValidRootedReferenceData ring hbank).referenceStop
          (bankValidRootedReferenceData ring hbank).spawn
          (bankValidRootedReferenceData ring hbank).win
          ((bankValidRootedReferenceData ring hbank).referenceStart seed)
          word = 1 := by
      unfold Prob.originEventWord
      split
      · rename_i he
        omega
      · rfl
    rw [hretry, hevent]
    exact Nat.le_refl 1

/-- Exact one-premise reduction of the BANK causal coverage
obligation. The premise is the previously defined, still-OPEN
physical K-head threshold; the retry-first word induction and
all receipt/origin transports have been discharged separately. -/
theorem bankReferenceRetryCoverageOfHeadThreshold {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hthreshold : BankCutGenuineHeadThreshold ring hbank) :
    ReferenceRetryCoverage ring hn
      (bankValidRootedReferenceData ring hbank) := by
  exact bankReferenceRetryCoverageOfSourceWitness
    ring hn hbank
    (bankRunSourceWitness_of_headThreshold
      ring hn hbank hthreshold)

end L3.BankRetryCoverage

#print axioms L3.BankRetryCoverage.bankFreshCutHasBirthEdge
#print axioms L3.BankRetryCoverage.bankRunSourceWitness_of_headThreshold
#print axioms L3.BankRetryCoverage.bankReferenceRetryCoverageOfSourceWitness
#print axioms L3.BankRetryCoverage.bankReferenceRetryCoverageOfHeadThreshold

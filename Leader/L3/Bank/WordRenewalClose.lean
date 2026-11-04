import Leader.L3.Bank.WordRenewalFrontier

/-!
R10a W stage, closing route: lap counting on the S1 restart
clock (research/lean-l3/ledgers/R10a-critical-path.md).

The consumer clock `BankWordEpochPostSOneWorkerClock` is the paper's
(E.B) first-genuine-hard clock.  Every reachable post-S1 state reaches
the next root S1 service within n(5n-4) (`bankWordEpochRestartSOneCost`),
so the clock follows from a deterministic lap count: along any run from
a reachable post-S1 state, the genuine hard-acceptance counter increases
before the (L+2)-nd root S1 service.  This file proves the reduction;
the lap count itself is the named input `BankWordEpochLapCount`,
discharged below from the serializer rows and the J-W lineage step.
-/

namespace L3.RenewalReferenceClock

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! ## Generic first-hit cost lemmas on a forward-closed domain -/

/-- Target monotonicity restricted to a forward-closed domain.
Consumer: the stage chain of `bankWordEpochPostSOneWorkerClockOfLapCount`. -/
theorem costNumerator_target_mono_on {S : Type} {n : Nat}
    (next : S → Fin n → S) (D Small Big : S → Prop)
    (hD : ∀ x, D x → ∀ e, D (next x e))
    (himp : ∀ x, D x → Small x → Big x) :
    ∀ (T : Nat) (x : S), D x →
      costNumerator next Big x T ≤ costNumerator next Small x T := by
  intro T
  induction T with
  | zero =>
      intro x _
      rw [costNumerator_zero]
      exact Nat.zero_le _
  | succ T ih =>
      intro x hx
      by_cases hb : Big x
      · rw [costNumerator_terminal next Big x hb (T + 1)]
        exact Nat.zero_le _
      · have hs : ¬ Small x := fun h => hb (himp x hx h)
        rw [costNumerator_succ next Big x hb T,
          costNumerator_succ next Small x hs T]
        exact Nat.add_le_add_left
          (ofFn_sum_le _ _ (fun e => ih (next x e) (hD x hx e))) _

/-- Stage reserve restricted to a forward-closed domain: the cost to P
is at most the cost to A-or-P plus the uniform cost from A-states on
the domain.  Consumer: `costNumerator_stage_le_on`. -/
theorem costNumerator_stage_reserve_on {S : Type} {n : Nat}
    (next : S → Fin n → S) (D A P : S → Prop)
    (hD : ∀ x, D x → ∀ e, D (next x e))
    (B₂ : Nat)
    (h₂ : ∀ y, D y → A y → ∀ T,
      costNumerator next P y T ≤ n ^ T * B₂) :
    ∀ (T : Nat) (y : S), D y →
      costNumerator next P y T ≤
        costNumerator next (fun z => A z ∨ P z) y T + n ^ T * B₂ := by
  intro T
  induction T with
  | zero =>
      intro y _
      simp only [costNumerator_zero, Nat.zero_add]
      exact Nat.zero_le _
  | succ T ih =>
      intro y hy
      by_cases hp : P y
      · have hr : A y ∨ P y := Or.inr hp
        rw [costNumerator_terminal next P y hp (T + 1),
          costNumerator_terminal next (fun z => A z ∨ P z) y hr (T + 1)]
        exact Nat.zero_le _
      · by_cases ha : A y
        · have hr : A y ∨ P y := Or.inl ha
          rw [costNumerator_terminal next (fun z => A z ∨ P z) y hr (T + 1)]
          simpa only [Nat.zero_add] using h₂ y hy ha (T + 1)
        · have hr : ¬ (A y ∨ P y) := by
            intro h
            rcases h with hA | hP
            · exact ha hA
            · exact hp hP
          rw [costNumerator_succ next P y hp T,
            costNumerator_succ next (fun z => A z ∨ P z) y hr T]
          have hs :
              (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum ≤
              (List.ofFn (fun e : Fin n =>
                costNumerator next (fun z => A z ∨ P z)
                  (next y e) T)).sum +
                n ^ (T + 1) * B₂ := by
            calc
              (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum ≤
                  (List.ofFn (fun e : Fin n =>
                    costNumerator next (fun z => A z ∨ P z)
                      (next y e) T + n ^ T * B₂)).sum :=
                ofFn_sum_le _ _ (fun e => ih (next y e) (hD y hy e))
              _ = (List.ofFn (fun e : Fin n =>
                    costNumerator next (fun z => A z ∨ P z)
                      (next y e) T)).sum +
                    n * (n ^ T * B₂) := by
                rw [ofFn_sum_add, ofFn_sum_const]
              _ = (List.ofFn (fun e : Fin n =>
                    costNumerator next (fun z => A z ∨ P z)
                      (next y e) T)).sum +
                    n ^ (T + 1) * B₂ := by
                rw [Nat.pow_succ]
                ac_rfl
          omega

/-- Two-stage composition on a forward-closed domain.
Consumer: one lap of the stage chain. -/
theorem costNumerator_stage_le_on {S : Type} {n : Nat}
    (next : S → Fin n → S) (D A P : S → Prop)
    (hD : ∀ x, D x → ∀ e, D (next x e))
    (x₀ : S) (hx₀ : D x₀) (B₁ B₂ : Nat)
    (h₁ : ∀ T,
      costNumerator next (fun z => A z ∨ P z) x₀ T ≤ n ^ T * B₁)
    (h₂ : ∀ y, D y → A y → ∀ T,
      costNumerator next P y T ≤ n ^ T * B₂) :
    ∀ T, costNumerator next P x₀ T ≤ n ^ T * (B₁ + B₂) := by
  intro T
  calc
    costNumerator next P x₀ T ≤
        costNumerator next (fun z => A z ∨ P z) x₀ T + n ^ T * B₂ :=
      costNumerator_stage_reserve_on next D A P hD B₂ h₂ T x₀ hx₀
    _ ≤ n ^ T * B₁ + n ^ T * B₂ :=
      Nat.add_le_add_right (h₁ T) _
    _ = n ^ T * (B₁ + B₂) := by rw [Nat.mul_add]

/-- First-entrance domination: if every entrance into A from the
domain lands in Good, the first hit of Good is no later than the first
hit of A.  No absorption of A is needed.  Consumer: the launch at the
genuine acceptance edge. -/
theorem costNumerator_entrance_le_on {S : Type} {n : Nat}
    (next : S → Fin n → S) (D A Good : S → Prop)
    (hD : ∀ x, D x → ∀ e, D (next x e))
    (hentr : ∀ x, D x → ¬ A x → ∀ e, A (next x e) → Good (next x e)) :
    ∀ (T : Nat) (x : S), D x → ¬ A x →
      costNumerator next Good x T ≤ costNumerator next A x T := by
  intro T
  induction T with
  | zero =>
      intro x _ _
      rw [costNumerator_zero]
      exact Nat.zero_le _
  | succ T ih =>
      intro x hx hA
      by_cases hg : Good x
      · rw [costNumerator_terminal next Good x hg (T + 1)]
        exact Nat.zero_le _
      · rw [costNumerator_succ next Good x hg T,
          costNumerator_succ next A x hA T]
        apply Nat.add_le_add_left
        apply ofFn_sum_le
        intro e
        by_cases hA' : A (next x e)
        · rw [costNumerator_terminal next Good (next x e)
            (hentr x hx hA e hA') T]
          exact Nat.zero_le _
        · exact ih (next x e) (hD x hx e) hA'

/-! ## Runs from an intermediate state -/

theorem bankWordEpochRunAppend {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (w₁ w₂ : List (Fin n)) :
    bankWordEpochRun ring root z (w₁ ++ w₂) =
      bankWordEpochRun ring root
        (bankWordEpochRun ring root z w₁) w₂ := by
  induction w₁ generalizing z with
  | nil => rfl
  | cons e rest ih =>
      show bankWordEpochRun ring root
          (bankWordEpochNext ring root z e) (rest ++ w₂) = _
      exact ih (bankWordEpochNext ring root z e)

/-- States reached from `z₀` by some scheduler word.  This is the
forward-closed domain of the lap count relative to `z₀`. -/
def BankWordEpochReachableFrom {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z₀ z : BankWordEpochState n) : Prop :=
  ∃ word : List (Fin n), bankWordEpochRun ring root z₀ word = z

theorem bankWordEpochReachableFromSelf {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z₀ : BankWordEpochState n) :
    BankWordEpochReachableFrom ring root z₀ z₀ :=
  ⟨[], rfl⟩

theorem bankWordEpochReachableFromNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z₀ z : BankWordEpochState n)
    (hz : BankWordEpochReachableFrom ring root z₀ z) (e : Fin n) :
    BankWordEpochReachableFrom ring root z₀
      (bankWordEpochNext ring root z e) := by
  obtain ⟨word, hw⟩ := hz
  refine ⟨word ++ [e], ?_⟩
  rw [bankWordEpochRunSnoc, hw]

/-- Reachability from a reachable state is reachability. -/
theorem bankWordEpochReachableOfFrom {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z₀ z : BankWordEpochState n)
    (hz₀ : BankWordEpochReachable ring root s z₀)
    (hz : BankWordEpochReachableFrom ring root z₀ z) :
    BankWordEpochReachable ring root s z := by
  obtain ⟨w₀, hw₀⟩ := hz₀
  obtain ⟨w, hw⟩ := hz
  refine ⟨w₀ ++ w, ?_⟩
  rw [bankWordEpochRunAppend, hw₀, hw]

/-! ## The root S1 counter and the restart clock -/

/-- Number of root-outgoing S1 services recorded by the origin
observer.  Consumer: the lap count `BankWordEpochLapCount`. -/
def bankWordRootStartCount {n : Nat} (root : Fin n)
    (z : BankWordEpochState n) : Nat :=
  z.2.2.services.countP
    (fun r => (r.edge == root) && (r.serializer.row == "S1"))

theorem bankWordEpochNextServices {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    (bankWordEpochNext ring root z e).2.2.services =
      bankWordEpochSelectedReceipt ring z e :: z.2.2.services := rfl

/-- The counter increments exactly at the S1-only observer's stop
service.  Consumer: `bankWordRootStartCountRestartCostEq`. -/
theorem bankWordRootStartCountNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    bankWordRootStartCount root (bankWordEpochNext ring root z e) =
      bankWordRootStartCount root z +
        (if clockSerializerSOneService ring root z.2.1 e then 1 else 0) := by
  unfold bankWordRootStartCount
  rw [bankWordEpochNextServices, List.countP_cons]
  congr 1
  by_cases h : clockSerializerSOneService ring root z.2.1 e
  · rw [if_pos h]
    obtain ⟨he, hrow⟩ := h
    subst he
    simp [bankWordEpochSelectedReceipt, hrow]
  · rw [if_neg h]
    by_cases he : e = root
    · subst he
      have hrow :
          (serW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).row ≠ "S1" :=
        fun hr => h (And.intro rfl hr)
      simp [bankWordEpochSelectedReceipt, hrow]
    · simp [bankWordEpochSelectedReceipt, he]

theorem bankWordRootStartCountMono {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    bankWordRootStartCount root z ≤
      bankWordRootStartCount root (bankWordEpochNext ring root z e) := by
  rw [bankWordRootStartCountNext]
  exact Nat.le_add_right _ _

/-- On the epoch chain, the first-hit cost of 'one more root S1' is
exactly the S1-only observer's stop cost restarted at the current
physical configuration.  Consumer: one lap of the stage chain. -/
theorem bankWordRootStartCountRestartCostEq {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (c : Nat) :
    ∀ (T : Nat) (y : BankWordEpochState n),
      bankWordRootStartCount root y = c →
      costNumerator (bankWordEpochNext ring root)
        (fun w => c < bankWordRootStartCount root w) y T =
      costNumerator (clockSerializerSOneOnlyNext ring root)
        clockSerializerIsStopped
        (.active y.2.1 : ClockSerializerStopNode n
          (compileAdvice (ceilLogTwo n))) T := by
  intro T
  induction T with
  | zero =>
      intro y _
      rfl
  | succ T ih =>
      intro y hy
      have hnot : ¬ (c < bankWordRootStartCount root y) := by
        rw [hy]
        exact Nat.lt_irrefl c
      have hobs : ¬ clockSerializerIsStopped
          (.active y.2.1 : ClockSerializerStopNode n
            (compileAdvice (ceilLogTwo n))) := by
        intro h
        cases h
      rw [costNumerator_succ (bankWordEpochNext ring root)
          (fun w => c < bankWordRootStartCount root w) y hnot T,
        costNumerator_succ (clockSerializerSOneOnlyNext ring root)
          clockSerializerIsStopped _ hobs T]
      congr 1
      apply ofFn_sum_eq
      intro e
      by_cases hs : clockSerializerSOneService ring root y.2.1 e
      · have hcount : c < bankWordRootStartCount root
            (bankWordEpochNext ring root y e) := by
          rw [bankWordRootStartCountNext, if_pos hs, hy]
          exact Nat.lt_succ_self c
        have hstep : clockSerializerSOneOnlyNext ring root
            (.active y.2.1 : ClockSerializerStopNode n
              (compileAdvice (ceilLogTwo n))) e = .stopped := by
          simp [clockSerializerSOneOnlyNext, hs]
        rw [hstep,
          costNumerator_terminal (bankWordEpochNext ring root)
            (fun w => c < bankWordRootStartCount root w) _ hcount T,
          costNumerator_terminal (clockSerializerSOneOnlyNext ring root)
            clockSerializerIsStopped
            (.stopped : ClockSerializerStopNode n
              (compileAdvice (ceilLogTwo n))) True.intro T]
      · have hcount : bankWordRootStartCount root
            (bankWordEpochNext ring root y e) = c := by
          rw [bankWordRootStartCountNext, if_neg hs, hy, Nat.add_zero]
        have hstep : clockSerializerSOneOnlyNext ring root
            (.active y.2.1 : ClockSerializerStopNode n
              (compileAdvice (ceilLogTwo n))) e =
            .active (bankWordEpochNext ring root y e).2.1 := by
          simp [clockSerializerSOneOnlyNext, hs,
            bankWordEpochPhysicalNext]
        rw [hstep]
        exact ih (bankWordEpochNext ring root y e) hcount

/-- From any reachable state the next root S1 costs at most n(5n-4):
the restart clock transferred to the counter.  Consumer: one lap. -/
theorem bankWordRootStartCountNextLapCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (y : BankWordEpochState n)
    (hy : BankWordEpochReachable ring root s y) (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      (fun w => bankWordRootStartCount root y <
        bankWordRootStartCount root w) y T ≤
      n ^ T * (n * (5 * n - 4)) := by
  rw [bankWordRootStartCountRestartCostEq ring root
    (bankWordRootStartCount root y) T y rfl]
  exact bankWordEpochRestartSOneCost ring hn hbank root s hs y hy T

/-! ## Genuine acceptances launch the ghost worker -/

theorem bankWordHardEpochCountNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).hardEpochs =
      (if bankWordHardEpochGenuine ring root
          (bankWordEpochSelectedReceipt ring z e)
          (bankWordHardEpochLedger ring root z) = true
       then (bankWordHardEpochLedger ring root z).hardEpochs + 1
       else (bankWordHardEpochLedger ring root z).hardEpochs) := by
  rw [bankWordHardEpochLedgerNext]
  unfold bankWordHardEpochGenuine
  simp [bankWordHardEpochStep]

theorem bankWordHardEpochCountMono {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    (bankWordHardEpochLedger ring root z).hardEpochs ≤
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).hardEpochs := by
  rw [bankWordHardEpochCountNext]
  split
  · exact Nat.le_succ _
  · exact Nat.le_refl _

/-- An increase of the genuine-acceptance counter is a genuine
acceptance of the selected receipt.  Consumer: the launch lemma. -/
theorem bankWordHardEpochGenuineOfCountIncrease {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (h : (bankWordHardEpochLedger ring root z).hardEpochs <
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).hardEpochs) :
    bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true := by
  rw [bankWordHardEpochCountNext] at h
  by_cases hg : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true
  · exact hg
  · rw [if_neg hg] at h
    exact absurd h (Nat.lt_irrefl _)

/-- At a genuine acceptance on a reachable run the origin observer
launches the worker: the physical row is I0 and the ghost ticket
join is the ledger's.  Consumer: the entrance step of the clock. -/
theorem bankWordEpochLaunchedOfGenuine {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hg : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    BankWordEpochWorkerLaunched (bankWordEpochNext ring root z e) := by
  obtain ⟨he, _, hhard⟩ :=
    bankWordHardEpochSelectedGenuineOwnerFlags ring root z e hg
  have hhard' : (serW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
      true := hhard
  have hrow : (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).row =
      "I0" :=
    bankWordHardEpochHardAcceptIzeroRow _ _ hhard'
  have hcoh := (bankWordRenewalFrontierLedgerGhostCoherence
    ring root s z hz).1
  unfold bankWordHardEpochGenuine at hg
  rw [hcoh] at hg
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hg
  refine ⟨{
    epoch := t
    acceptedAt := z.2.2.clock + 1
    phase := .prefixRun
    host := root
    target := root
    index := 0
    reads := []
    publications := [] }, ?_⟩
  show (wWorkerReceiptStep root e (ring.rightNeighbor e)
      (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
      z.2.2.worker).1 = some _
  simp only [bankWordEpochSelectedReceipt] at ht
  rw [ht]
  simp [wWorkerReceiptStep, hrow]

/-! ## The lap count and the clock -/

/-- DET.  Along any run from a reachable post-S1 state `z₀`, the
genuine-acceptance counter increases before the (L+2)-nd root S1
service after `z₀`, `L = bankWordRenewalLease n`.
Consumer: `bankWordEpochPostSOneWorkerClockOfLapCount`. -/
def BankWordEpochLapCount {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z₀ : BankWordEpochState n,
    BankWordEpochReachable ring root s z₀ →
    BankWordEpochSOneReached z₀ →
    ∀ z : BankWordEpochState n,
      BankWordEpochReachableFrom ring root z₀ z →
      bankWordRootStartCount root z₀ + (bankWordRenewalLease n + 2) ≤
        bankWordRootStartCount root z →
      (bankWordHardEpochLedger ring root z₀).hardEpochs <
        (bankWordHardEpochLedger ring root z).hardEpochs

/-- Chain of at most `L+2` laps, each paid by the restart clock.
Consumer: `bankWordEpochPostSOneWorkerClockOfLapCount`. -/
theorem bankWordEpochGenuineCostOfLapCount {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hlap : BankWordEpochLapCount ring root s)
    (z₀ : BankWordEpochState n)
    (hz₀ : BankWordEpochReachable ring root s z₀)
    (hstop : BankWordEpochSOneReached z₀) (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      (fun y => (bankWordHardEpochLedger ring root z₀).hardEpochs <
        (bankWordHardEpochLedger ring root y).hardEpochs) z₀ T ≤
      n ^ T * ((bankWordRenewalLease n + 2) * (n * (5 * n - 4))) := by
  have hD : ∀ x, BankWordEpochReachableFrom ring root z₀ x → ∀ e,
      BankWordEpochReachableFrom ring root z₀
        (bankWordEpochNext ring root x e) :=
    fun x hx e => bankWordEpochReachableFromNext ring root z₀ x hx e
  have hchain : ∀ j : Nat, ∀ y : BankWordEpochState n,
      BankWordEpochReachableFrom ring root z₀ y →
      bankWordRootStartCount root z₀ + (bankWordRenewalLease n + 2) ≤
        bankWordRootStartCount root y + j →
      ∀ U : Nat,
        costNumerator (bankWordEpochNext ring root)
          (fun w => (bankWordHardEpochLedger ring root z₀).hardEpochs <
            (bankWordHardEpochLedger ring root w).hardEpochs) y U ≤
        n ^ U * (j * (n * (5 * n - 4))) := by
    intro j
    induction j with
    | zero =>
        intro y hy hcount U
        have hA := hlap z₀ hz₀ hstop y hy (by simpa using hcount)
        rw [costNumerator_terminal (bankWordEpochNext ring root) _ y hA U]
        exact Nat.zero_le _
    | succ j ih =>
        intro y hy hcount U
        by_cases hA : (bankWordHardEpochLedger ring root z₀).hardEpochs <
            (bankWordHardEpochLedger ring root y).hardEpochs
        · rw [costNumerator_terminal (bankWordEpochNext ring root) _ y hA U]
          exact Nat.zero_le _
        · have hstage := costNumerator_stage_le_on
            (bankWordEpochNext ring root)
            (BankWordEpochReachableFrom ring root z₀)
            (fun w => bankWordRootStartCount root y <
              bankWordRootStartCount root w)
            (fun w => (bankWordHardEpochLedger ring root z₀).hardEpochs <
              (bankWordHardEpochLedger ring root w).hardEpochs)
            hD y hy (n * (5 * n - 4)) (j * (n * (5 * n - 4)))
            (fun V => by
              calc
                costNumerator (bankWordEpochNext ring root)
                    (fun w => bankWordRootStartCount root y <
                        bankWordRootStartCount root w ∨
                      (bankWordHardEpochLedger ring root z₀).hardEpochs <
                        (bankWordHardEpochLedger ring root w).hardEpochs)
                    y V ≤
                  costNumerator (bankWordEpochNext ring root)
                    (fun w => bankWordRootStartCount root y <
                      bankWordRootStartCount root w) y V :=
                  costNumerator_target_mono_on
                    (bankWordEpochNext ring root)
                    (BankWordEpochReachableFrom ring root z₀) _ _ hD
                    (fun w _ hw => Or.inl hw) V y hy
                _ ≤ n ^ V * (n * (5 * n - 4)) :=
                  bankWordRootStartCountNextLapCost ring hn hbank root s hs
                    y (bankWordEpochReachableOfFrom ring root s z₀ y hz₀ hy)
                    V)
            (fun w hw hcw V => ih w hw (by omega) V)
          have hmul : n * (5 * n - 4) + j * (n * (5 * n - 4)) =
              (j + 1) * (n * (5 * n - 4)) := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          rw [← hmul]
          exact hstage U
  exact hchain (bankWordRenewalLease n + 2) z₀
    (bankWordEpochReachableFromSelf ring root z₀) (Nat.le_refl _) T

/-- `(L+2) n(5n-4) ≤ 6n² + (L+1)(5n²+2n)`: the lap chain fits the
consumer's (E.B) budget.  Consumer: the clock below. -/
theorem bankWordEpochLapBudgetArithmetic (n L : Nat) :
    (L + 2) * (n * (5 * n - 4)) ≤
      6 * n ^ 2 + (L + 1) * (5 * n ^ 2 + 2 * n) := by
  have hfirst : n * (5 * n - 4) ≤ 5 * n ^ 2 := by
    calc
      n * (5 * n - 4) ≤ n * (5 * n) :=
        Nat.mul_le_mul_left n (Nat.sub_le _ _)
      _ = 5 * n ^ 2 := by
        rw [Nat.pow_two]
        ac_rfl
  have h2 : (L + 2) * (n * (5 * n - 4)) ≤ (L + 2) * (5 * n ^ 2) :=
    Nat.mul_le_mul_left _ hfirst
  have h3 : (L + 2) * (5 * n ^ 2) =
      (L + 1) * (5 * n ^ 2) + 5 * n ^ 2 := by
    show (L + 1 + 1) * (5 * n ^ 2) = _
    rw [Nat.add_mul, Nat.one_mul]
  have h4 : (L + 1) * (5 * n ^ 2) ≤ (L + 1) * (5 * n ^ 2 + 2 * n) :=
    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have h5 : 5 * n ^ 2 ≤ 6 * n ^ 2 :=
    Nat.mul_le_mul_right _ (by decide)
  calc
    (L + 2) * (n * (5 * n - 4)) ≤ (L + 2) * (5 * n ^ 2) := h2
    _ = (L + 1) * (5 * n ^ 2) + 5 * n ^ 2 := h3
    _ ≤ (L + 1) * (5 * n ^ 2 + 2 * n) + 6 * n ^ 2 :=
      Nat.add_le_add h4 h5
    _ = 6 * n ^ 2 + (L + 1) * (5 * n ^ 2 + 2 * n) := Nat.add_comm _ _

/-- The consumer's W-stage clock from the lap count: the first ghost
launch is no later than the first genuine acceptance (entrance lemma),
which costs at most `(L+2) n(5n-4)` by the lap chain.
Consumer: `bankWordProjectedOneEpochCostOfWorkerClock`. -/
theorem bankWordEpochPostSOneWorkerClockOfLapCount {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hlap : BankWordEpochLapCount ring root s) :
    BankWordEpochPostSOneWorkerClock ring root s := by
  intro z₀ hz₀ hstop T
  have hD : ∀ x, BankWordEpochReachableFrom ring root z₀ x → ∀ e,
      BankWordEpochReachableFrom ring root z₀
        (bankWordEpochNext ring root x e) :=
    fun x hx e => bankWordEpochReachableFromNext ring root z₀ x hx e
  have hentr : ∀ x, BankWordEpochReachableFrom ring root z₀ x →
      ¬ ((bankWordHardEpochLedger ring root z₀).hardEpochs <
        (bankWordHardEpochLedger ring root x).hardEpochs) →
      ∀ e, (bankWordHardEpochLedger ring root z₀).hardEpochs <
        (bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root x e)).hardEpochs →
      BankWordEpochWorkerLaunched (bankWordEpochNext ring root x e) := by
    intro x hx hnot e hnext
    have hx' := bankWordEpochReachableOfFrom ring root s z₀ x hz₀ hx
    have hinc : (bankWordHardEpochLedger ring root x).hardEpochs <
        (bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root x e)).hardEpochs := by
      omega
    exact bankWordEpochLaunchedOfGenuine ring root s x hx' e
      (bankWordHardEpochGenuineOfCountIncrease ring root x e hinc)
  calc
    costNumerator (bankWordEpochNext ring root)
        BankWordEpochWorkerLaunched z₀ T ≤
      costNumerator (bankWordEpochNext ring root)
        (fun y => (bankWordHardEpochLedger ring root z₀).hardEpochs <
          (bankWordHardEpochLedger ring root y).hardEpochs) z₀ T :=
      costNumerator_entrance_le_on (bankWordEpochNext ring root)
        (BankWordEpochReachableFrom ring root z₀) _ _ hD hentr T z₀
        (bankWordEpochReachableFromSelf ring root z₀)
        (Nat.lt_irrefl _)
    _ ≤ n ^ T * ((bankWordRenewalLease n + 2) * (n * (5 * n - 4))) :=
      bankWordEpochGenuineCostOfLapCount ring hn hbank root s hs hlap
        z₀ hz₀ hstop T
    _ ≤ n ^ T * (6 * n ^ 2 +
        (8 * ceilLogTwo (ceilLogTwo n) + 5) * (5 * n ^ 2 + 2 * n)) := by
      have hL : 8 * ceilLogTwo (ceilLogTwo n) + 5 =
          bankWordRenewalLease n + 1 := by
        unfold bankWordRenewalLease
        omega
      rw [hL]
      exact Nat.mul_le_mul_left _
        (bankWordEpochLapBudgetArithmetic n (bankWordRenewalLease n))


/-! ## Serializer and lease rows at the root, by post-E edge class -/

/-- At a root-outgoing edge no SI row completes a worker: the three
completing rows P0, P2, A0 need a leader responder.
Consumer: the root lease after a root-outgoing service. -/
theorem bankWordRootOutgoingNoDone {c : Compiled} (x y : ProjW c)
    (hy : (postW x y).eY.l = false) :
    (workerW x y).done = false := by
  simp [workerW, siStep, ProjW.lift, hy]
  repeat' (first | rfl | split)

/-- The new root lease on a root-outgoing edge is the literal
leasePair with a false completion bit.  Consumer: lap invariant. -/
theorem bankWordRootOutgoingLease {c : Compiled} (x y : ProjW c)
    (hy : (postW x y).eY.l = false) :
    (pairW x y).1.siLease =
      (leasePair c x.siLease y.siLease
        (serW x y).hard.hardAccept (serW x y).hard.softAccept false).1 := by
  have hd := bankWordRootOutgoingNoDone x y hy
  simp [pairW, hd]

/-- On an incoming root edge the responder lease never increases
(no hard reload without a leader initiator).  Consumer: lap invariant. -/
theorem bankWordIncomingLeaseLe (c : Compiled)
    (a b : Fin (c.siLeaseMax + 1)) (soft done : Bool) :
    (leasePair c a b false soft done).2.val ≤ b.val := by
  cases done <;> cases soft <;> simp [leasePair]

/-- Incoming root edge: the hard-accept flag is off and the root
serializer is either requested from idle or unchanged.
Consumer: lap invariant, incoming case. -/
theorem bankWordRootIncomingRows {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true) :
    (serW x y).hard.hardAccept = false ∧
    (y.ser.cert = .IDLE → (serW x y).y.cert = .REQUESTED) ∧
    (y.ser.cert ≠ .IDLE → (serW x y).y = y.ser) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [serW, serializerStep, ProjW.lift, hx]
  · intro hc
    exact (serRootIncomingIdle x y hx hy hc).2
  · intro hc
    simp [serW, serializerStep, ProjW.lift, hx, hy, hc]

/-- Root-outgoing edge at a REQUESTED root: the S1 row, with the
fresh wphase chosen by the lease and no acceptance flag.
Consumer: lap invariant, start case. -/
theorem bankWordRootOutgoingStartRows {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hreq : x.ser.cert = .REQUESTED) :
    (serW x y).row = "S1" ∧
    (serW x y).x.cert = .RUNNING ∧
    (serW x y).hard.hardAccept = false ∧
    (serW x y).hard.softAccept = false ∧
    (x.siLease.val = 0 → (serW x y).x.wphase = .VALIDATING) ∧
    (0 < x.siLease.val → (serW x y).x.wphase = .CURRENT) := by
  refine ⟨(serRootOutgoingStart x y hx hy hreq).1,
    (serRootOutgoingStart x y hx hy hreq).2.1, ?_, ?_, ?_, ?_⟩
  · simp [serW, serializerStep, ProjW.lift, hreq]
  · simp [serW, serializerStep, ProjW.lift, hreq]
  · intro hzero
    exact (bankWordHardEpochZeroLeaseHardStart x y hx hy hreq hzero).2.2
  · intro hpos
    exact (bankWordRenewalFrontierSoftSOneDoesNotValidate
      x y hx hy hreq hpos).2.2.1

/-- Root-outgoing edge at an IDLE root: never S1, root stays IDLE,
no acceptance flag.  Consumer: lap invariant, idle case. -/
theorem bankWordRootOutgoingIdleRows {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hidle : x.ser.cert = .IDLE) :
    (serW x y).row ≠ "S1" ∧
    (serW x y).x.cert = .IDLE ∧
    (serW x y).hard.hardAccept = false ∧
    (serW x y).hard.softAccept = false := by
  cases hp : x.ser.phase <;>
    cases ho : x.ser.out <;>
    cases hpy : y.ser.phase <;>
    cases hpr : y.ser.probe <;>
    simp [serW, serializerStep, ProjW.lift, serTbStar,
      serChallengeWrite, serEnterB, serEnterF,
      hx, hy, hidle, hp, ho, hpy, hpr]

/-- Root-outgoing edge at a RUNNING/B root outside the S6 guard:
never S1, root stays RUNNING/B with the same wphase, no flag.
Consumer: lap invariant, running case. -/
theorem bankWordRootOutgoingRunningFrameRows {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hrun : x.ser.cert = .RUNNING)
    (hb : x.ser.phase = .B)
    (hnot : ¬ (x.ser.out = .DONE ∧ y.ser.phase = .F)) :
    (serW x y).row ≠ "S1" ∧
    (serW x y).x.cert = .RUNNING ∧
    (serW x y).x.phase = .B ∧
    (serW x y).x.wphase = x.ser.wphase ∧
    (serW x y).hard.hardAccept = false ∧
    (serW x y).hard.softAccept = false := by
  cases ho : x.ser.out <;>
    cases hpy : y.ser.phase <;>
    cases hpr : y.ser.probe <;>
    simp [serW, serializerStep, ProjW.lift,
      serChallengeWrite, serEnterB, serEnterF,
      hx, hy, hrun, hb, ho, hpy, hpr] at hnot ⊢

/-- Root-outgoing edge at a RUNNING/B root inside the S6 guard:
the S6 row, root becomes IDLE, and the acceptance flag follows the
old wphase.  Consumer: lap invariant, finish case. -/
theorem bankWordRootOutgoingFinishRows {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hrun : x.ser.cert = .RUNNING)
    (hb : x.ser.phase = .B)
    (ho : x.ser.out = .DONE)
    (hf : y.ser.phase = .F) :
    (serW x y).row = "S6" ∧
    (serW x y).x.cert = .IDLE ∧
    (x.ser.wphase = .CURRENT →
      (serW x y).hard.softAccept = true ∧
      (serW x y).hard.hardAccept = false) ∧
    (x.ser.wphase = .VALIDATING →
      (serW x y).hard.hardAccept = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [serW, serializerStep, ProjW.lift, hx, hy, hrun, hb, ho, hf]
  · simp [serW, serializerStep, ProjW.lift, hx, hy, hrun, hb, ho, hf]
  · intro hw
    simp [serW, serializerStep, ProjW.lift, hx, hy, hrun, hb, ho, hf, hw]
  · intro hw
    simp [serW, serializerStep, ProjW.lift, hx, hy, hrun, hb, ho, hf, hw]

/-- Any root-outgoing S6 row leaves the root IDLE (both the flagged
RUNNING finish and the neutral IDLE finish).  Consumer: the
lineage base after an observed root S6. -/
theorem bankWordRootOutgoingSixIdle {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hrow : (serW x y).row = "S6") :
    (serW x y).x.cert = .IDLE := by
  cases hc : x.ser.cert <;>
    cases hp : x.ser.phase <;>
    cases ho : x.ser.out <;>
    cases hpy : y.ser.phase <;>
    simp [serW, serializerStep, ProjW.lift, serTbStar,
      serChallengeWrite, serEnterB, serEnterF,
      hx, hy, hc, hp, ho, hpy] at hrow ⊢

/-! ## Root record frames on the epoch chain -/

theorem bankWordEpochFixedRoot {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    WFixedRoot ring root z.2.1 :=
  (bankWordSerializerRootClassClosed ring hn hbank root).1 _
    (bankWordEpochReachablePhysicalRootClass ring hn hbank root s hs z hz)

theorem bankWordEpochFixedRootNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n) :
    WFixedRoot ring root (phiW ring z.2.1 e) := by
  have h := bankWordEpochFixedRoot ring hn hbank root s hs
    (bankWordEpochNext ring root z e)
    (bankWordEpochReachableNext ring root s z hz e)
  rw [bankWordEpochPhysicalNext] at h
  exact h

theorem bankWordEpochRootOutgoingRecord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) :
    (bankWordEpochNext ring root z root).2.1 root =
      (pairW (z.2.1 root) (z.2.1 (ring.rightNeighbor root))).1 := by
  rw [bankWordEpochPhysicalNext]
  simp [phiW, projectedEdge]

theorem bankWordEpochRootIncomingRecord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hj : ring.rightNeighbor e = root) (hne : root ≠ e) :
    (bankWordEpochNext ring root z e).2.1 root =
      (pairW (z.2.1 e) (z.2.1 root)).2 := by
  rw [bankWordEpochPhysicalNext]
  simp [phiW, projectedEdge, hj, hne]


/-! ## Observed root S6 and the post-latch root facts -/

/-- A root-outgoing S6 service has been recorded by the origin
observer.  After it the root is IDLE, so the J-W lineage holds
vacuously and is then carried by the lineage step. -/
def BankWordEpochEverSix {n : Nat} (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  ∃ r : WEdgeReceipt n (compileAdvice (ceilLogTwo n)),
    r ∈ z.2.2.services ∧ r.edge = root ∧ r.serializer.row = "S6"

theorem bankWordEpochEverSixNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (h : BankWordEpochEverSix root z) :
    BankWordEpochEverSix root (bankWordEpochNext ring root z e) := by
  obtain ⟨r, hr, he, hrow⟩ := h
  refine ⟨r, ?_, he, hrow⟩
  rw [bankWordEpochNextServices]
  exact List.mem_cons.mpr (Or.inr hr)

theorem bankWordEpochEverSixOfRow {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (he : e = root)
    (hrow : (serW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).row = "S6") :
    BankWordEpochEverSix root (bankWordEpochNext ring root z e) := by
  refine ⟨bankWordEpochSelectedReceipt ring z e, ?_, he, hrow⟩
  rw [bankWordEpochNextServices]
  exact List.mem_cons.mpr (Or.inl rfl)

theorem bankWordEpochEverSixNextCases {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (h : BankWordEpochEverSix root (bankWordEpochNext ring root z e)) :
    BankWordEpochEverSix root z ∨
      (e = root ∧
        (serW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).row = "S6") := by
  obtain ⟨r, hr, he, hrow⟩ := h
  rw [bankWordEpochNextServices] at hr
  rcases List.mem_cons.mp hr with hr | hr
  · subst hr
    exact Or.inr ⟨he, hrow⟩
  · exact Or.inl ⟨r, hr, he, hrow⟩

/-- Post-latch root facts carried from the entrance: a RUNNING root is
CURRENT or VALIDATING (its wphase was set by an observed S1), and an
IDLE or REQUESTED root has an observed root S6 behind it.
Consumer: the lap invariant. -/
def BankWordEpochPostLatchRootFacts {n : Nat} (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  BankWordEpochSOneReached z →
    ((z.2.1 root).ser.cert = .RUNNING →
      (z.2.1 root).ser.wphase = .CURRENT ∨
        (z.2.1 root).ser.wphase = .VALIDATING) ∧
    (((z.2.1 root).ser.cert = .IDLE ∨ (z.2.1 root).ser.cert = .REQUESTED) →
      BankWordEpochEverSix root z)

theorem bankWordEpochPostLatchRootFactsStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hF : BankWordEpochPostLatchRootFacts root z) :
    BankWordEpochPostLatchRootFacts root (bankWordEpochNext ring root z e) := by
  intro hstop'
  have hn2 : 2 ≤ n := by omega
  have hfixed := bankWordEpochFixedRootNext ring hn hbank root s hs z hz e
  have hrunB := bankWordEpochSOneRunningBReachable ring root hn hbank s hs z hz
  by_cases hstop : BankWordEpochSOneReached z
  · obtain ⟨hW, hSix⟩ := hF hstop
    rcases clockPostTrichotomy ring root z.2.1 e hn2 hfixed with
      ⟨he, hpx, hpy⟩ | ⟨hj, hpx, hpy⟩ | ⟨hne, hnj, hpx, hpy⟩
    · subst e
      rw [bankWordEpochRootOutgoingRecord, pairW_ser_left]
      cases hc : (z.2.1 root).ser.cert with
      | IDLE =>
          obtain ⟨_, hcert, _, _⟩ :=
            bankWordRootOutgoingIdleRows _ _ hpx hpy hc
          rw [hcert]
          exact ⟨(fun h => by cases h),
            fun _ => bankWordEpochEverSixNext ring root z root (hSix (Or.inl hc))⟩
      | REQUESTED =>
          obtain ⟨_, hcert, _, _, hzero, hpos⟩ :=
            bankWordRootOutgoingStartRows _ _ hpx hpy hc
          rw [hcert]
          refine ⟨fun _ => ?_, (fun h => by rcases h with h | h <;> cases h)⟩
          by_cases hl : (z.2.1 root).siLease.val = 0
          · exact Or.inr (hzero hl)
          · exact Or.inl (hpos (Nat.pos_of_ne_zero hl))
      | RUNNING =>
          have hb : (z.2.1 root).ser.phase = .B := hrunB.2 hstop hc
          by_cases hG : (z.2.1 root).ser.out = .DONE ∧
              (z.2.1 (ring.rightNeighbor root)).ser.phase = .F
          · obtain ⟨hrow, hcert, _, _⟩ :=
              bankWordRootOutgoingFinishRows _ _ hpx hpy hc hb hG.1 hG.2
            rw [hcert]
            exact ⟨(fun h => by cases h),
              fun _ => bankWordEpochEverSixOfRow ring root z root rfl hrow⟩
          · obtain ⟨_, hcert, _, hw, _, _⟩ :=
              bankWordRootOutgoingRunningFrameRows _ _ hpx hpy hc hb hG
            rw [hcert, hw]
            exact ⟨fun _ => hW hc, (fun h => by rcases h with h | h <;> cases h)⟩
    · have hne : root ≠ e := by
        rw [← hj]
        exact clockNeighborDifferent ring hn2 e
      rw [hj] at hpx hpy
      rw [bankWordEpochRootIncomingRecord ring root z e hj hne, pairW_ser_right]
      obtain ⟨_, hidle, hkeep⟩ := bankWordRootIncomingRows (z.2.1 e) (z.2.1 root) hpx hpy
      by_cases hc : (z.2.1 root).ser.cert = .IDLE
      · rw [hidle hc]
        exact ⟨(fun h => by cases h),
          fun _ => bankWordEpochEverSixNext ring root z e (hSix (Or.inl hc))⟩
      · rw [hkeep hc]
        exact ⟨hW, fun h => bankWordEpochEverSixNext ring root z e (hSix h)⟩
    · rw [bankWordHardEpochRootRemoteFrame ring root z e (Ne.symm hne) (Ne.symm hnj)]
      exact ⟨hW, fun h => bankWordEpochEverSixNext ring root z e (hSix h)⟩
  · -- the latch edge itself: the synchronized active observer stops at a root S1
    have hnode : ∃ w, z.1 = .active w := by
      cases hz1 : z.1 with
      | stopped =>
          exact absurd (show BankWordEpochSOneReached z by
            change clockSerializerIsStopped z.1
            rw [hz1]
            exact True.intro) hstop
      | active w => exact ⟨w, rfl⟩
    obtain ⟨w, hw⟩ := hnode
    have hweq : w = z.2.1 := hrunB.1 w hw
    have hserv : clockSerializerSOneService ring root z.2.1 e := by
      have h := hstop'
      change clockSerializerIsStopped
        (clockSerializerSOneOnlyNext ring root z.1 e) at h
      rw [hw, hweq] at h
      exact (clockSerializerSOneOnlyStopIff ring root z.2.1 e).mp h
    obtain ⟨he, hrow⟩ := hserv
    subst e
    have hpost := clockPostOutgoing ring root z.2.1 root hn2 hfixed rfl
    have hreq : (z.2.1 root).ser.cert = .REQUESTED :=
      ((clockSerializerSOneIffRequested ring root z.2.1 hn2 hfixed root).mp
        (And.intro rfl hrow)).2
    obtain ⟨_, hcert, _, _, hzero, hpos⟩ :=
      bankWordRootOutgoingStartRows _ _ hpost.1 hpost.2 hreq
    rw [bankWordEpochRootOutgoingRecord, pairW_ser_left, hcert]
    refine ⟨fun _ => ?_, (fun h => by rcases h with h | h <;> cases h)⟩
    by_cases hl : (z.2.1 root).siLease.val = 0
    · exact Or.inr (hzero hl)
    · exact Or.inl (hpos (Nat.pos_of_ne_zero hl))

theorem bankWordEpochPostLatchRootFactsReachable {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordEpochPostLatchRootFacts root z := by
  obtain ⟨word, hword⟩ := hz
  rw [← hword]
  have key : ∀ (w : List (Fin n)) (a : BankWordEpochState n),
      BankWordEpochReachable ring root s a →
      BankWordEpochPostLatchRootFacts root a →
      BankWordEpochPostLatchRootFacts root (bankWordEpochRun ring root a w) := by
    intro w
    induction w with
    | nil => intro a _ h; exact h
    | cons e rest ih =>
        intro a ha h
        exact ih _ (bankWordEpochReachableNext ring root s a ha e)
          (bankWordEpochPostLatchRootFactsStep ring hn hbank root s hs a ha e h)
  exact key word (bankWordEpochStart s) ⟨[], rfl⟩ ((fun h => by cases h))

/-! ## The J-W lineage step (named input) carries the lineage after
an observed root S6 -/

/-- The J-W all-edges step on the represented root class: the single
non-row input of the lap-count route.
Consumer: `bankWordRenewalLineageQuietOfEverSix`. -/
def BankWordRenewalLineageQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z →
    BankWordRenewalFrontierWaveLineageQuiet ring root z →
    ∀ e : Fin n,
      BankWordRenewalFrontierWaveLineageQuiet ring root
        (bankWordEpochNext ring root z e)

/-- At an IDLE root every lineage clause is vacuous.
Consumer: the base of the lineage carry after a root S6. -/
theorem bankWordRenewalLineageQuietOfIdle {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hidle : (z.2.1 root).ser.cert = .IDLE) :
    BankWordRenewalFrontierWaveLineageQuiet ring root z := by
  refine ⟨⟨⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, fun h => ?_⟩,
    fun hactive => ?_⟩
  · rw [hidle] at h
    cases h
  · rw [hidle] at h
    cases h.1
  · rw [hidle] at h
    cases h.1
  · rw [hidle] at h
    cases h.1
  · rw [hidle] at hactive
    cases hactive.1

/-- Once a root S6 has been observed, the J-W lineage holds at every
later reachable state: vacuous right after the S6 (root IDLE), then
carried by the lineage step.  Consumer: genuineness of the hard S6
that ends a post-S6 hard wave. -/
theorem bankWordRenewalLineageQuietOfEverSix {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hsix : BankWordEpochEverSix root z) :
    BankWordRenewalFrontierWaveLineageQuiet ring root z := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨word, hword⟩ := hz
  rw [← hword] at hsix ⊢
  have key : ∀ (w : List (Fin n)) (a : BankWordEpochState n),
      BankWordEpochReachable ring root s a →
      (BankWordEpochEverSix root a →
        BankWordRenewalFrontierWaveLineageQuiet ring root a) →
      (BankWordEpochEverSix root (bankWordEpochRun ring root a w) →
        BankWordRenewalFrontierWaveLineageQuiet ring root
          (bankWordEpochRun ring root a w)) := by
    intro w
    induction w with
    | nil => intro a _ h; exact h
    | cons e rest ih =>
        intro a ha h
        apply ih (bankWordEpochNext ring root a e)
          (bankWordEpochReachableNext ring root s a ha e)
        intro hsix'
        rcases bankWordEpochEverSixNextCases ring root a e hsix' with hold | ⟨he, hrow⟩
        · exact hstep a ha (h hold) e
        · subst e
          have hfixed := bankWordEpochFixedRootNext ring hn hbank root s hs a ha root
          have hpost := clockPostOutgoing ring root a.2.1 root hn2 hfixed rfl
          have hidle : ((bankWordEpochNext ring root a root).2.1 root).ser.cert = .IDLE := by
            rw [bankWordEpochRootOutgoingRecord, pairW_ser_left]
            exact bankWordRootOutgoingSixIdle _ _ hpost.1 hpost.2 hrow
          exact bankWordRenewalLineageQuietOfIdle ring root _ hidle
  refine key word (bankWordEpochStart s) ⟨[], rfl⟩ ?_ hsix
  intro h
  obtain ⟨r, hr, _, _⟩ := h
  simp [bankWordEpochStart, wOriginInitial] at hr

/-! ## The lap invariant relative to a post-S1 start -/

theorem bankWordEpochSOneReachedFrom {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z₀ z : BankWordEpochState n)
    (hz : BankWordEpochReachableFrom ring root z₀ z)
    (h0 : BankWordEpochSOneReached z₀) :
    BankWordEpochSOneReached z := by
  obtain ⟨w, hw⟩ := hz
  rw [← hw]
  have key : ∀ (w : List (Fin n)) (a : BankWordEpochState n),
      BankWordEpochSOneReached a →
      BankWordEpochSOneReached (bankWordEpochRun ring root a w) := by
    intro w
    induction w with
    | nil => intro a h; exact h
    | cons e rest ih =>
        intro a h
        exact ih _ (bankWordEpochSOneReachedNext ring root a h e)
  exact key w z₀ h0

theorem bankWordHardEpochCountFrom {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z₀ z : BankWordEpochState n)
    (hz : BankWordEpochReachableFrom ring root z₀ z) :
    (bankWordHardEpochLedger ring root z₀).hardEpochs ≤
      (bankWordHardEpochLedger ring root z).hardEpochs := by
  obtain ⟨w, hw⟩ := hz
  rw [← hw]
  have key : ∀ (w : List (Fin n)) (a : BankWordEpochState n),
      (bankWordHardEpochLedger ring root a).hardEpochs ≤
        (bankWordHardEpochLedger ring root
          (bankWordEpochRun ring root a w)).hardEpochs := by
    intro w
    induction w with
    | nil => intro a; exact Nat.le_refl _
    | cons e rest ih =>
        intro a
        exact Nat.le_trans (bankWordHardEpochCountMono ring root a e)
          (ih (bankWordEpochNext ring root a e))
  exact key w z₀

/-- The lap invariant relative to `z₀`, while no genuine acceptance
has happened since `z₀`: with `d` the root S1 services since `z₀`,
`ℓ` the root lease and `L` the lease cap, an IDLE/REQUESTED root has
`d ≤ L - ℓ`, a CURRENT wave has `d ≤ L + 1 - ℓ` and `d ≤ L`, and a
VALIDATING wave has `d ≤ L + 1` and either `d = 0` or an observed
root S6 (so its S6 will be genuine).  Consumer: `BankWordEpochLapCount`. -/
def BankWordEpochLapInvariant {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z₀ y : BankWordEpochState n) : Prop :=
  (bankWordHardEpochLedger ring root y).hardEpochs =
      (bankWordHardEpochLedger ring root z₀).hardEpochs →
  (((y.2.1 root).ser.cert = .IDLE ∨ (y.2.1 root).ser.cert = .REQUESTED) →
      bankWordRootStartCount root y + (y.2.1 root).siLease.val ≤
        bankWordRootStartCount root z₀ +
          (compileAdvice (ceilLogTwo n)).siLeaseMax) ∧
  ((y.2.1 root).ser.cert = .RUNNING →
    (y.2.1 root).ser.wphase = .CURRENT →
      bankWordRootStartCount root y + (y.2.1 root).siLease.val ≤
        bankWordRootStartCount root z₀ +
          (compileAdvice (ceilLogTwo n)).siLeaseMax + 1 ∧
      bankWordRootStartCount root y ≤
        bankWordRootStartCount root z₀ +
          (compileAdvice (ceilLogTwo n)).siLeaseMax) ∧
  ((y.2.1 root).ser.cert = .RUNNING →
    (y.2.1 root).ser.wphase = .VALIDATING →
      bankWordRootStartCount root y ≤
        bankWordRootStartCount root z₀ +
          (compileAdvice (ceilLogTwo n)).siLeaseMax + 1 ∧
      (bankWordRootStartCount root y = bankWordRootStartCount root z₀ ∨
        BankWordEpochEverSix root y))

theorem bankWordEpochLapInvariantSelf {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z₀ : BankWordEpochState n) :
    BankWordEpochLapInvariant ring root z₀ z₀ := by
  intro _
  have hl : (z₀.2.1 root).siLease.val ≤
      (compileAdvice (ceilLogTwo n)).siLeaseMax :=
    Nat.le_of_lt_succ (z₀.2.1 root).siLease.isLt
  refine ⟨fun _ => by omega, fun _ _ => ⟨by omega, by omega⟩,
    fun _ _ => ⟨by omega, Or.inl rfl⟩⟩

theorem bankWordEpochLapInvariantStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s)
    (z₀ : BankWordEpochState n)
    (hz₀ : BankWordEpochReachable ring root s z₀)
    (hstop : BankWordEpochSOneReached z₀)
    (y : BankWordEpochState n)
    (hy : BankWordEpochReachableFrom ring root z₀ y) (e : Fin n)
    (hinv : BankWordEpochLapInvariant ring root z₀ y) :
    BankWordEpochLapInvariant ring root z₀ (bankWordEpochNext ring root y e) := by
  intro hE'
  have hn2 : 2 ≤ n := by omega
  have hyR : BankWordEpochReachable ring root s y :=
    bankWordEpochReachableOfFrom ring root s z₀ y hz₀ hy
  have hEy : (bankWordHardEpochLedger ring root y).hardEpochs =
      (bankWordHardEpochLedger ring root z₀).hardEpochs := by
    have h1 := bankWordHardEpochCountMono ring root y e
    have h2 := bankWordHardEpochCountFrom ring root z₀ y hy
    omega
  obtain ⟨hI, hC, hV⟩ := hinv hEy
  have hstopy : BankWordEpochSOneReached y :=
    bankWordEpochSOneReachedFrom ring root z₀ y hy hstop
  obtain ⟨hW, hSix⟩ :=
    bankWordEpochPostLatchRootFactsReachable ring hn hbank root s hs y hyR hstopy
  have hrunB := (bankWordEpochSOneRunningBReachable ring root hn hbank s hs y hyR).2 hstopy
  have hfixed := bankWordEpochFixedRootNext ring hn hbank root s hs y hyR e
  have hcnt := bankWordRootStartCountNext ring root y e
  rcases clockPostTrichotomy ring root y.2.1 e hn2 hfixed with
    ⟨he, hpx, hpy⟩ | ⟨hj, hpx, hpy⟩ | ⟨hne, hnj, hpx, hpy⟩
  · subst e
    rw [bankWordEpochRootOutgoingRecord, pairW_ser_left,
      bankWordRootOutgoingLease _ _ hpy, hcnt]
    cases hc : (y.2.1 root).ser.cert with
    | IDLE =>
        obtain ⟨hrowne, hcert, hha, hsa⟩ :=
          bankWordRootOutgoingIdleRows _ _ hpx hpy hc
        have hno : ¬ clockSerializerSOneService ring root y.2.1 root :=
          fun h => hrowne h.2
        rw [hcert, hha, hsa, bankWordHardEpochSourceLeaseQuiet, if_neg hno]
        refine ⟨fun _ => ?_, (fun h => by cases h), (fun h => by cases h)⟩
        have := hI (Or.inl hc)
        omega
    | REQUESTED =>
        obtain ⟨hrow, hcert, hha, hsa, hzero, hpos⟩ :=
          bankWordRootOutgoingStartRows _ _ hpx hpy hc
        have hyes : clockSerializerSOneService ring root y.2.1 root :=
          And.intro rfl hrow
        have hIy := hI (Or.inr hc)
        have hsixy := hSix (Or.inr hc)
        rw [hcert, hha, hsa, bankWordHardEpochSourceLeaseQuiet, if_pos hyes]
        by_cases hl : (y.2.1 root).siLease.val = 0
        · rw [hzero hl]
          refine ⟨(fun h => by rcases h with h | h <;> cases h),
            (fun _ h => by cases h), fun _ _ => ⟨by omega, ?_⟩⟩
          exact Or.inr (bankWordEpochEverSixNext ring root y root hsixy)
        · rw [hpos (Nat.pos_of_ne_zero hl)]
          exact ⟨(fun h => by rcases h with h | h <;> cases h),
            fun _ _ => ⟨by omega, by omega⟩, (fun _ h => by cases h)⟩
    | RUNNING =>
        have hb : (y.2.1 root).ser.phase = .B := hrunB hc
        by_cases hG : (y.2.1 root).ser.out = .DONE ∧
            (y.2.1 (ring.rightNeighbor root)).ser.phase = .F
        · obtain ⟨hrow, hcert, hsoft, hhard⟩ :=
            bankWordRootOutgoingFinishRows _ _ hpx hpy hc hb hG.1 hG.2
          have hno : ¬ clockSerializerSOneService ring root y.2.1 root := by
            intro h
            obtain ⟨_, h2⟩ := h
            rw [hrow] at h2
            exact absurd h2 (by decide)
          rw [hcert, if_neg hno]
          rcases hW hc with hw | hw
          · obtain ⟨hsa, hha⟩ := hsoft hw
            rw [hha, hsa, bankWordEpochSoftAcceptanceLeaseRow]
            refine ⟨fun _ => ?_, (fun h => by cases h), (fun h => by cases h)⟩
            have := hC hc hw
            omega
          · have hha := hhard hw
            by_cases hgen : bankWordHardEpochGenuine ring root
                (bankWordEpochSelectedReceipt ring y root)
                (bankWordHardEpochLedger ring root y) = true
            · exfalso
              have h1 := bankWordHardEpochCountNext ring root y root
              rw [if_pos hgen] at h1
              omega
            · have hnotsix : ¬ BankWordEpochEverSix root y := by
                intro hsix
                exact hgen (bankWordRenewalFrontierWaveHardAcceptGenuine
                  ring root s hn hbank hs y hyR
                  (bankWordRenewalLineageQuietOfEverSix
                    ring hn hbank root s hs hstep y hyR hsix).wave hha)
              have hcnt0 : bankWordRootStartCount root y =
                  bankWordRootStartCount root z₀ := by
                rcases (hV hc hw).2 with h | h
                · exact h
                · exact absurd h hnotsix
              rw [hha, bankWordEpochHardAcceptanceReloadsLease]
              refine ⟨fun _ => by omega, (fun h => by cases h), (fun h => by cases h)⟩
        · obtain ⟨hrowne, hcert, _, hwph, hha, hsa⟩ :=
            bankWordRootOutgoingRunningFrameRows _ _ hpx hpy hc hb hG
          have hno : ¬ clockSerializerSOneService ring root y.2.1 root :=
            fun h => hrowne h.2
          rw [hcert, hwph, hha, hsa, bankWordHardEpochSourceLeaseQuiet, if_neg hno]
          refine ⟨(fun h => by rcases h with h | h <;> cases h),
            fun _ hw => ?_, fun _ hw => ⟨?_, ?_⟩⟩
          · have := hC hc hw
            omega
          · have := (hV hc hw).1
            omega
          · rcases (hV hc hw).2 with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (bankWordEpochEverSixNext ring root y root h)
  · have hne : root ≠ e := by
      rw [← hj]
      exact clockNeighborDifferent ring hn2 e
    rw [hj] at hpx hpy
    obtain ⟨hha, hidle, hkeep⟩ := bankWordRootIncomingRows (y.2.1 e) (y.2.1 root) hpx hpy
    have hlease : (pairW (y.2.1 e) (y.2.1 root)).2.siLease.val ≤
        (y.2.1 root).siLease.val := by
      show (leasePair (compileAdvice (ceilLogTwo n))
        (y.2.1 e).siLease (y.2.1 root).siLease
        (serW (y.2.1 e) (y.2.1 root)).hard.hardAccept
        (serW (y.2.1 e) (y.2.1 root)).hard.softAccept
        (workerW (y.2.1 e) (y.2.1 root)).done).2.val ≤ _
      rw [hha]
      exact bankWordIncomingLeaseLe _ _ _ _ _
    have hno : ¬ clockSerializerSOneService ring root y.2.1 e :=
      fun h => hne h.1.symm
    rw [bankWordEpochRootIncomingRecord ring root y e hj hne, hcnt, if_neg hno]
    rw [pairW_ser_right]
    by_cases hc : (y.2.1 root).ser.cert = .IDLE
    · rw [hidle hc]
      refine ⟨fun _ => ?_, (fun h => by cases h), (fun h => by cases h)⟩
      have := hI (Or.inl hc)
      omega
    · rw [hkeep hc]
      refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ⟨?_, ?_⟩⟩
      · have := hI h
        omega
      · have := hC h1 h2
        omega
      · have := (hV h1 h2).1
        omega
      · rcases (hV h1 h2).2 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (bankWordEpochEverSixNext ring root y e h)
  · have hno : ¬ clockSerializerSOneService ring root y.2.1 e :=
      fun h => hne h.1
    rw [bankWordHardEpochRootRemoteFrame ring root y e (Ne.symm hne) (Ne.symm hnj),
      hcnt, if_neg hno]
    refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ⟨?_, ?_⟩⟩
    · have := hI h
      omega
    · have := hC h1 h2
      omega
    · have := (hV h1 h2).1
      omega
    · rcases (hV h1 h2).2 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (bankWordEpochEverSixNext ring root y e h)

theorem bankWordEpochLapInvariantFrom {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s)
    (z₀ : BankWordEpochState n)
    (hz₀ : BankWordEpochReachable ring root s z₀)
    (hstop : BankWordEpochSOneReached z₀)
    (y : BankWordEpochState n)
    (hy : BankWordEpochReachableFrom ring root z₀ y) :
    BankWordEpochLapInvariant ring root z₀ y := by
  obtain ⟨w, hw⟩ := hy
  rw [← hw]
  have key : ∀ (w : List (Fin n)) (a : BankWordEpochState n),
      BankWordEpochReachableFrom ring root z₀ a →
      BankWordEpochLapInvariant ring root z₀ a →
      BankWordEpochLapInvariant ring root z₀ (bankWordEpochRun ring root a w) := by
    intro w
    induction w with
    | nil => intro a _ h; exact h
    | cons e rest ih =>
        intro a ha h
        exact ih _ (bankWordEpochReachableFromNext ring root z₀ a ha e)
          (bankWordEpochLapInvariantStep ring hn hbank root s hs hstep
            z₀ hz₀ hstop a ha e h)
  exact key w z₀ (bankWordEpochReachableFromSelf ring root z₀)
    (bankWordEpochLapInvariantSelf ring root z₀)

/-- DET from the lap invariant: in every root state `d ≤ L + 1`, so
`L + 2` root S1 services force a genuine acceptance.
Consumer: `bankWordEpochPostSOneWorkerClockOfLineageStep`. -/
theorem bankWordEpochLapCountOfLineageStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s) :
    BankWordEpochLapCount ring root s := by
  intro z₀ hz₀ hstop z hz hcount
  have hinv := bankWordEpochLapInvariantFrom ring hn hbank root s hs hstep
    z₀ hz₀ hstop z hz
  have hmono := bankWordHardEpochCountFrom ring root z₀ z hz
  rcases Nat.lt_or_ge (bankWordHardEpochLedger ring root z₀).hardEpochs
    (bankWordHardEpochLedger ring root z).hardEpochs with h | h
  · exact h
  · exfalso
    have hEq : (bankWordHardEpochLedger ring root z).hardEpochs =
        (bankWordHardEpochLedger ring root z₀).hardEpochs :=
      Nat.le_antisymm h hmono
    obtain ⟨hI, hC, hV⟩ := hinv hEq
    have hLdef : bankWordRenewalLease n =
        (compileAdvice (ceilLogTwo n)).siLeaseMax := by
      unfold bankWordRenewalLease
      exact (bankWordHardEpochBankLeaseMaximum hbank).symm
    rw [hLdef] at hcount
    have hzR : BankWordEpochReachable ring root s z :=
      bankWordEpochReachableOfFrom ring root s z₀ z hz₀ hz
    have hstopz := bankWordEpochSOneReachedFrom ring root z₀ z hz hstop
    obtain ⟨hW, _⟩ :=
      bankWordEpochPostLatchRootFactsReachable ring hn hbank root s hs z hzR hstopz
    cases hc : (z.2.1 root).ser.cert with
    | IDLE =>
        have := hI (Or.inl hc)
        omega
    | REQUESTED =>
        have := hI (Or.inr hc)
        omega
    | RUNNING =>
        rcases hW hc with hw | hw
        · have := hC hc hw
          omega
        · have := (hV hc hw).1
          omega

/-- R10a W-stage clock from the J-W lineage step alone.
Consumer: `bankWordProjectedOneEpochCostOfWorkerClock` /
`bankWordProjectedOneEpochExpectedOfWorkerClock`. -/
theorem bankWordEpochPostSOneWorkerClockOfLineageStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s) :
    BankWordEpochPostSOneWorkerClock ring root s :=
  bankWordEpochPostSOneWorkerClockOfLapCount ring hn hbank root s hs
    (bankWordEpochLapCountOfLineageStep ring hn hbank root s hs hstep)

/-- The consumer's one-epoch expected bound, conditional only on the
J-W lineage step.  Consumer: R10a board row. -/
theorem bankWordProjectedOneEpochExpectedOfLineageStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (bankWordEpochNext ring root)
      BankWordEpochWorkerLaunched
      (bankWordEpochStart s)
      ((11 * (8 * ceilLogTwo (ceilLogTwo n) + 5) *
        n ^ 2 : Nat) : Rat) :=
  bankWordProjectedOneEpochExpectedOfWorkerClock ring hn hbank root s hs
    (bankWordEpochPostSOneWorkerClockOfLineageStep ring hn hbank root s hs hstep)


/-! ## The same lap count pays the renewal attempt cost `hcost` -/

/-- First-hit costs transport along a step-commuting map.
Consumer: the subtype chain of the fresh kernel. -/
theorem costNumerator_map_eq {X Y : Type} {n : Nat}
    (next' : X → Fin n → X) (next : Y → Fin n → Y) (f : X → Y)
    (hf : ∀ x e, f (next' x e) = next (f x) e) (P : Y → Prop) :
    ∀ (T : Nat) (x : X),
      costNumerator next' (fun x => P (f x)) x T =
        costNumerator next P (f x) T := by
  intro T
  induction T with
  | zero => intro x; rfl
  | succ T ih =>
      intro x
      by_cases hp : P (f x)
      · rw [costNumerator_terminal next' (fun x => P (f x)) x hp (T + 1),
          costNumerator_terminal next P (f x) hp (T + 1)]
      · rw [costNumerator_succ next' (fun x => P (f x)) x hp T,
          costNumerator_succ next P (f x) hp T]
        congr 1
        apply ofFn_sum_eq
        intro e
        rw [← hf x e]
        exact ih (next' x e)

/-- The fresh seed carries no completion receipt: the genuine S6
service launches the worker (I0) and emits none.
Consumer: the attempt-cost simulation base. -/
theorem bankWordRenewalFreshNotCompleted {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (seed : BankWordRenewalFreshSeed ring root s) :
    ¬ BankWordRenewalCompleted seed.1.1 := by
  obtain ⟨pre, e, hg, heq⟩ := seed.2
  rw [← heq]
  obtain ⟨_, _, hhard⟩ :=
    bankWordHardEpochSelectedGenuineOwnerFlags ring root pre.1 e hg
  have hhard' : (serW (pre.1.2.1 e)
      (pre.1.2.1 (ring.rightNeighbor e))).hard.hardAccept = true := hhard
  have hrow := bankWordHardEpochHardAcceptIzeroRow _ _ hhard'
  have hcoh := (bankWordRenewalFrontierLedgerGhostCoherence
    ring root s pre.1 pre.2.1).1
  have hg' := hg
  unfold bankWordRenewalGenuine bankWordHardEpochGenuine at hg'
  rw [hcoh] at hg'
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hg'
  simp only [bankWordEpochSelectedReceipt] at ht
  intro hc
  obtain ⟨r, hr⟩ := hc
  change (wWorkerReceiptStep root e (ring.rightNeighbor e)
      (pre.1.2.2.clock + 1) (pre.1.2.1 e) (pre.1.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e (pre.1.2.1 e)
        (pre.1.2.1 (ring.rightNeighbor e))
        (pre.1.2.2.validation e)
        (pre.1.2.2.validation (ring.rightNeighbor e)))
      pre.1.2.2.worker).2 = some r at hr
  rw [ht] at hr
  simp [wWorkerReceiptStep, hrow] at hr

/-- One fresh attempt costs no more than the physical first hit of
'completed or one more genuine acceptance', from any active node
that is not yet completed and has not seen a new acceptance.
Consumer: `bankWordRenewalFreshAttemptCostOfLineageStep`. -/
theorem bankWordRenewalFreshAttemptCostLe {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (seed : BankWordRenewalFreshSeed ring root s) :
    ∀ (T : Nat) (a : BankWordRenewalPostSOne ring root s),
      ¬ BankWordRenewalCompleted a.1 →
      (bankWordHardEpochLedger ring root a.1).hardEpochs ≤
        (bankWordHardEpochLedger ring root seed.1.1).hardEpochs →
      costNumerator
        (L3.Prob.attemptStepper (bankWordRenewalFreshKernel ring root s))
        (fun q => L3.Prob.attemptGood q ∨ L3.Prob.attemptFail q)
        (.active a) T ≤
      costNumerator (bankWordRenewalNext ring root s)
        (fun v : BankWordRenewalPostSOne ring root s =>
          BankWordRenewalCompleted v.1 ∨
          (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
            (bankWordHardEpochLedger ring root v.1).hardEpochs) a T := by
  intro T
  induction T with
  | zero =>
      intro a _ _
      rw [costNumerator_zero]
      exact Nat.zero_le _
  | succ T ih =>
      intro a hnc hle
      have hnotP : ¬ (BankWordRenewalCompleted a.1 ∨
          (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
            (bankWordHardEpochLedger ring root a.1).hardEpochs) := by
        intro h
        rcases h with h | h
        · exact hnc h
        · omega
      have hnotA : ¬ (L3.Prob.attemptGood
          (.active a : PPL.Convergence.LDLocal.AttemptNode
            (BankWordRenewalPostSOne ring root s)
            (BankWordRenewalFreshSeed ring root s)) ∨
          L3.Prob.attemptFail
          (.active a : PPL.Convergence.LDLocal.AttemptNode
            (BankWordRenewalPostSOne ring root s)
            (BankWordRenewalFreshSeed ring root s))) := by
        simp [L3.Prob.attemptGood, L3.Prob.attemptFail]
      rw [costNumerator_succ
          (L3.Prob.attemptStepper (bankWordRenewalFreshKernel ring root s))
          (fun q => L3.Prob.attemptGood q ∨ L3.Prob.attemptFail q)
          (.active a) hnotA T,
        costNumerator_succ (bankWordRenewalNext ring root s)
          (fun v : BankWordRenewalPostSOne ring root s =>
            BankWordRenewalCompleted v.1 ∨
            (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
              (bankWordHardEpochLedger ring root v.1).hardEpochs)
          a hnotP T]
      apply Nat.add_le_add_left
      apply ofFn_sum_le
      intro e
      show costNumerator
        (L3.Prob.attemptStepper (bankWordRenewalFreshKernel ring root s))
        (fun q => L3.Prob.attemptGood q ∨ L3.Prob.attemptFail q)
        (bankWordRenewalFreshStep ring root s a e) T ≤ _
      by_cases hc : BankWordRenewalCompleted
          (bankWordRenewalNext ring root s a e).1
      · have hs : bankWordRenewalFreshStep ring root s a e = .success := by
          simp [bankWordRenewalFreshStep, hc]
        have hterm : costNumerator
            (L3.Prob.attemptStepper (bankWordRenewalFreshKernel ring root s))
            (fun q => L3.Prob.attemptGood q ∨ L3.Prob.attemptFail q)
            (bankWordRenewalFreshStep ring root s a e) T = 0 := by
          rw [hs]
          exact costNumerator_terminal
            (L3.Prob.attemptStepper (bankWordRenewalFreshKernel ring root s))
            (fun q => L3.Prob.attemptGood q ∨ L3.Prob.attemptFail q)
            .success (Or.inl True.intro) T
        rw [hterm]
        exact Nat.zero_le _
      · by_cases hg : bankWordRenewalGenuine ring root a.1 e
        · have hs : bankWordRenewalFreshStep ring root s a e =
              .retry ⟨bankWordRenewalNext ring root s a e,
                bankWordRenewalFreshAfterGenuine ring root s a e hg⟩ := by
            simp [bankWordRenewalFreshStep, hc, hg]
          have hterm : costNumerator
              (L3.Prob.attemptStepper (bankWordRenewalFreshKernel ring root s))
              (fun q => L3.Prob.attemptGood q ∨ L3.Prob.attemptFail q)
              (bankWordRenewalFreshStep ring root s a e) T = 0 := by
            rw [hs]
            exact costNumerator_terminal
              (L3.Prob.attemptStepper (bankWordRenewalFreshKernel ring root s))
              (fun q => L3.Prob.attemptGood q ∨ L3.Prob.attemptFail q)
              (.retry ⟨bankWordRenewalNext ring root s a e,
                bankWordRenewalFreshAfterGenuine ring root s a e hg⟩)
              (Or.inr True.intro) T
          rw [hterm]
          exact Nat.zero_le _
        · have hs : bankWordRenewalFreshStep ring root s a e =
              .active (bankWordRenewalNext ring root s a e) := by
            simp [bankWordRenewalFreshStep, hc, hg]
          rw [hs]
          apply ih (bankWordRenewalNext ring root s a e) hc
          have hg' : ¬ (bankWordHardEpochGenuine ring root
              (bankWordEpochSelectedReceipt ring a.1 e)
              (bankWordHardEpochLedger ring root a.1) = true) := hg
          have h := bankWordHardEpochCountNext ring root a.1 e
          rw [if_neg hg'] at h
          show (bankWordHardEpochLedger ring root
            (bankWordEpochNext ring root a.1 e)).hardEpochs ≤ _
          rw [h]
          exact hle

/-- `(L+2) n(5n-4) ≤ 11 (L+1) n²`: the lap chain fits one block B.
Consumer: the attempt cost. -/
theorem bankWordEpochLapBlockArithmetic (n L : Nat) :
    (L + 2) * (n * (5 * n - 4)) ≤ 11 * (L + 1) * n ^ 2 := by
  have hfirst : n * (5 * n - 4) ≤ 5 * n ^ 2 := by
    calc
      n * (5 * n - 4) ≤ n * (5 * n) :=
        Nat.mul_le_mul_left n (Nat.sub_le _ _)
      _ = 5 * n ^ 2 := by
        rw [Nat.pow_two]
        ac_rfl
  calc
    (L + 2) * (n * (5 * n - 4)) ≤ (L + 2) * (5 * n ^ 2) :=
      Nat.mul_le_mul_left _ hfirst
    _ = (5 * (L + 2)) * n ^ 2 := by ac_rfl
    _ ≤ (11 * (L + 1)) * n ^ 2 :=
      Nat.mul_le_mul_right _ (by omega)

/-- The renewal attempt cost `hcost` of BankWordRenewalFresh, from
the J-W lineage step alone: every fresh attempt ends (completion or
the next genuine acceptance) within one block B.
Consumer: `bankWordRenewalFreshFiveCostOfBounds`. -/
theorem bankWordRenewalFreshAttemptCostOfLineageStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s) :
    BankWordRenewalFreshAttemptCost ring root s := by
  intro seed T
  have hnc := bankWordRenewalFreshNotCompleted ring root s seed
  calc
    costNumerator
        (L3.Prob.attemptStepper (bankWordRenewalFreshKernel ring root s))
        (fun q => L3.Prob.attemptGood q ∨ L3.Prob.attemptFail q)
        (.active seed.1) T ≤
      costNumerator (bankWordRenewalNext ring root s)
        (fun v : BankWordRenewalPostSOne ring root s =>
          BankWordRenewalCompleted v.1 ∨
          (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
            (bankWordHardEpochLedger ring root v.1).hardEpochs) seed.1 T :=
      bankWordRenewalFreshAttemptCostLe ring root s seed T seed.1 hnc
        (Nat.le_refl _)
    _ ≤ costNumerator (bankWordRenewalNext ring root s)
        (fun v : BankWordRenewalPostSOne ring root s =>
          (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
            (bankWordHardEpochLedger ring root v.1).hardEpochs) seed.1 T :=
      L3.Prob.costNumerator_target_mono (bankWordRenewalNext ring root s)
        (fun v : BankWordRenewalPostSOne ring root s =>
          (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
            (bankWordHardEpochLedger ring root v.1).hardEpochs)
        (fun v : BankWordRenewalPostSOne ring root s =>
          BankWordRenewalCompleted v.1 ∨
          (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
            (bankWordHardEpochLedger ring root v.1).hardEpochs)
        (fun v h => Or.inr h) seed.1 T
    _ = costNumerator (bankWordEpochNext ring root)
        (fun y => (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
          (bankWordHardEpochLedger ring root y).hardEpochs) seed.1.1 T :=
      costNumerator_map_eq (bankWordRenewalNext ring root s)
        (bankWordEpochNext ring root) Subtype.val (fun _ _ => rfl)
        (fun y => (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
          (bankWordHardEpochLedger ring root y).hardEpochs) T seed.1
    _ ≤ n ^ T * ((bankWordRenewalLease n + 2) * (n * (5 * n - 4))) :=
      bankWordEpochGenuineCostOfLapCount ring hn hbank root s hs
        (bankWordEpochLapCountOfLineageStep ring hn hbank root s hs hstep)
        seed.1.1 seed.1.2.1 seed.1.2.2 T
    _ ≤ n ^ T * bankWordRenewalBlock n := by
      unfold bankWordRenewalBlock
      exact Nat.mul_le_mul_left _
        (bankWordEpochLapBlockArithmetic n (bankWordRenewalLease n))

/-- The 5B fresh-renewal completion bound, now conditional only on
the three-quarter retry estimate and the J-W lineage step.
Consumer: R10a 5B completion line of repair.tex. -/
theorem bankWordRenewalFreshFiveCostOfFailure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s)
    (hfail : ∀ seed : BankWordRenewalFreshSeed ring root s,
      ∀ T, 4 * PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s)
        (.active seed.1) T ≤ 3 * n ^ T)
    (seed : BankWordRenewalFreshSeed ring root s)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      seed.1 T ≤ n ^ T * (5 * bankWordRenewalBlock n) :=
  bankWordRenewalFreshFiveCostOfBounds ring root s
    (bankWordRenewalFreshAttemptCostOfLineageStep ring hn hbank root s hs hstep)
    hfail seed T


/-! ## Reduction of the J-W all-edges step to its two moving-row residues -/

/-- The lineage is vacuous whenever the root is neither REQUESTED nor
an active VALIDATING wave.  Consumer: the all-edges reduction. -/
theorem bankWordRenewalLineageQuietOfNonvalidating {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hreq : (z.2.1 root).ser.cert ≠ .REQUESTED)
    (hnv : ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root z := by
  refine ⟨⟨⟨fun h => (hreq h).elim, fun h => (hnv ⟨h.1, h.2.1⟩).elim,
    fun h => (hnv ⟨h.1, h.2.1⟩).elim⟩, fun h => (hnv h).elim⟩,
    fun hactive => (hnv hactive).elim⟩

/-- Residual root moving rows of the J-W step: a
RUNNING/VALIDATING/B root, root-outgoing, neither the S6 guard nor the
stationary B/DONE+B pair (challenge, internal and leaf admissions).
Consumer: `bankWordRenewalLineageQuietStepOfMovingRows`. -/
def BankWordRenewalLineageRootMovingStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z →
    BankWordRenewalFrontierWaveLineageQuiet ring root z →
    (z.2.1 root).ser.cert = .RUNNING →
    (z.2.1 root).ser.wphase = .VALIDATING →
    (z.2.1 root).ser.phase = .B →
    ¬ ((z.2.1 root).ser.out = .DONE ∧
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .F) →
    ¬ ((z.2.1 root).ser.out = .DONE ∧
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .B) →
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root)

/-- Residual internal moving rows of the J-W step (r10w): an active
VALIDATING root and a nonroot edge that is neither unvisited for every
shape witness nor the stationary B/DONE+B pair (moving frontierParent /
challengedChild, RETURN B/DONE -> F, S3 observation, S4 deletion).
Consumer: `bankWordRenewalLineageQuietStepOfMovingRows`. -/
def BankWordRenewalLineageInternalMovingStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z →
    BankWordRenewalFrontierWaveLineageQuiet ring root z →
    (z.2.1 root).ser.cert = .RUNNING →
    (z.2.1 root).ser.wphase = .VALIDATING →
    ∀ e : Fin n, e ≠ root → ring.rightNeighbor e ≠ root →
    ¬ (∀ g : L3.EWord.ValidationGhost,
        L3.EWord.ValidationShape ring root z.2.1 g →
        L3.EWord.validationEdgeClass ring root g e = .unvisitedSuffix) →
    ¬ ((z.2.1 e).ser.phase = .B ∧ (z.2.1 e).ser.out = .DONE ∧
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .B) →
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e)

/-- Every edge class other than the two residues is already closed:
incoming root (any row), root-outgoing at a REQUESTED / IDLE /
nonvalidating root, the S6 guard, the stationary B/DONE+B root pair,
SR at a C/F root, and internal edges with an inactive root, an
unvisited suffix or a stationary covered pair.
Consumer: `bankWordEpochPostSOneWorkerClockOfMovingRows`. -/
theorem bankWordRenewalLineageQuietStepOfMovingRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hroot : BankWordRenewalLineageRootMovingStep ring root s)
    (hint : BankWordRenewalLineageInternalMovingStep ring root s) :
    BankWordRenewalLineageQuietStep ring root s := by
  intro z hz hwave e
  have hn2 : 2 ≤ n := by omega
  have hfixed := bankWordEpochFixedRootNext ring hn hbank root s hs z hz e
  rcases clockPostTrichotomy ring root z.2.1 e hn2 hfixed with
    ⟨he, hpx, hpy⟩ | ⟨hj, hpx, hpy⟩ | ⟨hne, hnj, hpx, hpy⟩
  · subst e
    have hidleNext : ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
        .IDLE → BankWordRenewalFrontierWaveLineageQuiet ring root
          (bankWordEpochNext ring root z root) := by
      intro hidle
      apply bankWordRenewalLineageQuietOfNonvalidating
      · rw [hidle]
        exact fun h => by cases h
      · rw [hidle]
        exact fun h => by cases h.1
    have hrecovery : ((z.2.1 root).ser.cert = .IDLE ∨
          (z.2.1 root).ser.cert = .RUNNING) →
        ((z.2.1 root).ser.phase = .C ∨ (z.2.1 root).ser.phase = .F) →
        BankWordRenewalFrontierWaveLineageQuiet ring root
          (bankWordEpochNext ring root z root) := by
      intro hc hp
      apply hidleNext
      rw [bankWordEpochRootOutgoingRecord, pairW_ser_left]
      exact (serRootOutgoingRecovery _ _ hpx hpy hc hp).2.1
    by_cases hreq : (z.2.1 root).ser.cert = .REQUESTED
    · exact bankWordRenewalWaveRootOutgoingKnownRowsStep ring root s hn hbank hs
        z hz hwave (Or.inl hreq)
    · have hcases : (z.2.1 root).ser.cert = .IDLE ∨
          (z.2.1 root).ser.cert = .RUNNING := by
        cases hc : (z.2.1 root).ser.cert with
        | IDLE => exact Or.inl rfl
        | REQUESTED => exact absurd hc hreq
        | RUNNING => exact Or.inr rfl
      by_cases hb : (z.2.1 root).ser.phase = .B
      · by_cases hG : (z.2.1 root).ser.out = .DONE ∧
            (z.2.1 (ring.rightNeighbor root)).ser.phase = .F
        · exact bankWordRenewalWaveRootOutgoingKnownRowsStep ring root s hn hbank hs
            z hz hwave (Or.inr (Or.inl ⟨hreq, hb, hG.1, hG.2⟩))
        · rcases hcases with hc | hc
          · apply hidleNext
            rw [bankWordEpochRootOutgoingRecord, pairW_ser_left]
            exact (bankWordRootOutgoingIdleRows _ _ hpx hpy hc).2.1
          · by_cases hV : (z.2.1 root).ser.wphase = .VALIDATING
            · by_cases hDB : (z.2.1 root).ser.out = .DONE ∧
                  (z.2.1 (ring.rightNeighbor root)).ser.phase = .B
              · exact bankWordRenewalWaveRootOutgoingKnownRowsStep ring root s
                  hn hbank hs z hz hwave
                  (Or.inr (Or.inr ⟨hc, hb, hDB.1, hDB.2⟩))
              · exact hroot z hz hwave hc hV hb hG hDB
            · obtain ⟨_, hcert, _, hwph, _, _⟩ :=
                bankWordRootOutgoingRunningFrameRows _ _ hpx hpy hc hb hG
              apply bankWordRenewalLineageQuietOfNonvalidating
              · rw [bankWordEpochRootOutgoingRecord, pairW_ser_left, hcert]
                exact fun h => by cases h
              · rw [bankWordEpochRootOutgoingRecord, pairW_ser_left, hwph]
                exact fun h => hV h.2
      · have hp : (z.2.1 root).ser.phase = .C ∨ (z.2.1 root).ser.phase = .F := by
          cases hp : (z.2.1 root).ser.phase with
          | C => exact Or.inl rfl
          | B => exact absurd hp hb
          | F => exact Or.inr rfl
        exact hrecovery hcases hp
  · exact bankWordRenewalWaveRootIncomingStep ring root e s hn hbank hs z hz hj hwave
  · by_cases hV : (z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.wphase = .VALIDATING
    · by_cases hunv : ∀ g : L3.EWord.ValidationGhost,
          L3.EWord.ValidationShape ring root z.2.1 g →
          L3.EWord.validationEdgeClass ring root g e = .unvisitedSuffix
      · exact bankWordRenewalWaveInternalUnvisitedQuietStep ring root e s hn hbank hs
          z hz hne hnj hwave hunv
      · by_cases hDB : (z.2.1 e).ser.phase = .B ∧ (z.2.1 e).ser.out = .DONE ∧
            (z.2.1 (ring.rightNeighbor e)).ser.phase = .B
        · exact bankWordRenewalWaveInternalCoveredDoneQuietStep ring root e s hn hbank hs
            z hz hne hnj hwave hDB.1 hDB.2.1 hDB.2.2
        · exact hint z hz hwave hV.1 hV.2 e hne hnj hunv hDB
    · exact bankWordRenewalWaveInternalInactiveQuietStep ring root e z hne hnj hwave hV

/-- R10a W-stage clock from the two residual J-W moving-row facts.
Consumer: `bankWordProjectedOneEpochCostOfWorkerClock`. -/
theorem bankWordEpochPostSOneWorkerClockOfMovingRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hroot : BankWordRenewalLineageRootMovingStep ring root s)
    (hint : BankWordRenewalLineageInternalMovingStep ring root s) :
    BankWordEpochPostSOneWorkerClock ring root s :=
  bankWordEpochPostSOneWorkerClockOfLineageStep ring hn hbank root s hs
    (bankWordRenewalLineageQuietStepOfMovingRows ring hn hbank root s hs hroot hint)

/-- The renewal attempt cost from the two residual J-W facts.
Consumer: `bankWordRenewalFreshFiveCostOfBounds`. -/
theorem bankWordRenewalFreshAttemptCostOfMovingRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hroot : BankWordRenewalLineageRootMovingStep ring root s)
    (hint : BankWordRenewalLineageInternalMovingStep ring root s) :
    BankWordRenewalFreshAttemptCost ring root s :=
  bankWordRenewalFreshAttemptCostOfLineageStep ring hn hbank root s hs
    (bankWordRenewalLineageQuietStepOfMovingRows ring hn hbank root s hs hroot hint)

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

/-- The root residue of the J-W step holds on the represented BANK root class:
a root-outgoing edge at a RUNNING/VALIDATING root preserves the quiet lineage
(`bankWordRenewalWaveRootOutgoingActiveQuietStep`, which needs neither the
phase-B nor the two non-DONE guards of the residue).
Consumer: `bankWordEpochPostSOneWorkerClockOfMovingRows` (its `hroot`). -/
theorem bankWordRenewalLineageRootMovingStepHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s) :
    BankWordRenewalLineageRootMovingStep ring root s := by
  intro z hz hwave hrun hval _ _ _
  exact bankWordRenewalWaveRootOutgoingActiveQuietStep
    ring root s hn hbank hs z hz hwave ⟨hrun, hval⟩

/-- The W-stage clock with the root residue discharged: only the internal
moving rows remain. Consumer: BOARD R10a (`hworker` of the BankRepairWord
consumers). -/
theorem bankWordEpochPostSOneWorkerClockOfInternalRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hint : BankWordRenewalLineageInternalMovingStep ring root s) :
    BankWordEpochPostSOneWorkerClock ring root s :=
  bankWordEpochPostSOneWorkerClockOfMovingRows ring hn hbank root s hs
    (bankWordRenewalLineageRootMovingStepHolds ring hn hbank root s hs) hint

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

theorem bankWordRenewalWaveForwardExcludesReturnStage
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (gf gr : L3.EWord.ValidationGhost)
    (hf : L3.EWord.ForwardShape ring root s gf)
    (hr : L3.EWord.ReturnShape ring root s gr) : False := by
  by_cases hle : gr.pivot ≤ gf.pivot
  · by_cases heq : gr.pivot = gf.pivot
    · have hB := hf.parentB
      have hF := hr.leftmostF
      rw [heq] at hF
      rw [hF] at hB
      cases hB
    · have hlt : gr.pivot < gf.pivot := by omega
      have hB :=
        (hf.completed
          (⟨gr.pivot, hr.pivotBound⟩ : Fin n) hlt).1
      rw [hr.leftmostF] at hB
      cases hB
  · have hgt : gf.pivot < gr.pivot := by omega
    have hbound : gf.pivot < n := by
      have hp := hf.pivotBound
      omega
    have hD :=
      (hr.completed (⟨gf.pivot, hbound⟩ : Fin n) hgt).2.1
    rcases hf.currentObligation with hnew | hwait
    · have hN := hnew.2.1
      rw [hD] at hN
      cases hN
    · have hW := hwait.1
      rw [hD] at hW
      cases hW

/-- RETURN geometry only reads serializer records at the named
cyclic sites. This transports any candidate RETURN witness
backward across a physical serializer frame.
Consumer: quietness preservation at covered S2R and incoming S5. -/

theorem bankWordRenewalWaveInternalReturnRootLineageStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hr : L3.EWord.ReturnShape ring root z.2.1 g)
    (hp : 1 < g.pivot)
    (he : e = L3.EWord.site ring root (g.pivot - 1)) :
    BankWordRenewalFrontierTicketLineage ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hreturnRootCovered : 0 < g.scrub := by
    rw [hr.covered]
    have hbound := hr.pivotBound
    omega
  have hreturnSourceCovered : g.pivot - 1 < g.scrub := by
    rw [hr.covered]
    have hbound := hr.pivotBound
    omega
  have hreturnPivotCovered : g.pivot < g.scrub := by
    rw [hr.covered]
    exact hr.pivotBound
  have hrootDone := hr.completed
    (⟨0, (show 0 < n by omega)⟩ : Fin n)
    hr.pivotPositive
  have hbRoot : (z.2.1 root).ser.phase = .B := by
    simpa only [L3.EWord.siteZero] using hrootDone.1
  have hdRoot : (z.2.1 root).ser.out = .DONE := by
    simpa only [L3.EWord.siteZero] using hrootDone.2.1
  have hvalidRoot :
      (z.2.1 root).ser.wphase = .VALIDATING := hactive.2
  have hpIndex : g.pivot - 1 < n := by
    exact Nat.lt_of_le_of_lt (Nat.sub_le g.pivot 1)
      hr.pivotBound
  have hpPred : g.pivot - 1 < g.pivot := by omega
  have hsourceOld := hr.completed
    (⟨g.pivot - 1, hpIndex⟩ : Fin n)
    (by simpa only [Fin.val_mk] using hpPred)
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [he]
    exact hsourceOld.1
  have hd : (z.2.1 e).ser.out = .DONE := by
    rw [he]
    exact hsourceOld.2.1
  have hvalid : (z.2.1 e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hsourceOld.2.2
  have hresponder :
      ring.rightNeighbor e =
        L3.EWord.site ring root g.pivot := by
    have ht := L3.EWord.validationParentNeighbor
      ring root (g.pivot - 1) e he
    have hidx : g.pivot - 1 + 1 = g.pivot := by omega
    rw [hidx] at ht
    exact ht
  have hf : (z.2.1 (ring.rightNeighbor e)).ser.phase =
      .F := by
    rw [hresponder]
    exact hr.leftmostF
  have hsourceOldTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot - 1, hpIndex⟩ : Fin n)
        .done := by
    have ht := (hsites
      (⟨g.pivot - 1, hpIndex⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hreturnSourceCovered)).1
      ⟨by simpa only [Fin.val_mk] using hsourceOld.1,
       by simpa only [Fin.val_mk] using hsourceOld.2.2⟩
    have hdSite :
        (z.2.1
          (L3.EWord.site ring root (g.pivot - 1))).ser.out =
            .DONE := hsourceOld.2.1
    simpa [Fin.val_mk, hdSite] using ht
  have htargetOldTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot, hr.pivotBound⟩ : Fin n)
        .returned := by
    exact (hsites
      (⟨g.pivot, hr.pivotBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hreturnPivotCovered)).2.2.2.2
      ⟨by simpa only [Fin.val_mk] using hr.leftmostF,
       hr.isReturn,
       by simp only [Fin.val_mk]; exact Nat.le_refl g.pivot⟩
  obtain ⟨parent, htParent, hreqParent, hstampParent⟩ :=
    hsourceOldTicket
  obtain ⟨child, htChild, hreqChild, hstampChild⟩ :=
    htargetOldTicket
  have htParentAtE :
      wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation e) =
          some parent := by
    rw [he]
    simpa only [Fin.val_mk] using htParent
  have htChildAtResp :
      wTicketAt .returned
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) = some child := by
    rw [hresponder]
    simpa only [Fin.val_mk] using htChild
  have heNotRoot : e ≠ root := by
    rw [he]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (g.pivot - 1) hpIndex (by omega)
  have hrespNotRoot : ring.rightNeighbor e ≠ root := by
    rw [hresponder]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root g.pivot hr.pivotBound hr.pivotPositive
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed heNotRoot hrespNotRoot
  have hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N" :=
    (L3.EWord.validationReturnMoveSerializer
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hpost.1 hpost.2 hb hd hf).1
  have hjoined := bankWordRenewalWaveReturnMoveTicketStep
    ring root e z (by omega : 2 ≤ n) parent child
    hrow hd hf htParentAtE htChildAtResp
    (hreqParent.trans hreqChild.symm)
    (hstampParent.trans hstampChild.symm)
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    exact phiW_ser_remote ring z.2.1 e root
      heNotRoot.symm hrespNotRoot.symm
  have hrootLedger :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation root =
      (bankWordHardEpochLedger ring root z).validation root :=
    bankWordRenewalFrontierWaveTicketRemoteFrame
      ring root z e root heNotRoot.symm hrespNotRoot.symm
  have hrootOldTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨0, (show 0 < n by omega)⟩ : Fin n)
        .done := by
    have ht := (hsites
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hreturnRootCovered)).1
      ⟨by simpa only [Fin.val_mk, L3.EWord.siteZero] using hbRoot,
       by simpa only [Fin.val_mk, L3.EWord.siteZero] using
           hvalidRoot⟩
    simpa [Fin.val_mk, L3.EWord.siteZero, hdRoot] using ht
  obtain ⟨rootTicket, htRoot, hreqRoot, hstampRoot⟩ :=
    hrootOldTicket
  have htRootNew :
      wTicketAt .done
        ((bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root z e)).validation root) =
        some rootTicket := by
    rw [hrootLedger]
    simpa only [Fin.val_mk, L3.EWord.siteZero] using htRoot
  have hnewFirstB : 2 < g.pivot →
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser.phase = .B := by
    intro hlt
    have hfirstOld :
        (z.2.1 (ring.rightNeighbor root)).ser.phase = .B := by
      simpa only [L3.EWord.siteOne] using
        (hr.completed
          (⟨1, (show 1 < n by omega)⟩ : Fin n)
          (by simpa only [Fin.val_mk] using
            (show 1 < g.pivot by omega))).1
    have hpBound : g.pivot - 1 + 1 < n := by
      have ht := hr.pivotBound
      omega
    have hnotLeft : 1 ≠ g.pivot - 1 := by omega
    have hnotRight : 1 ≠ (g.pivot - 1) + 1 := by omega
    have hfr := L3.EWord.validationParentFrame
      ring root z.2.1 (g.pivot - 1) e
      hpBound he 1 (by omega : 1 < n)
      hnotLeft hnotRight
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor root)).ser.phase = .B
    rw [← L3.EWord.siteOne, hfr]
    exact hfirstOld
  unfold BankWordRenewalFrontierTicketLineage
  refine ⟨?_, ?_, ?_⟩
  · intro hnew
    have hold : (z.2.1 root).ser.cert = .REQUESTED := by
      simpa only [hrootSer] using hnew
    rw [hactive.1] at hold
    cases hold
  · intro hnew
    have hwrong :
        ((bankWordEpochNext ring root z e).2.1 root).ser.out =
          .WAIT := hnew.2.2.2.1
    rw [hrootSer, hdRoot] at hwrong
    cases hwrong
  · intro hnew
    by_cases htwo : g.pivot = 2
    · have hfirst : e = ring.rightNeighbor root := by
        simpa [htwo, L3.EWord.siteOne] using he
      have htFirstNew :
          wTicketAt .returned
            ((bankWordHardEpochLedger ring root
              (bankWordEpochNext ring root z e)).validation
                (ring.rightNeighbor root)) =
            some { parent with stage := .returned } := by
        rw [← hfirst, hjoined.1]
        rfl
      refine ⟨rootTicket, { parent with stage := .returned },
        htRootNew, htFirstNew, ?_, ?_⟩
      · exact hreqRoot.trans hreqParent.symm
      · exact hstampRoot.trans hstampParent.symm
    · have hlt : 2 < g.pivot := by
        have hpositive := hp
        omega
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor root)).ser.phase = .F :=
        hnew.2.2.2.2
      rw [hnewFirstB hlt] at hwrong
      cases hwrong

theorem bankWordRenewalWaveInternalReturnMoveQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hr : L3.EWord.ReturnShape ring root z.2.1 g)
    (hp : 1 < g.pivot)
    (he : e = L3.EWord.site ring root (g.pivot - 1)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hreturnSourceCovered : g.pivot - 1 < g.scrub := by
    rw [hr.covered]
    have hbound := hr.pivotBound
    omega
  have hreturnPivotCovered : g.pivot < g.scrub := by
    rw [hr.covered]
    exact hr.pivotBound
  have hbase := bankWordRenewalWaveInternalReturnRootLineageStep
    ring root e s hn hbank hs z hz hwave hactive
    g hg hr hp he
  have hbound : g.pivot - 1 < n := by
    exact Nat.lt_of_le_of_lt (Nat.sub_le g.pivot 1)
      hr.pivotBound
  have hpred : g.pivot - 1 < g.pivot := by omega
  have hsourceOld := hr.completed
    (⟨g.pivot - 1, hbound⟩ : Fin n)
    (by simpa only [Fin.val_mk] using hpred)
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [he]
    exact hsourceOld.1
  have hd : (z.2.1 e).ser.out = .DONE := by
    rw [he]
    exact hsourceOld.2.1
  have hresponder :
      ring.rightNeighbor e = L3.EWord.site ring root g.pivot := by
    have ht := L3.EWord.validationParentNeighbor
      ring root (g.pivot - 1) e he
    have hidx : g.pivot - 1 + 1 = g.pivot := by omega
    rw [hidx] at ht
    exact ht
  have hf : (z.2.1 (ring.rightNeighbor e)).ser.phase = .F := by
    rw [hresponder]
    exact hr.leftmostF
  have hsourceOldTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot - 1, hbound⟩ : Fin n)
        .done := by
    have hlt : g.pivot - 1 < g.scrub := hreturnSourceCovered
    have ht := (hsites
      (⟨g.pivot - 1, hbound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hlt)).1
      ⟨by simpa only [Fin.val_mk] using hsourceOld.1,
       by simpa only [Fin.val_mk] using hsourceOld.2.2⟩
    simpa [Fin.val_mk, hsourceOld.2.1] using ht
  have htargetOldTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot, hr.pivotBound⟩ : Fin n)
        .returned := by
    have hlt : g.pivot < g.scrub := hreturnPivotCovered
    exact (hsites
      (⟨g.pivot, hr.pivotBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hlt)).2.2.2.2
      ⟨by simpa only [Fin.val_mk] using hr.leftmostF,
       hr.isReturn,
       by simp only [Fin.val_mk]; exact Nat.le_refl g.pivot⟩
  obtain ⟨parent, htParent, hreqParent, hstampParent⟩ :=
    hsourceOldTicket
  obtain ⟨child, htChild, hreqChild, hstampChild⟩ :=
    htargetOldTicket
  have htParentAtE :
      wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation e) =
          some parent := by
    rw [he]
    simpa only [Fin.val_mk] using htParent
  have htChildAtResp :
      wTicketAt .returned
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) = some child := by
    rw [hresponder]
    simpa only [Fin.val_mk] using htChild
  have heNotRoot : e ≠ root := by
    rw [he]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (g.pivot - 1) hbound (by omega)
  have hrespNotRoot : ring.rightNeighbor e ≠ root := by
    rw [hresponder]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root g.pivot hr.pivotBound hr.pivotPositive
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed heNotRoot hrespNotRoot
  have hrow := L3.EWord.validationReturnMoveSerializer
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.1 hpost.2 hb hd hf
  have hrowAt :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N" := hrow.1
  have hjoined := bankWordRenewalWaveReturnMoveTicketStep
    ring root e z (by omega : 2 ≤ n) parent child
    hrowAt hd hf htParentAtE htChildAtResp
    (hreqParent.trans hreqChild.symm)
    (hstampParent.trans hstampChild.symm)
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hsourceF :
      ((bankWordEpochNext ring root z e).2.1 e).ser.phase =
        .F := by
    change ((phiW ring z.2.1 e) e).ser.phase = .F
    rw [phiW_ser_source]
    exact hrow.2.1
  have htargetF :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser.phase = .F := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor e)).ser.phase = .F
    rw [phiW_ser_target ring z.2.1 e hne, hrow.2.2.2]
    exact hf
  have hsourceTicketNew :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot - 1, hbound⟩ : Fin n) .returned := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .returned }, ?_, ?_, ?_⟩
    · simp only [Fin.val_mk, ← he, hjoined.1, wTicketAt]
      rfl
    · exact hreqParent
    · exact hstampParent
  have htargetTicketNew :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot, hr.pivotBound⟩ : Fin n) .returned := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨child, ?_, hreqChild, hstampChild⟩
    · simpa only [Fin.val_mk, ← hresponder, hjoined.2]
        using htChildAtResp
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
        false := L3.EWord.nonrootNoAccept
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardS1 =
        false := L3.EWord.nonrootHardStartFalse
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hghost := L3.EWord.validationReturnMoveGhost
    ring root z.2.1 g e hstart hr.isReturn hp he
    hb hd hf hrow.1
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1
          { g with pivot := g.pivot - 1 } := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hactiveNew
    refine ⟨{ g with pivot := g.pivot - 1 }, req, stamp,
      hshapeNew, ?_⟩
    intro k hk
    by_cases hsrcIndex : k.val = g.pivot - 1
    · have hsite :
          L3.EWord.site ring root k.val = e := by
        rw [hsrcIndex, ← he]
      have hindex : k =
          (⟨g.pivot - 1, hbound⟩ : Fin n) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hsrcIndex
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceF] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceF] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceF] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceF] at hwrong
        cases hwrong
      · intro h
        rw [hindex]
        exact hsourceTicketNew
    · by_cases hdstIndex : k.val = g.pivot
      · have hsite :
            L3.EWord.site ring root k.val =
              ring.rightNeighbor e := by
          rw [hdstIndex, ← hresponder]
        have hindex : k =
            (⟨g.pivot, hr.pivotBound⟩ : Fin n) := by
          apply Fin.ext
          simpa only [Fin.val_mk] using hdstIndex
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have hwrong := h.1
          rw [hsite, htargetF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, htargetF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, htargetF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, htargetF] at hwrong
          cases hwrong
        · intro h
          rw [hindex]
          exact htargetTicketNew
      · have hsrcNe :
            L3.EWord.site ring root k.val ≠ e := by
          intro h
          have hsame :
              L3.EWord.site ring root k.val =
                L3.EWord.site ring root (g.pivot - 1) := by
            rw [← he]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val (g.pivot - 1) k.isLt hbound hsame
          exact hsrcIndex heq
        have hdstNe :
            L3.EWord.site ring root k.val ≠
              ring.rightNeighbor e := by
          intro h
          have hsame :
              L3.EWord.site ring root k.val =
                L3.EWord.site ring root g.pivot := by
            rw [← hresponder]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val g.pivot k.isLt hr.pivotBound hsame
          exact hdstIndex heq
        have hserFrame :
            ((bankWordEpochNext ring root z e).2.1
              (L3.EWord.site ring root k.val)).ser =
              (z.2.1 (L3.EWord.site ring root k.val)).ser := by
          change ((phiW ring z.2.1 e)
            (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser
          exact phiW_ser_remote ring z.2.1 e
            (L3.EWord.site ring root k.val) hsrcNe hdstNe
        have hticketFrame := bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z e (L3.EWord.site ring root k.val)
          hsrcNe hdstNe
        have hkOld : k.val < g.scrub := by
          rw [hr.covered]
          exact k.isLt
        obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hkOld
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have ht := hB (by simpa only [hserFrame] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hserFrame, hticketFrame] using ht
        · intro h
          have ht := hP (by simpa only [hserFrame] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hserFrame, hticketFrame] using ht
        · intro h
          have ht := hI (by simpa only [hserFrame] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hserFrame, hticketFrame] using ht
        · intro h
          have ht := hL (by simpa only [hserFrame] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hserFrame, hticketFrame] using ht
        · intro h
          have hphase :
              (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
                .F := by
            simpa only [hserFrame] using h.1
          have hge : g.pivot ≤ k.val := by
            by_cases hsmall : k.val < g.pivot
            · have holdB := (hr.completed k hsmall).1
              rw [hphase] at holdB
              cases holdB
            · omega
          have ht := hF ⟨hphase, hr.isReturn, hge⟩
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hserFrame, hticketFrame] using ht
  exact bankWordRenewalWaveReturnMoveQuietUpgrade
    ring root e z (by omega : 2 ≤ n) g hwave hactive
    hshape hr hp he hfixed hpost.1 hpost.2 hb hd hf
    hnewWave

theorem bankWordRenewalWaveInternalFrontierInternalQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (hp : 0 < g.pivot)
    (he : e = L3.EWord.site ring root g.pivot)
    (hw : (z.2.1 e).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor e)).ser.phase = .C)
    (hi : (z.2.1 (ring.rightNeighbor e)).ser.probe =
      .INTERNAL_OK) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hwaitAt :
      (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
        .WAIT := by rw [← he]; exact hw
  have hwaitOb := L3.EWord.validationFrontierWaitObligation
    ring root z.2.1 g hf hwaitAt
  have hscrub : g.scrub = g.pivot + 2 := hwaitOb.1
  have hchildInternal := L3.EWord.validationFrontierWaitInternalWitness
    ring root z.2.1 g hf hwaitAt
    (by
      have hj := L3.EWord.validationParentNeighbor
        ring root g.pivot e he
      rw [← hj]
      exact hi)
  have hbound : g.pivot + 2 < n := hchildInternal.2
  have hpBound : g.pivot < n := by omega
  have hchildSite : ring.rightNeighbor e =
      L3.EWord.site ring root (g.pivot + 1) :=
    L3.EWord.validationParentNeighbor ring root g.pivot e he
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [he]
    exact hf.parentB
  have hv : (z.2.1 e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hf.parentValidating
  have hchildValid :
      (z.2.1 (ring.rightNeighbor e)).ser.wphase =
        .VALIDATING := by
    have hpc := hwaitOb.2
    unfold L3.EWord.pendingChild at hpc
    rcases hpc.2 with hpend | hinter | hleaf
    · have hwrong :
          (z.2.1 (ring.rightNeighbor e)).ser.probe =
            .PENDING := by
        rw [hchildSite]
        exact hpend.1
      rw [hi] at hwrong
      cases hwrong
    · rw [hchildSite]
      exact hinter.2.2
    · have hwrong :
          (z.2.1 (ring.rightNeighbor e)).ser.probe =
            .LEAF_OK := by
        rw [hchildSite]
        exact hleaf.2.1
      rw [hi] at hwrong
      cases hwrong
  have holdSource :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot, hpBound⟩ : Fin n) .waiting := by
    have hk : g.pivot < g.scrub := by rw [hscrub]; omega
    have ht := (hsites
      (⟨g.pivot, hpBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hk)).1
      ⟨by simpa only [Fin.val_mk] using hf.parentB,
       by simpa only [Fin.val_mk] using hf.parentValidating⟩
    simpa [Fin.val_mk, hwaitAt] using ht
  have holdChild :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp
        (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
        .observedInternal := by
    have hk : g.pivot + 1 < g.scrub := by rw [hscrub]; omega
    exact (hsites
      (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hk)).2.2.1
      ⟨by simpa only [Fin.val_mk, ← hchildSite] using hc,
       by simpa only [Fin.val_mk, ← hchildSite] using hi,
       by simpa only [Fin.val_mk, ← hchildSite] using hchildValid⟩
  obtain ⟨parent, htParent, hpReq, hpStamp⟩ := holdSource
  obtain ⟨child, htChild, hcReq, hcStamp⟩ := holdChild
  have htSourceAtE :
      wTicketAt .waiting
        ((bankWordHardEpochLedger ring root z).validation e) =
          some parent := by
    rw [he]
    simpa only [Fin.val_mk] using htParent
  have htChildAtResp :
      wTicketAt .observedInternal
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) = some child := by
    rw [hchildSite]
    simpa only [Fin.val_mk] using htChild
  have heNotRoot : e ≠ root := by
    rw [he]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root g.pivot hpBound hp
  have htargetNotRoot : ring.rightNeighbor e ≠ root := by
    rw [hchildSite]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (g.pivot + 1) hf.pivotBound (by omega)
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed heNotRoot htargetNotRoot
  have hpairSer := L3.EWord.validationParentInternalWrite
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.2 (by intro h; rw [hpost.1] at h; cases h)
    hb hw hv hc hi
  have hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N" := by
    change (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "S2N"
    simp [serW, serializerStep, ProjW.lift,
      hpost.1, hpost.2, hb]
  have hjoined := bankWordRenewalWaveInternalAdmissionTicketStep
    ring root e z (by omega : 2 ≤ n) parent child
    hrow hw hc hi htSourceAtE htChildAtResp
    (hpReq.trans hcReq.symm) (hpStamp.trans hcStamp.symm)
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hsrcSer :
      ((bankWordEpochNext ring root z e).2.1 e).ser =
        { (z.2.1 e).ser with out := .DONE } := by
    change ((phiW ring z.2.1 e) e).ser =
      { (z.2.1 e).ser with out := .DONE }
    rw [phiW_ser_source]
    exact hpairSer.1
  have hdstSer :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser =
        { (z.2.1 (ring.rightNeighbor e)).ser with
          phase := .B, out := .NEW, probe := .NONE,
          wphase := .VALIDATING } := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor e)).ser =
        { (z.2.1 (ring.rightNeighbor e)).ser with
          phase := .B, out := .NEW, probe := .NONE,
          wphase := .VALIDATING }
    rw [phiW_ser_target ring z.2.1 e hne]
    exact hpairSer.2
  have hsrcB :
      ((bankWordEpochNext ring root z e).2.1 e).ser.phase = .B := by
    rw [hsrcSer]
    exact hb
  have hsrcDone :
      ((bankWordEpochNext ring root z e).2.1 e).ser.out = .DONE := by
    rw [hsrcSer]
  have hdstB :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser.phase = .B := by
    rw [hdstSer]
  have hdstNew :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser.out = .NEW := by
    rw [hdstSer]
  have hsrcTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot, hpBound⟩ : Fin n) .done := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .done }, ?_, hpReq, hpStamp⟩
    simp only [Fin.val_mk, ← he, hjoined.1, wTicketAt]
    rfl
  have hdstTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
        .broadcaster := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .broadcaster }, ?_, hpReq, hpStamp⟩
    simp only [Fin.val_mk, ← hchildSite, hjoined.2, wTicketAt]
    rfl
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    exact phiW_ser_remote ring z.2.1 e root
      heNotRoot.symm htargetNotRoot.symm
  have hrootDone : (z.2.1 root).ser.out = .DONE := by
    have hdone := hf.completed
      (⟨0, (show 0 < n by omega)⟩ : Fin n) hp
    simpa only [L3.EWord.siteZero] using hdone.2.1
  have hfirstB :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser.phase = .B := by
    by_cases hone : g.pivot = 1
    · have hfirst : e = ring.rightNeighbor root := by
        simpa [hone, L3.EWord.siteOne] using he
      rw [← hfirst, hsrcB]
    · have hlt : 1 < g.pivot := by omega
      have hfirstOld :
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .B := by
        simpa only [L3.EWord.siteOne] using
          (hf.completed
            (⟨1, (show 1 < n by omega)⟩ : Fin n) hlt).1
      have hfirstFrame := L3.EWord.validationParentFrame
        ring root z.2.1 g.pivot e hf.pivotBound he
        1 (by omega : 1 < n) (by omega) (by omega)
      change ((phiW ring z.2.1 e)
        (ring.rightNeighbor root)).ser.phase = .B
      rw [← L3.EWord.siteOne, hfirstFrame]
      exact hfirstOld
  have hbase :
      BankWordRenewalFrontierTicketLineage ring root
        (bankWordEpochNext ring root z e) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hold : (z.2.1 root).ser.cert = .REQUESTED := by
        simpa only [hrootSer] using h
      rw [hactive.1] at hold
      cases hold
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1 root).ser.out =
            .WAIT := h.2.2.2.1
      rw [hrootSer, hrootDone] at hwrong
      cases hwrong
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor root)).ser.phase = .F :=
          h.2.2.2.2
      rw [hfirstB] at hwrong
      cases hwrong
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
      false := L3.EWord.nonrootNoAccept
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart := L3.EWord.validationParentHardStartFalse
    ring root z.2.1 g e hshape hfixed
  have hghost := L3.EWord.validationGhostParentInternalEq
    ring root z.2.1 g e hstart hf.isForward he
    hb hw hc hi
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1
          { g with pivot := g.pivot + 1 } := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hfNew :
      L3.EWord.ForwardShape ring root
        (bankWordEpochNext ring root z e).2.1
          { g with pivot := g.pivot + 1 } := by
    rcases hshapeNew.stageShape with hF | hR
    · exact hF
    · have hwrong : ({ g with pivot := g.pivot + 1 }).stage =
          .forward := hf.isForward
      rw [hR.isReturn] at hwrong
      cases hwrong
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hactiveNew
    refine ⟨{ g with pivot := g.pivot + 1 }, req, stamp,
      hshapeNew, ?_⟩
    intro k hk
    by_cases hsrcIndex : k.val = g.pivot
    · have hsite : L3.EWord.site ring root k.val = e := by
        rw [hsrcIndex, ← he]
      have hindex : k = (⟨g.pivot, hpBound⟩ : Fin n) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hsrcIndex
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rw [hindex]
        simpa [Fin.val_mk, ← he, hsrcDone] using hsrcTicket
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
    · by_cases hdstIndex : k.val = g.pivot + 1
      · have hsite : L3.EWord.site ring root k.val =
            ring.rightNeighbor e := by
          rw [hdstIndex, ← hchildSite]
        have hindex : k =
            (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n) := by
          apply Fin.ext
          simpa only [Fin.val_mk] using hdstIndex
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          rw [hindex]
          simpa [Fin.val_mk, ← hchildSite, hdstNew] using hdstTicket
        · intro h
          have hwrong := h.1
          rw [hsite, hdstB] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstB] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstB] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstB] at hwrong
          cases hwrong
      · have hsrcNe : L3.EWord.site ring root k.val ≠ e := by
          intro h
          have hsame : L3.EWord.site ring root k.val =
              L3.EWord.site ring root g.pivot := by
            rw [← he]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val g.pivot k.isLt hpBound hsame
          exact hsrcIndex heq
        have hdstNe : L3.EWord.site ring root k.val ≠
            ring.rightNeighbor e := by
          intro h
          have hsame : L3.EWord.site ring root k.val =
              L3.EWord.site ring root (g.pivot + 1) := by
            rw [← hchildSite]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val (g.pivot + 1) k.isLt
            hf.pivotBound hsame
          exact hdstIndex heq
        have hser :
            ((bankWordEpochNext ring root z e).2.1
              (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser := by
          change ((phiW ring z.2.1 e)
            (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser
          exact phiW_ser_remote ring z.2.1 e
            (L3.EWord.site ring root k.val) hsrcNe hdstNe
        have ht := bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z e (L3.EWord.site ring root k.val)
          hsrcNe hdstNe
        obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hk
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have htOld := hB (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hser, ht] using htOld
        · intro h
          have htOld := hP (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hser, ht] using htOld
        · intro h
          have htOld := hI (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hser, ht] using htOld
        · intro h
          have htOld := hL (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hser, ht] using htOld
        · intro h
          have hbelow : k.val < g.pivot := by
            have hkScrub : k.val < g.scrub := hk
            have hkPivot : k.val < g.pivot + 2 := by
              rw [hscrub] at hkScrub
              exact hkScrub
            omega
          have hdone := (hf.completed k hbelow).1
          have hphase :
              (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
                .F := by
            simpa only [hser] using h.1
          rw [hphase] at hdone
          cases hdone
  refine ⟨hnewWave, ?_⟩
  intro hactiveNew gnew hreturn k hk hc
  exact False.elim (bankWordRenewalWaveForwardExcludesReturnStage
    ring root (bankWordEpochNext ring root z e).2.1
    { g with pivot := g.pivot + 1 } gnew hfNew hreturn)

theorem bankWordRenewalWaveInternalFrontierLeafQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (he : e = L3.EWord.site ring root g.pivot)
    (hw : (z.2.1 e).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor e)).ser.phase = .C)
    (hl : (z.2.1 (ring.rightNeighbor e)).ser.probe =
      .LEAF_OK) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hparentWait :
      (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
        .WAIT := by rw [← he]; exact hw
  have hchildSite : ring.rightNeighbor e =
      L3.EWord.site ring root (g.pivot + 1) :=
    L3.EWord.validationParentNeighbor ring root g.pivot e he
  have hchildProbe :
      (z.2.1 (L3.EWord.site ring root (g.pivot + 1))).ser.probe =
        .LEAF_OK := by
    rw [← hchildSite]
    exact hl
  have hleafWitness := L3.EWord.validationFrontierWaitLeafWitness
    ring root z.2.1 g hf hparentWait hchildProbe
  have hscrub : g.scrub = g.pivot + 2 := hleafWitness.1
  have hlast : g.pivot + 2 = n := hleafWitness.2.1
  have hchildOff :
      (z.2.1 (ring.rightNeighbor e)).ser.wphase = .OFF := by
    rw [hchildSite]
    exact hleafWitness.2.2
  have hpBound : g.pivot < n := by
    have ht := hf.pivotBound
    omega
  have hpPositive : 0 < g.pivot := by omega
  have hpBeyondFirst : 1 < g.pivot := by
    have ht := hn
    omega
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [he]
    exact hf.parentB
  have hv : (z.2.1 e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hf.parentValidating
  have holdSource :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot, hpBound⟩ : Fin n) .waiting := by
    have hk : g.pivot < g.scrub := by rw [hscrub]; omega
    have ht := (hsites
      (⟨g.pivot, hpBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hk)).1
      ⟨by simpa only [Fin.val_mk] using hf.parentB,
       by simpa only [Fin.val_mk] using hf.parentValidating⟩
    simpa [Fin.val_mk, hparentWait] using ht
  have holdChild :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
        .observedLeaf := by
    have hk : g.pivot + 1 < g.scrub := by rw [hscrub]; omega
    exact (hsites
      (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hk)).2.2.2.1
      ⟨by simpa only [Fin.val_mk, ← hchildSite] using hc,
       by simpa only [Fin.val_mk, ← hchildSite] using hl⟩
  obtain ⟨parent, htParent, hpReq, hpStamp⟩ := holdSource
  obtain ⟨child, htChild, hcReq, hcStamp⟩ := holdChild
  have htParentAtE :
      wTicketAt .waiting
        ((bankWordHardEpochLedger ring root z).validation e) =
          some parent := by
    rw [he]
    simpa only [Fin.val_mk] using htParent
  have htChildAtResp :
      wTicketAt .observedLeaf
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) = some child := by
    rw [hchildSite]
    simpa only [Fin.val_mk] using htChild
  have heNotRoot : e ≠ root := by
    rw [he]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root g.pivot hpBound hpPositive
  have htargetNotRoot : ring.rightNeighbor e ≠ root := by
    rw [hchildSite]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (g.pivot + 1) hf.pivotBound (by omega)
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed heNotRoot htargetNotRoot
  have hpairSer := L3.EWord.validationParentLeafWrite
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.2 (by intro h; rw [hpost.1] at h; cases h)
    hb hw hc hl
  have hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N" := by
    change (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "S2N"
    simp [serW, serializerStep, ProjW.lift,
      hpost.1, hpost.2, hb]
  have hjoined := bankWordRenewalWaveInternalLeafTicketStep
    ring root e z (by omega : 2 ≤ n) parent child
    hrow hw hc hl htParentAtE htChildAtResp
    (hpReq.trans hcReq.symm) (hpStamp.trans hcStamp.symm)
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hsrcSer :
      ((bankWordEpochNext ring root z e).2.1 e).ser =
        { (z.2.1 e).ser with out := .DONE } := by
    change ((phiW ring z.2.1 e) e).ser =
      { (z.2.1 e).ser with out := .DONE }
    rw [phiW_ser_source]
    exact hpairSer.1
  have hdstSer :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser =
        { (z.2.1 (ring.rightNeighbor e)).ser with
          phase := .F, probe := .NONE } := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor e)).ser =
        { (z.2.1 (ring.rightNeighbor e)).ser with
          phase := .F, probe := .NONE }
    rw [phiW_ser_target ring z.2.1 e hne]
    exact hpairSer.2
  have hsrcB :
      ((bankWordEpochNext ring root z e).2.1 e).ser.phase = .B := by
    rw [hsrcSer]
    exact hb
  have hsrcDone :
      ((bankWordEpochNext ring root z e).2.1 e).ser.out = .DONE := by
    rw [hsrcSer]
  have hdstF :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser.phase = .F := by
    rw [hdstSer]
  have hsrcTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot, hpBound⟩ : Fin n) .done := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .done }, ?_, hpReq, hpStamp⟩
    simp only [Fin.val_mk, ← he, hjoined.1, wTicketAt]
    rfl
  have hdstTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
        .returned := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .returned }, ?_, hpReq, hpStamp⟩
    simp only [Fin.val_mk, ← hchildSite, hjoined.2, wTicketAt]
    rfl
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    exact phiW_ser_remote ring z.2.1 e root
      heNotRoot.symm htargetNotRoot.symm
  have hrootDone : (z.2.1 root).ser.out = .DONE := by
    have hdone := hf.completed
      (⟨0, (show 0 < n by omega)⟩ : Fin n) hpPositive
    simpa only [L3.EWord.siteZero] using hdone.2.1
  have hfirstOldB :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .B := by
    simpa only [L3.EWord.siteOne] using
      (hf.completed
        (⟨1, (show 1 < n by omega)⟩ : Fin n) hpBeyondFirst).1
  have hfirstFrame := L3.EWord.validationParentFrame
    ring root z.2.1 g.pivot e hf.pivotBound he
    1 (by omega : 1 < n) (by omega) (by omega)
  have hfirstB :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser.phase = .B := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor root)).ser.phase = .B
    rw [← L3.EWord.siteOne, hfirstFrame]
    exact hfirstOldB
  have hbase :
      BankWordRenewalFrontierTicketLineage ring root
        (bankWordEpochNext ring root z e) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hold : (z.2.1 root).ser.cert = .REQUESTED := by
        simpa only [hrootSer] using h
      rw [hactive.1] at hold
      cases hold
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1 root).ser.out =
            .WAIT := h.2.2.2.1
      rw [hrootSer, hrootDone] at hwrong
      cases hwrong
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor root)).ser.phase = .F :=
          h.2.2.2.2
      rw [hfirstB] at hwrong
      cases hwrong
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
      false := L3.EWord.nonrootNoAccept
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart := L3.EWord.validationParentHardStartFalse
    ring root z.2.1 g e hshape hfixed
  have hghost := L3.EWord.validationGhostParentLeafEq
    ring root z.2.1 g e hstart hf.isForward he
    hb hw hc hl
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1
          { g with stage := .returning, pivot := g.pivot + 1 } := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hrNew :
      L3.EWord.ReturnShape ring root
        (bankWordEpochNext ring root z e).2.1
          { g with stage := .returning, pivot := g.pivot + 1 } := by
    rcases hshapeNew.stageShape with hF | hR
    · have hwrong : L3.EWord.ValidationStage.returning =
          .forward := by
        simpa only using hF.isForward
      cases hwrong
    · exact hR
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hactiveNew
    refine ⟨{ g with stage := .returning, pivot := g.pivot + 1 },
      req, stamp, hshapeNew, ?_⟩
    intro k hk
    by_cases hsrcIndex : k.val = g.pivot
    · have hsite : L3.EWord.site ring root k.val = e := by
        rw [hsrcIndex, ← he]
      have hindex : k = (⟨g.pivot, hpBound⟩ : Fin n) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hsrcIndex
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rw [hindex]
        simpa [Fin.val_mk, ← he, hsrcDone] using hsrcTicket
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
    · by_cases hdstIndex : k.val = g.pivot + 1
      · have hsite : L3.EWord.site ring root k.val =
            ring.rightNeighbor e := by
          rw [hdstIndex, ← hchildSite]
        have hindex : k =
            (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n) := by
          apply Fin.ext
          simpa only [Fin.val_mk] using hdstIndex
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have hwrong := h.1
          rw [hsite, hdstF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstF] at hwrong
          cases hwrong
        · intro h
          rw [hindex]
          exact hdstTicket
      · have hsrcNe : L3.EWord.site ring root k.val ≠ e := by
          intro h
          have hsame : L3.EWord.site ring root k.val =
              L3.EWord.site ring root g.pivot := by
            rw [← he]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val g.pivot k.isLt hpBound hsame
          exact hsrcIndex heq
        have hdstNe : L3.EWord.site ring root k.val ≠
            ring.rightNeighbor e := by
          intro h
          have hsame : L3.EWord.site ring root k.val =
              L3.EWord.site ring root (g.pivot + 1) := by
            rw [← hchildSite]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val (g.pivot + 1) k.isLt
            hf.pivotBound hsame
          exact hdstIndex heq
        have hser :
            ((bankWordEpochNext ring root z e).2.1
              (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser := by
          change ((phiW ring z.2.1 e)
            (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser
          exact phiW_ser_remote ring z.2.1 e
            (L3.EWord.site ring root k.val) hsrcNe hdstNe
        have ht := bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z e (L3.EWord.site ring root k.val)
          hsrcNe hdstNe
        obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hk
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have hold := hB (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket, hser, ht] using hold
        · intro h
          have hold := hP (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket, hser, ht] using hold
        · intro h
          have hold := hI (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket, hser, ht] using hold
        · intro h
          have hold := hL (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket, hser, ht] using hold
        · intro h
          have hbelow : k.val < g.pivot := by
            have hkN : k.val < n := k.isLt
            have hlastN : g.pivot + 2 = n := hlast
            omega
          have hdone := (hf.completed k hbelow).1
          have hphase : (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .F := by
            simpa only [hser] using h.1
          rw [hphase] at hdone
          cases hdone
  refine ⟨hnewWave, ?_⟩
  intro hactiveNew gnew hreturn k hk hc
  have hpivot := bankWordRenewalWaveReturnPivotUnique
    ring root (bankWordEpochNext ring root z e).2.1
    { g with stage := .returning, pivot := g.pivot + 1 }
    gnew hrNew hreturn
  have hlastPivot : gnew.pivot + 1 = n := by
    have hq : gnew.pivot = g.pivot + 1 := hpivot.symm
    omega
  have hlt := k.isLt
  omega


/-- A forward physical serializer wave has a unique current parent
offset. Any smaller proposed parent is DONE in the other wave,
contradicting its own NEW/WAIT obligation.
Consumer: selection of the actual J-W historical witness. -/
theorem bankWordRenewalWaveForwardPivotUnique
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (a b : L3.EWord.ValidationGhost)
    (ha : L3.EWord.ForwardShape ring root s a)
    (hb : L3.EWord.ForwardShape ring root s b) :
    a.pivot = b.pivot := by
  have hnotDoneA :
      (s (L3.EWord.site ring root a.pivot)).ser.out ≠
        .DONE := by
    intro hd
    rcases ha.currentObligation with hnew | hwait
    · rw [hnew.2.1] at hd
      cases hd
    · rw [hwait.1] at hd
      cases hd
  have hnotDoneB :
      (s (L3.EWord.site ring root b.pivot)).ser.out ≠
        .DONE := by
    intro hd
    rcases hb.currentObligation with hnew | hwait
    · rw [hnew.2.1] at hd
      cases hd
    · rw [hwait.1] at hd
      cases hd
  by_cases hab : a.pivot < b.pivot
  · have hbound : a.pivot < n := by
      have hp := ha.pivotBound
      omega
    have hd := (hb.completed
      (⟨a.pivot, hbound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hab)).2.1
    exact False.elim (hnotDoneA hd)
  · by_cases hba : b.pivot < a.pivot
    · have hbound : b.pivot < n := by
        have hp := hb.pivotBound
        omega
      have hd := (ha.completed
        (⟨b.pivot, hbound⟩ : Fin n)
        (by simpa only [Fin.val_mk] using hba)).2.1
      exact False.elim (hnotDoneB hd)
    · omega

/-- The historical validation ghost is determined by the real
physical serializer ring. The proof uses forward pivot uniqueness,
RETURN F-pivot uniqueness, the conflicting stage grammars, and
the literal NEW/WAIT determination of scrub.
Consumer: replacing the weak not-for-all-unvisited guard by a
negative guard on the selected J-W witness. -/
theorem bankWordRenewalWaveValidationGhostUnique
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (a b : L3.EWord.ValidationGhost)
    (ha : L3.EWord.ValidationShape ring root s a)
    (hb : L3.EWord.ValidationShape ring root s b) :
    a = b := by
  have hpivot : a.pivot = b.pivot := by
    rcases ha.stageShape with haf | har
    · rcases hb.stageShape with hbf | hbr
      · exact bankWordRenewalWaveForwardPivotUnique
          ring root s a b haf hbf
      · exact False.elim
          (bankWordRenewalWaveForwardExcludesReturnStage
            ring root s a b haf hbr)
    · rcases hb.stageShape with hbf | hbr
      · exact False.elim
          (bankWordRenewalWaveForwardExcludesReturnStage
            ring root s b a hbf har)
      · exact bankWordRenewalWaveReturnPivotUnique
          ring root s a b har hbr
  have hstage : a.stage = b.stage := by
    rcases ha.stageShape with haf | har
    · rcases hb.stageShape with hbf | hbr
      · exact haf.isForward.trans hbf.isForward.symm
      · exact False.elim
          (bankWordRenewalWaveForwardExcludesReturnStage
            ring root s a b haf hbr)
    · rcases hb.stageShape with hbf | hbr
      · exact False.elim
          (bankWordRenewalWaveForwardExcludesReturnStage
            ring root s b a hbf har)
      · exact har.isReturn.trans hbr.isReturn.symm
  have hscrub : a.scrub = b.scrub := by
    rcases ha.stageShape with haf | har
    · rcases hb.stageShape with hbf | hbr
      · rcases haf.currentObligation with hnewA | hwaitA
        · rcases hbf.currentObligation with hnewB | hwaitB
          · calc
              a.scrub = a.pivot + 1 := hnewA.2.2
              _ = b.pivot + 1 := by rw [hpivot]
              _ = b.scrub := hnewB.2.2.symm
          · have hbad : SerOut.NEW = SerOut.WAIT := by
              have hleft := hnewA.2.1
              have hright := hwaitB.1
              rw [hpivot] at hleft
              exact hleft.symm.trans hright
            cases hbad
        · rcases hbf.currentObligation with hnewB | hwaitB
          · have hbad : SerOut.WAIT = SerOut.NEW := by
              have hleft := hwaitA.1
              have hright := hnewB.2.1
              rw [hpivot] at hleft
              exact hleft.symm.trans hright
            cases hbad
          · calc
              a.scrub = a.pivot + 2 := hwaitA.2.1
              _ = b.pivot + 2 := by rw [hpivot]
              _ = b.scrub := hwaitB.2.1.symm
      · exact False.elim
          (bankWordRenewalWaveForwardExcludesReturnStage
            ring root s a b haf hbr)
    · rcases hb.stageShape with hbf | hbr
      · exact False.elim
          (bankWordRenewalWaveForwardExcludesReturnStage
            ring root s b a hbf har)
      · exact har.covered.trans hbr.covered.symm
  have hfresh : a.fresh = b.fresh :=
    ha.genuine.trans hb.genuine.symm
  cases a with
  | mk fa sa sta pa =>
      cases b with
      | mk fb sb stb pb =>
          cases hfresh
          cases hscrub
          cases hstage
          cases hpivot
          rfl

/-- All physically valid W-validation witnesses are the same
ghost, so failure of the universally unvisited guard applies
to the chosen ghost whose historical five-site stamps are held
in BankWordRenewalFrontierWaveLineageQuiet.
Consumer: the active INTERNAL moving-row residual split. -/
theorem bankWordRenewalWaveChosenNotUnvisited {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (hunv : ¬ (∀ g : L3.EWord.ValidationGhost,
        L3.EWord.ValidationShape ring root z.2.1 g →
        L3.EWord.validationEdgeClass ring root g e =
          .unvisitedSuffix)) :
    L3.EWord.validationEdgeClass ring root
      (Classical.choose (hwave.wave.2 hactive)) e ≠
        .unvisitedSuffix := by
  intro hchosen
  apply hunv
  intro g hshape
  obtain ⟨req, stamp, hselected, hsites⟩ :=
    Classical.choose_spec (hwave.wave.2 hactive)
  have heq := bankWordRenewalWaveValidationGhostUnique
    ring root z.2.1 g
    (Classical.choose (hwave.wave.2 hactive))
    hshape hselected
  rw [heq]
  exact hchosen


/-- Any selected internal edge that is physically remote from
the whole scrubbed prefix preserves the actual five-clause
ticket genealogy. This is stronger than the priority-named
unvisitedSuffix class and is needed by the pre-challenge
challengedChild edge when its inherited C/B/F bytes are outside
the scrub. Consumer: forward challengedChild NEW case. -/
theorem bankWordRenewalWaveSelectedRemoteQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hremote : ∀ i : Fin n, i.val < g.scrub →
      L3.EWord.site ring root i.val ≠ e ∧
      L3.EWord.site ring root i.val ≠ ring.rightNeighbor e) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hrootSafe := hremote
    (⟨0, (show 0 < n by omega)⟩ : Fin n)
    (by simp only [Fin.val_mk]; exact Nat.lt_of_lt_of_le (by omega : 0 < 2) hshape.lower)
  have hfirstSafe := hremote
    (⟨1, (show 1 < n by omega)⟩ : Fin n)
    (by have := hshape.lower; simp only [Fin.val_mk]; omega)
  have hchildSafe :
      ring.rightNeighbor root ≠ e ∧
      ring.rightNeighbor root ≠ ring.rightNeighbor e := by
    simpa only [Fin.val_mk, L3.EWord.siteOne] using
      hfirstSafe
  have hbase := bankWordRenewalFrontierTicketLineageRemoteStep
    ring root e z he hj hchildSafe.1.symm
      hchildSafe.2.symm hwave.wave.1
  have hf : L3.EWord.ForwardShape ring root z.2.1 g := by
    rcases hshape.stageShape with hf | hr
    · exact hf
    · have hoff := L3.EWord.validationOffsetBound ring root e
      have hloc := L3.EWord.validationOffsetRepresentative
        ring root e
      have hs := (hremote
        (⟨PPL.cyclicOffset ring root e, hoff⟩ : Fin n)
        (by simp only [Fin.val_mk]; rw [hr.covered]; exact hoff)).1
      exact False.elim (hs hloc)
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hno := bankWordRootNonrootHardAcceptFalse
    ring hn hbank root s hs z hz e he
  have hghost := L3.EWord.unvisitedSuffixGhostUnchanged
    ring root z.2.1 g e hshape hremote
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hactiveNew
    refine ⟨g, req, stamp, hshapeNew, ?_⟩
    intro k hk
    have hsafe := hremote k hk
    have hsiteSer :
        ((bankWordEpochNext ring root z e).2.1
          (L3.EWord.site ring root k.val)).ser =
        (z.2.1 (L3.EWord.site ring root k.val)).ser := by
      change ((phiW ring z.2.1 e)
        (L3.EWord.site ring root k.val)).ser =
        (z.2.1 (L3.EWord.site ring root k.val)).ser
      exact phiW_ser_remote ring z.2.1 e
        (L3.EWord.site ring root k.val) hsafe.1 hsafe.2
    have hsiteTicket :=
      bankWordRenewalFrontierWaveTicketRemoteFrame
        ring root z e (L3.EWord.site ring root k.val)
        hsafe.1 hsafe.2
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using hsites k hk
  refine ⟨hnewWave, ?_⟩
  intro hactiveNew gnew hrnew k hk hc
  have hfNew : L3.EWord.ForwardShape ring root
      (bankWordEpochNext ring root z e).2.1 g := by
    rcases hshapeNew.stageShape with hforward | hreturn
    · exact hforward
    · have hbad := hreturn.isReturn
      rw [hf.isForward] at hbad
      cases hbad
  exact False.elim (bankWordRenewalWaveForwardExcludesReturnStage
    ring root (bankWordEpochNext ring root z e).2.1
    g gnew hfNew hrnew)

/-- When the FORWARD parent has not yet challenged its child,
the physical child-service pair lies entirely outside the
causal scrubbed prefix. Unlike its priority classification as
challengedChild, it cannot alter any historical W ticket or
RETURN quiet obligation of the active prefix.
Consumer: challengedChild B/NEW subcase of R10a J-W. -/
theorem bankWordRenewalWaveInternalChildPrechallengeQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (he : e = L3.EWord.site ring root (g.pivot + 1))
    (hnew : (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
      .NEW)
    (hj : ring.rightNeighbor e ≠ root) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hsc := (L3.EWord.validationFrontierNewObligation
    ring root z.2.1 g hf hnew).2
  have hnotSeam : e ≠ L3.EWord.site ring root (n - 1) := by
    intro hseam
    exact hj (L3.EWord.validationSeamNeighbor
      ring root e hseam)
  have hbound : g.pivot + 2 < n :=
    L3.EWord.validationChildNoSeamBound
      ring root g.pivot e (by omega : 3 ≤ n)
      hf.pivotBound he hnotSeam
  have htarget : ring.rightNeighbor e =
      L3.EWord.site ring root (g.pivot + 2) :=
    L3.EWord.validationChildNeighbor ring root g.pivot e he
  have heNotRoot : e ≠ root :=
    L3.EWord.validationChildNotRoot
      ring root g.pivot e (by omega : 3 ≤ n)
      hf.pivotBound he
  have hremote : ∀ k : Fin n, k.val < g.scrub →
      L3.EWord.site ring root k.val ≠ e ∧
      L3.EWord.site ring root k.val ≠ ring.rightNeighbor e := by
    intro k hk
    have hklt : k.val < g.pivot + 1 := by
      rw [hsc] at hk
      exact hk
    constructor
    · intro h
      have hsame :
          L3.EWord.site ring root k.val =
            L3.EWord.site ring root (g.pivot + 1) := by
        rw [← he]
        exact h
      have hbad := L3.EWord.validationSiteInjective
        ring root k.val (g.pivot + 1)
        k.isLt hf.pivotBound hsame
      omega
    · intro h
      have hsame :
          L3.EWord.site ring root k.val =
            L3.EWord.site ring root (g.pivot + 2) := by
        rw [← htarget]
        exact h
      have hbad := L3.EWord.validationSiteInjective
        ring root k.val (g.pivot + 2)
        k.isLt hbound hsame
      omega
  exact bankWordRenewalWaveSelectedRemoteQuietStep
    ring root e s hn hbank hs z hz heNotRoot hj
    hwave hactive g hg hremote


/-- The genuine moving FORWARD parent serves exactly one of the
three chronological S2N obligations: NEW starts a child, WAIT
with PENDING frames, WAIT/INTERNAL_OK admits the next B, or
WAIT/LEAF_OK starts RETURN. The actual old validation ticket
stages select the admission witnesses.
Consumer: INTERNAL moving frontierParent in R10a J-W. -/
theorem bankWordRenewalWaveInternalFrontierParentQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (hparent : e = L3.EWord.site ring root g.pivot) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hpositive : 0 < g.pivot := by
    by_cases hz : g.pivot = 0
    · have hroot : e = root := by
        rw [hparent, hz, L3.EWord.siteZero]
      exact False.elim (he hroot)
    · omega
  have hchildSite : ring.rightNeighbor e =
      L3.EWord.site ring root (g.pivot + 1) :=
    L3.EWord.validationParentNeighbor ring root g.pivot e hparent
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [hparent]
    exact hf.parentB
  rcases hf.currentObligation with hnew | hwait
  · have hnewOut : (z.2.1 e).ser.out = .NEW := by
      rw [hparent]
      exact hnew.2.1
    exact bankWordRenewalWaveInternalFrontierNewQuietStep
      ring root e s hn hbank hs z hz hwave hactive
      g hg hf.isForward hparent hnewOut
  · have hw : (z.2.1 e).ser.out = .WAIT := by
      rw [hparent]
      exact hwait.1
    have hc : (z.2.1 (ring.rightNeighbor e)).ser.phase =
        .C := by
      rw [hchildSite]
      exact hwait.2.2.1
    rcases hwait.2.2.2 with hpend | hinter | hleaf
    · have hp : (z.2.1 (ring.rightNeighbor e)).ser.probe =
          .PENDING := by
        rw [hchildSite]
        exact hpend.1
      exact bankWordRenewalWaveInternalPendingQuietStep
        ring root e s hn hbank hs z hz he hj hwave
        hb hw hc hp
    · have hi : (z.2.1 (ring.rightNeighbor e)).ser.probe =
          .INTERNAL_OK := by
        rw [hchildSite]
        exact hinter.2.1
      exact bankWordRenewalWaveInternalFrontierInternalQuietStep
        ring root e s hn hbank hs z hz hwave hactive
        g hg hf hpositive hparent hw hc hi
    · have hl : (z.2.1 (ring.rightNeighbor e)).ser.probe =
          .LEAF_OK := by
        rw [hchildSite]
        exact hleaf.2.1
      exact bankWordRenewalWaveInternalFrontierLeafQuietStep
        ring root e s hn hbank hs z hz hwave hactive
        g hg hf hparent hw hc hl

/-- FORWARD challengedChild updates are either causally
pre-challenge remote (parent NEW), S3 observation of a
PENDING child seeing a C responder, or nonpending C
stationary/canonical cleanup. The responder's literal
B/C/F phase supplies the exhaustive selected-row split.
Consumer: INTERNAL challengedChild case of R10a J-W. -/
theorem bankWordRenewalWaveInternalChallengedChildQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (hchild : e = L3.EWord.site ring root (g.pivot + 1)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hnotSeam :
      e ≠ L3.EWord.site ring root (n - 1) := by
    intro hs
    exact hj (L3.EWord.validationSeamNeighbor
      ring root e hs)
  have hbound : g.pivot + 2 < n :=
    L3.EWord.validationChildNoSeamBound ring root g.pivot e
      (by omega : 3 ≤ n) hf.pivotBound hchild hnotSeam
  have hparentWait :
      (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
        .WAIT →
      (z.2.1 e).ser.phase = .C := by
    intro hwait
    have hpc := (L3.EWord.validationFrontierWaitObligation
      ring root z.2.1 g hf hwait).2
    exact (by rw [hchild]; exact hpc.1)
  rcases hf.currentObligation with hnew | hwait
  · exact bankWordRenewalWaveInternalChildPrechallengeQuietStep
      ring root e s hn hbank hs z hz hwave hactive
      g hg hf hchild hnew.2.1 hj
  · have hsourceC : (z.2.1 e).ser.phase = .C :=
      hparentWait hwait.1
    have hpc := hwait.2.2
    rcases hpc.2 with hpend | hinter | hleaf
    · have hp : (z.2.1 e).ser.probe = .PENDING := by
        rw [hchild]
        exact hpend.1
      cases htarget :
          (z.2.1 (ring.rightNeighbor e)).ser.phase with
      | B =>
          exact bankWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hbank hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inl htarget)
      | C =>
          exact bankWordRenewalWaveInternalObservedChildQuietStep
            ring root e s hn hbank hs z hz hwave hactive
            g hg hf.isForward hchild hbound hwait.1
            hsourceC hp htarget
      | F =>
          exact bankWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hbank hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inr htarget)
    · have hi : (z.2.1 e).ser.probe = .INTERNAL_OK := by
        rw [hchild]
        exact hinter.2.1
      have hnotPending :
          (z.2.1 e).ser.probe ≠ .PENDING := by
        rw [hi]
        decide
      cases htarget :
          (z.2.1 (ring.rightNeighbor e)).ser.phase with
      | B =>
          exact bankWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hbank hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inl htarget)
      | C =>
          exact bankWordRenewalWaveInternalNonBToCQuietStep
            ring root e s hn hbank hs z hz he hj hwave
            (Or.inr ⟨hsourceC, hnotPending⟩) htarget
      | F =>
          exact bankWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hbank hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inr htarget)
    · have hl : (z.2.1 e).ser.probe = .LEAF_OK := by
        rw [hchild]
        exact hleaf.2.1
      have hnotPending :
          (z.2.1 e).ser.probe ≠ .PENDING := by
        rw [hl]
        decide
      cases htarget :
          (z.2.1 (ring.rightNeighbor e)).ser.phase with
      | B =>
          exact bankWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hbank hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inl htarget)
      | C =>
          exact bankWordRenewalWaveInternalNonBToCQuietStep
            ring root e s hn hbank hs z hz he hj hwave
            (Or.inr ⟨hsourceC, hnotPending⟩) htarget
      | F =>
          exact bankWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hbank hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inr htarget)


/-- A FORWARD coveredInside edge lies strictly behind the
moving parent and has the literal B/DONE+B serializer pair.
This is exactly the stationary class excluded by the internal
moving residue's second negative guard.
Consumer: R10a J-W FORWARD coveredInside contradiction. -/
theorem bankWordRenewalWaveForwardCoveredDonePair {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (g : L3.EWord.ValidationGhost)
    (hshape : L3.EWord.ValidationShape ring root z.2.1 g)
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (hinside : L3.EWord.validationEdgeClass ring root g e =
      .coveredInside) :
    (z.2.1 e).ser.phase = .B ∧
    (z.2.1 e).ser.out = .DONE ∧
    (z.2.1 (ring.rightNeighbor e)).ser.phase = .B := by
  have hk := L3.EWord.validationOffsetBound ring root e
  have he : e = L3.EWord.site ring root
      (PPL.cyclicOffset ring root e) :=
    (L3.EWord.validationOffsetRepresentative ring root e).symm
  have hbound : PPL.cyclicOffset ring root e + 1 < n :=
    L3.EWord.validationNonSeamOffset ring root e
      (L3.EWord.validationCoveredClassFacts
        ring root g e hinside).1
  have hlt := L3.EWord.validationForwardInsideOffset
    ring root z.2.1 g e hshape hf hinside
  have hj := L3.EWord.validationParentNeighbor
    ring root (PPL.cyclicOffset ring root e) e he
  have hdone := hf.completed
    (⟨PPL.cyclicOffset ring root e, hk⟩ : Fin n)
    (by simpa only [Fin.val_mk] using hlt)
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    exact hdone.1
  · rw [he]
    exact hdone.2.1
  · rw [hj]
    by_cases hp :
        PPL.cyclicOffset ring root e + 1 = g.pivot
    · rw [hp]
      exact hf.parentB
    · have hchild : PPL.cyclicOffset ring root e + 1 <
          g.pivot := by omega
      exact (hf.completed
        (⟨PPL.cyclicOffset ring root e + 1, hbound⟩ : Fin n)
        (by simpa only [Fin.val_mk] using hchild)).1

/-- Every RETURN coveredInside nonroot edge is either the
excluded B/DONE+B predecessor-prefix pair, the unique
B/DONE→F pivot predecessor, or a C/F suffix S3/S4 row.
The latter uses the historical RETURN nonpending clause to
exclude forged C/PENDING and routes to canonical or frame
proofs. Consumer: RETURN coveredInside of the internal moving
residue, including the pivot-one boundary. -/
theorem bankWordRenewalWaveInternalReturnCoveredQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hr : L3.EWord.ReturnShape ring root z.2.1 g)
    (hinside : L3.EWord.validationEdgeClass ring root g e =
      .coveredInside)
    (hnotdone : ¬ ((z.2.1 e).ser.phase = .B ∧
      (z.2.1 e).ser.out = .DONE ∧
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .B)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hk := L3.EWord.validationOffsetBound ring root e
  have heoff : e = L3.EWord.site ring root
      (PPL.cyclicOffset ring root e) :=
    (L3.EWord.validationOffsetRepresentative ring root e).symm
  have hbound : PPL.cyclicOffset ring root e + 1 < n :=
    L3.EWord.validationNonSeamOffset ring root e
      (L3.EWord.validationCoveredClassFacts
        ring root g e hinside).1
  have hjoff := L3.EWord.validationParentNeighbor ring root
    (PPL.cyclicOffset ring root e) e heoff
  by_cases hearly : PPL.cyclicOffset ring root e + 1 <
      g.pivot
  · have hleft := hr.completed
      (⟨PPL.cyclicOffset ring root e, hk⟩ : Fin n)
      (by simp only [Fin.val_mk]; omega)
    have hright := hr.completed
      (⟨PPL.cyclicOffset ring root e + 1, hbound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hearly)
    apply False.elim
    apply hnotdone
    refine ⟨?_, ?_, ?_⟩
    · rw [heoff]
      exact hleft.1
    · rw [heoff]
      exact hleft.2.1
    · rw [hjoff]
      exact hright.1
  · by_cases hmove :
        PPL.cyclicOffset ring root e + 1 = g.pivot
    · by_cases hone : g.pivot = 1
      · have hkzero : PPL.cyclicOffset ring root e = 0 := by
          omega
        have hroot : e = root := by
          rw [heoff, hkzero, L3.EWord.siteZero]
        exact False.elim (he hroot)
      · have hpositive : 1 < g.pivot := by
          have hp := hr.pivotPositive
          omega
        have hprev : g.pivot - 1 =
            PPL.cyclicOffset ring root e := by omega
        have hsource : e = L3.EWord.site ring root
            (g.pivot - 1) := by
          rw [hprev]
          exact heoff
        exact bankWordRenewalWaveInternalReturnMoveQuietStep
          ring root e s hn hbank hs z hz hwave hactive
          g hg hr hpositive hsource
    · have hge : g.pivot ≤ PPL.cyclicOffset ring root e := by
        omega
      have hsource :
          (z.2.1 e).ser.phase = .F ∨
          ((z.2.1 e).ser.phase = .C ∧
            (z.2.1 e).ser.probe ≠ .PENDING) := by
        by_cases hsame : PPL.cyclicOffset ring root e =
            g.pivot
        · left
          rw [heoff, hsame]
          exact hr.leftmostF
        · have hgreater : g.pivot <
              PPL.cyclicOffset ring root e := by omega
          rcases hr.suffix
            (⟨PPL.cyclicOffset ring root e, hk⟩ : Fin n)
            (by simpa only [Fin.val_mk] using hgreater)
            with hF | hC
          · left
            rw [heoff]
            exact hF.1
          · have hc : (z.2.1 e).ser.phase = .C := by
              rw [heoff]
              exact hC.1
            have hq := hwave.returnSuffixQuiet
              hactive g hr
              (⟨PPL.cyclicOffset ring root e, hk⟩ : Fin n)
              (by simpa only [Fin.val_mk] using hgreater)
              (by simpa only [Fin.val_mk] using hC.1)
            right
            refine ⟨hc, ?_⟩
            rw [heoff]
            simpa only [Fin.val_mk] using hq
      have hgreater : g.pivot <
          PPL.cyclicOffset ring root e + 1 := by omega
      have htarget :
          (z.2.1 (ring.rightNeighbor e)).ser.phase = .F ∨
          (z.2.1 (ring.rightNeighbor e)).ser.phase = .C := by
        rcases hr.suffix
          (⟨PPL.cyclicOffset ring root e + 1, hbound⟩ : Fin n)
          (by simpa only [Fin.val_mk] using hgreater)
          with hF | hC
        · left
          rw [hjoff]
          exact hF.1
        · right
          rw [hjoff]
          exact hC.1
      rcases htarget with htF | htC
      · rcases hsource with hsF | ⟨hsC, hq⟩
        · exact bankWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hbank hs z hz hwave he hj
            (Or.inr hsF) (Or.inr htF)
        · exact bankWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hbank hs z hz hwave he hj
            (Or.inl hsC) (Or.inr htF)
      · exact bankWordRenewalWaveInternalNonBToCQuietStep
          ring root e s hn hbank hs z hz he hj hwave
          hsource htC


/-- The selected historical W ghost classifies every internal
moving service. The root-seam is excluded by the right-endpoint
guard; unvisitedSuffix by the selected historical witness;
covered FORWARD is the forbidden B/DONE+B pair. The remaining
frontierParent, challengedChild, and RETURN coveredInside cases
are discharged by the literal S2N/S3/S4 admission and cleanup
proofs, not by an assumed generic protocol step.
Consumer: BankWordRenewalLineageInternalMovingStep. -/
theorem bankWordRenewalWaveSelectedInternalMovingQuietStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hshape : L3.EWord.ValidationShape ring root z.2.1 g)
    (hnotUnvisited :
      L3.EWord.validationEdgeClass ring root g e ≠
        .unvisitedSuffix)
    (hnotdone : ¬ ((z.2.1 e).ser.phase = .B ∧
      (z.2.1 e).ser.out = .DONE ∧
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .B)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hnotSeam :
      e ≠ L3.EWord.site ring root (n - 1) := by
    intro hseam
    exact hj (L3.EWord.validationSeamNeighbor
      ring root e hseam)
  have hnotRootClass :
      L3.EWord.validationEdgeClass ring root g e ≠
        .rootSeam := by
    intro hseam
    unfold L3.EWord.validationEdgeClass at hseam
    rw [if_neg hnotSeam] at hseam
    by_cases hp : g.stage = .forward ∧
        e = L3.EWord.site ring root g.pivot
    · rw [if_pos hp] at hseam
      cases hseam
    · rw [if_neg hp] at hseam
      by_cases hc : g.stage = .forward ∧
          e = L3.EWord.site ring root (g.pivot + 1)
      · rw [if_pos hc] at hseam
        cases hseam
      · rw [if_neg hc] at hseam
        by_cases hu : ∀ i : Fin n, i.val < g.scrub →
            L3.EWord.site ring root i.val ≠ e ∧
            L3.EWord.site ring root i.val ≠
              ring.rightNeighbor e
        · rw [if_pos hu] at hseam
          cases hseam
        · rw [if_neg hu] at hseam
          cases hseam
  rcases L3.EWord.validationEdgeClassCover ring root g e with
    hseam | hparent | hchild | hunvisited | hinside
  · exact False.elim (hnotRootClass hseam)
  · have hp : g.stage = .forward ∧
        e = L3.EWord.site ring root g.pivot := by
      unfold L3.EWord.validationEdgeClass at hparent
      rw [if_neg hnotSeam] at hparent
      by_cases hf : g.stage = .forward ∧
          e = L3.EWord.site ring root g.pivot
      · exact hf
      · rw [if_neg hf] at hparent
        by_cases hc : g.stage = .forward ∧
            e = L3.EWord.site ring root (g.pivot + 1)
        · rw [if_pos hc] at hparent
          cases hparent
        · rw [if_neg hc] at hparent
          by_cases hu : ∀ i : Fin n, i.val < g.scrub →
              L3.EWord.site ring root i.val ≠ e ∧
              L3.EWord.site ring root i.val ≠
                ring.rightNeighbor e
          · rw [if_pos hu] at hparent
            cases hparent
          · rw [if_neg hu] at hparent
            cases hparent
    have hf : L3.EWord.ForwardShape ring root z.2.1 g := by
      rcases hshape.stageShape with hF | hR
      · exact hF
      · have hbad := hR.isReturn
        rw [hp.1] at hbad
        cases hbad
    exact bankWordRenewalWaveInternalFrontierParentQuietStep
      ring root e s hn hbank hs z hz he hj hwave hactive
      g hg hf hp.2
  · have hp : g.stage = .forward ∧
        e = L3.EWord.site ring root (g.pivot + 1) := by
      unfold L3.EWord.validationEdgeClass at hchild
      rw [if_neg hnotSeam] at hchild
      by_cases hparent : g.stage = .forward ∧
          e = L3.EWord.site ring root g.pivot
      · rw [if_pos hparent] at hchild
        cases hchild
      · rw [if_neg hparent] at hchild
        by_cases hc : g.stage = .forward ∧
            e = L3.EWord.site ring root (g.pivot + 1)
        · exact hc
        · rw [if_neg hc] at hchild
          by_cases hu : ∀ i : Fin n, i.val < g.scrub →
              L3.EWord.site ring root i.val ≠ e ∧
              L3.EWord.site ring root i.val ≠
                ring.rightNeighbor e
          · rw [if_pos hu] at hchild
            cases hchild
          · rw [if_neg hu] at hchild
            cases hchild
    have hf : L3.EWord.ForwardShape ring root z.2.1 g := by
      rcases hshape.stageShape with hF | hR
      · exact hF
      · have hbad := hR.isReturn
        rw [hp.1] at hbad
        cases hbad
    exact bankWordRenewalWaveInternalChallengedChildQuietStep
      ring root e s hn hbank hs z hz he hj hwave hactive
      g hg hf hp.2
  · exact False.elim (hnotUnvisited hunvisited)
  · rcases hshape.stageShape with hf | hr
    · exact False.elim (hnotdone
        (bankWordRenewalWaveForwardCoveredDonePair
          ring root e z g hshape hf hinside))
    · exact bankWordRenewalWaveInternalReturnCoveredQuietStep
        ring root e s hn hbank hs z hz he hj hwave hactive
        g hg hr hinside hnotdone

/-- The INTERNAL moving lineage residue of R10a is proved by
choosing the historical witness of the active validating wave,
transporting the genuinely negative unvisitedSuffix guard to
that witness using physical ghost uniqueness, and exhausting
all five priority edge classes with their actual serializer and
ticket equations. Consumer: the R10a W worker clock. -/
theorem bankWordRenewalLineageInternalMovingStepHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s) :
    BankWordRenewalLineageInternalMovingStep ring root s := by
  intro z hz hwave hrun hval e he hj hunvisited hnotdone
  have hactive :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING :=
    ⟨hrun, hval⟩
  have hselected := Classical.choose_spec
    (hwave.wave.2 hactive)
  obtain ⟨req, stamp, hshape, hsites⟩ := hselected
  have hnotUnvisited :=
    bankWordRenewalWaveChosenNotUnvisited ring root e z
      hwave hactive hunvisited
  exact bankWordRenewalWaveSelectedInternalMovingQuietStep
    ring hn hbank root e s hs z hz hwave hactive he hj
    (Classical.choose (hwave.wave.2 hactive)) rfl hshape
    hnotUnvisited hnotdone

/-- R10a's post-S1 W worker clock has no remaining moving-row
Prop premise once the historical INTERNAL residue is discharged.
Consumer: BOARD R10a and BankRepairWord expected-cost bridge. -/
theorem bankWordEpochPostSOneWorkerClockHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s) :
    BankWordEpochPostSOneWorkerClock ring root s := by
  exact bankWordEpochPostSOneWorkerClockOfInternalRows
    ring hn hbank root s hs
    (bankWordRenewalLineageInternalMovingStepHolds
      ring hn hbank root s hs)

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
set_option autoImplicit false
set_option Elab.async false

/-- The actual BANK renewal kernel has the one-block expected
attempt cost from every fresh genuine-hard-entry seed. Both
moving-row inputs are now installed; no probability failure
estimate is used in this theorem.
Consumer: the five-block fresh completion step of R10 W. -/
theorem bankWordRenewalFreshAttemptCostHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s) :
    BankWordRenewalFreshAttemptCost ring root s := by
  exact bankWordRenewalFreshAttemptCostOfMovingRows
    ring hn hbank root s hs
    (bankWordRenewalLineageRootMovingStepHolds
      ring hn hbank root s hs)
    (bankWordRenewalLineageInternalMovingStepHolds
      ring hn hbank root s hs)

/-- An ACTUAL prepared BANK reference has a single nominated
root which represents its exact projected physical W state.
The native singleton and the candidate return target are
inherited, not manufactured by an abstract epoch start.
Consumer: the prepared-root entrance to the R10 W projected
clock, before the first genuine hard-acceptance service. -/
theorem bankWordPreparedProjectedSerializerRoot {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPreparedAtSomeRoot ring hbank z) :
    ∃ root : Fin n,
      BankWordSerializerRootClass ring hbank root (piW z.val.1) ∧
      ReferencePreparationCandidate.CandidateReturnTarget root
        (bankValidCandidateView ring hbank z) := by
  obtain ⟨root, hsingleton, hcandidate⟩ := hz
  refine ⟨root, ?_, hcandidate⟩
  exact ⟨z, hsingleton, rfl⟩

/-- The next actual physical epoch state after a genuinely
ticket-certified S6 is a fresh seed, with the same scheduler
successor and not a separately generated initial condition.
Consumer: the 5B renewal step after the first genuine worker
launch in the R10 W stage. -/
theorem bankWordRenewalFreshSeedAfterGenuine {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (pre : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hg : bankWordRenewalGenuine ring root pre.1 e) :
    ∃ seed : BankWordRenewalFreshSeed ring root s,
      seed.1 = bankWordRenewalNext ring root s pre e := by
  exact ⟨⟨bankWordRenewalNext ring root s pre e,
      bankWordRenewalFreshAfterGenuine ring root s pre e hg⟩,
    rfl⟩

/-- The installed J-W step closes hcost unconditionally; thus
the fresh kernel's three-quarter retry estimate is the ONLY
remaining premise of the physical 5B first-completion bound.
This conclusion concerns the WCompletionReceipt target, NOT
AcceptedReceipts.AcceptedWord.
Consumer: R10 W worker-completion segment after genuine S6. -/
theorem bankWordRenewalFreshFiveCostHoldsOfFailure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hfail : ∀ seed : BankWordRenewalFreshSeed ring root s,
      ∀ T, 4 * PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s)
        (.active seed.1) T ≤ 3 * n ^ T)
    (seed : BankWordRenewalFreshSeed ring root s)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      seed.1 T ≤ n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2) := by
  have hcost := bankWordRenewalFreshAttemptCostHolds
    ring hn hbank root s hs
  have hfive := bankWordRenewalFreshFiveCostOfBounds
    ring root s hcost hfail seed T
  rw [bankWordRenewalFiveCoefficient] at hfive
  exact hfive

/-- A selected genuine service supplies precisely the seed
required by the unconditional-hcost/conditional-hfail 5B bound.
The physical state is the SAME bankWordRenewalNext successor.
Consumer: composing the first genuine acceptance and fresh
worker completion on the R10 W scheduler. -/
theorem bankWordRenewalFiveCostAtGenuineSuccessor {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hfail : ∀ seed : BankWordRenewalFreshSeed ring root s,
      ∀ T, 4 * PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s)
        (.active seed.1) T ≤ 3 * n ^ T)
    (pre : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hg : bankWordRenewalGenuine ring root pre.1 e)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      (bankWordRenewalNext ring root s pre e) T ≤ n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2) := by
  obtain ⟨seed, hseed⟩ :=
    bankWordRenewalFreshSeedAfterGenuine ring root s pre e hg
  have hcost := bankWordRenewalFreshFiveCostHoldsOfFailure
    ring hn hbank root s hs hfail seed T
  rw [hseed] at hcost
  exact hcost


/-- The fresh same-word renewal inequality actually yields
FOUR blocks before the existing five-block weakening.
Using the now-unconditional J-W attempt cost, its ONLY
external premise is the three-quarter retry bound for the
ACTUAL fresh kernel. Consumer: the 1B + 4B staging budget
required by R10's exact (440*s+275)*n^2 W rate. -/
theorem bankWordRenewalFreshFourCostHoldsOfFailure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hfail : ∀ seed : BankWordRenewalFreshSeed ring root s,
      ∀ T, 4 * PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s)
        (.active seed.1) T ≤ 3 * n ^ T)
    (seed : BankWordRenewalFreshSeed ring root s)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      seed.1 T ≤ n ^ T * (4 * bankWordRenewalBlock n) := by
  have hcost := bankWordRenewalFreshAttemptCostHolds
    ring hn hbank root s hs
  have hc : ∀ a : BankWordRenewalFreshSeed ring root s,
      (bankWordRenewalFreshKernel ring root s).valid a →
      ∀ t,
        costNumerator
          (L3.Prob.attemptStepper
            (bankWordRenewalFreshKernel ring root s))
          (fun v => L3.Prob.attemptGood v ∨
            L3.Prob.attemptFail v)
          (.active ((bankWordRenewalFreshKernel ring root s).start a))
          t ≤ n ^ t * bankWordRenewalBlock n := by
    intro a _ t
    exact hcost a t
  have hf : ∀ a : BankWordRenewalFreshSeed ring root s,
      (bankWordRenewalFreshKernel ring root s).valid a →
      ∀ t, 4 * PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s)
        (.active ((bankWordRenewalFreshKernel ring root s).start a))
        t ≤ 3 * n ^ t := by
    intro a _ t
    exact hfail a t
  have hrenewal := L3.Prob.costNumerator_renewal_le
    (bankWordRenewalNext ring root s)
    (fun v : BankWordRenewalPostSOne ring root s =>
      BankWordRenewalCompleted v.1)
    (bankWordRenewalFreshKernel ring root s)
    (fun x y : BankWordRenewalPostSOne ring root s => x = y)
    (bankWordRenewalFreshSimulation ring root s)
    (bankWordRenewalBlock n) 3 4
    (by decide : 3 < (4 : Nat))
    hc hf seed.1 seed seed.2 rfl T
  rw [bankWordQuarterRetryCeiling] at hrenewal
  exact hrenewal

/-- From the ORIGINAL BANK prepared reference, choose its
actual native root and apply the R10a post-S1
worker clock. This pays one 11*(8*s+5)*n^2 block to the
first genuinely launched W worker on the exact projected
phiW epoch, without assuming a fresh seed at time zero.
Consumer: the first-stage input to R10's 1B + 4B bound. -/
theorem bankWordPreparedProjectedFirstLaunchCostHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPreparedAtSomeRoot ring hbank z)
    (T : Nat) :
    ∃ root : Fin n,
      costNumerator (bankWordEpochNext ring root)
        BankWordEpochWorkerLaunched
        (bankWordEpochStart (piW z.val.1)) T ≤
        n ^ T * bankWordRenewalBlock n := by
  obtain ⟨root, hs, hcandidate⟩ :=
    bankWordPreparedProjectedSerializerRoot ring hbank z hz
  have hworker := bankWordEpochPostSOneWorkerClockHolds
    ring hn hbank root (piW z.val.1) hs
  have hcost := bankWordProjectedOneEpochCostOfWorkerClock
    ring hn hbank root (piW z.val.1) hs hworker T
  have hcoeff :
      8 * ceilLogTwo (ceilLogTwo n) + 5 =
        bankWordRenewalLease n + 1 := by
    unfold bankWordRenewalLease
    omega
  rw [hcoeff] at hcost
  refine ⟨root, ?_⟩
  change costNumerator (bankWordEpochNext ring root)
      BankWordEpochWorkerLaunched
      (bankWordEpochStart (piW z.val.1)) T ≤
      n ^ T *
        (11 * (bankWordRenewalLease n + 1) * n ^ 2)
  exact hcost


/-- The finite E.G14 WordControl's complete follower
publication census entails its local receipt-consistency
predicate, provided the root has no unaccounted publication.
The argument uses the real cyclicOffset representative
rather than treating the follower indices as an arbitrary
enumeration. Consumer: the monitor component of the
WCompletionReceipt-to-AcceptedWord bridge. -/
theorem bankWordFiniteMonitorValidatedOfPublished
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (hpub : BlockA.wordAllPublished ring h)
    (hroot : h.publications h.root = .absent) :
    BlockA.wordValidated ring h := by
  have hfollower : ∀ i : Fin n, i ≠ h.root →
      (h.publications i = .prefixZero →
        h.prefixMarkers i = true ∧
        h.visibleReceipts i = true) ∧
      ((h.publications i = .prefixEnd ∨
        h.publications i = .recurrence) →
        h.visibleReceipts i = true) := by
    intro i hneq
    have hk : PPL.cyclicOffset ring h.root i < n :=
      L3.EWord.validationOffsetBound ring h.root i
    have hrepre := L3.EWord.validationOffsetRepresentative
      ring h.root i
    have hpositive : 0 < PPL.cyclicOffset ring h.root i := by
      by_cases hzero :
          PPL.cyclicOffset ring h.root i = 0
      · rw [hzero, L3.EWord.siteZero] at hrepre
        exact False.elim (hneq hrepre.symm)
      · omega
    have hrow := hpub
      (⟨PPL.cyclicOffset ring h.root i, hk⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hpositive)
    change
      (if PPL.cyclicOffset ring h.root i < c.t then
        h.publications
            (L3.EWord.site ring h.root
              (PPL.cyclicOffset ring h.root i)) =
          .prefixZero ∧
        h.prefixMarkers
            (L3.EWord.site ring h.root
              (PPL.cyclicOffset ring h.root i)) = true ∧
        h.visibleReceipts
            (L3.EWord.site ring h.root
              (PPL.cyclicOffset ring h.root i)) = true
      else if PPL.cyclicOffset ring h.root i = c.t then
        h.publications
            (L3.EWord.site ring h.root
              (PPL.cyclicOffset ring h.root i)) =
          .prefixEnd ∧
        h.visibleReceipts
            (L3.EWord.site ring h.root
              (PPL.cyclicOffset ring h.root i)) = true
      else
        h.publications
            (L3.EWord.site ring h.root
              (PPL.cyclicOffset ring h.root i)) =
          .recurrence ∧
        h.visibleReceipts
            (L3.EWord.site ring h.root
              (PPL.cyclicOffset ring h.root i)) = true) at hrow
    rw [hrepre] at hrow
    split at hrow
    · obtain ⟨hkind, hmarker, hvisible⟩ := hrow
      constructor
      · intro _
        exact ⟨hmarker, hvisible⟩
      · intro hbad
        rcases hbad with hbad | hbad
        · rw [hkind] at hbad
          cases hbad
        · rw [hkind] at hbad
          cases hbad
    · split at hrow
      · obtain ⟨hkind, hvisible⟩ := hrow
        constructor
        · intro hbad
          rw [hkind] at hbad
          cases hbad
        · intro _
          exact hvisible
      · obtain ⟨hkind, hvisible⟩ := hrow
        constructor
        · intro hbad
          rw [hkind] at hbad
          cases hbad
        · intro _
          exact hvisible
  constructor
  · intro i hprefix
    by_cases hrootSite : i = h.root
    · subst i
      rw [hroot] at hprefix
      cases hprefix
    · exact (hfollower i hrootSite).1 hprefix
  · intro i hpublished
    by_cases hrootSite : i = h.root
    · subst i
      rcases hpublished with hpublished | hpublished
      · rw [hroot] at hpublished
        cases hpublished
      · rw [hroot] at hpublished
        cases hpublished
    · exact (hfollower i hrootSite).2 hpublished


/-- The HARD and FRESH renewal kernels stop an attempt as retry
on exactly the same finite scheduler words. Their retry payloads
have different TYPES but each is generated by the SAME old-pair
genuine S6, so retryFirstWord never inspects the payload.
Consumer: transfer of the named BankWordRenewalAttemptFailure
to the fresh renewal kernel used in the 1B+4B clock. -/
theorem bankWordRenewalFreshRetryFirstWordEqHard {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (w : List (Fin n)) :
    L3.Prob.retryFirstWord
        (bankWordRenewalFreshKernel ring root s)
        (.active z) w =
      L3.Prob.retryFirstWord
        (bankWordRenewalHardKernel ring root s)
        (.active z) w := by
  induction w generalizing z with
  | nil =>
      rfl
  | cons e w ih =>
      change
        L3.Prob.retryFirstWord
            (bankWordRenewalFreshKernel ring root s)
            (bankWordRenewalFreshStep ring root s z e) w =
          L3.Prob.retryFirstWord
            (bankWordRenewalHardKernel ring root s)
            (bankWordRenewalHardStep ring root s z e) w
      by_cases hd : BankWordRenewalCompleted
          (bankWordRenewalNext ring root s z e).1
      · simp [bankWordRenewalFreshStep,
          bankWordRenewalHardStep, hd, L3.Prob.retryFirstWord]
      · by_cases hg : bankWordRenewalGenuine ring root z.1 e
        · simp [bankWordRenewalFreshStep,
            bankWordRenewalHardStep, hd, hg,
            L3.Prob.retryFirstWord]
        · simpa [bankWordRenewalFreshStep,
            bankWordRenewalHardStep, hd, hg,
            L3.Prob.retryFirstWord] using
              ih (bankWordRenewalNext ring root s z e)

/-- The two renewal retryCount numerators agree on every
post-S1 active state, by equality of their cylinder-event
indicators on every length-T scheduler word.
Consumer: the named hfail transfer without another probability
or stochastic independence premise. -/
theorem bankWordRenewalFreshRetryCountEqHard {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s) (T : Nat) :
    PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s)
        (.active z) T =
      PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalHardKernel ring root s)
        (.active z) T := by
  rw [L3.Prob.retryCount_eq_wordSum
      (bankWordRenewalFreshKernel ring root s)
      (.active z) T,
    L3.Prob.retryCount_eq_wordSum
      (bankWordRenewalHardKernel ring root s)
      (.active z) T]
  have heq :
      L3.Prob.retryFirstWord
          (bankWordRenewalFreshKernel ring root s)
          (.active z) =
        L3.Prob.retryFirstWord
          (bankWordRenewalHardKernel ring root s)
          (.active z) := by
    funext w
    exact bankWordRenewalFreshRetryFirstWordEqHard
      ring root s z w
  rw [heq]

/-- The ACTUAL fresh seed is hard-valid by its genuinely
accepted predecessor. Thus the named BankWordRenewalAttemptFailure
(hard retry kernel) supplies the retry bound required by the
fresh kernel without a second hfail.
Consumer: R10's fresh 4B renewal stage. -/
theorem bankWordRenewalFreshFailureOfHardFailure {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hfail : BankWordRenewalAttemptFailure ring root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (T : Nat) :
    4 * PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s)
        (.active seed.1) T ≤ 3 * n ^ T := by
  have hfields := bankWordRenewalFreshHardFields
    ring root s seed.1 seed.2
  have hvalid : bankWordRenewalHardValid ring root seed.1.1 :=
    hfields.2.2.2
  have hbound := hfail seed.1 hvalid T
  rw [bankWordRenewalFreshRetryCountEqHard
    ring root s seed.1 T]
  exact hbound

/-- From the SINGLE NAMED hfail premise the genuine fresh
completion costs at most four blocks. This combines the
kernel event-identity proof with the now-premise-free hcost.
Consumer: the continuation stage after the 1B first genuine
W launch in the projected R10 clock. -/
theorem bankWordRenewalFreshFourCostOfAttemptFailure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hfail : BankWordRenewalAttemptFailure ring root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      seed.1 T ≤ n ^ T * (4 * bankWordRenewalBlock n) := by
  exact bankWordRenewalFreshFourCostHoldsOfFailure
    ring hn hbank root s hs
    (fun a t =>
      bankWordRenewalFreshFailureOfHardFailure
        ring root s hfail a t) seed T

/-- A single actual genuine S6, not an artificial restarted
configuration, starts the four-block completion clock under
the named hard-epoch retry estimate.
Consumer: R10 W same-word first-launch → completion handoff. -/
theorem bankWordRenewalFourCostAtGenuineSuccessorOfFailure
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hfail : BankWordRenewalAttemptFailure ring root s)
    (pre : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hg : bankWordRenewalGenuine ring root pre.1 e)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      (bankWordRenewalNext ring root s pre e) T ≤
        n ^ T * (4 * bankWordRenewalBlock n) := by
  obtain ⟨seed, hseed⟩ :=
    bankWordRenewalFreshSeedAfterGenuine ring root s pre e hg
  have hc := bankWordRenewalFreshFourCostOfAttemptFailure
    ring hn hbank root s hs hfail seed T
  rw [hseed] at hc
  exact hc

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A newly populated observer worker, when the predecessor has no
observer worker, must be written by the I0 branch with a joined
genuine acceptance ticket. Consumer: first-launch/fresh-cut
entrance in the R10 W renewal composition. -/
theorem bankWordEpochGenuineOfFirstLaunch {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n)
    (hnot : ¬ BankWordEpochWorkerLaunched z)
    (hlaunch : BankWordEpochWorkerLaunched
      (bankWordEpochNext ring root z e)) :
    bankWordRenewalGenuine ring root z e := by
  have hempty : z.2.2.worker = none := by
    cases hw : z.2.2.worker with
    | none => rfl
    | some w => exact False.elim (hnot ⟨w, hw⟩)
  obtain ⟨w, hw⟩ := hlaunch
  have hstep :
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        none).1 = some w := by
    change (wWorkerReceiptStep root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      z.2.2.worker).1 = some w at hw
    rw [hempty] at hw
    exact hw
  have haccept :
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e))).isSome =
      true := by
    by_cases hi :
        (workerW (z.2.1 e)
          (z.2.1 (ring.rightNeighbor e))).row = "I0"
    · cases ha : wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)) with
      | none =>
          simp [wWorkerReceiptStep, hi, ha] at hstep
      | some ticket =>
          simp [ha]
    · simp [wWorkerReceiptStep, hi] at hstep
  have hcoh :=
    (bankWordRenewalFrontierLedgerGhostCoherence
      ring root s z hz).1
  unfold bankWordRenewalGenuine bankWordHardEpochGenuine
  change
    (wGenuineAcceptance root e
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      ((bankWordHardEpochLedger ring root z).validation e)
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor e))).isSome = true
  rw [hcoh]
  exact haccept

/-- A root ticket with an actual hard-S1 origin implies that the
stopped S1 clock has fired on the represented scheduler history.
Consumer: the post-S1 premise of the first fresh worker seed. -/
theorem bankWordEpochSOneReachedOfRootTicketOrigin {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n) (ticket : WValidationTicket)
    (horigin : BankWordRootTicketOrigin ring root s z ticket) :
    BankWordEpochSOneReached z := by
  obtain ⟨pre, mid, request, hstate, hrequested, _,
    _, _, _, _, _⟩ := horigin
  have hp : BankWordEpochReachable ring root s
      (bankWordEpochRun ring root (bankWordEpochStart s) pre) :=
    ⟨pre, rfl⟩
  have hfixed := bankWordEpochFixedRootNext ring hn hbank root s hs
    (bankWordEpochRun ring root (bankWordEpochStart s) pre) hp root
  have hservice : clockSerializerSOneService ring root
      (bankWordEpochRun ring root
        (bankWordEpochStart s) pre).2.1 root :=
    (clockSerializerSOneIffRequested ring root
      (bankWordEpochRun ring root (bankWordEpochStart s) pre).2.1
      (by omega : 2 ≤ n) hfixed root).2 ⟨rfl, hrequested⟩
  have hinv := bankWordEpochSOneRunningBReachable
    ring root hn hbank s hs
    (bankWordEpochRun ring root (bankWordEpochStart s) pre) hp
  have hstop : BankWordEpochSOneReached
      (bankWordEpochNext ring root
        (bankWordEpochRun ring root (bankWordEpochStart s) pre)
        root) := by
    change clockSerializerIsStopped
      (clockSerializerSOneOnlyNext ring root
        (bankWordEpochRun ring root (bankWordEpochStart s) pre).1 root)
    cases hnode :
        (bankWordEpochRun ring root (bankWordEpochStart s) pre).1 with
    | stopped =>
        exact trivial
    | active w =>
        have hw :
            w = (bankWordEpochRun ring root
              (bankWordEpochStart s) pre).2.1 :=
          hinv.1 w hnode
        rw [hw]
        exact (clockSerializerSOneOnlyStopIff ring root _ root).2
          hservice
  have hfrom : BankWordEpochReachableFrom ring root
      (bankWordEpochNext ring root
        (bankWordEpochRun ring root (bankWordEpochStart s) pre)
        root) z := by
    refine ⟨mid, ?_⟩
    calc
      bankWordEpochRun ring root
          (bankWordEpochNext ring root
            (bankWordEpochRun ring root (bankWordEpochStart s) pre)
            root) mid =
        bankWordEpochRun ring root
          (bankWordEpochRun ring root (bankWordEpochStart s) pre)
          (root :: mid) := rfl
      _ = bankWordEpochRun ring root (bankWordEpochStart s)
          (pre ++ (root :: mid)) :=
        (bankWordEpochRunAppend ring root (bankWordEpochStart s)
          pre (root :: mid)).symm
      _ = z := by rw [hstate]; simp
  exact bankWordEpochSOneReachedFrom ring root _ z hfrom hstop

/-- The represented historical done ticket at genuine S6 has a
root hard-S1 origin, so genuine acceptance cannot precede the
observer's first S1 latch. Consumer: the fresh-seed witness of
the first launched worker on the original projected W chain. -/
theorem bankWordEpochSOneReachedOfGenuine {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hg : bankWordRenewalGenuine ring root z e) :
    BankWordEpochSOneReached z := by
  have hgenuine :
      bankWordHardEpochGenuine ring root
        (bankWordEpochSelectedReceipt ring z e)
        (bankWordHardEpochLedger ring root z) = true := hg
  obtain ⟨he, _, _⟩ :=
    bankWordHardEpochSelectedGenuineOwnerFlags
      ring root z e hgenuine
  subst e
  obtain ⟨ticket, sibling, hdone, _, _, _⟩ :=
    bankWordHardEpochGenuineJoinedStamps
      ring root (bankWordEpochSelectedReceipt ring z root)
      (bankWordHardEpochLedger ring root z) hgenuine
  have hdoneRoot :
      wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation root) =
      some ticket := by
    exact hdone
  have horigin :=
    (bankWordRootDoneOriginReachable
      ring hn hbank root s hs z hz) ticket hdoneRoot
  exact bankWordEpochSOneReachedOfRootTicketOrigin
    ring hn hbank root s hs z ticket horigin

/-- A renewal cut is not an arbitrary launched state: it is an
actual post-S1 successor of a genuine accepted S6, with an explicit
fresh-seed history witness. Consumer: the 1B+4B stage target. -/
def BankWordEpochFreshCut {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n) : Prop :=
  ∃ seed : BankWordRenewalFreshSeed ring root s, seed.1.1 = z

/-- The first nonempty worker edge is a genuine hard S6 and is
already a fresh post-S1 cut on the same physical scheduler word.
Consumer: first-hit entrance domination before the 4B stage. -/
theorem bankWordEpochFreshCutOfFirstLaunch {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n)
    (hnot : ¬ BankWordEpochWorkerLaunched z)
    (hlaunch : BankWordEpochWorkerLaunched
      (bankWordEpochNext ring root z e)) :
    BankWordEpochFreshCut ring root s
      (bankWordEpochNext ring root z e) := by
  have hg := bankWordEpochGenuineOfFirstLaunch
    ring root s z hz e hnot hlaunch
  have hSOne := bankWordEpochSOneReachedOfGenuine
    ring hn hbank root s hs z hz e hg
  obtain ⟨seed, hseed⟩ :=
    bankWordRenewalFreshSeedAfterGenuine ring root s
      ⟨z, hz, hSOne⟩ e hg
  exact ⟨seed, congrArg Subtype.val hseed⟩

/-- From any genuinely fresh cut the real epoch process reaches
the causal worker-completion receipt within four renewal blocks.
The cost is transported by the exact post-S1 subtype projection.
Consumer: the second stage of the R10 W five-block bound. -/
theorem bankWordEpochFreshCutFourCostOfFailure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hfail : BankWordRenewalAttemptFailure ring root s)
    (z : BankWordEpochState n)
    (hfresh : BankWordEpochFreshCut ring root s z)
    (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordRenewalCompleted z T ≤
        n ^ T * (4 * bankWordRenewalBlock n) := by
  obtain ⟨seed, heq⟩ := hfresh
  have hcost := bankWordRenewalFreshFourCostOfAttemptFailure
    ring hn hbank root s hs hfail seed T
  have hmap := costNumerator_map_eq
    (bankWordRenewalNext ring root s)
    (bankWordEpochNext ring root)
    (fun v : BankWordRenewalPostSOne ring root s => v.1)
    (by intro v e; rfl)
    BankWordRenewalCompleted T seed.1
  rw [hmap] at hcost
  rw [heq] at hcost
  exact hcost

/-- A complete W-origin worker receipt is hit in five blocks
from the actual represented projected W entrance, using only
the named retry failure estimate. This does NOT yet assert
AcceptedReceipts.AcceptedWord. Consumer: the completion-stage
input of the exact R10 projected-clock bridge. -/
theorem bankWordEpochCompletionFiveCostOfFailure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hfail : BankWordRenewalAttemptFailure ring root s)
    (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordRenewalCompleted
      (bankWordEpochStart s) T ≤
      n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2) := by
  have hinit : BankWordEpochReachable ring root s
      (bankWordEpochStart s) := ⟨[], rfl⟩
  have hnot :
      ¬ BankWordEpochWorkerLaunched (bankWordEpochStart s) := by
    intro h
    obtain ⟨w, hw⟩ := h
    change (none : Option (WWorkerTrail n)) = some w at hw
    cases hw
  have hfirst : ∀ U,
      costNumerator (bankWordEpochNext ring root)
        (fun z => BankWordEpochFreshCut ring root s z ∨
          BankWordRenewalCompleted z)
        (bankWordEpochStart s) U ≤
        n ^ U * bankWordRenewalBlock n := by
    intro U
    have hentr := costNumerator_entrance_le_on
      (bankWordEpochNext ring root)
      (BankWordEpochReachable ring root s)
      BankWordEpochWorkerLaunched
      (fun z => BankWordEpochFreshCut ring root s z ∨
        BankWordRenewalCompleted z)
      (fun z hz e => bankWordEpochReachableNext ring root s z hz e)
      (fun z hz hnotz e hlaunched =>
        Or.inl (bankWordEpochFreshCutOfFirstLaunch
          ring hn hbank root s hs z hz e hnotz hlaunched))
      U (bankWordEpochStart s) hinit hnot
    have hworker := bankWordEpochPostSOneWorkerClockHolds
      ring hn hbank root s hs
    have hlaunch := bankWordProjectedOneEpochCostOfWorkerClock
      ring hn hbank root s hs hworker U
    have hcoeff :
        8 * ceilLogTwo (ceilLogTwo n) + 5 =
          bankWordRenewalLease n + 1 := by
      unfold bankWordRenewalLease
      omega
    rw [hcoeff] at hlaunch
    change costNumerator (bankWordEpochNext ring root)
      BankWordEpochWorkerLaunched (bankWordEpochStart s) U ≤
      n ^ U * bankWordRenewalBlock n at hlaunch
    exact Nat.le_trans hentr hlaunch
  have hsecond : ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochFreshCut ring root s z →
      ∀ U, costNumerator (bankWordEpochNext ring root)
        BankWordRenewalCompleted z U ≤
        n ^ U * (4 * bankWordRenewalBlock n) := by
    intro z _ hfresh U
    exact bankWordEpochFreshCutFourCostOfFailure
      ring hn hbank root s hs hfail z hfresh U
  have hstage := costNumerator_stage_le_on
    (bankWordEpochNext ring root)
    (BankWordEpochReachable ring root s)
    (BankWordEpochFreshCut ring root s)
    BankWordRenewalCompleted
    (fun z hz e => bankWordEpochReachableNext ring root s z hz e)
    (bankWordEpochStart s) hinit
    (bankWordRenewalBlock n) (4 * bankWordRenewalBlock n)
    hfirst hsecond T
  have hbudget :
      bankWordRenewalBlock n + 4 * bankWordRenewalBlock n =
        5 * bankWordRenewalBlock n := by
    calc
      bankWordRenewalBlock n + 4 * bankWordRenewalBlock n =
          (1 + 4) * bankWordRenewalBlock n := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = 5 * bankWordRenewalBlock n := rfl
  calc
    costNumerator (bankWordEpochNext ring root)
        BankWordRenewalCompleted (bankWordEpochStart s) T ≤
      n ^ T *
        (bankWordRenewalBlock n + 4 * bankWordRenewalBlock n) :=
      hstage
    _ = n ^ T * (5 * bankWordRenewalBlock n) :=
      congrArg (fun b : Nat => n ^ T * b) hbudget
    _ = n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2) := by
      rw [bankWordRenewalFiveCoefficient]

/-- Precise remaining conditional consumer. If every reachable
causal completion really has an E.G14 Generated/validated/QWord
AcceptedWord witness, the completion five-block estimate transfers
to the original phiW first-hit clock at exactly the target budget.
This theorem deliberately does not assert the unproved bridge.
Consumer: BankWordProjectedClock and repair.tex's W stage. -/
theorem bankWordProjectedClockOfFailureAndCompletionBridge {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hfail : ∀ root : Fin n,
      ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        BankWordSerializerRootClass ring hbank root s →
        BankWordRenewalAttemptFailure ring root s)
    (hcompletion : ∀ root : Fin n,
      ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        BankWordSerializerRootClass ring hbank root s →
        ∀ z : BankWordEpochState n,
          BankWordEpochReachable ring root s z →
          BankWordRenewalCompleted z →
          BankWordProjectedTarget ring z.2.1) :
    BankWordProjectedClock ring hbank := by
  intro z hz T
  obtain ⟨root, hs, _⟩ :=
    bankWordPreparedProjectedSerializerRoot ring hbank z hz
  have hcompletionCost := bankWordEpochCompletionFiveCostOfFailure
    ring hn hbank root (piW z.val.1) hs
    (hfail root (piW z.val.1) hs) T
  have hmono := costNumerator_target_mono_on
    (bankWordEpochNext ring root)
    (BankWordEpochReachable ring root (piW z.val.1))
    BankWordRenewalCompleted
    (fun q : BankWordEpochState n =>
      BankWordProjectedTarget ring q.2.1)
    (fun q hq e =>
      bankWordEpochReachableNext
        ring root (piW z.val.1) q hq e)
    (fun q hq hcomplete =>
      hcompletion root (piW z.val.1) hs q hq hcomplete)
    T (bankWordEpochStart (piW z.val.1)) ⟨[], rfl⟩
  have hmap := costNumerator_map_eq
    (bankWordEpochNext ring root)
    (phiW ring)
    (fun q : BankWordEpochState n => q.2.1)
    (by intro q e; exact bankWordEpochPhysicalNext ring root q e)
    (BankWordProjectedTarget ring)
    T (bankWordEpochStart (piW z.val.1))
  rw [hmap] at hmono
  exact Nat.le_trans hmono hcompletionCost

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordRenewalLineageQuietStepOfMovingRows
#print axioms L3.RenewalReferenceClock.bankWordEpochPostSOneWorkerClockOfMovingRows
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshAttemptCostOfMovingRows
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshNotCompleted
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshAttemptCostLe
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshAttemptCostOfLineageStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshFiveCostOfFailure
#print axioms L3.RenewalReferenceClock.bankWordEpochPostLatchRootFactsReachable
#print axioms L3.RenewalReferenceClock.bankWordRenewalLineageQuietOfEverSix
#print axioms L3.RenewalReferenceClock.bankWordEpochLapInvariantStep
#print axioms L3.RenewalReferenceClock.bankWordEpochLapCountOfLineageStep
#print axioms L3.RenewalReferenceClock.bankWordEpochPostSOneWorkerClockOfLineageStep
#print axioms L3.RenewalReferenceClock.bankWordProjectedOneEpochExpectedOfLineageStep
#print axioms L3.RenewalReferenceClock.bankWordRootOutgoingNoDone
#print axioms L3.RenewalReferenceClock.bankWordRootOutgoingRunningFrameRows
#print axioms L3.RenewalReferenceClock.bankWordRootOutgoingFinishRows
#print axioms L3.RenewalReferenceClock.bankWordRootOutgoingSixIdle
#print axioms L3.RenewalReferenceClock.costNumerator_entrance_le_on
#print axioms L3.RenewalReferenceClock.bankWordRootStartCountRestartCostEq
#print axioms L3.RenewalReferenceClock.bankWordEpochLaunchedOfGenuine
#print axioms L3.RenewalReferenceClock.bankWordEpochGenuineCostOfLapCount
#print axioms L3.RenewalReferenceClock.bankWordEpochPostSOneWorkerClockOfLapCount
#print axioms L3.RenewalReferenceClock.bankWordRenewalLineageRootMovingStepHolds
#print axioms L3.RenewalReferenceClock.bankWordEpochPostSOneWorkerClockOfInternalRows
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveForwardExcludesReturnStage
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalReturnRootLineageStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalReturnMoveQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalFrontierInternalQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalFrontierLeafQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveForwardPivotUnique
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveValidationGhostUnique
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveChosenNotUnvisited
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveSelectedRemoteQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalChildPrechallengeQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalFrontierParentQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalChallengedChildQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveForwardCoveredDonePair
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalReturnCoveredQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveSelectedInternalMovingQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalLineageInternalMovingStepHolds
#print axioms L3.RenewalReferenceClock.bankWordEpochPostSOneWorkerClockHolds
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshAttemptCostHolds
#print axioms L3.RenewalReferenceClock.bankWordPreparedProjectedSerializerRoot
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshSeedAfterGenuine
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshFiveCostHoldsOfFailure
#print axioms L3.RenewalReferenceClock.bankWordRenewalFiveCostAtGenuineSuccessor
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshFourCostHoldsOfFailure
#print axioms L3.RenewalReferenceClock.bankWordPreparedProjectedFirstLaunchCostHolds
#print axioms L3.RenewalReferenceClock.bankWordFiniteMonitorValidatedOfPublished
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshRetryFirstWordEqHard
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshRetryCountEqHard
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshFailureOfHardFailure
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshFourCostOfAttemptFailure
#print axioms L3.RenewalReferenceClock.bankWordRenewalFourCostAtGenuineSuccessorOfFailure
#print axioms L3.RenewalReferenceClock.bankWordEpochGenuineOfFirstLaunch
#print axioms L3.RenewalReferenceClock.bankWordEpochSOneReachedOfRootTicketOrigin
#print axioms L3.RenewalReferenceClock.bankWordEpochSOneReachedOfGenuine
#print axioms L3.RenewalReferenceClock.bankWordEpochFreshCutOfFirstLaunch
#print axioms L3.RenewalReferenceClock.bankWordEpochFreshCutFourCostOfFailure
#print axioms L3.RenewalReferenceClock.bankWordEpochCompletionFiveCostOfFailure
#print axioms L3.RenewalReferenceClock.bankWordProjectedClockOfFailureAndCompletionBridge

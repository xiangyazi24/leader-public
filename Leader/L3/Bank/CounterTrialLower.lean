import Leader.L3.Bank.CounterCold

/-!
First-K physical-port fairness for a BANK trial.

This concerns the original IID Fin n scheduler and does not
identify a successful private-counter trial with its edge labels.
-/

namespace L3.CounterTrialLower

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

private theorem ofFnDistinctNames {k : Nat} {A : Type}
    (f : Fin k → A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        have hh := hf hi
        cases hh
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

/-- The two nominated ports contribute one copy each. -/
private theorem twoPortSum {n : Nat}
    (a b : Fin n) (x y z : Nat) (hab : a ≠ b) :
    (List.ofFn (fun e : Fin n =>
      if e = a then x else if e = b then y else z)).sum =
      x + y + (n - 2) * z := by
  have hh := sum_two_exceptions
    (List.ofFn (fun e : Fin n => e)) a b
    (fun e : Fin n =>
      if e = a then x else if e = b then y else z) z
    (ofFnDistinctNames (fun e : Fin n => e) Function.injective_id)
    (List.mem_ofFn.mpr ⟨a, rfl⟩)
    (List.mem_ofFn.mpr ⟨b, rfl⟩) hab
    (by
      intro e _ hea heb
      simp [hea, heb])
  simpa [List.map_ofFn, Function.comp_def, hab,
    Ne.symm hab] using hh

/-- Finite padded word mass of a constant weight. -/
private theorem constantWordMass (n T x : Nat) :
    Counter.resetColdWordSum n T (fun _ => x) =
      n ^ T * x := by
  induction T with
  | zero =>
      show x = n ^ 0 * x
      rw [Nat.pow_zero, Nat.one_mul]
  | succ T ih =>
      change (List.ofFn (fun _ : Fin n =>
        Counter.resetColdWordSum n T (fun _ => x))).sum =
        n ^ (T + 1) * x
      rw [ih, ofFn_sum_const, Nat.pow_succ]
      ac_rfl

/-- The first k interactions at the two ports are all outgoing. -/
def allOutgoingWord {n : Nat} (a b : Fin n) :
    Nat → List (Fin n) → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | k + 1, e :: w =>
      if e = a then allOutgoingWord a b k w
      else if e = b then false
      else allOutgoingWord a b (k + 1) w

/-- At least k interactions hit either nominated port. -/
def enoughIncidentsWord {n : Nat} (a b : Fin n) :
    Nat → List (Fin n) → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | k + 1, e :: w =>
      if e = a ∨ e = b then enoughIncidentsWord a b k w
      else enoughIncidentsWord a b (k + 1) w

noncomputable def allOutgoingMass {n : Nat}
    (a b : Fin n) (k T : Nat) : Nat :=
  Counter.resetColdWordSum n T (fun w =>
    if allOutgoingWord a b k w then 1 else 0)

noncomputable def enoughIncidentsMass {n : Nat}
    (a b : Fin n) (k T : Nat) : Nat :=
  Counter.resetColdWordSum n T (fun w =>
    if enoughIncidentsWord a b k w then 1 else 0)

private theorem allOutgoingMassZero {n : Nat}
    (a b : Fin n) (T : Nat) :
    allOutgoingMass a b 0 T = n ^ T := by
  unfold allOutgoingMass
  have h : (fun w : List (Fin n) =>
      if allOutgoingWord a b 0 w then 1 else 0) = fun _ => 1 := by
    funext w
    simp [allOutgoingWord]
  rw [h, constantWordMass]
  simp

private theorem enoughIncidentsMassZero {n : Nat}
    (a b : Fin n) (T : Nat) :
    enoughIncidentsMass a b 0 T = n ^ T := by
  unfold enoughIncidentsMass
  have h : (fun w : List (Fin n) =>
      if enoughIncidentsWord a b 0 w then 1 else 0) = fun _ => 1 := by
    funext w
    simp [enoughIncidentsWord]
  rw [h, constantWordMass]
  simp

private theorem allOutgoingMassEmpty {n : Nat}
    (a b : Fin n) (k : Nat) :
    allOutgoingMass a b (k + 1) 0 = 0 := rfl

private theorem enoughIncidentsMassEmpty {n : Nat}
    (a b : Fin n) (k : Nat) :
    enoughIncidentsMass a b (k + 1) 0 = 0 := rfl

private theorem allOutgoingChild {n : Nat}
    (a b e : Fin n) (k T : Nat) :
    Counter.resetColdWordSum n T (fun w =>
      if allOutgoingWord a b (k + 1) (e :: w) then 1 else 0) =
    (if e = a then allOutgoingMass a b k T
     else if e = b then 0
     else allOutgoingMass a b (k + 1) T) := by
  by_cases ha : e = a
  · simp [allOutgoingWord, ha, allOutgoingMass]
  · by_cases hb : e = b
    · subst hb
      have hz : Counter.resetColdWordSum n T
          (fun _ : List (Fin n) => 0) = 0 := by
        rw [constantWordMass]
        simp
      simp [allOutgoingWord, ha, hz]
    · simp [allOutgoingWord, ha, hb, allOutgoingMass]

private theorem enoughIncidentsChild {n : Nat}
    (a b e : Fin n) (k T : Nat) :
    Counter.resetColdWordSum n T (fun w =>
      if enoughIncidentsWord a b (k + 1) (e :: w) then 1 else 0) =
    (if e = a then enoughIncidentsMass a b k T
     else if e = b then enoughIncidentsMass a b k T
     else enoughIncidentsMass a b (k + 1) T) := by
  by_cases ha : e = a
  · simp [enoughIncidentsWord, ha, enoughIncidentsMass]
  · by_cases hb : e = b
    · simp [enoughIncidentsWord, ha, hb, enoughIncidentsMass]
    · simp [enoughIncidentsWord, ha, hb, enoughIncidentsMass]

private theorem allOutgoingMassSucc {n : Nat}
    (a b : Fin n) (hab : a ≠ b) (k T : Nat) :
    allOutgoingMass a b (k + 1) (T + 1) =
      allOutgoingMass a b k T +
        (n - 2) * allOutgoingMass a b (k + 1) T := by
  calc
    allOutgoingMass a b (k + 1) (T + 1) =
        (List.ofFn (fun e : Fin n =>
          Counter.resetColdWordSum n T (fun w =>
            if allOutgoingWord a b (k + 1) (e :: w)
            then 1 else 0))).sum := rfl
    _ = (List.ofFn (fun e : Fin n =>
          if e = a then allOutgoingMass a b k T
          else if e = b then 0
          else allOutgoingMass a b (k + 1) T)).sum := by
        apply congrArg (fun f : Fin n → Nat => (List.ofFn f).sum)
        funext e
        exact allOutgoingChild a b e k T
    _ = allOutgoingMass a b k T + 0 +
          (n - 2) * allOutgoingMass a b (k + 1) T :=
        twoPortSum a b _ _ _ hab
    _ = allOutgoingMass a b k T +
          (n - 2) * allOutgoingMass a b (k + 1) T := by omega

private theorem enoughIncidentsMassSucc {n : Nat}
    (a b : Fin n) (hab : a ≠ b) (k T : Nat) :
    enoughIncidentsMass a b (k + 1) (T + 1) =
      2 * enoughIncidentsMass a b k T +
        (n - 2) * enoughIncidentsMass a b (k + 1) T := by
  calc
    enoughIncidentsMass a b (k + 1) (T + 1) =
        (List.ofFn (fun e : Fin n =>
          Counter.resetColdWordSum n T (fun w =>
            if enoughIncidentsWord a b (k + 1) (e :: w)
            then 1 else 0))).sum := rfl
    _ = (List.ofFn (fun e : Fin n =>
          if e = a then enoughIncidentsMass a b k T
          else if e = b then enoughIncidentsMass a b k T
          else enoughIncidentsMass a b (k + 1) T)).sum := by
        apply congrArg (fun f : Fin n → Nat => (List.ofFn f).sum)
        funext e
        exact enoughIncidentsChild a b e k T
    _ = enoughIncidentsMass a b k T +
          enoughIncidentsMass a b k T +
          (n - 2) * enoughIncidentsMass a b (k + 1) T :=
        twoPortSum a b _ _ _ hab
    _ = 2 * enoughIncidentsMass a b k T +
          (n - 2) * enoughIncidentsMass a b (k + 1) T := by omega

/-- Exact fair-bit law on the original full scheduler tape.
Only words with >=K root incidences appear on the right. -/
theorem allOutgoingFairMass {n : Nat}
    (a b : Fin n) (hab : a ≠ b) (T K : Nat) :
    2 ^ K * allOutgoingMass a b K T =
      enoughIncidentsMass a b K T := by
  induction T generalizing K with
  | zero =>
      cases K with
      | zero =>
          rw [allOutgoingMassZero, enoughIncidentsMassZero]
          simp
      | succ K =>
          rw [allOutgoingMassEmpty, enoughIncidentsMassEmpty]
          simp
  | succ T ih =>
      cases K with
      | zero =>
          rw [allOutgoingMassZero, enoughIncidentsMassZero]
          simp
      | succ K =>
          rw [allOutgoingMassSucc a b hab K T,
            enoughIncidentsMassSucc a b hab K T]
          have hk := ih K
          have hnext := ih (K + 1)
          calc
            2 ^ (K + 1) *
                (allOutgoingMass a b K T +
                  (n - 2) * allOutgoingMass a b (K + 1) T) =
              2 * (2 ^ K * allOutgoingMass a b K T) +
                (n - 2) *
                  (2 ^ (K + 1) * allOutgoingMass a b (K + 1) T) := by
                    simp only [Nat.pow_succ, Nat.mul_add]
                    ac_rfl
            _ = 2 * enoughIncidentsMass a b K T +
                  (n - 2) * enoughIncidentsMass a b (K + 1) T := by
                    rw [hk, hnext]

/-- Genuine incoming root port is distinct from the outgoing one
whenever the protected spatial roles are complete. -/
theorem cleanRootPortsDistinct {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.ResetClockBankClean ring C root) :
    root ≠ Counter.site ring root (n - 1) := by
  intro he
  have hlast := Counter.resetColdLastSiteIncoming ring root
  rw [← he] at hlast
  exact (Counter.resetColdRootPortDistinct ring C root hc.1) hlast

/-- First-K heads from the actual pair of ring-edge names. -/
theorem cleanAllOutgoingFairMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.ResetClockBankClean ring C root)
    (T K : Nat) :
    2 ^ K *
      allOutgoingMass root (Counter.site ring root (n - 1)) K T =
      enoughIncidentsMass root (Counter.site ring root (n - 1)) K T := by
  exact allOutgoingFairMass root (Counter.site ring root (n - 1))
    (cleanRootPortsDistinct ring root C hc) T K

/-- Other edges cannot change the actual root mode. -/
theorem nonincidentRootModeFixed {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (he : e ≠ root)
    (hpred : ring.rightNeighbor e ≠ root) :
    (((protocol q).step ring C e) root).mode = (C root).mode := by
  exact Counter.resetColdNonincidentRootMode ring C root e he hpred

/-- The good outgoing root service begins a genuine head. -/
theorem cleanOutgoingStartsHead {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.ResetClockBankClean ring C root)
    (hg : Counter.resetColdPrivateGlobalGrantFree C)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ Counter.ResetClockBankDefectEntry ring C root root) :
    Counter.resetColdLatchedPrivateNext ring root
      (.live C false) root =
        .live ((protocol q).step ring C root) true := by
  exact Counter.resetColdPrivateFirstOutgoingLive
    ring root C hc hg hsp hno

/-- The good incoming root service is a tail, not a head. -/
theorem cleanIncomingStartsTail {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.ResetClockBankClean ring C root)
    (hg : Counter.GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ Counter.ResetClockBankDefectEntry ring C root
      (Counter.site ring root (n - 1))) :
    Counter.resetColdLatchedPrivateNext ring root
      (.live C false) (Counter.site ring root (n - 1)) =
      .recovery ((protocol q).step ring C
        (Counter.site ring root (n - 1))) := by
  exact Counter.resetColdLatchedPrivateIncomingTail
    ring root (Counter.site ring root (n - 1))
    C false hsp hc.1 hg hno
    (Counter.resetColdLastSiteIncoming ring root)
    (Ne.symm (cleanRootPortsDistinct ring root C hc))
    hc.2.1

/-- The C.1 numeric watchdog bound is already established upstream. -/
theorem spatialWatchdogMargin (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    Counter.resetColdWatchdogNumerator (compileAdvice q).b <
      Counter.resetColdWatchdogDenominator (compileAdvice q).b := by
  exact Counter.resetColdWatchdogAll (compileAdvice q).b
    (Counter.resetColdWatchdogSpatialWidth q hsp)

/-- The desired C.4/C.5 lower bound, stated only as a Prop.
A finite T is appropriate because the watchdog estimate is strict.
No machine-level lower bound is asserted as a theorem here. -/
noncomputable def PrivateTrialSuccessLower {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  (compileAdvice q).useSmall = false →
    ∀ C : Counter.Config q n,
      Counter.ResetClockBankClean ring C root →
      Counter.resetColdPrivateGlobalGrantFree C →
      ∃ T : Nat,
        1023 * n ^ T ≤
          1024 * 2 ^ (compileAdvice q).K *
            Counter.resetColdLatchedPrivateSuccessMass ring root C T

end L3.CounterTrialLower

/-!
Adapted worker watchdogs on the SAME IID edge tape.

At each selected physical edge an adapted observer can create a finite
list of new worker origins. Each origin carries its data to a predicate
on the future scheduler suffix. No independent worker clocks are
introduced. Actual physical C.1 rarity and worker-start count are Props,
not asserted theorems of the BANK transition.
-/

namespace L3.CounterTrialLower

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

def workerTimeoutNumerator (b : Nat) : Nat :=
  2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)

def workerTimeoutDenominator (b : Nat) : Nat :=
  5 ^ (11 * b + 24)

/-- Adapted union bound over all worker-start cuts in one physical
word. OriginRarity is the conditional suffix failure bound at
every actual post-service start. The stopped origins/first-success
counting theorem proves the tower property without independence.
The global cap M is on all materialized histories, not active slots. -/
theorem adaptedWorkerTimeoutUnion {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (starts : S → Fin n → List O)
    (timeout : O → List (Fin n) → Bool)
    (num den M : Nat)
    (hrare : L3.Prob.OriginRarity Stop starts timeout num den)
    (x : S) (T : Nat)
    (hcap : ∀ w : List (Fin n),
      L3.Prob.originsWord next Stop starts x w ≤ M) :
    den * L3.Prob.originEventNumerator
      next Stop starts timeout x T ≤ num * (n ^ T * M) := by
  have hfirst := L3.Prob.origin_counting_le
    next Stop starts timeout num den hrare x T
  have hcount : L3.Prob.originsNumerator
      next Stop starts x T ≤ n ^ T * M := by
    change L3.Prob.scheduleSum n T
      (L3.Prob.originsWord next Stop starts x) ≤ n ^ T * M
    calc
      _ ≤ L3.Prob.scheduleSum n T (fun _ => M) :=
        L3.Density.schedule_sum_mono T _ _ hcap
      _ = n ^ T * M := L3.Density.schedule_sum_const T M
  exact Nat.le_trans hfirst (Nat.mul_le_mul_left num hcount)

/-- The missing real C.1 per-clean-worker estimate as a named Prop.
Here starts reads ONLY the actual latched observer and physical edge;
timeout must report failure of that very clean worker in the real
future suffix. The observer creates no origins after terminal. -/
def PrivateCleanWorkerWatchdog {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    {O : Type}
    (starts : Counter.ResetColdLatchedPrivateState q n →
      Fin n → List O)
    (timeout : O → List (Fin n) → Bool) : Prop :=
  L3.Prob.OriginRarity
    (Counter.resetColdLatchedPrivateTerminal)
    starts timeout
    (workerTimeoutNumerator (compileAdvice q).b)
    (workerTimeoutDenominator (compileAdvice q).b)

/-- Separate physical worker-history multiplicity premise.
This applies to all words, not only to a future-chosen good word. -/
def PrivateCleanWorkerStartCap {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) {O : Type}
    (starts : Counter.ResetColdLatchedPrivateState q n →
      Fin n → List O) : Prop :=
  ∀ w : List (Fin n),
    L3.Prob.originsWord
      (Counter.resetColdLatchedPrivateNext ring root)
      (Counter.resetColdLatchedPrivateTerminal)
      starts (.live C false) w ≤
        2 * (compileAdvice q).K + 1

/-- Unnormalized count of words with any spawned worker timeout. -/
noncomputable def privateWorkerTimeoutMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) {O : Type}
    (starts : Counter.ResetColdLatchedPrivateState q n →
      Fin n → List O)
    (timeout : O → List (Fin n) → Bool)
    (T : Nat) : Nat :=
  L3.Prob.originEventNumerator
    (Counter.resetColdLatchedPrivateNext ring root)
    (Counter.resetColdLatchedPrivateTerminal)
    starts timeout (.live C false) T

theorem privateWorkerTimeoutUnion {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) {O : Type}
    (starts : Counter.ResetColdLatchedPrivateState q n →
      Fin n → List O)
    (timeout : O → List (Fin n) → Bool)
    (hrare : PrivateCleanWorkerWatchdog ring root starts timeout)
    (hcap : PrivateCleanWorkerStartCap ring root C starts)
    (T : Nat) :
    workerTimeoutDenominator (compileAdvice q).b *
      privateWorkerTimeoutMass ring root C starts timeout T ≤
    workerTimeoutNumerator (compileAdvice q).b *
      (n ^ T * (2 * (compileAdvice q).K + 1)) := by
  exact adaptedWorkerTimeoutUnion
    (Counter.resetColdLatchedPrivateNext ring root)
    (Counter.resetColdLatchedPrivateTerminal)
    starts timeout
    (workerTimeoutNumerator (compileAdvice q).b)
    (workerTimeoutDenominator (compileAdvice q).b)
    (2 * (compileAdvice q).K + 1) hrare
    (.live C false) T hcap

/-- M = 2K+1 is within the C.4 numerical worker allowance. -/
theorem workerCountWithinWatchdog (b K : Nat)
    (hwidth : K < 2 ^ b) :
    2 * K + 1 ≤ 2 ^ (b + 1) + 1 := by
  have hm := Nat.mul_le_mul_left 2 (Nat.le_of_lt hwidth)
  rw [Nat.pow_succ]
  omega

theorem workerCountNumeratorLe (b K : Nat)
    (hwidth : K < 2 ^ b) :
    (2 * K + 1) * workerTimeoutNumerator b ≤
      (2 ^ (b + 1) + 1) * workerTimeoutNumerator b := by
  exact Nat.mul_le_mul_right _
    (workerCountWithinWatchdog b K hwidth)

/-- Exact reuse of the resetColdWatchdogCompiled certificate:
1024 * M * deltaNumerator < deltaDenominator. -/
theorem workerBudgetBelowThousandTwentyFour (q M : Nat)
    (hsp : (compileAdvice q).useSmall = false)
    (hcount : M ≤ 2 ^ ((compileAdvice q).b + 1) + 1) :
    1024 * M * workerTimeoutNumerator (compileAdvice q).b <
      workerTimeoutDenominator (compileAdvice q).b := by
  have hw := Counter.resetColdWatchdogCompiled q hsp
  unfold workerTimeoutNumerator workerTimeoutDenominator
  calc
    1024 * M *
        (2 ^ (2 * (compileAdvice q).b + 2) *
          4 ^ (11 * (compileAdvice q).b + 24)) ≤
      1024 * (2 ^ ((compileAdvice q).b + 1) + 1) *
        2 ^ (2 * (compileAdvice q).b + 2) *
          4 ^ (11 * (compileAdvice q).b + 24) := by
            have hm := Nat.mul_le_mul_left 1024 hcount
            have htwo := Nat.mul_le_mul_right
              (2 ^ (2 * (compileAdvice q).b + 2)) hm
            have hfour := Nat.mul_le_mul_right
              (4 ^ (11 * (compileAdvice q).b + 24)) htwo
            simpa only [Nat.mul_assoc] using hfour
    _ < 5 ^ (11 * (compileAdvice q).b + 24) := hw

theorem privateWorkerBudgetCompiled (q : Nat)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b) :
    1024 * (2 * (compileAdvice q).K + 1) *
        workerTimeoutNumerator (compileAdvice q).b <
      workerTimeoutDenominator (compileAdvice q).b := by
  exact workerBudgetBelowThousandTwentyFour q
    (2 * (compileAdvice q).K + 1) hsp
    (workerCountWithinWatchdog (compileAdvice q).b
      (compileAdvice q).K hwidth)

/-- Conditional on the named worker premises, the UNCONDITIONAL
timeout mass in the original uniform scheduler is at most 1/1024. -/
theorem privateWorkerTimeoutTiny {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) {O : Type}
    (starts : Counter.ResetColdLatchedPrivateState q n →
      Fin n → List O)
    (timeout : O → List (Fin n) → Bool)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hrare : PrivateCleanWorkerWatchdog ring root starts timeout)
    (hcap : PrivateCleanWorkerStartCap ring root C starts)
    (T : Nat) :
    1024 * privateWorkerTimeoutMass ring root C starts timeout T ≤
      n ^ T := by
  have hr := privateWorkerTimeoutUnion
    ring root C starts timeout hrare hcap T
  have hm := privateWorkerBudgetCompiled q hsp hwidth
  have hden : 0 < workerTimeoutDenominator (compileAdvice q).b :=
    Nat.pow_pos (by decide : 0 < (5 : Nat))
  generalize workerTimeoutDenominator (compileAdvice q).b = D at hr hm hden ⊢
  generalize workerTimeoutNumerator (compileAdvice q).b = N at hr hm ⊢
  generalize privateWorkerTimeoutMass ring root C starts timeout T = X at hr ⊢
  generalize 2 * (compileAdvice q).K + 1 = M at hr hm ⊢
  generalize n ^ T = P at hr ⊢
  have hscaled : D * (1024 * X) ≤ D * P := by
    calc
      D * (1024 * X) = 1024 * (D * X) := Nat.mul_left_comm D 1024 X
      _ ≤ 1024 * (N * (P * M)) := Nat.mul_le_mul_left 1024 hr
      _ = (1024 * M * N) * P := by ac_rfl
      _ ≤ D * P := Nat.mul_le_mul_right P (Nat.le_of_lt hm)
  exact Nat.le_of_mul_le_mul_left hscaled hden

theorem privateWorkerNoTimeoutMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) {O : Type}
    (starts : Counter.ResetColdLatchedPrivateState q n →
      Fin n → List O)
    (timeout : O → List (Fin n) → Bool)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hrare : PrivateCleanWorkerWatchdog ring root starts timeout)
    (hcap : PrivateCleanWorkerStartCap ring root C starts)
    (T : Nat) :
    1023 * n ^ T ≤
      1024 * (n ^ T -
        privateWorkerTimeoutMass ring root C starts timeout T) := by
  have ht := privateWorkerTimeoutTiny
    ring root C starts timeout hsp hwidth hrare hcap T
  omega

/-- No supported OLD bad-pair or protected-role-change defect. -/
def DefectFreeSupport {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Prop :=
  ∀ e : Fin n, Counter.Support q ring root e →
    ¬ Counter.ResetClockBankDefectEntry ring C root e

theorem defectFreeSelected {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hfree : DefectFreeSupport ring root C) :
    ¬ Counter.ResetClockBankDefectEntry ring C root e := by
  intro hd
  exact hfree e hd.1 hd

/-- Defect is not an available LIVE exit under DefectFreeSupport.
A later authenticated Clean still can produce ordinary failure. -/
theorem defectFreeLatchedLiveStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n) (started : Bool)
    (hfree : DefectFreeSupport ring root C) :
    Counter.resetColdLatchedPrivateNext ring root (.live C started) e =
      (if Counter.resetColdPrivateSuccessAt ring root C e then
        .success ((protocol q).step ring C e)
      else if Counter.resetColdLatchedBegun ring root e started then
        if Counter.ResetClockBankClean ring
          ((protocol q).step ring C e) root then
          .failure ((protocol q).step ring C e)
        else if Counter.resetColdLatchedAbort ring root C e then
          .recovery ((protocol q).step ring C e)
        else .live ((protocol q).step ring C e) true
      else if Counter.resetColdLatchedAbort ring root C e then
        .recovery ((protocol q).step ring C e)
      else .live ((protocol q).step ring C e) false) := by
  have hno := defectFreeSelected ring root e C hfree
  simp only [Counter.resetColdLatchedPrivateNext, if_neg hno]

theorem defectFreeLatchedRecoveryStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hfree : DefectFreeSupport ring root C) :
    Counter.resetColdLatchedPrivateNext ring root (.recovery C) e =
      (if Counter.ResetClockBankClean ring
        ((protocol q).step ring C e) root then
        .failure ((protocol q).step ring C e)
      else .recovery ((protocol q).step ring C e)) := by
  have hno := defectFreeSelected ring root e C hfree
  simp only [Counter.resetColdLatchedPrivateNext, if_neg hno]

/-- Defect-free scope at every actual preterminal cut, not only
at the initial Clean snapshot. -/
def DefectFreeLatchedHistory {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Prop :=
  ∀ w : List (Fin n),
    ¬ Counter.resetColdLatchedPrivateTerminal
      (Counter.resetColdLatchedPrivateRun ring root (.live C false) w) →
    DefectFreeSupport ring root
      (Counter.resetColdLatchedPrivateConfig
        (Counter.resetColdLatchedPrivateRun ring root (.live C false) w))

theorem defectFreeHistorySelected {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hfree : DefectFreeLatchedHistory ring root C)
    (w : List (Fin n))
    (hlive : ¬ Counter.resetColdLatchedPrivateTerminal
      (Counter.resetColdLatchedPrivateRun ring root (.live C false) w)) :
    ¬ Counter.ResetClockBankDefectEntry ring
      (Counter.resetColdLatchedPrivateConfig
        (Counter.resetColdLatchedPrivateRun ring root (.live C false) w))
      root e := by
  exact defectFreeSelected ring root e _ (hfree w hlive)

/-- Required C.4/C.5 lower success probability, explicitly
restricted to defect-free actual histories. Prop ONLY, unproved. -/
noncomputable def PrivateTrialSuccessLowerDefectFree {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  (compileAdvice q).useSmall = false →
    ∀ C : Counter.Config q n,
      Counter.ResetClockBankClean ring C root →
      Counter.resetColdPrivateGlobalGrantFree C →
      DefectFreeLatchedHistory ring root C →
      ∃ T : Nat,
        1023 * n ^ T ≤
          1024 * 2 ^ (compileAdvice q).K *
            Counter.resetColdLatchedPrivateSuccessMass ring root C T

end L3.CounterTrialLower


/-!
Conditional two-penalty C.1 bound on one IID scheduler tape.

The observer state x can contain the entire revealed prefix and the
current worker names. The next designated letter and penalty predicate
depend on x, not on the unseen next scheduler letter. The penalty
cardinality bound is required at every x, including adapted cuts.

The finite-word count G is truncated at the end of the word when fewer
than L services have occurred. Thus the tail statement also controls
every finite observation prefix of an unfinished worker. No independent
worker scheduler is introduced.
-/

namespace L3.CounterTrialLower

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- Penalties observed before the L-th designated service or the word end.
The next designation can depend on the entire preceding word via x. -/
noncomputable def workerPenaltyCount {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop) :
    S → Nat → List (Fin n) → Nat
  | _, _, [] => 0
  | _, 0, _ :: _ => 0
  | x, L + 1, e :: w =>
      if e = designated x then
        workerPenaltyCount next designated penalty (next x e) L w
      else if penalty x e then
        1 + workerPenaltyCount next designated penalty
          (next x e) (L + 1) w
      else
        workerPenaltyCount next designated penalty
          (next x e) (L + 1) w

/-- Cleared exponential moment, stopped at m penalties and L services.
The initial weight is 4^m; each penalized service replaces one factor
4 by 5. A designated service decreases the service budget. -/
noncomputable def workerCapWeight {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop) :
    S → Nat → Nat → List (Fin n) → Nat
  | _, _, m, [] => 4 ^ m
  | x, L, m, e :: w =>
      if m = 0 then 1
      else if L = 0 then 4 ^ m
      else if e = designated x then
        workerCapWeight next designated penalty
          (next x e) (L - 1) m w
      else if penalty x e then
        5 * workerCapWeight next designated penalty
          (next x e) L (m - 1) w
      else
        workerCapWeight next designated penalty
          (next x e) L m w

noncomputable def workerCapMass {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop)
    (x : S) (L m T : Nat) : Nat :=
  Counter.resetColdWordSum n T
    (workerCapWeight next designated penalty x L m)

noncomputable def workerPenaltyTailMass {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop)
    (x : S) (L m T : Nat) : Nat :=
  Counter.resetColdWordSum n T
    (fun w => if m ≤ workerPenaltyCount next designated penalty x L w
      then 1 else 0)

/-- Linear positive scalar commutes with the finite scheduler sum. -/
private theorem workerWordSumMul {n : Nat}
    (T k : Nat) (f : List (Fin n) → Nat) :
    Counter.resetColdWordSum n T (fun w => k * f w) =
      k * Counter.resetColdWordSum n T f := by
  induction T generalizing f with
  | zero => rfl
  | succ T ih =>
      calc
        Counter.resetColdWordSum n (T + 1) (fun w => k * f w) =
            (List.ofFn (fun e : Fin n =>
              Counter.resetColdWordSum n T
                (fun w => k * f (e :: w)))).sum := rfl
        _ = (List.ofFn (fun e : Fin n =>
              k * Counter.resetColdWordSum n T
                (fun w => f (e :: w)))).sum :=
          ofFn_sum_eq _ _ (fun e => ih (fun w => f (e :: w)))
        _ = k * (List.ofFn (fun e : Fin n =>
              Counter.resetColdWordSum n T
                (fun w => f (e :: w)))).sum := by
          rw [ofFn_sum_mul_left]
        _ = k * Counter.resetColdWordSum n (T + 1) f := rfl

private theorem workerWordSumMono {n : Nat}
    (T : Nat) (f g : List (Fin n) → Nat)
    (h : ∀ w, f w ≤ g w) :
    Counter.resetColdWordSum n T f ≤
      Counter.resetColdWordSum n T g := by
  induction T generalizing f g with
  | zero => exact h []
  | succ T ih =>
      change
        (List.ofFn (fun e : Fin n =>
          Counter.resetColdWordSum n T (fun w => f (e :: w)))).sum ≤
        (List.ofFn (fun e : Fin n =>
          Counter.resetColdWordSum n T (fun w => g (e :: w)))).sum
      exact ofFn_sum_le _ _ (fun e =>
        ih (fun w => f (e :: w))
          (fun w => g (e :: w)) (fun w => h (e :: w)))

private theorem workerSpikeMass {n : Nat}
    (a : Fin n) (v : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = a then v else 0)).sum = v := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
      cases a using Fin.cases with
      | zero =>
          have hz : ∀ m : Nat,
              (List.ofFn (fun _ : Fin m => (0 : Nat))).sum = 0 := by
            intro m
            induction m with
            | zero => rfl
            | succ m ihm =>
                rw [List.ofFn_succ, List.sum_cons, ihm]
          have hf : (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0) =
              fun _ => 0 :=
            funext fun i => if_neg (Fin.succ_ne_zero i)
          simp only [List.ofFn_succ, List.sum_cons]
          rw [hf, hz]
          simp
      | succ a =>
          have hf : (fun i : Fin n =>
              if i.succ = a.succ then v else 0) =
              fun i => if i = a then v else 0 :=
            funext fun i => by simp only [Fin.succ_inj]
          simp only [List.ofFn_succ, List.sum_cons]
          rw [hf, ih a, if_neg (Fin.succ_ne_zero a).symm, Nat.zero_add]

/-- The local Bellman coefficient is at most the total number of
scheduler outcomes times four. The selected D-letter contributes 2
instead of 4; at most two disjoint P-letters contribute 5 instead of 4.
This is the integer form of 1/2 + 2(5/4) + (n-3) <= n. -/
private theorem workerCoefficientBound {n : Nat}
    (d : Fin n) (p : Fin n → Prop)
    (hdisj : ¬ p d)
    (hcap : (List.ofFn (fun e : Fin n =>
      if p e then 1 else 0)).sum ≤ 2) :
    (List.ofFn (fun e : Fin n =>
      if e = d then 2 else if p e then 5 else 4)).sum ≤
      4 * n := by
  have hpoint (e : Fin n) :
      (if e = d then 2 else if p e then 5 else 4) +
        (if e = d then 2 else 0) =
        4 + (if p e then 1 else 0) := by
    by_cases hd : e = d
    · subst e
      simp [hdisj]
    · by_cases hp : p e
      · simp [hd, hp]
      · simp [hd, hp]
  have hs := ofFn_sum_eq
    (fun e : Fin n =>
      (if e = d then 2 else if p e then 5 else 4) +
        (if e = d then 2 else 0))
    (fun e : Fin n => 4 + (if p e then 1 else 0)) hpoint
  rw [ofFn_sum_add, ofFn_sum_add, ofFn_sum_const,
    workerSpikeMass] at hs
  omega

private theorem workerCapMassZeroService {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop)
    (x : S) (m T : Nat) :
    workerCapMass next designated penalty x 0 m T =
      n ^ T * 4 ^ m := by
  unfold workerCapMass
  have hfun :
      (workerCapWeight next designated penalty x 0 m) =
        (fun _ : List (Fin n) => 4 ^ m) := by
    funext w
    cases w with
    | nil => rfl
    | cons e w =>
        by_cases hm : m = 0
        · subst m
          simp [workerCapWeight]
        · simp [workerCapWeight, hm]
  rw [hfun, constantWordMass]

private theorem workerCapMassZeroPenalty {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop)
    (x : S) (L T : Nat) :
    workerCapMass next designated penalty x L 0 T =
      n ^ T := by
  unfold workerCapMass
  have hfun :
      (workerCapWeight next designated penalty x L 0) =
        (fun _ : List (Fin n) => 1) := by
    funext w
    cases w with
    | nil => simp [workerCapWeight]
    | cons e w => simp [workerCapWeight]
  rw [hfun, constantWordMass, Nat.mul_one]

/-- Integer exponential-moment estimate, uniform in the horizon T,
the observer x, and all later adapted designations. -/
theorem adaptedWorkerPenaltyMoment {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop)
    (hdisj : ∀ x, ¬ penalty x (designated x))
    (hcap : ∀ x, (List.ofFn (fun e : Fin n =>
      if penalty x e then 1 else 0)).sum ≤ 2)
    (x : S) (L m T : Nat) :
    workerCapMass next designated penalty x L m T ≤
      2 ^ L * 4 ^ m * n ^ T := by
  induction T generalizing x L m with
  | zero =>
      change 4 ^ m ≤ 2 ^ L * 4 ^ m * n ^ 0
      have hp : 0 < 2 ^ L :=
        Nat.pow_pos (by decide : 0 < (2 : Nat))
      have hh : 1 ≤ 2 ^ L := by omega
      have hs : 4 ^ m ≤ 2 ^ L * 4 ^ m := by
        simpa only [Nat.one_mul] using
          Nat.mul_le_mul_right (4 ^ m) hh
      simpa only [Nat.pow_zero, Nat.mul_one] using hs
  | succ T ih =>
      cases L with
      | zero =>
          rw [workerCapMassZeroService]
          simp only [Nat.pow_zero, Nat.one_mul]
          exact Nat.le_of_eq (Nat.mul_comm _ _)
      | succ L =>
          cases m with
          | zero =>
              rw [workerCapMassZeroPenalty]
              have hp : 0 < 2 ^ (L + 1) :=
                Nat.pow_pos (by decide : 0 < (2 : Nat))
              have hh : 1 ≤ 2 ^ (L + 1) := by omega
              have hs : n ^ (T + 1) ≤
                  2 ^ (L + 1) * n ^ (T + 1) := by
                simpa only [Nat.one_mul] using
                  Nat.mul_le_mul_right (n ^ (T + 1)) hh
              simpa only [Nat.pow_zero, Nat.mul_one] using hs
          | succ m =>
              have hrow (e : Fin n) :
                  Counter.resetColdWordSum n T
                    (fun w => workerCapWeight next designated penalty
                      x (L + 1) (m + 1) (e :: w)) ≤
                  (2 * (2 ^ L * 4 ^ m * n ^ T)) *
                    (if e = designated x then 2
                     else if penalty x e then 5 else 4) := by
                by_cases hd : e = designated x
                · have hchild :
                      Counter.resetColdWordSum n T
                        (fun w => workerCapWeight next designated penalty
                          x (L + 1) (m + 1) (e :: w)) =
                      workerCapMass next designated penalty
                        (next x e) L (m + 1) T := by
                    unfold workerCapMass
                    apply congrArg (fun f : List (Fin n) → Nat =>
                      Counter.resetColdWordSum n T f)
                    funext w
                    simp [workerCapWeight, hd]
                  rw [hchild]
                  simp only [if_pos hd]
                  calc
                    workerCapMass next designated penalty
                        (next x e) L (m + 1) T ≤
                        2 ^ L * 4 ^ (m + 1) * n ^ T :=
                      ih (next x e) L (m + 1)
                    _ = (2 * (2 ^ L * 4 ^ m * n ^ T)) * 2 := by
                      rw [Nat.pow_succ, Nat.mul_comm 2 (2 ^ L * 4 ^ m * n ^ T),
                        Nat.mul_assoc (2 ^ L * 4 ^ m * n ^ T) 2 2,
                        show (2 : Nat) * 2 = 4 from rfl]
                      ac_rfl
                · by_cases hp : penalty x e
                  · have hchild :
                        Counter.resetColdWordSum n T
                          (fun w => workerCapWeight next designated penalty
                            x (L + 1) (m + 1) (e :: w)) =
                        5 * workerCapMass next designated penalty
                          (next x e) (L + 1) m T := by
                      unfold workerCapMass
                      have hfun :
                          (fun w : List (Fin n) =>
                            workerCapWeight next designated penalty
                              x (L + 1) (m + 1) (e :: w)) =
                          (fun w : List (Fin n) =>
                            5 * workerCapWeight next designated penalty
                              (next x e) (L + 1) m w) := by
                        funext w
                        simp [workerCapWeight, hd, hp]
                      rw [hfun, workerWordSumMul]
                    rw [hchild]
                    simp only [if_neg hd, if_pos hp]
                    calc
                      5 * workerCapMass next designated penalty
                          (next x e) (L + 1) m T ≤
                          5 * (2 ^ (L + 1) * 4 ^ m * n ^ T) :=
                        Nat.mul_le_mul_left 5
                          (ih (next x e) (L + 1) m)
                      _ = (2 * (2 ^ L * 4 ^ m * n ^ T)) * 5 := by
                        rw [Nat.pow_succ]
                        ac_rfl
                  · have hchild :
                        Counter.resetColdWordSum n T
                          (fun w => workerCapWeight next designated penalty
                            x (L + 1) (m + 1) (e :: w)) =
                        workerCapMass next designated penalty
                          (next x e) (L + 1) (m + 1) T := by
                      unfold workerCapMass
                      apply congrArg (fun f : List (Fin n) → Nat =>
                        Counter.resetColdWordSum n T f)
                      funext w
                      simp [workerCapWeight, hd, hp]
                    rw [hchild]
                    simp only [if_neg hd, if_neg hp]
                    calc
                      workerCapMass next designated penalty
                          (next x e) (L + 1) (m + 1) T ≤
                          2 ^ (L + 1) * 4 ^ (m + 1) * n ^ T :=
                        ih (next x e) (L + 1) (m + 1)
                      _ = (2 * (2 ^ L * 4 ^ m * n ^ T)) * 4 := by
                        rw [Nat.pow_succ, Nat.pow_succ]
                        ac_rfl
              have hc := workerCoefficientBound (designated x)
                (penalty x) (hdisj x) (hcap x)
              calc
                workerCapMass next designated penalty
                    x (L + 1) (m + 1) (T + 1) =
                    (List.ofFn (fun e : Fin n =>
                      Counter.resetColdWordSum n T
                        (fun w => workerCapWeight next designated penalty
                          x (L + 1) (m + 1) (e :: w)))).sum := rfl
                _ ≤ (List.ofFn (fun e : Fin n =>
                      (2 * (2 ^ L * 4 ^ m * n ^ T)) *
                        (if e = designated x then 2
                         else if penalty x e then 5 else 4))).sum :=
                  ofFn_sum_le _ _ hrow
                _ = (2 * (2 ^ L * 4 ^ m * n ^ T)) *
                    (List.ofFn (fun e : Fin n =>
                      if e = designated x then 2
                      else if penalty x e then 5 else 4)).sum := by
                  rw [ofFn_sum_mul_left]
                _ ≤ (2 * (2 ^ L * 4 ^ m * n ^ T)) * (4 * n) :=
                  Nat.mul_le_mul_left _ hc
                _ = 2 ^ (L + 1) * 4 ^ (m + 1) * n ^ (T + 1) := by
                  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
                  ac_rfl

/-- Any word which has seen at least m penalties before L designated
services has at least 5^m in the capped moment weight. -/
private theorem workerTailWeight {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop)
    (x : S) (L m : Nat) (w : List (Fin n))
    (hm : m ≤ workerPenaltyCount next designated penalty x L w) :
    5 ^ m ≤ workerCapWeight next designated penalty x L m w := by
  induction w generalizing x L m with
  | nil =>
      have hzero : m ≤ 0 := by
        simpa [workerPenaltyCount] using hm
      have hz : m = 0 := by omega
      subst m
      simp [workerCapWeight]
  | cons e w ih =>
      cases m with
      | zero =>
          simp [workerCapWeight]
      | succ m =>
          cases L with
          | zero =>
              have hzero : m + 1 ≤ 0 := by
                simpa [workerPenaltyCount] using hm
              omega
          | succ L =>
              by_cases hd : e = designated x
              · have hh : m + 1 ≤
                    workerPenaltyCount next designated penalty
                      (next x e) L w := by
                  simpa [workerPenaltyCount, hd] using hm
                have hi := ih (next x e) L (m + 1) hh
                simpa [workerCapWeight, hd] using hi
              · by_cases hp : penalty x e
                · have hh : m ≤
                      workerPenaltyCount next designated penalty
                        (next x e) (L + 1) w := by
                    have ht : m + 1 ≤ 1 +
                        workerPenaltyCount next designated penalty
                          (next x e) (L + 1) w := by
                      simpa [workerPenaltyCount, hd, hp] using hm
                    omega
                  have hi := ih (next x e) (L + 1) m hh
                  have hs : 5 ^ (m + 1) ≤
                      5 * workerCapWeight next designated penalty
                        (next x e) (L + 1) m w := by
                    calc
                      5 ^ (m + 1) = 5 * 5 ^ m := by
                        rw [Nat.pow_succ]
                        ac_rfl
                      _ ≤ 5 * workerCapWeight next designated penalty
                            (next x e) (L + 1) m w :=
                        Nat.mul_le_mul_left 5 hi
                  simpa [workerCapWeight, hd, hp] using hs
                · have hh : m + 1 ≤
                      workerPenaltyCount next designated penalty
                        (next x e) (L + 1) w := by
                    simpa [workerPenaltyCount, hd, hp] using hm
                  have hi := ih (next x e) (L + 1) (m + 1) hh
                  simpa [workerCapWeight, hd, hp] using hi

/-- Discrete exponential Markov inequality on actual Fin n words.
The count is unnormalized and no clock independence is assumed. -/
theorem adaptedWorkerPenaltyTail {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop)
    (hdisj : ∀ x, ¬ penalty x (designated x))
    (hcap : ∀ x, (List.ofFn (fun e : Fin n =>
      if penalty x e then 1 else 0)).sum ≤ 2)
    (x : S) (L m T : Nat) :
    5 ^ m * workerPenaltyTailMass
        next designated penalty x L m T ≤
      2 ^ L * 4 ^ m * n ^ T := by
  calc
    5 ^ m * workerPenaltyTailMass
        next designated penalty x L m T =
        Counter.resetColdWordSum n T (fun w =>
          5 ^ m *
            (if m ≤ workerPenaltyCount next designated penalty x L w
             then 1 else 0)) := by
      unfold workerPenaltyTailMass
      exact (workerWordSumMul T (5 ^ m)
        (fun w => if m ≤ workerPenaltyCount
          next designated penalty x L w then 1 else 0)).symm
    _ ≤ Counter.resetColdWordSum n T
          (workerCapWeight next designated penalty x L m) := by
      apply workerWordSumMono
      intro w
      by_cases hb : m ≤ workerPenaltyCount
          next designated penalty x L w
      · simp only [if_pos hb, Nat.mul_one]
        exact workerTailWeight next designated penalty x L m w hb
      · simp only [if_neg hb, Nat.mul_zero]
        exact Nat.zero_le _
    _ = workerCapMass next designated penalty x L m T := rfl
    _ ≤ 2 ^ L * 4 ^ m * n ^ T :=
      adaptedWorkerPenaltyMoment next designated penalty
        hdisj hcap x L m T

/-- The paper's watchdog service count and lease slack. -/
theorem workerLambdaSlack (b : Nat) :
    13 * (b + 2) - (2 * b + 2) = 11 * b + 24 := by
  omega

/-- C.1 with exactly the numerator and denominator definitions
already consumed by privateWorkerTimeoutUnion. -/
theorem adaptedWorkerTimeoutNumerator {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop)
    (hdisj : ∀ x, ¬ penalty x (designated x))
    (hcap : ∀ x, (List.ofFn (fun e : Fin n =>
      if penalty x e then 1 else 0)).sum ≤ 2)
    (x : S) (b T : Nat) :
    workerTimeoutDenominator b *
        workerPenaltyTailMass next designated penalty
          x (2 * b + 2) (11 * b + 24) T ≤
      workerTimeoutNumerator b * n ^ T := by
  exact adaptedWorkerPenaltyTail next designated penalty
    hdisj hcap x (2 * b + 2) (11 * b + 24) T

/-- The same estimate with m written literally as Lambda - L. -/
theorem adaptedWorkerTimeoutAtLambda {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop)
    (hdisj : ∀ x, ¬ penalty x (designated x))
    (hcap : ∀ x, (List.ofFn (fun e : Fin n =>
      if penalty x e then 1 else 0)).sum ≤ 2)
    (x : S) (b T : Nat) :
    workerTimeoutDenominator b *
        workerPenaltyTailMass next designated penalty x
          (2 * b + 2) (13 * (b + 2) - (2 * b + 2)) T ≤
      workerTimeoutNumerator b * n ^ T := by
  rw [workerLambdaSlack]
  exact adaptedWorkerTimeoutNumerator next designated penalty
    hdisj hcap x b T

end L3.CounterTrialLower

/-!
Physical RESET-worker watchdog from the actual BANK comparison.

Only the waitLoss exit is counted; defect, grant, and RETURN(1)
success are distinct absorbing exits. Origins are certified physical
RESET launches stored after their actual scheduler edge, with no
independent worker tape. The sharp bound below uses the existing
physical BANK race potential. The pathwise equality between spent
lease and workerPenaltyCount is not asserted here.
-/

namespace L3.CounterTrialLower

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- A cyclic ring's right-neighbor operation is injective. -/
private theorem privateWorkerSuccMod {n : Nat}
    (ring : DirectedRing n) (a : Fin n) :
    (a.val + 1) % n =
      (if a.val + 1 = n then 0 else a.val + 1) := by
  by_cases h : a.val + 1 = n
  · rw [h]
    simp
  · have hlt : a.val + 1 < n := by
      have ha := a.isLt
      omega
    rw [Nat.mod_eq_of_lt hlt]
    simp [h]

private theorem privateWorkerRightNeighborInjective {n : Nat}
    (ring : DirectedRing n) (a b : Fin n)
    (h : ring.rightNeighbor a = ring.rightNeighbor b) : a = b := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (a.val + 1) % n = (b.val + 1) % n at hv
  rw [privateWorkerSuccMod ring a, privateWorkerSuccMod ring b] at hv
  split at hv <;> split at hv <;> omega

private theorem privateWorkerIncomingUnique {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (h : ring.rightNeighbor e = root) :
    e = Counter.site ring root (n - 1) := by
  exact privateWorkerRightNeighborInjective ring e
    (Counter.site ring root (n - 1))
    (h.trans (Counter.resetColdLastSiteIncoming ring root).symm)

/-- Any subset of two nominated scheduler letters has size at most two,
whether or not the two names are distinct. -/
private theorem privateWorkerTwoPortCap {n : Nat}
    (a b : Fin n) (P : Fin n → Prop)
    (hP : ∀ e, P e → e = a ∨ e = b) :
    (List.ofFn (fun e : Fin n => if P e then 1 else 0)).sum ≤ 2 := by
  have hpoint (e : Fin n) :
      (if P e then 1 else 0) ≤
        (if e = a then 1 else 0) +
          (if e = b then 1 else 0) := by
    by_cases hp : P e
    · simp only [if_pos hp]
      rcases hP e hp with ha | hb
      · subst e
        simp
      · subst e
        simp
    · simp only [if_neg hp]
      exact Nat.zero_le _
  calc
    (List.ofFn (fun e : Fin n => if P e then 1 else 0)).sum ≤
        (List.ofFn (fun e : Fin n =>
          (if e = a then 1 else 0) +
            (if e = b then 1 else 0))).sum :=
      ofFn_sum_le _ _ hpoint
    _ = 1 + 1 := by
      rw [ofFn_sum_add, workerSpikeMass a 1, workerSpikeMass b 1]
    _ = 2 := rfl

/-- The next productive reset-front service, at the physical BANK
comparison's current authenticated phase. -/
noncomputable def privateResetDesignated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankComparisonState q n) : Fin n :=
  Counter.resetClockNominated ring root (compileAdvice q).b x.1.2

/-- Root-incident lease-spending services which are not the current
designated productive service. This is defined also at absorbing cuts. -/
def privateResetPenalty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankComparisonState q n)
    (e : Fin n) : Prop :=
  (e = root ∨ ring.rightNeighbor e = root) ∧
    e ≠ privateResetDesignated ring root x

theorem privateResetPenaltyDisjoint {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ x : Counter.ResetClockBankComparisonState q n,
      ¬ privateResetPenalty ring root x
        (privateResetDesignated ring root x) := by
  intro x hp
  exact hp.2 rfl

theorem privateResetPenaltyCardinality {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ x : Counter.ResetClockBankComparisonState q n,
      (List.ofFn (fun e : Fin n =>
        if privateResetPenalty ring root x e then 1 else 0)).sum ≤ 2 := by
  intro x
  exact privateWorkerTwoPortCap
    root (Counter.site ring root (n - 1))
    (privateResetPenalty ring root x)
    (fun e hp => by
      rcases hp.1 with he | he
      · exact Or.inl he
      · exact Or.inr
          (privateWorkerIncomingUnique ring root e he))

/-- The earlier exponential-moment bound, with the observer's
actual physical comparison transition and the current nominated
and two root-incident edges. -/
theorem privateResetAdaptedPenaltyTail {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankComparisonState q n)
    (T : Nat) :
    workerTimeoutDenominator (compileAdvice q).b *
      workerPenaltyTailMass
        (Counter.resetClockBankComparisonNext ring root)
        (privateResetDesignated ring root)
        (privateResetPenalty ring root)
        x (2 * (compileAdvice q).b + 2)
          (11 * (compileAdvice q).b + 24) T ≤
      workerTimeoutNumerator (compileAdvice q).b * n ^ T := by
  exact adaptedWorkerTimeoutNumerator
    (Counter.resetClockBankComparisonNext ring root)
    (privateResetDesignated ring root)
    (privateResetPenalty ring root)
    (privateResetPenaltyDisjoint ring root)
    (privateResetPenaltyCardinality ring root)
    x (compileAdvice q).b T

/-- Numerator/denominator ratio for the initial physical BANK
race potential at a full-lease reset launch. -/
private theorem privateWorkerRawRaceBound
    (L d rank : Nat) (hr : rank ≤ L) :
    5 ^ d *
      Counter.resetClockRawRaceWeight L (L + d) rank (L + d) ≤
      (2 ^ L * 4 ^ d) * (2 ^ L * 5 ^ (L + d)) := by
  have hpow : 2 ^ (L - rank) ≤ 5 ^ (L - rank) :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 5) (L - rank)
  have hf : 5 ^ L = 5 ^ rank * 5 ^ (L - rank) := by
    have hh : rank + (L - rank) = L := by omega
    calc
      5 ^ L = 5 ^ (rank + (L - rank)) := by rw [hh]
      _ = 5 ^ rank * 5 ^ (L - rank) := by rw [Nat.pow_add]
  have hraw :
      Counter.resetClockRawRaceWeight L (L + d) rank (L + d) =
        5 ^ rank * 4 ^ (L + d) * 2 ^ (L - rank) := by
    simp [Counter.resetClockRawRaceWeight]
  have hmono :
      Counter.resetClockRawRaceWeight L (L + d) rank (L + d) ≤
        5 ^ L * 4 ^ (L + d) := by
    rw [hraw]
    calc
      5 ^ rank * 4 ^ (L + d) * 2 ^ (L - rank) ≤
          5 ^ rank * 4 ^ (L + d) * 5 ^ (L - rank) :=
        Nat.mul_le_mul_left _ hpow
      _ = 5 ^ L * 4 ^ (L + d) := by rw [hf]; ac_rfl
  have hfour : 4 ^ L = 2 ^ L * 2 ^ L := by
    simpa using (Nat.mul_pow 2 2 L)
  calc
    5 ^ d *
        Counter.resetClockRawRaceWeight L (L + d) rank (L + d) ≤
      5 ^ d * (5 ^ L * 4 ^ (L + d)) :=
        Nat.mul_le_mul_left _ hmono
    _ = (2 ^ L * 4 ^ d) * (2 ^ L * 5 ^ (L + d)) := by
      simp only [Nat.pow_add, hfour]
      ac_rfl

private theorem privateWorkerScaledTransfer
    (S F N W num den : Nat)
    (hS : 0 < S)
    (hcount : S * F ≤ N * W)
    (hratio : den * W ≤ num * S) :
    den * F ≤ num * N := by
  have hm : S * (den * F) ≤ S * (num * N) := by
    calc
      S * (den * F) = den * (S * F) := by ac_rfl
      _ ≤ den * (N * W) := Nat.mul_le_mul_left den hcount
      _ = N * (den * W) := by ac_rfl
      _ ≤ N * (num * S) := Nat.mul_le_mul_left N hratio
      _ = S * (num * N) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hm hS

/-- Genuine post-RESET-launch C.1 bound for the physical BANK
comparison. waitLoss, and only waitLoss, is charged as timeout. -/
theorem privateResetLaunchSharpWatchdog {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (C : Counter.Config q n)
    (hlaunch : Counter.ResetLaunchPhysical ring C root)
    (T : Nat) :
    workerTimeoutDenominator (compileAdvice q).b *
      Counter.resetClockBankFailureCount ring root
        ((C, .outward 1), .live) T ≤
      workerTimeoutNumerator (compileAdvice q).b * n ^ T := by
  have hg := Counter.resetClockBankComparisonGoodLaunch
    ring root C hlaunch
  have hcount := Counter.resetClockBankTreeFailureBound
    ring root hsp ((C, .outward 1), .live) hg T
  rw [← Counter.resetClockBankFailureCountEqTree
    ring root ((C, .outward 1), .live) T] at hcount
  have hcap :
      (compileAdvice q).bankLeaseCap =
        (2 * (compileAdvice q).b + 2) +
          (11 * (compileAdvice q).b + 24) := by
    change 13 * ((compileAdvice q).b + 2) =
      (2 * (compileAdvice q).b + 2) +
        (11 * (compileAdvice q).b + 24)
    omega
  have hlease :
      (C root).lease.val = (compileAdvice q).bankLeaseCap := by
    change (C root).lease.val = 13 * ((compileAdvice q).b + 2)
    exact hlaunch.2.2.2.2.2.2
  have hrank :
      2 * (compileAdvice q).b - 1 ≤
        2 * (compileAdvice q).b + 2 := by omega
  have hweight :
      Counter.resetClockBankRaceWeight ring root
          ((C, .outward 1), .live) =
      Counter.resetClockRawRaceWeight
        (2 * (compileAdvice q).b + 2)
        ((2 * (compileAdvice q).b + 2) +
          (11 * (compileAdvice q).b + 24))
        (2 * (compileAdvice q).b - 1)
        ((2 * (compileAdvice q).b + 2) +
          (11 * (compileAdvice q).b + 24)) := by
    have hh := Counter.resetClockRaceWeightLiveRaw
      ring root ((C, .outward 1), .live) rfl
    simpa only [Counter.resetClockRank, hlease, hcap] using hh
  have hraw := privateWorkerRawRaceBound
    (2 * (compileAdvice q).b + 2)
    (11 * (compileAdvice q).b + 24)
    (2 * (compileAdvice q).b - 1) hrank
  have hratio :
      workerTimeoutDenominator (compileAdvice q).b *
        Counter.resetClockBankRaceWeight ring root
          ((C, .outward 1), .live) ≤
      workerTimeoutNumerator (compileAdvice q).b *
        Counter.resetClockBankRaceScale q := by
    unfold workerTimeoutNumerator workerTimeoutDenominator
    rw [hweight]
    simpa only [Counter.resetClockBankRaceScale, hcap] using hraw
  have hscale : 0 < Counter.resetClockBankRaceScale q := by
    unfold Counter.resetClockBankRaceScale
    exact Nat.mul_pos (Nat.pow_pos (by decide))
      (Nat.pow_pos (by decide))
  exact privateWorkerScaledTransfer
    (Counter.resetClockBankRaceScale q)
    (Counter.resetClockBankFailureCount ring root
      ((C, .outward 1), .live) T)
    (n ^ T)
    (Counter.resetClockBankRaceWeight ring root
      ((C, .outward 1), .live))
    (workerTimeoutNumerator (compileAdvice q).b)
    (workerTimeoutDenominator (compileAdvice q).b)
    hscale hcount hratio

private theorem privateWorkerComparisonWordAbsorbing {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankComparisonState q n)
    (hx : x.2 ≠ .live) (w : List (Fin n)) :
    Counter.resetClockBankComparisonWord ring root w x = x := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      change Counter.resetClockBankComparisonWord ring root w
        (Counter.resetClockBankComparisonNext ring root x e) = x
      rw [Counter.resetClockBankComparisonExitAbsorbing ring root e x hx]
      exact ih

/-- Exact finite-word correspondence between literal waitLoss
and the existing physical BANK failure-count recursion. -/
private theorem privateWorkerComparisonFailureMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (x : Counter.ResetClockBankComparisonState q n) (T : Nat),
      Counter.resetColdWordSum n T (fun w =>
        if (Counter.resetClockBankComparisonWord
          ring root w x).2 = .waitLoss then 1 else 0) =
      Counter.resetClockBankFailureCount ring root x T := by
  intro x T
  induction T generalizing x with
  | zero =>
      rfl
  | succ T ih =>
      by_cases hl : x.2 = .live
      · change
          (List.ofFn (fun e : Fin n =>
            Counter.resetColdWordSum n T (fun w =>
              if (Counter.resetClockBankComparisonWord ring root w
                  (Counter.resetClockBankComparisonNext ring root x e)).2 =
                .waitLoss then 1 else 0))).sum =
          (if x.2 = .live then
            (List.ofFn (fun e : Fin n =>
              Counter.resetClockBankFailureCount ring root
                (Counter.resetClockBankComparisonNext ring root x e) T)).sum
           else if x.2 = .waitLoss then n ^ (T + 1) else 0)
        rw [if_pos hl]
        exact ofFn_sum_eq _ _ (fun e =>
          ih (Counter.resetClockBankComparisonNext ring root x e))
      · by_cases hw : x.2 = .waitLoss
        · have hfun :
              (fun w : List (Fin n) =>
                if (Counter.resetClockBankComparisonWord
                    ring root w x).2 = .waitLoss then 1 else 0) =
                (fun _ => 1) := by
            funext w
            rw [privateWorkerComparisonWordAbsorbing ring root x hl w]
            simp [hw]
          calc
            Counter.resetColdWordSum n (T + 1) (fun w =>
                if (Counter.resetClockBankComparisonWord
                    ring root w x).2 = .waitLoss then 1 else 0) =
              Counter.resetColdWordSum n (T + 1) (fun _ => 1) := by
                rw [hfun]
            _ = n ^ (T + 1) := by
              rw [constantWordMass]
              simp
            _ = Counter.resetClockBankFailureCount
                  ring root x (T + 1) :=
              (Counter.resetClockBankFailureCountWaitLoss
                ring root x hw (T + 1)).symm
        · have hfun :
              (fun w : List (Fin n) =>
                if (Counter.resetClockBankComparisonWord
                    ring root w x).2 = .waitLoss then 1 else 0) =
                (fun _ => 0) := by
            funext w
            rw [privateWorkerComparisonWordAbsorbing ring root x hl w]
            simp [hw]
          calc
            Counter.resetColdWordSum n (T + 1) (fun w =>
                if (Counter.resetClockBankComparisonWord
                    ring root w x).2 = .waitLoss then 1 else 0) =
              Counter.resetColdWordSum n (T + 1) (fun _ => 0) := by
                rw [hfun]
            _ = 0 := by
              rw [constantWordMass]
              simp
            _ = Counter.resetClockBankFailureCount
                  ring root x (T + 1) :=
              (Counter.resetClockBankFailureCountOtherExit
                ring root x hl hw (T + 1)).symm

/-- Both scheduler word-sum interfaces count the same IID Fin n words. -/
private theorem privateWorkerScheduleSum {n : Nat}
    (T : Nat) (f : List (Fin n) → Nat) :
    L3.Prob.scheduleSum n T f =
      Counter.resetColdWordSum n T f := by
  induction T generalizing f with
  | zero =>
      simp [L3.Prob.scheduleSum,
        FixedSpanRenewalPayload.wordSum, allSchedules,
        Counter.resetColdWordSum]
  | succ T ih =>
      change FixedSpanRenewalPayload.wordSum n (T + 1) f =
        Counter.resetColdWordSum n (T + 1) f
      rw [FixedSpanRenewalPayload.wordSum_succ]
      change
        (List.ofFn (fun e : Fin n =>
          FixedSpanRenewalPayload.wordSum n T
            (fun w => f (e :: w)))).sum =
        (List.ofFn (fun e : Fin n =>
          Counter.resetColdWordSum n T
            (fun w => f (e :: w)))).sum
      exact ofFn_sum_eq _ _ (fun e => ih (fun w => f (e :: w)))

/-- The postservice physical state and genuine-launch witness
for each worker origin. -/
abbrev PrivateResetWorkerOrigin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  { C : Counter.Config q n //
    (compileAdvice q).useSmall = false ∧
      Counter.ResetLaunchPhysical ring C root }

/-- A certified actual RESET -> RWAIT launch creates one origin.
No origins are emitted after the private observer stops. -/
noncomputable def privateResetWorkerStarts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : Counter.ResetColdLatchedPrivateState q n)
    (e : Fin n) : List (PrivateResetWorkerOrigin (q := q) ring root) :=
  if Counter.resetColdLatchedPrivateTerminal z then []
  else if h :
      e = root ∧
        ((Counter.resetColdLatchedPrivateConfig z) root).mode = .RESET ∧
        (compileAdvice q).useSmall = false ∧
        Counter.ResetLaunchPhysical ring
          ((protocol q).step ring
            (Counter.resetColdLatchedPrivateConfig z) e) root then
    [⟨(protocol q).step ring
        (Counter.resetColdLatchedPrivateConfig z) e,
      ⟨h.2.2.1, h.2.2.2⟩⟩]
  else []

/-- Timeout is only the role-stable physical comparison's waitLoss.
Every LIVE comparison letter is the actual physical scheduler step. -/
noncomputable def privateResetWorkerTimeout {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : PrivateResetWorkerOrigin (q := q) ring root)
    (w : List (Fin n)) : Bool :=
  if (Counter.resetClockBankComparisonWord ring root w
       ((o.val, .outward 1), .live)).2 = .waitLoss
  then true else false

private theorem privateResetWorkerTimeoutMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : PrivateResetWorkerOrigin (q := q) ring root)
    (T : Nat) :
    L3.Prob.scheduleSum n T
      (fun w => L3.Prob.indicator
        (privateResetWorkerTimeout ring root o w)) =
      Counter.resetClockBankFailureCount ring root
        ((o.val, .outward 1), .live) T := by
  calc
    L3.Prob.scheduleSum n T
        (fun w => L3.Prob.indicator
          (privateResetWorkerTimeout ring root o w)) =
      Counter.resetColdWordSum n T
        (fun w => L3.Prob.indicator
          (privateResetWorkerTimeout ring root o w)) :=
        privateWorkerScheduleSum T _
    _ = Counter.resetColdWordSum n T (fun w =>
          if (Counter.resetClockBankComparisonWord ring root w
            ((o.val, .outward 1), .live)).2 = .waitLoss
          then 1 else 0) := by
      apply congrArg (fun f : List (Fin n) → Nat =>
        Counter.resetColdWordSum n T f)
      funext w
      by_cases hw :
          (Counter.resetClockBankComparisonWord ring root w
            ((o.val, .outward 1), .live)).2 = .waitLoss
      · simp [L3.Prob.indicator, privateResetWorkerTimeout, hw]
      · simp [L3.Prob.indicator, privateResetWorkerTimeout, hw]
    _ = Counter.resetClockBankFailureCount ring root
          ((o.val, .outward 1), .live) T :=
      privateWorkerComparisonFailureMass ring root
        ((o.val, .outward 1), .live) T

/-- The named rarity premise for *all* certified actual
RESET worker origins. Its suffix uses the same original IID tape,
and no future-conditioned origin selection is required. -/
theorem privateResetWorkerWatchdog {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    PrivateCleanWorkerWatchdog (q := q) ring root
      (privateResetWorkerStarts (q := q) ring root)
      (privateResetWorkerTimeout (q := q) ring root) := by
  intro z hz e o ho T
  change workerTimeoutDenominator (compileAdvice q).b *
      L3.Prob.scheduleSum n T
        (fun w => L3.Prob.indicator
          (privateResetWorkerTimeout ring root o w)) ≤
      workerTimeoutNumerator (compileAdvice q).b * n ^ T
  rw [privateResetWorkerTimeoutMass ring root o T]
  exact privateResetLaunchSharpWatchdog ring root
    o.property.1 o.val o.property.2 T

end L3.CounterTrialLower

/-!
The two non-reset BANK worker origins and the three-kind
origin interface.

The source's existing resetClockBankTreeFailureBound is proved for
RWAIT/reset fronts, not for the IWAIT increment or CWAIT comparator.
Consequently the two non-reset C.1 rarity statements below remain
named Props, and the all-kind rarity and union theorems explicitly
take those Props as hypotheses. The all-word 2K+1 start cap is also
an explicit hypothesis, not a fabricated physical theorem.

The IWAIT and CWAIT observers below execute the actual protocol on
each live edge. Their exits distinguish a matching return, a new
grant, a supported PACK defect, and root-incident lease exhaustion.
In particular the CWAIT/CL1 return is not counted as a watchdog
timeout even though it may put the physical root into RESET.
-/

namespace L3.CounterTrialLower

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- Literal ARMED/IR launch: the fresh IWAIT lease is Lambda.
This is a BANK row on the same physical protocol, not a new step. -/
private theorem privateIncrementLeaseLaunchRow
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = true)
    (hb : 1 ≤ b) :
    (bankPair x y 1 b theta).1.lease = 13 * (b + 2) := by
  simp [bankPair, hr, hg, hy, hm, ht, hbit, hb, isRetTok]

/-- Literal CSTART/CR launch: the fresh CWAIT lease is Lambda.
The existing comparator-row theorem supplies the matching CR token. -/
private theorem privateComparatorLeaseLaunchRow
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .CSTART)
    (ht : y.tok = .E) (hb : 1 ≤ b) :
    (bankPair x y 1 b theta).1.lease = 13 * (b + 2) := by
  simp [bankPair, hr, hg, hy, hm, ht, hb, isRetTok, isWaitMode]

/-- Physical postservice certificate for an ARMED -> IWAIT carry.
The letter that launches it has already been consumed. -/
def PrivateIncrementLaunchCertified {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Prop :=
  (compileAdvice q).useSmall = false ∧
    Counter.Complete ring C root ∧
    Counter.GrantFree C root ∧
    (C root).mode = .IWAIT ∧
    (C root).lease.val = (compileAdvice q).bankLeaseCap ∧
    (C (Counter.site ring root 1)).tok = .IR

/-- Physical postservice certificate for a CSTART -> CWAIT
comparator. The initial token is either CR0 or CR1. -/
def PrivateComparatorLaunchCertified {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Prop :=
  (compileAdvice q).useSmall = false ∧
    Counter.Complete ring C root ∧
    Counter.GrantFree C root ∧
    (C root).mode = .CWAIT ∧
    (C root).lease.val = (compileAdvice q).bankLeaseCap ∧
    ((C (Counter.site ring root 1)).tok = .CR0 ∨
      (C (Counter.site ring root 1)).tok = .CR1)

abbrev PrivateIncrementWorkerOrigin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  { C : Counter.Config q n //
      PrivateIncrementLaunchCertified ring root C }

abbrev PrivateComparatorWorkerOrigin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  { C : Counter.Config q n //
      PrivateComparatorLaunchCertified ring root C }

/-- A certified actual outgoing ARMED service emits one increment
origin. Recovery and absorbing observer states emit nothing. -/
noncomputable def privateIncrementWorkerStarts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Counter.ResetColdLatchedPrivateState q n → Fin n →
      List (PrivateIncrementWorkerOrigin (q := q) ring root)
  | .live C _, e =>
      if h : e = root ∧ (C root).mode = .ARMED ∧
          PrivateIncrementLaunchCertified ring root
            ((protocol q).step ring C e) then
        [⟨(protocol q).step ring C e, h.2.2⟩]
      else []
  | _, _ => []

/-- A certified actual outgoing CSTART service emits one
comparator origin. The launch post-state, not the old state,
is stored for all future scheduler-suffix tests. -/
noncomputable def privateComparatorWorkerStarts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Counter.ResetColdLatchedPrivateState q n → Fin n →
      List (PrivateComparatorWorkerOrigin (q := q) ring root)
  | .live C _, e =>
      if h : e = root ∧ (C root).mode = .CSTART ∧
          PrivateComparatorLaunchCertified ring root
            ((protocol q).step ring C e) then
        [⟨(protocol q).step ring C e, h.2.2⟩]
      else []
  | _, _ => []

/-- A non-reset worker comparison has a real physical configuration
and an absorbing outcome label. No independent scheduler is supplied. -/
inductive PrivateWaitingExit where
  | live
  | completed
  | waitLoss
  | grant
  | defect
  | aborted
  deriving DecidableEq

abbrev PrivateWaitingState (q n : Nat) :=
  Counter.Config q n × PrivateWaitingExit

/-- Matching returning tokens. CL1 is a completed comparator, not
a failure, even when its root transition enters RESET. -/
def privateIncrementReturnToken (t : BTok) : Prop := t = .AL

def privateComparatorReturnToken (t : BTok) : Prop :=
  t = .CL0 ∨ t = .CL1

/-- Priority is defect, matching worker return, new grant,
a previously lost waiting mode, exhausted incident lease, and
otherwise continuation or abort. Each test reads the real OLD
state or the actual physical protocol successor. -/
noncomputable def privateWaitingOutcome {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (waitingMode : Mode) (returnToken : BTok → Prop)
    (C : Counter.Config q n) (e : Fin n) :
    PrivateWaitingExit :=
  if Counter.ResetClockBankDefectEntry ring C root e then .defect
  else if e = root ∧
      returnToken (C (Counter.site ring root 1)).tok then .completed
  else if ¬ Counter.GrantFree ((protocol q).step ring C e) root then .grant
  else if (C root).mode ≠ waitingMode then .aborted
  else if (e = root ∨ ring.rightNeighbor e = root) ∧
      (C root).lease.val = 1 then .waitLoss
  else if (((protocol q).step ring C e) root).mode = waitingMode
    then .live
  else .aborted

/-- The full Cartesian physical state follows Protocol.step
on every nonterminal comparison letter. -/
noncomputable def privateWaitingNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (waitingMode : Mode) (returnToken : BTok → Prop) :
    PrivateWaitingState q n → Fin n → PrivateWaitingState q n
  | (C, .live), e =>
      ((protocol q).step ring C e,
        privateWaitingOutcome ring root waitingMode returnToken C e)
  | z, _ => z

theorem privateWaitingNextPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (waitingMode : Mode) (returnToken : BTok → Prop)
    (C : Counter.Config q n) (e : Fin n) :
    (privateWaitingNext ring root waitingMode returnToken
      (C, .live) e).1 = (protocol q).step ring C e := rfl

/-- The matching return takes precedence over a lease-one
RESET, especially in the comparator CL1 case. -/
theorem privateWaitingReturnPriority {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (waitingMode : Mode) (returnToken : BTok → Prop)
    (C : Counter.Config q n) (e : Fin n)
    (hdef : ¬ Counter.ResetClockBankDefectEntry ring C root e)
    (hret : e = root ∧
      returnToken (C (Counter.site ring root 1)).tok) :
    privateWaitingOutcome ring root waitingMode returnToken C e =
      .completed := by
  simp only [privateWaitingOutcome, if_neg hdef, if_pos hret]

/-- Finite suffix on the original edge alphabet. The comparison
stops changing at the first nonlive outcome. -/
noncomputable def privateWaitingWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (waitingMode : Mode) (returnToken : BTok → Prop) :
    List (Fin n) → PrivateWaitingState q n → PrivateWaitingState q n
  | [], z => z
  | e :: w, z =>
      privateWaitingWord ring root waitingMode returnToken w
        (privateWaitingNext ring root waitingMode returnToken z e)

/-- Only a genuine waitLoss of the increment comparison counts. -/
noncomputable def privateIncrementWorkerTimeout {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : PrivateIncrementWorkerOrigin (q := q) ring root)
    (w : List (Fin n)) : Bool :=
  if (privateWaitingWord ring root .IWAIT
      privateIncrementReturnToken w (o.val, .live)).2 = .waitLoss
    then true else false

/-- Only a genuine waitLoss of the comparator comparison counts. -/
noncomputable def privateComparatorWorkerTimeout {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : PrivateComparatorWorkerOrigin (q := q) ring root)
    (w : List (Fin n)) : Bool :=
  if (privateWaitingWord ring root .CWAIT
      privateComparatorReturnToken w (o.val, .live)).2 = .waitLoss
    then true else false

/-- Exact C.1 for the physical IWAIT comparison is the first missing
non-reset race-drift obligation. No proof is asserted here. -/
def PrivateIncrementWorkerRarity {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (o : PrivateIncrementWorkerOrigin (q := q) ring root) (T : Nat),
    workerTimeoutDenominator (compileAdvice q).b *
      L3.Prob.scheduleSum n T (fun w =>
        L3.Prob.indicator (privateIncrementWorkerTimeout ring root o w)) ≤
      workerTimeoutNumerator (compileAdvice q).b * n ^ T

/-- Exact C.1 for the physical CWAIT comparison is the second
missing non-reset race-drift obligation. -/
def PrivateComparatorWorkerRarity {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (o : PrivateComparatorWorkerOrigin (q := q) ring root) (T : Nat),
    workerTimeoutDenominator (compileAdvice q).b *
      L3.Prob.scheduleSum n T (fun w =>
        L3.Prob.indicator (privateComparatorWorkerTimeout ring root o w)) ≤
      workerTimeoutNumerator (compileAdvice q).b * n ^ T

/-- Disjoint tagged origins from the three physical launch types. -/
inductive PrivateTrialWorkerOrigin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) where
  | reset : PrivateResetWorkerOrigin (q := q) ring root →
      PrivateTrialWorkerOrigin ring root
  | increment : PrivateIncrementWorkerOrigin (q := q) ring root →
      PrivateTrialWorkerOrigin ring root
  | comparator : PrivateComparatorWorkerOrigin (q := q) ring root →
      PrivateTrialWorkerOrigin ring root

/-- This is a SINGLE actual-observer starts function. The C.4
all-head-trial accounting is restricted to LIVE phases; the
observer's RECOVERY phase is not an all-head continuation.
Every origin carries the physical post-service snapshot. -/
noncomputable def privateTrialWorkerStarts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Counter.ResetColdLatchedPrivateState q n → Fin n →
      List (PrivateTrialWorkerOrigin (q := q) ring root)
  | .live C started, e =>
      ((privateResetWorkerStarts (q := q) ring root
          (.live C started) e).map
        (fun o => PrivateTrialWorkerOrigin.reset o)) ++
      ((privateIncrementWorkerStarts (q := q) ring root
          (.live C started) e).map
        (fun o => PrivateTrialWorkerOrigin.increment o)) ++
      ((privateComparatorWorkerStarts (q := q) ring root
          (.live C started) e).map
        (fun o => PrivateTrialWorkerOrigin.comparator o))
  | _, _ => []

/-- The single timeout classifier retains the worker kind. -/
noncomputable def privateTrialWorkerTimeout {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    PrivateTrialWorkerOrigin (q := q) ring root →
      List (Fin n) → Bool
  | .reset o, w => privateResetWorkerTimeout ring root o w
  | .increment o, w => privateIncrementWorkerTimeout ring root o w
  | .comparator o, w => privateComparatorWorkerTimeout ring root o w

/-- Combine the RESET C.1 with exactly the two outstanding
IWAIT and CWAIT rarity premises. The union needs no independence
or extra scheduler and works at every adapted LIVE start. -/
theorem privateTrialWorkerWatchdogOfRarities {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hi : PrivateIncrementWorkerRarity (q := q) ring root)
    (hc : PrivateComparatorWorkerRarity (q := q) ring root) :
    PrivateCleanWorkerWatchdog (q := q) ring root
      (privateTrialWorkerStarts (q := q) ring root)
      (privateTrialWorkerTimeout (q := q) ring root) := by
  intro z hz e o ho T
  cases z with
  | live C started =>
      simp only [privateTrialWorkerStarts, List.mem_append,
        List.mem_map] at ho
      rcases ho with (hr | hiw) | hcw
      · obtain ⟨r, hmem, heq⟩ := hr
        cases heq
        have h := privateResetWorkerWatchdog (q := q) ring root
          (.live C started) hz e r hmem T
        simpa only [privateTrialWorkerTimeout] using h
      · obtain ⟨r, _, heq⟩ := hiw
        cases heq
        simpa only [privateTrialWorkerTimeout] using hi r T
      · obtain ⟨r, _, heq⟩ := hcw
        cases heq
        simpa only [privateTrialWorkerTimeout] using hc r T
  | recovery C =>
      simp [privateTrialWorkerStarts] at ho
  | success C =>
      simp [privateTrialWorkerStarts] at ho
  | failure C =>
      simp [privateTrialWorkerStarts] at ho

/-- The three-kind C.4 union, conditionally on the two currently
missing non-reset rare-event bounds and the missing wordwise
multiplicity cap. The source's original finite scheduler is used. -/
theorem privateTrialWorkerTimeoutUnionOfRarities {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hi : PrivateIncrementWorkerRarity (q := q) ring root)
    (hc : PrivateComparatorWorkerRarity (q := q) ring root)
    (hcap : PrivateCleanWorkerStartCap (q := q)
      ring root C (privateTrialWorkerStarts (q := q) ring root))
    (T : Nat) :
    workerTimeoutDenominator (compileAdvice q).b *
      privateWorkerTimeoutMass ring root C
        (privateTrialWorkerStarts (q := q) ring root)
        (privateTrialWorkerTimeout (q := q) ring root) T ≤
      workerTimeoutNumerator (compileAdvice q).b *
        (n ^ T * (2 * (compileAdvice q).K + 1)) := by
  exact privateWorkerTimeoutUnion ring root C
    (privateTrialWorkerStarts (q := q) ring root)
    (privateTrialWorkerTimeout (q := q) ring root)
    (privateTrialWorkerWatchdogOfRarities ring root hi hc)
    hcap T

/-- Once the physical IWAIT/CWAIT races and the wordwise start cap
are supplied, the original compiled 1/1024 budget closes without
any additional probabilistic assumption. -/
theorem privateTrialWorkerTimeoutTinyOfRarities {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hi : PrivateIncrementWorkerRarity (q := q) ring root)
    (hc : PrivateComparatorWorkerRarity (q := q) ring root)
    (hcap : PrivateCleanWorkerStartCap (q := q)
      ring root C (privateTrialWorkerStarts (q := q) ring root))
    (T : Nat) :
    1024 * privateWorkerTimeoutMass ring root C
        (privateTrialWorkerStarts (q := q) ring root)
        (privateTrialWorkerTimeout (q := q) ring root) T ≤
      n ^ T := by
  exact privateWorkerTimeoutTiny ring root C
    (privateTrialWorkerStarts (q := q) ring root)
    (privateTrialWorkerTimeout (q := q) ring root)
    hsp hwidth
    (privateTrialWorkerWatchdogOfRarities ring root hi hc)
    hcap T

end L3.CounterTrialLower

/-!
IWAIT certificate audit, with an actual internal collision row.

The original PrivateIncrementLaunchCertified does NOT assert
resetColdPrivateOnlyWorker at digit one. Consequently it admits an
IR at digit one alongside a CR0 at digit two. The literal BANK
priority erases both on the edge from digit one to digit two, with
no productive IR advance, and the real protocol frames the IWAIT
root's mode and lease on that interior edge.

This is the first missing premise for the claimed IWAIT race drift:
a clean isolated front, plus its closure on the actual comparison.
No proof of PrivateIncrementWorkerRarity is asserted here.
-/

namespace L3.CounterTrialLower

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- A nonincident physical edge cannot spend the root's BANK lease.
No waiting-mode or cleanliness hypotheses are needed for this frame. -/
theorem privateIncrementNonincidentLeaseFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hleft : e ≠ root)
    (hright : ring.rightNeighbor e ≠ root) :
    (((protocol q).step ring C e) root).lease.val =
      (C root).lease.val := by
  exact congrArg (fun a : Agent (compileAdvice q) => a.lease.val)
    (Counter.step_frame ring C e root (Ne.symm hleft) (Ne.symm hright))

/-- Both tokens are destroyed by the literal nonreset interior
collision rule. The ordinary IR-forward case occurs AFTER this
priority and therefore is not executed. Both bits are framed. -/
private theorem privateIncrementCollisionBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 1) (hy : y.role = 2)
    (hb : 2 < b) (htx : x.tok = .IR) (hty : y.tok = .CR0) :
    (bankPair x y 2 b theta).1.tok = .E ∧
      (bankPair x y 2 b theta).1.bit = x.bit ∧
      (bankPair x y 2 b theta).2.tok = .E ∧
      (bankPair x y 2 b theta).2.bit = y.bit := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxle : 1 ≤ x.role := by omega
  have hxlt : x.role < b := by omega
  have hyle : y.role ≤ b := by omega
  have hylink : y.role = x.role + 1 := by omega
  have hxnb : x.role ≠ b := by omega
  have hynb : y.role ≠ b := by omega
  simp [bankPair, hx, hy, hb, htx, hty, hxne, hyne,
    hxle, hxlt, hyle, hylink, hxnb, hynb, isRetTok,
    isWaitMode] <;>
    repeat (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩ | omega | split)

/-- The same two-token collision at the ACTUAL physical protocol
edge from protected digit one to protected digit two. -/
theorem privateIncrementCollisionPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hb : 2 < (compileAdvice q).b)
    (htx : (C (Counter.site ring root 1)).tok = .IR)
    (hty : (C (Counter.site ring root 2)).tok = .CR0) :
    (((protocol q).step ring C (Counter.site ring root 1))
      (Counter.site ring root 1)).tok = .E ∧
    (((protocol q).step ring C (Counter.site ring root 1))
      (Counter.site ring root 2)).tok = .E := by
  have hrow :
      (Counter.resetColdPrivateInteriorBankAt ring root C 1).1.tok =
        .E ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C 1).1.bit =
        (C (Counter.site ring root 1)).bit ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C 1).2.tok =
        .E ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C 1).2.bit =
        (C (Counter.site ring root 2)).bit := by
    change
      (bankPair (bankCell (C (Counter.site ring root 1)) 1)
        (bankCell (C (Counter.site ring root 2)) 2)
        2 (compileAdvice q).b (compileAdvice q).theta).1.tok =
          .E ∧
      (bankPair (bankCell (C (Counter.site ring root 1)) 1)
        (bankCell (C (Counter.site ring root 2)) 2)
        2 (compileAdvice q).b (compileAdvice q).theta).1.bit =
          (C (Counter.site ring root 1)).bit ∧
      (bankPair (bankCell (C (Counter.site ring root 1)) 1)
        (bankCell (C (Counter.site ring root 2)) 2)
        2 (compileAdvice q).b (compileAdvice q).theta).2.tok =
          .E ∧
      (bankPair (bankCell (C (Counter.site ring root 1)) 1)
        (bankCell (C (Counter.site ring root 2)) 2)
        2 (compileAdvice q).b (compileAdvice q).theta).2.bit =
          (C (Counter.site ring root 2)).bit
    exact privateIncrementCollisionBank
      (bankCell (C (Counter.site ring root 1)) 1)
      (bankCell (C (Counter.site ring root 2)) 2)
      (compileAdvice q).b (compileAdvice q).theta
      rfl rfl hb htx hty
  have hphysical := Counter.resetColdPrivateInteriorRowFields
    ring root C hc hsp 1 (by omega) (by omega)
    .E .E (C (Counter.site ring root 1)).bit
    (C (Counter.site ring root 2)).bit hrow
  exact ⟨hphysical.1, hphysical.2.2.1⟩

/-- Thus a postlaunch snapshot satisfying the CURRENT certificate
can lose both the designated IR and the obstructing CR0 on a
non-root-incident service, while its IWAIT mode and full BANK lease
remain untouched. In particular the selected service need not
decrease any authenticated carry-front rank. -/
theorem privateIncrementCertifiedCollision {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ho : PrivateIncrementLaunchCertified ring root C)
    (hb : 2 < (compileAdvice q).b)
    (hgarbage : (C (Counter.site ring root 2)).tok = .CR0) :
    (((protocol q).step ring C (Counter.site ring root 1))
      (Counter.site ring root 1)).tok = .E ∧
    (((protocol q).step ring C (Counter.site ring root 1))
      (Counter.site ring root 2)).tok = .E ∧
    (((protocol q).step ring C (Counter.site ring root 1))
      root).mode = .IWAIT ∧
    (((protocol q).step ring C (Counter.site ring root 1))
      root).lease.val = (compileAdvice q).bankLeaseCap := by
  obtain ⟨hsp, hcomplete, _, hmode, hlease, hfirst⟩ := ho
  have hc := privateIncrementCollisionPhysical
    ring root C hcomplete hsp hb hfirst hgarbage
  have hports := Counter.resetClockInteriorEdgeNotRootIncident
    ring C root hcomplete 1 (by omega) (by omega)
  have hframe := Counter.step_frame ring C (Counter.site ring root 1)
    root (Ne.symm hports.1) (Ne.symm hports.2)
  have hm :
      (((protocol q).step ring C (Counter.site ring root 1))
        root).mode = .IWAIT :=
    (congrArg (fun a : Agent (compileAdvice q) => a.mode)
      hframe).trans hmode
  have hl :
      (((protocol q).step ring C (Counter.site ring root 1))
        root).lease.val = (compileAdvice q).bankLeaseCap :=
    (congrArg (fun a : Agent (compileAdvice q) => a.lease.val)
      hframe).trans hlease
  exact ⟨hc.1, hc.2, hm, hl⟩

/-- If every other protected slot was empty, the very same
collision leaves the ENTIRE protected worker word empty while
the IWAIT root remains active. This is the workerless waiting
trap that the weak launch certificate fails to exclude. -/
theorem privateIncrementCollisionEmptiesWorkers {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ho : PrivateIncrementLaunchCertified ring root C)
    (hb : 2 < (compileAdvice q).b)
    (hgarbage : (C (Counter.site ring root 2)).tok = .CR0)
    (hother : ∀ i : Nat, 3 ≤ i →
      i ≤ (compileAdvice q).b →
      (C (Counter.site ring root i)).tok = .E) :
    Counter.resetColdPrivateNoWorkers ring root
      ((protocol q).step ring C (Counter.site ring root 1)) := by
  obtain ⟨hsp, hcomplete, _, _, _, hfirst⟩ := ho
  have hc := privateIncrementCollisionPhysical
    ring root C hcomplete hsp hb hfirst hgarbage
  intro i hi hib
  by_cases hone : i = 1
  · subst i
    exact hc.1
  · by_cases htwo : i = 2
    · subst i
      exact hc.2
    · rw [Counter.resetColdPrivateInteriorOtherFrame
        ring root C hcomplete 1 (by omega) (by omega)
        i hi hib hone htwo]
      exact hother i (by omega) hib

/-- An actual outgoing ARMED launch touches root and digit one;
it does not sanitize an unrelated CR0 already stored at digit two. -/
theorem privateIncrementLaunchPreservesGarbage {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hb : 2 ≤ (compileAdvice q).b)
    (hgarbage : (C (Counter.site ring root 2)).tok = .CR0) :
    (((protocol q).step ring C root)
      (Counter.site ring root 2)).tok = .CR0 := by
  rw [Counter.resetColdOutgoingRootOtherDigitsFrame
    ring C root hc 2 (by omega) hb]
  exact hgarbage

/-- Repaired origin domain: the current certificate is strengthened
with a physically UNIQUE IR front. No probability bound for this
stronger domain is claimed without the needed full-word closure. -/
def PrivateIncrementIsolatedLaunch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Prop :=
  PrivateIncrementLaunchCertified ring root C ∧
    Counter.resetColdPrivateOnlyWorker ring root C 1 .IR

/-- The missing isolation clause really excludes the concrete
two-token obstruction at digit two. -/
theorem privateIncrementIsolatedExcludesCollision {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (h : PrivateIncrementIsolatedLaunch ring root C)
    (hb : 2 ≤ (compileAdvice q).b) :
    (C (Counter.site ring root 2)).tok ≠ .CR0 := by
  have he : 2 ≠ 1 := by omega
  have ht := h.2.2.2.2 2 (by omega) hb he
  rw [ht]
  intro hx
  cases hx

/-- The compiled watchdog fraction is far smaller than the
constant-order collision-first probability in the weak domain. -/
theorem privateIncrementWatchdogNumericallyTiny (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    1024 * workerTimeoutNumerator (compileAdvice q).b <
      workerTimeoutDenominator (compileAdvice q).b := by
  have hcount :
      1 ≤ 2 ^ ((compileAdvice q).b + 1) + 1 := Nat.le_add_left 1 _
  have h := workerBudgetBelowThousandTwentyFour q 1 hsp hcount
  simpa only [Nat.mul_one] using h

end L3.CounterTrialLower

/-!
Isolated nonreset origins, conditional C.1 union, and the
remaining IWAIT top-overflow obstruction.

The new isolated origin predicates exclude simultaneous worker
collisions. They do NOT, by themselves, bound the binary head.
The exact source BANK top-source row may erase an isolated IR at
digit b. Consequently a global IWAIT rarity theorem is NOT
asserted. The bounded authenticated front and pathwise timeout
inclusion are exposed separately.
-/

namespace L3.CounterTrialLower

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- The comparator counterpart of the isolated IWAIT launch.
The stored first CR token must be the only protected worker. -/
def PrivateComparatorIsolatedLaunch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Prop :=
  PrivateComparatorLaunchCertified ring root C ∧
    ∃ t : BTok, (t = .CR0 ∨ t = .CR1) ∧
      Counter.resetColdPrivateOnlyWorker ring root C 1 t

/-- A comparator isolation certificate contains an actual matching
CR token and empties every other protected slot. -/
theorem privateComparatorIsolatedFirstToken {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (h : PrivateComparatorIsolatedLaunch ring root C) :
    ∃ t : BTok, (t = .CR0 ∨ t = .CR1) ∧
      (C (Counter.site ring root 1)).tok = t := by
  obtain ⟨t, ht, hw⟩ := h.2
  exact ⟨t, ht, hw.2.2.1⟩

theorem privateComparatorIsolatedOtherEmpty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (h : PrivateComparatorIsolatedLaunch ring root C)
    (j : Nat) (hj : 2 ≤ j)
    (hjb : j ≤ (compileAdvice q).b) :
    (C (Counter.site ring root j)).tok = .E := by
  obtain ⟨t, ht, hw⟩ := h.2
  exact hw.2.2.2 j (by omega) hjb (by omega)

/-- The new origin type exposes its original physical poststate.
The existing unisolated origin remains available for projecting
the unchanged actual waiting timeout. -/
abbrev PrivateIncrementIsolatedOrigin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  { C : Counter.Config q n //
      PrivateIncrementIsolatedLaunch ring root C }

abbrev PrivateComparatorIsolatedOrigin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  { C : Counter.Config q n //
      PrivateComparatorIsolatedLaunch ring root C }

/-- A real ARMED root service emits an IWAIT origin only when its
physical poststate has the sole protected IR worker at digit one. -/
noncomputable def privateIncrementIsolatedStarts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Counter.ResetColdLatchedPrivateState q n → Fin n →
      List (PrivateIncrementIsolatedOrigin (q := q) ring root)
  | .live C _, e =>
      if h : e = root ∧ (C root).mode = .ARMED ∧
          PrivateIncrementIsolatedLaunch ring root
            ((protocol q).step ring C e) then
        [⟨(protocol q).step ring C e, h.2.2⟩]
      else []
  | _, _ => []

/-- A real CSTART root service emits a comparator origin only
when the sole CR worker is physically certified after launch. -/
noncomputable def privateComparatorIsolatedStarts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Counter.ResetColdLatchedPrivateState q n → Fin n →
      List (PrivateComparatorIsolatedOrigin (q := q) ring root)
  | .live C _, e =>
      if h : e = root ∧ (C root).mode = .CSTART ∧
          PrivateComparatorIsolatedLaunch ring root
            ((protocol q).step ring C e) then
        [⟨(protocol q).step ring C e, h.2.2⟩]
      else []
  | _, _ => []

/-- The same physical IWAIT suffix comparison as before; the only
change is the additional isolated postlaunch certificate. -/
noncomputable def privateIncrementIsolatedTimeout {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : PrivateIncrementIsolatedOrigin (q := q) ring root)
    (w : List (Fin n)) : Bool :=
  privateIncrementWorkerTimeout ring root
    (⟨o.val, o.property.1⟩ :
      PrivateIncrementWorkerOrigin (q := q) ring root) w

/-- The same real CWAIT comparison, now restricted to an isolated
first CR worker. In particular the CL1 success priority is unchanged. -/
noncomputable def privateComparatorIsolatedTimeout {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : PrivateComparatorIsolatedOrigin (q := q) ring root)
    (w : List (Fin n)) : Bool :=
  privateComparatorWorkerTimeout ring root
    (⟨o.val, o.property.1⟩ :
      PrivateComparatorWorkerOrigin (q := q) ring root) w

/-- Corrected quantified IWAIT C.1 obligation. Note that the
isolated launch need not have a head smaller than K; see the
top-overflow row below. -/
def PrivateIncrementIsolatedRarity {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (o : PrivateIncrementIsolatedOrigin (q := q) ring root)
    (T : Nat),
    workerTimeoutDenominator (compileAdvice q).b *
      L3.Prob.scheduleSum n T (fun w =>
        L3.Prob.indicator
          (privateIncrementIsolatedTimeout ring root o w)) ≤
      workerTimeoutNumerator (compileAdvice q).b * n ^ T

/-- Corrected quantified comparator C.1 obligation. -/
def PrivateComparatorIsolatedRarity {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (o : PrivateComparatorIsolatedOrigin (q := q) ring root)
    (T : Nat),
    workerTimeoutDenominator (compileAdvice q).b *
      L3.Prob.scheduleSum n T (fun w =>
        L3.Prob.indicator
          (privateComparatorIsolatedTimeout ring root o w)) ≤
      workerTimeoutNumerator (compileAdvice q).b * n ^ T

/-- One tagged union of RESET origins and isolated IWAIT/CWAIT
origins. No origins are created in RECOVERY or after absorption. -/
inductive PrivateIsolatedTrialOrigin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) where
  | reset : PrivateResetWorkerOrigin (q := q) ring root →
      PrivateIsolatedTrialOrigin ring root
  | increment : PrivateIncrementIsolatedOrigin (q := q) ring root →
      PrivateIsolatedTrialOrigin ring root
  | comparator : PrivateComparatorIsolatedOrigin (q := q) ring root →
      PrivateIsolatedTrialOrigin ring root

noncomputable def privateIsolatedTrialStarts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Counter.ResetColdLatchedPrivateState q n → Fin n →
      List (PrivateIsolatedTrialOrigin (q := q) ring root)
  | .live C started, e =>
      ((privateResetWorkerStarts (q := q) ring root
          (.live C started) e).map
        (fun o => PrivateIsolatedTrialOrigin.reset o)) ++
      ((privateIncrementIsolatedStarts (q := q) ring root
          (.live C started) e).map
        (fun o => PrivateIsolatedTrialOrigin.increment o)) ++
      ((privateComparatorIsolatedStarts (q := q) ring root
          (.live C started) e).map
        (fun o => PrivateIsolatedTrialOrigin.comparator o))
  | _, _ => []

noncomputable def privateIsolatedTrialTimeout {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    PrivateIsolatedTrialOrigin (q := q) ring root →
      List (Fin n) → Bool
  | .reset o, w => privateResetWorkerTimeout ring root o w
  | .increment o, w => privateIncrementIsolatedTimeout ring root o w
  | .comparator o, w => privateComparatorIsolatedTimeout ring root o w

/-- RESET conditional C.1 plus the two NEW isolated rarity
obligations gives the entire isolated three-kind watchdog. -/
theorem privateIsolatedTrialWatchdogOfRarities {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hi : PrivateIncrementIsolatedRarity (q := q) ring root)
    (hc : PrivateComparatorIsolatedRarity (q := q) ring root) :
    PrivateCleanWorkerWatchdog (q := q) ring root
      (privateIsolatedTrialStarts (q := q) ring root)
      (privateIsolatedTrialTimeout (q := q) ring root) := by
  intro z hz e o ho T
  cases z with
  | live C started =>
      simp only [privateIsolatedTrialStarts, List.mem_append,
        List.mem_map] at ho
      rcases ho with (hr | hiw) | hcw
      · obtain ⟨r, hmem, heq⟩ := hr
        cases heq
        have h := privateResetWorkerWatchdog (q := q) ring root
          (.live C started) hz e r hmem T
        simpa only [privateIsolatedTrialTimeout] using h
      · obtain ⟨r, _, heq⟩ := hiw
        cases heq
        simpa only [privateIsolatedTrialTimeout] using hi r T
      · obtain ⟨r, _, heq⟩ := hcw
        cases heq
        simpa only [privateIsolatedTrialTimeout] using hc r T
  | recovery C =>
      simp [privateIsolatedTrialStarts] at ho
  | success C =>
      simp [privateIsolatedTrialStarts] at ho
  | failure C =>
      simp [privateIsolatedTrialStarts] at ho

/-- C.4 union for the corrected three-kind observer, conditional
on precisely the missing isolated rarities and the wordwise cap. -/
theorem privateIsolatedTrialUnionOfRarities {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hi : PrivateIncrementIsolatedRarity (q := q) ring root)
    (hc : PrivateComparatorIsolatedRarity (q := q) ring root)
    (hcap : PrivateCleanWorkerStartCap (q := q)
      ring root C (privateIsolatedTrialStarts (q := q) ring root))
    (T : Nat) :
    workerTimeoutDenominator (compileAdvice q).b *
      privateWorkerTimeoutMass ring root C
        (privateIsolatedTrialStarts (q := q) ring root)
        (privateIsolatedTrialTimeout (q := q) ring root) T ≤
      workerTimeoutNumerator (compileAdvice q).b *
        (n ^ T * (2 * (compileAdvice q).K + 1)) := by
  exact privateWorkerTimeoutUnion ring root C
    (privateIsolatedTrialStarts (q := q) ring root)
    (privateIsolatedTrialTimeout (q := q) ring root)
    (privateIsolatedTrialWatchdogOfRarities ring root hi hc)
    hcap T

/-- The existing compiled 1024 certificate needs no alteration
when the isolated rarity and start cap premises become available. -/
theorem privateIsolatedTrialTinyOfRarities {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hi : PrivateIncrementIsolatedRarity (q := q) ring root)
    (hc : PrivateComparatorIsolatedRarity (q := q) ring root)
    (hcap : PrivateCleanWorkerStartCap (q := q)
      ring root C (privateIsolatedTrialStarts (q := q) ring root))
    (T : Nat) :
    1024 * privateWorkerTimeoutMass ring root C
        (privateIsolatedTrialStarts (q := q) ring root)
        (privateIsolatedTrialTimeout (q := q) ring root) T ≤
      n ^ T := by
  exact privateWorkerTimeoutTiny ring root C
    (privateIsolatedTrialStarts (q := q) ring root)
    (privateIsolatedTrialTimeout (q := q) ring root)
    hsp hwidth
    (privateIsolatedTrialWatchdogOfRarities ring root hi hc)
    hcap T

/-- Literal top-source row: when the old PACK successor role is
unchanged, the outgoing service from top digit b deletes an IR
token at its source. No special top worker semantics are invented. -/
theorem privateIncrementTopSourceErasesIR {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpost :
      packNext
        (C (Counter.site ring root (compileAdvice q).b)).pack.val
        (C (Counter.site ring root ((compileAdvice q).b + 1))).pack.val
        (compileAdvice q).b =
        (C (Counter.site ring root ((compileAdvice q).b + 1))).pack.val)
    (htop : (C (Counter.site ring root (compileAdvice q).b)).tok =
      .IR) :
    (((protocol q).step ring C
        (Counter.site ring root (compileAdvice q).b))
        (Counter.site ring root (compileAdvice q).b)).tok = .E := by
  have hb : 0 < (compileAdvice q).b := by
    have hh := Counter.resetTrialCompiledWidth q
    omega
  have hn : 2 ≤ n := by
    have hh : 2 * (13 * ((compileAdvice q).b + 2)) ≤ n := by
      simpa only [Compiled.bankLeaseCap] using hlarge
    omega
  have hne :
      ring.rightNeighbor
        (Counter.site ring root (compileAdvice q).b) ≠
        Counter.site ring root (compileAdvice q).b :=
    Counter.resetRootPortDistinct ring
      (Counter.site ring root (compileAdvice q).b) hn
  have hrole :
      (C (Counter.site ring root (compileAdvice q).b)).pack.val =
        (compileAdvice q).b :=
    hc (compileAdvice q).b (by omega)
  have hraw := Counter.resetColdBankTopSourceToken
    (bankCell (C (Counter.site ring root (compileAdvice q).b))
      (C (Counter.site ring root (compileAdvice q).b)).pack.val)
    (bankCell (C (Counter.site ring root ((compileAdvice q).b + 1)))
      (C (Counter.site ring root ((compileAdvice q).b + 1))).pack.val)
    (packNext
      (C (Counter.site ring root (compileAdvice q).b)).pack.val
      (C (Counter.site ring root ((compileAdvice q).b + 1))).pack.val
      (compileAdvice q).b)
    (compileAdvice q).b (compileAdvice q).theta hrole hb
  have hbank :
      (Counter.resetBankOld
        (C (Counter.site ring root (compileAdvice q).b))
        (C (Counter.site ring root ((compileAdvice q).b + 1)))).1.tok =
        .E := by
    simpa only [Counter.resetBankOld, bankCell,
      hpost, htop, ↓reduceIte] using hraw
  have htrip := Counter.resetPhysicalEdgeBankTrip ring C
    (Counter.site ring root (compileAdvice q).b) hne hsp
  exact (congrArg (fun z : Mode × Bool × BTok => z.2.2)
    htrip.1).trans hbank

/-- If the IR at the top digit is the unique protected worker,
the real top-source service leaves every protected worker slot
empty. Thus spatial isolation is lost on that *nonproductive* edge. -/
theorem privateIncrementTopSourceDestroysIsolation {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpost :
      packNext
        (C (Counter.site ring root (compileAdvice q).b)).pack.val
        (C (Counter.site ring root ((compileAdvice q).b + 1))).pack.val
        (compileAdvice q).b =
        (C (Counter.site ring root ((compileAdvice q).b + 1))).pack.val)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C
      (compileAdvice q).b .IR) :
    Counter.resetColdPrivateNoWorkers ring root
      ((protocol q).step ring C
        (Counter.site ring root (compileAdvice q).b)) := by
  have htop := privateIncrementTopSourceErasesIR
    ring root C hc hsp hlarge hpost hw.2.2.1
  intro i hi hib
  by_cases he : i = (compileAdvice q).b
  · subst i
    exact htop
  · rw [Counter.resetColdPrivateTopSourceLowerFrame
      ring root C hc i hi (by omega)]
    exact hw.2.2.2 i hi hib he

/-- The top-source step just exhibited does not spend a root
lease or change IWAIT, when the counter's physical hlarge geometry
holds. Its effect is solely a destructive worker transition. -/
theorem privateIncrementTopSourceWaitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hm : (C root).mode = .IWAIT)
    (hl : (C root).lease.val = (compileAdvice q).bankLeaseCap) :
    (((protocol q).step ring C
        (Counter.site ring root (compileAdvice q).b)) root).mode =
      .IWAIT ∧
    (((protocol q).step ring C
        (Counter.site ring root (compileAdvice q).b)) root).lease.val =
      (compileAdvice q).bankLeaseCap := by
  have hf := Counter.resetColdTopRootPhysicalFrame
    ring C root hc hlarge
  exact ⟨
    (congrArg (fun a : Agent (compileAdvice q) => a.mode)
      hf).trans hm,
    (congrArg (fun a : Agent (compileAdvice q) => a.lease.val)
      hf).trans hl⟩

/-- Additional AUTHENTICATED numeric-head condition needed to
exclude the top-IR destruction demonstrated above. The already
proved source theorem now applies. -/
def PrivateIncrementBoundedIsolatedLaunch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Prop :=
  PrivateIncrementIsolatedLaunch ring root C ∧
    Counter.ResetColdPrivateLiveShapeAuth ring root C ∧
    (compileAdvice q).K < 2 ^ (compileAdvice q).b

theorem privateIncrementBoundedExcludesTopIR {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (h : PrivateIncrementBoundedIsolatedLaunch ring root C) :
    (C (Counter.site ring root (compileAdvice q).b)).tok ≠ .IR := by
  intro ht
  exact Counter.resetColdPrivateTopIRImpossible ring root C
    h.2.2 h.2.1.1 ht

/-- Root-incident nondesignated services define an adapted penalty
set for ANY physical nonreset comparison and ANY adapted edge
designation. Disjointness and cardinality are unconditional. -/
def privateWaitingPenalty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (designated : PrivateWaitingState q n → Fin n)
    (x : PrivateWaitingState q n) (e : Fin n) : Prop :=
  (e = root ∨ ring.rightNeighbor e = root) ∧ e ≠ designated x

theorem privateWaitingPenaltyDisjoint {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (designated : PrivateWaitingState q n → Fin n) :
    ∀ x : PrivateWaitingState q n,
      ¬ privateWaitingPenalty ring root designated x
        (designated x) := by
  intro x hp
  exact hp.2 rfl

theorem privateWaitingPenaltyCap {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (designated : PrivateWaitingState q n → Fin n) :
    ∀ x : PrivateWaitingState q n,
      (List.ofFn (fun e : Fin n =>
        if privateWaitingPenalty ring root designated x e then 1 else 0)).sum ≤
        2 := by
  intro x
  exact privateWorkerTwoPortCap
    root (Counter.site ring root (n - 1))
    (privateWaitingPenalty ring root designated x)
    (fun e hp => by
      rcases hp.1 with he | he
      · exact Or.inl he
      · exact Or.inr
          (privateWorkerIncomingUnique ring root e he))

/-- Exact reduction of the isolated IWAIT C.1 to its first missing
physical fact: for every scheduler word, an observed waitLoss
must entail at least Lambda-L nondesignated root incidents before
at most L designated productive services. No such pathwise
inclusion is postulated by this theorem; it is a hypothesis. -/
theorem privateIncrementIsolatedRarityOfPathwiseTail {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (designated : PrivateWaitingState q n → Fin n)
    (hcover :
      ∀ (o : PrivateIncrementIsolatedOrigin (q := q) ring root)
        (w : List (Fin n)),
        privateIncrementIsolatedTimeout ring root o w = true →
        11 * (compileAdvice q).b + 24 ≤
          workerPenaltyCount
            (privateWaitingNext ring root .IWAIT
              privateIncrementReturnToken)
            designated
            (privateWaitingPenalty ring root designated)
            (o.val, .live)
            (2 * (compileAdvice q).b + 2) w) :
    PrivateIncrementIsolatedRarity (q := q) ring root := by
  intro o T
  have htail := adaptedWorkerTimeoutNumerator
    (privateWaitingNext ring root .IWAIT
      privateIncrementReturnToken)
    designated (privateWaitingPenalty ring root designated)
    (privateWaitingPenaltyDisjoint ring root designated)
    (privateWaitingPenaltyCap ring root designated)
    (o.val, .live) (compileAdvice q).b T
  have hpoint (w : List (Fin n)) :
      L3.Prob.indicator
        (privateIncrementIsolatedTimeout ring root o w) ≤
        (if 11 * (compileAdvice q).b + 24 ≤
          workerPenaltyCount
            (privateWaitingNext ring root .IWAIT
              privateIncrementReturnToken)
            designated (privateWaitingPenalty ring root designated)
            (o.val, .live)
            (2 * (compileAdvice q).b + 2) w
        then 1 else 0) := by
    cases hw : privateIncrementIsolatedTimeout ring root o w with
    | false =>
        simp [L3.Prob.indicator, hw]
    | true =>
        have hineq := hcover o w hw
        simp [L3.Prob.indicator, hw, hineq]
  calc
    workerTimeoutDenominator (compileAdvice q).b *
        L3.Prob.scheduleSum n T (fun w =>
          L3.Prob.indicator
            (privateIncrementIsolatedTimeout ring root o w)) =
      workerTimeoutDenominator (compileAdvice q).b *
        Counter.resetColdWordSum n T (fun w =>
          L3.Prob.indicator
            (privateIncrementIsolatedTimeout ring root o w)) := by
          rw [privateWorkerScheduleSum]
    _ ≤ workerTimeoutDenominator (compileAdvice q).b *
        Counter.resetColdWordSum n T (fun w =>
          if 11 * (compileAdvice q).b + 24 ≤
            workerPenaltyCount
              (privateWaitingNext ring root .IWAIT
                privateIncrementReturnToken)
              designated
              (privateWaitingPenalty ring root designated)
              (o.val, .live)
              (2 * (compileAdvice q).b + 2) w
          then 1 else 0) := by
            exact Nat.mul_le_mul_left _
              (workerWordSumMono T _ _ hpoint)
    _ = workerTimeoutDenominator (compileAdvice q).b *
        workerPenaltyTailMass
          (privateWaitingNext ring root .IWAIT
            privateIncrementReturnToken)
          designated
          (privateWaitingPenalty ring root designated)
          (o.val, .live)
          (2 * (compileAdvice q).b + 2)
          (11 * (compileAdvice q).b + 24) T := rfl
    _ ≤ workerTimeoutNumerator (compileAdvice q).b *
          n ^ T := htail

end L3.CounterTrialLower

/-!
The physical IWAIT comparison versus the authenticated
latched observer, plus a finite-word lease/rank accounting engine.

Unlike Counter.resetColdPrivateLiveShapeAuthWord, the comparison
starts at an arbitrary bounded, isolated postlaunch configuration.
This section proves that every surviving comparison-LIVE suffix
inherits Auth and Complete, by transport through the actual latched
observer's LIVE step. It does not silently assert the missing
designated-edge rank-drop or root-lease local accounting lemmas.
-/

namespace L3.CounterTrialLower

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- Extract the four guards actually passed by an IWAIT comparison
LIVE transition. In particular neither a matching AL return nor a
root lease-one exit can be labelled LIVE. -/
theorem privateIWaitComparisonLiveGuards {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C e = .live) :
    ¬ Counter.ResetClockBankDefectEntry ring C root e ∧
    ¬ (e = root ∧
      privateIncrementReturnToken
        (C (Counter.site ring root 1)).tok) ∧
    Counter.GrantFree ((protocol q).step ring C e) root ∧
    (C root).mode = .IWAIT ∧
    (((protocol q).step ring C e) root).mode = .IWAIT := by
  by_cases hd : Counter.ResetClockBankDefectEntry ring C root e
  · simp [privateWaitingOutcome, hd] at hlive
  · by_cases hr : e = root ∧
        privateIncrementReturnToken
          (C (Counter.site ring root 1)).tok
    · by_cases hdr : Counter.ResetClockBankDefectEntry ring C root root <;>
        simp [privateWaitingOutcome, hd, hr, hdr] at hlive
    · by_cases hg : Counter.GrantFree
          ((protocol q).step ring C e) root
      · by_cases hm : (C root).mode = .IWAIT
        · by_cases hp : (e = root ∨
              ring.rightNeighbor e = root) ∧
              (C root).lease.val = 1
          · simp [privateWaitingOutcome, hd, hr, hg, hm, hp] at hlive
          · by_cases hn :
                (((protocol q).step ring C e) root).mode = .IWAIT
            · exact ⟨hd, hr, hg, hm, hn⟩
            · simp [privateWaitingOutcome, hd, hr, hg, hm,
                hp, hn] at hlive
        · simp [privateWaitingOutcome, hd, hr, hg, hm] at hlive
      · simp [privateWaitingOutcome, hd, hr, hg] at hlive

/-- A surviving physical IWAIT comparison service is also a LIVE
transition of the *actual latched private observer*, with begun=true.
This is the bridge needed to reuse CounterCold's word-level Auth
closure. No stochastic or fake transition is introduced. -/
theorem privateIWaitComparisonLiveObserver {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C e = .live) :
    Counter.resetColdLatchedPrivateNext ring root
      (.live C true) e =
      .live ((protocol q).step ring C e) true := by
  obtain ⟨hdef, _, _, hold, hnew⟩ :=
    privateIWaitComparisonLiveGuards ring root e C hlive
  have hnSuccess : ¬ Counter.resetColdPrivateSuccessAt
      ring root C e := by
    intro hs
    have hm := Counter.resetColdPrivateSuccessRequiresCWait
      ring root e C hs
    rw [hold] at hm
    cases hm
  have hnClean : ¬ Counter.ResetClockBankClean ring
      ((protocol q).step ring C e) root := by
    intro hc
    have hm := hc.2.1
    rw [hnew] at hm
    cases hm
  have hnAbort : ¬ Counter.resetColdLatchedAbort
      ring root C e := by
    intro ha
    rcases ha with hi | hr
    · rw [hold] at hi
      cases hi.1
    · rw [hnew] at hr
      cases hr
  have hbegun : Counter.resetColdLatchedBegun ring root e true :=
    Or.inl rfl
  simp only [Counter.resetColdLatchedPrivateNext,
    if_neg hdef, if_neg hnSuccess, if_pos hbegun,
    if_neg hnClean, if_neg hnAbort]

/-- A single surviving IWAIT comparison service preserves both
Auth and Complete, and still has root mode IWAIT. The source's
resetColdPrivateLiveAuthStep exhaustively handles all real edges. -/
theorem privateIWaitComparisonAuthStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C e = .live) :
    Counter.ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C e) ∧
    Counter.Complete ring ((protocol q).step ring C e) root ∧
    (((protocol q).step ring C e) root).mode = .IWAIT := by
  have hobs := privateIWaitComparisonLiveObserver
    ring root e C hlive
  have haStep := Counter.resetColdPrivateLiveAuthStep
    ring root e C ((protocol q).step ring C e)
    true true hc hsp hlarge hwidth ha hobs
  have hcStep := Counter.resetColdPrivateLiveCompleteStep
    ring root e C ((protocol q).step ring C e)
    true true hc hobs
  have hmStep :=
    (privateIWaitComparisonLiveGuards ring root e C hlive).2.2.2.2
  exact ⟨haStep.1, hcStep, hmStep⟩

/-- Once the waiting comparison is non-LIVE, it is genuinely
absorbing, including the waitLoss, grant, defect and completed
return states. -/
theorem privateIWaitComparisonWordAbsorbing {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : PrivateWaitingState q n)
    (hz : z.2 ≠ .live) (w : List (Fin n)) :
    privateWaitingWord ring root .IWAIT
      privateIncrementReturnToken w z = z := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      change privateWaitingWord ring root .IWAIT
        privateIncrementReturnToken w
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken z e) = z
      have hnext : privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken z e = z := by
        cases z with
        | mk C s =>
            cases s <;> simp [privateWaitingNext] at hz ⊢
      rw [hnext]
      exact ih

/-- Auth and Complete hold at every IWAIT comparison LIVE suffix
from ANY bounded isolated authenticated origin, not merely a
history globally known to begin at an earlier Clean cut. This
is a transport theorem for the exact privateWaitingWord. -/
theorem privateIWaitComparisonAuthWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    ∀ (C : Counter.Config q n) (w : List (Fin n)),
      Counter.ResetColdPrivateLiveShapeAuth ring root C →
      Counter.Complete ring C root →
      (C root).mode = .IWAIT →
      (privateWaitingWord ring root .IWAIT
        privateIncrementReturnToken w (C, .live)).2 = .live →
      Counter.ResetColdPrivateLiveShapeAuth ring root
        (privateWaitingWord ring root .IWAIT
          privateIncrementReturnToken w (C, .live)).1 ∧
      Counter.Complete ring
        (privateWaitingWord ring root .IWAIT
          privateIncrementReturnToken w (C, .live)).1 root ∧
      ((privateWaitingWord ring root .IWAIT
          privateIncrementReturnToken w (C, .live)).1 root).mode =
        .IWAIT := by
  intro C w
  induction w generalizing C with
  | nil =>
      intro ha hc hm _
      exact ⟨ha, hc, hm⟩
  | cons e w ih =>
      intro ha hc hm hresult
      have hstep :
          (privateWaitingNext ring root .IWAIT
            privateIncrementReturnToken (C, .live) e).2 =
            .live := by
        by_cases hl :
            (privateWaitingNext ring root .IWAIT
              privateIncrementReturnToken (C, .live) e).2 = .live
        · exact hl
        · have hstay :=
            privateIWaitComparisonWordAbsorbing ring root
              (privateWaitingNext ring root .IWAIT
                privateIncrementReturnToken (C, .live) e)
              hl w
          change (privateWaitingWord ring root .IWAIT
              privateIncrementReturnToken w
              (privateWaitingNext ring root .IWAIT
                privateIncrementReturnToken (C, .live) e)).2 =
              .live at hresult
          rw [hstay] at hresult
          exact False.elim (hl hresult)
      have hout :
          privateWaitingOutcome ring root .IWAIT
            privateIncrementReturnToken C e = .live := hstep
      have hnext :=
        privateIWaitComparisonAuthStep ring root e C
          hsp hlarge hwidth ha hc hout
      have hpair :
          privateWaitingNext ring root .IWAIT
            privateIncrementReturnToken (C, .live) e =
            ((protocol q).step ring C e, .live) := by
        change ((protocol q).step ring C e,
          privateWaitingOutcome ring root .IWAIT
            privateIncrementReturnToken C e) =
            ((protocol q).step ring C e, .live)
        rw [hout]
      change (privateWaitingWord ring root .IWAIT
        privateIncrementReturnToken w
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken (C, .live) e)).2 =
          .live at hresult
      rw [hpair] at hresult
      have hword :
          privateWaitingWord ring root .IWAIT
              privateIncrementReturnToken (e :: w) (C, .live) =
            privateWaitingWord ring root .IWAIT
              privateIncrementReturnToken w
              ((protocol q).step ring C e, .live) := by
        rw [← hpair]
        rfl
      rw [hword]
      exact ih ((protocol q).step ring C e)
        hnext.1 hnext.2.1 hnext.2.2 hresult

/-- In any authenticated IWAIT configuration there exists exactly
one occupied carry-worker slot. This extracts the correct phase of
the CounterCold four-way Auth invariant. -/
theorem privateIWaitAuthenticatedFront {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT) :
    ∃ j : Nat, ∃ t : BTok,
      Counter.resetColdPrivateOnlyWorker ring root C j t ∧
      Counter.resetColdPrivateCarryToken t := by
  rcases ha.1 with harm | hrest
  · obtain ⟨_, _, hmode, _, _⟩ := harm
    rw [hmode] at hm
    cases hm
  · rcases hrest with hstart | hrest
    · obtain ⟨_, _, hmode, _, _⟩ := hstart
      rw [hmode] at hm
      cases hm
    · rcases hrest with hcomp | hcarry
      · obtain ⟨_, _, _, _, hmode, _, _, _, _, _⟩ := hcomp
        rw [hmode] at hm
        cases hm
      · obtain ⟨_, j, t, _, _, hw, ht, _⟩ := hcarry
        exact ⟨j, t, hw, ht⟩

/-- The original physical IWAIT observer's accepted word keeps the
unique worker and its Auth provenance up to the first detected
terminal service. -/
theorem privateIWaitComparisonFrontWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (o : { C : Counter.Config q n //
      PrivateIncrementBoundedIsolatedLaunch ring root C })
    (w : List (Fin n))
    (hlive : (privateWaitingWord ring root .IWAIT
      privateIncrementReturnToken w (o.val, .live)).2 = .live) :
    ∃ j : Nat, ∃ t : BTok,
      Counter.resetColdPrivateOnlyWorker ring root
        (privateWaitingWord ring root .IWAIT
          privateIncrementReturnToken w (o.val, .live)).1 j t ∧
      Counter.resetColdPrivateCarryToken t := by
  have hh := privateIWaitComparisonAuthWord ring root
    o.property.1.1.1 hlarge o.property.2.2
    o.val w o.property.2.1 o.property.1.1.2.1
    o.property.1.1.2.2.2.1 hlive
  exact privateIWaitAuthenticatedFront ring root
    (privateWaitingWord ring root .IWAIT
      privateIncrementReturnToken w (o.val, .live)).1
    hh.1 hh.2.2


/-- Original finite scheduler word, without changing the original
transition or introducing a new sample space. -/
def privateWorkerRawRun {S : Type} {n : Nat}
    (next : S → Fin n → S) : S → List (Fin n) → S
  | x, [] => x
  | x, e :: w => privateWorkerRawRun next (next x e) w

/-- Any non-LIVE absorbing state stays unchanged over the entire
remaining scheduler suffix, not merely the next selected edge. -/
theorem privateWorkerRawRunAbsorbing {S : Type} {n : Nat}
    (next : S → Fin n → S) (live : S → Prop)
    (habsorb : ∀ x e, ¬ live x → next x e = x)
    (x : S) (hx : ¬ live x) (w : List (Fin n)) :
    privateWorkerRawRun next x w = x := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      change privateWorkerRawRun next (next x e) w = x
      rw [habsorb x e hx]
      exact ih

/-- Fully proved Nat-valued pathwise accounting lemma. A LIVE
front has strictly positive rank. On each designated service it
drops at least one rank unit and leaves the lease unchanged;
on a penalty it loses one lease unit and does not increase rank;
on every other service both quantities stay nonincreasing.
An absorbing failure must occur at one last penalty, with one
unit of lease remaining. Then any failure word contains at
least its *initial lease* many penalty letters before the
finite designated-service budget is used up. -/
theorem privateWorkerLeaseRankWordBound
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (designated : S → Fin n)
    (penalty : S → Fin n → Prop)
    (good live failure : S → Prop)
    (rank fuel : S → Nat)
    (habsorb : ∀ x e, ¬ live x → next x e = x)
    (hfailureNotLive : ∀ x, failure x → ¬ live x)
    (hgoodStep : ∀ x e,
      good x → live x → live (next x e) → good (next x e))
    (hrankPos : ∀ x, good x → live x → 0 < rank x)
    (hstep : ∀ x e, good x → live x → live (next x e) →
      (e = designated x →
        rank (next x e) + 1 ≤ rank x ∧
        fuel (next x e) = fuel x) ∧
      (e ≠ designated x → penalty x e →
        rank (next x e) ≤ rank x ∧
        fuel (next x e) + 1 = fuel x) ∧
      (e ≠ designated x → ¬ penalty x e →
        rank (next x e) ≤ rank x ∧
        fuel (next x e) = fuel x))
    (hfailureStep : ∀ x e,
      good x → live x → failure (next x e) →
      e ≠ designated x ∧ penalty x e ∧ fuel x = 1) :
    ∀ (w : List (Fin n)) (x : S) (budget : Nat),
      good x → live x → rank x ≤ budget →
      failure (privateWorkerRawRun next x w) →
      fuel x ≤ workerPenaltyCount next designated penalty
        x budget w := by
  intro w
  induction w with
  | nil =>
      intro x budget hg hl hr hf
      exact False.elim ((hfailureNotLive x hf) hl)
  | cons e w ih =>
      intro x budget hg hl hr hf
      have hpos := hrankPos x hg hl
      cases budget with
      | zero =>
          have hbad : False := by omega
          exact False.elim hbad
      | succ rest =>
          have hchildFail :
              failure (privateWorkerRawRun next (next x e) w) := hf
          by_cases hchild : live (next x e)
          · have hgoodChild :=
              hgoodStep x e hg hl hchild
            obtain ⟨hdesignated, hpenalty, hother⟩ :=
              hstep x e hg hl hchild
            by_cases hd : e = designated x
            · obtain ⟨hdrop, hlease⟩ := hdesignated hd
              have hrchild : rank (next x e) ≤ rest := by omega
              have htail := ih (next x e) rest
                hgoodChild hchild hrchild hchildFail
              calc
                fuel x = fuel (next x e) := hlease.symm
                _ ≤ workerPenaltyCount next designated penalty
                    (next x e) rest w := htail
                _ = workerPenaltyCount next designated penalty
                    x (rest + 1) (e :: w) := by
                      simp only [workerPenaltyCount, if_pos hd]
            · by_cases hp : penalty x e
              · obtain ⟨hrchild, hlease⟩ := hpenalty hd hp
                have htail := ih (next x e) (rest + 1)
                  hgoodChild hchild (by omega) hchildFail
                calc
                  fuel x = 1 + fuel (next x e) := by omega
                  _ ≤ 1 + workerPenaltyCount next designated
                      penalty (next x e) (rest + 1) w :=
                    Nat.add_le_add_left htail 1
                  _ = workerPenaltyCount next designated penalty
                      x (rest + 1) (e :: w) := by
                        simp only [workerPenaltyCount,
                          if_neg hd, if_pos hp]
              · obtain ⟨hrchild, hlease⟩ := hother hd hp
                have htail := ih (next x e) (rest + 1)
                  hgoodChild hchild (by omega) hchildFail
                calc
                  fuel x = fuel (next x e) := hlease.symm
                  _ ≤ workerPenaltyCount next designated penalty
                      (next x e) (rest + 1) w := htail
                  _ = workerPenaltyCount next designated penalty
                      x (rest + 1) (e :: w) := by
                        simp only [workerPenaltyCount,
                          if_neg hd, if_neg hp]
          · have hstay := privateWorkerRawRunAbsorbing
              next live habsorb (next x e) hchild w
            have hfailed : failure (next x e) := by
              rw [hstay] at hchildFail
              exact hchildFail
            obtain ⟨hd, hp, hlease⟩ :=
              hfailureStep x e hg hl hfailed
            calc
              fuel x = 1 := hlease
              _ ≤ 1 + workerPenaltyCount next designated penalty
                  (next x e) (rest + 1) w := by omega
              _ = workerPenaltyCount next designated penalty
                  x (rest + 1) (e :: w) := by
                    simp only [workerPenaltyCount,
                      if_neg hd, if_pos hp]

/-- The generic accounting engine is literally on the original
IWAIT comparison word, not a fictitious worker scheduler. -/
theorem privateIWaitRawRunEqWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (w : List (Fin n)) (x : PrivateWaitingState q n) :
    privateWorkerRawRun
      (privateWaitingNext ring root .IWAIT
        privateIncrementReturnToken) x w =
      privateWaitingWord ring root .IWAIT
        privateIncrementReturnToken w x := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
      change privateWorkerRawRun
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken)
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) w =
        privateWaitingWord ring root .IWAIT
          privateIncrementReturnToken w
          (privateWaitingNext ring root .IWAIT
            privateIncrementReturnToken x e)
      exact ih _



/-- The authenticated IWAIT worker is determined from the CURRENT
physical state. Classical choice only chooses an existing unique
worker position, never an independent future scheduler letter. -/
noncomputable def privateIWaitFrontIndex {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Nat :=
  if h : ∃ j : Nat, ∃ t : BTok,
      Counter.resetColdPrivateOnlyWorker ring root C j t ∧
      Counter.resetColdPrivateCarryToken t then
    Classical.choose h
  else 1

/-- At an Auth/IWAIT cut the chosen index is a physically occupied
protected digit, of type IR or AL. -/
theorem privateIWaitFrontIndexSpec {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT) :
    ∃ t : BTok,
      Counter.resetColdPrivateOnlyWorker ring root C
        (privateIWaitFrontIndex ring root C) t ∧
      Counter.resetColdPrivateCarryToken t := by
  have hex := privateIWaitAuthenticatedFront ring root C ha hm
  unfold privateIWaitFrontIndex
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem privateIWaitFrontIndexBounds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT) :
    1 ≤ privateIWaitFrontIndex ring root C ∧
      privateIWaitFrontIndex ring root C ≤ (compileAdvice q).b := by
  obtain ⟨t, hw, _⟩ :=
    privateIWaitFrontIndexSpec ring root C ha hm
  exact ⟨hw.1, hw.2.1⟩

/-- The next worker service is its source edge when forwarding IR,
and the predecessor edge when returning AL. At AL(1) the root
edge completes the worker and ends the comparison. -/
noncomputable def privateIWaitDesignated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : PrivateWaitingState q n) : Fin n :=
  if (x.1 (Counter.site ring root
        (privateIWaitFrontIndex ring root x.1))).tok = .IR then
    Counter.site ring root (privateIWaitFrontIndex ring root x.1)
  else if privateIWaitFrontIndex ring root x.1 = 1 then
    root
  else
    Counter.site ring root
      (privateIWaitFrontIndex ring root x.1 - 1)

/-- Natural service rank of an authenticated IWAIT front. The IR
phase uses the remaining outward-and-return route; the AL phase
uses its current distance to the root. Every designated LIVE
service is expected to decrease this rank, but that physical
step fact is not silently assumed. -/
noncomputable def privateIWaitRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : PrivateWaitingState q n) : Nat :=
  if (x.1 (Counter.site ring root
        (privateIWaitFrontIndex ring root x.1))).tok = .IR then
    2 * (compileAdvice q).b + 2 -
      privateIWaitFrontIndex ring root x.1
  else privateIWaitFrontIndex ring root x.1

/-- The rank is positive and below the paper's fixed L=2b+2
for every Auth IWAIT cut. This also covers all surviving
comparison LIVE words by privateIWaitComparisonAuthWord. -/
theorem privateIWaitRankBounds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT) :
    0 < privateIWaitRank ring root (C, .live) ∧
      privateIWaitRank ring root (C, .live) ≤
        2 * (compileAdvice q).b + 2 := by
  obtain ⟨hj, hjb⟩ :=
    privateIWaitFrontIndexBounds ring root C ha hm
  by_cases ht :
      (C (Counter.site ring root
        (privateIWaitFrontIndex ring root C))).tok = .IR
  · simp only [privateIWaitRank, if_pos ht]
    omega
  · simp only [privateIWaitRank, if_neg ht]
    omega

/-- Bounded, isolated origins for the intended physical C.1
statement. This is a strict subtype of the isolated origins. -/
abbrev PrivateIncrementBoundedOrigin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  { C : Counter.Config q n //
      PrivateIncrementBoundedIsolatedLaunch ring root C }

noncomputable def privateIncrementBoundedTimeout {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : PrivateIncrementBoundedOrigin (q := q) ring root)
    (w : List (Fin n)) : Bool :=
  privateIncrementIsolatedTimeout ring root
    (⟨o.val, o.property.1⟩ :
      PrivateIncrementIsolatedOrigin (q := q) ring root) w

/-- Desired sharp C.1 for authenticated bounded IWAIT origins on
the large-ring spatial domain. Still an unproved Prop until the
concrete rank/lease local-step ledger below is checked. -/
def PrivateIncrementBoundedRarity {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  ∀ (o : PrivateIncrementBoundedOrigin (q := q) ring root)
    (T : Nat),
    workerTimeoutDenominator (compileAdvice q).b *
      L3.Prob.scheduleSum n T (fun w =>
        L3.Prob.indicator
          (privateIncrementBoundedTimeout ring root o w)) ≤
      workerTimeoutNumerator (compileAdvice q).b * n ^ T



/-- The minimal current-state comparison invariant. Every LIVE
phase is authenticated, complete and literally waiting in IWAIT. -/
def PrivateIWaitComparisonGood {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : PrivateWaitingState q n) : Prop :=
  x.2 = .live →
    Counter.ResetColdPrivateLiveShapeAuth ring root x.1 ∧
    Counter.Complete ring x.1 root ∧
    (x.1 root).mode = .IWAIT

/-- The exact physical IWAIT comparison is absorbing in every
non-LIVE state, including all distinct terminal labels. -/
theorem privateIWaitNextAbsorbing {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : PrivateWaitingState q n) (e : Fin n)
    (hx : x.2 ≠ .live) :
    privateWaitingNext ring root .IWAIT
      privateIncrementReturnToken x e = x := by
  cases x with
  | mk C s =>
      cases s <;> simp [privateWaitingNext] at hx ⊢

/-- Auth and Complete are an invariant of the REAL physical IWAIT
comparison, not merely of a separately defined abstract clock. -/
theorem privateIWaitComparisonGoodStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (x : PrivateWaitingState q n)
    (hg : PrivateIWaitComparisonGood ring root x)
    (e : Fin n) :
    PrivateIWaitComparisonGood ring root
      (privateWaitingNext ring root .IWAIT
        privateIncrementReturnToken x e) := by
  intro hnext
  by_cases hx : x.2 = .live
  · obtain ⟨ha, hc, hm⟩ := hg hx
    have hpair :
        privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e =
        ((protocol q).step ring x.1 e,
          privateWaitingOutcome ring root .IWAIT
            privateIncrementReturnToken x.1 e) := by
      cases x with
      | mk C s =>
          cases s <;> simp [privateWaitingNext] at hx ⊢
    have hout :
        privateWaitingOutcome ring root .IWAIT
          privateIncrementReturnToken x.1 e = .live := by
      rw [hpair] at hnext
      exact hnext
    have hh := privateIWaitComparisonAuthStep
      ring root e x.1 hsp hlarge hwidth ha hc hout
    rw [hpair]
    exact hh
  · have hpair :=
      privateIWaitNextAbsorbing ring root x e hx
    rw [hpair] at hnext
    exact False.elim (hx hnext)

/-- The rank and root lease of a LIVE IWAIT comparison state. -/
def privateIWaitRootLease {n q : Nat}
    (root : Fin n) (x : PrivateWaitingState q n) : Nat :=
  (x.1 root).lease.val

/-- All still-live comparison cuts have strictly positive service
rank, no larger than the paper's L=2b+2. -/
theorem privateIWaitGoodRankBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : PrivateWaitingState q n)
    (hg : PrivateIWaitComparisonGood ring root x)
    (hl : x.2 = .live) :
    0 < privateIWaitRank ring root x ∧
      privateIWaitRank ring root x ≤
        2 * (compileAdvice q).b + 2 := by
  obtain ⟨ha, _, hm⟩ := hg hl
  exact privateIWaitRankBounds ring root x.1 ha hm

/-- The exact remaining physical obligations, separated from
the already-proved finite-word exponential moment. The first
conjunct is the rank/lease rule for LIVE successors; the second
identifies every physical waitLoss edge as a final lease-unit
penalty, never a nominated productive service. -/
def PrivateIWaitRankLeaseRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  (∀ x : PrivateWaitingState q n, ∀ e : Fin n,
    PrivateIWaitComparisonGood ring root x →
    x.2 = .live →
    (privateWaitingNext ring root .IWAIT
      privateIncrementReturnToken x e).2 = .live →
    (e = privateIWaitDesignated ring root x →
      privateIWaitRank ring root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) + 1 ≤
        privateIWaitRank ring root x ∧
      privateIWaitRootLease root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) =
        privateIWaitRootLease root x) ∧
    (e ≠ privateIWaitDesignated ring root x →
      privateWaitingPenalty ring root
        (privateIWaitDesignated ring root) x e →
      privateIWaitRank ring root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) ≤
        privateIWaitRank ring root x ∧
      privateIWaitRootLease root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) + 1 =
        privateIWaitRootLease root x) ∧
    (e ≠ privateIWaitDesignated ring root x →
      ¬ privateWaitingPenalty ring root
        (privateIWaitDesignated ring root) x e →
      privateIWaitRank ring root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) ≤
        privateIWaitRank ring root x ∧
      privateIWaitRootLease root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) =
        privateIWaitRootLease root x)) ∧
  (∀ x : PrivateWaitingState q n, ∀ e : Fin n,
    PrivateIWaitComparisonGood ring root x →
    x.2 = .live →
    (privateWaitingNext ring root .IWAIT
      privateIncrementReturnToken x e).2 = .waitLoss →
    e ≠ privateIWaitDesignated ring root x ∧
    privateWaitingPenalty ring root
      (privateIWaitDesignated ring root) x e ∧
    privateIWaitRootLease root x = 1)

/-- From the concrete two local physical row obligations,
the generic word lemma gives the exact implication needed
by the moment method. The original current-state edge tape
and the actual waitLoss comparison are retained throughout. -/
theorem privateIWaitRankRowsGiveCover {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hrows : PrivateIWaitRankLeaseRows (q := q) ring root)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .IWAIT)
    (w : List (Fin n))
    (hfail :
      (privateWaitingWord ring root .IWAIT
        privateIncrementReturnToken w (C, .live)).2 = .waitLoss) :
    privateIWaitRootLease root (C, .live) ≤
      workerPenaltyCount
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken)
        (privateIWaitDesignated ring root)
        (privateWaitingPenalty ring root
          (privateIWaitDesignated ring root))
        (C, .live) (2 * (compileAdvice q).b + 2) w := by
  have hgood :
      PrivateIWaitComparisonGood ring root (C, .live) :=
    fun _ => ⟨ha, hc, hm⟩
  have hbound := privateIWaitGoodRankBound
    ring root (C, .live) hgood rfl
  have hrec := privateWorkerLeaseRankWordBound
    (privateWaitingNext ring root .IWAIT
      privateIncrementReturnToken)
    (privateIWaitDesignated ring root)
    (privateWaitingPenalty ring root
      (privateIWaitDesignated ring root))
    (PrivateIWaitComparisonGood ring root)
    (fun x : PrivateWaitingState q n => x.2 = .live)
    (fun x : PrivateWaitingState q n => x.2 = .waitLoss)
    (privateIWaitRank ring root)
    (privateIWaitRootLease root)
    (privateIWaitNextAbsorbing ring root)
    (fun x hf hl => by rw [hf] at hl; cases hl)
    (fun x e hg _ _ =>
      privateIWaitComparisonGoodStep ring root
        hsp hlarge hwidth x hg e)
    (fun x hg hl => (privateIWaitGoodRankBound
      ring root x hg hl).1)
    hrows.1 hrows.2
    w (C, .live) (2 * (compileAdvice q).b + 2)
    hgood rfl hbound.2
  apply hrec
  rw [privateIWaitRawRunEqWord]
  exact hfail



/-- The sharp C.1 bound for bounded isolated IWAIT origins reduces
to the exact local physical service rows in
PrivateIWaitRankLeaseRows. The finite-word counting and adapted
exponential moment are fully discharged here; the physical row
premise remains explicit, not an axiom or a claimed theorem. -/
theorem privateIncrementBoundedRarityOfRankRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : PrivateIWaitRankLeaseRows (q := q) ring root) :
    PrivateIncrementBoundedRarity (q := q) ring root := by
  intro hlarge o T
  have hcover (w : List (Fin n))
      (hw : privateIncrementBoundedTimeout ring root o w = true) :
      11 * (compileAdvice q).b + 24 ≤
      workerPenaltyCount
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken)
        (privateIWaitDesignated ring root)
        (privateWaitingPenalty ring root
          (privateIWaitDesignated ring root))
        (o.val, .live) (2 * (compileAdvice q).b + 2) w := by
    have hfail :
        (privateWaitingWord ring root .IWAIT
          privateIncrementReturnToken w (o.val, .live)).2 =
          .waitLoss := by
      by_cases he :
          (privateWaitingWord ring root .IWAIT
            privateIncrementReturnToken w (o.val, .live)).2 =
            .waitLoss
      · exact he
      · simp [privateIncrementBoundedTimeout,
          privateIncrementIsolatedTimeout,
          privateIncrementWorkerTimeout, he] at hw
    have hcount := privateIWaitRankRowsGiveCover ring root
      o.property.1.1.1 hlarge o.property.2.2 hrows
      o.val o.property.2.1 o.property.1.1.2.1
      o.property.1.1.2.2.2.1 w hfail
    have hlease :
        privateIWaitRootLease root (o.val, .live) =
          (compileAdvice q).bankLeaseCap := by
      change (o.val root).lease.val =
        (compileAdvice q).bankLeaseCap
      exact o.property.1.1.2.2.2.2.1
    rw [hlease] at hcount
    change 13 * ((compileAdvice q).b + 2) ≤
      workerPenaltyCount
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken)
        (privateIWaitDesignated ring root)
        (privateWaitingPenalty ring root
          (privateIWaitDesignated ring root))
        (o.val, .live) (2 * (compileAdvice q).b + 2) w
      at hcount
    omega
  have htail := adaptedWorkerTimeoutNumerator
    (privateWaitingNext ring root .IWAIT
      privateIncrementReturnToken)
    (privateIWaitDesignated ring root)
    (privateWaitingPenalty ring root
      (privateIWaitDesignated ring root))
    (privateWaitingPenaltyDisjoint ring root
      (privateIWaitDesignated ring root))
    (privateWaitingPenaltyCap ring root
      (privateIWaitDesignated ring root))
    (o.val, .live) (compileAdvice q).b T
  have hpoint (w : List (Fin n)) :
      L3.Prob.indicator
        (privateIncrementBoundedTimeout ring root o w) ≤
      (if 11 * (compileAdvice q).b + 24 ≤
        workerPenaltyCount
          (privateWaitingNext ring root .IWAIT
            privateIncrementReturnToken)
          (privateIWaitDesignated ring root)
          (privateWaitingPenalty ring root
            (privateIWaitDesignated ring root))
          (o.val, .live) (2 * (compileAdvice q).b + 2) w
      then 1 else 0) := by
    cases hw : privateIncrementBoundedTimeout ring root o w with
    | false =>
        simp [L3.Prob.indicator, hw]
    | true =>
        have hh := hcover w hw
        simp [L3.Prob.indicator, hw, hh]
  calc
    workerTimeoutDenominator (compileAdvice q).b *
        L3.Prob.scheduleSum n T (fun w =>
          L3.Prob.indicator
            (privateIncrementBoundedTimeout ring root o w)) =
      workerTimeoutDenominator (compileAdvice q).b *
        Counter.resetColdWordSum n T (fun w =>
          L3.Prob.indicator
            (privateIncrementBoundedTimeout ring root o w)) := by
          rw [privateWorkerScheduleSum]
    _ ≤ workerTimeoutDenominator (compileAdvice q).b *
        Counter.resetColdWordSum n T (fun w =>
          if 11 * (compileAdvice q).b + 24 ≤
            workerPenaltyCount
              (privateWaitingNext ring root .IWAIT
                privateIncrementReturnToken)
              (privateIWaitDesignated ring root)
              (privateWaitingPenalty ring root
                (privateIWaitDesignated ring root))
              (o.val, .live) (2 * (compileAdvice q).b + 2) w
          then 1 else 0) := by
            exact Nat.mul_le_mul_left _
              (workerWordSumMono T _ _ hpoint)
    _ = workerTimeoutDenominator (compileAdvice q).b *
        workerPenaltyTailMass
          (privateWaitingNext ring root .IWAIT
            privateIncrementReturnToken)
          (privateIWaitDesignated ring root)
          (privateWaitingPenalty ring root
            (privateIWaitDesignated ring root))
          (o.val, .live) (2 * (compileAdvice q).b + 2)
          (11 * (compileAdvice q).b + 24) T := rfl
    _ ≤ workerTimeoutNumerator (compileAdvice q).b *
          n ^ T := htail



/-- The source classifier itself proves the physical character of
any IWAIT waitLoss: it is a root-incident service with precisely
one old lease unit, and not the matching AL return. This does
NOT rely on an approximate waiting clock. -/
theorem privateIWaitLossIncidentLeaseOne {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hwait : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C e = .waitLoss) :
    (e = root ∨ ring.rightNeighbor e = root) ∧
    (C root).lease.val = 1 ∧
    ¬ (e = root ∧
      privateIncrementReturnToken
        (C (Counter.site ring root 1)).tok) := by
  by_cases hd : Counter.ResetClockBankDefectEntry ring C root e
  · simp [privateWaitingOutcome, hd] at hwait
  · by_cases hr : e = root ∧
        privateIncrementReturnToken
          (C (Counter.site ring root 1)).tok
    · by_cases hdr : Counter.ResetClockBankDefectEntry ring C root root <;>
        simp [privateWaitingOutcome, hd, hr, hdr] at hwait
    · by_cases hg : Counter.GrantFree
          ((protocol q).step ring C e) root
      · by_cases hm : (C root).mode = .IWAIT
        · by_cases hp : (e = root ∨
              ring.rightNeighbor e = root) ∧
              (C root).lease.val = 1
          · exact ⟨hp.1, hp.2, hr⟩
          · by_cases hn : (((protocol q).step ring C e) root).mode = .IWAIT <;>
              simp [privateWaitingOutcome, hd, hr, hg, hm, hp, hn] at hwait
        · simp [privateWaitingOutcome, hd, hr, hg, hm] at hwait
      · simp [privateWaitingOutcome, hd, hr, hg] at hwait

/-- The nominated service of an authenticated IWAIT front cannot
be a watchdog-failure edge. For IR, the source edge is strictly
interior; for AL(j>1), its predecessor is strictly interior; and
the AL(1) root edge is a matching return checked before lease loss. -/
theorem privateIWaitLossNotDesignated {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .IWAIT)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hwait : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C e = .waitLoss) :
    e ≠ privateIWaitDesignated ring root (C, .live) := by
  obtain ⟨hinc, _, hnotreturn⟩ :=
    privateIWaitLossIncidentLeaseOne ring root e C hwait
  obtain ⟨t, hw, htype⟩ :=
    privateIWaitFrontIndexSpec ring root C ha hm
  have htok :
      (C (Counter.site ring root
        (privateIWaitFrontIndex ring root C))).tok = t :=
    hw.2.2.1
  rcases htype with hir | hal
  · have htoken :
        (C (Counter.site ring root
          (privateIWaitFrontIndex ring root C))).tok = .IR :=
      htok.trans hir
    have hnotTop :
        privateIWaitFrontIndex ring root C <
          (compileAdvice q).b := by
      have hno := Counter.resetColdPrivateTopIRImpossible
        ring root C hwidth ha.1
      by_cases heq :
          privateIWaitFrontIndex ring root C =
            (compileAdvice q).b
      · have ht :
            (C (Counter.site ring root (compileAdvice q).b)).tok =
              .IR := by
          rw [← heq]
          exact htoken
        exact False.elim (hno ht)
      · have hjb := hw.2.1
        omega
    have havoid := Counter.resetClockInteriorEdgeNotRootIncident
      ring C root hc (privateIWaitFrontIndex ring root C)
      hw.1 (by omega)
    have hdes :
        privateIWaitDesignated ring root (C, .live) =
          Counter.site ring root
            (privateIWaitFrontIndex ring root C) := by
      simp [privateIWaitDesignated, htoken]
    intro he
    rw [hdes] at he
    rcases hinc with hs | ht
    · exact havoid.1 (he.symm.trans hs)
    · exact havoid.2
        ((congrArg ring.rightNeighbor he.symm).trans ht)
  · have htoken :
        (C (Counter.site ring root
          (privateIWaitFrontIndex ring root C))).tok = .AL :=
      htok.trans hal
    have hne :
        (C (Counter.site ring root
          (privateIWaitFrontIndex ring root C))).tok ≠ .IR := by
      rw [htoken]
      intro h
      cases h
    by_cases hone : privateIWaitFrontIndex ring root C = 1
    · have hdes :
          privateIWaitDesignated ring root (C, .live) =
            root := by
        have hne1 : (C (Counter.site ring root 1)).tok ≠ .IR := by
          rw [← hone]
          exact hne
        simp [privateIWaitDesignated, hne1, hone]
      intro he
      have hroot : e = root := he.trans hdes
      have halone :
          (C (Counter.site ring root 1)).tok = .AL := by
        rw [← hone]
        exact htoken
      exact hnotreturn
        ⟨hroot, by exact halone⟩
    · have hj1 := hw.1
      have hjb := hw.2.1
      have havoid := Counter.resetClockInteriorEdgeNotRootIncident
        ring C root hc
        (privateIWaitFrontIndex ring root C - 1)
        (by omega) (by omega)
      have hdes :
          privateIWaitDesignated ring root (C, .live) =
            Counter.site ring root
              (privateIWaitFrontIndex ring root C - 1) := by
        simp [privateIWaitDesignated, hne, hone]
      intro he
      rw [hdes] at he
      rcases hinc with hs | ht
      · exact havoid.1 (he.symm.trans hs)
      · exact havoid.2
          ((congrArg ring.rightNeighbor he.symm).trans ht)

/-- A watchdog failure uses one last nondesignated root incident.
This discharges the second half of PrivateIWaitRankLeaseRows from
the actual priority and spatial geometry, without a new assumption. -/
theorem privateIWaitFailureIsPenalty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    ∀ x : PrivateWaitingState q n, ∀ e : Fin n,
      PrivateIWaitComparisonGood ring root x →
      x.2 = .live →
      (privateWaitingNext ring root .IWAIT
        privateIncrementReturnToken x e).2 = .waitLoss →
      e ≠ privateIWaitDesignated ring root x ∧
      privateWaitingPenalty ring root
        (privateIWaitDesignated ring root) x e ∧
      privateIWaitRootLease root x = 1 := by
  intro x e hg hl hw
  obtain ⟨ha, hc, hm⟩ := hg hl
  have hclass :
      privateWaitingOutcome ring root .IWAIT
        privateIncrementReturnToken x.1 e = .waitLoss := by
    cases x with
    | mk C state =>
        cases state <;> simp [privateWaitingNext] at hl hw ⊢ <;> exact hw
  obtain ⟨hincident, hlease, _⟩ :=
    privateIWaitLossIncidentLeaseOne ring root e x.1 hclass
  have hnot :=
    privateIWaitLossNotDesignated ring root e x.1
      ha hc hm hwidth hclass
  exact ⟨hnot, ⟨hincident, hnot⟩, hlease⟩

/-- After the explicit terminal row is closed, only the three LIVE
rank/lease cases remain as physical obligations. Their conjunction
is enough to discharge the original PrivateIWaitRankLeaseRows. -/
def PrivateIWaitLiveRankLeaseRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ x : PrivateWaitingState q n, ∀ e : Fin n,
    PrivateIWaitComparisonGood ring root x →
    x.2 = .live →
    (privateWaitingNext ring root .IWAIT
      privateIncrementReturnToken x e).2 = .live →
    (e = privateIWaitDesignated ring root x →
      privateIWaitRank ring root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) + 1 ≤
        privateIWaitRank ring root x ∧
      privateIWaitRootLease root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) =
        privateIWaitRootLease root x) ∧
    (e ≠ privateIWaitDesignated ring root x →
      privateWaitingPenalty ring root
        (privateIWaitDesignated ring root) x e →
      privateIWaitRank ring root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) ≤
        privateIWaitRank ring root x ∧
      privateIWaitRootLease root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) + 1 =
        privateIWaitRootLease root x) ∧
    (e ≠ privateIWaitDesignated ring root x →
      ¬ privateWaitingPenalty ring root
        (privateIWaitDesignated ring root) x e →
      privateIWaitRank ring root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) ≤
        privateIWaitRank ring root x ∧
      privateIWaitRootLease root
        (privateWaitingNext ring root .IWAIT
          privateIncrementReturnToken x e) =
        privateIWaitRootLease root x)

theorem privateIWaitRankLeaseRowsOfLiveRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hrows : PrivateIWaitLiveRankLeaseRows (q := q) ring root) :
    PrivateIWaitRankLeaseRows (q := q) ring root :=
  ⟨hrows, privateIWaitFailureIsPenalty ring root hwidth⟩

/-- The remaining burden is now only a three-case LIVE physical
rank/lease calculation. No terminal waitLoss subcase remains. -/
theorem privateIncrementBoundedRarityOfLiveRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hrows : PrivateIWaitLiveRankLeaseRows (q := q) ring root) :
    PrivateIncrementBoundedRarity (q := q) ring root := by
  exact privateIncrementBoundedRarityOfRankRows ring root
    (privateIWaitRankLeaseRowsOfLiveRows ring root hwidth hrows)


end L3.CounterTrialLower

/-!
Exact physical IWAIT local rank/lease rows.
-/

namespace L3.CounterTrialLower

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- A physical single worker of type IR or AL has one unique
protected position. Proof does not impose a ghost scheduler. -/
private theorem privateIWaitWorkerPositionUnique {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (j k : Nat) (t u : BTok)
    (hj : Counter.resetColdPrivateOnlyWorker ring root C j t)
    (hk : Counter.resetColdPrivateOnlyWorker ring root C k u)
    (hu : Counter.resetColdPrivateCarryToken u) : j = k := by
  by_cases he : j = k
  · exact he
  · have hzero := hj.2.2.2 k hk.1 hk.2.1 (Ne.symm he)
    rw [hk.2.2.1] at hzero
    rcases hu with hu | hu
    · rw [hu] at hzero
      cases hzero
    · rw [hu] at hzero
      cases hzero

/-- A specialization with a known physical worker token; the
old index witness is recovered without supposing a second token. -/
theorem privateIWaitFrontIndexOfCarry {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (j : Nat) (t : BTok)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C j t)
    (ht : Counter.resetColdPrivateCarryToken t) :
    privateIWaitFrontIndex ring root C = j := by
  obtain ⟨u, hu, htype⟩ :=
    privateIWaitFrontIndexSpec ring root C ha hm
  exact privateIWaitWorkerPositionUnique ring root C
    (privateIWaitFrontIndex ring root C) j u t hu hw ht

/-- A known IR at j supplies the exact chosen rank and next edge. -/
theorem privateIWaitIRRankAt {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (j : Nat)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C j .IR) :
    privateIWaitRank ring root (C, .live) =
        2 * (compileAdvice q).b + 2 - j ∧
    privateIWaitDesignated ring root (C, .live) =
        Counter.site ring root j := by
  have hi := privateIWaitFrontIndexOfCarry ring root C j .IR
    ha hm hw (Or.inl rfl)
  constructor
  · unfold privateIWaitRank
    rw [hi, hw.2.2.1]
    simp
  · unfold privateIWaitDesignated
    rw [hi, hw.2.2.1]
    simp

/-- An AL at j has rank j and moves toward its predecessor,
or returns directly across root when j=1. -/
theorem privateIWaitALRankAt {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (j : Nat)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C j .AL) :
    privateIWaitRank ring root (C, .live) = j ∧
    privateIWaitDesignated ring root (C, .live) =
      (if j = 1 then root else Counter.site ring root (j - 1)) := by
  have hi := privateIWaitFrontIndexOfCarry ring root C j .AL
    ha hm hw (Or.inr rfl)
  constructor
  · unfold privateIWaitRank
    rw [hi, hw.2.2.1]
    simp
  · unfold privateIWaitDesignated
    rw [hi, hw.2.2.1]
    simp

/-- Every protected physical token survives a pointwise token frame,
including the unique front's position and type. -/
theorem privateIWaitOnlyWorkerFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Counter.Config q n) (j : Nat) (t : BTok)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C j t)
    (hf : ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (D (Counter.site ring root i)).tok =
        (C (Counter.site ring root i)).tok) :
    Counter.resetColdPrivateOnlyWorker ring root D j t := by
  refine ⟨hw.1, hw.2.1, ?_, ?_⟩
  · rw [hf j hw.1 hw.2.1]
    exact hw.2.2.1
  · intro i hi hib hine
    rw [hf i hi hib]
    exact hw.2.2.2 i hi hib hine

/-- All-digit token frame preserves the actual service rank.
The current front index is reidentified AFTER each physical step. -/
theorem privateIWaitRankTokenFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hd : Counter.ResetColdPrivateLiveShapeAuth ring root D)
    (hm : (C root).mode = .IWAIT)
    (hn : (D root).mode = .IWAIT)
    (hf : ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (D (Counter.site ring root i)).tok =
        (C (Counter.site ring root i)).tok) :
    privateIWaitRank ring root (D, .live) =
      privateIWaitRank ring root (C, .live) := by
  obtain ⟨j, t, hw, ht⟩ :=
    privateIWaitAuthenticatedFront ring root C ha hm
  have hwD := privateIWaitOnlyWorkerFrame
    ring root C D j t hw hf
  rcases ht with ht | ht
  · subst t
    rw [(privateIWaitIRRankAt ring root D j hd hn hwD).1,
      (privateIWaitIRRankAt ring root C j ha hm hw).1]
  · subst t
    rw [(privateIWaitALRankAt ring root D j hd hn hwD).1,
      (privateIWaitALRankAt ring root C j ha hm hw).1]

/-- Full unrelated-edge rank/lease frame. This is part (c) for
edges avoiding root and every protected digit at BOTH endpoints.
It is independent of the worker's phase and physical orientation. -/
theorem privateIWaitOutsideRankLeaseFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .IWAIT)
    (hout : Counter.OutsideSites q ring root e)
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C e = .live) :
    privateIWaitRank ring root
        ((protocol q).step ring C e, .live) =
      privateIWaitRank ring root (C, .live) ∧
    (((protocol q).step ring C e) root).lease.val =
      (C root).lease.val := by
  have hs := privateIWaitComparisonAuthStep ring root e C
    hsp hlarge hwidth ha hc hlive
  have hf : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (((protocol q).step ring C e)
        (Counter.site ring root i)).tok =
        (C (Counter.site ring root i)).tok := by
    intro i hi hib
    rw [Counter.outside_frame ring C root e hout i hib]
  have hroot := Counter.outside_frame ring C root e hout
    0 (by omega)
  change ((protocol q).step ring C e) root = C root at hroot
  exact ⟨privateIWaitRankTokenFrame ring root C
    ((protocol q).step ring C e) ha hs.1 hm hs.2.2 hf,
    congrArg (fun a : Agent (compileAdvice q) => a.lease.val)
      hroot⟩

/-- In an actual LIVE IWAIT outgoing-root service the first digit
is not a return token. A physical AL(1) would have already
completed the comparison before any waiting-lease test. -/
theorem privateIWaitRootLiveNoReturn {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT)
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C root = .live) :
    isRetTok (C (Counter.site ring root 1)).tok = false := by
  obtain ⟨j, t, hw, ht⟩ :=
    privateIWaitAuthenticatedFront ring root C ha hm
  by_cases hj : j = 1
  · rcases ht with hIR | hAL
    · have hfirst :
          (C (Counter.site ring root 1)).tok = .IR := by
        rw [← hj]
        exact hw.2.2.1.trans hIR
      rw [hfirst]
      rfl
    · have hfirst :
          (C (Counter.site ring root 1)).tok = .AL := by
        rw [← hj]
        exact hw.2.2.1.trans hAL
      have hnot := (privateIWaitComparisonLiveGuards
        ring root root C hlive).2.1
      exact False.elim (hnot ⟨rfl, by
        unfold privateIncrementReturnToken
        exact hfirst⟩)
  · have hb : 1 ≤ (compileAdvice q).b :=
      Nat.le_of_lt (Counter.resetTrialCompiledWidth q)
    have hfirst := hw.2.2.2 1 (by omega) hb (Ne.symm hj)
    rw [hfirst]
    rfl

/-- The exact physical lease tick on a still-LIVE root-incident
IWAIT service, including the OLD-lease>1 requirement. Nothing
outside the root's two incident edges can spend this lease. -/
theorem privateIWaitIncidentLiveLeaseTick {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .IWAIT)
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C e = .live)
    (hi : e = root ∨ ring.rightNeighbor e = root) :
    1 < (C root).lease.val ∧
    (((protocol q).step ring C e) root).lease.val + 1 =
      (C root).lease.val := by
  have hobs := privateIWaitComparisonLiveObserver
    ring root e C hlive
  have hg := Counter.resetColdPrivateLiveIncidentGrantFree
    ring root e C ((protocol q).step ring C e) true true
    hc hsp hi hobs
  have hnew := (privateIWaitComparisonLiveGuards
    ring root e C hlive).2.2.2.2
  rcases hi with he | hp
  · subst e
    have hnon := privateIWaitRootLiveNoReturn
      ring root C ha hm hlive
    have hrow := Counter.resetColdPhysicalWaitNonreturn
      ring C root hc hg hsp (by rw [hm]; rfl) hnon
    have hpositive : 1 < (C root).lease.val := by
      by_cases hval : 1 < (C root).lease.val
      · exact hval
      · have hreset :
            (((protocol q).step ring C root) root).mode =
              .RESET := by
          rw [hrow.1]
          simp [Counter.resetColdWaitTickMode, hval]
        rw [hnew] at hreset
        cases hreset
    constructor
    · exact hpositive
    · rw [hrow.2.1]
      simp only [Counter.resetColdWaitTickLease,
        if_pos hpositive]
      omega
  · have hnoDef := (privateIWaitComparisonLiveGuards
      ring root e C hlive).1
    have hrole := Counter.resetColdIncomingRoleOfNoDefect
      ring C root e hc hp hnoDef
    have hrow := Counter.resetColdPhysicalIncomingWait
      ring C root e hc hg hsp hp hrole
      (by rw [hm]; rfl)
    have hpositive : 1 < (C root).lease.val := by
      by_cases hval : 1 < (C root).lease.val
      · exact hval
      · have hreset :
            (((protocol q).step ring C e) root).mode =
              .RESET := by
          rw [hrow.1]
          simp [Counter.resetColdWaitTickMode, hval]
        rw [hnew] at hreset
        cases hreset
    constructor
    · exact hpositive
    · rw [hrow.2]
      simp only [Counter.resetColdWaitTickLease,
        if_pos hpositive]
      omega

/-- The actual LIVE root-incident waiting step frames EVERY
protected worker token. Its source/target can touch the root,
but not an interior carry or return worker; the outgoing-root
first-digit token is preserved by the literal nonreturn BANK row. -/
theorem privateIWaitIncidentLiveTokenFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .IWAIT)
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C e = .live)
    (hi : e = root ∨ ring.rightNeighbor e = root) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C e)
        (Counter.site ring root i)).tok =
        (C (Counter.site ring root i)).tok := by
  rcases hi with he | hp
  · subst e
    have hobs := privateIWaitComparisonLiveObserver
      ring root root C hlive
    have hg := Counter.resetColdPrivateLiveIncidentGrantFree
      ring root root C ((protocol q).step ring C root)
      true true hc hsp (Or.inl rfl) hobs
    have hnon := privateIWaitRootLiveNoReturn
      ring root C ha hm hlive
    have hrow := Counter.resetColdPhysicalWaitNonreturn
      ring C root hc hg hsp (by rw [hm]; rfl) hnon
    intro i hii hib
    by_cases hone : i = 1
    · subst i
      exact hrow.2.2
    · rw [Counter.resetColdOutgoingRootOtherDigitsFrame
        ring C root hc i (by omega) hib]
  · have hex := Counter.resetColdIncomingExteriorOfLarge
      ring C root e hc hlarge hp
    intro i hii hib
    exact congrArg (fun a : Agent (compileAdvice q) => a.tok)
      (Counter.resetColdIncomingRootDigitFrame
        ring C root e hc hp hex i hii hib)

/-- Root-incident LIVE services are genuine penalty services:
they preserve the physical service rank and spend exactly
one lease unit. This is the entire (b) row, with no assumption
about the particular IR/AL position. -/
theorem privateIWaitIncidentLiveRankLease {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .IWAIT)
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C e = .live)
    (hi : e = root ∨ ring.rightNeighbor e = root) :
    privateIWaitRank ring root
        ((protocol q).step ring C e, .live) =
      privateIWaitRank ring root (C, .live) ∧
    (((protocol q).step ring C e) root).lease.val + 1 =
      (C root).lease.val := by
  have hs := privateIWaitComparisonAuthStep ring root e C
    hsp hlarge hwidth ha hc hlive
  have hf := privateIWaitIncidentLiveTokenFrame ring root e C
    hsp hlarge ha hc hm hlive hi
  have hr := privateIWaitRankTokenFrame ring root C
    ((protocol q).step ring C e) ha hs.1 hm hs.2.2 hf
  exact ⟨hr, (privateIWaitIncidentLiveLeaseTick
    ring root e C hsp hlarge ha hc hm hlive hi).2⟩



/-- Exact physical token frame on an interior empty/AL-source
hold pair, including all unselected protected digits. -/
theorem privateIWaitInteriorHoldTokenFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (ht : (C (Counter.site ring root j)).tok = .E ∨
      (C (Counter.site ring root j)).tok = .AL)
    (he : (C (Counter.site ring root (j + 1))).tok = .E) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C
        (Counter.site ring root j))
        (Counter.site ring root i)).tok =
      (C (Counter.site ring root i)).tok := by
  have hbankRaw := Counter.resetColdPrivateInteriorHoldBank
    (bankCell (C (Counter.site ring root j)) j)
    (bankCell (C (Counter.site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by
      change (C (Counter.site ring root j)).tok = .E ∨
        (C (Counter.site ring root j)).tok = .AL ∨
        (C (Counter.site ring root j)).tok = .CL0 ∨
        (C (Counter.site ring root j)).tok = .CL1
      rcases ht with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh))
    (by change (C (Counter.site ring root (j + 1))).tok = .E
        exact he)
  have hbank :
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.tok =
        (C (Counter.site ring root j)).tok ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (Counter.site ring root j)).bit ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (C (Counter.site ring root (j + 1))).tok ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (Counter.site ring root (j + 1))).bit := by
    unfold Counter.resetColdPrivateInteriorBankAt
    simpa only [bankCell] using hbankRaw
  have hf := Counter.resetColdPrivateInteriorRowFields ring root C
    hc hsp j hj hjb
    (C (Counter.site ring root j)).tok
    (C (Counter.site ring root (j + 1))).tok
    (C (Counter.site ring root j)).bit
    (C (Counter.site ring root (j + 1))).bit hbank
  intro i hi hib
  by_cases hleft : i = j
  · subst i
    exact hf.1
  · by_cases hright : i = j + 1
    · subst i
      exact hf.2.2.1
    · rw [Counter.resetColdPrivateInteriorOtherFrame
        ring root C hc j hj hjb i hi hib hleft hright]

/-- Exact interior responder-IR hold: it does not advance IR
backward. The top responder is excluded by the authenticated
numerical head in the later application. -/
theorem privateIWaitInteriorResponderIRFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (hntop : j + 1 ≠ (compileAdvice q).b)
    (he : (C (Counter.site ring root j)).tok = .E)
    (ht : (C (Counter.site ring root (j + 1))).tok = .IR) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C
        (Counter.site ring root j))
        (Counter.site ring root i)).tok =
      (C (Counter.site ring root i)).tok := by
  have hraw := Counter.resetColdPrivateInteriorResponderHoldBank
    (bankCell (C (Counter.site ring root j)) j)
    (bankCell (C (Counter.site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl (by change j + 1 ≠ (compileAdvice q).b; exact hntop)
    (by change (C (Counter.site ring root j)).tok = .E; exact he)
    (by
      change (C (Counter.site ring root (j + 1))).tok = .IR ∨
        (C (Counter.site ring root (j + 1))).tok = .CR0 ∨
        (C (Counter.site ring root (j + 1))).tok = .CR1
      exact Or.inl ht)
  have hbank :
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.tok =
        (C (Counter.site ring root j)).tok ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (Counter.site ring root j)).bit ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (C (Counter.site ring root (j + 1))).tok ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (Counter.site ring root (j + 1))).bit := by
    unfold Counter.resetColdPrivateInteriorBankAt
    simpa only [bankCell] using hraw
  have hf := Counter.resetColdPrivateInteriorRowFields ring root C
    hc hsp j hj hjb
    (C (Counter.site ring root j)).tok
    (C (Counter.site ring root (j + 1))).tok
    (C (Counter.site ring root j)).bit
    (C (Counter.site ring root (j + 1))).bit hbank
  intro i hi hib
  by_cases hleft : i = j
  · subst i
    exact hf.1
  · by_cases hright : i = j + 1
    · subst i
      exact hf.2.2.1
    · rw [Counter.resetColdPrivateInteriorOtherFrame
        ring root C hc j hj hjb i hi hib hleft hright]

/-- All actual non-designated interior services frame every
protected token, regardless of whether the unique IR/AL worker
is at their source, their responder, or elsewhere. -/
theorem privateIWaitInteriorNondesignatedTokenFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (hnot : Counter.site ring root j ≠
      privateIWaitDesignated ring root (C, .live)) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C (Counter.site ring root j))
        (Counter.site ring root i)).tok =
        (C (Counter.site ring root i)).tok := by
  obtain ⟨k, t, hw, ht⟩ :=
    privateIWaitAuthenticatedFront ring root C ha hm
  by_cases hs : k = j
  · subst k
    rcases ht with hir | hal
    · have he := (privateIWaitIRRankAt ring root C j ha hm
        (by rw [hir] at hw; exact hw)).2
      exact False.elim (hnot (he.symm))
    · have hwAL :
          Counter.resetColdPrivateOnlyWorker ring root C j .AL := by
        rw [hal] at hw
        exact hw
      have hdest := hwAL.2.2.2 (j + 1)
        (by omega) (by omega) (by omega)
      exact privateIWaitInteriorHoldTokenFrame ring root C
        hc hsp j hj hjb (Or.inr hwAL.2.2.1) hdest
  · by_cases hd : k = j + 1
    · rcases ht with hir | hal
      · have hwIR :
            Counter.resetColdPrivateOnlyWorker ring root C k .IR := by
          rw [hir] at hw
          exact hw
        have he : (C (Counter.site ring root j)).tok = .E :=
          hwIR.2.2.2 j hj (by omega) (by omega)
        have htop : j + 1 ≠ (compileAdvice q).b := by
          intro hh
          have hIRTop :
              (C (Counter.site ring root
                (compileAdvice q).b)).tok = .IR := by
            rw [← hh, ← hd]
            exact hwIR.2.2.1
          exact Counter.resetColdPrivateTopIRImpossible
            ring root C hwidth ha.1 hIRTop
        have htgt :
            (C (Counter.site ring root (j + 1))).tok = .IR := by
          rw [← hd]
          exact hwIR.2.2.1
        exact privateIWaitInteriorResponderIRFrame
          ring root C hc hsp j hj hjb htop he htgt
      · have hwAL :
            Counter.resetColdPrivateOnlyWorker ring root C k .AL := by
          rw [hal] at hw
          exact hw
        have heq : k - 1 = j := by omega
        have hdes := (privateIWaitALRankAt
          ring root C k ha hm hwAL).2
        have hk : k ≠ 1 := by omega
        rw [if_neg hk, heq] at hdes
        exact False.elim (hnot hdes.symm)
    · have hemptySource :=
        hw.2.2.2 j hj (by omega) (Ne.symm hs)
      have hemptyTarget :=
        hw.2.2.2 (j + 1) (by omega) (by omega) (Ne.symm hd)
      exact privateIWaitInteriorHoldTokenFrame
        ring root C hc hsp j hj hjb
        (Or.inl hemptySource) hemptyTarget

/-- Part (c) for an internal nonproductive selected edge:
the rank is exactly preserved and the physical root lease
is framed because neither endpoint touches the root. -/
theorem privateIWaitInteriorNondesignatedRankLease {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .IWAIT)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (hnot : Counter.site ring root j ≠
      privateIWaitDesignated ring root (C, .live))
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C
        (Counter.site ring root j) = .live) :
    privateIWaitRank ring root
        ((protocol q).step ring C (Counter.site ring root j), .live) =
      privateIWaitRank ring root (C, .live) ∧
    (((protocol q).step ring C
      (Counter.site ring root j)) root).lease.val =
      (C root).lease.val := by
  have hf := privateIWaitInteriorNondesignatedTokenFrame
    ring root C hc hsp hwidth ha hm j hj hjb hnot
  have hnew := privateIWaitComparisonAuthStep ring root
    (Counter.site ring root j) C hsp hlarge hwidth
    ha hc hlive
  have hport := Counter.resetClockInteriorEdgeNotRootIncident
    ring C root hc j hj hjb
  exact ⟨privateIWaitRankTokenFrame ring root C
      ((protocol q).step ring C (Counter.site ring root j))
      ha hnew.1 hm hnew.2.2 hf,
    privateIncrementNonincidentLeaseFrame ring root
      (Counter.site ring root j) C hport.1 hport.2⟩



/-- A designated IR service on the actual interior protocol edge
leaves a single protected worker at the next digit, with token IR
or AL according to its OLD bit. This exact token motion is the
missing refinement beyond the existing Auth-only source theorem. -/
theorem privateIWaitIRForwardWorker {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C j .IR) :
    Counter.resetColdPrivateOnlyWorker ring root
      ((protocol q).step ring C (Counter.site ring root j))
      (j + 1)
      (if (C (Counter.site ring root (j + 1))).bit
        then .IR else .AL) := by
  have hempty :
      (C (Counter.site ring root (j + 1))).tok = .E :=
    hw.2.2.2 (j + 1) (by omega) (by omega) (by omega)
  have hraw := Counter.resetColdPrivateIRForwardBank
    (bankCell (C (Counter.site ring root j)) j)
    (bankCell (C (Counter.site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change (C (Counter.site ring root j)).tok = .IR
        exact hw.2.2.1)
    (by change (C (Counter.site ring root (j + 1))).tok = .E
        exact hempty)
  have hbank :
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.tok =
        .E ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (Counter.site ring root j)).bit ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (if (C (Counter.site ring root (j + 1))).bit
          then BTok.IR else BTok.AL) ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.bit =
        !(C (Counter.site ring root (j + 1))).bit := by
    unfold Counter.resetColdPrivateInteriorBankAt
    exact hraw
  have hf := Counter.resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb
    .E
    (if (C (Counter.site ring root (j + 1))).bit
      then BTok.IR else BTok.AL)
    (C (Counter.site ring root j)).bit
    (!(C (Counter.site ring root (j + 1))).bit)
    hbank
  exact Counter.resetColdPrivateInteriorWorkerForward
    ring root C hc j hj hjb .IR
      (if (C (Counter.site ring root (j + 1))).bit
        then BTok.IR else BTok.AL)
    hw hf.1 hf.2.2.1

/-- A designated AL retreat is the actual physical inverse
transport of the sole worker from j+1 back to j. -/
theorem privateIWaitALBackwardWorker {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C
      (j + 1) .AL) :
    Counter.resetColdPrivateOnlyWorker ring root
      ((protocol q).step ring C (Counter.site ring root j))
      j .AL := by
  have hempty : (C (Counter.site ring root j)).tok = .E :=
    hw.2.2.2 j hj (by omega) (by omega)
  have hraw := Counter.resetColdPrivateALRetreatBank
    (bankCell (C (Counter.site ring root j)) j)
    (bankCell (C (Counter.site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change (C (Counter.site ring root j)).tok = .E
        exact hempty)
    (by change (C (Counter.site ring root (j + 1))).tok = .AL
        exact hw.2.2.1)
  have hbank :
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.tok =
        .AL ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (Counter.site ring root j)).bit ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.tok =
        .E ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (Counter.site ring root (j + 1))).bit := by
    unfold Counter.resetColdPrivateInteriorBankAt
    have hr := hraw
    simp only [bankCell] at hr ⊢
    exact ⟨hr.1, hr.2.2.1, hr.2.1, hr.2.2.2⟩
  have hf := Counter.resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb .AL .E
    (C (Counter.site ring root j)).bit
    (C (Counter.site ring root (j + 1))).bit hbank
  exact Counter.resetColdPrivateInteriorWorkerBackward
    ring root C hc j hj hjb .AL .AL
    hw hf.1 hf.2.2.1

/-- The REAL designated service strictly decreases the natural
service rank and frames the root lease. An AL at digit one is
a completed return, so it cannot have a LIVE comparison successor. -/
theorem privateIWaitDesignatedLiveRankLease {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .IWAIT)
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C e = .live)
    (he : e = privateIWaitDesignated ring root (C, .live)) :
    privateIWaitRank ring root
        ((protocol q).step ring C e, .live) + 1 ≤
      privateIWaitRank ring root (C, .live) ∧
    (((protocol q).step ring C e) root).lease.val =
      (C root).lease.val := by
  obtain ⟨j, t, hw, ht⟩ :=
    privateIWaitAuthenticatedFront ring root C ha hm
  have hs := privateIWaitComparisonAuthStep ring root e C
    hsp hlarge hwidth ha hc hlive
  rcases ht with hir | hal
  · have hwIR :
        Counter.resetColdPrivateOnlyWorker ring root C j .IR := by
      rw [hir] at hw
      exact hw
    have hold := privateIWaitIRRankAt ring root C j ha hm hwIR
    have hjb : j < (compileAdvice q).b := by
      have htop := Counter.resetColdPrivateTopIRImpossible
        ring root C hwidth ha.1
      by_cases hj : j = (compileAdvice q).b
      · have htoken :
            (C (Counter.site ring root (compileAdvice q).b)).tok =
              .IR := by
          rw [← hj]
          exact hwIR.2.2.1
        exact False.elim (htop htoken)
      · have hjle := hwIR.2.1
        omega
    have hedge : e = Counter.site ring root j := he.trans hold.2
    have hport := Counter.resetClockInteriorEdgeNotRootIncident
      ring C root hc j hwIR.1 hjb
    have hlease :
        (((protocol q).step ring C e) root).lease.val =
          (C root).lease.val := by
      rw [hedge]
      exact privateIncrementNonincidentLeaseFrame ring root
        (Counter.site ring root j) C hport.1 hport.2
    have hworker := privateIWaitIRForwardWorker ring root C
      hc hsp j hwIR.1 hjb hwIR
    have hafter : Counter.ResetColdPrivateLiveShapeAuth ring root
        ((protocol q).step ring C (Counter.site ring root j)) := by
      rw [← hedge]
      exact hs.1
    have hmode :
        (((protocol q).step ring C
          (Counter.site ring root j)) root).mode = .IWAIT := by
      rw [← hedge]
      exact hs.2.2
    by_cases hbit : (C (Counter.site ring root (j + 1))).bit
    · have hnewIR :
          Counter.resetColdPrivateOnlyWorker ring root
            ((protocol q).step ring C (Counter.site ring root j))
            (j + 1) .IR := by
        simpa [hbit] using hworker
      have hnew := (privateIWaitIRRankAt ring root
        ((protocol q).step ring C (Counter.site ring root j))
        (j + 1) hafter hmode hnewIR).1
      constructor
      · rw [hedge, hnew, hold.1]
        omega
      · exact hlease
    · have hnewAL :
          Counter.resetColdPrivateOnlyWorker ring root
            ((protocol q).step ring C (Counter.site ring root j))
            (j + 1) .AL := by
        simp [hbit] at hworker
        exact hworker
      have hnew := (privateIWaitALRankAt ring root
        ((protocol q).step ring C (Counter.site ring root j))
        (j + 1) hafter hmode hnewAL).1
      constructor
      · rw [hedge, hnew, hold.1]
        omega
      · exact hlease
  · have hwAL :
        Counter.resetColdPrivateOnlyWorker ring root C j .AL := by
      rw [hal] at hw
      exact hw
    have hold := privateIWaitALRankAt ring root C j ha hm hwAL
    have hjAL1 := hwAL.1
    have hjALb := hwAL.2.1
    by_cases hj : j = 1
    · have hdes : privateIWaitDesignated ring root (C, .live) =
          root := by rw [hold.2, hj]; rfl
      have heRoot : e = root := he.trans hdes
      have hfirst :
          (C (Counter.site ring root 1)).tok = .AL := by
        rw [← hj]
        exact hwAL.2.2.1
      have hnot := (privateIWaitComparisonLiveGuards
        ring root e C hlive).2.1
      exact False.elim (hnot ⟨heRoot, by
        unfold privateIncrementReturnToken
        exact hfirst⟩)
    · have hk : 1 ≤ j - 1 := by omega
      have hkb : j - 1 < (compileAdvice q).b := by omega
      have hsum : j - 1 + 1 = j := by omega
      have hpre :
          privateIWaitDesignated ring root (C, .live) =
            Counter.site ring root (j - 1) := by
        rw [hold.2, if_neg hj]
      have hedge : e = Counter.site ring root (j - 1) :=
        he.trans hpre
      have hport := Counter.resetClockInteriorEdgeNotRootIncident
        ring C root hc (j - 1) hk hkb
      have hlease :
          (((protocol q).step ring C e) root).lease.val =
            (C root).lease.val := by
        rw [hedge]
        exact privateIncrementNonincidentLeaseFrame ring root
          (Counter.site ring root (j - 1)) C hport.1 hport.2
      have hwpre :
          Counter.resetColdPrivateOnlyWorker ring root C
            (j - 1 + 1) .AL := by
        rw [hsum]
        exact hwAL
      have hworker := privateIWaitALBackwardWorker ring root C
        hc hsp (j - 1) hk hkb hwpre
      have hafter : Counter.ResetColdPrivateLiveShapeAuth ring root
          ((protocol q).step ring C
            (Counter.site ring root (j - 1))) := by
        rw [← hedge]
        exact hs.1
      have hmode :
          (((protocol q).step ring C
            (Counter.site ring root (j - 1))) root).mode = .IWAIT := by
        rw [← hedge]
        exact hs.2.2
      have hnew := (privateIWaitALRankAt ring root
        ((protocol q).step ring C (Counter.site ring root (j - 1)))
        (j - 1) hafter hmode hworker).1
      constructor
      · rw [hedge, hnew, hold.1]
        omega
      · exact hlease



/-- A top-source token row keeps a non-IR token whichever branch
the role comparison takes. Stated on plain BTok values (rewriting
the if inside configuration terms fails). -/
private theorem topSourceIteKeep (P : Prop) [Decidable P] (t : BTok)
    (h : t ≠ .IR) :
    (if P then (if t = .IR then BTok.E else t) else t) = t := by
  by_cases hp : P
  · rw [if_pos hp, if_neg h]
  · rw [if_neg hp]

/-- The physical top-source service preserves all protected
IWAIT worker tokens. Auth and the compiled head-width rule exclude
IR at the top, which is the ONLY token erased by this BANK row. -/
theorem privateIWaitTopSourceTokenFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C
        (Counter.site ring root (compileAdvice q).b))
        (Counter.site ring root i)).tok =
      (C (Counter.site ring root i)).tok := by
  have hb : 0 < (compileAdvice q).b := by
    have hh := Counter.resetTrialCompiledWidth q
    omega
  have hn : 2 ≤ n := by
    have hh : 2 * (13 * ((compileAdvice q).b + 2)) ≤ n := by
      simpa only [Compiled.bankLeaseCap] using hlarge
    omega
  have hne :
      ring.rightNeighbor
        (Counter.site ring root (compileAdvice q).b) ≠
        Counter.site ring root (compileAdvice q).b :=
    Counter.resetRootPortDistinct ring
      (Counter.site ring root (compileAdvice q).b) hn
  have hrole :
      (C (Counter.site ring root (compileAdvice q).b)).pack.val =
        (compileAdvice q).b := hc (compileAdvice q).b (by omega)
  have hnotIR :
      (C (Counter.site ring root (compileAdvice q).b)).tok ≠
        .IR := by
    intro ht
    exact Counter.resetColdPrivateTopIRImpossible
      ring root C hwidth ha.1 ht
  have hraw := Counter.resetColdBankTopSourceToken
    (bankCell (C (Counter.site ring root (compileAdvice q).b))
      (C (Counter.site ring root (compileAdvice q).b)).pack.val)
    (bankCell (C (Counter.site ring root ((compileAdvice q).b + 1)))
      (C (Counter.site ring root ((compileAdvice q).b + 1))).pack.val)
    (packNext
      (C (Counter.site ring root (compileAdvice q).b)).pack.val
      (C (Counter.site ring root ((compileAdvice q).b + 1))).pack.val
      (compileAdvice q).b)
    (compileAdvice q).b (compileAdvice q).theta
    hrole hb
  have hbank :
      (Counter.resetBankOld
        (C (Counter.site ring root (compileAdvice q).b))
        (C (Counter.site ring root ((compileAdvice q).b + 1)))).1.tok =
        (C (Counter.site ring root (compileAdvice q).b)).tok := by
    have hkeep := hraw.trans (topSourceIteKeep _ _ hnotIR)
    simpa only [Counter.resetBankOld, bankCell] using hkeep
  have htrip := Counter.resetPhysicalEdgeBankTrip ring C
    (Counter.site ring root (compileAdvice q).b) hne hsp
  have htop :
      (((protocol q).step ring C
        (Counter.site ring root (compileAdvice q).b))
        (Counter.site ring root (compileAdvice q).b)).tok =
      (C (Counter.site ring root (compileAdvice q).b)).tok :=
    (congrArg (fun z : Mode × Bool × BTok => z.2.2)
      htrip.1).trans hbank
  intro i hi hib
  by_cases hlast : i = (compileAdvice q).b
  · subst i
    exact htop
  · exact congrArg
      (fun a : Agent (compileAdvice q) => a.tok)
      (Counter.resetColdPrivateTopSourceLowerFrame
        ring root C hc i hi (by omega))

/-- This completes the rank and lease frame on the top source.
In contrast, an unbounded isolated IWAIT configuration can have
IR at the top, where the source really erases the only worker. -/
theorem privateIWaitTopSourceRankLeaseFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT)
    (hlive : privateWaitingOutcome ring root .IWAIT
      privateIncrementReturnToken C
        (Counter.site ring root (compileAdvice q).b) = .live) :
    privateIWaitRank ring root
        ((protocol q).step ring C
          (Counter.site ring root (compileAdvice q).b), .live) =
      privateIWaitRank ring root (C, .live) ∧
    (((protocol q).step ring C
      (Counter.site ring root (compileAdvice q).b)) root).lease.val =
      (C root).lease.val := by
  have hnew := privateIWaitComparisonAuthStep ring root
    (Counter.site ring root (compileAdvice q).b)
    C hsp hlarge hwidth ha hc hlive
  have hf := privateIWaitTopSourceTokenFrame ring root C
    hc hsp hlarge hwidth ha
  have hroot := Counter.resetColdTopRootPhysicalFrame
    ring C root hc hlarge
  exact ⟨privateIWaitRankTokenFrame ring root C
      ((protocol q).step ring C
        (Counter.site ring root (compileAdvice q).b))
      ha hnew.1 hm hnew.2.2 hf,
    congrArg (fun a : Agent (compileAdvice q) => a.lease.val)
      hroot⟩



/-- The three LIVE rank/lease rows hold for the literal
physical IWAIT worker in the large-ring Auth domain. Every edge
is classified by the existing source geometry: protected source,
incoming root, or completely exterior. The final AL(1) return is
not LIVE. -/
theorem privateIWaitLiveRankLeaseRowsPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    PrivateIWaitLiveRankLeaseRows (q := q) ring root := by
  intro x e hg hx hn
  cases x with
  | mk C s =>
      cases s with
      | live =>
          obtain ⟨ha, hc, hm⟩ := hg rfl
          have hout :
              privateWaitingOutcome ring root .IWAIT
                privateIncrementReturnToken C e = .live := hn
          have hp :
              privateWaitingNext ring root .IWAIT
                privateIncrementReturnToken (C, .live) e =
              ((protocol q).step ring C e, .live) := by
            change ((protocol q).step ring C e,
              privateWaitingOutcome ring root .IWAIT
                privateIncrementReturnToken C e) =
              ((protocol q).step ring C e, .live)
            rw [hout]
          constructor
          · intro hd
            have hh := privateIWaitDesignatedLiveRankLease
              ring root e C hsp hlarge hwidth
              ha hc hm hout hd
            rw [hp]
            exact hh
          · constructor
            · intro hd hpen
              have hh := privateIWaitIncidentLiveRankLease
                ring root e C hsp hlarge hwidth
                ha hc hm hout hpen.1
              rw [hp]
              exact ⟨Nat.le_of_eq hh.1, hh.2⟩
            · intro hd hnp
              have hni :
                  ¬ (e = root ∨ ring.rightNeighbor e = root) := by
                intro hi
                exact hnp ⟨hi, hd⟩
              rcases Counter.resetTrialEdgeGeometry (q := q)
                  ring root e with hsite | hinc | houtside
              · obtain ⟨j, hjb, he⟩ := hsite
                subst e
                by_cases hz : j = 0
                · subst j
                  exact False.elim (hni (Or.inl rfl))
                · have hj : 1 ≤ j := by omega
                  by_cases htop : j = (compileAdvice q).b
                  · subst j
                    have hh := privateIWaitTopSourceRankLeaseFrame
                      ring root C hc hsp hlarge hwidth
                      ha hm hout
                    rw [hp]
                    exact ⟨Nat.le_of_eq hh.1, hh.2⟩
                  · have hlt : j < (compileAdvice q).b := by
                      omega
                    have hh :=
                      privateIWaitInteriorNondesignatedRankLease
                        ring root C hsp hlarge hwidth
                        ha hc hm j hj hlt hd hout
                    rw [hp]
                    exact ⟨Nat.le_of_eq hh.1, hh.2⟩
              · exact False.elim (hni (Or.inr hinc))
              · have hh := privateIWaitOutsideRankLeaseFrame
                  ring root e C hsp hlarge hwidth ha hc hm
                  houtside hout
                rw [hp]
                exact ⟨Nat.le_of_eq hh.1, hh.2⟩
      | completed =>
          cases hx
      | waitLoss =>
          cases hx
      | grant =>
          cases hx
      | defect =>
          cases hx
      | aborted =>
          cases hx

/-- Exact C.1 fraction, no unproved live-step premise: the
repaired bounded isolated IWAIT comparison has the physical
Lambda-L penalty tail. This theorem uses the original finite
scheduler and all live nonreset protocol services. -/
theorem privateIncrementBoundedRarityPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    PrivateIncrementBoundedRarity (q := q) ring root := by
  intro hlarge o T
  have hrows : PrivateIWaitLiveRankLeaseRows (q := q) ring root :=
    privateIWaitLiveRankLeaseRowsPhysical ring root
      hsp hlarge hwidth
  have hh := privateIncrementBoundedRarityOfLiveRows
    ring root hwidth hrows
  exact hh hlarge o T


end L3.CounterTrialLower


/-!
CWAIT authenticated comparison front and failure-edge closure.

The comparator differs from the increment: the highest CR front
turns into CL via its PREDECESSOR edge; CL0/CL1 at digit 1
returns at the root, and CL1 is a real observer success.
-/

namespace L3.CounterTrialLower

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-! A LIVE CWAIT letter passes every actual physical guard. -/
theorem privateCWaitComparisonLiveGuards {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C e = .live) :
    ¬ Counter.ResetClockBankDefectEntry ring C root e ∧
    ¬ (e = root ∧
      privateComparatorReturnToken
        (C (Counter.site ring root 1)).tok) ∧
    Counter.GrantFree ((protocol q).step ring C e) root ∧
    (C root).mode = .CWAIT ∧
    (((protocol q).step ring C e) root).mode = .CWAIT := by
  by_cases hd : Counter.ResetClockBankDefectEntry ring C root e
  · simp [privateWaitingOutcome, hd] at hlive
  · by_cases hr : e = root ∧
        privateComparatorReturnToken
          (C (Counter.site ring root 1)).tok
    · by_cases hdr : Counter.ResetClockBankDefectEntry ring C root root <;>
        simp [privateWaitingOutcome, hd, hr, hdr] at hlive
    · by_cases hg : Counter.GrantFree
          ((protocol q).step ring C e) root
      · by_cases hm : (C root).mode = .CWAIT
        · by_cases hp : (e = root ∨
              ring.rightNeighbor e = root) ∧
              (C root).lease.val = 1
          · simp [privateWaitingOutcome, hd, hr, hg, hm, hp] at hlive
          · by_cases hn :
                (((protocol q).step ring C e) root).mode = .CWAIT
            · exact ⟨hd, hr, hg, hm, hn⟩
            · simp [privateWaitingOutcome, hd, hr, hg, hm,
                hp, hn] at hlive
        · simp [privateWaitingOutcome, hd, hr, hg, hm] at hlive
      · simp [privateWaitingOutcome, hd, hr, hg] at hlive

/-! Unlike IWAIT, a real CWAIT success is possible, but it is
precisely the forbidden root/CL1 return. -/
theorem privateCWaitComparisonLiveObserver {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C e = .live) :
    Counter.resetColdLatchedPrivateNext ring root
      (.live C true) e =
      .live ((protocol q).step ring C e) true := by
  obtain ⟨hdef, hreturn, _, hold, hnew⟩ :=
    privateCWaitComparisonLiveGuards ring root e C hlive
  have hnSuccess : ¬ Counter.resetColdPrivateSuccessAt
      ring root C e := by
    intro hs
    have he := Counter.resetColdPrivateSuccessOutgoing
      ring root e C hs
    have ht := Counter.resetColdPrivateSuccessFirstCL1
      ring root e C hs
    apply hreturn
    exact ⟨he, Or.inr ht⟩
  have hnClean : ¬ Counter.ResetClockBankClean ring
      ((protocol q).step ring C e) root := by
    intro hc
    have hm := hc.2.1
    rw [hnew] at hm
    cases hm
  have hnAbort : ¬ Counter.resetColdLatchedAbort
      ring root C e := by
    intro ha
    rcases ha with hi | hr
    · rw [hold] at hi
      cases hi.1
    · rw [hnew] at hr
      cases hr
  have hbegun : Counter.resetColdLatchedBegun ring root e true :=
    Or.inl rfl
  simp only [Counter.resetColdLatchedPrivateNext,
    if_neg hdef, if_neg hnSuccess, if_pos hbegun,
    if_neg hnClean, if_neg hnAbort]

theorem privateCWaitComparisonAuthStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C e = .live) :
    Counter.ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C e) ∧
    Counter.Complete ring ((protocol q).step ring C e) root ∧
    (((protocol q).step ring C e) root).mode = .CWAIT := by
  have hobs := privateCWaitComparisonLiveObserver
    ring root e C hlive
  have haStep := Counter.resetColdPrivateLiveAuthStep
    ring root e C ((protocol q).step ring C e)
    true true hc hsp hlarge hwidth ha hobs
  have hcStep := Counter.resetColdPrivateLiveCompleteStep
    ring root e C ((protocol q).step ring C e)
    true true hc hobs
  have hmStep :=
    (privateCWaitComparisonLiveGuards ring root e C hlive).2.2.2.2
  exact ⟨haStep.1, hcStep, hmStep⟩

theorem privateCWaitComparisonWordAbsorbing {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : PrivateWaitingState q n)
    (hz : z.2 ≠ .live) (w : List (Fin n)) :
    privateWaitingWord ring root .CWAIT
      privateComparatorReturnToken w z = z := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      change privateWaitingWord ring root .CWAIT
        privateComparatorReturnToken w
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken z e) = z
      have hnext : privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken z e = z := by
        cases z with
        | mk C s =>
            cases s <;> simp [privateWaitingNext] at hz ⊢
      rw [hnext]
      exact ih

theorem privateCWaitComparisonAuthWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    ∀ (C : Counter.Config q n) (w : List (Fin n)),
      Counter.ResetColdPrivateLiveShapeAuth ring root C →
      Counter.Complete ring C root →
      (C root).mode = .CWAIT →
      (privateWaitingWord ring root .CWAIT
        privateComparatorReturnToken w (C, .live)).2 = .live →
      Counter.ResetColdPrivateLiveShapeAuth ring root
        (privateWaitingWord ring root .CWAIT
          privateComparatorReturnToken w (C, .live)).1 ∧
      Counter.Complete ring
        (privateWaitingWord ring root .CWAIT
          privateComparatorReturnToken w (C, .live)).1 root ∧
      ((privateWaitingWord ring root .CWAIT
          privateComparatorReturnToken w (C, .live)).1 root).mode =
        .CWAIT := by
  intro C w
  induction w generalizing C with
  | nil =>
      intro ha hc hm _
      exact ⟨ha, hc, hm⟩
  | cons e w ih =>
      intro ha hc hm hresult
      have hstep :
          (privateWaitingNext ring root .CWAIT
            privateComparatorReturnToken (C, .live) e).2 =
            .live := by
        by_cases hl :
            (privateWaitingNext ring root .CWAIT
              privateComparatorReturnToken (C, .live) e).2 = .live
        · exact hl
        · have hstay :=
            privateCWaitComparisonWordAbsorbing ring root
              (privateWaitingNext ring root .CWAIT
                privateComparatorReturnToken (C, .live) e)
              hl w
          change (privateWaitingWord ring root .CWAIT
              privateComparatorReturnToken w
              (privateWaitingNext ring root .CWAIT
                privateComparatorReturnToken (C, .live) e)).2 =
              .live at hresult
          rw [hstay] at hresult
          exact False.elim (hl hresult)
      have hout :
          privateWaitingOutcome ring root .CWAIT
            privateComparatorReturnToken C e = .live := hstep
      have hnext :=
        privateCWaitComparisonAuthStep ring root e C
          hsp hlarge hwidth ha hc hout
      have hpair :
          privateWaitingNext ring root .CWAIT
            privateComparatorReturnToken (C, .live) e =
            ((protocol q).step ring C e, .live) := by
        change ((protocol q).step ring C e,
          privateWaitingOutcome ring root .CWAIT
            privateComparatorReturnToken C e) =
            ((protocol q).step ring C e, .live)
        rw [hout]
      change (privateWaitingWord ring root .CWAIT
        privateComparatorReturnToken w
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken (C, .live) e)).2 =
          .live at hresult
      rw [hpair] at hresult
      have hword :
          privateWaitingWord ring root .CWAIT
              privateComparatorReturnToken (e :: w) (C, .live) =
            privateWaitingWord ring root .CWAIT
              privateComparatorReturnToken w
              ((protocol q).step ring C e, .live) := by
        rw [← hpair]
        rfl
      rw [hword]
      exact ih ((protocol q).step ring C e)
        hnext.1 hnext.2.1 hnext.2.2 hresult

/-! The CWAIT branch of the four-phase authenticated
shape supplies the sole CR0/CR1/CL0/CL1 worker. -/
theorem privateCWaitAuthenticatedFront {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT) :
    ∃ j : Nat, ∃ t : BTok,
      Counter.resetColdPrivateOnlyWorker ring root C j t ∧
      Counter.resetColdPrivateComparatorToken t := by
  rcases ha.1 with harm | hrest
  · obtain ⟨_, _, hmode, _, _⟩ := harm
    rw [hmode] at hm
    cases hm
  · rcases hrest with hstart | hrest
    · obtain ⟨_, _, hmode, _, _⟩ := hstart
      rw [hmode] at hm
      cases hm
    · rcases hrest with hcompare | hcarry
      · obtain ⟨_, j, t, _, _, hw, ht, _, _, _⟩ := hcompare
        exact ⟨j, t, hw, ht⟩
      · obtain ⟨_, _, _, _, hmode, _, _, _⟩ := hcarry
        rw [hmode] at hm
        cases hm

/-! At every surviving physical CWAIT word, the authenticated
sole comparator front remains present. -/
theorem privateCWaitComparisonFrontWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (C : Counter.Config q n) (w : List (Fin n))
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .CWAIT)
    (hlive : (privateWaitingWord ring root .CWAIT
      privateComparatorReturnToken w (C, .live)).2 = .live) :
    ∃ j : Nat, ∃ t : BTok,
      Counter.resetColdPrivateOnlyWorker ring root
        (privateWaitingWord ring root .CWAIT
          privateComparatorReturnToken w (C, .live)).1 j t ∧
      Counter.resetColdPrivateComparatorToken t := by
  have hh := privateCWaitComparisonAuthWord ring root
    hsp hlarge hwidth C w ha hc hm hlive
  exact privateCWaitAuthenticatedFront ring root
    (privateWaitingWord ring root .CWAIT
      privateComparatorReturnToken w (C, .live)).1
    hh.1 hh.2.2

noncomputable def privateCWaitFrontIndex {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Nat :=
  if h : ∃ j : Nat, ∃ t : BTok,
      Counter.resetColdPrivateOnlyWorker ring root C j t ∧
      Counter.resetColdPrivateComparatorToken t then
    Classical.choose h
  else 1

theorem privateCWaitFrontIndexSpec {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT) :
    ∃ t : BTok,
      Counter.resetColdPrivateOnlyWorker ring root C
        (privateCWaitFrontIndex ring root C) t ∧
      Counter.resetColdPrivateComparatorToken t := by
  have hex := privateCWaitAuthenticatedFront ring root C ha hm
  unfold privateCWaitFrontIndex
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem privateCWaitFrontIndexBounds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT) :
    1 ≤ privateCWaitFrontIndex ring root C ∧
      privateCWaitFrontIndex ring root C ≤ (compileAdvice q).b := by
  obtain ⟨t, hw, _⟩ :=
    privateCWaitFrontIndexSpec ring root C ha hm
  exact ⟨hw.1, hw.2.1⟩

/-! Two distinct protected positions cannot both carry comparator tokens:
the physical only-worker predicate empties every other protected slot. -/
private theorem privateCWaitWorkerPositionUnique {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (j k : Nat) (t u : BTok)
    (hj : Counter.resetColdPrivateOnlyWorker ring root C j t)
    (hk : Counter.resetColdPrivateOnlyWorker ring root C k u)
    (hu : Counter.resetColdPrivateComparatorToken u) : j = k := by
  by_cases he : j = k
  · exact he
  · have hzero := hj.2.2.2 k hk.1 hk.2.1 (Ne.symm he)
    rw [hk.2.2.1] at hzero
    rcases hu with hz | ho | hz | ho
    · rw [hz] at hzero
      cases hzero
    · rw [ho] at hzero
      cases hzero
    · rw [hz] at hzero
      cases hzero
    · rw [ho] at hzero
      cases hzero

/-- The choice-based front is the unique physically occupied
comparator position when a concrete front is known. -/
theorem privateCWaitFrontIndexOfComparator {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (j : Nat) (t : BTok)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C j t)
    (ht : Counter.resetColdPrivateComparatorToken t) :
    privateCWaitFrontIndex ring root C = j := by
  obtain ⟨u, hu, _⟩ :=
    privateCWaitFrontIndexSpec ring root C ha hm
  exact privateCWaitWorkerPositionUnique ring root C
    (privateCWaitFrontIndex ring root C) j u t hu hw ht

/-! The CR front normally advances on its outgoing source.
At CR(b), however, the PREDECESSOR edge performs the top turn.
A CL front retreats on its predecessor, except that CL(1) completes
on the root edge. -/
noncomputable def privateCWaitDesignated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : PrivateWaitingState q n) : Fin n :=
  if (x.1 (Counter.site ring root
        (privateCWaitFrontIndex ring root x.1))).tok = .CR0 ∨
      (x.1 (Counter.site ring root
        (privateCWaitFrontIndex ring root x.1))).tok = .CR1 then
    if privateCWaitFrontIndex ring root x.1 =
        (compileAdvice q).b then
      Counter.site ring root
        (privateCWaitFrontIndex ring root x.1 - 1)
    else Counter.site ring root (privateCWaitFrontIndex ring root x.1)
  else if privateCWaitFrontIndex ring root x.1 = 1 then
    root
  else Counter.site ring root
    (privateCWaitFrontIndex ring root x.1 - 1)

/-- CR uses its remaining outward-and-return budget; CL uses its
remaining distance to the root. The maximum remains L=2b+2. -/
noncomputable def privateCWaitRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : PrivateWaitingState q n) : Nat :=
  if (x.1 (Counter.site ring root
        (privateCWaitFrontIndex ring root x.1))).tok = .CR0 ∨
      (x.1 (Counter.site ring root
        (privateCWaitFrontIndex ring root x.1))).tok = .CR1 then
    2 * (compileAdvice q).b + 2 -
      privateCWaitFrontIndex ring root x.1
  else privateCWaitFrontIndex ring root x.1

/-- The actual authenticated comparator front has positive
service rank bounded by 2b+2. -/
theorem privateCWaitRankBounds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT) :
    0 < privateCWaitRank ring root (C, .live) ∧
      privateCWaitRank ring root (C, .live) ≤
        2 * (compileAdvice q).b + 2 := by
  obtain ⟨hj, hjb⟩ :=
    privateCWaitFrontIndexBounds ring root C ha hm
  by_cases ht :
      (C (Counter.site ring root
        (privateCWaitFrontIndex ring root C))).tok = .CR0 ∨
      (C (Counter.site ring root
        (privateCWaitFrontIndex ring root C))).tok = .CR1
  · simp only [privateCWaitRank, if_pos ht]
    omega
  · simp only [privateCWaitRank, if_neg ht]
    omega

def PrivateCWaitComparisonGood {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : PrivateWaitingState q n) : Prop :=
  x.2 = .live →
    Counter.ResetColdPrivateLiveShapeAuth ring root x.1 ∧
    Counter.Complete ring x.1 root ∧
    (x.1 root).mode = .CWAIT

theorem privateCWaitNextAbsorbing {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : PrivateWaitingState q n) (e : Fin n)
    (hx : x.2 ≠ .live) :
    privateWaitingNext ring root .CWAIT
      privateComparatorReturnToken x e = x := by
  cases x with
  | mk C s =>
      cases s <;> simp [privateWaitingNext] at hx ⊢

theorem privateCWaitComparisonGoodStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (x : PrivateWaitingState q n)
    (hg : PrivateCWaitComparisonGood ring root x)
    (e : Fin n) :
    PrivateCWaitComparisonGood ring root
      (privateWaitingNext ring root .CWAIT
        privateComparatorReturnToken x e) := by
  intro hnext
  by_cases hx : x.2 = .live
  · obtain ⟨ha, hc, hm⟩ := hg hx
    have hpair :
        privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e =
        ((protocol q).step ring x.1 e,
          privateWaitingOutcome ring root .CWAIT
            privateComparatorReturnToken x.1 e) := by
      cases x with
      | mk C s =>
          cases s <;> simp [privateWaitingNext] at hx ⊢
    have hout :
        privateWaitingOutcome ring root .CWAIT
          privateComparatorReturnToken x.1 e = .live := by
      rw [hpair] at hnext
      exact hnext
    have hh := privateCWaitComparisonAuthStep
      ring root e x.1 hsp hlarge hwidth ha hc hout
    rw [hpair]
    exact hh
  · have hpair :=
      privateCWaitNextAbsorbing ring root x e hx
    rw [hpair] at hnext
    exact False.elim (hx hnext)

def privateCWaitRootLease {n q : Nat}
    (root : Fin n) (x : PrivateWaitingState q n) : Nat :=
  (x.1 root).lease.val

theorem privateCWaitGoodRankBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : PrivateWaitingState q n)
    (hg : PrivateCWaitComparisonGood ring root x)
    (hl : x.2 = .live) :
    0 < privateCWaitRank ring root x ∧
      privateCWaitRank ring root x ≤
        2 * (compileAdvice q).b + 2 := by
  obtain ⟨ha, _, hm⟩ := hg hl
  exact privateCWaitRankBounds ring root x.1 ha hm

theorem privateCWaitLossIncidentLeaseOne {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hwait : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C e = .waitLoss) :
    (e = root ∨ ring.rightNeighbor e = root) ∧
    (C root).lease.val = 1 ∧
    ¬ (e = root ∧
      privateComparatorReturnToken
        (C (Counter.site ring root 1)).tok) := by
  by_cases hd : Counter.ResetClockBankDefectEntry ring C root e
  · simp [privateWaitingOutcome, hd] at hwait
  · by_cases hr : e = root ∧
        privateComparatorReturnToken
          (C (Counter.site ring root 1)).tok
    · by_cases hdr : Counter.ResetClockBankDefectEntry ring C root root <;>
        simp [privateWaitingOutcome, hd, hr, hdr] at hwait
    · by_cases hg : Counter.GrantFree
          ((protocol q).step ring C e) root
      · by_cases hm : (C root).mode = .CWAIT
        · by_cases hp : (e = root ∨
              ring.rightNeighbor e = root) ∧
              (C root).lease.val = 1
          · exact ⟨hp.1, hp.2, hr⟩
          · by_cases hn : (((protocol q).step ring C e) root).mode = .CWAIT <;>
              simp [privateWaitingOutcome, hd, hr, hg, hm, hp, hn] at hwait
        · simp [privateWaitingOutcome, hd, hr, hg, hm] at hwait
      · simp [privateWaitingOutcome, hd, hr, hg] at hwait

/-! The failure is never the comparator's productive edge:
CR< b uses its interior source; CR=b uses the interior predecessor
(top turn); CL>1 uses its interior predecessor; CL(1) has the
root return-priority guard, for either CL0 or CL1. -/
theorem privateCWaitLossNotDesignated {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .CWAIT)
    (hwait : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C e = .waitLoss) :
    e ≠ privateCWaitDesignated ring root (C, .live) := by
  obtain ⟨hinc, _, hnotreturn⟩ :=
    privateCWaitLossIncidentLeaseOne ring root e C hwait
  obtain ⟨t, hw, htype⟩ :=
    privateCWaitFrontIndexSpec ring root C ha hm
  have htok :
      (C (Counter.site ring root
        (privateCWaitFrontIndex ring root C))).tok = t :=
    hw.2.2.1
  have hgroups :
      (t = .CR0 ∨ t = .CR1) ∨
      (t = .CL0 ∨ t = .CL1) := by
    rcases htype with hzero | hone | hzero | hone
    · exact Or.inl (Or.inl hzero)
    · exact Or.inl (Or.inr hone)
    · exact Or.inr (Or.inl hzero)
    · exact Or.inr (Or.inr hone)
  rcases hgroups with hcr | hcl
  · have hforward :
        (C (Counter.site ring root
          (privateCWaitFrontIndex ring root C))).tok = .CR0 ∨
        (C (Counter.site ring root
          (privateCWaitFrontIndex ring root C))).tok = .CR1 := by
      rw [htok]
      exact hcr
    by_cases htop :
        privateCWaitFrontIndex ring root C = (compileAdvice q).b
    · have hb : 2 ≤ (compileAdvice q).b := by
        have hh := Counter.resetTrialCompiledWidth q
        omega
      have havoid := Counter.resetClockInteriorEdgeNotRootIncident
        ring C root hc
        (privateCWaitFrontIndex ring root C - 1)
        (by omega) (by omega)
      have hdes :
          privateCWaitDesignated ring root (C, .live) =
            Counter.site ring root
              (privateCWaitFrontIndex ring root C - 1) := by
        simp only [privateCWaitDesignated]
        rw [if_pos hforward, if_pos htop]
      intro he
      rw [hdes] at he
      rcases hinc with hs | ht
      · exact havoid.1 (he.symm.trans hs)
      · exact havoid.2
          ((congrArg ring.rightNeighbor he.symm).trans ht)
    · have hjb := hw.2.1
      have havoid := Counter.resetClockInteriorEdgeNotRootIncident
        ring C root hc (privateCWaitFrontIndex ring root C)
        hw.1 (by omega)
      have hdes :
          privateCWaitDesignated ring root (C, .live) =
            Counter.site ring root
              (privateCWaitFrontIndex ring root C) := by
        simp only [privateCWaitDesignated]
        rw [if_pos hforward, if_neg htop]
      intro he
      rw [hdes] at he
      rcases hinc with hs | ht
      · exact havoid.1 (he.symm.trans hs)
      · exact havoid.2
          ((congrArg ring.rightNeighbor he.symm).trans ht)
  · have hnotforward :
        ¬ ((C (Counter.site ring root
          (privateCWaitFrontIndex ring root C))).tok = .CR0 ∨
          (C (Counter.site ring root
          (privateCWaitFrontIndex ring root C))).tok = .CR1) := by
      rw [htok]
      rcases hcl with hzero | hone
      · simp [hzero]
      · simp [hone]
    by_cases hone : privateCWaitFrontIndex ring root C = 1
    · have hdes :
          privateCWaitDesignated ring root (C, .live) =
            root := by
        simp only [privateCWaitDesignated]
        rw [if_neg hnotforward, if_pos hone]
      intro he
      have hroot : e = root := he.trans hdes
      have hreturn :
          privateComparatorReturnToken
            (C (Counter.site ring root 1)).tok := by
        have htfirst :
            (C (Counter.site ring root 1)).tok = t := by
          rw [← hone]
          exact htok
        rw [htfirst]
        exact hcl
      exact hnotreturn ⟨hroot, hreturn⟩
    · have hj1 := hw.1
      have hjb := hw.2.1
      have havoid := Counter.resetClockInteriorEdgeNotRootIncident
        ring C root hc
        (privateCWaitFrontIndex ring root C - 1)
        (by omega) (by omega)
      have hdes :
          privateCWaitDesignated ring root (C, .live) =
            Counter.site ring root
              (privateCWaitFrontIndex ring root C - 1) := by
        simp only [privateCWaitDesignated]
        rw [if_neg hnotforward, if_neg hone]
      intro he
      rw [hdes] at he
      rcases hinc with hs | ht
      · exact havoid.1 (he.symm.trans hs)
      · exact havoid.2
          ((congrArg ring.rightNeighbor he.symm).trans ht)

theorem privateCWaitFailureIsPenalty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    : ∀ x : PrivateWaitingState q n, ∀ e : Fin n,
      PrivateCWaitComparisonGood ring root x →
      x.2 = .live →
      (privateWaitingNext ring root .CWAIT
        privateComparatorReturnToken x e).2 = .waitLoss →
      e ≠ privateCWaitDesignated ring root x ∧
      privateWaitingPenalty ring root
        (privateCWaitDesignated ring root) x e ∧
      privateCWaitRootLease root x = 1 := by
  intro x e hg hl hw
  obtain ⟨ha, hc, hm⟩ := hg hl
  have hclass :
      privateWaitingOutcome ring root .CWAIT
        privateComparatorReturnToken x.1 e = .waitLoss := by
    cases x with
    | mk C state =>
        cases state <;> simp [privateWaitingNext] at hl hw ⊢ <;> exact hw
  obtain ⟨hincident, hlease, _⟩ :=
    privateCWaitLossIncidentLeaseOne ring root e x.1 hclass
  have hnot :=
    privateCWaitLossNotDesignated ring root e x.1
      ha hc hm hclass
  exact ⟨hnot, ⟨hincident, hnot⟩, hlease⟩

end L3.CounterTrialLower

/-!
Actual CWAIT comparator rank/lease physical service rows
and finite-word bounded rarity.
-/

namespace L3.CounterTrialLower

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-! The CR comparator rank and designated service are determined
by its actual physical front. The top CR(b) changes direction on
the predecessor edge rather than moving right on source b. -/
theorem privateCWaitCRRankAt {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (j : Nat) (t : BTok)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C j t)
    (ht : t = .CR0 ∨ t = .CR1) :
    privateCWaitRank ring root (C, .live) =
        2 * (compileAdvice q).b + 2 - j ∧
    privateCWaitDesignated ring root (C, .live) =
      (if j = (compileAdvice q).b then
        Counter.site ring root (j - 1)
       else Counter.site ring root j) := by
  have hi := privateCWaitFrontIndexOfComparator ring root C
    j t ha hm hw (Or.elim ht
      (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
  have hf :
      (C (Counter.site ring root j)).tok = .CR0 ∨
      (C (Counter.site ring root j)).tok = .CR1 := by
    rw [hw.2.2.1]
    exact ht
  constructor
  · unfold privateCWaitRank
    rw [hi, if_pos hf]
  · unfold privateCWaitDesignated
    rw [hi, if_pos hf]

/-- CL at j has rank j. Both CL0 and CL1 return at root from
j=1, and this is completed, not a CWAIT LIVE transition. -/
theorem privateCWaitCLRankAt {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) (j : Nat) (t : BTok)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C j t)
    (ht : t = .CL0 ∨ t = .CL1) :
    privateCWaitRank ring root (C, .live) = j ∧
    privateCWaitDesignated ring root (C, .live) =
      (if j = 1 then root else Counter.site ring root (j - 1)) := by
  have hi := privateCWaitFrontIndexOfComparator ring root C
    j t ha hm hw (Or.elim ht
      (fun h => Or.inr (Or.inr (Or.inl h)))
      (fun h => Or.inr (Or.inr (Or.inr h))))
  have hf :
      ¬ ((C (Counter.site ring root j)).tok = .CR0 ∨
        (C (Counter.site ring root j)).tok = .CR1) := by
    rw [hw.2.2.1]
    rcases ht with hz | ho
    · simp [hz]
    · simp [ho]
  constructor
  · unfold privateCWaitRank
    rw [hi, if_neg hf]
  · unfold privateCWaitDesignated
    rw [hi, if_neg hf]

/-! The full protected-token frame preserves the chosen unique
comparator front and its rank, for every CR and CL byte. -/
theorem privateCWaitRankTokenFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hd : Counter.ResetColdPrivateLiveShapeAuth ring root D)
    (hm : (C root).mode = .CWAIT)
    (hn : (D root).mode = .CWAIT)
    (hf : ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (D (Counter.site ring root i)).tok =
        (C (Counter.site ring root i)).tok) :
    privateCWaitRank ring root (D, .live) =
      privateCWaitRank ring root (C, .live) := by
  obtain ⟨j, t, hw, ht⟩ :=
    privateCWaitAuthenticatedFront ring root C ha hm
  have hwD := privateIWaitOnlyWorkerFrame
    ring root C D j t hw hf
  rcases ht with hz | ho | hz | ho
  · rw [hz] at hw hwD
    rw [(privateCWaitCRRankAt ring root D j .CR0 hd hn
      hwD (Or.inl rfl)).1,
      (privateCWaitCRRankAt ring root C j .CR0 ha hm
        hw (Or.inl rfl)).1]
  · rw [ho] at hw hwD
    rw [(privateCWaitCRRankAt ring root D j .CR1 hd hn
      hwD (Or.inr rfl)).1,
      (privateCWaitCRRankAt ring root C j .CR1 ha hm
        hw (Or.inr rfl)).1]
  · rw [hz] at hw hwD
    rw [(privateCWaitCLRankAt ring root D j .CL0 hd hn
      hwD (Or.inl rfl)).1,
      (privateCWaitCLRankAt ring root C j .CL0 ha hm
        hw (Or.inl rfl)).1]
  · rw [ho] at hw hwD
    rw [(privateCWaitCLRankAt ring root D j .CL1 hd hn
      hwD (Or.inr rfl)).1,
      (privateCWaitCLRankAt ring root C j .CL1 ha hm
        hw (Or.inr rfl)).1]

theorem privateCWaitOutsideRankLeaseFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .CWAIT)
    (hout : Counter.OutsideSites q ring root e)
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C e = .live) :
    privateCWaitRank ring root
        ((protocol q).step ring C e, .live) =
      privateCWaitRank ring root (C, .live) ∧
    (((protocol q).step ring C e) root).lease.val =
      (C root).lease.val := by
  have hs := privateCWaitComparisonAuthStep ring root e C
    hsp hlarge hwidth ha hc hlive
  have hf : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (((protocol q).step ring C e)
        (Counter.site ring root i)).tok =
        (C (Counter.site ring root i)).tok := by
    intro i hi hib
    rw [Counter.outside_frame ring C root e hout i hib]
  have hroot := Counter.outside_frame ring C root e hout
    0 (by omega)
  change ((protocol q).step ring C e) root = C root at hroot
  exact ⟨privateCWaitRankTokenFrame ring root C
    ((protocol q).step ring C e) ha hs.1 hm hs.2.2 hf,
    congrArg (fun a : Agent (compileAdvice q) => a.lease.val)
      hroot⟩

/-! A LIVE outgoing root service cannot be on a returning
CL0 or CL1 first-digit byte; those are classified as complete
before the lease-one exit or physical root mode is tested. -/
theorem privateCWaitRootLiveNoReturn {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT)
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C root = .live) :
    isRetTok (C (Counter.site ring root 1)).tok = false := by
  obtain ⟨j, t, hw, ht⟩ :=
    privateCWaitAuthenticatedFront ring root C ha hm
  by_cases hj : j = 1
  · rcases ht with hzero | hone | hzero | hone
    · have hfirst :
          (C (Counter.site ring root 1)).tok = .CR0 := by
        rw [← hj]
        exact hw.2.2.1.trans hzero
      rw [hfirst]
      rfl
    · have hfirst :
          (C (Counter.site ring root 1)).tok = .CR1 := by
        rw [← hj]
        exact hw.2.2.1.trans hone
      rw [hfirst]
      rfl
    · have hfirst :
          (C (Counter.site ring root 1)).tok = .CL0 := by
        rw [← hj]
        exact hw.2.2.1.trans hzero
      have hnot := (privateCWaitComparisonLiveGuards
        ring root root C hlive).2.1
      exact False.elim (hnot ⟨rfl, Or.inl hfirst⟩)
    · have hfirst :
          (C (Counter.site ring root 1)).tok = .CL1 := by
        rw [← hj]
        exact hw.2.2.1.trans hone
      have hnot := (privateCWaitComparisonLiveGuards
        ring root root C hlive).2.1
      exact False.elim (hnot ⟨rfl, Or.inr hfirst⟩)
  · have hb : 1 ≤ (compileAdvice q).b :=
      Nat.le_of_lt (Counter.resetTrialCompiledWidth q)
    have hfirst := hw.2.2.2 1 (by omega) hb (Ne.symm hj)
    rw [hfirst]
    rfl

theorem privateCWaitIncidentLiveLeaseTick {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .CWAIT)
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C e = .live)
    (hi : e = root ∨ ring.rightNeighbor e = root) :
    1 < (C root).lease.val ∧
    (((protocol q).step ring C e) root).lease.val + 1 =
      (C root).lease.val := by
  have hobs := privateCWaitComparisonLiveObserver
    ring root e C hlive
  have hg := Counter.resetColdPrivateLiveIncidentGrantFree
    ring root e C ((protocol q).step ring C e) true true
    hc hsp hi hobs
  have hnew := (privateCWaitComparisonLiveGuards
    ring root e C hlive).2.2.2.2
  rcases hi with he | hp
  · subst e
    have hnon := privateCWaitRootLiveNoReturn
      ring root C ha hm hlive
    have hrow := Counter.resetColdPhysicalWaitNonreturn
      ring C root hc hg hsp (by rw [hm]; rfl) hnon
    have hpositive : 1 < (C root).lease.val := by
      by_cases hval : 1 < (C root).lease.val
      · exact hval
      · have hreset :
            (((protocol q).step ring C root) root).mode =
              .RESET := by
          rw [hrow.1]
          simp [Counter.resetColdWaitTickMode, hval]
        rw [hnew] at hreset
        cases hreset
    constructor
    · exact hpositive
    · rw [hrow.2.1]
      simp only [Counter.resetColdWaitTickLease,
        if_pos hpositive]
      omega
  · have hnoDef := (privateCWaitComparisonLiveGuards
      ring root e C hlive).1
    have hrole := Counter.resetColdIncomingRoleOfNoDefect
      ring C root e hc hp hnoDef
    have hrow := Counter.resetColdPhysicalIncomingWait
      ring C root e hc hg hsp hp hrole
      (by rw [hm]; rfl)
    have hpositive : 1 < (C root).lease.val := by
      by_cases hval : 1 < (C root).lease.val
      · exact hval
      · have hreset :
            (((protocol q).step ring C e) root).mode =
              .RESET := by
          rw [hrow.1]
          simp [Counter.resetColdWaitTickMode, hval]
        rw [hnew] at hreset
        cases hreset
    constructor
    · exact hpositive
    · rw [hrow.2]
      simp only [Counter.resetColdWaitTickLease,
        if_pos hpositive]
      omega

theorem privateCWaitIncidentLiveTokenFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .CWAIT)
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C e = .live)
    (hi : e = root ∨ ring.rightNeighbor e = root) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C e)
        (Counter.site ring root i)).tok =
        (C (Counter.site ring root i)).tok := by
  rcases hi with he | hp
  · subst e
    have hobs := privateCWaitComparisonLiveObserver
      ring root root C hlive
    have hg := Counter.resetColdPrivateLiveIncidentGrantFree
      ring root root C ((protocol q).step ring C root)
      true true hc hsp (Or.inl rfl) hobs
    have hnon := privateCWaitRootLiveNoReturn
      ring root C ha hm hlive
    have hrow := Counter.resetColdPhysicalWaitNonreturn
      ring C root hc hg hsp (by rw [hm]; rfl) hnon
    intro i hii hib
    by_cases hone : i = 1
    · subst i
      exact hrow.2.2
    · rw [Counter.resetColdOutgoingRootOtherDigitsFrame
        ring C root hc i (by omega) hib]
  · have hex := Counter.resetColdIncomingExteriorOfLarge
      ring C root e hc hlarge hp
    intro i hii hib
    exact congrArg (fun a : Agent (compileAdvice q) => a.tok)
      (Counter.resetColdIncomingRootDigitFrame
        ring C root e hc hp hex i hii hib)

theorem privateCWaitIncidentLiveRankLease {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .CWAIT)
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C e = .live)
    (hi : e = root ∨ ring.rightNeighbor e = root) :
    privateCWaitRank ring root
        ((protocol q).step ring C e, .live) =
      privateCWaitRank ring root (C, .live) ∧
    (((protocol q).step ring C e) root).lease.val + 1 =
      (C root).lease.val := by
  have hs := privateCWaitComparisonAuthStep ring root e C
    hsp hlarge hwidth ha hc hlive
  have hf := privateCWaitIncidentLiveTokenFrame ring root e C
    hsp hlarge ha hc hm hlive hi
  have hr := privateCWaitRankTokenFrame ring root C
    ((protocol q).step ring C e) ha hs.1 hm hs.2.2 hf
  exact ⟨hr, (privateCWaitIncidentLiveLeaseTick
    ring root e C hsp hlarge ha hc hm hlive hi).2⟩


theorem privateCWaitInteriorHoldTokenFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (ht : (C (Counter.site ring root j)).tok = .E ∨
      (C (Counter.site ring root j)).tok = .CL0 ∨
      (C (Counter.site ring root j)).tok = .CL1)
    (he : (C (Counter.site ring root (j + 1))).tok = .E) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C
        (Counter.site ring root j))
        (Counter.site ring root i)).tok =
      (C (Counter.site ring root i)).tok := by
  have hbankRaw := Counter.resetColdPrivateInteriorHoldBank
    (bankCell (C (Counter.site ring root j)) j)
    (bankCell (C (Counter.site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by
      change (C (Counter.site ring root j)).tok = .E ∨
        (C (Counter.site ring root j)).tok = .AL ∨
        (C (Counter.site ring root j)).tok = .CL0 ∨
        (C (Counter.site ring root j)).tok = .CL1
      rcases ht with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inr (Or.inl hh))
      · exact Or.inr (Or.inr (Or.inr hh)))
    (by change (C (Counter.site ring root (j + 1))).tok = .E
        exact he)
  have hbank :
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.tok =
        (C (Counter.site ring root j)).tok ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (Counter.site ring root j)).bit ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (C (Counter.site ring root (j + 1))).tok ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (Counter.site ring root (j + 1))).bit := by
    unfold Counter.resetColdPrivateInteriorBankAt
    simpa only [bankCell] using hbankRaw
  have hf := Counter.resetColdPrivateInteriorRowFields ring root C
    hc hsp j hj hjb
    (C (Counter.site ring root j)).tok
    (C (Counter.site ring root (j + 1))).tok
    (C (Counter.site ring root j)).bit
    (C (Counter.site ring root (j + 1))).bit hbank
  intro i hi hib
  by_cases hleft : i = j
  · subst i
    exact hf.1
  · by_cases hright : i = j + 1
    · subst i
      exact hf.2.2.1
    · rw [Counter.resetColdPrivateInteriorOtherFrame
        ring root C hc j hj hjb i hi hib hleft hright]

theorem privateCWaitInteriorResponderCRFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (hntop : j + 1 ≠ (compileAdvice q).b)
    (he : (C (Counter.site ring root j)).tok = .E)
    (ht : (C (Counter.site ring root (j + 1))).tok = .CR0 ∨
      (C (Counter.site ring root (j + 1))).tok = .CR1) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C
        (Counter.site ring root j))
        (Counter.site ring root i)).tok =
      (C (Counter.site ring root i)).tok := by
  have hraw := Counter.resetColdPrivateInteriorResponderHoldBank
    (bankCell (C (Counter.site ring root j)) j)
    (bankCell (C (Counter.site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl (by change j + 1 ≠ (compileAdvice q).b; exact hntop)
    (by change (C (Counter.site ring root j)).tok = .E; exact he)
    (by
      change (C (Counter.site ring root (j + 1))).tok = .IR ∨
        (C (Counter.site ring root (j + 1))).tok = .CR0 ∨
        (C (Counter.site ring root (j + 1))).tok = .CR1
      exact Or.inr ht)
  have hbank :
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.tok =
        (C (Counter.site ring root j)).tok ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (Counter.site ring root j)).bit ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (C (Counter.site ring root (j + 1))).tok ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (Counter.site ring root (j + 1))).bit := by
    unfold Counter.resetColdPrivateInteriorBankAt
    simpa only [bankCell] using hraw
  have hf := Counter.resetColdPrivateInteriorRowFields ring root C
    hc hsp j hj hjb
    (C (Counter.site ring root j)).tok
    (C (Counter.site ring root (j + 1))).tok
    (C (Counter.site ring root j)).bit
    (C (Counter.site ring root (j + 1))).bit hbank
  intro i hi hib
  by_cases hleft : i = j
  · subst i
    exact hf.1
  · by_cases hright : i = j + 1
    · subst i
      exact hf.2.2.1
    · rw [Counter.resetColdPrivateInteriorOtherFrame
        ring root C hc j hj hjb i hi hib hleft hright]

/-! Any actual nondesignated interior CWAIT service leaves
all protected token bytes unchanged. The sole nontrivial branch
is a CR front on the TOP responder, where the predecessor is
designated and so cannot occur under hnot. -/
theorem privateCWaitInteriorNondesignatedTokenFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (hnot : Counter.site ring root j ≠
      privateCWaitDesignated ring root (C, .live)) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C (Counter.site ring root j))
        (Counter.site ring root i)).tok =
        (C (Counter.site ring root i)).tok := by
  obtain ⟨k, t, hw, ht⟩ :=
    privateCWaitAuthenticatedFront ring root C ha hm
  have hgroups :
      (t = .CR0 ∨ t = .CR1) ∨
      (t = .CL0 ∨ t = .CL1) := by
    rcases ht with hz | ho | hz | ho
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr ho)
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr ho)
  by_cases hs : k = j
  · subst k
    rcases hgroups with hcr | hcl
    · have hdes :=
        (privateCWaitCRRankAt ring root C j t ha hm hw hcr).2
      have hntop : j ≠ (compileAdvice q).b := by omega
      rw [if_neg hntop] at hdes
      exact False.elim (hnot hdes.symm)
    · have hsource :
          (C (Counter.site ring root j)).tok = .CL0 ∨
          (C (Counter.site ring root j)).tok = .CL1 := by
        rw [hw.2.2.1]
        exact hcl
      have hdest := hw.2.2.2 (j + 1)
        (by omega) (by omega) (by omega)
      exact privateCWaitInteriorHoldTokenFrame ring root C
        hc hsp j hj hjb (Or.inr hsource) hdest
  · by_cases hd : k = j + 1
    · rcases hgroups with hcr | hcl
      · have hdes :=
          (privateCWaitCRRankAt ring root C k t ha hm hw hcr).2
        have hntop : j + 1 ≠ (compileAdvice q).b := by
          intro htop
          have hkTop : k = (compileAdvice q).b := by omega
          rw [if_pos hkTop] at hdes
          have heq : k - 1 = j := by omega
          rw [heq] at hdes
          exact hnot hdes.symm
        have hempty : (C (Counter.site ring root j)).tok = .E :=
          hw.2.2.2 j hj (by omega) (Ne.symm hs)
        have htok :
            (C (Counter.site ring root (j + 1))).tok = .CR0 ∨
            (C (Counter.site ring root (j + 1))).tok = .CR1 := by
          rw [← hd, hw.2.2.1]
          exact hcr
        exact privateCWaitInteriorResponderCRFrame
          ring root C hc hsp j hj hjb hntop hempty htok
      · have heq : k - 1 = j := by omega
        have hdes :=
          (privateCWaitCLRankAt ring root C k t ha hm hw hcl).2
        have hk : k ≠ 1 := by omega
        rw [if_neg hk, heq] at hdes
        exact False.elim (hnot hdes.symm)
    · have hemptySource :=
        hw.2.2.2 j hj (by omega) (Ne.symm hs)
      have hemptyTarget :=
        hw.2.2.2 (j + 1) (by omega) (by omega) (Ne.symm hd)
      exact privateCWaitInteriorHoldTokenFrame
        ring root C hc hsp j hj hjb
        (Or.inl hemptySource) hemptyTarget

theorem privateCWaitInteriorNondesignatedRankLease {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .CWAIT)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (hnot : Counter.site ring root j ≠
      privateCWaitDesignated ring root (C, .live))
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C
        (Counter.site ring root j) = .live) :
    privateCWaitRank ring root
        ((protocol q).step ring C (Counter.site ring root j), .live) =
      privateCWaitRank ring root (C, .live) ∧
    (((protocol q).step ring C
      (Counter.site ring root j)) root).lease.val =
      (C root).lease.val := by
  have hf := privateCWaitInteriorNondesignatedTokenFrame
    ring root C hc hsp ha hm j hj hjb hnot
  have hnew := privateCWaitComparisonAuthStep ring root
    (Counter.site ring root j) C hsp hlarge hwidth
    ha hc hlive
  have hport := Counter.resetClockInteriorEdgeNotRootIncident
    ring C root hc j hj hjb
  exact ⟨privateCWaitRankTokenFrame ring root C
      ((protocol q).step ring C (Counter.site ring root j))
      ha hnew.1 hm hnew.2.2 hf,
    privateIncrementNonincidentLeaseFrame ring root
      (Counter.site ring root j) C hport.1 hport.2⟩

/-! A CR0/CR1 service on the actual interior outgoing edge
creates a unique next-digit CR token; the equality flag and
next OLD digit bit determine CR0 versus CR1. -/
theorem privateCWaitCRForwardWorker {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (t : BTok)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C j t)
    (ht : t = .CR0 ∨ t = .CR1) :
    Counter.resetColdPrivateOnlyWorker ring root
      ((protocol q).step ring C (Counter.site ring root j))
      (j + 1)
      (if t == .CR1 &&
        (C (Counter.site ring root (j + 1))).bit ==
          (compileAdvice q).theta j
        then BTok.CR1 else BTok.CR0) := by
  have hempty :
      (C (Counter.site ring root (j + 1))).tok = .E :=
    hw.2.2.2 (j + 1) (by omega) (by omega) (by omega)
  have hidx : j + 1 - 1 = j := by omega
  have hraw := Counter.resetColdPrivateCRForwardBank
    (bankCell (C (Counter.site ring root j)) j)
    (bankCell (C (Counter.site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by
      change (C (Counter.site ring root j)).tok = .CR0 ∨
        (C (Counter.site ring root j)).tok = .CR1
      rw [hw.2.2.1]
      exact ht)
    (by change (C (Counter.site ring root (j + 1))).tok = .E
        exact hempty)
  have hbank :
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.tok =
        .E ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (Counter.site ring root j)).bit ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (if t == .CR1 &&
          (C (Counter.site ring root (j + 1))).bit ==
            (compileAdvice q).theta j
          then BTok.CR1 else BTok.CR0) ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (Counter.site ring root (j + 1))).bit := by
    unfold Counter.resetColdPrivateInteriorBankAt
    have hr := hraw
    simp only [bankCell, hw.2.2.1, hidx] at hr ⊢
    exact ⟨hr.1, hr.2.1, hr.2.2.2, hr.2.2.1⟩
  have hf := Counter.resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb
    .E
    (if t == .CR1 &&
      (C (Counter.site ring root (j + 1))).bit ==
        (compileAdvice q).theta j
      then BTok.CR1 else BTok.CR0)
    (C (Counter.site ring root j)).bit
    (C (Counter.site ring root (j + 1))).bit hbank
  exact Counter.resetColdPrivateInteriorWorkerForward
    ring root C hc j hj hjb t
      (if t == .CR1 &&
        (C (Counter.site ring root (j + 1))).bit ==
          (compileAdvice q).theta j
        then BTok.CR1 else BTok.CR0)
    hw hf.1 hf.2.2.1

/-! Top CR at digit b turns to CL at digit b-1 under
the predecessor source edge; this is a *productive* physical
edge, not a nondesignated hold. -/
theorem privateCWaitCRTopTurnWorker {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (htop : j + 1 = (compileAdvice q).b)
    (t : BTok)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C
      (j + 1) t)
    (ht : t = .CR0 ∨ t = .CR1) :
    Counter.resetColdPrivateOnlyWorker ring root
      ((protocol q).step ring C (Counter.site ring root j))
      j (if t = .CR1 then BTok.CL1 else BTok.CL0) := by
  have hempty : (C (Counter.site ring root j)).tok = .E :=
    hw.2.2.2 j hj (by omega) (by omega)
  have hraw := Counter.resetColdPrivateCRTopTurnBank
    (bankCell (C (Counter.site ring root j)) j)
    (bankCell (C (Counter.site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl (by change j + 1 = (compileAdvice q).b; exact htop)
    (by change (C (Counter.site ring root j)).tok = .E
        exact hempty)
    (by
      change (C (Counter.site ring root (j + 1))).tok = .CR0 ∨
        (C (Counter.site ring root (j + 1))).tok = .CR1
      rw [hw.2.2.1]
      exact ht)
  have hbank :
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.tok =
        (if t = .CR1 then BTok.CL1 else BTok.CL0) ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (Counter.site ring root j)).bit ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.tok =
        .E ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (Counter.site ring root (j + 1))).bit := by
    unfold Counter.resetColdPrivateInteriorBankAt
    have hr := hraw
    simp only [bankCell, hw.2.2.1] at hr ⊢
    exact ⟨hr.1, hr.2.2.1, hr.2.1, hr.2.2.2⟩
  have hf := Counter.resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb
    (if t = .CR1 then BTok.CL1 else BTok.CL0) .E
    (C (Counter.site ring root j)).bit
    (C (Counter.site ring root (j + 1))).bit hbank
  exact Counter.resetColdPrivateInteriorWorkerBackward
    ring root C hc j hj hjb t
      (if t = .CR1 then BTok.CL1 else BTok.CL0)
    hw hf.1 hf.2.2.1

/-! A CL0/CL1 worker moves backward unchanged to the
source of its predecessor edge, leaving its old responder empty. -/
theorem privateCWaitCLBackwardWorker {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (t : BTok)
    (hw : Counter.resetColdPrivateOnlyWorker ring root C
      (j + 1) t)
    (ht : t = .CL0 ∨ t = .CL1) :
    Counter.resetColdPrivateOnlyWorker ring root
      ((protocol q).step ring C (Counter.site ring root j))
      j t := by
  have hempty : (C (Counter.site ring root j)).tok = .E :=
    hw.2.2.2 j hj (by omega) (by omega)
  have hraw := Counter.resetColdPrivateCLReturnBank
    (bankCell (C (Counter.site ring root j)) j)
    (bankCell (C (Counter.site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change (C (Counter.site ring root j)).tok = .E
        exact hempty)
    (by
      change (C (Counter.site ring root (j + 1))).tok = .CL0 ∨
        (C (Counter.site ring root (j + 1))).tok = .CL1
      rw [hw.2.2.1]
      exact ht)
  have hbank :
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.tok =
        t ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (Counter.site ring root j)).bit ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.tok =
        .E ∧
      (Counter.resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (Counter.site ring root (j + 1))).bit := by
    unfold Counter.resetColdPrivateInteriorBankAt
    have hr := hraw
    simp only [bankCell, hw.2.2.1] at hr ⊢
    exact ⟨hr.1, hr.2.2.1, hr.2.1, hr.2.2.2⟩
  have hf := Counter.resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb t .E
    (C (Counter.site ring root j)).bit
    (C (Counter.site ring root (j + 1))).bit hbank
  exact Counter.resetColdPrivateInteriorWorkerBackward
    ring root C hc j hj hjb t t
    hw hf.1 hf.2.2.1


/-! A designated physical CR/CL service strictly decreases the
comparator's Nat rank and frames the root lease. The top CR(b)
turn spends its predecessor edge and drops the rank by three.
A returning CL0/CL1(1) root service is completed, never LIVE. -/
theorem privateCWaitDesignatedLiveRankLease {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Counter.Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .CWAIT)
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C e = .live)
    (he : e = privateCWaitDesignated ring root (C, .live)) :
    privateCWaitRank ring root
        ((protocol q).step ring C e, .live) + 1 ≤
      privateCWaitRank ring root (C, .live) ∧
    (((protocol q).step ring C e) root).lease.val =
      (C root).lease.val := by
  obtain ⟨j, t, hw, ht⟩ :=
    privateCWaitAuthenticatedFront ring root C ha hm
  have hs := privateCWaitComparisonAuthStep ring root e C
    hsp hlarge hwidth ha hc hlive
  have hgroups :
      (t = .CR0 ∨ t = .CR1) ∨
      (t = .CL0 ∨ t = .CL1) := by
    rcases ht with hz | ho | hz | ho
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr ho)
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr ho)
  rcases hgroups with hcr | hcl
  · have hold :=
      privateCWaitCRRankAt ring root C j t ha hm hw hcr
    have hj1 := hw.1
    have hjb := hw.2.1
    by_cases htop : j = (compileAdvice q).b
    · have hpre :
          privateCWaitDesignated ring root (C, .live) =
            Counter.site ring root (j - 1) := by
        rw [hold.2, if_pos htop]
      have hedge : e = Counter.site ring root (j - 1) :=
        he.trans hpre
      have hb : 2 ≤ (compileAdvice q).b := by
        have hh := Counter.resetTrialCompiledWidth q
        omega
      have hk : 1 ≤ j - 1 := by omega
      have hkb : j - 1 < (compileAdvice q).b := by omega
      have hsum : j - 1 + 1 = j := by omega
      have hport := Counter.resetClockInteriorEdgeNotRootIncident
        ring C root hc (j - 1) hk hkb
      have hlease :
          (((protocol q).step ring C e) root).lease.val =
            (C root).lease.val := by
        rw [hedge]
        exact privateIncrementNonincidentLeaseFrame ring root
          (Counter.site ring root (j - 1)) C hport.1 hport.2
      have hwpre :
          Counter.resetColdPrivateOnlyWorker ring root C
            (j - 1 + 1) t := by
        rw [hsum]
        exact hw
      have hworker := privateCWaitCRTopTurnWorker ring root C
        hc hsp (j - 1) hk hkb (by omega) t hwpre hcr
      have hafter : Counter.ResetColdPrivateLiveShapeAuth ring root
          ((protocol q).step ring C
            (Counter.site ring root (j - 1))) := by
        rw [← hedge]
        exact hs.1
      have hmode :
          (((protocol q).step ring C
            (Counter.site ring root (j - 1))) root).mode = .CWAIT := by
        rw [← hedge]
        exact hs.2.2
      have hclnew :
          (if t = .CR1 then BTok.CL1 else BTok.CL0) = .CL0 ∨
          (if t = .CR1 then BTok.CL1 else BTok.CL0) = .CL1 := by
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
      have hnew := (privateCWaitCLRankAt ring root
        ((protocol q).step ring C
          (Counter.site ring root (j - 1)))
        (j - 1) (if t = .CR1 then BTok.CL1 else BTok.CL0)
        hafter hmode hworker hclnew).1
      constructor
      · rw [hedge, hnew, hold.1]
        omega
      · exact hlease
    · have hlt : j < (compileAdvice q).b := by omega
      have hpre :
          privateCWaitDesignated ring root (C, .live) =
            Counter.site ring root j := by
        rw [hold.2, if_neg htop]
      have hedge : e = Counter.site ring root j :=
        he.trans hpre
      have hport := Counter.resetClockInteriorEdgeNotRootIncident
        ring C root hc j hj1 hlt
      have hlease :
          (((protocol q).step ring C e) root).lease.val =
            (C root).lease.val := by
        rw [hedge]
        exact privateIncrementNonincidentLeaseFrame ring root
          (Counter.site ring root j) C hport.1 hport.2
      have hworker := privateCWaitCRForwardWorker ring root C
        hc hsp j hj1 hlt t hw hcr
      have hafter : Counter.ResetColdPrivateLiveShapeAuth ring root
          ((protocol q).step ring C (Counter.site ring root j)) := by
        rw [← hedge]
        exact hs.1
      have hmode :
          (((protocol q).step ring C
            (Counter.site ring root j)) root).mode = .CWAIT := by
        rw [← hedge]
        exact hs.2.2
      have hcrnew :
          (if t == .CR1 &&
            (C (Counter.site ring root (j + 1))).bit ==
              (compileAdvice q).theta j
            then BTok.CR1 else BTok.CR0) = .CR0 ∨
          (if t == .CR1 &&
            (C (Counter.site ring root (j + 1))).bit ==
              (compileAdvice q).theta j
            then BTok.CR1 else BTok.CR0) = .CR1 := by
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
      have hnew := (privateCWaitCRRankAt ring root
        ((protocol q).step ring C (Counter.site ring root j))
        (j + 1)
        (if t == .CR1 &&
          (C (Counter.site ring root (j + 1))).bit ==
            (compileAdvice q).theta j
          then BTok.CR1 else BTok.CR0)
        hafter hmode hworker hcrnew).1
      constructor
      · rw [hedge, hnew, hold.1]
        omega
      · exact hlease
  · have hold :=
      privateCWaitCLRankAt ring root C j t ha hm hw hcl
    have hj1 := hw.1
    have hjb := hw.2.1
    by_cases hone : j = 1
    · have hdes :
          privateCWaitDesignated ring root (C, .live) =
            root := by
        rw [hold.2, if_pos hone]
      have heRoot : e = root := he.trans hdes
      have hfirst :
          (C (Counter.site ring root 1)).tok = t := by
        rw [← hone]
        exact hw.2.2.1
      have hret :
          privateComparatorReturnToken
            (C (Counter.site ring root 1)).tok := by
        rw [hfirst]
        exact hcl
      have hnot := (privateCWaitComparisonLiveGuards
        ring root e C hlive).2.1
      exact False.elim (hnot ⟨heRoot, hret⟩)
    · have hk : 1 ≤ j - 1 := by omega
      have hkb : j - 1 < (compileAdvice q).b := by omega
      have hsum : j - 1 + 1 = j := by omega
      have hpre :
          privateCWaitDesignated ring root (C, .live) =
            Counter.site ring root (j - 1) := by
        rw [hold.2, if_neg hone]
      have hedge : e = Counter.site ring root (j - 1) :=
        he.trans hpre
      have hport := Counter.resetClockInteriorEdgeNotRootIncident
        ring C root hc (j - 1) hk hkb
      have hlease :
          (((protocol q).step ring C e) root).lease.val =
            (C root).lease.val := by
        rw [hedge]
        exact privateIncrementNonincidentLeaseFrame ring root
          (Counter.site ring root (j - 1)) C hport.1 hport.2
      have hwpre :
          Counter.resetColdPrivateOnlyWorker ring root C
            (j - 1 + 1) t := by
        rw [hsum]
        exact hw
      have hworker := privateCWaitCLBackwardWorker ring root C
        hc hsp (j - 1) hk hkb t hwpre hcl
      have hafter : Counter.ResetColdPrivateLiveShapeAuth ring root
          ((protocol q).step ring C
            (Counter.site ring root (j - 1))) := by
        rw [← hedge]
        exact hs.1
      have hmode :
          (((protocol q).step ring C
            (Counter.site ring root (j - 1))) root).mode = .CWAIT := by
        rw [← hedge]
        exact hs.2.2
      have hnew := (privateCWaitCLRankAt ring root
        ((protocol q).step ring C (Counter.site ring root (j - 1)))
        (j - 1) t hafter hmode hworker hcl).1
      constructor
      · rw [hedge, hnew, hold.1]
        omega
      · exact hlease

theorem privateCWaitTopSourceRankLeaseFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT)
    (hlive : privateWaitingOutcome ring root .CWAIT
      privateComparatorReturnToken C
        (Counter.site ring root (compileAdvice q).b) = .live) :
    privateCWaitRank ring root
        ((protocol q).step ring C
          (Counter.site ring root (compileAdvice q).b), .live) =
      privateCWaitRank ring root (C, .live) ∧
    (((protocol q).step ring C
      (Counter.site ring root (compileAdvice q).b)) root).lease.val =
      (C root).lease.val := by
  have hnew := privateCWaitComparisonAuthStep ring root
    (Counter.site ring root (compileAdvice q).b)
    C hsp hlarge hwidth ha hc hlive
  have hf := privateIWaitTopSourceTokenFrame ring root C
    hc hsp hlarge hwidth ha
  have hroot := Counter.resetColdTopRootPhysicalFrame
    ring C root hc hlarge
  exact ⟨privateCWaitRankTokenFrame ring root C
      ((protocol q).step ring C
        (Counter.site ring root (compileAdvice q).b))
      ha hnew.1 hm hnew.2.2 hf,
    congrArg (fun a : Agent (compileAdvice q) => a.lease.val)
      hroot⟩


def PrivateCWaitRankLeaseRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  (∀ x : PrivateWaitingState q n, ∀ e : Fin n,
    PrivateCWaitComparisonGood ring root x →
    x.2 = .live →
    (privateWaitingNext ring root .CWAIT
      privateComparatorReturnToken x e).2 = .live →
    (e = privateCWaitDesignated ring root x →
      privateCWaitRank ring root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) + 1 ≤
        privateCWaitRank ring root x ∧
      privateCWaitRootLease root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) =
        privateCWaitRootLease root x) ∧
    (e ≠ privateCWaitDesignated ring root x →
      privateWaitingPenalty ring root
        (privateCWaitDesignated ring root) x e →
      privateCWaitRank ring root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) ≤
        privateCWaitRank ring root x ∧
      privateCWaitRootLease root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) + 1 =
        privateCWaitRootLease root x) ∧
    (e ≠ privateCWaitDesignated ring root x →
      ¬ privateWaitingPenalty ring root
        (privateCWaitDesignated ring root) x e →
      privateCWaitRank ring root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) ≤
        privateCWaitRank ring root x ∧
      privateCWaitRootLease root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) =
        privateCWaitRootLease root x)) ∧
  (∀ x : PrivateWaitingState q n, ∀ e : Fin n,
    PrivateCWaitComparisonGood ring root x →
    x.2 = .live →
    (privateWaitingNext ring root .CWAIT
      privateComparatorReturnToken x e).2 = .waitLoss →
    e ≠ privateCWaitDesignated ring root x ∧
    privateWaitingPenalty ring root
      (privateCWaitDesignated ring root) x e ∧
    privateCWaitRootLease root x = 1)

def PrivateCWaitLiveRankLeaseRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ x : PrivateWaitingState q n, ∀ e : Fin n,
    PrivateCWaitComparisonGood ring root x →
    x.2 = .live →
    (privateWaitingNext ring root .CWAIT
      privateComparatorReturnToken x e).2 = .live →
    (e = privateCWaitDesignated ring root x →
      privateCWaitRank ring root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) + 1 ≤
        privateCWaitRank ring root x ∧
      privateCWaitRootLease root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) =
        privateCWaitRootLease root x) ∧
    (e ≠ privateCWaitDesignated ring root x →
      privateWaitingPenalty ring root
        (privateCWaitDesignated ring root) x e →
      privateCWaitRank ring root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) ≤
        privateCWaitRank ring root x ∧
      privateCWaitRootLease root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) + 1 =
        privateCWaitRootLease root x) ∧
    (e ≠ privateCWaitDesignated ring root x →
      ¬ privateWaitingPenalty ring root
        (privateCWaitDesignated ring root) x e →
      privateCWaitRank ring root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) ≤
        privateCWaitRank ring root x ∧
      privateCWaitRootLease root
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) =
        privateCWaitRootLease root x)

theorem privateCWaitRankLeaseRowsOfLiveRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : PrivateCWaitLiveRankLeaseRows (q := q) ring root) :
    PrivateCWaitRankLeaseRows (q := q) ring root :=
  ⟨hrows, privateCWaitFailureIsPenalty ring root⟩

theorem privateCWaitLiveRankLeaseRowsPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    PrivateCWaitLiveRankLeaseRows (q := q) ring root := by
  intro x e hg hx hn
  cases x with
  | mk C s =>
      cases s with
      | live =>
          obtain ⟨ha, hc, hm⟩ := hg rfl
          have hout :
              privateWaitingOutcome ring root .CWAIT
                privateComparatorReturnToken C e = .live := hn
          have hp :
              privateWaitingNext ring root .CWAIT
                privateComparatorReturnToken (C, .live) e =
              ((protocol q).step ring C e, .live) := by
            change ((protocol q).step ring C e,
              privateWaitingOutcome ring root .CWAIT
                privateComparatorReturnToken C e) =
              ((protocol q).step ring C e, .live)
            rw [hout]
          constructor
          · intro hd
            have hh := privateCWaitDesignatedLiveRankLease
              ring root e C hsp hlarge hwidth
              ha hc hm hout hd
            rw [hp]
            exact hh
          · constructor
            · intro hd hpen
              have hh := privateCWaitIncidentLiveRankLease
                ring root e C hsp hlarge hwidth
                ha hc hm hout hpen.1
              rw [hp]
              exact ⟨Nat.le_of_eq hh.1, hh.2⟩
            · intro hd hnp
              have hni :
                  ¬ (e = root ∨ ring.rightNeighbor e = root) := by
                intro hi
                exact hnp ⟨hi, hd⟩
              rcases Counter.resetTrialEdgeGeometry (q := q)
                  ring root e with hsite | hinc | houtside
              · obtain ⟨j, hjb, he⟩ := hsite
                subst e
                by_cases hz : j = 0
                · subst j
                  exact False.elim (hni (Or.inl rfl))
                · have hj : 1 ≤ j := by omega
                  by_cases htop : j = (compileAdvice q).b
                  · subst j
                    have hh := privateCWaitTopSourceRankLeaseFrame
                      ring root C hc hsp hlarge hwidth
                      ha hm hout
                    rw [hp]
                    exact ⟨Nat.le_of_eq hh.1, hh.2⟩
                  · have hlt : j < (compileAdvice q).b := by
                      omega
                    have hh :=
                      privateCWaitInteriorNondesignatedRankLease
                        ring root C hsp hlarge hwidth
                        ha hc hm j hj hlt hd hout
                    rw [hp]
                    exact ⟨Nat.le_of_eq hh.1, hh.2⟩
              · exact False.elim (hni (Or.inr hinc))
              · have hh := privateCWaitOutsideRankLeaseFrame
                  ring root e C hsp hlarge hwidth ha hc hm
                  houtside hout
                rw [hp]
                exact ⟨Nat.le_of_eq hh.1, hh.2⟩
      | completed =>
          cases hx
      | waitLoss =>
          cases hx
      | grant =>
          cases hx
      | defect =>
          cases hx
      | aborted =>
          cases hx

theorem privateCWaitRawRunEqWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (w : List (Fin n)) (x : PrivateWaitingState q n) :
    privateWorkerRawRun
      (privateWaitingNext ring root .CWAIT
        privateComparatorReturnToken) x w =
      privateWaitingWord ring root .CWAIT
        privateComparatorReturnToken w x := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
      change privateWorkerRawRun
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken)
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken x e) w =
        privateWaitingWord ring root .CWAIT
          privateComparatorReturnToken w
          (privateWaitingNext ring root .CWAIT
            privateComparatorReturnToken x e)
      exact ih _


/-! Bounded authenticated isolated CWAIT origins use the same
actual comparator observer and the compiled spatial width. -/
def PrivateComparatorBoundedIsolatedLaunch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Prop :=
  PrivateComparatorIsolatedLaunch ring root C ∧
    Counter.ResetColdPrivateLiveShapeAuth ring root C ∧
    (compileAdvice q).K < 2 ^ (compileAdvice q).b

abbrev PrivateComparatorBoundedOrigin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  { C : Counter.Config q n //
      PrivateComparatorBoundedIsolatedLaunch ring root C }

noncomputable def privateComparatorBoundedTimeout {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (o : PrivateComparatorBoundedOrigin (q := q) ring root)
    (w : List (Fin n)) : Bool :=
  privateComparatorIsolatedTimeout ring root
    (⟨o.val, o.property.1⟩ :
      PrivateComparatorIsolatedOrigin (q := q) ring root) w

/-- Sharp C.1 rarity for every authenticated isolated comparator
origin on the spatially large-ring domain. -/
def PrivateComparatorBoundedRarity {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  ∀ (o : PrivateComparatorBoundedOrigin (q := q) ring root)
    (T : Nat),
    workerTimeoutDenominator (compileAdvice q).b *
      L3.Prob.scheduleSum n T (fun w =>
        L3.Prob.indicator
          (privateComparatorBoundedTimeout ring root o w)) ≤
      workerTimeoutNumerator (compileAdvice q).b * n ^ T

theorem privateCWaitRankRowsGiveCover {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hrows : PrivateCWaitRankLeaseRows (q := q) ring root)
    (C : Counter.Config q n)
    (ha : Counter.ResetColdPrivateLiveShapeAuth ring root C)
    (hc : Counter.Complete ring C root)
    (hm : (C root).mode = .CWAIT)
    (w : List (Fin n))
    (hfail :
      (privateWaitingWord ring root .CWAIT
        privateComparatorReturnToken w (C, .live)).2 = .waitLoss) :
    privateCWaitRootLease root (C, .live) ≤
      workerPenaltyCount
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken)
        (privateCWaitDesignated ring root)
        (privateWaitingPenalty ring root
          (privateCWaitDesignated ring root))
        (C, .live) (2 * (compileAdvice q).b + 2) w := by
  have hgood :
      PrivateCWaitComparisonGood ring root (C, .live) :=
    fun _ => ⟨ha, hc, hm⟩
  have hbound := privateCWaitGoodRankBound
    ring root (C, .live) hgood rfl
  have hrec := privateWorkerLeaseRankWordBound
    (privateWaitingNext ring root .CWAIT
      privateComparatorReturnToken)
    (privateCWaitDesignated ring root)
    (privateWaitingPenalty ring root
      (privateCWaitDesignated ring root))
    (PrivateCWaitComparisonGood ring root)
    (fun x : PrivateWaitingState q n => x.2 = .live)
    (fun x : PrivateWaitingState q n => x.2 = .waitLoss)
    (privateCWaitRank ring root)
    (privateCWaitRootLease root)
    (privateCWaitNextAbsorbing ring root)
    (fun x hf hl => by rw [hf] at hl; cases hl)
    (fun x e hg _ _ =>
      privateCWaitComparisonGoodStep ring root
        hsp hlarge hwidth x hg e)
    (fun x hg hl => (privateCWaitGoodRankBound
      ring root x hg hl).1)
    hrows.1 hrows.2
    w (C, .live) (2 * (compileAdvice q).b + 2)
    hgood rfl hbound.2
  apply hrec
  rw [privateCWaitRawRunEqWord]
  exact hfail

theorem privateComparatorBoundedRarityOfRankRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : PrivateCWaitRankLeaseRows (q := q) ring root) :
    PrivateComparatorBoundedRarity (q := q) ring root := by
  intro hlarge o T
  have hcover (w : List (Fin n))
      (hw : privateComparatorBoundedTimeout ring root o w = true) :
      11 * (compileAdvice q).b + 24 ≤
      workerPenaltyCount
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken)
        (privateCWaitDesignated ring root)
        (privateWaitingPenalty ring root
          (privateCWaitDesignated ring root))
        (o.val, .live) (2 * (compileAdvice q).b + 2) w := by
    have hfail :
        (privateWaitingWord ring root .CWAIT
          privateComparatorReturnToken w (o.val, .live)).2 =
          .waitLoss := by
      by_cases he :
          (privateWaitingWord ring root .CWAIT
            privateComparatorReturnToken w (o.val, .live)).2 =
            .waitLoss
      · exact he
      · simp [privateComparatorBoundedTimeout,
          privateComparatorIsolatedTimeout,
          privateComparatorWorkerTimeout, he] at hw
    have hcount := privateCWaitRankRowsGiveCover ring root
      o.property.1.1.1 hlarge o.property.2.2 hrows
      o.val o.property.2.1 o.property.1.1.2.1
      o.property.1.1.2.2.2.1 w hfail
    have hlease :
        privateCWaitRootLease root (o.val, .live) =
          (compileAdvice q).bankLeaseCap := by
      change (o.val root).lease.val =
        (compileAdvice q).bankLeaseCap
      exact o.property.1.1.2.2.2.2.1
    rw [hlease] at hcount
    change 13 * ((compileAdvice q).b + 2) ≤
      workerPenaltyCount
        (privateWaitingNext ring root .CWAIT
          privateComparatorReturnToken)
        (privateCWaitDesignated ring root)
        (privateWaitingPenalty ring root
          (privateCWaitDesignated ring root))
        (o.val, .live) (2 * (compileAdvice q).b + 2) w
      at hcount
    omega
  have htail := adaptedWorkerTimeoutNumerator
    (privateWaitingNext ring root .CWAIT
      privateComparatorReturnToken)
    (privateCWaitDesignated ring root)
    (privateWaitingPenalty ring root
      (privateCWaitDesignated ring root))
    (privateWaitingPenaltyDisjoint ring root
      (privateCWaitDesignated ring root))
    (privateWaitingPenaltyCap ring root
      (privateCWaitDesignated ring root))
    (o.val, .live) (compileAdvice q).b T
  have hpoint (w : List (Fin n)) :
      L3.Prob.indicator
        (privateComparatorBoundedTimeout ring root o w) ≤
      (if 11 * (compileAdvice q).b + 24 ≤
        workerPenaltyCount
          (privateWaitingNext ring root .CWAIT
            privateComparatorReturnToken)
          (privateCWaitDesignated ring root)
          (privateWaitingPenalty ring root
            (privateCWaitDesignated ring root))
          (o.val, .live) (2 * (compileAdvice q).b + 2) w
      then 1 else 0) := by
    cases hw : privateComparatorBoundedTimeout ring root o w with
    | false =>
        simp [L3.Prob.indicator, hw]
    | true =>
        have hh := hcover w hw
        simp [L3.Prob.indicator, hw, hh]
  calc
    workerTimeoutDenominator (compileAdvice q).b *
        L3.Prob.scheduleSum n T (fun w =>
          L3.Prob.indicator
            (privateComparatorBoundedTimeout ring root o w)) =
      workerTimeoutDenominator (compileAdvice q).b *
        Counter.resetColdWordSum n T (fun w =>
          L3.Prob.indicator
            (privateComparatorBoundedTimeout ring root o w)) := by
          rw [privateWorkerScheduleSum]
    _ ≤ workerTimeoutDenominator (compileAdvice q).b *
        Counter.resetColdWordSum n T (fun w =>
          if 11 * (compileAdvice q).b + 24 ≤
            workerPenaltyCount
              (privateWaitingNext ring root .CWAIT
                privateComparatorReturnToken)
              (privateCWaitDesignated ring root)
              (privateWaitingPenalty ring root
                (privateCWaitDesignated ring root))
              (o.val, .live) (2 * (compileAdvice q).b + 2) w
          then 1 else 0) := by
            exact Nat.mul_le_mul_left _
              (workerWordSumMono T _ _ hpoint)
    _ = workerTimeoutDenominator (compileAdvice q).b *
        workerPenaltyTailMass
          (privateWaitingNext ring root .CWAIT
            privateComparatorReturnToken)
          (privateCWaitDesignated ring root)
          (privateWaitingPenalty ring root
            (privateCWaitDesignated ring root))
          (o.val, .live) (2 * (compileAdvice q).b + 2)
          (11 * (compileAdvice q).b + 24) T := rfl
    _ ≤ workerTimeoutNumerator (compileAdvice q).b *
          n ^ T := htail

/-! The physical CWAIT local steps imply the exact pathwise
Lambda-L penalty tail and hence the original finite-scheduler
exponential moment, with no independent worker schedule. -/
theorem privateComparatorBoundedRarityOfLiveRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : PrivateCWaitLiveRankLeaseRows (q := q) ring root) :
    PrivateComparatorBoundedRarity (q := q) ring root := by
  exact privateComparatorBoundedRarityOfRankRows ring root
    (privateCWaitRankLeaseRowsOfLiveRows ring root hrows)

/-- Sharp CWAIT physical rarity on the spatial branch K < 2^b,
using the stop-absorbing and waitLoss classification. -/
theorem privateComparatorBoundedRarityPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    PrivateComparatorBoundedRarity (q := q) ring root := by
  intro hlarge o T
  have hrows : PrivateCWaitLiveRankLeaseRows (q := q) ring root :=
    privateCWaitLiveRankLeaseRowsPhysical ring root
      hsp hlarge hwidth
  have hh := privateComparatorBoundedRarityOfLiveRows
    ring root hrows
  exact hh hlarge o T

end L3.CounterTrialLower

import Leader.L3.Grant.DrainCompose

namespace L3.GrantDrainEntrance

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

set_option autoImplicit false
set_option Elab.async false

/-!
# Predictable grant-label families and a twenty-three-square cost

The abstract theorem below needs only the current state and each
label's nominated scheduler edge. The label-index set is Fin d,
with d ≤ n; labels may nominate identical edges and may coalesce.
The integer binomial tail is defined by its exact Bernoulli recursion,
so no independence assumption about labels is used.

The physical warm-to-marked FIRST transition has not been established.
In particular we do not assert a real-chain all-origin eight-n quota.
The generic twenty-three-square result is usable when that missing
physical charging invariant has been supplied.
-/

/-- A nominated hit depends only on the state before the letter. -/
def grantDrainLabelHits {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n) :
    S → List (Fin n) → Nat
  | _, [] => 0
  | x, e :: es =>
      (if e = chosen x then 1 else 0) +
        grantDrainLabelHits next chosen (next x e) es

/-- The actual scheduler word, not a separately generated label tape. -/
def grantDrainLabelRun {S : Type} {n : Nat}
    (next : S → Fin n → S) :
    S → List (Fin n) → S
  | x, [] => x
  | x, e :: es => grantDrainLabelRun next (next x e) es

/-- Unnormalized lower tail of Bin(T,1/n): the selected letter
contributes one success and the other n-1 letters contribute zero.
For n>0, divide by n^T to obtain the binomial probability. -/
def grantDrainLabelBinomialShort (n : Nat) : Nat → Nat → Nat
  | 0, Q => if 0 < Q then 1 else 0
  | T + 1, Q =>
      (if 0 < Q then
        grantDrainLabelBinomialShort n T (Q - 1)
       else 0) +
      (n - 1) * grantDrainLabelBinomialShort n T Q

private theorem grantDrainLabelScheduleConst
    (n T c : Nat) :
    L3.Prob.scheduleSum n T (fun _ : List (Fin n) => c) =
      n ^ T * c := by
  change FixedSpanRenewalPayload.wordSum n T
    (fun _ : List (Fin n) => c) = n ^ T * c
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
    (fun _ : List (Fin n) => c)]
  exact ofFn_sum_const _ _

/-- The nominated scheduler letter appears exactly once among
all n possible next letters, even if the nomination is adaptive. -/
private theorem grantDrainLabelSumChosen
    {n : Nat} (a : Fin n) (u v : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = a then u else v)).sum = u + (n - 1) * v := by
  induction n with
  | zero =>
      exact Fin.elim0 a
  | succ n ih =>
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons, if_pos rfl]
        have htail :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then u else v)).sum =
              n * v := by
          have heq :
              (List.ofFn (fun i : Fin n =>
                if i.succ = (0 : Fin (n + 1)) then u else v)).sum =
              (List.ofFn (fun _ : Fin n => v)).sum := by
            apply ofFn_sum_eq
            intro i
            have hne : i.succ ≠ (0 : Fin (n + 1)) := by
              intro hh
              have hv := congrArg Fin.val hh
              change i.val + 1 = 0 at hv
              omega
            rw [if_neg hne]
          rw [heq, ofFn_sum_const]
        rw [htail]
        have hpred : n + 1 - 1 = n := by omega
        rw [hpred]
      · intro b
        rw [List.ofFn_succ, List.sum_cons]
        have hne : (0 : Fin (n + 1)) ≠ b.succ := by
          intro hh
          have hv := congrArg Fin.val hh
          change 0 = b.val + 1 at hv
          omega
        rw [if_neg hne]
        have htail :
            (List.ofFn (fun i : Fin n =>
              if i.succ = b.succ then u else v)).sum =
            (List.ofFn (fun i : Fin n =>
              if i = b then u else v)).sum := by
          apply ofFn_sum_eq
          intro i
          simp only [Fin.succ_inj]
        rw [htail, ih b]
        have hpos : 1 ≤ n := by
          have hb := b.isLt
          omega
        have hprev : n - 1 + 1 = n :=
          Nat.sub_add_cancel hpos
        have hpred : n + 1 - 1 = n := by omega
        rw [hpred]
        calc
          v + (u + (n - 1) * v) =
              u + ((n - 1) * v + v) := by omega
          _ = u + ((n - 1 + 1) * v) := by
            rw [Nat.add_mul, Nat.one_mul]
          _ = u + n * v := by rw [hprev]

private theorem grantDrainLabelBinomialShortZero
    (n T : Nat) :
    grantDrainLabelBinomialShort n T 0 = 0 := by
  induction T with
  | zero =>
      rfl
  | succ T ih =>
      simp [grantDrainLabelBinomialShort, ih]

theorem grantDrainLabelBinomialLaw
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n)
    (x : S) (T Q : Nat) (hn : 0 < n) :
    L3.Prob.scheduleSum n T
      (fun w => if grantDrainLabelHits next chosen x w < Q
        then 1 else 0) =
    grantDrainLabelBinomialShort n T Q := by
  induction T generalizing x Q with
  | zero =>
      simp [L3.Prob.scheduleSum, FixedSpanRenewalPayload.wordSum,
        allSchedules, grantDrainLabelHits,
        grantDrainLabelBinomialShort]
  | succ T ih =>
      cases Q with
      | zero =>
          have hZero :
              (fun w : List (Fin n) =>
                if grantDrainLabelHits next chosen x w < 0
                  then 1 else 0) =
              (fun _ : List (Fin n) => 0) := by
            funext w
            simp
          calc
            L3.Prob.scheduleSum n (T + 1)
                (fun w => if grantDrainLabelHits next chosen x w < 0
                  then 1 else 0) =
              L3.Prob.scheduleSum n (T + 1)
                (fun _ : List (Fin n) => 0) := by
                  rw [hZero]
            _ = 0 := by
              rw [grantDrainLabelScheduleConst]
              simp
            _ = grantDrainLabelBinomialShort n (T + 1) 0 :=
              (grantDrainLabelBinomialShortZero n (T + 1)).symm
      | succ Q =>
          have hrow (e : Fin n) :
              L3.Prob.scheduleSum n T
                (fun es =>
                  if grantDrainLabelHits next chosen x (e :: es) <
                      Q + 1 then 1 else 0) =
              if e = chosen x then
                grantDrainLabelBinomialShort n T Q
              else grantDrainLabelBinomialShort n T (Q + 1) := by
            by_cases he : e = chosen x
            · rw [if_pos he]
              have heq :
                  (fun es : List (Fin n) =>
                    if grantDrainLabelHits next chosen x (e :: es) <
                        Q + 1 then 1 else 0) =
                  (fun es : List (Fin n) =>
                    if grantDrainLabelHits next chosen
                      (next x e) es < Q then 1 else 0) := by
                funext es
                simp only [grantDrainLabelHits, if_pos he]
                split <;> split <;> omega
              rw [heq]
              exact ih (next x e) Q
            · rw [if_neg he]
              have heq :
                  (fun es : List (Fin n) =>
                    if grantDrainLabelHits next chosen x (e :: es) <
                        Q + 1 then 1 else 0) =
                  (fun es : List (Fin n) =>
                    if grantDrainLabelHits next chosen
                      (next x e) es < Q + 1 then 1 else 0) := by
                funext es
                simp only [grantDrainLabelHits, if_neg he, Nat.zero_add]
              rw [heq]
              exact ih (next x e) (Q + 1)
          calc
            L3.Prob.scheduleSum n (T + 1)
                (fun w => if grantDrainLabelHits next chosen x w <
                  Q + 1 then 1 else 0) =
              (List.ofFn (fun e : Fin n =>
                L3.Prob.scheduleSum n T
                  (fun es => if grantDrainLabelHits next chosen x
                    (e :: es) < Q + 1 then 1 else 0))).sum :=
                FixedSpanRenewalPayload.wordSum_succ n T _
            _ = (List.ofFn (fun e : Fin n =>
                  if e = chosen x then
                    grantDrainLabelBinomialShort n T Q
                  else grantDrainLabelBinomialShort n T (Q + 1))).sum :=
                ofFn_sum_eq _ _ hrow
            _ = grantDrainLabelBinomialShort n T Q +
                  (n - 1) *
                    grantDrainLabelBinomialShort n T (Q + 1) :=
                grantDrainLabelSumChosen (chosen x) _ _
            _ = grantDrainLabelBinomialShort n (T + 1) (Q + 1) := by
              simp [grantDrainLabelBinomialShort]


/-- A surviving first-hit word is a 0/1 indicator. -/
private theorem grantDrainLabelSurvivalBit
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) :
    ∀ (x : S) (w : List (Fin n)),
      UniformFirstHit.survivalWord next P x w ≤ 1 := by
  classical
  intro x w
  induction w generalizing x with
  | nil =>
      by_cases hp : P x
      · simp [UniformFirstHit.survivalWord, hp]
      · simp [UniformFirstHit.survivalWord, hp]
  | cons e es ih =>
      by_cases hp : P x
      · simp [UniformFirstHit.survivalWord, hp]
      · simpa only [UniformFirstHit.survivalWord, if_neg hp] using
          ih (next x e)

/-- Survival through all letters excludes the target at the
last physical state, without assuming that the target is closed. -/
private theorem grantDrainLabelSurvivalEnd
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) :
    ∀ (x : S) (w : List (Fin n)),
      UniformFirstHit.survivalWord next P x w = 1 →
      ¬ P (grantDrainLabelRun next x w) := by
  classical
  intro x w
  induction w generalizing x with
  | nil =>
      intro hs hp
      simp [UniformFirstHit.survivalWord] at hs
      exact hs hp
  | cons e es ih =>
      intro hs
      by_cases hp : P x
      · simp [UniformFirstHit.survivalWord, hp] at hs
      · have ht :
            UniformFirstHit.survivalWord next P
              (next x e) es = 1 := by
          simpa only [UniformFirstHit.survivalWord, if_neg hp] using hs
        exact ih (next x e) ht

private theorem grantDrainLabelOneLeSum
    (xs : List Nat) (h : (1 : Nat) ∈ xs) :
    1 ≤ xs.sum := by
  induction xs with
  | nil =>
      cases h
  | cons a rest ih =>
      simp only [List.mem_cons] at h
      rcases h with ha | hr
      · subst a
        simp only [List.sum_cons]
        omega
      · have ht := ih hr
        simp only [List.sum_cons]
        omega

/-- EXACT d-label union bound. Each label has its own predictable
choice; labels are not assumed independent. The witness is the
pathwise statement that an unfinished word has a live origin whose
nominated-hit count is still strictly below Q. -/
theorem grantDrainLabelFamilyBinomialSurvival
    {S : Type} {n d : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (chosen : Fin d → S → Fin n)
    (x : S) (Q T : Nat) (hn : 0 < n)
    (hShort : ∀ w : List (Fin n),
      ¬ P (grantDrainLabelRun next x w) →
      ∃ i : Fin d,
        grantDrainLabelHits next (chosen i) x w < Q) :
    UniformFirstHit.survivalNumerator next P x T ≤
      d * grantDrainLabelBinomialShort n T Q := by
  classical
  have hpoint (w : List (Fin n)) :
      UniformFirstHit.survivalWord next P x w ≤
      (List.ofFn (fun i : Fin d =>
        if grantDrainLabelHits next (chosen i) x w < Q
        then 1 else 0)).sum := by
    by_cases hs :
        UniformFirstHit.survivalWord next P x w = 1
    · have hEnd := grantDrainLabelSurvivalEnd next P x w hs
      obtain ⟨i, hi⟩ := hShort w hEnd
      have hMember : (1 : Nat) ∈
          List.ofFn (fun i : Fin d =>
            if grantDrainLabelHits next (chosen i) x w < Q
            then 1 else 0) :=
        List.mem_ofFn.mpr ⟨i, by simp [hi]⟩
      rw [hs]
      exact grantDrainLabelOneLeSum _ hMember
    · have hz :
          UniformFirstHit.survivalWord next P x w = 0 := by
        have hb := grantDrainLabelSurvivalBit next P x w
        omega
      rw [hz]
      exact Nat.zero_le _
  have hMass :
      UniformFirstHit.survivalNumerator next P x T ≤
      L3.Prob.scheduleSum n T
        (fun w => (List.ofFn (fun i : Fin d =>
          if grantDrainLabelHits next (chosen i) x w < Q
          then 1 else 0)).sum) := by
    change L3.Prob.scheduleSum n T
      (UniformFirstHit.survivalWord next P x) ≤ _
    exact L3.Density.schedule_sum_mono T _ _ hpoint
  calc
    UniformFirstHit.survivalNumerator next P x T ≤
        L3.Prob.scheduleSum n T
          (fun w => (List.ofFn (fun i : Fin d =>
            if grantDrainLabelHits next (chosen i) x w < Q
            then 1 else 0)).sum) := hMass
    _ = (List.ofFn (fun i : Fin d =>
          L3.Prob.scheduleSum n T
            (fun w => if grantDrainLabelHits next (chosen i)
              x w < Q then 1 else 0))).sum := by
        rw [L3.Density.schedule_sum_fin]
    _ = (List.ofFn (fun _ : Fin d =>
          grantDrainLabelBinomialShort n T Q)).sum := by
        apply ofFn_sum_eq
        intro i
        exact grantDrainLabelBinomialLaw
          next (chosen i) x T Q hn
    _ = d * grantDrainLabelBinomialShort n T Q := by
        rw [ofFn_sum_const]

theorem grantDrainLabelQuotaWordCharge
    {S : Type} {n d : Nat}
    (next : S → Fin n → S)
    (quota : Fin d → S → Nat)
    (chosen : Fin d → S → Fin n)
    (hMono : ∀ x i e,
      quota i (next x e) ≤ quota i x)
    (hDrop : ∀ x i, 0 < quota i x →
      quota i (next x (chosen i x)) + 1 ≤ quota i x) :
    ∀ (w : List (Fin n)) (x : S) (i : Fin d),
      0 < quota i (grantDrainLabelRun next x w) →
      grantDrainLabelHits next (chosen i) x w +
        quota i (grantDrainLabelRun next x w) ≤ quota i x := by
  intro w
  induction w with
  | nil =>
      intro x i _
      simp [grantDrainLabelHits, grantDrainLabelRun]
  | cons e es ih =>
      intro x i hEnd
      change 0 < quota i
        (grantDrainLabelRun next (next x e) es) at hEnd
      have hChild := ih (next x e) i hEnd
      have hFirst := hMono x i e
      have hPos : 0 < quota i x := by
        omega
      have hSelected :
          (if e = chosen i x then 1 else 0) +
            quota i (next x e) ≤ quota i x := by
        by_cases he : e = chosen i x
        · have hd : quota i (next x e) + 1 ≤ quota i x := by
            rw [he]
            exact hDrop x i hPos
          simp only [if_pos he]
          omega
        · simp only [if_neg he, Nat.zero_add]
          exact hFirst
      change (if e = chosen i x then 1 else 0) +
        grantDrainLabelHits next (chosen i) (next x e) es +
        quota i (grantDrainLabelRun next (next x e) es) ≤ quota i x
      omega


/-- Under the local grant-label quota conditions, every unfinished
word carries an initially indexed label with fewer than Q hits.
This is the precise interface missing from the physical warm handoff. -/
theorem grantDrainLabelQuotaShortWitness
    {S : Type} {n d : Nat}
    (next : S → Fin n → S)
    (quota : Fin d → S → Nat)
    (chosen : Fin d → S → Fin n)
    (hMono : ∀ x i e,
      quota i (next x e) ≤ quota i x)
    (hDrop : ∀ x i, 0 < quota i x →
      quota i (next x (chosen i x)) + 1 ≤ quota i x)
    (x : S) (Q : Nat)
    (hBound : ∀ i : Fin d, quota i x ≤ Q)
    (w : List (Fin n))
    (hNotDead : ¬ ∀ i : Fin d,
      quota i (grantDrainLabelRun next x w) = 0) :
    ∃ i : Fin d,
      grantDrainLabelHits next (chosen i) x w < Q := by
  classical
  have hSome : ∃ i : Fin d,
      0 < quota i (grantDrainLabelRun next x w) := by
    by_cases hs : ∃ i : Fin d,
        0 < quota i (grantDrainLabelRun next x w)
    · exact hs
    · have hAll : ∀ i : Fin d,
          quota i (grantDrainLabelRun next x w) = 0 := by
        intro i
        have hz : ¬ 0 <
            quota i (grantDrainLabelRun next x w) := by
          intro hi
          exact hs ⟨i, hi⟩
        omega
      exact False.elim (hNotDead hAll)
  obtain ⟨i, hi⟩ := hSome
  have hCharge :=
    grantDrainLabelQuotaWordCharge next quota chosen
      hMono hDrop w x i hi
  exact ⟨i, by have hb := hBound i; omega⟩

/-- For every initial state, a real finite family of remaining
quotas is dominated by d copies of Bin(T,1/n)'s lower tail. -/
theorem grantDrainLabelQuotaBinomialSurvival
    {S : Type} {n d : Nat}
    (next : S → Fin n → S)
    (quota : Fin d → S → Nat)
    (chosen : Fin d → S → Fin n)
    (hMono : ∀ x i e,
      quota i (next x e) ≤ quota i x)
    (hDrop : ∀ x i, 0 < quota i x →
      quota i (next x (chosen i x)) + 1 ≤ quota i x)
    (x : S) (Q T : Nat) (hn : 0 < n)
    (hBound : ∀ i : Fin d, quota i x ≤ Q) :
    UniformFirstHit.survivalNumerator next
      (fun y : S => ∀ i : Fin d, quota i y = 0) x T ≤
        d * grantDrainLabelBinomialShort n T Q := by
  exact grantDrainLabelFamilyBinomialSurvival
    next (fun y : S => ∀ i : Fin d, quota i y = 0)
    chosen x Q T hn
    (fun w hNot =>
      grantDrainLabelQuotaShortWitness
        next quota chosen hMono hDrop x Q hBound w hNot)

private theorem grantDrainLabelWeightedStepAlgebra
    (a b c : Nat) :
    2 * (a * c) + (2 * b) * ((2 * a) * c) =
      (2 * a) * ((1 + 2 * b) * c) := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem grantDrainLabelBinomialWeighted
    (n T Q : Nat) (hn : 0 < n) :
    2 ^ (T + 1) * grantDrainLabelBinomialShort n T Q ≤
      2 ^ Q * (2 * n - 1) ^ T := by
  induction T generalizing Q with
  | zero =>
      cases Q with
      | zero =>
          rw [grantDrainLabelBinomialShortZero]
          simp
      | succ Q =>
          have hp : 2 ^ 1 ≤ 2 ^ (Q + 1) :=
            Nat.pow_le_pow_right
              (by decide : 0 < (2 : Nat)) (by omega)
          simpa [grantDrainLabelBinomialShort] using hp
  | succ T ih =>
      cases Q with
      | zero =>
          rw [grantDrainLabelBinomialShortZero]
          simp
      | succ Q =>
          have hPrev := ih Q
          have hSame := ih (Q + 1)
          have hCoef : 1 + 2 * (n - 1) = 2 * n - 1 := by
            omega
          have hDouble : 2 ^ (Q + 1) = 2 * 2 ^ Q := by
            rw [Nat.pow_succ]
            exact Nat.mul_comm _ _
          change
            2 ^ ((T + 1) + 1) *
                (grantDrainLabelBinomialShort n T Q +
                  (n - 1) *
                    grantDrainLabelBinomialShort n T (Q + 1)) ≤
              2 ^ (Q + 1) * (2 * n - 1) ^ (T + 1)
          calc
            2 ^ ((T + 1) + 1) *
                (grantDrainLabelBinomialShort n T Q +
                  (n - 1) *
                    grantDrainLabelBinomialShort n T (Q + 1)) =
              2 * (2 ^ (T + 1) *
                grantDrainLabelBinomialShort n T Q) +
              (2 * (n - 1)) * (2 ^ (T + 1) *
                grantDrainLabelBinomialShort n T (Q + 1)) := by
                  rw [Nat.pow_succ 2 (T + 1)]
                  simp only [Nat.mul_add, Nat.mul_assoc,
                    Nat.mul_comm, Nat.mul_left_comm]
            _ ≤ 2 * (2 ^ Q * (2 * n - 1) ^ T) +
                  (2 * (n - 1)) *
                    (2 ^ (Q + 1) * (2 * n - 1) ^ T) :=
              Nat.add_le_add
                (Nat.mul_le_mul_left 2 hPrev)
                (Nat.mul_le_mul_left (2 * (n - 1)) hSame)
            _ = (2 * (2 ^ Q)) *
                  ((1 + 2 * (n - 1)) *
                    (2 * n - 1) ^ T) := by
              rw [hDouble]
              exact grantDrainLabelWeightedStepAlgebra
                (2 ^ Q) (n - 1) ((2 * n - 1) ^ T)
            _ = 2 ^ (Q + 1) * (2 * n - 1) ^ (T + 1) := by
              rw [hDouble, Nat.pow_succ (2 * n - 1) T, ← hCoef]
              simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]


private theorem grantDrainLabelTailLinearPower
    (a k : Nat) :
    a ^ k * (a + 1 + k) ≤ (a + 1) ^ (k + 1) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hp : a ^ (k + 1) ≤ (a + 1) ^ (k + 1) :=
        Nat.pow_le_pow_left (Nat.le_succ a) (k + 1)
      calc
        a ^ (k + 1) * (a + 1 + (k + 1)) =
            (a ^ k * (a + 1 + k)) * a + a ^ (k + 1) := by
              have hc : a + 1 + (k + 1) = a + 1 + k + 1 := by
                omega
              rw [hc]
              simp only [Nat.pow_succ, Nat.mul_add, Nat.add_mul,
                Nat.mul_one, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm,
                Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]
        _ ≤ (a + 1) ^ (k + 1) * a +
              (a + 1) ^ (k + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right a ih) hp
        _ = (a + 1) ^ ((k + 1) + 1) := by
          rw [Nat.pow_succ (a + 1) (k + 1),
            Nat.mul_add, Nat.mul_one]

private theorem grantDrainLabelTailHalfBlock
    (n : Nat) (hn : 0 < n) :
    2 * (2 * n - 1) ^ (2 * n) ≤ (2 * n) ^ (2 * n) := by
  have he : (2 * n - 1) + 1 = 2 * n := by omega
  have hpow :
      (2 * n - 1) ^ (2 * n) =
        (2 * n - 1) ^ (2 * n - 1) * (2 * n - 1) := by
    calc
      (2 * n - 1) ^ (2 * n) =
          (2 * n - 1) ^ ((2 * n - 1) + 1) := by rw [he]
      _ = (2 * n - 1) ^ (2 * n - 1) * (2 * n - 1) :=
        Nat.pow_succ _ _
  calc
    2 * (2 * n - 1) ^ (2 * n) =
        (2 * n - 1) ^ (2 * n - 1) * (2 * (2 * n - 1)) := by
          rw [hpow]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (2 * n - 1) ^ (2 * n - 1) *
          ((2 * n - 1) + 1 + (2 * n - 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ ≤ ((2 * n - 1) + 1) ^ ((2 * n - 1) + 1) :=
      grantDrainLabelTailLinearPower _ _
    _ = (2 * n) ^ (2 * n) := by rw [he]

/-- Each block of 2n scheduler letters saves a factor two from
the integer Bernoulli exponential moment. -/
theorem grantDrainLabelTailDecay
    (n T Q : Nat) (hn : 0 < n)
    (hT : 2 * n * Q ≤ T) :
    2 ^ Q * (2 * n - 1) ^ T ≤ (2 * n) ^ T := by
  have hblock := grantDrainLabelTailHalfBlock n hn
  have hpower :
      (2 * (2 * n - 1) ^ (2 * n)) ^ Q ≤
        ((2 * n) ^ (2 * n)) ^ Q :=
    Nat.pow_le_pow_left hblock Q
  have hblocks :
      2 ^ Q * (2 * n - 1) ^ (2 * n * Q) ≤
        (2 * n) ^ (2 * n * Q) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul] using hpower
  have hsplit : 2 * n * Q + (T - 2 * n * Q) = T := by omega
  calc
    2 ^ Q * (2 * n - 1) ^ T =
        (2 ^ Q * (2 * n - 1) ^ (2 * n * Q)) *
          (2 * n - 1) ^ (T - 2 * n * Q) := by
            rw [Nat.mul_assoc, ← Nat.pow_add, hsplit]
    _ ≤ (2 * n) ^ (2 * n * Q) *
          (2 * n) ^ (T - 2 * n * Q) :=
      Nat.mul_le_mul hblocks
        (Nat.pow_le_pow_left
          (by omega : 2 * n - 1 ≤ 2 * n) (T - 2 * n * Q))
    _ = (2 * n) ^ T := by
      rw [← Nat.pow_add, hsplit]

private theorem grantDrainLabelCountLeTwoPower (n : Nat) :
    n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hp : 0 < 2 ^ n :=
        Nat.pow_pos (by decide : 0 < (2 : Nat))
      rw [Nat.pow_succ]
      generalize hPower : 2 ^ n = p at *
      omega

private theorem grantDrainLabelScaleEight
    (power d short : Nat) :
    power * (8 * (d * short)) =
      2 * ((4 * d) * (power * short)) := by
  have hEight : (8 : Nat) = 2 * 4 := by decide
  rw [hEight]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem grantDrainLabelScaleTwoPower
    (n T : Nat) :
    2 * (2 * n) ^ T = 2 ^ (T + 1) * n ^ T := by
  calc
    2 * (2 * n) ^ T = 2 * (2 ^ T * n ^ T) := by
      rw [Nat.mul_pow]
    _ = (2 ^ T * 2) * n ^ T := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ = 2 ^ (T + 1) * n ^ T := by
      rw [Nat.pow_succ]

theorem grantDrainLabelBinomialTwentySquare
    (n d : Nat) (hn : 5 ≤ n) (hd : d ≤ n) :
    8 * (d * grantDrainLabelBinomialShort n
        (20 * n ^ 2) (8 * n)) ≤
      n ^ (20 * n ^ 2) := by
  have hPositive : 0 < n := by omega
  have hTwo : 2 * n ≤ n * n :=
    Nat.mul_le_mul_right n (by omega : 2 ≤ n)
  have hTime : 2 * n * (9 * n + 2) ≤ 20 * n ^ 2 := by
    calc
      2 * n * (9 * n + 2) = 18 * (n * n) + 4 * n := by
        simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm, Nat.reduceMul]
      _ ≤ 18 * (n * n) + 2 * (n * n) := by
        have hFour : 4 * n ≤ 2 * (n * n) := by
          calc
            4 * n = 2 * (2 * n) := by omega
            _ ≤ 2 * (n * n) := Nat.mul_le_mul_left 2 hTwo
        exact Nat.add_le_add_left hFour _
      _ = 20 * n ^ 2 := by
        rw [Nat.pow_two]
        omega
  have hCoef :
      4 * d * 2 ^ (8 * n) ≤ 2 ^ (9 * n + 2) := by
    have hD : d ≤ 2 ^ n :=
      Nat.le_trans hd (grantDrainLabelCountLeTwoPower n)
    calc
      4 * d * 2 ^ (8 * n) ≤ 4 * 2 ^ n * 2 ^ (8 * n) :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left 4 hD)
      _ = 2 ^ (9 * n + 2) := by
        have he : 9 * n + 2 = (n + 8 * n) + 2 := by omega
        rw [he, Nat.pow_add, Nat.pow_add]
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one,
          Nat.reduceMul, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
  have hWeighted :=
    grantDrainLabelBinomialWeighted n (20 * n ^ 2)
      (8 * n) hPositive
  have hDecay :=
    grantDrainLabelTailDecay n (20 * n ^ 2)
      (9 * n + 2) hPositive hTime
  have hScaled :
      2 ^ (20 * n ^ 2 + 1) *
        (8 * (d * grantDrainLabelBinomialShort n
          (20 * n ^ 2) (8 * n))) ≤
      2 ^ (20 * n ^ 2 + 1) * n ^ (20 * n ^ 2) := by
    calc
      2 ^ (20 * n ^ 2 + 1) *
          (8 * (d * grantDrainLabelBinomialShort n
            (20 * n ^ 2) (8 * n))) =
        2 * ((4 * d) *
          (2 ^ (20 * n ^ 2 + 1) *
            grantDrainLabelBinomialShort n
              (20 * n ^ 2) (8 * n))) :=
          grantDrainLabelScaleEight
            (2 ^ (20 * n ^ 2 + 1)) d
            (grantDrainLabelBinomialShort n
              (20 * n ^ 2) (8 * n))
      _ ≤ 2 * ((4 * d) *
          (2 ^ (8 * n) * (2 * n - 1) ^ (20 * n ^ 2))) :=
        Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left (4 * d) hWeighted)
      _ = 2 * ((4 * d * 2 ^ (8 * n)) *
          (2 * n - 1) ^ (20 * n ^ 2)) := by
            simp only [Nat.mul_assoc]
      _ ≤ 2 * (2 ^ (9 * n + 2) *
          (2 * n - 1) ^ (20 * n ^ 2)) :=
        Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_right _ hCoef)
      _ ≤ 2 * (2 * n) ^ (20 * n ^ 2) :=
        Nat.mul_le_mul_left 2 hDecay
      _ = 2 ^ (20 * n ^ 2 + 1) * n ^ (20 * n ^ 2) :=
        grantDrainLabelScaleTwoPower n (20 * n ^ 2)
  exact Nat.le_of_mul_le_mul_left hScaled
    (Nat.pow_pos (by decide : 0 < (2 : Nat)))


private theorem grantDrainLabelCeilingOpaque
    (q : Nat) (hq : 7 ≤ q) :
    L3.Prob.ceilNat (160 * q) 7 ≤ 23 * q := by
  have hdiv := Nat.div_add_mod (160 * q) 7
  have hmod : (160 * q) % 7 < 7 :=
    Nat.mod_lt _ (by decide : 0 < (7 : Nat))
  unfold L3.Prob.ceilNat
  split <;> omega

/-- The block renewal ceiling is <=23n^2; integer division is
proved over an opaque square, not by expanding scheduler powers. -/
theorem grantDrainLabelTwentyThreeCeiling
    (n : Nat) (hn : 5 ≤ n) :
    L3.Prob.renewalCeiling (20 * n ^ 2) 1 8 ≤ 23 * n ^ 2 := by
  have hTwo : 2 * n ≤ n * n :=
    Nat.mul_le_mul_right n (by omega : 2 ≤ n)
  have hSq : 7 ≤ n ^ 2 := by
    rw [Nat.pow_two]
    have hFive : 5 * n ≤ n * n :=
      Nat.mul_le_mul_right n hn
    omega
  change L3.Prob.ceilNat ((20 * n ^ 2) * 8) (8 - 1) ≤
    23 * n ^ 2
  have hCoeff : (20 * n ^ 2) * 8 = 160 * n ^ 2 := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.reduceMul]
  rw [hCoeff]
  change L3.Prob.ceilNat (160 * n ^ 2) 7 ≤ 23 * n ^ 2
  exact grantDrainLabelCeilingOpaque (n ^ 2) hSq

/-- Closed "all labels retired" target. No positive quota can
reappear after it has reached zero. -/
theorem grantDrainLabelAllDeadClosed
    {S : Type} {n d : Nat}
    (next : S → Fin n → S)
    (quota : Fin d → S → Nat)
    (hMono : ∀ x i e,
      quota i (next x e) ≤ quota i x) :
    ∀ x e, (∀ i : Fin d, quota i x = 0) →
      ∀ i : Fin d, quota i (next x e) = 0 := by
  intro x e hZero i
  have hm := hMono x i e
  have hz := hZero i
  omega

private theorem grantDrainLabelSurvivalEndpoint
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (hc : ∀ x e, P x → P (next x e)) :
    ∀ x T,
      UniformFirstHit.survivalNumerator next P x T =
        wordSum next (miss P) x T := by
  classical
  intro x T
  induction T generalizing x with
  | zero =>
      by_cases hx : P x
      · rw [UniformFirstHit.survivalNumerator_of_target
          next P x hx 0, LeaderCountDyadicTail.wordSum_zero]
        simp [miss, hx]
      · rw [UniformFirstHit.survivalNumerator_zero_of_not
          next P x hx, LeaderCountDyadicTail.wordSum_zero]
        simp [miss, hx]
  | succ T ih =>
      by_cases hx : P x
      · rw [UniformFirstHit.survivalNumerator_of_target
          next P x hx (T + 1),
          miss_zero next P hc x hx (T + 1)]
      · rw [UniformFirstHit.survivalNumerator_succ_of_not
          next P x hx T, LeaderCountDyadicTail.wordSum_succ]
        exact ofFn_sum_eq _ _ (fun e => ih (next x e))


/-- FULLY GENERIC finite-family consequence: if every label
has at most 8n lifetime nominated services, with persistent
nonincreasing remaining quota and no budget reset, then the
expected time to retire all d<=n labels is at most 23n^2.
This is a theorem about certified chains, not a claim that the
physical warm/marked grant chain is already certified. -/
theorem grantDrainLabelFamilyTwentyThreeSquareCost
    {S : Type} {n d : Nat}
    (next : S → Fin n → S)
    (quota : Fin d → S → Nat)
    (chosen : Fin d → S → Fin n)
    (hn : 5 ≤ n) (hd : d ≤ n)
    (hMono : ∀ x i e,
      quota i (next x e) ≤ quota i x)
    (hDrop : ∀ x i, 0 < quota i x →
      quota i (next x (chosen i x)) + 1 ≤ quota i x)
    (hBound : ∀ x i, quota i x ≤ 8 * n) :
    ∀ x T,
      costNumerator next
        (fun y : S => ∀ i : Fin d, quota i y = 0)
        x T ≤ n ^ T * (23 * n ^ 2) := by
  have hClosed :=
    grantDrainLabelAllDeadClosed next quota hMono
  have hBlock :
      ∀ x : S,
        8 * wordSum next
          (miss (fun y : S => ∀ i : Fin d, quota i y = 0))
          x (20 * n ^ 2) ≤ n ^ (20 * n ^ 2) := by
    intro x
    have hBinomial :=
      grantDrainLabelQuotaBinomialSurvival
        next quota chosen hMono hDrop
        x (8 * n) (20 * n ^ 2)
        (by omega : 0 < n) (hBound x)
    have hCut :=
      grantDrainLabelBinomialTwentySquare n d hn hd
    rw [← grantDrainLabelSurvivalEndpoint
      next (fun y : S => ∀ i : Fin d, quota i y = 0)
      hClosed x (20 * n ^ 2)]
    exact Nat.le_trans (Nat.mul_le_mul_left 8 hBinomial) hCut
  have hSquare : 0 < n ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n)
  have hCeiling := grantDrainLabelTwentyThreeCeiling n hn
  intro x T
  have hCost := L3.Density.costNumerator_of_block
    next (fun y : S => ∀ i : Fin d, quota i y = 0)
    (20 * n ^ 2) 1 8
    (by omega : 0 < 20 * n ^ 2)
    (by decide : 1 < (8 : Nat))
    hClosed (by intro y; simpa only [Nat.one_mul] using hBlock y)
    x T
  exact Nat.le_trans hCost
    (Nat.mul_le_mul_left (n ^ T) hCeiling)

/-- The already marked source-ledger quota stays bounded across
every following word; this does NOT establish that the first edge
ending warmth creates the mark. -/
theorem grantDrainLabelMarkedCutNoReset
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (x : GrantDrainEntranceState n Scratch)
    (id : Fin n) (word : List (Fin n))
    (hMarked : (x.grantLabels id).mark ≠ .unmarked) :
    ((grantDrainEntranceRun ring fresh update x word).grantLabels
      id).remaining ≤ (x.grantLabels id).remaining := by
  have hProjection :=
    grantDrainEntranceGrantLedgerProjection
      ring fresh update word x id
  rw [← hProjection]
  exact grantDrainLedgerMarkedWordNoReset
    ring fresh update word x.physical
    (x.grantLabels id) hMarked

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainLabelBinomialLaw
#print axioms L3.GrantDrainEntrance.grantDrainLabelFamilyBinomialSurvival
#print axioms L3.GrantDrainEntrance.grantDrainLabelQuotaWordCharge
#print axioms L3.GrantDrainEntrance.grantDrainLabelQuotaBinomialSurvival
#print axioms L3.GrantDrainEntrance.grantDrainLabelBinomialTwentySquare
#print axioms L3.GrantDrainEntrance.grantDrainLabelFamilyTwentyThreeSquareCost
#print axioms L3.GrantDrainEntrance.grantDrainLabelMarkedCutNoReset

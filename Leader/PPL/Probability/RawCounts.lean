import Leader.Wu.Scheduler.Probability




set_option autoImplicit false




namespace PPL.Probability




/-! # Raw finite scheduler counts




Everything in this file is a natural-number numerator.  The generic
binomial mass is parameterized by the number of hot and cold letters.
The population-protocol specialization has exactly two hot edges and
n - 2 cold edges.
-/




/-- Pascal coefficient, kept source-local so RawCounts does not depend on
Mathlib or on an older probability module. -/
def chooseCount : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | T + 1, m + 1 => chooseCount T m + chooseCount T (m + 1)




private theorem chooseCount_zero_of_lt {T m : Nat} (h : T < m) :
    chooseCount T m = 0 := by
  induction T generalizing m with
  | zero =>
      cases m with
      | zero => omega
      | succ m => rfl
  | succ T ih =>
      cases m with
      | zero => omega
      | succ m =>
          simp only [chooseCount]
          rw [ih (by omega), ih (by omega)]




private theorem chooseCount_self (T : Nat) :
    chooseCount T T = 1 := by
  induction T with
  | zero => rfl
  | succ T ih =>
      have hz : chooseCount T (T + 1) = 0 :=
        chooseCount_zero_of_lt (by omega)
      simp only [chooseCount, ih, hz, Nat.add_zero]




/-- Generic Pascal mass:
C(T,m) * hot^m * cold^(T-m).  The recursive presentation is convenient
for exact finite counting; binomialMass_eq_closed proves the displayed
closed form. -/
def binomialMass (hot cold : Nat) : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | T + 1, 0 => cold * binomialMass hot cold T 0
  | T + 1, m + 1 =>
      hot * binomialMass hot cold T m +
        cold * binomialMass hot cold T (m + 1)




/-- Closed form for the generic recursive Pascal mass. -/
theorem binomialMass_eq_closed
    (hot cold T m : Nat) :
    binomialMass hot cold T m =
      chooseCount T m * hot ^ m * cold ^ (T - m) := by
  induction T generalizing m with
  | zero =>
      cases m <;> simp [binomialMass, chooseCount]
  | succ T ih =>
      cases m with
      | zero =>
          rw [binomialMass, ih]
          simp [chooseCount, Nat.pow_succ, Nat.mul_comm]
      | succ m =>
          rw [binomialMass, ih m, ih (m + 1)]
          by_cases hlt : m < T
          · have hsub0 :
                (T + 1) - (m + 1) = T - m := by omega
            have hsub1 :
                T - m = (T - (m + 1)) + 1 := by omega
            rw [hsub0, hsub1]
            simp only [chooseCount, Nat.pow_succ, Nat.add_mul]
            ac_rfl
          · by_cases heq : m = T
            · subst m
              have hz : chooseCount T (T + 1) = 0 :=
                chooseCount_zero_of_lt (by omega)
              rw [chooseCount_self T, hz, chooseCount_self (T + 1)]
              simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
                Nat.mul_assoc]
            · have hgt : T < m := by omega
              have hz0 : chooseCount T m = 0 :=
                chooseCount_zero_of_lt hgt
              have hz1 : chooseCount T (m + 1) = 0 :=
                chooseCount_zero_of_lt (by omega)
              have hz2 : chooseCount (T + 1) (m + 1) = 0 :=
                chooseCount_zero_of_lt (by omega)
              rw [hz0, hz1, hz2]
              simp




private theorem binomialMass_zero_of_lt
    (hot cold : Nat) {T m : Nat} (h : T < m) :
    binomialMass hot cold T m = 0 := by
  rw [binomialMass_eq_closed, chooseCount_zero_of_lt h]
  simp




/-! ## Exact tail sums -/




/-- Sum of masses with m < a. -/
def lowerTailCount (hot cold T : Nat) : Nat → Nat
  | 0 => 0
  | a + 1 =>
      lowerTailCount hot cold T a + binomialMass hot cold T a




/-- Auxiliary sum of k masses strictly above threshold a. -/
private def upperTailAux (hot cold T a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      upperTailAux hot cold T a k +
        binomialMass hot cold T (a + k + 1)




/-- Sum of all masses with m > a. -/
def upperTailCount (hot cold T a : Nat) : Nat :=
  upperTailAux hot cold T a (T - a)




private theorem upperTailAux_eq_sum
    (hot cold T a k : Nat) :
    upperTailAux hot cold T a k =
      ((List.range k).map
        (fun d => binomialMass hot cold T (a + 1 + d))).sum := by
  induction k with
  | zero => simp [upperTailAux]
  | succ k ih =>
      rw [upperTailAux, List.range_succ, List.map_append,
        List.sum_append, ih]
      simp only [List.map_singleton, List.sum_singleton]
      have hidx : a + k + 1 = a + 1 + k := by omega
      rw [hidx]




/-- Lower tail written as the literal finite binomial sum. -/
theorem lowerTailCount_eq_sum
    (hot cold T a : Nat) :
    lowerTailCount hot cold T a =
      ((List.range a).map
        (fun m =>
          chooseCount T m * hot ^ m * cold ^ (T - m))).sum := by
  induction a with
  | zero => simp [lowerTailCount]
  | succ a ih =>
      rw [lowerTailCount, List.range_succ, List.map_append,
        List.sum_append, ih, binomialMass_eq_closed]
      simp




/-- Upper tail written as the literal finite binomial sum over
m = a+1,...,T. -/
theorem upperTailCount_eq_sum
    (hot cold T a : Nat) :
    upperTailCount hot cold T a =
      ((List.range (T - a)).map
        (fun d =>
          let m := a + 1 + d
          chooseCount T m * hot ^ m * cold ^ (T - m))).sum := by
  unfold upperTailCount
  rw [upperTailAux_eq_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  simp only
  rw [binomialMass_eq_closed]




private theorem lowerTail_horizon_succ
    (hot cold T a : Nat) :
    lowerTailCount hot cold (T + 1) (a + 1) =
      cold * lowerTailCount hot cold T (a + 1) +
        hot * lowerTailCount hot cold T a := by
  induction a with
  | zero =>
      simp [lowerTailCount, binomialMass]
  | succ a ih =>
      change
        lowerTailCount hot cold (T + 1) (a + 1) +
              binomialMass hot cold (T + 1) (a + 1) =
          cold *
              (lowerTailCount hot cold T (a + 1) +
                binomialMass hot cold T (a + 1)) +
            hot *
              (lowerTailCount hot cold T a +
                binomialMass hot cold T a)
      rw [ih, binomialMass]
      simp only [Nat.mul_add]
      ac_rfl




private theorem lowerTail_full
    (hot cold T : Nat) :
    lowerTailCount hot cold T (T + 1) = (hot + cold) ^ T := by
  induction T with
  | zero =>
      simp [lowerTailCount, binomialMass]
  | succ T ih =>
      rw [lowerTail_horizon_succ hot cold T (T + 1)]
      have hz :
          binomialMass hot cold T (T + 1) = 0 :=
        binomialMass_zero_of_lt hot cold (by omega)
      have hsame :
          lowerTailCount hot cold T (T + 2) =
            lowerTailCount hot cold T (T + 1) := by
        rw [lowerTailCount, hz, Nat.add_zero]
      rw [hsame, ih, Nat.pow_succ, Nat.mul_add]
      ac_rfl




private theorem lowerTail_add_upperTailAux
    (hot cold T a k : Nat) :
    lowerTailCount hot cold T (a + 1 + k) =
      lowerTailCount hot cold T (a + 1) +
        upperTailAux hot cold T a k := by
  induction k with
  | zero =>
      simp [upperTailAux]
  | succ k ih =>
      rw [show a + 1 + (k + 1) = (a + 1 + k) + 1 by omega,
        lowerTailCount, ih, upperTailAux]
      have hidx : a + 1 + k = a + k + 1 := by omega
      rw [hidx]
      omega




private theorem lowerTail_mono
    (hot cold T : Nat) {a b : Nat} (hab : a ≤ b) :
    lowerTailCount hot cold T a ≤ lowerTailCount hot cold T b := by
  cases a with
  | zero =>
      simp [lowerTailCount]
  | succ a =>
      let k := b - (a + 1)
      have hb : b = a + 1 + k := by
        dsimp [k]
        omega
      rw [hb, lowerTail_add_upperTailAux]
      omega




private theorem upperTail_le_full
    (hot cold T a : Nat) :
    upperTailCount hot cold T a ≤
      lowerTailCount hot cold T (T + 1) := by
  unfold upperTailCount
  by_cases h : a ≤ T
  · have hp :=
      lowerTail_add_upperTailAux hot cold T a (T - a)
    have hs : a + 1 + (T - a) = T + 1 := by omega
    rw [hs] at hp
    omega
  · have hz : T - a = 0 := by omega
    rw [hz]
    simp [upperTailAux]




private theorem binomialMass_mul_twoPow_le_hotDoubled
    (hot cold T a m : Nat) (ham : a + 1 ≤ m) :
    binomialMass hot cold T m * 2 ^ (a + 1) ≤
      binomialMass (2 * hot) cold T m := by
  rw [binomialMass_eq_closed, binomialMass_eq_closed]
  have hp :
      2 ^ (a + 1) ≤ 2 ^ m :=
    Nat.pow_le_pow_right (by omega) ham
  calc
    chooseCount T m * hot ^ m * cold ^ (T - m) * 2 ^ (a + 1) ≤
        chooseCount T m * hot ^ m * cold ^ (T - m) * 2 ^ m :=
      Nat.mul_le_mul_left _ hp
    _ = chooseCount T m * (2 * hot) ^ m * cold ^ (T - m) := by
      rw [Nat.mul_pow]
      ac_rfl




private theorem upperTailAux_mul_twoPow_le_hotDoubled
    (hot cold T a k : Nat) :
    upperTailAux hot cold T a k * 2 ^ (a + 1) ≤
      upperTailAux (2 * hot) cold T a k := by
  induction k with
  | zero =>
      simp [upperTailAux]
  | succ k ih =>
      simp only [upperTailAux, Nat.add_mul]
      exact Nat.add_le_add ih
        (binomialMass_mul_twoPow_le_hotDoubled
          hot cold T a (a + k + 1) (by omega))




private theorem binomialMass_mul_twoPow_le_coldDoubled
    (hot cold T m d : Nat) (hd : d ≤ T - m) :
    binomialMass hot cold T m * 2 ^ d ≤
      binomialMass hot (2 * cold) T m := by
  rw [binomialMass_eq_closed, binomialMass_eq_closed]
  have hp :
      2 ^ d ≤ 2 ^ (T - m) :=
    Nat.pow_le_pow_right (by omega) hd
  calc
    chooseCount T m * hot ^ m * cold ^ (T - m) * 2 ^ d ≤
        chooseCount T m * hot ^ m * cold ^ (T - m) *
          2 ^ (T - m) :=
      Nat.mul_le_mul_left _ hp
    _ = chooseCount T m * hot ^ m * (2 * cold) ^ (T - m) := by
      rw [Nat.mul_pow]
      ac_rfl




private theorem lowerTail_mul_twoPow_le_coldDoubled
    (hot cold T a d : Nat) (hd : d + a ≤ T + 1) :
    lowerTailCount hot cold T a * 2 ^ d ≤
      lowerTailCount hot (2 * cold) T a := by
  induction a generalizing d with
  | zero =>
      simp [lowerTailCount]
  | succ a ih =>
      simp only [lowerTailCount, Nat.add_mul]
      exact Nat.add_le_add
        (ih (d := d) (by omega))
        (binomialMass_mul_twoPow_le_coldDoubled
          hot cold T a d (by omega))




/-! ## Two distinguished scheduler letters -/




def twoEdgeLetter {n : Nat} (a b : Fin n) (e : Fin n) : Bool :=
  decide (e = a ∨ e = b)




def twoEdgeHits {n : Nat} (a b : Fin n) (word : DetSchedule n) : Nat :=
  word.countP (twoEdgeLetter a b)




/-- Exact number of length-T raw words with exactly m occurrences of the
two distinguished letters. -/
def exactTwoEdgeWordCount {n : Nat}
    (a b : Fin n) (T m : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word => decide (twoEdgeHits a b word = m))




private theorem countP_eq_sum_indicator
    {A : Type} (xs : List A) (p : A → Bool) :
    xs.countP p =
      (xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
      cases h : p x <;> simp [h, Nat.add_comm]




private theorem ofFn_sum_eq {n : Nat} (f g : Fin n → Nat)
    (hfg : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        hfg 0]
      exact congrArg (g 0 + ·)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))




private theorem ofFn_sum_add {n : Nat} (f g : Fin n → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega




private theorem ofFn_sum_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _




private theorem sum_spike (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0)
            (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v




private theorem twoEdgeLetter_count {n : Nat}
    (a b : Fin n) (hab : a ≠ b) :
    (List.ofFn (fun e : Fin n => e)).countP
      (twoEdgeLetter a b) = 2 := by
  rw [countP_eq_sum_indicator, List.map_ofFn]
  calc
    (List.ofFn
        (fun e : Fin n =>
          if twoEdgeLetter a b e then 1 else 0)).sum =
        (List.ofFn
          (fun e : Fin n =>
            (if e = a then 1 else 0) +
              (if e = b then 1 else 0))).sum := by
          apply ofFn_sum_eq
          intro e
          by_cases hea : e = a
          · subst e
            simp [twoEdgeLetter, hab, hab.symm]
          · by_cases heb : e = b
            · subst e
              simp [twoEdgeLetter, hab, hab.symm]
            · simp [twoEdgeLetter, hea, heb]
    _ = (List.ofFn
          (fun e : Fin n => if e = a then 1 else 0)).sum +
        (List.ofFn
          (fun e : Fin n => if e = b then 1 else 0)).sum :=
      ofFn_sum_add _ _
    _ = 2 := by rw [sum_spike, sum_spike]




private theorem countP_not_add_countP
    {A : Type} (p : A → Bool) (xs : List A) :
    xs.countP (fun x => !p x) + xs.countP p = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.length_cons]
      cases hp : p x <;>
        simp [hp, Nat.add_assoc, Nat.add_comm] at * <;>
        omega




private theorem twoEdgeCold_count {n : Nat}
    (hn2 : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    (List.ofFn (fun e : Fin n => e)).countP
      (fun e => !twoEdgeLetter a b e) = n - 2 := by
  have hpart := countP_not_add_countP
    (twoEdgeLetter a b) (List.ofFn (fun e : Fin n => e))
  rw [twoEdgeLetter_count a b hab] at hpart
  simp only [List.length_ofFn] at hpart
  omega




private theorem twoEdgeHits_append_singleton {n : Nat}
    (a b e : Fin n) (word : DetSchedule n) :
    twoEdgeHits a b (word ++ [e]) =
      twoEdgeHits a b word +
        (if twoEdgeLetter a b e then 1 else 0) := by
  unfold twoEdgeHits
  rw [List.countP_append]
  cases h : twoEdgeLetter a b e <;> simp [h]




private theorem extension_exact_count {n : Nat}
    (hn2 : 2 ≤ n) (a b : Fin n) (hab : a ≠ b)
    (word : DetSchedule n) (m : Nat) :
    (List.ofFn (fun e : Fin n => word ++ [e])).countP
        (fun u => decide (twoEdgeHits a b u = m)) =
      (if twoEdgeHits a b word + 1 = m then 2 else 0) +
        (if twoEdgeHits a b word = m then n - 2 else 0) := by
  have hmap :
      List.ofFn (fun e : Fin n => word ++ [e]) =
        (List.ofFn (fun e : Fin n => e)).map
          (fun e => word ++ [e]) := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, List.countP_map]
  simp only [Function.comp_def]
  by_cases hplus : twoEdgeHits a b word + 1 = m
  · have heq : twoEdgeHits a b word ≠ m := by omega
    have hp :
        (fun e : Fin n =>
          decide (twoEdgeHits a b (word ++ [e]) = m)) =
        twoEdgeLetter a b := by
      funext e
      rw [twoEdgeHits_append_singleton]
      cases he : twoEdgeLetter a b e <;>
        simp [he, hplus, heq]
    rw [hp, twoEdgeLetter_count a b hab]
    simp [hplus, heq]
  · by_cases heq : twoEdgeHits a b word = m
    · have hp :
          (fun e : Fin n =>
            decide (twoEdgeHits a b (word ++ [e]) = m)) =
          (fun e => !twoEdgeLetter a b e) := by
        funext e
        rw [twoEdgeHits_append_singleton]
        cases he : twoEdgeLetter a b e <;>
          simp [he, hplus, heq]
      rw [hp, twoEdgeCold_count hn2 a b hab]
      simp [hplus, heq]
    · have hp :
          (fun e : Fin n =>
            decide (twoEdgeHits a b (word ++ [e]) = m)) =
          (fun _ => false) := by
        funext e
        rw [twoEdgeHits_append_singleton]
        cases he : twoEdgeLetter a b e <;>
          simp [he, hplus, heq]
      rw [hp]
      simp [hplus, heq]




private theorem sum_map_add
    {A : Type} (xs : List A) (f g : A → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega




private theorem sum_if_count
    {A : Type} (xs : List A) (p : A → Bool) (c : Nat) :
    (xs.map (fun x => if p x then c else 0)).sum =
      xs.countP p * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.countP_cons, ih]
      cases p x <;> simp [Nat.add_mul, Nat.add_comm]




private theorem exactTwoEdgeWordCount_succ_zero {n T : Nat}
    (hn2 : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    exactTwoEdgeWordCount a b (T + 1) 0 =
      (n - 2) * exactTwoEdgeWordCount a b T 0 := by
  unfold exactTwoEdgeWordCount
  rw [allSchedules, List.countP_flatMap]
  have hmap :
      (List.map
          (List.countP
              (fun u => decide (twoEdgeHits a b u = 0)) ∘
            (fun word =>
              List.ofFn (fun e : Fin n => word ++ [e])))
          (allSchedules n T)) =
        (List.map
          (fun word =>
            if decide (twoEdgeHits a b word = 0)
            then n - 2 else 0)
          (allSchedules n T)) := by
    apply List.map_congr_left
    intro word hword
    change
      (List.ofFn (fun e : Fin n => word ++ [e])).countP
          (fun u => decide (twoEdgeHits a b u = 0)) = _
    rw [extension_exact_count hn2 a b hab word 0]
    by_cases h : twoEdgeHits a b word = 0 <;> simp [h]
  rw [hmap, sum_if_count]
  ac_rfl




private theorem exactTwoEdgeWordCount_succ_succ {n T m : Nat}
    (hn2 : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    exactTwoEdgeWordCount a b (T + 1) (m + 1) =
      2 * exactTwoEdgeWordCount a b T m +
        (n - 2) * exactTwoEdgeWordCount a b T (m + 1) := by
  unfold exactTwoEdgeWordCount
  rw [allSchedules, List.countP_flatMap]
  have hmap :
      (List.map
          (List.countP
              (fun u => decide (twoEdgeHits a b u = m + 1)) ∘
            (fun word =>
              List.ofFn (fun e : Fin n => word ++ [e])))
          (allSchedules n T)) =
        (List.map
          (fun word =>
            (if decide (twoEdgeHits a b word = m) then 2 else 0) +
              (if decide (twoEdgeHits a b word = m + 1)
                then n - 2 else 0))
          (allSchedules n T)) := by
    apply List.map_congr_left
    intro word hword
    change
      (List.ofFn (fun e : Fin n => word ++ [e])).countP
          (fun u => decide (twoEdgeHits a b u = m + 1)) = _
    rw [extension_exact_count hn2 a b hab word (m + 1)]
    by_cases h0 : twoEdgeHits a b word = m
    · have hp : twoEdgeHits a b word + 1 = m + 1 := by omega
      have h1 : twoEdgeHits a b word ≠ m + 1 := by omega
      simp [h0, hp, h1]
    · by_cases h1 : twoEdgeHits a b word = m + 1
      · have hp : twoEdgeHits a b word + 1 ≠ m + 1 := by omega
        simp [h0, h1, hp]
      · have hp : twoEdgeHits a b word + 1 ≠ m + 1 := by omega
        simp [h0, h1, hp]
  rw [hmap, sum_map_add, sum_if_count, sum_if_count]
  ac_rfl




private theorem exactTwoEdgeWordCount_eq_mass {n T m : Nat}
    (hn2 : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    exactTwoEdgeWordCount a b T m =
      binomialMass 2 (n - 2) T m := by
  induction T generalizing m with
  | zero =>
      cases m <;>
        simp [exactTwoEdgeWordCount, allSchedules,
          twoEdgeHits, binomialMass]
  | succ T ih =>
      cases m with
      | zero =>
          rw [exactTwoEdgeWordCount_succ_zero hn2 a b hab,
            binomialMass, ih]
      | succ m =>
          rw [exactTwoEdgeWordCount_succ_succ hn2 a b hab,
            binomialMass, ih, ih]




/-- Exact fixed-two-edge word count:
C(T,m) * 2^m * (n-2)^(T-m). -/
theorem exactTwoEdgeWordCount_eq_closed {n T m : Nat}
    (hn2 : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    exactTwoEdgeWordCount a b T m =
      chooseCount T m * 2 ^ m * (n - 2) ^ (T - m) := by
  rw [exactTwoEdgeWordCount_eq_mass hn2 a b hab,
    binomialMass_eq_closed]




/-! ## Two-edge upper and lower tails -/




def twoEdgeUpperTailCount (n T a : Nat) : Nat :=
  upperTailCount 2 (n - 2) T a




def twoEdgeLowerTailCount (n T a : Nat) : Nat :=
  lowerTailCount 2 (n - 2) T a




/-- Literal closed sum for the upper tail m > a. -/
theorem twoEdgeUpperTailCount_eq_sum
    (n T a : Nat) :
    twoEdgeUpperTailCount n T a =
      ((List.range (T - a)).map
        (fun d =>
          let m := a + 1 + d
          chooseCount T m * 2 ^ m * (n - 2) ^ (T - m))).sum := by
  exact upperTailCount_eq_sum 2 (n - 2) T a




/-- Literal closed sum for the lower tail m < a. -/
theorem twoEdgeLowerTailCount_eq_sum
    (n T a : Nat) :
    twoEdgeLowerTailCount n T a =
      ((List.range a).map
        (fun m =>
          chooseCount T m * 2 ^ m * (n - 2) ^ (T - m))).sum := by
  exact lowerTailCount_eq_sum 2 (n - 2) T a




/-- Base-2 exponential-moment upper-tail estimate.  It is the exact Nat
counterpart of E[2^X] = (1 + 2/n)^T for X ~ Bin(T,2/n). -/
theorem twoEdgeUpperTailCount_mul_twoPow_le
    (n T a : Nat) (hn2 : 2 ≤ n) :
    twoEdgeUpperTailCount n T a * 2 ^ (a + 1) ≤
      (n + 2) ^ T := by
  unfold twoEdgeUpperTailCount upperTailCount
  have hscale :=
    upperTailAux_mul_twoPow_le_hotDoubled
      2 (n - 2) T a (T - a)
  have htotal :
      upperTailAux 4 (n - 2) T a (T - a) ≤
        lowerTailCount 4 (n - 2) T (T + 1) := by
    change upperTailCount 4 (n - 2) T a ≤
      lowerTailCount 4 (n - 2) T (T + 1)
    exact upperTail_le_full 4 (n - 2) T a
  calc
    upperTailAux 2 (n - 2) T a (T - a) * 2 ^ (a + 1) ≤
        upperTailAux 4 (n - 2) T a (T - a) := by
      simpa using hscale
    _ ≤ lowerTailCount 4 (n - 2) T (T + 1) := htotal
    _ = (4 + (n - 2)) ^ T := lowerTail_full 4 (n - 2) T
    _ = (n + 2) ^ T := by
      congr 1
      omega




/-- Base-2 lower-tail transform.  For m < a there are at least
T+1-a cold positions, so doubling cold letters gives the bound. -/
theorem twoEdgeLowerTailCount_mul_twoPow_le
    (n T a : Nat) (hn2 : 2 ≤ n) (ha : a ≤ T + 1) :
    twoEdgeLowerTailCount n T a * 2 ^ (T + 1 - a) ≤
      (2 * n - 2) ^ T := by
  unfold twoEdgeLowerTailCount
  have hscale :=
    lowerTail_mul_twoPow_le_coldDoubled
      2 (n - 2) T a (T + 1 - a) (by omega)
  have hmono :
      lowerTailCount 2 (2 * (n - 2)) T a ≤
        lowerTailCount 2 (2 * (n - 2)) T (T + 1) :=
    lowerTail_mono 2 (2 * (n - 2)) T ha
  calc
    lowerTailCount 2 (n - 2) T a * 2 ^ (T + 1 - a) ≤
        lowerTailCount 2 (2 * (n - 2)) T a := hscale
    _ ≤ lowerTailCount 2 (2 * (n - 2)) T (T + 1) := hmono
    _ = (2 + 2 * (n - 2)) ^ T :=
      lowerTail_full 2 (2 * (n - 2)) T
    _ = (2 * n - 2) ^ T := by
      congr 1
      omega




/-- One explicit Nat inequality sufficient to convert the upper Chernoff
transform to a 2^-K scaled scheduler-space bound. -/
def UpperTailScaleArithmetic (n T a K : Nat) : Prop :=
  (n + 2) ^ T * 2 ^ K ≤ n ^ T * 2 ^ (a + 1)




/-- Generic upper-tail scaled bound, conditional only on the displayed
Nat arithmetic inequality. -/
theorem twoEdgeUpperTail_scaled_of_arithmetic
    (n T a K : Nat) (hn2 : 2 ≤ n)
    (harith : UpperTailScaleArithmetic n T a K) :
    twoEdgeUpperTailCount n T a * 2 ^ K ≤ n ^ T := by
  have hcher :=
    twoEdgeUpperTailCount_mul_twoPow_le n T a hn2
  have hmul :=
    Nat.mul_le_mul_right (2 ^ K) hcher
  have hchain :
      (twoEdgeUpperTailCount n T a * 2 ^ (a + 1)) * 2 ^ K ≤
        n ^ T * 2 ^ (a + 1) :=
    Nat.le_trans hmul harith
  have hcancel :
      2 ^ (a + 1) *
          (twoEdgeUpperTailCount n T a * 2 ^ K) ≤
        2 ^ (a + 1) * n ^ T := by
    calc
      _ = (twoEdgeUpperTailCount n T a * 2 ^ (a + 1)) *
          2 ^ K := by ac_rfl
      _ ≤ n ^ T * 2 ^ (a + 1) := hchain
      _ = _ := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hcancel
    (Nat.pow_pos (by omega))




/-- One explicit Nat inequality sufficient to convert the lower-tail
transform to a 2^-K scheduler-space bound. -/
def LowerTailScaleArithmetic (n T a K : Nat) : Prop :=
  (2 * n - 2) ^ T * 2 ^ K ≤
    n ^ T * 2 ^ (T + 1 - a)




/-- Generic lower-tail scaled bound under one explicit Nat inequality. -/
theorem twoEdgeLowerTail_scaled_of_arithmetic
    (n T a K : Nat) (hn2 : 2 ≤ n) (ha : a ≤ T + 1)
    (harith : LowerTailScaleArithmetic n T a K) :
    twoEdgeLowerTailCount n T a * 2 ^ K ≤ n ^ T := by
  have hcher :=
    twoEdgeLowerTailCount_mul_twoPow_le n T a hn2 ha
  have hmul :=
    Nat.mul_le_mul_right (2 ^ K) hcher
  have hchain :
      (twoEdgeLowerTailCount n T a * 2 ^ (T + 1 - a)) *
          2 ^ K ≤
        n ^ T * 2 ^ (T + 1 - a) :=
    Nat.le_trans hmul harith
  have hcancel :
      2 ^ (T + 1 - a) *
          (twoEdgeLowerTailCount n T a * 2 ^ K) ≤
        2 ^ (T + 1 - a) * n ^ T := by
    calc
      _ = (twoEdgeLowerTailCount n T a *
          2 ^ (T + 1 - a)) * 2 ^ K := by ac_rfl
      _ ≤ n ^ T * 2 ^ (T + 1 - a) := hchain
      _ = _ := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hcancel
    (Nat.pow_pos (by omega))






/-! ## Elementary arithmetic for the fixed-agent 24n bound -/


/-- Core-only Bernoulli inequality, in the same Nat style as
Leader/Wu/Splice/OrderedWindowMatcher.lean. -/
private theorem natBernoulli (a : Nat) : ∀ k,
    a ^ (k + 1) + (k + 1) * a ^ k ≤ (a + 1) ^ (k + 1)
  | 0 => by simp
  | k + 1 => by
      have ih := natBernoulli a k
      have h1 :
          (a + 1) *
                (a ^ (k + 1) + (k + 1) * a ^ k) ≤
            (a + 1) * (a + 1) ^ (k + 1) :=
        Nat.mul_le_mul_left _ ih
      have e2 :
          (a + 1) *
                (a ^ (k + 1) + (k + 1) * a ^ k) =
            a ^ (k + 1 + 1) +
              (k + 1) * a ^ (k + 1) +
              a ^ (k + 1) +
              (k + 1) * a ^ k := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add,
          Nat.pow_succ a (k + 1)]
        have hmul :
            a * ((k + 1) * a ^ k) =
              (k + 1) * a ^ (k + 1) := by
          rw [Nat.pow_succ, Nat.mul_left_comm,
            Nat.mul_comm (a ^ k) a]
        rw [hmul, Nat.mul_comm a (a ^ (k + 1))]
        omega
      have e3 :
          (a + 1) * (a + 1) ^ (k + 1) =
            (a + 1) ^ (k + 1 + 1) := by
        rw [Nat.pow_succ (a + 1) (k + 1), Nat.mul_comm]
      rw [e2, e3] at h1
      have e4 :
          (k + 1 + 1) * a ^ (k + 1) =
            (k + 1) * a ^ (k + 1) + a ^ (k + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [e4]
      omega


/-- Core-local factorial.  Core Lean 4.33 does not provide `Nat.factorial`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n


@[simp] theorem fact_zero : fact 0 = 1 := rfl


@[simp] theorem fact_succ (n : Nat) :
    fact (n + 1) = (n + 1) * fact n := rfl




/-- A factorial times the source-local Pascal coefficient is bounded by the
corresponding power. -/
private theorem factorial_mul_chooseCount_le_pow (T : Nat) :
    ∀ m, fact m * chooseCount T m ≤ T ^ m := by
  induction T with
  | zero =>
      intro m
      cases m <;> simp [chooseCount]
  | succ T ih =>
      intro m
      cases m with
      | zero => simp [chooseCount]
      | succ m =>
          calc
            fact (m + 1) *
                  chooseCount (T + 1) (m + 1) =
                (m + 1) *
                    (fact m * chooseCount T m) +
                  fact (m + 1) *
                    chooseCount T (m + 1) := by
              simp only [chooseCount, fact_succ, Nat.mul_add]
              ac_rfl
            _ ≤ (m + 1) * T ^ m + T ^ (m + 1) :=
              Nat.add_le_add
                (Nat.mul_le_mul_left (m + 1) (ih m))
                (ih (m + 1))
            _ = T ^ (m + 1) + (m + 1) * T ^ m :=
              Nat.add_comm _ _
            _ ≤ (T + 1) ^ (m + 1) :=
              natBernoulli T m


private theorem factorial_mul_binomialMass_two_self_le
    (n m : Nat) (hm : m ≤ n) :
    fact m * binomialMass 2 n n m ≤
      2 ^ m * n ^ n := by
  rw [binomialMass_eq_closed]
  have hc := factorial_mul_chooseCount_le_pow n m
  calc
    fact m *
          (chooseCount n m * 2 ^ m * n ^ (n - m)) =
        (fact m * chooseCount n m) *
          (2 ^ m * n ^ (n - m)) := by
      ac_rfl
    _ ≤ n ^ m * (2 ^ m * n ^ (n - m)) :=
      Nat.mul_le_mul_right _ hc
    _ = 2 ^ m * (n ^ m * n ^ (n - m)) := by
      ac_rfl
    _ = 2 ^ m * n ^ (m + (n - m)) := by
      rw [Nat.pow_add]
    _ = 2 ^ m * n ^ n := by
      rw [Nat.add_sub_of_le hm]


private theorem six_mul_four_pow_le_factorial_add_three (k : Nat) :
    6 * 4 ^ k ≤ fact (k + 3) := by
  induction k with
  | zero => simp [fact]
  | succ k ih =>
      calc
        6 * 4 ^ (k + 1) = 4 * (6 * 4 ^ k) := by
          rw [Nat.pow_succ]
          ac_rfl
        _ ≤ (k + 4) * fact (k + 3) :=
          Nat.mul_le_mul (by omega) ih
        _ = ((k + 3) + 1) * fact (k + 3) := by
          rw [show k + 4 = (k + 3) + 1 by omega]
        _ = fact ((k + 3) + 1) :=
          (fact_succ (k + 3)).symm
        _ = fact (k + 1 + 3) := by
          congr 1


private theorem tailTerm_three_scaled
    (n k : Nat) (hk : k + 3 ≤ n) :
    3 * 2 ^ k * binomialMass 2 n n (k + 3) ≤
      4 * n ^ n := by
  let M := binomialMass 2 n n (k + 3)
  have hmass :
      fact (k + 3) * M ≤
        2 ^ (k + 3) * n ^ n := by
    dsimp [M]
    exact factorial_mul_binomialMass_two_self_le n (k + 3) hk
  have hfac := six_mul_four_pow_le_factorial_add_three k
  have hleft :
      6 * 4 ^ k * M ≤ fact (k + 3) * M :=
    Nat.mul_le_mul_right M hfac
  have hchain :
      6 * 4 ^ k * M ≤ 2 ^ (k + 3) * n ^ n :=
    Nat.le_trans hleft hmass
  have hcancelPow :
      2 ^ k * (6 * 2 ^ k * M) ≤
        2 ^ k * (8 * n ^ n) := by
    calc
      2 ^ k * (6 * 2 ^ k * M) =
          6 * 4 ^ k * M := by
        rw [show (4 : Nat) = 2 * 2 by rfl, Nat.mul_pow]
        ac_rfl
      _ ≤ 2 ^ (k + 3) * n ^ n := hchain
      _ = 2 ^ k * (8 * n ^ n) := by
        rw [Nat.pow_add]
        simp
        ac_rfl
  have h6 :
      6 * 2 ^ k * M ≤ 8 * n ^ n :=
    Nat.le_of_mul_le_mul_left hcancelPow
      (Nat.pow_pos (by omega))
  have h2 :
      2 * (3 * 2 ^ k * M) ≤
        2 * (4 * n ^ n) := by
    calc
      2 * (3 * 2 ^ k * M) = 6 * 2 ^ k * M := by
        rw [show (6 : Nat) = 2 * 3 by rfl]
        ac_rfl
      _ ≤ 8 * n ^ n := h6
      _ = 2 * (4 * n ^ n) := by
        rw [show (8 : Nat) = 2 * 4 by rfl]
        ac_rfl
  exact Nat.le_of_mul_le_mul_left h2 (by omega)


private theorem upperTailAux_three_scaled
    (n k : Nat) (hk : k + 2 ≤ n) :
    3 * 2 ^ k * upperTailAux 2 n n 2 k ≤
      8 * n ^ n * (2 ^ k - 1) := by
  induction k generalizing n with
  | zero => simp [upperTailAux]
  | succ k ih =>
      have hk0 : k + 2 ≤ n := by omega
      have hk1 : k + 3 ≤ n := by omega
      have hi := ih n hk0
      have ht := tailTerm_three_scaled n k hk1
      have hidx : 2 + k + 1 = k + 3 := by omega
      have hgeom :
          2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by
        rw [Nat.pow_succ]
        have hp : 0 < 2 ^ k := Nat.pow_pos (by omega)
        omega
      calc
        3 * 2 ^ (k + 1) *
              upperTailAux 2 n n 2 (k + 1) =
            2 * (3 * 2 ^ k * upperTailAux 2 n n 2 k) +
              2 * (3 * 2 ^ k * binomialMass 2 n n (k + 3)) := by
          rw [upperTailAux, hidx, Nat.pow_succ, Nat.mul_add]
          ac_rfl
        _ ≤ 2 * (8 * n ^ n * (2 ^ k - 1)) +
              2 * (4 * n ^ n) :=
          Nat.add_le_add
            (Nat.mul_le_mul_left 2 hi)
            (Nat.mul_le_mul_left 2 ht)
        _ = 8 * n ^ n * (2 * (2 ^ k - 1) + 1) := by
          rw [Nat.mul_add]
          have h24 : 2 * (4 * n ^ n) = 8 * n ^ n := by
            rw [show (8 : Nat) = 2 * 4 by rfl]
            ac_rfl
          rw [h24]
          ac_rfl
        _ = 8 * n ^ n * (2 ^ (k + 1) - 1) := by
          rw [hgeom]


private theorem upperTailAux_three_le_three_pow
    (n : Nat) (hn2 : 2 ≤ n) :
    upperTailAux 2 n n 2 (n - 2) ≤ 3 * n ^ n := by
  have hs :=
    upperTailAux_three_scaled n (n - 2) (by omega)
  have hsub :
      2 ^ (n - 2) - 1 ≤ 2 ^ (n - 2) :=
    Nat.sub_le _ _
  have hs' :
      3 * 2 ^ (n - 2) * upperTailAux 2 n n 2 (n - 2) ≤
        8 * n ^ n * 2 ^ (n - 2) :=
    Nat.le_trans hs (Nat.mul_le_mul_left (8 * n ^ n) hsub)
  have hcancel :
      2 ^ (n - 2) *
            (3 * upperTailAux 2 n n 2 (n - 2)) ≤
        2 ^ (n - 2) * (8 * n ^ n) := by
    calc
      _ = 3 * 2 ^ (n - 2) *
            upperTailAux 2 n n 2 (n - 2) := by
        ac_rfl
      _ ≤ 8 * n ^ n * 2 ^ (n - 2) := hs'
      _ = _ := by ac_rfl
  have h8 :
      3 * upperTailAux 2 n n 2 (n - 2) ≤
        8 * n ^ n :=
    Nat.le_of_mul_le_mul_left hcancel
      (Nat.pow_pos (by omega))
  have h9 :
      3 * upperTailAux 2 n n 2 (n - 2) ≤
        3 * (3 * n ^ n) := by
    exact Nat.le_trans h8 (by omega)
  exact Nat.le_of_mul_le_mul_left h9 (by omega)


private theorem lowerTail_three_le_five_pow
    (n : Nat) (hn2 : 2 ≤ n) :
    lowerTailCount 2 n n 3 ≤ 5 * n ^ n := by
  have h0raw :=
    factorial_mul_binomialMass_two_self_le n 0 (by omega)
  have h1raw :=
    factorial_mul_binomialMass_two_self_le n 1 (by omega)
  have h2raw :=
    factorial_mul_binomialMass_two_self_le n 2 hn2
  have h0 :
      binomialMass 2 n n 0 ≤ n ^ n := by
    simpa [fact] using h0raw
  have h1 :
      binomialMass 2 n n 1 ≤ 2 * n ^ n := by
    simpa [fact] using h1raw
  have h2scaled :
      2 * binomialMass 2 n n 2 ≤ 4 * n ^ n := by
    simpa [fact] using h2raw
  have h2 :
      binomialMass 2 n n 2 ≤ 2 * n ^ n := by
    have hc :
        2 * binomialMass 2 n n 2 ≤
          2 * (2 * n ^ n) := by
      exact Nat.le_trans h2scaled (by omega)
    exact Nat.le_of_mul_le_mul_left hc (by omega)
  simp only [lowerTailCount]
  omega


/-- Elementary core-Nat replacement for the analytic inequality
(1 + 2/n)^n < e^2 < 8.  No division or reals are used in the proof. -/
theorem addTwo_pow_self_le_eight_mul_pow_self
    (n : Nat) (hn1 : 1 ≤ n) :
    (n + 2) ^ n ≤ 8 * n ^ n := by
  by_cases hn2 : 2 ≤ n
  · have hsplit :=
      lowerTail_add_upperTailAux 2 n n 2 (n - 2)
    have hsum : 2 + 1 + (n - 2) = n + 1 := by omega
    rw [hsum, lowerTail_full] at hsplit
    have hhead := lowerTail_three_le_five_pow n hn2
    have htail := upperTailAux_three_le_three_pow n hn2
    calc
      (n + 2) ^ n = (2 + n) ^ n := by
        rw [Nat.add_comm]
      _ = lowerTailCount 2 n n 3 +
            upperTailAux 2 n n 2 (n - 2) := hsplit
      _ ≤ 5 * n ^ n + 3 * n ^ n :=
        Nat.add_le_add hhead htail
      _ = 8 * n ^ n := by omega
  · have hn : n = 1 := by omega
    subst n
    simp


/-! ## ERRATA S3.2 / FixedAgent24nBound




R10 originally froze the 24n statement as an open arithmetic node.  The
combinatorial and Chernoff layers above reduce it to the following single Nat
inequality; the elementary Nat argument below now discharges that node.
-/




def FixedAgent24nArithmetic (n : Nat) : Prop :=
  (n + 2) ^ (6 * n * n) * 2 ^ (4 * n) ≤
    n ^ (6 * n * n) * 2 ^ (24 * n + 1)


/-- The arithmetic node is unconditional (in fact already for n ≥ 1). -/
theorem fixedAgent24nArithmetic
    (n : Nat) (hn1 : 1 ≤ n) :
    FixedAgent24nArithmetic n := by
  unfold FixedAgent24nArithmetic
  have hbase :=
    addTwo_pow_self_le_eight_mul_pow_self n hn1
  have hpow0 :=
    Nat.pow_le_pow_left hbase (6 * n)
  have hexp : 6 * n * n = n * (6 * n) := by
    ac_rfl
  have hpow :
      (n + 2) ^ (6 * n * n) ≤
        8 ^ (6 * n) * n ^ (6 * n * n) := by
    calc
      (n + 2) ^ (6 * n * n) =
          (n + 2) ^ (n * (6 * n)) := by rw [hexp]
      _ = ((n + 2) ^ n) ^ (6 * n) := by
        rw [Nat.pow_mul]
      _ ≤ (8 * n ^ n) ^ (6 * n) := hpow0
      _ = 8 ^ (6 * n) * (n ^ n) ^ (6 * n) := by
        rw [Nat.mul_pow]
      _ = 8 ^ (6 * n) * n ^ (n * (6 * n)) := by
        rw [← Nat.pow_mul]
      _ = 8 ^ (6 * n) * n ^ (6 * n * n) := by
        rw [← hexp]
  have htwo :
      8 ^ (6 * n) * 2 ^ (4 * n) ≤
        2 ^ (24 * n + 1) := by
    have h8 : (8 : Nat) = 2 ^ 3 := by rfl
    rw [h8]
    calc
      (2 ^ 3) ^ (6 * n) * 2 ^ (4 * n) =
          2 ^ (3 * (6 * n)) * 2 ^ (4 * n) := by
        rw [← Nat.pow_mul]
      _ = 2 ^ (3 * (6 * n) + 4 * n) := by
        rw [Nat.pow_add]
      _ = 2 ^ (22 * n) := by
        congr 1
        omega
      _ ≤ 2 ^ (24 * n + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have hmul :=
    Nat.mul_le_mul_right (2 ^ (4 * n)) hpow
  calc
    (n + 2) ^ (6 * n * n) * 2 ^ (4 * n) ≤
        (8 ^ (6 * n) * n ^ (6 * n * n)) *
          2 ^ (4 * n) := hmul
    _ = n ^ (6 * n * n) *
          (8 ^ (6 * n) * 2 ^ (4 * n)) := by
      ac_rfl
    _ ≤ n ^ (6 * n * n) * 2 ^ (24 * n + 1) :=
      Nat.mul_le_mul_left _ htwo




/-- The exact ERRATA S3.2 bound follows from the single explicit arithmetic
inequality FixedAgent24nArithmetic. -/
theorem fixedAgent24nBound_of_arithmetic
    (n : Nat) (hn2 : 2 ≤ n)
    (harith : FixedAgent24nArithmetic n) :
    twoEdgeUpperTailCount n (6 * n * n) (24 * n) *
        2 ^ (4 * n) ≤
      n ^ (6 * n * n) := by
  apply twoEdgeUpperTail_scaled_of_arithmetic
    n (6 * n * n) (24 * n) (4 * n) hn2
  simpa [UpperTailScaleArithmetic, FixedAgent24nArithmetic] using harith


/-- Unconditional ERRATA S3.2 bound for every n ≥ 2. -/
theorem fixedAgent24nBound
    (n : Nat) (hn2 : 2 ≤ n) :
    twoEdgeUpperTailCount n (6 * n * n) (24 * n) *
        2 ^ (4 * n) ≤
      n ^ (6 * n * n) := by
  exact fixedAgent24nBound_of_arithmetic n hn2
    (fixedAgent24nArithmetic n (by omega))




/-- If the threshold is at least the horizon, the strict upper tail is empty. -/
theorem twoEdgeUpperTailCount_eq_zero_of_horizon_le_threshold
    (n T a : Nat) (hTa : T ≤ a) :
    twoEdgeUpperTailCount n T a = 0 := by
  unfold twoEdgeUpperTailCount upperTailCount
  have hz : T - a = 0 := Nat.sub_eq_zero_of_le hTa
  simp [hz, upperTailAux]




/-- Small-ring part of FixedAgent24nBound: for 2 ≤ n ≤ 4, 24n is at
least the whole 6n^2 horizon, so the bad numerator is exactly zero. -/
theorem fixedAgent24nBound_small
    (n : Nat) (hn2 : 2 ≤ n) (hn4 : n ≤ 4) :
    twoEdgeUpperTailCount n (6 * n * n) (24 * n) *
        2 ^ (4 * n) ≤
      n ^ (6 * n * n) := by
  have hcases : n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hcases with rfl | rfl | rfl <;>
    simp [twoEdgeUpperTailCount, upperTailCount, upperTailAux]




end PPL.Probability




#print axioms PPL.Probability.exactTwoEdgeWordCount_eq_closed
#print axioms PPL.Probability.twoEdgeUpperTailCount_mul_twoPow_le
#print axioms PPL.Probability.twoEdgeLowerTailCount_mul_twoPow_le
#print axioms PPL.Probability.addTwo_pow_self_le_eight_mul_pow_self
#print axioms PPL.Probability.fixedAgent24nArithmetic
#print axioms PPL.Probability.fixedAgent24nBound
#print axioms PPL.Probability.fixedAgent24nBound_small

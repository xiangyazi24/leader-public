import Leader.PPL.Probability.RawCounts

set_option autoImplicit false

namespace PPL.Probability

/-!
# Predictable-host encounter projection

A scheduler letter e : Fin n names the directed edge from e to its right
neighbor.  Therefore the two scheduler letters incident to a host x are x
itself and ring.leftNeighbor x.

The crucial predictability condition is represented by the type of host:
host : List (Fin n) → Fin n.  At a letter e, host is evaluated only on the
already-consumed pre, before e is inspected.
-/

def incidentLetter {n : Nat} (ring : DirectedRing n)
    (x e : Fin n) : Bool :=
  twoEdgeLetter x (ring.leftNeighbor x) e

def predictableHostHitsAux {n : Nat} (ring : DirectedRing n)
    (host : List (Fin n) → Fin n) :
    List (Fin n) → List (Fin n) → Nat
  | _, [] => 0
  | pre, e :: rest =>
      (if incidentLetter ring (host pre) e then 1 else 0) +
        predictableHostHitsAux ring host (pre ++ [e]) rest

def predictableHostHits {n : Nat} (ring : DirectedRing n)
    (host : List (Fin n) → Fin n) (word : DetSchedule n) : Nat :=
  predictableHostHitsAux ring host [] word

def exactPredictableHostWordCount {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (T m : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word => decide (predictableHostHits ring host word = m))

def predictableHostUpperTailCount {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (T a : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word => decide (a < predictableHostHits ring host word))

def predictableHostLowerTailCount {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (T a : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word => decide (predictableHostHits ring host word < a))

private theorem leftNeighbor_ne_self {n : Nat}
    (ring : DirectedRing n) (hn2 : 2 ≤ n) (x : Fin n) :
    ring.leftNeighbor x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  change (x.val + n - 1) % n = x.val at hv
  rcases Nat.eq_zero_or_pos x.val with h0 | hpos
  · have h1 : (x.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h0] at hv
    omega
  · have h1 : (x.val + n - 1) % n = x.val - 1 := by
      rw [show x.val + n - 1 = (x.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1] at hv
    omega

private theorem countP_eq_sum_indicator_local
    {A : Type} (xs : List A) (p : A → Bool) :
    xs.countP p =
      (xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
      cases h : p x <;> simp [h, Nat.add_comm]

private theorem ofFn_sum_eq_local {n : Nat} (f g : Fin n → Nat)
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

private theorem ofFn_sum_add_local {n : Nat} (f g : Fin n → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

private theorem ofFn_sum_const_local (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

private theorem sum_spike_local (n : Nat) :
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
          have hh := ofFn_sum_eq_local
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
          simpa only [ofFn_sum_const_local, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq_local
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

private theorem twoEdgeLetter_count_local {n : Nat}
    (a b : Fin n) (hab : a ≠ b) :
    (List.ofFn (fun e : Fin n => e)).countP
      (twoEdgeLetter a b) = 2 := by
  rw [countP_eq_sum_indicator_local, List.map_ofFn]
  calc
    (List.ofFn
        (fun e : Fin n =>
          if twoEdgeLetter a b e then 1 else 0)).sum =
        (List.ofFn
          (fun e : Fin n =>
            (if e = a then 1 else 0) +
              (if e = b then 1 else 0))).sum := by
          apply ofFn_sum_eq_local
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
      ofFn_sum_add_local _ _
    _ = 2 := by rw [sum_spike_local, sum_spike_local]

private theorem countP_not_add_countP_local
    {A : Type} (p : A → Bool) (xs : List A) :
    xs.countP (fun x => !p x) + xs.countP p = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.length_cons]
      cases hp : p x <;>
        simp [hp, Nat.add_assoc, Nat.add_comm] at * <;>
        omega

private theorem twoEdgeCold_count_local {n : Nat}
    (hn2 : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    (List.ofFn (fun e : Fin n => e)).countP
      (fun e => !twoEdgeLetter a b e) = n - 2 := by
  have hpart := countP_not_add_countP_local
    (twoEdgeLetter a b) (List.ofFn (fun e : Fin n => e))
  rw [twoEdgeLetter_count_local a b hab] at hpart
  simp only [List.length_ofFn] at hpart
  omega

private theorem incidentLetter_count {n : Nat}
    (ring : DirectedRing n) (hn2 : 2 ≤ n) (x : Fin n) :
    (List.ofFn (fun e : Fin n => e)).countP
      (incidentLetter ring x) = 2 := by
  have hne : x ≠ ring.leftNeighbor x := by
    intro h
    exact leftNeighbor_ne_self ring hn2 x h.symm
  exact twoEdgeLetter_count_local x (ring.leftNeighbor x) hne

private theorem incidentCold_count {n : Nat}
    (ring : DirectedRing n) (hn2 : 2 ≤ n) (x : Fin n) :
    (List.ofFn (fun e : Fin n => e)).countP
      (fun e => !incidentLetter ring x e) = n - 2 := by
  have hne : x ≠ ring.leftNeighbor x := by
    intro h
    exact leftNeighbor_ne_self ring hn2 x h.symm
  simpa [incidentLetter] using
    (twoEdgeCold_count_local hn2 x (ring.leftNeighbor x) hne)

private theorem predictableHostHitsAux_append_singleton {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (pre word : List (Fin n)) (e : Fin n) :
    predictableHostHitsAux ring host pre (word ++ [e]) =
      predictableHostHitsAux ring host pre word +
        (if incidentLetter ring (host (pre ++ word)) e then 1 else 0) := by
  induction word generalizing pre with
  | nil =>
      simp [predictableHostHitsAux]
  | cons x xs ih =>
      simp only [List.cons_append, predictableHostHitsAux]
      rw [ih (pre := pre ++ [x])]
      have hp :
          (pre ++ [x]) ++ xs = pre ++ (x :: xs) := by
        simp [List.append_assoc]
      rw [hp]
      omega

private theorem predictableHostHits_append_singleton {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (word : DetSchedule n) (e : Fin n) :
    predictableHostHits ring host (word ++ [e]) =
      predictableHostHits ring host word +
        (if incidentLetter ring (host word) e then 1 else 0) := by
  simpa [predictableHostHits] using
    (predictableHostHitsAux_append_singleton ring host [] word e)

private theorem predictable_extension_exact_count {n : Nat}
    (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n) (word : DetSchedule n) (m : Nat) :
    (List.ofFn (fun e : Fin n => word ++ [e])).countP
        (fun u => decide (predictableHostHits ring host u = m)) =
      (if predictableHostHits ring host word + 1 = m then 2 else 0) +
        (if predictableHostHits ring host word = m then n - 2 else 0) := by
  have hmap :
      List.ofFn (fun e : Fin n => word ++ [e]) =
        (List.ofFn (fun e : Fin n => e)).map
          (fun e => word ++ [e]) := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, List.countP_map]
  simp only [Function.comp_def]
  by_cases hplus : predictableHostHits ring host word + 1 = m
  · have heq : predictableHostHits ring host word ≠ m := by omega
    have hp :
        (fun e : Fin n =>
          decide (predictableHostHits ring host (word ++ [e]) = m)) =
        incidentLetter ring (host word) := by
      funext e
      rw [predictableHostHits_append_singleton]
      cases he : incidentLetter ring (host word) e <;>
        simp [he, hplus, heq]
    rw [hp, incidentLetter_count ring hn2 (host word)]
    simp [hplus, heq]
  · by_cases heq : predictableHostHits ring host word = m
    · have hp :
          (fun e : Fin n =>
            decide (predictableHostHits ring host (word ++ [e]) = m)) =
          (fun e => !incidentLetter ring (host word) e) := by
        funext e
        rw [predictableHostHits_append_singleton]
        cases he : incidentLetter ring (host word) e <;>
          simp [he, hplus, heq]
      rw [hp, incidentCold_count ring hn2 (host word)]
      simp [hplus, heq]
    · have hp :
          (fun e : Fin n =>
            decide (predictableHostHits ring host (word ++ [e]) = m)) =
          (fun _ => false) := by
        funext e
        rw [predictableHostHits_append_singleton]
        cases he : incidentLetter ring (host word) e <;>
          simp [he, hplus, heq]
      rw [hp]
      simp [hplus, heq]

private theorem sum_map_add_local
    {A : Type} (xs : List A) (f g : A → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

private theorem sum_if_count_local
    {A : Type} (xs : List A) (p : A → Bool) (c : Nat) :
    (xs.map (fun x => if p x then c else 0)).sum =
      xs.countP p * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.countP_cons, ih]
      cases p x <;> simp [Nat.add_mul, Nat.add_comm]

private theorem exactPredictableHostWordCount_succ_zero {n T : Nat}
    (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n) :
    exactPredictableHostWordCount ring host (T + 1) 0 =
      (n - 2) * exactPredictableHostWordCount ring host T 0 := by
  unfold exactPredictableHostWordCount
  rw [allSchedules, List.countP_flatMap]
  have hmap :
      (List.map
          (List.countP
              (fun u => decide (predictableHostHits ring host u = 0)) ∘
            (fun word =>
              List.ofFn (fun e : Fin n => word ++ [e])))
          (allSchedules n T)) =
        (List.map
          (fun word =>
            if decide (predictableHostHits ring host word = 0)
            then n - 2 else 0)
          (allSchedules n T)) := by
    apply List.map_congr_left
    intro word hword
    change
      (List.ofFn (fun e : Fin n => word ++ [e])).countP
          (fun u => decide (predictableHostHits ring host u = 0)) = _
    rw [predictable_extension_exact_count hn2 ring host word 0]
    by_cases h : predictableHostHits ring host word = 0 <;> simp [h]
  rw [hmap, sum_if_count_local]
  ac_rfl

private theorem exactPredictableHostWordCount_succ_succ {n T m : Nat}
    (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n) :
    exactPredictableHostWordCount ring host (T + 1) (m + 1) =
      2 * exactPredictableHostWordCount ring host T m +
        (n - 2) * exactPredictableHostWordCount ring host T (m + 1) := by
  unfold exactPredictableHostWordCount
  rw [allSchedules, List.countP_flatMap]
  have hmap :
      (List.map
          (List.countP
              (fun u =>
                decide (predictableHostHits ring host u = m + 1)) ∘
            (fun word =>
              List.ofFn (fun e : Fin n => word ++ [e])))
          (allSchedules n T)) =
        (List.map
          (fun word =>
            (if decide (predictableHostHits ring host word = m)
              then 2 else 0) +
            (if decide (predictableHostHits ring host word = m + 1)
              then n - 2 else 0))
          (allSchedules n T)) := by
    apply List.map_congr_left
    intro word hword
    change
      (List.ofFn (fun e : Fin n => word ++ [e])).countP
          (fun u =>
            decide (predictableHostHits ring host u = m + 1)) = _
    rw [predictable_extension_exact_count hn2 ring host word (m + 1)]
    by_cases h0 : predictableHostHits ring host word = m
    · have hp : predictableHostHits ring host word + 1 = m + 1 := by
        omega
      have h1 : predictableHostHits ring host word ≠ m + 1 := by
        omega
      simp [h0, hp, h1]
    · by_cases h1 : predictableHostHits ring host word = m + 1
      · have hp :
            predictableHostHits ring host word + 1 ≠ m + 1 := by
          omega
        simp [h0, h1, hp]
      · have hp :
            predictableHostHits ring host word + 1 ≠ m + 1 := by
          omega
        simp [h0, h1, hp]
  rw [hmap, sum_map_add_local, sum_if_count_local, sum_if_count_local]
  ac_rfl

private theorem exactPredictableHostWordCount_eq_mass
    {n T m : Nat} (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n) :
    exactPredictableHostWordCount ring host T m =
      binomialMass 2 (n - 2) T m := by
  induction T generalizing m with
  | zero =>
      cases m <;>
        simp [exactPredictableHostWordCount, allSchedules,
          predictableHostHits, predictableHostHitsAux, binomialMass]
  | succ T ih =>
      cases m with
      | zero =>
          rw [exactPredictableHostWordCount_succ_zero hn2 ring host,
            binomialMass, ih]
      | succ m =>
          rw [exactPredictableHostWordCount_succ_succ hn2 ring host,
            binomialMass, ih, ih]

/-- Exact predictable-host mass.  Adaptivity to the pre-letter prefix does not
change the count: each node of the schedule tree still has exactly two hot
children and n-2 cold children. -/
theorem exactPredictableHostWordCount_eq_closed
    (n T m : Nat) (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n) :
    exactPredictableHostWordCount ring host T m =
      chooseCount T m * 2 ^ m * (n - 2) ^ (T - m) := by
  rw [exactPredictableHostWordCount_eq_mass hn2 ring host,
    binomialMass_eq_closed]

private theorem countP_lt_succ
    {A : Type} (xs : List A) (f : A → Nat) (a : Nat) :
    xs.countP (fun x => decide (f x < a + 1)) =
      xs.countP (fun x => decide (f x < a)) +
        xs.countP (fun x => decide (f x = a)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
      by_cases hlt : f x < a
      · have hs : f x < a + 1 := by omega
        have heq : f x ≠ a := by omega
        simp [hlt, hs, heq] <;> omega
      · by_cases heq : f x = a
        · have hs : f x < a + 1 := by omega
          simp [hlt, heq, hs] <;> omega
        · have hs : ¬f x < a + 1 := by omega
          simp [hlt, heq, hs]

/-- Exact lower-tail law for a predictable host. -/
theorem predictableHostLowerTailCount_eq
    (n T a : Nat) (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n) :
    predictableHostLowerTailCount ring host T a =
      twoEdgeLowerTailCount n T a := by
  unfold twoEdgeLowerTailCount
  induction a with
  | zero =>
      simp [predictableHostLowerTailCount, lowerTailCount]
  | succ a ih =>
      change
        (allSchedules n T).countP
            (fun word =>
              decide (predictableHostHits ring host word < a + 1)) =
          lowerTailCount 2 (n - 2) T (a + 1)
      rw [countP_lt_succ, lowerTailCount]
      change
        predictableHostLowerTailCount ring host T a +
            exactPredictableHostWordCount ring host T a =
          lowerTailCount 2 (n - 2) T a +
            binomialMass 2 (n - 2) T a
      rw [ih, exactPredictableHostWordCount_eq_mass hn2 ring host]

private theorem predictableHostHitsAux_le_length {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (pre word : List (Fin n)) :
    predictableHostHitsAux ring host pre word ≤ word.length := by
  induction word generalizing pre with
  | nil =>
      simp [predictableHostHitsAux]
  | cons e rest ih =>
      have htail := ih (pre := pre ++ [e])
      cases h : incidentLetter ring (host pre) e <;>
        simp [predictableHostHitsAux, h] <;> omega

private theorem predictableHostHits_le_length {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (word : DetSchedule n) :
    predictableHostHits ring host word ≤ word.length := by
  simpa [predictableHostHits] using
    (predictableHostHitsAux_le_length ring host [] word)

private theorem countP_lt_succ_add_countP_gt
    {A : Type} (xs : List A) (f : A → Nat) (a : Nat) :
    xs.countP (fun x => decide (f x < a + 1)) +
        xs.countP (fun x => decide (a < f x)) =
      xs.length := by
  have hpart := countP_not_add_countP_local
    (fun x => decide (a < f x)) xs
  have hp :
      (fun x => !decide (a < f x)) =
        (fun x => decide (f x < a + 1)) := by
    funext x
    by_cases hgt : a < f x
    · have hnot : ¬f x < a + 1 := by omega
      simp [hgt, hnot]
    · have hlt : f x < a + 1 := by omega
      simp [hgt, hlt]
  rw [hp] at hpart
  exact hpart

private theorem binomialMass_zero_of_lt_local
    (hot cold : Nat) {T m : Nat} (h : T < m) :
    binomialMass hot cold T m = 0 := by
  induction T generalizing m with
  | zero =>
      cases m with
      | zero => omega
      | succ m => rfl
  | succ T ih =>
      cases m with
      | zero => omega
      | succ m =>
          simp only [binomialMass]
          rw [ih (by omega), ih (by omega)]
          simp

private theorem lowerTail_horizon_succ_local
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

private theorem lowerTail_full_local
    (hot cold T : Nat) :
    lowerTailCount hot cold T (T + 1) = (hot + cold) ^ T := by
  induction T with
  | zero =>
      simp [lowerTailCount, binomialMass]
  | succ T ih =>
      rw [lowerTail_horizon_succ_local hot cold T (T + 1)]
      have hz :
          binomialMass hot cold T (T + 1) = 0 :=
        binomialMass_zero_of_lt_local hot cold (by omega)
      have hsame :
          lowerTailCount hot cold T (T + 2) =
            lowerTailCount hot cold T (T + 1) := by
        rw [lowerTailCount, hz, Nat.add_zero]
      rw [hsame, ih, Nat.pow_succ, Nat.mul_add]
      ac_rfl

private theorem lowerTail_add_mass_sum
    (hot cold T a k : Nat) :
    lowerTailCount hot cold T (a + 1 + k) =
      lowerTailCount hot cold T (a + 1) +
        ((List.range k).map
          (fun d => binomialMass hot cold T (a + 1 + d))).sum := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [show a + 1 + (k + 1) = (a + 1 + k) + 1 by omega,
        lowerTailCount, ih, List.range_succ, List.map_append,
        List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      omega

private theorem twoEdgeUpperTailCount_eq_mass_sum
    (n T a : Nat) :
    twoEdgeUpperTailCount n T a =
      ((List.range (T - a)).map
        (fun d => binomialMass 2 (n - 2) T (a + 1 + d))).sum := by
  rw [twoEdgeUpperTailCount_eq_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  simp only
  rw [binomialMass_eq_closed]

private theorem twoEdge_tail_partition_of_lt
    (n T a : Nat) (hn2 : 2 ≤ n) (ha : a < T) :
    twoEdgeLowerTailCount n T (a + 1) +
        twoEdgeUpperTailCount n T a =
      n ^ T := by
  have hsplit :=
    lowerTail_add_mass_sum 2 (n - 2) T a (T - a)
  have hidx : a + 1 + (T - a) = T + 1 := by omega
  rw [hidx, lowerTail_full_local] at hsplit
  have hbase : 2 + (n - 2) = n := by omega
  rw [hbase] at hsplit
  have hu := twoEdgeUpperTailCount_eq_mass_sum n T a
  rw [← hu] at hsplit
  change
    lowerTailCount 2 (n - 2) T (a + 1) +
        twoEdgeUpperTailCount n T a =
      n ^ T
  exact hsplit.symm

/-- Exact upper-tail law for a predictable host. -/
theorem predictableHostUpperTailCount_eq
    (n T a : Nat) (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n) :
    predictableHostUpperTailCount ring host T a =
      twoEdgeUpperTailCount n T a := by
  by_cases hTa : T ≤ a
  · have hz : predictableHostUpperTailCount ring host T a = 0 := by
      unfold predictableHostUpperTailCount
      apply List.countP_eq_zero.mpr
      intro word hword hbad
      have hlt : a < predictableHostHits ring host word :=
        of_decide_eq_true hbad
      have hlen := allSchedules_schedule_length n T word hword
      have hh := predictableHostHits_le_length ring host word
      omega
    rw [hz, twoEdgeUpperTailCount_eq_zero_of_horizon_le_threshold
      n T a hTa]
  · have ha : a < T := by omega
    have hpart :=
      countP_lt_succ_add_countP_gt
        (allSchedules n T)
        (fun word => predictableHostHits ring host word) a
    change
      predictableHostLowerTailCount ring host T (a + 1) +
          predictableHostUpperTailCount ring host T a =
        (allSchedules n T).length at hpart
    rw [predictableHostLowerTailCount_eq n T (a + 1) hn2 ring host,
      allSchedules_length] at hpart
    have hraw := twoEdge_tail_partition_of_lt n T a hn2 ha
    omega

/-! ## Prefix-measurable stopping -/

def stoppedPredictableHostHitsAux {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) :
    List (Fin n) → List (Fin n) → Nat
  | _, [] => 0
  | pre, e :: rest =>
      if stop pre then 0
      else
        (if incidentLetter ring (host pre) e then 1 else 0) +
          stoppedPredictableHostHitsAux ring host stop
            (pre ++ [e]) rest

def stoppedPredictableHostHits {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) (word : DetSchedule n) : Nat :=
  stoppedPredictableHostHitsAux ring host stop [] word

def stopReachedAux {n : Nat} (stop : List (Fin n) → Bool) :
    List (Fin n) → List (Fin n) → Bool
  | pre, [] => stop pre
  | pre, e :: rest =>
      stop pre || stopReachedAux stop (pre ++ [e]) rest

def stopReached {n : Nat} (stop : List (Fin n) → Bool)
    (word : DetSchedule n) : Bool :=
  stopReachedAux stop [] word

def stoppedPredictableHostUpperTailCount {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) (T a : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word =>
      decide (a < stoppedPredictableHostHits ring host stop word))

def stoppedPredictableHostLowerTailCount {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) (T a : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word =>
      decide (stoppedPredictableHostHits ring host stop word < a))

/-- For lower-tail use in a protocol proof, an early stop may be success.
This numerator counts only words with too few stopped hits on which the stopping
predicate was never reached, including at the full horizon pre. -/
def stoppedPredictableHostLowerFailureCount {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) (T a : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word =>
      decide
        (stopReached stop word = false ∧
          stoppedPredictableHostHits ring host stop word < a))

private theorem stoppedPredictableHostHitsAux_le {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (pre word : List (Fin n)) :
    stoppedPredictableHostHitsAux ring host stop pre word ≤
      predictableHostHitsAux ring host pre word := by
  induction word generalizing pre with
  | nil =>
      simp [stoppedPredictableHostHitsAux, predictableHostHitsAux]
  | cons e rest ih =>
      cases hs : stop pre with
      | false =>
          have htail := ih (pre := pre ++ [e])
          cases hi : incidentLetter ring (host pre) e <;>
            simp [stoppedPredictableHostHitsAux,
              predictableHostHitsAux, hs, hi] at * <;>
            omega
      | true =>
          simp [stoppedPredictableHostHitsAux,
            predictableHostHitsAux, hs]

private theorem stoppedPredictableHostHits_le {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) (word : DetSchedule n) :
    stoppedPredictableHostHits ring host stop word ≤
      predictableHostHits ring host word := by
  simpa [stoppedPredictableHostHits, predictableHostHits] using
    (stoppedPredictableHostHitsAux_le ring host stop [] word)

private theorem stoppedPredictableHostHitsAux_eq_of_stopReachedAux_false
    {n : Nat} (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (pre word : List (Fin n))
    (hstop : stopReachedAux stop pre word = false) :
    stoppedPredictableHostHitsAux ring host stop pre word =
      predictableHostHitsAux ring host pre word := by
  induction word generalizing pre with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hs : stop pre with
      | false =>
          have hrest :
              stopReachedAux stop (pre ++ [e]) rest = false := by
            simpa [stopReachedAux, hs] using hstop
          have htail := ih (pre := pre ++ [e]) hrest
          simp [stoppedPredictableHostHitsAux,
            predictableHostHitsAux, hs, htail]
      | true =>
          simp [stopReachedAux, hs] at hstop

private theorem stoppedPredictableHostHits_eq_of_stopReached_false
    {n : Nat} (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) (word : DetSchedule n)
    (hstop : stopReached stop word = false) :
    stoppedPredictableHostHits ring host stop word =
      predictableHostHits ring host word := by
  simpa [stoppedPredictableHostHits, predictableHostHits, stopReached] using
    (stoppedPredictableHostHitsAux_eq_of_stopReachedAux_false
      ring host stop [] word hstop)

private theorem countP_mono_local
    {A : Type} (xs : List A) (p q : A → Bool)
    (hpq : ∀ x, p x = true → q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      have htail := ih
      cases hp : p x with
      | false =>
          cases hq : q x <;> simp [hp, hq] <;> omega
      | true =>
          have hqx : q x = true := hpq x hp
          simp [hp, hqx]
          omega

/-- Stopping can only remove hits, so the stopped strict upper tail is
dominated by the exact predictable/fixed-site upper tail. -/
theorem stoppedPredictableHostUpperTailCount_le
    (n T a : Nat) (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) :
    stoppedPredictableHostUpperTailCount ring host stop T a ≤
      twoEdgeUpperTailCount n T a := by
  unfold stoppedPredictableHostUpperTailCount
  calc
    (allSchedules n T).countP
        (fun word =>
          decide (a < stoppedPredictableHostHits ring host stop word)) ≤
      (allSchedules n T).countP
        (fun word =>
          decide (a < predictableHostHits ring host word)) := by
      apply countP_mono_local
      intro word hbad
      have hlt :
          a < stoppedPredictableHostHits ring host stop word :=
        of_decide_eq_true hbad
      have hle :=
        stoppedPredictableHostHits_le ring host stop word
      have hfull :
          a < predictableHostHits ring host word :=
        Nat.lt_of_lt_of_le hlt hle
      simp [hfull]
    _ = predictableHostUpperTailCount ring host T a := rfl
    _ = twoEdgeUpperTailCount n T a :=
      predictableHostUpperTailCount_eq n T a hn2 ring host

/-- The naive stopped lower tail goes in the opposite direction: every word
that has too few full predictable-host hits also has too few stopped hits. -/
theorem twoEdgeLowerTailCount_le_stoppedPredictableHostLowerTailCount
    (n T a : Nat) (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) :
    twoEdgeLowerTailCount n T a ≤
      stoppedPredictableHostLowerTailCount ring host stop T a := by
  rw [← predictableHostLowerTailCount_eq n T a hn2 ring host]
  unfold predictableHostLowerTailCount
  unfold stoppedPredictableHostLowerTailCount
  apply countP_mono_local
  intro word hbad
  have hlt : predictableHostHits ring host word < a :=
    of_decide_eq_true hbad
  have hle := stoppedPredictableHostHits_le ring host stop word
  have hstopped :
      stoppedPredictableHostHits ring host stop word < a :=
    Nat.lt_of_le_of_lt hle hlt
  simp [hstopped]

/-- Smallest nontrivial counterexample to the false inequality
stopped-lower-tail ≤ fixed lower tail, under the intended domain n ≥ 2:
n=2, T=1, a=1, constant host 0, and stop immediately. -/
theorem stoppedPredictableHostLowerTail_naive_counterexample :
    ∃ (ring : DirectedRing 2)
      (host : List (Fin 2) → Fin 2)
      (stop : List (Fin 2) → Bool),
      stoppedPredictableHostLowerTailCount ring host stop 1 1 = 2 ∧
        twoEdgeLowerTailCount 2 1 1 = 0 := by
  refine ⟨⟨by omega⟩, (fun _ => (0 : Fin 2)), (fun _ => true), ?_⟩
  decide

/-- If an early stop is success, the bad lower-tail event is
(no stop by the horizon) AND (too few stopped hits).  On no-stop words the
stopped and full predictable-host hit counts are equal, so this bad numerator
is dominated by the exact fixed lower tail. -/
theorem stoppedPredictableHostLowerFailureCount_le
    (n T a : Nat) (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) :
    stoppedPredictableHostLowerFailureCount ring host stop T a ≤
      twoEdgeLowerTailCount n T a := by
  unfold stoppedPredictableHostLowerFailureCount
  calc
    (allSchedules n T).countP
        (fun word =>
          decide
            (stopReached stop word = false ∧
              stoppedPredictableHostHits ring host stop word < a)) ≤
      (allSchedules n T).countP
        (fun word =>
          decide (predictableHostHits ring host word < a)) := by
      apply countP_mono_local
      intro word hbad
      have hb :
          stopReached stop word = false ∧
            stoppedPredictableHostHits ring host stop word < a :=
        of_decide_eq_true hbad
      have heq :=
        stoppedPredictableHostHits_eq_of_stopReached_false
          ring host stop word hb.1
      have hlt : predictableHostHits ring host word < a := by
        simpa [heq] using hb.2
      simp [hlt]
    _ = predictableHostLowerTailCount ring host T a := rfl
    _ = twoEdgeLowerTailCount n T a :=
      predictableHostLowerTailCount_eq n T a hn2 ring host

/-- Closed interface for the open-node name in the frozen plan.
The stopped lower clause is deliberately the success-aware bad event above;
the naive stopped lower domination is false, as certified by the preceding
counterexample. -/
def PredictableHostTails : Prop :=
  ∀ (n T a : Nat) (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n),
    predictableHostUpperTailCount ring host T a =
        twoEdgeUpperTailCount n T a ∧
    predictableHostLowerTailCount ring host T a =
        twoEdgeLowerTailCount n T a ∧
    ∀ stop : List (Fin n) → Bool,
      stoppedPredictableHostUpperTailCount ring host stop T a ≤
          twoEdgeUpperTailCount n T a ∧
      stoppedPredictableHostLowerFailureCount ring host stop T a ≤
          twoEdgeLowerTailCount n T a

theorem predictableHostTails : PredictableHostTails := by
  intro n T a hn2 ring host
  refine
    ⟨predictableHostUpperTailCount_eq n T a hn2 ring host,
      predictableHostLowerTailCount_eq n T a hn2 ring host, ?_⟩
  intro stop
  exact
    ⟨stoppedPredictableHostUpperTailCount_le
        n T a hn2 ring host stop,
      stoppedPredictableHostLowerFailureCount_le
        n T a hn2 ring host stop⟩

/-- Predictable-host form of the now-proved ERRATA S3.2 24n bound. -/
theorem predictableHost24nBound
    (n : Nat) (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n) :
    predictableHostUpperTailCount ring host (6 * n * n) (24 * n) *
        2 ^ (4 * n) ≤
      n ^ (6 * n * n) := by
  rw [predictableHostUpperTailCount_eq
    n (6 * n * n) (24 * n) hn2 ring host]
  exact fixedAgent24nBound n hn2

/-- The 24n bound remains valid after any prefix-measurable stopping rule. -/
theorem stoppedPredictableHost24nBound
    (n : Nat) (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool) :
    stoppedPredictableHostUpperTailCount
          ring host stop (6 * n * n) (24 * n) *
        2 ^ (4 * n) ≤
      n ^ (6 * n * n) := by
  have hdom :=
    stoppedPredictableHostUpperTailCount_le
      n (6 * n * n) (24 * n) hn2 ring host stop
  have hmul :=
    Nat.mul_le_mul_right (2 ^ (4 * n)) hdom
  exact Nat.le_trans hmul (fixedAgent24nBound n hn2)

end PPL.Probability

#print axioms PPL.Probability.exactPredictableHostWordCount_eq_closed
#print axioms PPL.Probability.predictableHostLowerTailCount_eq
#print axioms PPL.Probability.predictableHostUpperTailCount_eq
#print axioms PPL.Probability.stoppedPredictableHostUpperTailCount_le
#print axioms PPL.Probability.twoEdgeLowerTailCount_le_stoppedPredictableHostLowerTailCount
#print axioms PPL.Probability.stoppedPredictableHostLowerTail_naive_counterexample
#print axioms PPL.Probability.stoppedPredictableHostLowerFailureCount_le
#print axioms PPL.Probability.predictableHostTails
#print axioms PPL.Probability.predictableHost24nBound
#print axioms PPL.Probability.stoppedPredictableHost24nBound

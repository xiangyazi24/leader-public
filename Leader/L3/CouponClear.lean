import Leader.L3.FreshScan

/-!
Discrete coupon clearing and tolerant-scan recurrence.

The computable p_j recurrence below uses a sorted list of *unhit*
strictly-future edge labels. This is the complement of the paper's
set A of once-prematurely-hit labels. Removing an unhit label is the
same event as adding it to A. The denominator t-j removes the j
harmless already-behind labels from the first-step equation.
-/

namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference
open FreshCoupon
open FreshFixed

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-! ## Kernel-computable finite scanner recursion

The mathematical state uses B = unhit strictly future labels,
the complement of the paper's once-hit set A. Every progress or
first-hit transition strictly decreases the measure
(t-j)+B.length. A fuel parameter makes reduction structural.
The return value is an *unnormalised* positive-denominator fraction.
-/

/-- Remove the first occurrence of a future physical edge label. -/
def eraseAvailable (k : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
      if x = k then xs else x :: eraseAvailable k xs

theorem eraseAvailable_length_le (k : Nat) :
    ∀ xs : List Nat, (eraseAvailable k xs).length ≤ xs.length := by
  intro xs
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      by_cases hx : x = k
      · simp [eraseAvailable, hx]
      · simpa only [eraseAvailable, if_neg hx, List.length_cons]
          using Nat.succ_le_succ ih

theorem eraseAvailable_length_lt_of_mem (k : Nat) :
    ∀ xs : List Nat, k ∈ xs →
      (eraseAvailable k xs).length < xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro hk
      cases hk
  | cons x xs ih =>
      intro hk
      by_cases hx : x = k
      · simp [eraseAvailable, hx]
      · have htail : k ∈ xs := by
          rcases List.mem_cons.mp hk with hhead | hrest
          · exact False.elim (hx hhead.symm)
          · exact hrest
        have hh := ih htail
        simpa only [eraseAvailable, if_neg hx, List.length_cons]
          using Nat.succ_lt_succ hh

/-- Addition of unnormalised nonnegative rational pairs. -/
def pairAdd (a b : Nat × Nat) : Nat × Nat :=
  (a.1 * b.2 + b.1 * a.2, a.2 * b.2)

/-- Division of a pair by a positive natural integer is multiplication
of the denominator. The recursion uses it only when j<t. -/
def pairDiv (a : Nat × Nat) (k : Nat) : Nat × Nat :=
  (a.1, a.2 * k)

/-- The first-step equation is represented by the structurally
recursive successor-fuel branch. Failed (second-premature) letters
contribute zero and do not enter the sum; the j behind labels have
already been removed from the denominator. At exhausted fuel before
completion the result is zero; at terminal j>=t it is one. -/
def pFuel : Nat → Nat → Nat → List Nat → Nat × Nat
  | 0, t, j, _ =>
      if j < t then (0, 1) else (1, 1)
  | fuel + 1, t, j, B =>
      if j < t then
        let progress := pFuel fuel t (j + 1) (eraseAvailable (j + 1) B)
        let firstHits := B.map (fun k : Nat =>
          pFuel fuel t j (eraseAvailable k B))
        pairDiv (firstHits.foldl pairAdd progress) (t - j)
      else (1, 1)

/-- Exact first-step identity, without a general fixed-point assumption
or a non-reducing well-founded recursive definition. -/
theorem pFuel_first_step (fuel t j : Nat) (B : List Nat)
    (hj : j < t) :
    pFuel (fuel + 1) t j B =
      pairDiv
        ((B.map (fun k : Nat =>
          pFuel fuel t j (eraseAvailable k B))).foldl pairAdd
          (pFuel fuel t (j + 1) (eraseAvailable (j + 1) B)))
        (t - j) := by
  simp only [pFuel, if_pos hj]

theorem pFuel_terminal (fuel t : Nat) (B : List Nat) :
    pFuel fuel t t B = (1, 1) := by
  cases fuel <;> simp [pFuel]

/-- The sorted list of strictly future labels that are not in A.
A contains the labels already visited prematurely. -/
def futureUnhit (t j : Nat) (A : List Nat) : List Nat :=
  (List.range t).filter (fun k => decide (j < k ∧ k ∉ A))

/-- The paper's state value, with sufficient termination fuel for its
strictly decreasing measure; the value is an unnormalised fraction. -/
def pPairAt (t j : Nat) (A : List Nat) : Nat × Nat :=
  let B := futureUnhit t j A
  pFuel (t - j + B.length) t j B

/-- The first-step equation for the paper's state p_j(A). The child
calls use fuel one lower, exactly as in a finite absorbing chain.
This is equivalent to equation (certificate.tex:325-327), with B
the complement of A; all denominators are natural. -/
theorem pPairAt_first_step (t j : Nat) (A : List Nat)
    (hj : j < t) :
    pPairAt t j A =
      let B := futureUnhit t j A
      let fuel := t - j + B.length - 1
      pairDiv
        ((B.map (fun k : Nat =>
          pFuel fuel t j (eraseAvailable k B))).foldl pairAdd
          (pFuel fuel t (j + 1) (eraseAvailable (j + 1) B)))
        (t - j) := by
  let B := futureUnhit t j A
  let m := t - j + B.length
  have hmpos : 0 < m := by
    dsimp only [m]
    omega
  have hm : m - 1 + 1 = m := by omega
  change pFuel m t j B = _
  rw [← hm]
  exact pFuel_first_step (m - 1) t j B hj

/-- The exact integer pair used for the paper's p_scan(t)=p_0(∅). -/
def pPair (t : Nat) : Nat × Nat :=
  pPairAt t 0 []

/- All four numerical values are *cross-multiplied Nat statements*;
no Rat gcd normalization is needed in the kernel. -/
theorem p_scan_two :
    (pPair 2).1 * 4 = 3 * (pPair 2).2 := by decide +kernel

theorem p_scan_three :
    (pPair 3).1 * 54 = 23 * (pPair 3).2 := by decide +kernel

theorem p_scan_four :
    (pPair 4).1 * 6912 = 1325 * (pPair 4).2 := by decide +kernel

theorem p_scan_five :
    (pPair 5).1 * 10800000 = 767441 * (pPair 5).2 := by decide +kernel

/-- The rational interpretation can be used by a later stage/renewal
theorem, without forcing Rat arithmetic into the kernel certificates. -/
def pScanRat (t : Nat) : Rat :=
  ((pPair t).1 : Rat) / ((pPair t).2 : Rat)

/-- Exactly H_m, represented by an unnormalised natural fraction. -/
def harmonicPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | k + 1 => pairAdd (harmonicPair k) (1, k + 1)

/-- Unnormalised fraction for the coefficient
G(t)=(H_M M! L² + 2L + t) / p_scan(t). -/
def couponGPair (t : Nat) : Nat × Nat :=
  let M := t + 3
  let L := t + 2
  let h := harmonicPair M
  let p := pPair t
  ((h.1 * freshFact M * L ^ 2 + (2 * L + t) * h.2) * p.2,
    h.2 * p.1)

/-- Exact paper coefficient, rationally interpreted from the pair. -/
def couponG (t : Nat) : Rat :=
  ((couponGPair t).1 : Rat) / ((couponGPair t).2 : Rat)

/- The original Rat-decide goals are now kernel Nat certificates. -/
theorem couponG_three :
    (couponGPair 3).1 * 23 =
      2382102 * (couponGPair 3).2 := by decide +kernel

/- 6093 is the correct width-band ceiling for t=3 and N_t=17. -/
theorem couponG_three_band :
    6092 * 17 * (couponGPair 3).2 < (couponGPair 3).1 ∧
      (couponGPair 3).1 ≤ 6093 * 17 * (couponGPair 3).2 := by
  decide


/-! ## Exact scaled coupon-cover stopping cost

The coupon clock is the discrete physical-edge maskDrop process.
A scaled Bellman certificate avoids rounding each geometric coupon
stage separately. The scale n! is divisible by all 1 <= k <= n;
the rational n H_M does not depend on which common multiple is used.
-/

/-- Finite-horizon Bellman induction with an integer scale. -/
theorem costNumerator_scaled_potential {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (Φ : S → Nat) (scale : Nat)
    (hdrift : ∀ x, ¬ P x →
      scale * n +
        (List.ofFn (fun e : Fin n => Φ (next x e))).sum ≤ n * Φ x) :
    ∀ x T, scale * costNumerator next P x T ≤ n ^ T * Φ x := by
  classical
  intro x T
  induction T generalizing x with
  | zero =>
      simp only [costNumerator_zero, Nat.mul_zero]
      exact Nat.zero_le _
  | succ T ih =>
      by_cases hp : P x
      · rw [costNumerator_terminal next P x hp (T + 1)]
        exact Nat.zero_le _
      · rw [costNumerator_succ next P x hp T]
        have hs := ofFn_sum_le
          (fun e : Fin n =>
            scale * costNumerator next P (next x e) T)
          (fun e : Fin n =>
            n ^ T * Φ (next x e))
          (fun e => ih (next x e))
        calc
          scale * (n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                costNumerator next P (next x e) T)).sum) =
            n ^ T * (scale * n) +
              (List.ofFn (fun e : Fin n =>
                scale * costNumerator next P (next x e) T)).sum := by
                  rw [Nat.mul_add, ofFn_sum_mul_left, Nat.pow_succ]
                  ac_rfl
          _ ≤ n ^ T * (scale * n) +
              (List.ofFn (fun e : Fin n =>
                n ^ T * Φ (next x e))).sum :=
            Nat.add_le_add_left hs _
          _ = n ^ T * (scale * n +
              (List.ofFn (fun e : Fin n => Φ (next x e))).sum) := by
                  rw [Nat.mul_add, ofFn_sum_mul_left]
          _ ≤ n ^ T * (n * Φ x) :=
            Nat.mul_le_mul_left _ (hdrift x hp)
          _ = n ^ (T + 1) * Φ x := by
                  rw [Nat.pow_succ]
                  ac_rfl

theorem coupon_factorial_pos (m : Nat) :
    0 < freshFact m := by
  induction m with
  | zero => decide
  | succ m ih =>
      change 0 < (m + 1) * freshFact m
      exact Nat.mul_pos (by omega) ih

theorem coupon_factorial_dvd :
    ∀ (m k : Nat), 0 < k → k ≤ m → k ∣ freshFact m := by
  intro m
  induction m with
  | zero =>
      intro k hk hkm
      omega
  | succ m ih =>
      intro k hk hkm
      by_cases hlast : k = m + 1
      · subst k
        change m + 1 ∣ (m + 1) * freshFact m
        exact ⟨freshFact m, rfl⟩
      · have hle : k ≤ m := by omega
        obtain ⟨v, hv⟩ := ih k hk hle
        refine ⟨(m + 1) * v, ?_⟩
        change (m + 1) * freshFact m = k * ((m + 1) * v)
        rw [hv]
        ac_rfl

/-- Integer version of D*H_m when every 1<=k<=m divides D. -/
def scaledHarmonic (D : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => scaledHarmonic D m + D / (m + 1)

theorem scaledHarmonic_succ (D m : Nat) :
    scaledHarmonic D (m + 1) =
      scaledHarmonic D m + D / (m + 1) := rfl

theorem scaledHarmonic_step (D m : Nat) (hm : 0 < m) :
    scaledHarmonic D m =
      scaledHarmonic D (m - 1) + D / m := by
  cases m with
  | zero => omega
  | succ m =>
      simp only [scaledHarmonic, Nat.succ_eq_add_one,
        Nat.add_sub_cancel]

theorem coupon_maskSize_le {n : Nat} (r : Fin n → Bool) :
    maskSize r ≤ n := by
  have hs := ofFn_sum_le
    (fun e : Fin n => if r e then 1 else 0)
    (fun _ : Fin n => 1)
    (by intro e; cases r e <;> decide)
  simpa only [maskSize, ofFn_sum_const, Nat.mul_one] using hs

theorem coupon_maskDrop_false {n : Nat}
    (r : Fin n → Bool) (e : Fin n) (he : r e = false) :
    maskDrop r e = r := by
  funext i
  by_cases hi : i = e
  · subst i
    simp [maskDrop, he]
  · simp [maskDrop, hi]

theorem coupon_maskDrop_true {n : Nat}
    (r : Fin n → Bool) (e : Fin n) (he : r e = true) :
    maskSize (maskDrop r e) + 1 = maskSize r := by
  have hrow (i : Fin n) :
      (if r i then 1 else 0) =
        (if maskDrop r e i then 1 else 0) +
          (if i = e then 1 else 0) := by
    by_cases hi : i = e
    · subst i
      simp [maskDrop, he]
    · simp [maskDrop, hi]
  have hs := ofFn_sum_eq _ _ hrow
  rw [ofFn_sum_add, FreshFixed.sum_spike n e 1] at hs
  exact hs.symm

theorem coupon_mask_split_sum {n : Nat}
    (r : Fin n → Bool) (a b : Nat) :
    (List.ofFn (fun e : Fin n => if r e then b else a)).sum =
      (n - maskSize r) * a + maskSize r * b := by
  let z := (List.ofFn
    (fun e : Fin n => if r e then 0 else 1)).sum
  have htotal : maskSize r + z = n := by
    have hs := ofFn_sum_eq
      (fun e : Fin n =>
        (if r e then 1 else 0) +
          (if r e then 0 else 1))
      (fun _ : Fin n => 1)
      (by intro e; cases r e <;> rfl)
    rw [ofFn_sum_add, ofFn_sum_const] at hs
    simpa only [Nat.mul_one, maskSize, z] using hs
  have hz : z = n - maskSize r := by omega
  have hrow (e : Fin n) :
      (if r e then b else a) =
        a * (if r e then 0 else 1) +
          b * (if r e then 1 else 0) := by
    cases r e <;> simp
  calc
    (List.ofFn (fun e : Fin n => if r e then b else a)).sum =
      (List.ofFn (fun e : Fin n =>
        a * (if r e then 0 else 1) +
          b * (if r e then 1 else 0))).sum :=
        ofFn_sum_eq _ _ hrow
    _ = a * z + b * maskSize r := by
          rw [ofFn_sum_add, ofFn_sum_mul_left,
            ofFn_sum_mul_left]
          simp only [z, maskSize]
    _ = (n - maskSize r) * a + maskSize r * b := by
          rw [hz]
          ac_rfl

def couponPotential (n : Nat) (r : Fin n → Bool) : Nat :=
  n * scaledHarmonic (freshFact n) (maskSize r)

/-- Exact Bellman drift: the m unseen edges decrease the potential
by n*n!/m; the other n-m selections preserve the mask. -/
theorem couponPotential_drift {n : Nat}
    (r : Fin n → Bool) (hr : ¬ maskSize r = 0) :
    freshFact n * n +
      (List.ofFn (fun e : Fin n =>
        couponPotential n (maskDrop r e))).sum ≤
      n * couponPotential n r := by
  let m := maskSize r
  let D := freshFact n
  have hmpos : 0 < m := by
    dsimp only [m]
    omega
  have hmle : m ≤ n := coupon_maskSize_le r
  have hdvd : m ∣ D := by
    dsimp only [D]
    exact coupon_factorial_dvd n m hmpos hmle
  let v := scaledHarmonic D (m - 1)
  let h := D / m
  have hh : scaledHarmonic D m = v + h := by
    dsimp only [v, h]
    exact scaledHarmonic_step D m hmpos
  have hdiv : h * m = D := Nat.div_mul_cancel hdvd
  have hvalue (e : Fin n) :
      couponPotential n (maskDrop r e) =
        if r e then n * v else n * (v + h) := by
    by_cases he : r e = true
    · have hs : maskSize (maskDrop r e) + 1 = m :=
        coupon_maskDrop_true r e he
      have hsize : maskSize (maskDrop r e) = m - 1 := by
        omega
      simp [couponPotential, he, hsize, v]
      try rfl
    · have hf : r e = false := by
        cases hv : r e with
        | false => rfl
        | true => exact False.elim (he hv)
      have hs := coupon_maskDrop_false r e hf
      simp only [couponPotential, hf, hs, if_false]
      exact congrArg (fun x => n * x) hh
  have hsum :
      (List.ofFn (fun e : Fin n =>
        couponPotential n (maskDrop r e))).sum =
        (n - m) * (n * (v + h)) + m * (n * v) := by
    calc
      (List.ofFn (fun e : Fin n =>
        couponPotential n (maskDrop r e))).sum =
        (List.ofFn (fun e : Fin n =>
          if r e then n * v else n * (v + h))).sum :=
        ofFn_sum_eq _ _ hvalue
      _ = _ := by
        simpa only [m] using
          coupon_mask_split_sum r (n * (v + h)) (n * v)
  have hpart :
      D * n + m * (n * v) = m * (n * (v + h)) := by
    calc
      D * n + m * (n * v) =
        m * (n * h) + m * (n * v) := by
          rw [← hdiv]
          ac_rfl
      _ = m * (n * (v + h)) := by
          rw [Nat.mul_add, Nat.mul_add]
          ac_rfl
  have hsplit : n - m + m = n :=
    Nat.sub_add_cancel hmle
  change D * n +
      (List.ofFn (fun e : Fin n =>
        couponPotential n (maskDrop r e))).sum ≤
    n * (n * scaledHarmonic D m)
  rw [hsum, hh]
  apply Nat.le_of_eq
  calc
    D * n +
        ((n - m) * (n * (v + h)) + m * (n * v)) =
      (n - m) * (n * (v + h)) +
        (D * n + m * (n * v)) := by ac_rfl
    _ = (n - m) * (n * (v + h)) +
        m * (n * (v + h)) := by rw [hpart]
    _ = n * (n * (v + h)) := by
          rw [← Nat.add_mul, hsplit]

/-- Cross-multiplied exact finite-horizon coupon hitting-time bound. -/
theorem coupon_cover_cost_scaled (n : Nat) (r : Fin n → Bool) :
    ∀ T,
      freshFact n *
          costNumerator (fun C (e : Fin n) => maskDrop C e)
            (fun C => maskSize C = 0) r T ≤
        n ^ T * couponPotential n r := by
  intro T
  exact costNumerator_scaled_potential
    (fun C (e : Fin n) => maskDrop C e)
    (fun C : Fin n → Bool => maskSize C = 0)
    (couponPotential n) (freshFact n)
    (fun C hC => couponPotential_drift C hC)
    r T

def couponCeil (a d : Nat) : Nat :=
  a / d + if a % d = 0 then 0 else 1

theorem couponCeil_budget (a d : Nat) (hd : 0 < d) :
    a ≤ d * couponCeil a d := by
  have he : d * (a / d) + a % d = a := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod a d
  have hr := Nat.mod_lt a hd
  by_cases hz : a % d = 0
  · simp only [couponCeil, if_pos hz, Nat.add_zero]
    omega
  · simp only [couponCeil, if_neg hz, Nat.mul_add, Nat.mul_one]
    omega

def couponCoverCeiling (n m : Nat) : Nat :=
  couponCeil (n * scaledHarmonic (freshFact n) m)
    (freshFact n)

/-- The exact ceiling of n H_m, after cancelling the common scale. -/
theorem coupon_cover_cost_ceiling (n : Nat) (r : Fin n → Bool) :
    ∀ T,
      costNumerator (fun C (e : Fin n) => maskDrop C e)
          (fun C => maskSize C = 0) r T ≤
        n ^ T * couponCoverCeiling n (maskSize r) := by
  intro T
  have hscaled := coupon_cover_cost_scaled n r T
  have hpos : 0 < freshFact n := coupon_factorial_pos n
  have hceil :
      n * scaledHarmonic (freshFact n) (maskSize r) ≤
        freshFact n * couponCoverCeiling n (maskSize r) :=
    couponCeil_budget _ _ hpos
  have hbound :
      freshFact n *
          costNumerator (fun C (e : Fin n) => maskDrop C e)
            (fun C => maskSize C = 0) r T ≤
        freshFact n * (n ^ T * couponCoverCeiling n (maskSize r)) := by
    calc
      freshFact n *
          costNumerator (fun C (e : Fin n) => maskDrop C e)
            (fun C => maskSize C = 0) r T ≤
        n ^ T * couponPotential n r := hscaled
      _ ≤ n ^ T *
          (freshFact n * couponCoverCeiling n (maskSize r)) := by
            exact Nat.mul_le_mul_left _ hceil
      _ = freshFact n * (n ^ T * couponCoverCeiling n (maskSize r)) := by
            ac_rfl
  exact Nat.le_of_mul_le_mul_left hbound hpos

/-- The original all-cover event is the terminal predicate of the
same maskDrop fold used in the cost theorem. -/
theorem coupon_maskCover_run {n : Nat}
    (r : Fin n → Bool) (w : List (Fin n)) :
    maskCover r w =
      if maskSize (w.foldl maskDrop r) = 0 then 1 else 0 := by
  induction w generalizing r with
  | nil => rfl
  | cons e tail ih =>
      change maskCover (maskDrop r e) tail =
        if maskSize (tail.foldl maskDrop (maskDrop r e)) = 0
          then 1 else 0
      exact ih (maskDrop r e)

/-- The protected M=t+3 physical labels, rotated exactly as in
the paper's last-order clearing. First-cover cost is n H_M. -/
theorem protected_coupon_first_cover_cost {n q : Nat}
    (s : Fin n) (hn : (compileAdvice q).t + 3 ≤ n) :
    ∀ T,
      costNumerator (fun C (e : Fin n) => maskDrop C e)
        (fun C => maskSize C = 0)
        (fun e => canonicalMask ((compileAdvice q).t + 3)
          (protectedLabel s e)) T ≤
        n ^ T * couponCoverCeiling n ((compileAdvice q).t + 3) := by
  intro T
  let M := (compileAdvice q).t + 3
  let r : Fin n → Bool := fun e => canonicalMask M (protectedLabel s e)
  have hm : maskSize r = M :=
    relabeled_mask_size
      (rotate (certSite s (n - 2)))
      (unrotate (certSite s (n - 2)))
      (unrotate_rotate (certSite s (n - 2)))
      (rotate_unrotate (certSite s (n - 2)))
      M hn
  have h := coupon_cover_cost_ceiling n r T
  simpa only [r, M, hm] using h

/-- One-step physical scanner provenance through an edge outside the
forward B family, including arbitrary incoming collisions. -/
theorem tolerant_outside {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (z : FreshGhostConfig n q) (e : Fin n)
    (hout : OutsideCoverage (q := q) s e)
    (hstage : TaggedIndexStage s j z) :
    TaggedIndexStage s j (freshGhostStep ring fixed s z e) :=
  tagged_stage_wait ring fixed s j z e hout hstage

/-- The actual selected required B-edge transports the tagged
scanner through its empty successor and increases its hop index. -/
theorem tolerant_progress {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (hj : j.val + 1 < (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (z : FreshGhostConfig n q)
    (hstage : TaggedIndexStage s j z) :
    TaggedIndexStage s ⟨j.val + 1, hj⟩
      (freshGhostStep ring fixed s z (certSite s j.val)) :=
  tagged_stage_advance ring fixed s j hj hn z hstage

/-- A chosen resident scanner's origin tag survives an R0a
collision without assuming the incoming scanner is untagged. -/
theorem tolerant_resident_collision {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (z : FreshGhostConfig n q)
    (e site : Fin n) (r : RawTok (compileAdvice q).t)
    (hs : site ≠ e)
    (hresident : (z.1 site).rawTok = some r) :
    (freshGhostStep ring fixed s z e).2.trail site =
      z.2.trail site :=
  fresh_resident_tag_wait ring fixed s z e site r hs hresident


/-- Physical R1b of the *first* premature hit of a future edge:
both OLD token slots are empty and the OLD right kick is clear.
It changes the kick to true, but creates no scanner. -/
theorem tolerant_first_premature {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hsrc : (C e).rawTok = none)
    (htgt : (C (ring.rightNeighbor e)).rawTok = none)
    (hkick : (C (ring.rightNeighbor e)).rawKick = false) :
    (step ring fixed C e (ring.rightNeighbor e)).rawTok = none ∧
      (step ring fixed C e (ring.rightNeighbor e)).rawKick = true := by
  obtain ⟨ht, hk⟩ := target_raw ring fixed C e hne
  constructor
  · rw [ht]
    simp [rawD1Step, hsrc, htgt, hkick]
  · rw [hk]
    simp [rawD1Step, hsrc, htgt, hkick]

/-- General preservation of the physical index/tag stage whenever the
selected edge is not the designated outgoing edge and does not enter
a strictly future token slot. An incoming R0a collision at the
designated resident is explicitly allowed. -/
theorem tolerant_avoid_source_future {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (z : FreshGhostConfig n q) (e : Fin n)
    (hsource : certSite s j.val ≠ e)
    (hfuture : ∀ k : Nat, j.val < k → k ≤ (compileAdvice q).t →
      certSite s k ≠ ring.rightNeighbor e)
    (hstage : TaggedIndexStage s j z) :
    TaggedIndexStage s j (freshGhostStep ring fixed s z e) := by
  obtain ⟨r, hr, hindex⟩ := hstage.1
  have hproj :
      (freshGhostStep ring fixed s z e).1 =
        step ring fixed z.1 e :=
    freshGhost_projection ring fixed s z e
  refine ⟨⟨r, ?_, hindex⟩, ?_, ?_⟩
  · rw [hproj]
    exact resident_of_no_outgoing ring fixed z.1 e
      (certSite s j.val) r hsource hr
  · intro k hjk hkt
    rw [hproj]
    exact empty_of_no_incoming ring fixed z.1 e
      (certSite s k) (hfuture k hjk hkt)
      (hstage.2.1 k hjk hkt)
  · have ht := fresh_resident_tag_wait ring fixed s z e
      (certSite s j.val) r hsource hr
    rw [ht]
    exact hstage.2.2

/-- An edge already behind the designated scanner preserves the
stage, even if it sends an unrelated scanner into the occupied
resident site. The only required geometry is t+3 ≤ n. -/
theorem tolerant_behind {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (k : Nat) (hk : k < j.val)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (z : FreshGhostConfig n q)
    (hstage : TaggedIndexStage s j z) :
    TaggedIndexStage s j
      (freshGhostStep ring fixed s z (certSite s k)) := by
  have hsource : certSite s j.val ≠ certSite s k := by
    intro heq
    have hjBound : j.val < n := by
      have hh := j.isLt
      omega
    have hkBound : k < n := by omega
    have he := site_offset_injective s j.val k hjBound hkBound heq
    omega
  have hfuture :
      ∀ m : Nat, j.val < m → m ≤ (compileAdvice q).t →
        certSite s m ≠ ring.rightNeighbor (certSite s k) := by
    intro m hm hmt
    rw [ring_neighbor_certSite]
    intro heq
    have hmBound : m < n := by omega
    have hkBound : k + 1 < n := by
      have hj := j.isLt
      omega
    have he := site_offset_injective s m (k + 1)
      hmBound hkBound heq
    omega
  exact tolerant_avoid_source_future ring fixed s j z (certSite s k)
    hsource hfuture hstage

/-- Exact discrete M!-to-one count of all-cover scheduler words
versus the increasing-last-appearance order. No Poissonization. -/
theorem protected_coupon_factorial {n q : Nat}
    (s : Fin n) (T : Nat)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    Prob.scheduleSum n T
        (maskCover (fun e =>
          canonicalMask ((compileAdvice q).t + 3) (protectedLabel s e))) =
      freshFact ((compileAdvice q).t + 3) *
        Prob.scheduleSum n T
          (fun word =>
            lastAccept ((compileAdvice q).t + 3)
              (word.map (protectedLabel s))) :=
  protected_cover_eq_factorial_last s T hn

/-- Successful increasing last appearances physically clear every
protected raw scanner slot and kick, for arbitrary inherited scratch.
The cut starts from the actual reference state (not a reset). -/
theorem protected_coupon_clears {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n) (word : List (Fin n))
    (hn : (compileAdvice q).t + 3 ≤ n)
    (haccept :
      lastAccept ((compileAdvice q).t + 3)
        (word.map (protectedLabel s)) = 1) :
    ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear (runList ring fixed C word)
        (certSite s (n - 1 + j.val)) :=
  recognized_list_clears ring fixed C s word hn haccept

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

/-!
Fuel-independent scanner fractions.
-/

theorem coupon_pairFold_den_pos
    (xs : List (Nat × Nat)) :
    ∀ a : Nat × Nat, 0 < a.2 →
      (∀ b, b ∈ xs → 0 < b.2) →
      0 < (xs.foldl pairAdd a).2 := by
  induction xs with
  | nil =>
      intro a ha _
      exact ha
  | cons b xs ih =>
      intro a ha hs
      apply ih (pairAdd a b)
      · exact Nat.mul_pos ha (hs b (by simp))
      · intro c hc
        exact hs c (List.mem_cons.mpr (Or.inr hc))

theorem coupon_pairFold_num_pos
    (xs : List (Nat × Nat)) :
    ∀ a : Nat × Nat, 0 < a.1 →
      (∀ b, b ∈ xs → 0 < b.2) →
      0 < (xs.foldl pairAdd a).1 := by
  induction xs with
  | nil =>
      intro a ha _
      exact ha
  | cons b xs ih =>
      intro a ha hs
      apply ih (pairAdd a b)
      · have hp : 0 < a.1 * b.2 :=
          Nat.mul_pos ha (hs b (by simp))
        change 0 < a.1 * b.2 + b.1 * a.2
        omega
      · intro c hc
        exact hs c (List.mem_cons.mpr (Or.inr hc))

theorem pFuel_den_pos (fuel t j : Nat) (B : List Nat) :
    0 < (pFuel fuel t j B).2 := by
  induction fuel generalizing t j B with
  | zero =>
      by_cases hj : j < t <;> simp [pFuel, hj]
  | succ fuel ih =>
      by_cases hj : j < t
      · rw [pFuel_first_step fuel t j B hj]
        apply Nat.mul_pos
        · apply coupon_pairFold_den_pos
          · exact ih t (j + 1) (eraseAvailable (j + 1) B)
          · intro b hb
            obtain ⟨k, _, hk⟩ := List.mem_map.mp hb
            rw [← hk]
            exact ih t j (eraseAvailable k B)
        · omega
      · simp [pFuel, hj]

/-- The all-progress branch is positive as soon as fuel covers the
remaining required progress edges. No bound on the width is used. -/
theorem pFuel_num_pos (fuel t j : Nat) (B : List Nat)
    (hf : t - j ≤ fuel) :
    0 < (pFuel fuel t j B).1 := by
  induction fuel generalizing t j B with
  | zero =>
      have hj : ¬ j < t := by omega
      simp [pFuel, hj]
  | succ fuel ih =>
      by_cases hj : j < t
      · rw [pFuel_first_step fuel t j B hj]
        change 0 <
          ((B.map (fun k : Nat =>
            pFuel fuel t j (eraseAvailable k B))).foldl pairAdd
              (pFuel fuel t (j + 1)
                (eraseAvailable (j + 1) B))).1
        apply coupon_pairFold_num_pos
        · exact ih t (j + 1) (eraseAvailable (j + 1) B) (by omega)
        · intro b hb
          obtain ⟨k, _, hk⟩ := List.mem_map.mp hb
          rw [← hk]
          exact pFuel_den_pos fuel t j (eraseAvailable k B)
      · simp [pFuel, hj]

/-- Fuel beyond the decreasing measure changes neither component
of the unnormalised pair. This is equality of pairs, not just equality
after cross multiplication. -/
theorem pFuel_stable (fuel other t j : Nat) (B : List Nat)
    (hf : t - j + B.length ≤ fuel)
    (ho : t - j + B.length ≤ other) :
    pFuel fuel t j B = pFuel other t j B := by
  induction fuel generalizing other t j B with
  | zero =>
      have hj : ¬ j < t := by omega
      cases other <;> simp [pFuel, hj]
  | succ fuel ih =>
      by_cases hj : j < t
      · cases other with
        | zero =>
            omega
        | succ other =>
            have hlen := eraseAvailable_length_le (j + 1) B
            have hprogress :
                pFuel fuel t (j + 1) (eraseAvailable (j + 1) B) =
                  pFuel other t (j + 1) (eraseAvailable (j + 1) B) :=
              ih other t (j + 1) (eraseAvailable (j + 1) B)
                (by omega) (by omega)
            have hmap :
                B.map (fun k : Nat =>
                  pFuel fuel t j (eraseAvailable k B)) =
                B.map (fun k : Nat =>
                  pFuel other t j (eraseAvailable k B)) := by
              apply List.map_congr_left
              intro k hk
              have hshort := eraseAvailable_length_lt_of_mem k B hk
              exact ih other t j (eraseAvailable k B)
                (by omega) (by omega)
            rw [pFuel_first_step fuel t j B hj,
              pFuel_first_step other t j B hj, hprogress, hmap]
      · cases other <;> simp [pFuel, hj]

/-- Canonical sufficient-fuel value for an available-label list. -/
def pAvailable (t j : Nat) (B : List Nat) : Nat × Nat :=
  pFuel (t - j + B.length) t j B

/-- Closed first-step equation: each child uses its own sufficient
fuel. Thus no recurrence edge silently relies on exhausted fuel. -/
theorem pAvailable_first_step (t j : Nat) (B : List Nat)
    (hj : j < t) :
    pAvailable t j B =
      pairDiv
        ((B.map (fun k : Nat =>
          pAvailable t j (eraseAvailable k B))).foldl pairAdd
          (pAvailable t (j + 1) (eraseAvailable (j + 1) B)))
        (t - j) := by
  let fuel := t - j + B.length - 1
  have hfull : fuel + 1 = t - j + B.length := by
    dsimp only [fuel]
    omega
  have hstart :
      pAvailable t j B = pFuel (fuel + 1) t j B := by
    simp only [pAvailable, hfull]
  have hlen := eraseAvailable_length_le (j + 1) B
  have hprogress :
      pFuel fuel t (j + 1) (eraseAvailable (j + 1) B) =
        pAvailable t (j + 1) (eraseAvailable (j + 1) B) := by
    unfold pAvailable
    apply pFuel_stable
    · dsimp only [fuel]
      omega
    · exact Nat.le_refl _
  have hmap :
      B.map (fun k : Nat => pFuel fuel t j (eraseAvailable k B)) =
        B.map (fun k : Nat => pAvailable t j (eraseAvailable k B)) := by
    apply List.map_congr_left
    intro k hk
    have hshort := eraseAvailable_length_lt_of_mem k B hk
    unfold pAvailable
    apply pFuel_stable
    · dsimp only [fuel]
      omega
    · exact Nat.le_refl _
  rw [hstart, pFuel_first_step fuel t j B hj, hprogress, hmap]

theorem pPairAt_available (t j : Nat) (A : List Nat) :
    pPairAt t j A = pAvailable t j (futureUnhit t j A) := rfl

theorem pPair_den_pos (t : Nat) : 0 < (pPair t).2 := by
  dsimp only [pPair, pPairAt]
  exact pFuel_den_pos _ _ _ _

theorem pPair_num_pos (t : Nat) : 0 < (pPair t).1 := by
  dsimp only [pPair, pPairAt]
  apply pFuel_num_pos
  omega

theorem harmonicPair_den_pos (m : Nat) :
    0 < (harmonicPair m).2 := by
  induction m with
  | zero =>
      decide +kernel
  | succ m ih =>
      change 0 < (harmonicPair m).2 * (m + 1)
      exact Nat.mul_pos ih (by omega)

theorem couponGPair_den_pos (t : Nat) :
    0 < (couponGPair t).2 := by
  change 0 < (harmonicPair (t + 3)).2 * (pPair t).1
  exact Nat.mul_pos (harmonicPair_den_pos (t + 3))
    (pPair_num_pos t)


/-- The harmonic Nat pair and the divisible integer scale represent
the same exact number; this avoids rounding the cover phase. -/
theorem harmonic_pair_scaled (D : Nat) :
    ∀ m : Nat, (∀ k : Nat, 0 < k → k ≤ m → k ∣ D) →
      scaledHarmonic D m * (harmonicPair m).2 =
        D * (harmonicPair m).1 := by
  intro m
  induction m with
  | zero =>
      intro _
      simp [scaledHarmonic, harmonicPair]
  | succ m ih =>
      intro hdiv
      have hprev := ih (fun k hk hkm => hdiv k hk (by omega))
      have hlast : D / (m + 1) * (m + 1) = D :=
        Nat.div_mul_cancel (hdiv (m + 1) (by omega) (Nat.le_refl _))
      change
        (scaledHarmonic D m + D / (m + 1)) *
            ((harmonicPair m).2 * (m + 1)) =
          D * ((harmonicPair m).1 * (m + 1) +
            1 * (harmonicPair m).2)
      simp only [Nat.one_mul]
      calc
        (scaledHarmonic D m + D / (m + 1)) *
            ((harmonicPair m).2 * (m + 1)) =
          (scaledHarmonic D m * (harmonicPair m).2) * (m + 1) +
            (harmonicPair m).2 * (D / (m + 1) * (m + 1)) := by
              rw [Nat.add_mul]
              ac_rfl
        _ = (D * (harmonicPair m).1) * (m + 1) +
              (harmonicPair m).2 * D := by rw [hprev, hlast]
        _ = D * ((harmonicPair m).1 * (m + 1) +
              (harmonicPair m).2) := by
              simp only [Nat.mul_add, Nat.mul_one]
              ac_rfl

end L3.CouponClear

namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting

/-- Exact rational coupon cost in the very harmonic-pair scale used
by couponGPair. No individual phase ceiling has been taken. -/
theorem coupon_cover_cost_pair (n : Nat) (r : Fin n → Bool) (T : Nat) :
    (harmonicPair (maskSize r)).2 *
        costNumerator (fun C (e : Fin n) => maskDrop C e)
          (fun C => maskSize C = 0) r T ≤
      n ^ T * (n * (harmonicPair (maskSize r)).1) := by
  have hcost := coupon_cover_cost_scaled n r T
  have hsize : maskSize r ≤ n := coupon_maskSize_le r
  have hh := harmonic_pair_scaled (freshFact n) (maskSize r)
    (fun k hk hkm => coupon_factorial_dvd n k hk (by omega))
  have hscaled :
      freshFact n *
          ((harmonicPair (maskSize r)).2 *
            costNumerator (fun C (e : Fin n) => maskDrop C e)
              (fun C => maskSize C = 0) r T) ≤
        freshFact n *
          (n ^ T * (n * (harmonicPair (maskSize r)).1)) := by
    calc
      freshFact n *
          ((harmonicPair (maskSize r)).2 *
            costNumerator (fun C (e : Fin n) => maskDrop C e)
              (fun C => maskSize C = 0) r T) =
        (harmonicPair (maskSize r)).2 *
          (freshFact n *
            costNumerator (fun C (e : Fin n) => maskDrop C e)
              (fun C => maskSize C = 0) r T) := by ac_rfl
      _ ≤ (harmonicPair (maskSize r)).2 *
          (n ^ T * couponPotential n r) :=
        Nat.mul_le_mul_left _ hcost
      _ = n ^ T *
          (n * (scaledHarmonic (freshFact n) (maskSize r) *
            (harmonicPair (maskSize r)).2)) := by
        unfold couponPotential
        ac_rfl
      _ = n ^ T *
          (n * (freshFact n * (harmonicPair (maskSize r)).1)) := by
        rw [hh]
      _ = freshFact n *
          (n ^ T * (n * (harmonicPair (maskSize r)).1)) := by
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled (coupon_factorial_pos n)

theorem protected_coupon_first_cover_cost_exact {n q : Nat}
    (s : Fin n) (hn : (compileAdvice q).t + 3 ≤ n) (T : Nat) :
    (harmonicPair ((compileAdvice q).t + 3)).2 *
        costNumerator (fun C (e : Fin n) => maskDrop C e)
          (fun C => maskSize C = 0)
          (fun e => canonicalMask ((compileAdvice q).t + 3)
            (protectedLabel s e)) T ≤
      n ^ T * (n * (harmonicPair ((compileAdvice q).t + 3)).1) := by
  let M := (compileAdvice q).t + 3
  let r : Fin n → Bool := fun e => canonicalMask M (protectedLabel s e)
  have hm : maskSize r = M :=
    relabeled_mask_size
      (rotate (certSite s (n - 2)))
      (unrotate (certSite s (n - 2)))
      (unrotate_rotate (certSite s (n - 2)))
      (rotate_unrotate (certSite s (n - 2)))
      M hn
  have h := coupon_cover_cost_pair n r T
  simpa only [hm, r, M] using h

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference
open FreshCoupon
open FreshFixed

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-!
Exact first-cover last-order counting.

The final coupon of a first-cover word is absent from the preceding
word. Removing that one label leaves n-1 allowed scheduler labels.
The counting proof below retains this restriction explicitly.
-/

/-- Indicator that a specified physical label never occurs. -/
def couponAvoid {n : Nat} (a : Fin n) : List (Fin n) → Nat
  | [] => 1
  | e :: word => if e = a then 0 else couponAvoid a word

theorem couponAvoid_range {n : Nat} (a : Fin n)
    (word : List (Fin n)) :
    couponAvoid a word = 0 ∨ couponAvoid a word = 1 := by
  induction word with
  | nil =>
      exact Or.inr rfl
  | cons e word ih =>
      by_cases he : e = a
      · simp [couponAvoid, he]
      · simpa only [couponAvoid, if_neg he] using ih

theorem couponAvoid_one_iff {n : Nat} (a : Fin n)
    (word : List (Fin n)) :
    couponAvoid a word = 1 ↔ a ∉ word := by
  induction word with
  | nil =>
      simp [couponAvoid]
  | cons e word ih =>
      by_cases he : e = a
      · subst e
        simp [couponAvoid]
      · have hae : a ≠ e := Ne.symm he
        simp [couponAvoid, he, ih, hae]

theorem coupon_binary_eq (a b : Nat)
    (ha : a = 0 ∨ a = 1)
    (hb : b = 0 ∨ b = 1)
    (hone : a = 1 ↔ b = 1) :
    a = b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · omega
  · have hh := hone.mpr hb
    omega
  · have hh := hone.mp ha
    omega
  · omega

theorem couponAvoid_reverse {n : Nat} (a : Fin n)
    (word : List (Fin n)) :
    couponAvoid a word.reverse = couponAvoid a word := by
  apply coupon_binary_eq
  · exact couponAvoid_range a word.reverse
  · exact couponAvoid_range a word
  · simp only [couponAvoid_one_iff, List.mem_reverse]

theorem coupon_maskCover_reverse {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n)) :
    maskCover r word.reverse = maskCover r word := by
  apply coupon_binary_eq
  · exact maskCover_range r word.reverse
  · exact maskCover_range r word
  · simp only [maskCover_correct, List.mem_reverse]

/-- Reverse-word form of first cover on the final service.

The head is the last selected edge in chronological order.
It must be a required coupon, absent from the earlier word;
every other required coupon must already have occurred.
-/
def couponFirstCoverHead {n : Nat}
    (r : Fin n → Bool) : List (Fin n) → Nat
  | [] => if maskSize r = 0 then 1 else 0
  | e :: word =>
      if r e = true then
        couponAvoid e word * maskCover (maskDrop r e) word
      else 0

def couponFirstCoverEnd {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n)) : Nat :=
  couponFirstCoverHead r word.reverse

theorem couponFirstCoverEnd_snoc {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n)) (e : Fin n) :
    couponFirstCoverEnd r (word ++ [e]) =
      if r e = true then
        couponAvoid e word * maskCover (maskDrop r e) word
      else 0 := by
  simp only [couponFirstCoverEnd, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, couponFirstCoverHead,
    couponAvoid_reverse, coupon_maskCover_reverse]

theorem couponFirstCoverEnd_snoc_data {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n)) (e : Fin n) :
    couponFirstCoverEnd r (word ++ [e]) = 1 ↔
      r e = true ∧ e ∉ word ∧
        maskCover (maskDrop r e) word = 1 := by
  rw [couponFirstCoverEnd_snoc]
  by_cases hr : r e = true
  · rw [if_pos hr]
    have hprod :
        couponAvoid e word * maskCover (maskDrop r e) word = 1 ↔
          couponAvoid e word = 1 ∧
            maskCover (maskDrop r e) word = 1 := by
      rcases couponAvoid_range e word with ha | ha <;>
        rcases maskCover_range (maskDrop r e) word with hb | hb <;>
        simp [ha, hb]
    rw [hprod, couponAvoid_one_iff]
    constructor
    · intro h
      exact ⟨hr, h.1, h.2⟩
    · intro h
      exact ⟨h.2.1, h.2.2⟩
  · rw [if_neg hr]
    constructor
    · intro h
      omega
    · intro h
      exact False.elim (hr h.1)

/-- Exact connection to the existing maskCover clock.

For a nonempty word, this is first cover on the final service,
rather than cover at a deterministic horizon with arbitrary
earlier completion.
-/
theorem couponFirstCoverEnd_snoc_spec {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n)) (e : Fin n) :
    couponFirstCoverEnd r (word ++ [e]) = 1 ↔
      maskCover r (word ++ [e]) = 1 ∧
        maskCover r word = 0 := by
  rw [couponFirstCoverEnd_snoc_data]
  constructor
  · intro h
    obtain ⟨hre, habsent, hdrop⟩ := h
    have hcovered : maskCover r (word ++ [e]) = 1 := by
      apply (maskCover_correct r (word ++ [e])).mpr
      intro i hi
      by_cases hie : i = e
      · subst i
        simp
      · have hdi : maskDrop r e i = true := by
          simp [maskDrop, hie, hi]
        have hmem :=
          (maskCover_correct (maskDrop r e) word).mp hdrop i hdi
        exact List.mem_append.mpr (Or.inl hmem)
    have hbefore : maskCover r word = 0 := by
      rcases maskCover_range r word with hz | ho
      · exact hz
      · have hmem := (maskCover_correct r word).mp ho e hre
        exact False.elim (habsent hmem)
    exact ⟨hcovered, hbefore⟩
  · intro h
    obtain ⟨hafter, hbefore⟩ := h
    have hmembers := (maskCover_correct r (word ++ [e])).mp hafter
    have hre : r e = true := by
      by_cases hr : r e = true
      · exact hr
      · have hp : maskCover r word = 1 := by
          apply (maskCover_correct r word).mpr
          intro i hi
          rcases List.mem_append.mp (hmembers i hi) with hw | hlast
          · exact hw
          · have hie : i = e := by simpa using hlast
            subst i
            exact False.elim (hr hi)
        rw [hbefore] at hp
        omega
    have habsent : e ∉ word := by
      intro he
      have hp : maskCover r word = 1 := by
        apply (maskCover_correct r word).mpr
        intro i hi
        rcases List.mem_append.mp (hmembers i hi) with hw | hlast
        · exact hw
        · have hie : i = e := by simpa using hlast
          simpa only [hie] using he
      rw [hbefore] at hp
      omega
    have hdrop : maskCover (maskDrop r e) word = 1 := by
      apply (maskCover_correct (maskDrop r e) word).mpr
      intro i hi
      have hine : i ≠ e := by
        intro hie
        subst i
        simp [maskDrop] at hi
      have hir : r i = true := by
        simpa only [maskDrop, if_neg hine] using hi
      rcases List.mem_append.mp (hmembers i hir) with hw | hlast
      · exact hw
      · have hie : i = e := by simpa using hlast
        exact False.elim (hine hie)
    exact ⟨hre, habsent, hdrop⟩

/-- A false mask entry supplies one unused alphabet position. -/
theorem coupon_maskSize_room {n : Nat}
    (r : Fin n → Bool) (a : Fin n)
    (ha : r a = false) :
    maskSize r + 1 ≤ n := by
  have hrow (e : Fin n) :
      (if r e then 1 else 0) +
          (if e = a then 1 else 0) ≤ 1 := by
    by_cases he : e = a
    · subst e
      simp [ha]
    · simp only [if_neg he, Nat.add_zero]
      cases r e <;> decide +kernel
  have hs := ofFn_sum_le
    (fun e : Fin n =>
      (if r e then 1 else 0) + (if e = a then 1 else 0))
    (fun _ : Fin n => 1) hrow
  rw [ofFn_sum_add, FreshFixed.sum_spike, ofFn_sum_const] at hs
  simpa only [maskSize, Nat.mul_one] using hs

/-- Mask splitting after forbidding one label outside the mask. -/
theorem coupon_sum_excluding_mask {n : Nat}
    (r : Fin n → Bool) (a : Fin n)
    (ha : r a = false) (outside inside : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = a then 0 else if r e then inside else outside)).sum =
      (n - 1 - maskSize r) * outside + maskSize r * inside := by
  have hrow (e : Fin n) :
      (if r e then inside else outside) =
        (if e = a then 0 else if r e then inside else outside) +
          (if e = a then outside else 0) := by
    by_cases he : e = a
    · subst e
      simp [ha]
    · simp [he]
  have hs := ofFn_sum_eq _ _ hrow
  rw [coupon_mask_split_sum, ofFn_sum_add,
    FreshFixed.sum_spike] at hs
  have hroom := coupon_maskSize_room r a ha
  have hsplit :
      n - maskSize r = (n - 1 - maskSize r) + 1 := by
    omega
  rw [hsplit, Nat.add_mul, Nat.one_mul] at hs
  omega

/-- Exact coverage count when one outside label is forbidden. -/
theorem couponAvoid_cover_count {n : Nat}
    (len : Nat) (a : Fin n) :
    ∀ r : Fin n → Bool, r a = false →
      Prob.scheduleSum n len
        (fun word => couponAvoid a word * maskCover r word) =
      covered (n - 1) len (maskSize r) := by
  induction len with
  | zero =>
      intro r hr
      simp [FreshFixed.sum_zero, couponAvoid, maskCover, covered]
  | succ len ih =>
      intro r hr
      have hrow (e : Fin n) :
          Prob.scheduleSum n len
            (fun word =>
              couponAvoid a (e :: word) * maskCover r (e :: word)) =
          if e = a then 0
          else if r e then
            covered (n - 1) len (maskSize r - 1)
          else covered (n - 1) len (maskSize r) := by
        by_cases he : e = a
        · simp [couponAvoid, he, FreshFixed.sum_const]
        · have hadrop : maskDrop r e a = false := by
            simp [maskDrop, Ne.symm he, hr]
          simp only [couponAvoid, if_neg he, maskCover]
          rw [ih (maskDrop r e) hadrop]
          cases hri : r e with
          | false =>
              have hd := coupon_maskDrop_false r e hri
              simp [hri, hd]
          | true =>
              have hs := coupon_maskDrop_true r e hri
              have hd :
                  maskSize (maskDrop r e) = maskSize r - 1 := by
                omega
              simp [hri, hd]
      rw [FreshFixed.sum_succ, ofFn_sum_eq _ _ hrow,
        coupon_sum_excluding_mask r a hr]
      cases hm : maskSize r with
      | zero =>
          simp [hm, covered_zero_width, Nat.pow_succ, Nat.mul_comm]
      | succ m =>
          simp only [hm, Nat.add_sub_cancel, covered]

/-- Reverse first-appearance order forces every required label
to occur. This is a pointwise fact, independent of counting. -/
theorem coupon_ordered_mem {n : Nat} :
    ∀ (word : List (Fin n)) (k : Nat),
      orderedAccept k word = 1 →
      ∀ i : Fin n, i.val < k → i ∈ word := by
  intro word
  induction word with
  | nil =>
      intro k h i hi
      have hk : k = 0 := by
        by_cases hk : k = 0
        · exact hk
        · simp [orderedAccept, hk] at h
      omega
  | cons e word ih =>
      intro k h i hi
      by_cases hp : e.val + 1 = k
      · have htail : orderedAccept (k - 1) word = 1 := by
          simpa only [orderedAccept, if_pos hp] using h
        by_cases hie : i = e
        · subst i
          simp
        · have hne : i.val ≠ e.val := by
            intro hv
            exact hie (Fin.ext hv)
          have hsmall : i.val < k - 1 := by omega
          exact List.mem_cons.mpr
            (Or.inr (ih (k - 1) htail i hsmall))
      · by_cases hout : k ≤ e.val
        · have htail : orderedAccept k word = 1 := by
            simpa only [orderedAccept, if_neg hp, if_pos hout] using h
          exact List.mem_cons.mpr (Or.inr (ih k htail i hi))
        · simp [orderedAccept, hp, hout] at h

theorem coupon_ordered_cover {n : Nat}
    (k : Nat) (word : List (Fin n))
    (h : orderedAccept k word = 1) :
    maskCover (canonicalMask (n := n) k) word = 1 := by
  apply (maskCover_correct (canonicalMask (n := n) k) word).mpr
  intro i hi
  have hsmall : i.val < k := by
    exact of_decide_eq_true hi
  exact coupon_ordered_mem word k h i hsmall

theorem coupon_ordered_cover_mul {n : Nat}
    (k : Nat) (word : List (Fin n)) :
    maskCover (canonicalMask (n := n) k) word *
        orderedAccept k word =
      orderedAccept k word := by
  rcases orderedAccept_range k word with hz | ho
  · rw [hz, Nat.mul_zero]
  · have hc := coupon_ordered_cover k word ho
    rw [hc, Nat.one_mul]

def couponChoice (k outside progress value : Nat) : Nat :=
  if value + 1 = k then progress
  else if k ≤ value then outside else 0

/-- Sum of one progress branch, outside branches, and losing branches. -/
theorem coupon_choice_sum (n k outside progress : Nat)
    (hk : k ≤ n) :
    (List.ofFn (fun e : Fin n =>
      couponChoice k outside progress e.val)).sum =
      (n - k) * outside + if k = 0 then 0 else progress := by
  cases k with
  | zero =>
      simp [couponChoice, ofFn_sum_const]
  | succ k =>
      let top : Fin n := ⟨k, by omega⟩
      have hrow (e : Fin n) :
          couponChoice (k + 1) outside progress e.val =
            (if canonicalMask (k + 1) e then 0 else outside) +
              (if e = top then progress else 0) := by
        by_cases he : e = top
        · subst e
          simp [couponChoice, canonicalMask, top]
        · have hne : e.val ≠ k := by
            intro hv
            exact he (Fin.ext hv)
          have hp : ¬ e.val + 1 = k + 1 := by omega
          by_cases hbelow : e.val < k + 1
          · have hout : ¬ k + 1 ≤ e.val := by omega
            simp [couponChoice, canonicalMask, hp, hne, hbelow, hout, he] <;> omega
          · have hout : k + 1 ≤ e.val := by omega
            simp [couponChoice, canonicalMask, hp, hne, hbelow, hout, he] <;> omega
      rw [ofFn_sum_eq _ _ hrow, ofFn_sum_add,
        coupon_mask_split_sum,
        canonicalMask_size n (k + 1) hk,
        FreshFixed.sum_spike]
      simp

/-- The forbidden label is one of the harmless outside branches. -/
theorem coupon_sum_excluding_choice {n : Nat}
    (a : Fin n) (k outside progress : Nat)
    (hk : k ≤ a.val) :
    (List.ofFn (fun e : Fin n =>
      if e = a then 0
      else couponChoice k outside progress e.val)).sum =
      (n - 1 - k) * outside +
        if k = 0 then 0 else progress := by
  have hatop : couponChoice k outside progress a.val = outside := by
    have hp : ¬ a.val + 1 = k := by omega
    simp [couponChoice, hp, hk]
  have hrow (e : Fin n) :
      couponChoice k outside progress e.val =
        (if e = a then 0
         else couponChoice k outside progress e.val) +
          (if e = a then outside else 0) := by
    by_cases he : e = a
    · subst e
      simp [hatop]
    · simp [he]
  have hs := ofFn_sum_eq _ _ hrow
  have hkn : k ≤ n := by
    have ha := a.isLt
    omega
  rw [coupon_choice_sum n k outside progress hkn,
    ofFn_sum_add, FreshFixed.sum_spike] at hs
  have hsplit : n - k = (n - 1 - k) + 1 := by
    have ha := a.isLt
    omega
  rw [hsplit, Nat.add_mul, Nat.one_mul] at hs
  omega

/-- Exact ordered-appearance count with an outside label forbidden. -/
theorem couponAvoid_ordered_count {n : Nat}
    (len : Nat) (a : Fin n) :
    ∀ k : Nat, k ≤ a.val →
      Prob.scheduleSum n len
        (fun word => couponAvoid a word * orderedAccept k word) =
      ordered (n - 1) len k := by
  induction len with
  | zero =>
      intro k hk
      simp [FreshFixed.sum_zero, couponAvoid, orderedAccept, ordered]
  | succ len ih =>
      intro k hk
      have hrow (e : Fin n) :
          Prob.scheduleSum n len
            (fun word =>
              couponAvoid a (e :: word) * orderedAccept k (e :: word)) =
          if e = a then 0
          else couponChoice k
            (ordered (n - 1) len k)
            (ordered (n - 1) len (k - 1)) e.val := by
        by_cases he : e = a
        · simp [couponAvoid, he, FreshFixed.sum_const]
        · by_cases hp : e.val + 1 = k
          · have hh := ih (k - 1) (by omega)
            simpa only [couponAvoid, if_neg he, orderedAccept,
              if_pos hp, couponChoice] using hh
          · by_cases hout : k ≤ e.val
            · have hh := ih k hk
              simpa only [couponAvoid, if_neg he, orderedAccept,
                if_neg hp, if_pos hout, couponChoice] using hh
            · simp [couponAvoid, he, orderedAccept, hp, hout,
                couponChoice, FreshFixed.sum_const]
      rw [FreshFixed.sum_succ, ofFn_sum_eq _ _ hrow,
        coupon_sum_excluding_choice a k
          (ordered (n - 1) len k)
          (ordered (n - 1) len (k - 1)) hk]
      cases k with
      | zero =>
          simp [ordered_zero_width, Nat.pow_succ, Nat.mul_comm]
      | succ k =>
          simp only [Nat.add_sub_cancel, ordered,
            Nat.succ_ne_zero, if_false]

/-- Ordered first cover in reverse-word form. Its first letter must
be the largest coupon, and that letter must never recur. -/
def couponOrderedFirstCoverHead {n : Nat} :
    Nat → List (Fin n) → Nat
  | k, [] => if k = 0 then 1 else 0
  | k, e :: word =>
      if e.val + 1 = k then
        couponAvoid e word * orderedAccept (k - 1) word
      else 0

def couponOrderedFirstCoverEnd {n : Nat}
    (k : Nat) (word : List (Fin n)) : Nat :=
  couponOrderedFirstCoverHead k word.reverse

/-- The ordered first-cover recognizer is exactly the product of
first-cover and increasing-last-order indicators. -/
theorem coupon_firstCoverHead_order {n : Nat}
    (k : Nat) (word : List (Fin n)) :
    couponFirstCoverHead (canonicalMask (n := n) k) word *
        orderedAccept k word =
      couponOrderedFirstCoverHead k word := by
  cases word with
  | nil =>
      cases k <;>
        simp [couponFirstCoverHead, couponOrderedFirstCoverHead,
          orderedAccept, canonicalMask, maskSize, ofFn_sum_const]
  | cons e word =>
      by_cases hp : e.val + 1 = k
      · have hbelow : e.val < k := by omega
        have hbool : canonicalMask k e = true := by
          simp [canonicalMask, hbelow]
        have hdrop :
            maskDrop (canonicalMask (n := n) k) e =
              canonicalMask (k - 1) := by
          funext i
          by_cases hie : i = e
          · subst i
            have hnot : ¬ e.val < k - 1 := by omega
            simp [maskDrop, canonicalMask, hnot]
          · have hne : i.val ≠ e.val := by
              intro hv
              exact hie (Fin.ext hv)
            have hiff : i.val < k ↔ i.val < k - 1 := by omega
            simp only [maskDrop, if_neg hie, canonicalMask, hiff]
        have hmul := coupon_ordered_cover_mul (k - 1) word
        calc
          couponFirstCoverHead (canonicalMask (n := n) k) (e :: word) *
              orderedAccept k (e :: word) =
            couponAvoid e word *
              (maskCover (canonicalMask (n := n) (k - 1)) word *
                orderedAccept (k - 1) word) := by
                  simp only [couponFirstCoverHead, hbool, if_true,
                    orderedAccept, if_pos hp, hdrop, Nat.mul_assoc]
          _ = couponAvoid e word * orderedAccept (k - 1) word := by
                rw [hmul]
          _ = couponOrderedFirstCoverHead k (e :: word) := by
                simp [couponOrderedFirstCoverHead, hp]
      · by_cases hout : k ≤ e.val
        · have hbool : canonicalMask k e = false := by
            simp [canonicalMask, Nat.not_lt.mpr hout]
          simp [couponFirstCoverHead, hbool,
            couponOrderedFirstCoverHead, hp]
        · simp [couponFirstCoverHead, orderedAccept,
            couponOrderedFirstCoverHead, hp, hout]

theorem coupon_firstCoverEnd_order {n : Nat}
    (k : Nat) (word : List (Fin n)) :
    couponFirstCoverEnd (canonicalMask (n := n) k) word *
        lastAccept k word =
      couponOrderedFirstCoverEnd k word :=
  coupon_firstCoverHead_order k word.reverse

/-- Exact number of words whose first cover is the final service. -/
theorem coupon_first_cover_count {n : Nat}
    (len : Nat) (r : Fin n → Bool) :
    Prob.scheduleSum n (len + 1) (couponFirstCoverEnd r) =
      maskSize r * covered (n - 1) len (maskSize r - 1) := by
  change Prob.scheduleSum n (len + 1)
    (fun word => couponFirstCoverHead r word.reverse) = _
  rw [scheduleSum_reverse, FreshFixed.sum_succ]
  have hrow (e : Fin n) :
      Prob.scheduleSum n len
        (fun word => couponFirstCoverHead r (e :: word)) =
      if r e then
        covered (n - 1) len (maskSize r - 1)
      else 0 := by
    cases hr : r e with
    | false =>
        simp [couponFirstCoverHead, hr, FreshFixed.sum_const]
    | true =>
        have hfalse : maskDrop r e e = false := by
          simp [maskDrop]
        have hh := couponAvoid_cover_count len e (maskDrop r e) hfalse
        have hs := coupon_maskDrop_true r e hr
        have hsize :
            maskSize (maskDrop r e) = maskSize r - 1 := by omega
        simpa only [couponFirstCoverHead, hr, if_pos rfl,
          hsize, if_true] using hh
  rw [ofFn_sum_eq _ _ hrow, coupon_mask_split_sum]
  simp

/-- Exact number of increasing-last-order first-cover words. -/
theorem coupon_ordered_first_cover_count {n : Nat}
    (len k : Nat) (hk : k + 1 ≤ n) :
    Prob.scheduleSum n (len + 1)
      (couponOrderedFirstCoverEnd (n := n) (k + 1)) =
      ordered (n - 1) len k := by
  change Prob.scheduleSum n (len + 1)
    (fun word => couponOrderedFirstCoverHead (k + 1) word.reverse) = _
  rw [scheduleSum_reverse, FreshFixed.sum_succ]
  let top : Fin n := ⟨k, by omega⟩
  have hrow (e : Fin n) :
      Prob.scheduleSum n len
        (fun word => couponOrderedFirstCoverHead (k + 1) (e :: word)) =
      if e = top then ordered (n - 1) len k else 0 := by
    by_cases he : e = top
    · subst e
      have hh := couponAvoid_ordered_count len top k
        (by exact Nat.le_refl k)
      simpa [couponOrderedFirstCoverHead, top] using hh
    · have hp : ¬ e.val + 1 = k + 1 := by
        intro hv
        apply he
        apply Fin.ext
        change e.val = k
        omega
      have hval : e.val ≠ k := by
        intro hv
        exact he (Fin.ext hv)
      simp [couponOrderedFirstCoverHead, hp, hval, he,
        FreshFixed.sum_const] <;> omega
  rw [ofFn_sum_eq _ _ hrow, FreshFixed.sum_spike]

/-- First-cover factorial symmetry at each positive exact length. -/
theorem coupon_first_cover_factorial_succ {n : Nat}
    (len k : Nat) (hk : k + 1 ≤ n) :
    Prob.scheduleSum n (len + 1)
        (couponFirstCoverEnd (canonicalMask (n := n) (k + 1))) =
      freshFact (k + 1) *
        Prob.scheduleSum n (len + 1)
          (fun word =>
            couponFirstCoverEnd (canonicalMask (n := n) (k + 1)) word *
              lastAccept (k + 1) word) := by
  have hfun :
      (fun word : List (Fin n) =>
        couponFirstCoverEnd (canonicalMask (n := n) (k + 1)) word *
          lastAccept (k + 1) word) =
        couponOrderedFirstCoverEnd (k + 1) := by
    funext word
    exact coupon_firstCoverEnd_order (k + 1) word
  rw [hfun, coupon_first_cover_count,
    canonicalMask_size n (k + 1) hk,
    coupon_ordered_first_cover_count len k hk,
    Nat.add_sub_cancel, covered_eq_factorial_ordered]
  change
    (k + 1) * (freshFact k * ordered (n - 1) len k) =
      ((k + 1) * freshFact k) * ordered (n - 1) len k
  ac_rfl

/-- The factorial identity holds conditional on every possible
first-cover length, including the zero-length boundary. -/
theorem coupon_first_cover_factorial {n : Nat}
    (T M : Nat) (hpos : 0 < M) (hwidth : M ≤ n) :
    Prob.scheduleSum n T
        (couponFirstCoverEnd (canonicalMask (n := n) M)) =
      freshFact M *
        Prob.scheduleSum n T
          (fun word =>
            couponFirstCoverEnd (canonicalMask (n := n) M) word *
              lastAccept M word) := by
  cases T with
  | zero =>
      have hm : maskSize (canonicalMask (n := n) M) ≠ 0 := by
        rw [canonicalMask_size n M hwidth]
        omega
      simp [FreshFixed.sum_zero, couponFirstCoverEnd,
        couponFirstCoverHead, hm]
  | succ T =>
      cases M with
      | zero => omega
      | succ k =>
          exact coupon_first_cover_factorial_succ T k hwidth

/-- The stopped factorial law for the paper's rotated protected
physical labels. No deterministic cutoff is substituted for
the actual first-cover event. -/
theorem protected_coupon_first_cover_factorial {n q : Nat}
    (s : Fin n) (T : Nat)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    Prob.scheduleSum n T
        (fun word =>
          couponFirstCoverEnd
            (canonicalMask ((compileAdvice q).t + 3))
            (word.map (protectedLabel s))) =
      freshFact ((compileAdvice q).t + 3) *
        Prob.scheduleSum n T
          (fun word =>
            couponFirstCoverEnd
                (canonicalMask ((compileAdvice q).t + 3))
                (word.map (protectedLabel s)) *
              lastAccept ((compileAdvice q).t + 3)
                (word.map (protectedLabel s))) := by
  let base := certSite s (n - 2)
  let M := (compileAdvice q).t + 3
  have hleft := scheduleSum_relabel
    (unrotate base) (rotate base)
    (rotate_unrotate base) (unrotate_rotate base)
    T (couponFirstCoverEnd (canonicalMask (n := n) M))
  have hright := scheduleSum_relabel
    (unrotate base) (rotate base)
    (rotate_unrotate base) (unrotate_rotate base)
    T (fun word =>
      couponFirstCoverEnd (canonicalMask (n := n) M) word *
        lastAccept M word)
  calc
    Prob.scheduleSum n T
        (fun word =>
          couponFirstCoverEnd
            (canonicalMask ((compileAdvice q).t + 3))
            (word.map (protectedLabel s))) =
      Prob.scheduleSum n T
        (couponFirstCoverEnd (canonicalMask (n := n) M)) := by
          change Prob.scheduleSum n T
              (fun word =>
                couponFirstCoverEnd (canonicalMask (n := n) M)
                  (word.map (unrotate base))) =
              Prob.scheduleSum n T
                (couponFirstCoverEnd (canonicalMask (n := n) M))
          exact hleft
    _ = freshFact M *
        Prob.scheduleSum n T
          (fun word =>
            couponFirstCoverEnd (canonicalMask (n := n) M) word *
              lastAccept M word) :=
      coupon_first_cover_factorial T M (by dsimp only [M]; omega) hn
    _ = freshFact ((compileAdvice q).t + 3) *
        Prob.scheduleSum n T
          (fun word =>
            couponFirstCoverEnd
                (canonicalMask ((compileAdvice q).t + 3))
                (word.map (protectedLabel s)) *
              lastAccept ((compileAdvice q).t + 3)
                (word.map (protectedLabel s))) := by
      apply congrArg (fun v : Nat => freshFact M * v)
      change Prob.scheduleSum n T
          (fun word =>
            couponFirstCoverEnd (canonicalMask (n := n) M) word *
              lastAccept M word) =
        Prob.scheduleSum n T
          (fun word =>
            couponFirstCoverEnd (canonicalMask (n := n) M)
                (word.map (unrotate base)) *
              lastAccept M (word.map (unrotate base)))
      exact hright.symm


/-- Pointwise relabeling identifies the cover count with the actual
physical mask clock, not only with an equinumerous abstract event. -/
theorem coupon_maskCover_map {n : Nat}
    (p q : Fin n → Fin n)
    (hpq : ∀ e, q (p e) = e)
    (hqp : ∀ e, p (q e) = e)
    (r : Fin n → Bool) (word : List (Fin n)) :
    maskCover r (word.map p) =
      maskCover (fun e => r (p e)) word := by
  apply coupon_binary_eq
  · exact maskCover_range r (word.map p)
  · exact maskCover_range (fun e => r (p e)) word
  · constructor
    · intro h
      apply (maskCover_correct (fun e => r (p e)) word).mpr
      intro e he
      have hm := (maskCover_correct r (word.map p)).mp h (p e) he
      obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
      have hsame : a = e := by
        simpa only [hpq] using congrArg q heq
      simpa only [hsame] using ha
    · intro h
      apply (maskCover_correct r (word.map p)).mpr
      intro i hi
      have hr : r (p (q i)) = true := by
        rw [hqp i]
        exact hi
      have hm := (maskCover_correct (fun e => r (p e)) word).mp h (q i) hr
      exact List.mem_map.mpr ⟨q i, hm, hqp i⟩

theorem protected_coupon_maskCover_map {n q : Nat}
    (s : Fin n) (word : List (Fin n)) :
    maskCover (canonicalMask ((compileAdvice q).t + 3))
        (word.map (protectedLabel s)) =
      maskCover (fun e => canonicalMask ((compileAdvice q).t + 3)
        (protectedLabel s e)) word := by
  exact coupon_maskCover_map
    (unrotate (certSite s (n - 2)))
    (rotate (certSite s (n - 2)))
    (rotate_unrotate (certSite s (n - 2)))
    (unrotate_rotate (certSite s (n - 2)))
    (canonicalMask ((compileAdvice q).t + 3)) word

/-- The protected factorial count uses exactly the first-cover
stopping event of the physical maskDrop process. -/
theorem protected_coupon_first_cover_spec {n q : Nat}
    (s : Fin n) (word : List (Fin n)) (e : Fin n) :
    couponFirstCoverEnd (canonicalMask ((compileAdvice q).t + 3))
        ((word ++ [e]).map (protectedLabel s)) = 1 ↔
      maskCover (fun a => canonicalMask ((compileAdvice q).t + 3)
          (protectedLabel s a)) (word ++ [e]) = 1 ∧
        maskCover (fun a => canonicalMask ((compileAdvice q).t + 3)
          (protectedLabel s a)) word = 0 := by
  have h := couponFirstCoverEnd_snoc_spec
    (canonicalMask ((compileAdvice q).t + 3))
    (word.map (protectedLabel s)) (protectedLabel s e)
  have hmap : (word ++ [e]).map (protectedLabel s) =
      word.map (protectedLabel s) ++ [protectedLabel s e] := by
    simp only [List.map_append, List.map_cons, List.map_nil]
  rw [← hmap] at h
  rw [protected_coupon_maskCover_map s (word ++ [e]),
    protected_coupon_maskCover_map s word] at h
  exact h

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference
open FreshCoupon
open FreshFixed

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-!
Stopped two-hit launch.

The first recognizer counts words that have completed k monitored
hits. The second additionally requires each of those first k hits
to be the designated launch edge. Both absorb after completion.
-/

def launchHitAccept {n : Nat} (outside : Fin n → Bool) :
    Nat → List (Fin n) → Nat
  | 0, _ => 1
  | _ + 1, [] => 0
  | k + 1, e :: w =>
      if outside e then launchHitAccept outside (k + 1) w
      else launchHitAccept outside k w

def launchMarkAccept {n : Nat}
    (outside : Fin n → Bool) (a : Fin n) :
    Nat → List (Fin n) → Nat
  | 0, _ => 1
  | _ + 1, [] => 0
  | k + 1, e :: w =>
      if e = a then launchMarkAccept outside a k w
      else if outside e then launchMarkAccept outside a (k + 1) w
      else 0

theorem launch_hits_count_step {n : Nat}
    (outside : Fin n → Bool) (k T : Nat) :
    Prob.scheduleSum n (T + 1) (launchHitAccept outside (k + 1)) =
      (n - maskSize outside) *
          Prob.scheduleSum n T (launchHitAccept outside k) +
        maskSize outside *
          Prob.scheduleSum n T (launchHitAccept outside (k + 1)) := by
  have hrow (e : Fin n) :
      Prob.scheduleSum n T
          (fun w => launchHitAccept outside (k + 1) (e :: w)) =
        if outside e then
          Prob.scheduleSum n T (launchHitAccept outside (k + 1))
        else Prob.scheduleSum n T (launchHitAccept outside k) := by
    cases he : outside e <;> simp [launchHitAccept, he]
  rw [sum_succ, ofFn_sum_eq _ _ hrow, coupon_mask_split_sum]

theorem launch_marks_count_step {n : Nat}
    (outside : Fin n → Bool) (a : Fin n) (k T : Nat)
    (ha : outside a = false) :
    Prob.scheduleSum n (T + 1)
        (launchMarkAccept outside a (k + 1)) =
      Prob.scheduleSum n T (launchMarkAccept outside a k) +
        maskSize outside *
          Prob.scheduleSum n T (launchMarkAccept outside a (k + 1)) := by
  have hrow (e : Fin n) :
      Prob.scheduleSum n T
          (fun w => launchMarkAccept outside a (k + 1) (e :: w)) =
        (if e = a then
          Prob.scheduleSum n T (launchMarkAccept outside a k) else 0) +
        (if outside e then
          Prob.scheduleSum n T (launchMarkAccept outside a (k + 1))
         else 0) := by
    by_cases he : e = a
    · subst e
      simp [launchMarkAccept, ha]
    · cases ho : outside e <;>
        simp [launchMarkAccept, he, ho, sum_const]
  rw [sum_succ, ofFn_sum_eq _ _ hrow, ofFn_sum_add,
    FreshFixed.sum_spike, FreshFixed.sum_mask]

/-- Exact finite-horizon conditional count for the first k monitored
letters. The statement includes every outside delay and every suffix
after completion. -/
theorem launch_mark_count {n : Nat}
    (outside : Fin n → Bool) (a : Fin n)
    (ha : outside a = false) :
    ∀ T k,
      (n - maskSize outside) ^ k *
          Prob.scheduleSum n T (launchMarkAccept outside a k) =
        Prob.scheduleSum n T (launchHitAccept outside k) := by
  intro T
  induction T with
  | zero =>
      intro k
      cases k <;>
        simp [sum_zero, launchMarkAccept, launchHitAccept]
  | succ T ih =>
      intro k
      cases k with
      | zero =>
          have hsame : launchMarkAccept outside a 0 =
              launchHitAccept outside 0 := by
            funext w
            cases w <;> simp [launchMarkAccept, launchHitAccept]
          simpa only [Nat.pow_zero, Nat.one_mul, hsame]
      | succ k =>
          rw [launch_marks_count_step outside a k T ha,
            launch_hits_count_step outside k T]
          calc
            (n - maskSize outside) ^ (k + 1) *
                (Prob.scheduleSum n T (launchMarkAccept outside a k) +
                  maskSize outside *
                    Prob.scheduleSum n T
                      (launchMarkAccept outside a (k + 1))) =
              (n - maskSize outside) *
                  ((n - maskSize outside) ^ k *
                    Prob.scheduleSum n T
                      (launchMarkAccept outside a k)) +
                maskSize outside *
                  ((n - maskSize outside) ^ (k + 1) *
                    Prob.scheduleSum n T
                      (launchMarkAccept outside a (k + 1))) := by
                simp only [Nat.mul_add, Nat.pow_succ]
                ac_rfl
            _ = _ := by
              rw [ih k, ih (k + 1)]

/-- Exactly one of the L launch letters is the desired edge.
Conditionally on completing the first two launch-set hits, the
two prescribed letters have probability exactly 1/L^2. -/
theorem two_hit_launch_count {n q : Nat}
    (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n) (T : Nat) :
    ((compileAdvice q).t + 2) ^ 2 *
        Prob.scheduleSum n T
          (launchMarkAccept (outsideLaunch (q := q) s)
            (certSite s (n - 1)) 2) =
      Prob.scheduleSum n T
        (launchHitAccept (outsideLaunch (q := q) s) 2) := by
  have hsize :
      n - maskSize (outsideLaunch (q := q) s) =
        (compileAdvice q).t + 2 := by
    rw [outsideLaunch_size s hn]
    omega
  have h := launch_mark_count
    (outsideLaunch (q := q) s) (certSite s (n - 1))
    (outsideLaunch_mark_false s hn) T 2
  rw [hsize] at h
  exact h

/-- Number of monitored hits still required. This counter does not
alter the physical edge selected or the physical transition. -/
def launchRemainingStep {n : Nat}
    (outside : Fin n → Bool) (k : Nat) (e : Fin n) : Nat :=
  if outside e then k else k - 1

/-- The completed-hit recognizer is exactly the terminal indicator
of the counter used in the launch stopping-cost theorem. -/
theorem launch_hits_run {n : Nat}
    (outside : Fin n → Bool) (k : Nat) (word : List (Fin n)) :
    launchHitAccept outside k word =
      if word.foldl (launchRemainingStep outside) k = 0 then 1 else 0 := by
  induction word generalizing k with
  | nil =>
      cases k <;> rfl
  | cons e word ih =>
      cases k with
      | zero =>
          have hs : launchRemainingStep outside 0 e = 0 := by
            unfold launchRemainingStep
            cases outside e <;> rfl
          change 1 =
            if word.foldl (launchRemainingStep outside)
              (launchRemainingStep outside 0 e) = 0 then 1 else 0
          rw [hs]
          simpa only [launchHitAccept] using ih 0
      | succ k =>
          change
            (if outside e then launchHitAccept outside (k + 1) word
             else launchHitAccept outside k word) =
            if word.foldl (launchRemainingStep outside)
              (launchRemainingStep outside (k + 1) e) = 0 then 1 else 0
          cases he : outside e with
          | false =>
              have hs : launchRemainingStep outside (k + 1) e = k := by
                simp [launchRemainingStep, he]
              rw [hs]
              exact ih k
          | true =>
              have hs :
                  launchRemainingStep outside (k + 1) e = k + 1 := by
                simp [launchRemainingStep, he]
              rw [hs]
              exact ih (k + 1)

theorem launch_hits_terminal_iff {n : Nat}
    (outside : Fin n → Bool) (k : Nat) (word : List (Fin n)) :
    launchHitAccept outside k word = 1 ↔
      word.foldl (launchRemainingStep outside) k = 0 := by
  rw [launch_hits_run]
  by_cases h : word.foldl (launchRemainingStep outside) k = 0 <;>
    simp [h]

/-- Exact one-step potential identity for the monitored-hit clock. -/
theorem launch_clock_drift {n : Nat}
    (outside : Fin n → Bool) (k : Nat) (hk : ¬ k = 0) :
    (n - maskSize outside) * n +
        (List.ofFn (fun e : Fin n =>
          n * launchRemainingStep outside k e)).sum =
      n * (n * k) := by
  have hpositive : k - 1 + 1 = k := by omega
  have hsplit : n - maskSize outside + maskSize outside = n :=
    Nat.sub_add_cancel (coupon_maskSize_le outside)
  have hrow (e : Fin n) :
      n * launchRemainingStep outside k e =
        if outside e then n * k else n * (k - 1) := by
    cases he : outside e <;>
      simp [launchRemainingStep, he]
  have hpay :
      (n - maskSize outside) * n +
          (n - maskSize outside) * (n * (k - 1)) =
        (n - maskSize outside) * (n * k) := by
    calc
      (n - maskSize outside) * n +
          (n - maskSize outside) * (n * (k - 1)) =
        (n - maskSize outside) * (n * (k - 1 + 1)) := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
          ac_rfl
      _ = (n - maskSize outside) * (n * k) := by
        rw [hpositive]
  rw [ofFn_sum_eq _ _ hrow, coupon_mask_split_sum]
  calc
    (n - maskSize outside) * n +
        ((n - maskSize outside) * (n * (k - 1)) +
          maskSize outside * (n * k)) =
      ((n - maskSize outside) * n +
        (n - maskSize outside) * (n * (k - 1))) +
          maskSize outside * (n * k) := by ac_rfl
    _ = (n - maskSize outside) * (n * k) +
        maskSize outside * (n * k) := by rw [hpay]
    _ = n * (n * k) := by rw [← Nat.add_mul, hsplit]

/-- Unrounded finite-horizon stopping cost for k monitored hits. -/
theorem launch_clock_cost {n : Nat}
    (outside : Fin n → Bool) (k T : Nat) :
    (n - maskSize outside) *
        costNumerator (launchRemainingStep outside)
          (fun j => j = 0) k T ≤
      n ^ T * (n * k) := by
  exact costNumerator_scaled_potential
    (launchRemainingStep outside) (fun j => j = 0)
    (fun j => n * j) (n - maskSize outside)
    (fun j hj => Nat.le_of_eq (launch_clock_drift outside j hj))
    k T

/-- The two-hit launch clock carries the actual reference/ghost state.
Its invoked mean-cost bound is 2n/L, expressed without rounding. -/
theorem two_hit_launch_cost {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (z : FreshGhostConfig n q) (T : Nat) :
    ((compileAdvice q).t + 2) *
        costNumerator
          (fun (x : Nat × FreshGhostConfig n q) (e : Fin n) =>
            (launchRemainingStep (outsideLaunch (q := q) s) x.1 e,
              freshGhostStep ring fixed s x.2 e))
          (fun x => x.1 = 0) (2, z) T ≤
      n ^ T * (2 * n) := by
  have hprojection := Prob.costNumerator_ghost_eq
    (launchRemainingStep (outsideLaunch (q := q) s))
    (fun (x : Nat × FreshGhostConfig n q) (e : Fin n) =>
      (launchRemainingStep (outsideLaunch (q := q) s) x.1 e,
        freshGhostStep ring fixed s x.2 e))
    (fun _ _ => rfl) (fun k => k = 0) (2, z) T
  rw [hprojection]
  have hsize :
      n - maskSize (outsideLaunch (q := q) s) =
        (compileAdvice q).t + 2 := by
    rw [outsideLaunch_size s hn]
    omega
  have hcost := launch_clock_cost (outsideLaunch (q := q) s) 2 T
  rw [hsize] at hcost
  calc
    ((compileAdvice q).t + 2) *
        costNumerator
          (launchRemainingStep (outsideLaunch (q := q) s))
          (fun k => k = 0) 2 T ≤
      n ^ T * (n * 2) := hcost
    _ = n ^ T * (2 * n) := by rw [Nat.mul_comm n 2]

/-- A successful positive mark count has a first prescribed hit;
every preceding letter is outside the monitored family. -/
theorem launch_first_mark_prefix {n : Nat}
    (outside : Fin n → Bool) (a : Fin n) (k : Nat) :
    ∀ word : List (Fin n),
      launchMarkAccept outside a (k + 1) word = 1 →
      ∃ before after : List (Fin n),
        word = before ++ [a] ++ after ∧
        (∀ e, e ∈ before → outside e = true) ∧
        launchMarkAccept outside a k after = 1 := by
  intro word
  induction word with
  | nil =>
      intro h
      simp [launchMarkAccept] at h
  | cons e word ih =>
      intro h
      by_cases he : e = a
      · subst e
        refine ⟨[], word, rfl, ?_, ?_⟩
        · intro b hb
          cases hb
        · simpa [launchMarkAccept] using h
      · cases ho : outside e with
        | false =>
            simp [launchMarkAccept, he, ho] at h
        | true =>
            have htail :
                launchMarkAccept outside a (k + 1) word = 1 := by
              simpa [launchMarkAccept, he, ho] using h
            obtain ⟨before, after, hword, hbefore, hafter⟩ := ih htail
            refine ⟨e :: before, after, ?_, ?_, hafter⟩
            · simpa only [List.cons_append] using
                congrArg (fun w => e :: w) hword
            · intro b hb
              rcases List.mem_cons.mp hb with hb | hb
              · subst b
                exact ho
              · exact hbefore b hb

theorem launch_two_mark_prefix {n : Nat}
    (outside : Fin n → Bool) (a : Fin n)
    (word : List (Fin n))
    (h : launchMarkAccept outside a 2 word = 1) :
    ∃ before between after : List (Fin n),
      word = before ++ [a] ++ between ++ [a] ++ after ∧
      (∀ e, e ∈ before → outside e = true) ∧
      (∀ e, e ∈ between → outside e = true) := by
  obtain ⟨before, rest, hword, hbefore, hrest⟩ :=
    launch_first_mark_prefix outside a 1 word h
  obtain ⟨between, after, hrestWord, hbetween, _⟩ :=
    launch_first_mark_prefix outside a 0 rest hrest
  refine ⟨before, between, after, ?_, hbefore, hbetween⟩
  rw [hword, hrestWord]
  simp only [List.append_assoc]

/-- Launch readiness retains the sampled record, its genuine origin
tag, and all clear future kicks. -/
def CouponLaunchReady {n q : Nat}
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (ht : 2 ≤ (compileAdvice q).t)
    (z : FreshGhostConfig n q) : Prop :=
  Frozen fixed z.1 ∧
  SampledStage fixed s ⟨0, by omega⟩ z.1 ∧
  TaggedIndexStage s ⟨0, by omega⟩ z ∧
  ForwardClear z.1 s

/-- Deterministic physical launch from the cleared protected slots. -/
theorem launch_marked_ready {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (hclear : ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear z.1 (certSite s (n - 1 + j.val)))
    (before between : List (Fin n))
    (hbefore : ∀ e, e ∈ before → ¬ LaunchEdge (q := q) s e)
    (hbetween : ∀ e, e ∈ between → ¬ LaunchEdge (q := q) s e) :
    CouponLaunchReady fixed s ht
      (LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z
        (before ++ [certSite s (n - 1)] ++
          between ++ [certSite s (n - 1)])) := by
  let e := certSite s (n - 1)
  let zBefore := LDSinkBoundedKernel.run
    (freshGhostStep ring fixed s) z before
  let zArmed := freshGhostStep ring fixed s zBefore e
  let zBetween := LDSinkBoundedKernel.run
    (freshGhostStep ring fixed s) zArmed between
  have hscratch : LaunchScratch z.1 s false :=
    launchScratch_of_protected_clear z.1 s hn hclear
  have hbeforeProjection :
      zBefore.1 = runList ring fixed z.1 before :=
    fixedGhostRun_projection ring fixed s z before
  have hbeforeScratch : LaunchScratch zBefore.1 s false := by
    rw [hbeforeProjection]
    exact launch_outside_run ring fixed z.1 s false ht hn
      before hscratch hbefore
  have harmedProjection :
      zArmed.1 = step ring fixed zBefore.1 e :=
    freshGhost_projection ring fixed s zBefore e
  have harmedScratch : LaunchScratch zArmed.1 s true := by
    rw [harmedProjection]
    exact launch_arm ring fixed zBefore.1 s hn hbeforeScratch
  have hbetweenProjection :
      zBetween.1 = runList ring fixed zArmed.1 between :=
    fixedGhostRun_projection ring fixed s zArmed between
  have hbetweenScratch : LaunchScratch zBetween.1 s true := by
    rw [hbetweenProjection]
    exact launch_outside_run ring fixed zArmed.1 s true ht hn
      between harmedScratch hbetween
  have hrun :
      LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z
        (before ++ [e] ++ between ++ [e]) =
      freshGhostStep ring fixed s zBetween e := by
    simp only [List.append_assoc, fixedRun_append,
      LDSinkBoundedKernel.run, zBefore, zArmed, zBetween]
  have hprojection :
      (LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z
        (before ++ [e] ++ between ++ [e])).1 =
      runList ring fixed z.1
        (before ++ [e] ++ between ++ [e]) :=
    fixedGhostRun_projection ring fixed s z
      (before ++ [e] ++ between ++ [e])
  have hsampled := launch_two_marks ring fixed z.1 s ht hn
    hroot hz hclear before between hbefore hbetween
  unfold CouponLaunchReady
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hprojection]
    exact hsampled.1
  · rw [hprojection]
    constructor
    · simpa only [certSite_zero] using hsampled.2.1
    · exact hsampled.2.2
  · rw [hrun]
    exact tagged_second_launch ring fixed s ht hn
      zBetween hbetweenScratch
  · rw [hrun, freshGhost_projection]
    exact launch_forward_clear ring fixed zBetween.1 s hn
      hbetweenScratch.2.2.2

/-- Every counted successful launch has an actual physical prefix
with sampled-token provenance and clear future scratch. -/
theorem two_hit_launch_physical {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (hclear : ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear z.1 (certSite s (n - 1 + j.val)))
    (word : List (Fin n))
    (hword :
      launchMarkAccept (outsideLaunch (q := q) s)
        (certSite s (n - 1)) 2 word = 1) :
    ∃ before between after : List (Fin n),
      word = before ++ [certSite s (n - 1)] ++
        between ++ [certSite s (n - 1)] ++ after ∧
      CouponLaunchReady fixed s ht
        (LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z
          (before ++ [certSite s (n - 1)] ++
            between ++ [certSite s (n - 1)])) := by
  obtain ⟨before, between, after, hsplit, hbefore, hbetween⟩ :=
    launch_two_mark_prefix (outsideLaunch (q := q) s)
      (certSite s (n - 1)) word hword
  refine ⟨before, between, after, hsplit, ?_⟩
  exact launch_marked_ready ring fixed s ht hn hroot z hz hclear
    before between
    (fun e he => (outsideLaunch_true_iff s hn e).mp (hbefore e he))
    (fun e he => (outsideLaunch_true_iff s hn e).mp (hbetween e he))

/-- The protected-coupon clearing theorem supplies the launch
hypothesis on the actual post-cover reference/ghost state. -/
theorem two_hit_launch_after_cover {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (clear word : List (Fin n))
    (hclear :
      lastAccept ((compileAdvice q).t + 3)
        (clear.map (protectedLabel s)) = 1)
    (hword :
      launchMarkAccept (outsideLaunch (q := q) s)
        (certSite s (n - 1)) 2 word = 1) :
    ∃ before between after : List (Fin n),
      word = before ++ [certSite s (n - 1)] ++
        between ++ [certSite s (n - 1)] ++ after ∧
      CouponLaunchReady fixed s ht
        (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
          (LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z clear)
          (before ++ [certSite s (n - 1)] ++
            between ++ [certSite s (n - 1)])) := by
  let zClear := LDSinkBoundedKernel.run
    (freshGhostStep ring fixed s) z clear
  have hprojection : zClear.1 = runList ring fixed z.1 clear :=
    fixedGhostRun_projection ring fixed s z clear
  have hFrozen : Frozen fixed zClear.1 := by
    rw [hprojection]
    exact runList_frozen ring fixed z.1 clear hz
  have hslots : ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear zClear.1 (certSite s (n - 1 + j.val)) := by
    intro j
    rw [hprojection]
    exact protected_coupon_clears ring fixed z.1 s clear hn hclear j
  exact two_hit_launch_physical ring fixed s ht hn hroot
    zClear hFrozen hslots word hword

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree LeaderCountDyadicTail LDSinkBoundedKernel

/-!
Full invariant and same-word tolerant scan.
-/

-- A contains once-hit future labels. Entries already behind are harmless.
-- The sampled payload is retained explicitly; a bare index/tag is insufficient.
structure TolerantInvariant {n q : Nat}
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (j : Fin (compileAdvice q).t) (A : List Nat)
    (z : FreshGhostConfig n q) : Prop where
  frozen : Frozen fixed z.1
  sampled : SampledStage fixed s j z.1
  tag : z.2.trail (certSite s j.val) =
    some { origin := s, hops := j.val }
  unhitKick : ∀ k : Nat, j.val < k → k < (compileAdvice q).t →
    k ∉ A → (z.1 (certSite s (k + 1))).rawKick = false

theorem tolerant_invariant_tagged {n q : Nat}
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (j : Fin (compileAdvice q).t) (A : List Nat)
    (z : FreshGhostConfig n q)
    (h : TolerantInvariant fixed s j A z) :
    TaggedIndexStage s j z := by
  refine ⟨⟨rawPrefixSample
    (certificateWordOfAgents (compileAdvice q) fixed) s j,
    h.sampled.1, ?_⟩, h.sampled.2, h.tag⟩
  rfl

theorem tolerant_mem_erase_of_ne (a b : Nat) (hne : a ≠ b) :
    ∀ xs : List Nat, a ∈ xs → a ∈ eraseAvailable b xs := by
  intro xs
  induction xs with
  | nil =>
      intro ha
      cases ha
  | cons x xs ih =>
      intro ha
      by_cases hx : x = b
      · subst x
        simp only [eraseAvailable, if_pos rfl]
        rcases List.mem_cons.mp ha with he | ht
        · exact False.elim (hne he)
        · exact ht
      · simp only [eraseAvailable, if_neg hx]
        rcases List.mem_cons.mp ha with he | ht
        · exact List.mem_cons.mpr (Or.inl he)
        · exact List.mem_cons.mpr (Or.inr (ih ht))

theorem tolerant_kick_no_incoming {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e site : Fin n)
    (hno : site ≠ ring.rightNeighbor e)
    (hk : (C site).rawKick = false) :
    (step ring fixed C e site).rawKick = false := by
  by_cases hs : site = e
  · subst site
    exact (source_clears ring fixed C e).2
  · rw [other ring fixed C e site hs hno]
    exact hk

-- This covers every outside-family or already-behind selected edge,
-- including arbitrary collisions into the designated resident.
theorem tolerant_invariant_wait {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (j : Fin (compileAdvice q).t) (A : List Nat)
    (z : FreshGhostConfig n q) (e : Fin n)
    (h : TolerantInvariant fixed s j A z)
    (hsource : certSite s j.val ≠ e)
    (hforward : ∀ k : Nat, j.val < k → k < (compileAdvice q).t →
      certSite s k ≠ e) :
    TolerantInvariant fixed s j A (freshGhostStep ring fixed s z e) := by
  have hno : ∀ m : Nat, j.val < m → m ≤ (compileAdvice q).t →
      certSite s m ≠ ring.rightNeighbor e := by
    intro m hjm hmt he
    have hm : m - 1 + 1 = m := by omega
    have hneighbor :
        ring.rightNeighbor (certSite s (m - 1)) = certSite s m := by
      simpa only [hm] using ring_neighbor_certSite ring s (m - 1)
    have hedge : certSite s (m - 1) = e :=
      neighbor_injective ring (certSite s (m - 1)) e
        (hneighbor.trans he)
    by_cases hcurrent : m - 1 = j.val
    · apply hsource
      simpa only [hcurrent] using hedge
    · exact hforward (m - 1) (by omega) (by omega) hedge
  have htagged := tolerant_avoid_source_future ring fixed s j z e
    hsource hno (tolerant_invariant_tagged fixed s j A z h)
  refine ⟨step_frozen ring fixed z.1 h.frozen e,
    ⟨?_, htagged.2.1⟩, htagged.2.2, ?_⟩
  · exact resident_of_no_outgoing ring fixed z.1 e
      (certSite s j.val)
      (rawPrefixSample
        (certificateWordOfAgents (compileAdvice q) fixed) s j)
      hsource h.sampled.1
  · intro k hjk hkt hkA
    exact tolerant_kick_no_incoming ring fixed z.1 e
      (certSite s (k + 1))
      (hno (k + 1) (by omega) (by omega))
      (h.unhitKick k hjk hkt hkA)

theorem tolerant_invariant_first {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (j : Fin (compileAdvice q).t) (A : List Nat)
    (z : FreshGhostConfig n q)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (h : TolerantInvariant fixed s j A z)
    (k : Nat) (hjk : j.val < k) (hkt : k < (compileAdvice q).t)
    (hkA : k ∉ A) :
    TolerantInvariant fixed s j (k :: A)
      (freshGhostStep ring fixed s z (certSite s k)) := by
  have hjt := j.isLt
  have hsource : certSite s j.val ≠ certSite s k := by
    intro he
    have hv := site_offset_injective s j.val k (by omega) (by omega) he
    omega
  have hneighbor :
      ring.rightNeighbor (certSite s k) = certSite s (k + 1) :=
    ring_neighbor_certSite ring s k
  have hdistinct : ring.rightNeighbor (certSite s k) ≠ certSite s k :=
    Ne.symm (ring_neighbor_distinct ring (by omega) (certSite s k))
  have hsrc : (z.1 (certSite s k)).rawTok = none :=
    h.sampled.2 k hjk (by omega)
  have htgt : (z.1 (ring.rightNeighbor (certSite s k))).rawTok = none := by
    rw [hneighbor]
    exact h.sampled.2 (k + 1) (by omega) (by omega)
  have hkick : (z.1 (ring.rightNeighbor (certSite s k))).rawKick = false := by
    rw [hneighbor]
    exact h.unhitKick k hjk hkt hkA
  have hfirst := tolerant_first_premature ring fixed z.1
    (certSite s k) hdistinct hsrc htgt hkick
  have htarget :
      (step ring fixed z.1 (certSite s k) (certSite s (k + 1))).rawTok = none := by
    simpa only [hneighbor] using hfirst.1
  have hempty : ∀ m : Nat, j.val < m → m ≤ (compileAdvice q).t →
      (step ring fixed z.1 (certSite s k) (certSite s m)).rawTok = none := by
    intro m hjm hmt
    by_cases hm : m = k + 1
    · subst m
      exact htarget
    · have hno : certSite s m ≠ ring.rightNeighbor (certSite s k) := by
        rw [hneighbor]
        intro he
        have hv := site_offset_injective s m (k + 1)
          (by omega) (by omega) he
        exact hm hv
      exact empty_of_no_incoming ring fixed z.1 (certSite s k)
        (certSite s m) hno (h.sampled.2 m hjm hmt)
  refine ⟨step_frozen ring fixed z.1 h.frozen (certSite s k),
    ⟨?_, hempty⟩, ?_, ?_⟩
  · exact resident_of_no_outgoing ring fixed z.1 (certSite s k)
      (certSite s j.val)
      (rawPrefixSample
        (certificateWordOfAgents (compileAdvice q) fixed) s j)
      hsource h.sampled.1
  · rw [fresh_resident_tag_wait ring fixed s z (certSite s k)
      (certSite s j.val)
      (rawPrefixSample
        (certificateWordOfAgents (compileAdvice q) fixed) s j)
      hsource h.sampled.1]
    exact h.tag
  · intro m hjm hmt hmA
    have hmk : m ≠ k := by
      intro he
      exact hmA (List.mem_cons.mpr (Or.inl he))
    have hmOld : m ∉ A := by
      intro hm
      exact hmA (List.mem_cons.mpr (Or.inr hm))
    have hno : certSite s (m + 1) ≠ ring.rightNeighbor (certSite s k) := by
      rw [hneighbor]
      intro he
      have hv := site_offset_injective s (m + 1) (k + 1)
        (by omega) (by omega) he
      apply hmk
      omega
    exact tolerant_kick_no_incoming ring fixed z.1 (certSite s k)
      (certSite s (m + 1)) hno (h.unhitKick m hjm hmt hmOld)

theorem tolerant_invariant_progress {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (j : Fin (compileAdvice q).t) (A : List Nat)
    (z : FreshGhostConfig n q)
    (hj : j.val + 1 < (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (h : TolerantInvariant fixed s j A z) :
    TolerantInvariant fixed s ⟨j.val + 1, hj⟩
      (eraseAvailable (j.val + 1) A)
      (freshGhostStep ring fixed s z (certSite s j.val)) := by
  have hsampled := sampled_stage_advance ring fixed z.1 s j hj hn
    hroot h.frozen h.sampled
  have htagged := tolerant_progress ring fixed s j hj hn z
    (tolerant_invariant_tagged fixed s j A z h)
  refine ⟨step_frozen ring fixed z.1 h.frozen (certSite s j.val),
    hsampled, htagged.2.2, ?_⟩
  intro k hjk hkt hkA
  change j.val + 1 < k at hjk
  have hkOld : k ∉ A := by
    intro hk
    exact hkA (tolerant_mem_erase_of_ne k (j.val + 1)
      (by omega) A hk)
  have hno : certSite s (k + 1) ≠
      ring.rightNeighbor (certSite s j.val) := by
    rw [ring_neighbor_certSite]
    intro he
    have hv := site_offset_injective s (k + 1) (j.val + 1)
      (by omega) (by omega) he
    omega
  exact tolerant_kick_no_incoming ring fixed z.1 (certSite s j.val)
    (certSite s (k + 1)) hno
    (h.unhitKick k (by omega) hkt hkOld)

theorem tolerant_terminal_good {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (j : Fin (compileAdvice q).t) (A : List Nat)
    (z : FreshGhostConfig n q)
    (h : TolerantInvariant fixed s j A z)
    (hlast : j.val + 1 = (compileAdvice q).t) :
    freshGhostGood (freshGhostStep ring fixed s z (certSite s j.val)) := by
  let W := certificateWordOfAgents (compileAdvice q) fixed
  have hjlt : j.val < (compileAdvice q).t := j.isLt
  have hjval : j.val = (compileAdvice q).t - 1 := by omega
  have hj : j = (⟨(compileAdvice q).t - 1, by omega⟩ :
      Fin (compileAdvice q).t) := by
    apply Fin.ext
    change j.val = (compileAdvice q).t - 1
    exact hjval
  have hprefix : rawPrefixSample W s j = rawSampledTerminal W s ht :=
    (congrArg (rawPrefixSample W s) hj).trans
      (ghost_prefix_last_eq_sampled W s ht)
  have htok : (z.1 (certSite s j.val)).rawTok =
      some (rawSampledTerminal W s ht) :=
    h.sampled.1.trans (congrArg some hprefix)
  have hneighbor : ring.rightNeighbor (certSite s j.val) =
      certSite s (compileAdvice q).t := by
    simpa only [hlast] using ring_neighbor_certSite ring s j.val
  have hreport :
      (rawResult ring z.1 (certSite s j.val)).reject = true := by
    unfold rawResult
    rw [hneighbor]
    exact sampled_bad_pair_rejects W s ht
      (by intro i; exact hroot i) hbad _ _ htok
      (h.sampled.2 (compileAdvice q).t j.isLt (Nat.le_refl _))
      (frozen_fields fixed z.1 h.frozen (certSite s (compileAdvice q).t)).1
      (frozen_rootless fixed z.1 hroot h.frozen (certSite s j.val))
      (frozen_rootless fixed z.1 hroot h.frozen
        (certSite s (compileAdvice q).t))
  have hrow : (rawResult ring z.1 (certSite s j.val)).row = "R0c" :=
    fixed_raw_reject_row _ _ _ _ hreport
  have htag := h.tag
  have hselected :
      freshSelectedReject ring z.1 z.2 (certSite s j.val) = true := by
    simp [freshSelectedReject, htag, hlast, hrow, hreport]
  simp [freshGhostGood, freshGhost_flag_step, hselected]

-- Active states have j<t. Terminal states accept every remaining suffix.
-- A second premature hit is an absorbing rejection of this proof trial.
def tolerantAccept {n : Nat} (s : Fin n) (t : Nat) :
    List (Fin n) → Nat → List Nat → Nat
  | [], j, _ => if t ≤ j then 1 else 0
  | e :: word, j, A =>
      if t ≤ j then 1
      else
        let k := (unrotate s e).val
        if k = j then
          tolerantAccept s t word (j + 1) (eraseAvailable (j + 1) A)
        else if j < k ∧ k < t then
          if k ∈ A then 0
          else tolerantAccept s t word j (k :: A)
        else tolerantAccept s t word j A

theorem tolerantAccept_terminal {n : Nat}
    (s : Fin n) (t j : Nat) (A : List Nat)
    (word : List (Fin n)) (hj : t ≤ j) :
    tolerantAccept s t word j A = 1 := by
  cases word <;> simp only [tolerantAccept, if_pos hj]

theorem tolerantAccept_le_one {n : Nat}
    (s : Fin n) (t : Nat) :
    ∀ (word : List (Fin n)) (j : Nat) (A : List Nat),
      tolerantAccept s t word j A ≤ 1 := by
  intro word
  induction word with
  | nil =>
      intro j A
      by_cases hj : t ≤ j <;> simp [tolerantAccept, hj]
  | cons e word ih =>
      intro j A
      by_cases hj : t ≤ j
      · simpa only [tolerantAccept, if_pos hj] using (Nat.le_refl 1)
      · by_cases he : (unrotate s e).val = j
        · simpa only [tolerantAccept, if_neg hj, if_pos he] using
            ih (j + 1) (eraseAvailable (j + 1) A)
        · by_cases hf : j < (unrotate s e).val ∧ (unrotate s e).val < t
          · by_cases hm : (unrotate s e).val ∈ A
            · simpa only [tolerantAccept, if_neg hj, if_neg he, if_pos hf,
                if_pos hm] using (Nat.zero_le 1)
            · simpa only [tolerantAccept, if_neg hj, if_neg he, if_pos hf,
                if_neg hm] using ih j ((unrotate s e).val :: A)
          · simpa only [tolerantAccept, if_neg hj, if_neg he, if_neg hf] using ih j A

theorem tolerant_scan_word_sound {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s) :
    ∀ (word : List (Fin n)) (j : Fin (compileAdvice q).t)
      (A : List Nat) (z : FreshGhostConfig n q),
      TolerantInvariant fixed s j A z →
      tolerantAccept s (compileAdvice q).t word j.val A = 1 →
      freshGhostGood (LDSinkBoundedKernel.run
        (freshGhostStep ring fixed s) z word) := by
  intro word
  induction word with
  | nil =>
      intro j A z h haccept
      have hnon : ¬ (compileAdvice q).t ≤ j.val := by
        have hj := j.isLt
        omega
      have hzero : (0 : Nat) = 1 := by
        simpa only [tolerantAccept, if_neg hnon] using haccept
      cases hzero
  | cons e word ih =>
      intro j A z h haccept
      have hjt := j.isLt
      have hnon : ¬ (compileAdvice q).t ≤ j.val := by omega
      have hdecode : certSite s (unrotate s e).val = e :=
        rotate_unrotate s e
      by_cases hc : (unrotate s e).val = j.val
      · have htail : tolerantAccept s (compileAdvice q).t word
            (j.val + 1) (eraseAvailable (j.val + 1) A) = 1 := by
          simpa only [tolerantAccept, if_neg hnon, if_pos hc] using haccept
        have hedge : e = certSite s j.val := by
          rw [← hdecode, hc]
        by_cases hj : j.val + 1 < (compileAdvice q).t
        · have hnext := tolerant_invariant_progress ring fixed s j A z
            hj hn hroot h
          have hgood := ih ⟨j.val + 1, hj⟩ (eraseAvailable (j.val + 1) A)
            (freshGhostStep ring fixed s z (certSite s j.val)) hnext htail
          simpa only [LDSinkBoundedKernel.run, hedge] using hgood
        · have hlast : j.val + 1 = (compileAdvice q).t := by omega
          have hgood := tolerant_terminal_good ring fixed s ht hroot hbad
            j A z h hlast
          have hpadded := fixedGhostRun_sticky ring fixed s word
            (freshGhostStep ring fixed s z (certSite s j.val)) hgood
          simpa only [LDSinkBoundedKernel.run, hedge] using hpadded
      · by_cases hf : j.val < (unrotate s e).val ∧
            (unrotate s e).val < (compileAdvice q).t
        · by_cases hm : (unrotate s e).val ∈ A
          · have hzero : (0 : Nat) = 1 := by
              simpa only [tolerantAccept, if_neg hnon, if_neg hc,
                if_pos hf, if_pos hm] using haccept
            cases hzero
          · have htail : tolerantAccept s (compileAdvice q).t word
                j.val ((unrotate s e).val :: A) = 1 := by
              simpa only [tolerantAccept, if_neg hnon, if_neg hc,
                if_pos hf, if_neg hm] using haccept
            have hnext := tolerant_invariant_first ring fixed s j A z hn h
              (unrotate s e).val hf.1 hf.2 hm
            have hgood := ih j ((unrotate s e).val :: A)
              (freshGhostStep ring fixed s z
                (certSite s (unrotate s e).val)) hnext htail
            simpa only [LDSinkBoundedKernel.run, hdecode] using hgood
        · have htail : tolerantAccept s (compileAdvice q).t word j.val A = 1 := by
            simpa only [tolerantAccept, if_neg hnon, if_neg hc, if_neg hf]
              using haccept
          have hsource : certSite s j.val ≠ e := by
            intro he
            have hv := site_offset_injective s j.val (unrotate s e).val
              (by omega) (unrotate s e).isLt (he.trans hdecode.symm)
            exact hc hv.symm
          have hforward : ∀ k : Nat, j.val < k → k < (compileAdvice q).t →
              certSite s k ≠ e := by
            intro k hjk hkt he
            have hv := site_offset_injective s k (unrotate s e).val
              (by omega) (unrotate s e).isLt (he.trans hdecode.symm)
            exact hf ⟨by omega, by omega⟩
          have hnext := tolerant_invariant_wait ring fixed s j A z e h
            hsource hforward
          have hgood := ih j A (freshGhostStep ring fixed s z e) hnext htail
          simpa only [LDSinkBoundedKernel.run] using hgood

-- Each accepted length-T word is disjoint from every word still missing
-- freshGhostGood. This is the all-n^T-words counting interface used by
-- the existing stopped-cost machinery; no finite T is replaced by infinity.
theorem tolerant_scan_success_count {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (j : Fin (compileAdvice q).t) (A : List Nat)
    (z : FreshGhostConfig n q)
    (h : TolerantInvariant fixed s j A z) :
    ∀ T,
      Prob.scheduleSum n T
          (fun word => tolerantAccept s (compileAdvice q).t word j.val A) +
        wordSum (freshGhostStep ring fixed s) (miss freshGhostGood) z T ≤ n ^ T := by
  intro T
  exact Prob.FixedAttempts.accepted_add_miss_le_total
    (freshGhostStep ring fixed s) freshGhostGood T
    (fun word => tolerantAccept s (compileAdvice q).t word j.val A)
    (fun word _ => tolerantAccept_le_one s (compileAdvice q).t word j.val A)
    z (fun word _ ha =>
      tolerant_scan_word_sound ring fixed s ht hn hroot hbad word j A z h ha)

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting

/-!
Physical-edge stopping clock for the tolerant scan.

Failure is an absorbing observer state. The physical process is still
advanced by the same selected letter in the product construction.
-/

inductive TolerantScanState where
  | failed
  | live (j : Nat) (A : List Nat)

def tolerantScanStep {n : Nat} (s : Fin n) (t : Nat) :
    TolerantScanState → Fin n → TolerantScanState
  | .failed, _ => .failed
  | .live j A, e =>
      if t ≤ j then .live j A
      else
        let k := (unrotate s e).val
        if k = j then .live (j + 1) (eraseAvailable (j + 1) A)
        else if j < k ∧ k < t then
          if k ∈ A then .failed else .live j (k :: A)
        else .live j A

def tolerantScanDone (t : Nat) : TolerantScanState → Prop
  | .failed => True
  | .live j _ => t ≤ j

def tolerantScanSuccess (t : Nat) : TolerantScanState → Prop
  | .failed => False
  | .live j _ => t ≤ j

instance tolerantScanSuccessDecidable
    (t : Nat) (x : TolerantScanState) :
    Decidable (tolerantScanSuccess t x) := by
  cases x with
  | failed => exact inferInstanceAs (Decidable False)
  | live j A => exact inferInstanceAs (Decidable (t ≤ j))

def tolerantRemaining (t : Nat) : TolerantScanState → Nat
  | .failed => 0
  | .live j _ => t - j

def tolerantChosen {n : Nat} (s : Fin n) :
    TolerantScanState → Fin n
  | .failed => s
  | .live j _ => certSite s j

theorem tolerant_unrotate_site {n : Nat}
    (s : Fin n) (j : Nat) (hj : j < n) :
    (unrotate s (certSite s j)).val = j := by
  have h := congrArg Fin.val
    (unrotate_rotate s (⟨j, hj⟩ : Fin n))
  exact h

theorem tolerant_remaining_nonincrease {n : Nat}
    (s : Fin n) (t : Nat)
    (x : TolerantScanState) (e : Fin n) :
    tolerantRemaining t (tolerantScanStep s t x e) ≤
      tolerantRemaining t x := by
  cases x with
  | failed =>
      exact Nat.le_refl _
  | live j A =>
      by_cases hdone : t ≤ j
      · simp [tolerantScanStep, hdone, tolerantRemaining]
      · by_cases he : (unrotate s e).val = j
        · have hstep :
              tolerantScanStep s t (.live j A) e =
                .live (j + 1) (eraseAvailable (j + 1) A) := by
                simp [tolerantScanStep, hdone, he]
          rw [hstep]
          change t - (j + 1) ≤ t - j
          omega
        · by_cases hf : j < (unrotate s e).val ∧
              (unrotate s e).val < t
          · by_cases hh : (unrotate s e).val ∈ A
            · simp [tolerantScanStep, hdone, he, hf, hh,
                tolerantRemaining]
            · simp [tolerantScanStep, hdone, he, hf, hh,
                tolerantRemaining]
          · simp [tolerantScanStep, hdone, he, hf,
              tolerantRemaining]

/-- The current required edge lowers the remaining-stage potential.
The same statement covers the final progress edge. -/
theorem tolerant_remaining_drop {n : Nat}
    (s : Fin n) (t : Nat) (htn : t ≤ n)
    (x : TolerantScanState) (hx : ¬ tolerantScanDone t x) :
    tolerantRemaining t
        (tolerantScanStep s t x (tolerantChosen s x)) + 1 ≤
      tolerantRemaining t x := by
  cases x with
  | failed =>
      exact False.elim (hx trivial)
  | live j A =>
      have hdone : ¬ t ≤ j := hx
      have hjt : j < t := by omega
      have hj : j < n := by omega
      have he := tolerant_unrotate_site s j hj
      have hstep :
          tolerantScanStep s t (.live j A)
              (tolerantChosen s (.live j A)) =
            .live (j + 1) (eraseAvailable (j + 1) A) := by
              simp [tolerantScanStep, tolerantChosen, hdone, he]
      rw [hstep]
      change t - (j + 1) + 1 ≤ t - j
      omega

/-- At most n global services per remaining required progress edge.
A second premature hit stops the watch immediately. -/
theorem tolerant_scan_stopping_cost {n : Nat}
    (s : Fin n) (t : Nat) (htn : t ≤ n)
    (j : Nat) (A : List Nat) (T : Nat) :
    costNumerator (tolerantScanStep s t)
        (tolerantScanDone t) (.live j A) T ≤
      n ^ T * (n * (t - j)) := by
  exact Prob.costNumerator_le_of_nominated_edge
    (tolerantScanStep s t) (tolerantScanDone t)
    (tolerantRemaining t) (tolerantChosen s)
    (fun x hx => tolerant_remaining_drop s t htn x hx)
    (fun x _ e => tolerant_remaining_nonincrease s t x e)
    (.live j A) T

/-- The stopping-cost theorem on the same physical scheduler words
while the actual reference/ghost process continues to evolve. -/
theorem tolerant_scan_physical_stopping_cost {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (z : FreshGhostConfig n q) (j : Nat) (A : List Nat)
    (T : Nat) :
    costNumerator
        (fun (x : TolerantScanState × FreshGhostConfig n q)
            (e : Fin n) =>
          (tolerantScanStep s (compileAdvice q).t x.1 e,
            freshGhostStep ring fixed s x.2 e))
        (fun x => tolerantScanDone (compileAdvice q).t x.1)
        (.live j A, z) T ≤
      n ^ T * (n * ((compileAdvice q).t - j)) := by
  rw [Prob.costNumerator_ghost_eq
    (tolerantScanStep s (compileAdvice q).t)
    (fun (x : TolerantScanState × FreshGhostConfig n q)
        (e : Fin n) =>
      (tolerantScanStep s (compileAdvice q).t x.1 e,
        freshGhostStep ring fixed s x.2 e))
    (fun _ _ => rfl) (tolerantScanDone (compileAdvice q).t)
    (.live j A, z) T]
  exact tolerant_scan_stopping_cost s (compileAdvice q).t
    (by omega) j A T

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree LeaderCountDyadicTail LDSinkBoundedKernel

/-!
Interfaces between launch, the stopped observer, and the
physical tolerant scan.
-/

theorem tolerant_invariant_of_launch {n q : Nat}
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t) (z : FreshGhostConfig n q)
    (h : CouponLaunchReady fixed s ht z) :
    TolerantInvariant fixed s ⟨0, by omega⟩ [] z := by
  refine ⟨h.1, h.2.1, h.2.2.1.2.2, ?_⟩
  intro k _ hkt _
  exact ((h.2.2.2) (⟨k, hkt⟩ : Fin (compileAdvice q).t)).2

theorem tolerant_failed_run {n : Nat}
    (s : Fin n) (t : Nat) (word : List (Fin n)) :
    LDSinkBoundedKernel.run (tolerantScanStep s t) .failed word = .failed := by
  induction word with
  | nil => rfl
  | cons e word ih =>
      simpa only [LDSinkBoundedKernel.run, tolerantScanStep] using ih

theorem tolerant_state_accept_eq_run {n : Nat}
    (s : Fin n) (t : Nat) :
    ∀ (word : List (Fin n)) (x : TolerantScanState),
      (match x with
        | .failed => 0
        | .live j A => tolerantAccept s t word j A) =
      if tolerantScanSuccess t
          (LDSinkBoundedKernel.run (tolerantScanStep s t) x word)
        then 1 else 0 := by
  classical
  intro word
  induction word with
  | nil =>
      intro x
      cases x with
      | failed => simp [LDSinkBoundedKernel.run, tolerantScanSuccess]
      | live j A =>
          by_cases h : t ≤ j <;>
            simp [LDSinkBoundedKernel.run, tolerantScanSuccess, tolerantAccept, h]
  | cons e word ih =>
      intro x
      cases x with
      | failed =>
          simp [tolerant_failed_run, tolerantScanSuccess]
      | live j A =>
          by_cases hj : t ≤ j
          · have hh := ih (.live j A)
            change tolerantAccept s t word j A = _ at hh
            have hvalue := (tolerantAccept_terminal s t j A word hj).symm.trans hh
            simpa only [tolerantAccept, LDSinkBoundedKernel.run,
              tolerantScanStep, if_pos hj] using hvalue
          · by_cases he : (unrotate s e).val = j
            · simpa only [tolerantAccept, LDSinkBoundedKernel.run,
                tolerantScanStep, if_neg hj, if_pos he] using
                ih (.live (j + 1) (eraseAvailable (j + 1) A))
            · by_cases hf : j < (unrotate s e).val ∧ (unrotate s e).val < t
              · by_cases hm : (unrotate s e).val ∈ A
                · simpa only [tolerantAccept, LDSinkBoundedKernel.run,
                    tolerantScanStep, if_neg hj, if_neg he, if_pos hf,
                    if_pos hm] using ih .failed
                · simpa only [tolerantAccept, LDSinkBoundedKernel.run,
                    tolerantScanStep, if_neg hj, if_neg he, if_pos hf,
                    if_neg hm] using ih (.live j ((unrotate s e).val :: A))
              · simpa only [tolerantAccept, LDSinkBoundedKernel.run,
                  tolerantScanStep, if_neg hj, if_neg he, if_neg hf] using
                  ih (.live j A)

theorem tolerant_accept_eq_chain_success {n : Nat}
    (s : Fin n) (t j : Nat) (A : List Nat) (word : List (Fin n)) :
    tolerantAccept s t word j A =
      if tolerantScanSuccess t
          (LDSinkBoundedKernel.run (tolerantScanStep s t) (.live j A) word)
        then 1 else 0 := by
  classical
  exact tolerant_state_accept_eq_run s t word (.live j A)

/-- A second premature hit is a literal absorbing failure of the
observer. The physical ghost step still occurs on that letter. -/
theorem tolerant_second_hit_failure {n : Nat}
    (s : Fin n) (t j : Nat) (A : List Nat) (e : Fin n)
    (hfuture : j < (unrotate s e).val ∧ (unrotate s e).val < t)
    (hhit : (unrotate s e).val ∈ A) :
    tolerantScanStep s t (.live j A) e = .failed := by
  have hj : ¬ t ≤ j := by omega
  have he : (unrotate s e).val ≠ j := by omega
  simp only [tolerantScanStep, if_neg hj, if_neg he,
    if_pos hfuture, if_pos hhit]

/-- Physical soundness for the complete successful cover/launch/scan
word. This theorem does not assert the unfinished retry budget. -/
theorem coupon_attempt_word_sound {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (clear before between scan : List (Fin n))
    (hclear : lastAccept ((compileAdvice q).t + 3)
      (clear.map (protectedLabel s)) = 1)
    (hbefore : ∀ e, e ∈ before → ¬ LaunchEdge (q := q) s e)
    (hbetween : ∀ e, e ∈ between → ¬ LaunchEdge (q := q) s e)
    (hscan : tolerantAccept s (compileAdvice q).t scan 0 [] = 1) :
    freshGhostGood
      (LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z
        (clear ++
          ((before ++ [certSite s (n - 1)] ++
            between ++ [certSite s (n - 1)]) ++ scan))) := by
  let zClear := LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z clear
  let launch := before ++ [certSite s (n - 1)] ++
    between ++ [certSite s (n - 1)]
  let zLaunch := LDSinkBoundedKernel.run
    (freshGhostStep ring fixed s) zClear launch
  have hproj : zClear.1 = runList ring fixed z.1 clear :=
    fixedGhostRun_projection ring fixed s z clear
  have hFrozen : Frozen fixed zClear.1 := by
    rw [hproj]
    exact runList_frozen ring fixed z.1 clear hz
  have hslots : ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear zClear.1 (certSite s (n - 1 + j.val)) := by
    intro j
    rw [hproj]
    exact protected_coupon_clears ring fixed z.1 s clear hn hclear j
  have hready : CouponLaunchReady fixed s ht zLaunch :=
    launch_marked_ready ring fixed s ht hn hroot zClear hFrozen
      hslots before between hbefore hbetween
  have hinv : TolerantInvariant fixed s ⟨0, by omega⟩ [] zLaunch :=
    tolerant_invariant_of_launch fixed s ht zLaunch hready
  have hgood := tolerant_scan_word_sound ring fixed s ht hn hroot hbad
    scan ⟨0, by omega⟩ [] zLaunch hinv hscan
  simpa only [fixedRun_append, zLaunch, zClear, launch] using hgood

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (AttemptNode RetryKernel retryCount)

/-!
Online first-cover, launch and tolerant-scan attempt.
The attempt observer is distinct from the real ghost process.
At success it checks the real sticky seen flag; at retry it keeps
the actual reached ghost state and every physical scratch field.
The exact joint finite-horizon budget remains an explicit premise.
-/

inductive CouponAttemptPhase (n : Nat) where
  | covering (mask : Fin n → Bool) (word : List (Fin n))
  | launching (hits : Nat)
  | scanning (j : Nat) (once : List Nat)
  | succeeded
  | failed

def couponAttemptStart {n q : Nat} (s : Fin n) :
    CouponAttemptPhase n :=
  .covering (fun e =>
    canonicalMask ((compileAdvice q).t + 3) (protectedLabel s e)) []

/-- Online first cover, factorial test, two hit launch and scan. -/
def couponAttemptPhaseNext {n q : Nat} (s : Fin n) :
    CouponAttemptPhase n → Fin n → CouponAttemptPhase n
  | .covering mask word, e =>
      let mask' := maskDrop mask e
      let word' := word ++ [e]
      if maskSize mask' = 0 then
        if lastAccept ((compileAdvice q).t + 3)
            (word'.map (protectedLabel s)) = 1
        then .launching 0
        else .failed
      else .covering mask' word'
  | .launching hits, e =>
      if e = certSite s (n - 1) then
        if hits = 0 then .launching 1
        else if hits = 1 then .scanning 0 []
        else .failed
      else if outsideLaunch (q := q) s e then .launching hits
      else .failed
  | .scanning j once, e =>
      match tolerantScanStep s (compileAdvice q).t (.live j once) e with
      | .failed => .failed
      | .live k once' =>
          if (compileAdvice q).t ≤ k then .succeeded
          else .scanning k once'
  | .succeeded, _ => .succeeded
  | .failed, _ => .failed

theorem couponAttemptFailed_absorbing {n q : Nat} (s e : Fin n) :
    couponAttemptPhaseNext (q := q) s (.failed) e = .failed := by
  rfl

theorem couponAttemptSucceeded_absorbing {n q : Nat} (s e : Fin n) :
    couponAttemptPhaseNext (q := q) s (.succeeded) e = .succeeded := by
  rfl

theorem couponAttempt_second_premature {n q : Nat}
    (s e : Fin n) (j : Nat) (once : List Nat)
    (hfuture : j < (unrotate s e).val ∧
      (unrotate s e).val < (compileAdvice q).t)
    (hhit : (unrotate s e).val ∈ once) :
    couponAttemptPhaseNext (q := q) s (.scanning j once) e =
      .failed := by
  have h := tolerant_second_hit_failure s (compileAdvice q).t
    j once e hfuture hhit
  simp only [couponAttemptPhaseNext, h]

/-- Retry seeds always satisfy the original frozen-public invariant. -/
abbrev CouponSeed {n q : Nat}
    (fixed : (protocol q).Configuration n) :=
  { z : FreshGhostConfig n q // Frozen fixed z.1 }

def couponSeedStep {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed) (e : Fin n) :
    CouponSeed fixed :=
  ⟨freshGhostStep ring fixed s seed.1 e, by
    rw [freshGhost_projection]
    exact step_frozen ring fixed seed.1.1 seed.2 e⟩

theorem couponSeedStep_physical {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed) (e : Fin n) :
    (couponSeedStep ring fixed s seed e).1 =
      freshGhostStep ring fixed s seed.1 e := by
  rfl

/-- Only proof-side observation restarts; never the physical ghost. -/
def couponTrialKernel {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n) :
    RetryKernel
      (CouponSeed fixed × CouponAttemptPhase n)
      (CouponSeed fixed) n :=
  { start := fun seed => (seed, couponAttemptStart (q := q) s)
    step := fun a e =>
      let nextSeed := couponSeedStep ring fixed s a.1 e
      match couponAttemptPhaseNext (q := q) s a.2 e with
      | .succeeded =>
          if nextSeed.1.2.seen then .success else .retry nextSeed
      | .failed => .retry nextSeed
      | phase => .active (nextSeed, phase)
    valid := fun _ => True
    retry_valid := by
      intro a e child h
      trivial }

def couponTrialRelation {n q : Nat}
    (fixed : (protocol q).Configuration n)
    (z : FreshGhostConfig n q)
    (a : CouponSeed fixed × CouponAttemptPhase n) : Prop :=
  z = a.1.1

/-- A complete same-edge RetrySimulation with actual reached restarts. -/
theorem couponTrialSimulation {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n) :
    Prob.RetrySimulation
      (couponTrialKernel ring fixed s)
      (freshGhostStep ring fixed s)
      freshGhostGood
      (couponTrialRelation fixed) := by
  intro z a hrel hnot e
  cases a with
  | mk seed phase =>
      change z = seed.1 at hrel
      rw [hrel]
      cases hp : couponAttemptPhaseNext (q := q) s phase e with
      | succeeded =>
          cases hs : (freshGhostStep ring fixed s seed.1 e).2.seen <;>
            simp [couponTrialKernel, couponTrialRelation,
              couponSeedStep, couponAttemptStart,
              freshGhostGood, hp, hs]
      | failed =>
          simp [couponTrialKernel, couponTrialRelation,
            couponSeedStep, couponAttemptStart, hp]
      | covering mask word =>
          simp [couponTrialKernel, couponTrialRelation,
            couponSeedStep, hp]
      | launching hits =>
          simp [couponTrialKernel, couponTrialRelation,
            couponSeedStep, hp]
      | scanning j once =>
          simp [couponTrialKernel, couponTrialRelation,
            couponSeedStep, hp]

/-- OPEN budget definition; no proof is asserted here.
It is one joint D-cost plus P-retry inequality, not a collection
of independently ceiling-rounded stage-cost claims. -/
def CouponJointBudget {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n) : Prop :=
  ∀ seed : CouponSeed fixed, ∀ T : Nat,
    (couponGPair (compileAdvice q).t).2 *
      costNumerator (Prob.attemptStepper
        (couponTrialKernel ring fixed s))
        (fun node => Prob.attemptGood node ∨ Prob.attemptFail node)
        (.active ((couponTrialKernel ring fixed s).start seed)) T +
      (n * (couponGPair (compileAdvice q).t).1) *
        retryCount (couponTrialKernel ring fixed s)
          (.active ((couponTrialKernel ring fixed s).start seed)) T ≤
      n ^ T * (n * (couponGPair (compileAdvice q).t).1)

/-- Conditional instantiation of the exact scaled renewal theorem. -/
theorem couponGhost_scaled_of_joint_budget {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (hbudget : CouponJointBudget ring fixed s) :
    ∀ T,
      (couponGPair (compileAdvice q).t).2 *
        costNumerator (freshGhostStep ring fixed s)
          freshGhostGood z T ≤
        n ^ T * (n * (couponGPair (compileAdvice q).t).1) := by
  let seed : CouponSeed fixed := ⟨z, hz⟩
  have hrel :
      couponTrialRelation fixed z
        ((couponTrialKernel ring fixed s).start seed) := by
    rfl
  exact Prob.ScaledRenewal.costNumerator_renewal_scaled_le
    (freshGhostStep ring fixed s) freshGhostGood
    (couponTrialKernel ring fixed s)
    (couponTrialRelation fixed)
    (couponTrialSimulation ring fixed s)
    (couponGPair (compileAdvice q).t).2
    (n * (couponGPair (compileAdvice q).t).1)
    (by
      intro child hvalid T
      exact hbudget child T)
    z seed (by trivial) hrel

/-- A generic exact Rat bridge. An integer B establishes almost-sure
hitting; cross-multiplication retains the exact partial-moment
coefficient B/D without separately rounding any stage. -/
theorem coupon_scaled_expected_ratio
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (hn : 0 < n) (x : S) (D B : Nat) (hD : 0 < D)
    (hscaled : ∀ T,
      D * costNumerator next P x T ≤ n ^ T * B) :
    UniformFirstHit.ExpectedHittingTimeAtMost next P x
      ((B : Rat) / (D : Rat)) := by
  have hDB : B ≤ D * B := by
    have h := Nat.mul_le_mul_right B (show 1 ≤ D by omega)
    simpa only [Nat.one_mul] using h
  have hNat : ∀ T, costNumerator next P x T ≤ n ^ T * B := by
    intro T
    have hmul : D * costNumerator next P x T ≤
        D * (n ^ T * B) := by
      calc
        D * costNumerator next P x T ≤ n ^ T * B :=
          hscaled T
        _ ≤ n ^ T * (D * B) :=
          Nat.mul_le_mul_left _ hDB
        _ = D * (n ^ T * B) := by ac_rfl
    exact Nat.le_of_mul_le_mul_left hmul hD
  have hExpected :
      UniformFirstHit.ExpectedHittingTimeAtMost next P x
        (B : Rat) :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      next P hn x B).mpr hNat
  refine ⟨hExpected.1, ?_⟩
  intro K
  rw [UniformFirstHit.partialExpectation_eq next P hn x K]
  have hmoment :
      D * UniformFirstHit.momentNumerator next P x K ≤
        n ^ K * B := by
    calc
      D * UniformFirstHit.momentNumerator next P x K ≤
          D * costNumerator next P x K :=
        Nat.mul_le_mul_left D
          (UniformFirstHit.moment_le_cost next P x K)
      _ ≤ n ^ K * B := hscaled K
  have hcast :
      (((D * UniformFirstHit.momentNumerator next P x K) : Nat) : Rat) ≤
        (((n ^ K * B) : Nat) : Rat) :=
    Rat.natCast_le_natCast.mpr hmoment
  have hcross :
      (D : Rat) * (UniformFirstHit.momentNumerator next P x K : Rat) ≤
        (B : Rat) * (n : Rat) ^ K := by
    calc
      (D : Rat) * (UniformFirstHit.momentNumerator next P x K : Rat) =
          (((D * UniformFirstHit.momentNumerator next P x K) : Nat) : Rat) := by
        rw [Rat.natCast_mul]
      _ ≤ (((n ^ K * B) : Nat) : Rat) := hcast
      _ = (B : Rat) * (n : Rat) ^ K := by
        rw [Rat.natCast_mul, Rat.natCast_pow]
        exact Rat.mul_comm _ _
  have hq : (0 : Rat) < (n : Rat) ^ K :=
    Rat.pow_pos (Rat.natCast_pos.2 hn)
  have hden : (0 : Rat) < (D : Rat) :=
    Rat.natCast_pos.2 hD
  apply Rat.le_of_mul_le_mul_right _ hden
  rw [Rat.div_mul_cancel (Rat.ne_of_gt hden)]
  apply Rat.le_of_mul_le_mul_right _ hq
  calc
    ((UniformFirstHit.momentNumerator next P x K : Rat) /
        (n : Rat) ^ K) * (D : Rat) * (n : Rat) ^ K =
      (D : Rat) * (UniformFirstHit.momentNumerator next P x K : Rat) := by
        calc
          ((UniformFirstHit.momentNumerator next P x K : Rat) /
              (n : Rat) ^ K) * (D : Rat) * (n : Rat) ^ K =
            (((UniformFirstHit.momentNumerator next P x K : Rat) /
                (n : Rat) ^ K) * (n : Rat) ^ K) * (D : Rat) := by
              rw [Rat.mul_assoc, Rat.mul_comm (D : Rat), ← Rat.mul_assoc]
          _ = (UniformFirstHit.momentNumerator next P x K : Rat) *
              (D : Rat) := by
                rw [Rat.div_mul_cancel (Rat.ne_of_gt hq)]
          _ = (D : Rat) *
              (UniformFirstHit.momentNumerator next P x K : Rat) := by
                exact Rat.mul_comm _ _
    _ ≤ (B : Rat) * (n : Rat) ^ K := hcross

theorem couponGhost_expected_of_joint_budget {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (hbudget : CouponJointBudget ring fixed s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (freshGhostStep ring fixed s) freshGhostGood z
      ((n : Rat) * couponG (compileAdvice q).t) := by
  have hnpos : 0 < n := by omega
  have hrational :=
    coupon_scaled_expected_ratio
      (freshGhostStep ring fixed s) freshGhostGood
      hnpos z
      (couponGPair (compileAdvice q).t).2
      (n * (couponGPair (compileAdvice q).t).1)
      (couponGPair_den_pos (compileAdvice q).t)
      (couponGhost_scaled_of_joint_budget ring fixed s z hz hbudget)
  simpa only [couponG, Rat.natCast_mul,
    Rat.div_def, Rat.mul_assoc] using hrational

/-- The requested fresh-scan hypotheses are explicit; the extra
joint budget is not smuggled into the conclusion. -/
theorem coupon_clear_scaled_if_joint_budget {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (hbudget : CouponJointBudget ring fixed s) :
    ∀ T,
      (couponGPair (compileAdvice q).t).2 *
        costNumerator (freshGhostStep ring fixed s)
          freshGhostGood z T ≤
        n ^ T * (n * (couponGPair (compileAdvice q).t).1) := by
  exact couponGhost_scaled_of_joint_budget ring fixed s z hz hbudget

theorem coupon_clear_expected_if_joint_budget {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (hbudget : CouponJointBudget ring fixed s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (freshGhostStep ring fixed s) freshGhostGood z
      ((n : Rat) * couponG (compileAdvice q).t) := by
  exact couponGhost_expected_of_joint_budget
    ring fixed s hn z hz hbudget

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree LDSinkBoundedKernel
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount)

/-!
Finite-horizon scan mass and joint retry potential machinery.

The scan absorption theorem is unconditional. The harmonic-mass
identity is conditional on an explicit local integer-valued
harmonic certificate, and the joint-budget induction is conditional
on an explicit node potential and its one-step drift inequality.
The omitted task is constructing those potentials from pPairAt,
harmonicPair and the physical first-cover/launch observer.
-/

/-- Reaching the absorbing observer boundary, whether it is
success or failure, has an expected cost at most n*(t-j). -/
theorem tolerant_scan_absorption_expected {n : Nat}
    (s : Fin n) (t : Nat) (htn : t ≤ n)
    (hn : 0 < n) (j : Nat) (A : List Nat) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (tolerantScanStep s t) (tolerantScanDone t)
      (.live j A) ((n * (t - j) : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (tolerantScanStep s t) (tolerantScanDone t)
    hn (.live j A) (n * (t - j))).2
  intro T
  exact tolerant_scan_stopping_cost s t htn j A T

/-- An exact finite-horizon tail estimate, for every live observer
state, including an arbitrary inherited once-prematurely-hit list. -/
theorem tolerant_scan_terminal_tail_mass {n : Nat}
    (s : Fin n) (t : Nat) (htn : t ≤ n)
    (j : Nat) (A : List Nat) (T : Nat) :
    T * UniformFirstHit.survivalNumerator
      (tolerantScanStep s t) (tolerantScanDone t)
      (.live j A) T ≤
    n ^ T * (n * (t - j)) := by
  calc
    T * UniformFirstHit.survivalNumerator
        (tolerantScanStep s t) (tolerantScanDone t)
        (.live j A) T ≤
      costNumerator (tolerantScanStep s t)
        (tolerantScanDone t) (.live j A) T :=
      UniformFirstHit.survival_mul_le_cost
        (tolerantScanStep s t) (tolerantScanDone t)
        (.live j A) T
    _ ≤ n ^ T * (n * (t - j)) :=
      tolerant_scan_stopping_cost s t htn j A T

theorem coupon_scheduleSum_add {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun w => f w + g w) =
      Prob.scheduleSum n T f + Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T
      (fun w => f w + g w) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (fun w => f w + g w),
    ← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_add _ _

/-- A one-step harmonic equality gives an EXACT identity over all
n^T scheduler words at every finite horizon. -/
theorem coupon_harmonic_word_mass
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (Φ : S → Nat)
    (hharm : ∀ x,
      (List.ofFn (fun e : Fin n => Φ (next x e))).sum =
        n * Φ x) :
    ∀ (x : S) (T : Nat),
      Prob.scheduleSum n T
          (fun w => Φ (LDSinkBoundedKernel.run next x w)) =
        n ^ T * Φ x := by
  intro x T
  induction T generalizing x with
  | zero =>
      rw [FreshFixed.sum_zero]
      simp [LDSinkBoundedKernel.run]
  | succ T ih =>
      rw [FreshFixed.sum_succ]
      calc
        (List.ofFn (fun e : Fin n =>
          Prob.scheduleSum n T
            (fun w => Φ (LDSinkBoundedKernel.run next x (e :: w))))).sum =
          (List.ofFn (fun e : Fin n =>
            n ^ T * Φ (next x e))).sum := by
              apply ofFn_sum_eq
              intro e
              simpa only [LDSinkBoundedKernel.run] using ih (next x e)
        _ = n ^ T *
              (List.ofFn (fun e : Fin n => Φ (next x e))).sum := by
                rw [ofFn_sum_mul_left]
        _ = n ^ T * (n * Φ x) := by rw [hharm x]
        _ = n ^ (T + 1) * Φ x := by
              rw [Nat.pow_succ]
              ac_rfl

def couponScanSuccessReward (t Q : Nat) :
    TolerantScanState → Nat
  | .failed => 0
  | .live j _ => if t ≤ j then Q else 0

def couponScanRunningReward (t : Nat)
    (Φ : TolerantScanState → Nat) :
    TolerantScanState → Nat
  | .failed => 0
  | .live j A => if t ≤ j then 0 else Φ (.live j A)

/-- Pointwise decomposition of a harmonic weight between the
successful boundary payoff and the still-running payoff. -/
theorem couponScanReward_partition (t Q : Nat)
    (Φ : TolerantScanState → Nat)
    (hfail : Φ .failed = 0)
    (hsuccess : ∀ j A, t ≤ j → Φ (.live j A) = Q) :
    ∀ x : TolerantScanState,
      couponScanSuccessReward t Q x +
        couponScanRunningReward t Φ x = Φ x := by
  intro x
  cases x with
  | failed =>
      simp [couponScanSuccessReward,
        couponScanRunningReward, hfail]
  | live j A =>
      by_cases hj : t ≤ j
      · simp [couponScanSuccessReward, couponScanRunningReward,
          hj, hsuccess j A hj]
      · simp [couponScanSuccessReward, couponScanRunningReward, hj]

theorem couponScanSuccessReward_eq (t Q : Nat)
    (x : TolerantScanState) :
    couponScanSuccessReward t Q x =
      Q * (if tolerantScanSuccess t x then 1 else 0) := by
  cases x with
  | failed =>
      simp [couponScanSuccessReward, tolerantScanSuccess]
  | live j A =>
      by_cases hj : t ≤ j
      · simp [couponScanSuccessReward, tolerantScanSuccess, hj]
      · simp [couponScanSuccessReward, tolerantScanSuccess, hj]

/-- The exact form required for scan success-count accounting:
Q*N_accepted(T) + N_running_weight(T) = Num*n^T.
The premise hharm is a genuine mathematical obligation; this
theorem does not assert it for the yet-to-be-built pPairAt
integer scaling. -/
theorem coupon_scan_mass_if_harmonic {n : Nat}
    (s : Fin n) (t Q Num j : Nat) (A : List Nat)
    (Φ : TolerantScanState → Nat)
    (hfail : Φ .failed = 0)
    (hsuccess : ∀ k B, t ≤ k → Φ (.live k B) = Q)
    (hharm : ∀ x,
      (List.ofFn (fun e : Fin n =>
        Φ (tolerantScanStep s t x e))).sum = n * Φ x)
    (hstart : Φ (.live j A) = Num) (T : Nat) :
    Q * Prob.scheduleSum n T
        (fun w =>
          if tolerantScanSuccess t
              (LDSinkBoundedKernel.run (tolerantScanStep s t)
                (.live j A) w)
          then 1 else 0) +
      Prob.scheduleSum n T
        (fun w =>
          couponScanRunningReward t Φ
            (LDSinkBoundedKernel.run (tolerantScanStep s t)
              (.live j A) w)) =
      n ^ T * Num := by
  let next := tolerantScanStep s t
  let start : TolerantScanState := .live j A
  have hpay (w : List (Fin n)) :
      couponScanSuccessReward t Q
          (LDSinkBoundedKernel.run next start w) =
        Q * (if tolerantScanSuccess t
          (LDSinkBoundedKernel.run next start w) then 1 else 0) :=
    couponScanSuccessReward_eq t Q _
  have hsum :
      Prob.scheduleSum n T
          (fun w =>
            couponScanSuccessReward t Q
              (LDSinkBoundedKernel.run next start w)) =
        Q * Prob.scheduleSum n T
          (fun w => if tolerantScanSuccess t
            (LDSinkBoundedKernel.run next start w) then 1 else 0) := by
    calc
      _ = Prob.scheduleSum n T
          (fun w => Q * (if tolerantScanSuccess t
            (LDSinkBoundedKernel.run next start w) then 1 else 0)) :=
        FreshFixed.sum_ext n T _ _ hpay
      _ = _ := FreshFixed.sum_mul_left n T Q _
  have hpartition (w : List (Fin n)) :
      couponScanSuccessReward t Q
          (LDSinkBoundedKernel.run next start w) +
        couponScanRunningReward t Φ
          (LDSinkBoundedKernel.run next start w) =
        Φ (LDSinkBoundedKernel.run next start w) :=
    couponScanReward_partition t Q Φ hfail hsuccess _
  calc
    Q * Prob.scheduleSum n T
          (fun w => if tolerantScanSuccess t
            (LDSinkBoundedKernel.run next start w) then 1 else 0) +
        Prob.scheduleSum n T
          (fun w => couponScanRunningReward t Φ
            (LDSinkBoundedKernel.run next start w)) =
      Prob.scheduleSum n T
          (fun w => couponScanSuccessReward t Q
            (LDSinkBoundedKernel.run next start w)) +
        Prob.scheduleSum n T
          (fun w => couponScanRunningReward t Φ
            (LDSinkBoundedKernel.run next start w)) := by
              rw [hsum]
    _ = Prob.scheduleSum n T
          (fun w =>
            couponScanSuccessReward t Q
              (LDSinkBoundedKernel.run next start w) +
            couponScanRunningReward t Φ
              (LDSinkBoundedKernel.run next start w)) :=
          (coupon_scheduleSum_add T _ _).symm
    _ = Prob.scheduleSum n T
          (fun w => Φ (LDSinkBoundedKernel.run next start w)) :=
        FreshFixed.sum_ext n T _ _ hpartition
    _ = n ^ T * Φ start :=
          coupon_harmonic_word_mass next Φ hharm start T
    _ = n ^ T * Num := by rw [hstart]

/-- State cost after one attempt: active Φ, retry P, success 0. -/
def couponAttemptNodeValue {A Seed : Type}
    (P : Nat) (Φ : A → Nat) :
    AttemptNode A Seed → Nat
  | .active a => Φ a
  | .success => 0
  | .retry _ => P

/-- Exact finite-horizon budget from ONE local node drift, by
induction on the remaining scheduler horizon. The refund for
retry is paid inside Φ rather than in a separate stage ceiling. -/
theorem coupon_attempt_budget_from_drift
    {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (D P : Nat) (Φ : A → Nat)
    (hdrift : ∀ a,
      D * n +
        (List.ofFn (fun e : Fin n =>
          couponAttemptNodeValue P Φ (K.step a e))).sum ≤
      n * Φ a) :
    ∀ (z : AttemptNode A Seed) (T : Nat),
      D * attemptCostNumerator K z T +
        P * retryCount K z T ≤
      n ^ T * couponAttemptNodeValue P Φ z := by
  intro z T
  induction T generalizing z with
  | zero =>
      cases z <;>
        simp [attemptCostNumerator, retryCount,
          couponAttemptNodeValue]
  | succ T ih =>
      cases z with
      | success =>
          simp [attemptCostNumerator, retryCount,
            couponAttemptNodeValue]
      | retry seed =>
          simp [attemptCostNumerator, retryCount,
            couponAttemptNodeValue, Nat.mul_comm]
      | active a =>
          change
            D * (n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  attemptCostNumerator K (K.step a e) T)).sum) +
              P * (List.ofFn (fun e : Fin n =>
                  retryCount K (K.step a e) T)).sum ≤
            n ^ (T + 1) * Φ a
          have hc (e : Fin n) :
              D * attemptCostNumerator K (K.step a e) T +
                P * retryCount K (K.step a e) T ≤
              n ^ T * couponAttemptNodeValue P Φ (K.step a e) :=
            ih (K.step a e)
          have hsum :
              (List.ofFn (fun e : Fin n =>
                D * attemptCostNumerator K (K.step a e) T +
                  P * retryCount K (K.step a e) T)).sum ≤
              n ^ T * (List.ofFn (fun e : Fin n =>
                couponAttemptNodeValue P Φ (K.step a e))).sum := by
            have hh := ofFn_sum_le _ _ hc
            simpa only [ofFn_sum_mul_left] using hh
          calc
            D * (n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  attemptCostNumerator K (K.step a e) T)).sum) +
              P * (List.ofFn (fun e : Fin n =>
                retryCount K (K.step a e) T)).sum =
              n ^ T * (D * n) +
                (List.ofFn (fun e : Fin n =>
                  D * attemptCostNumerator K (K.step a e) T +
                    P * retryCount K (K.step a e) T)).sum := by
                    simp only [Nat.mul_add, Nat.pow_succ,
                      ofFn_sum_mul_left, ofFn_sum_add]
                    ac_rfl
            _ ≤ n ^ T * (D * n) +
                n ^ T * (List.ofFn (fun e : Fin n =>
                  couponAttemptNodeValue P Φ (K.step a e))).sum :=
              Nat.add_le_add_left hsum _
            _ = n ^ T * (D * n +
                (List.ofFn (fun e : Fin n =>
                  couponAttemptNodeValue P Φ (K.step a e))).sum) := by
                    rw [Nat.mul_add]
            _ ≤ n ^ T * (n * Φ a) :=
              Nat.mul_le_mul_left _ (hdrift a)
            _ = n ^ (T + 1) * Φ a := by
              rw [Nat.pow_succ]
              ac_rfl

theorem coupon_joint_budget_of_node_potential
    {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (D P : Nat) (Φ : A → Nat)
    (hdrift : ∀ a,
      D * n +
        (List.ofFn (fun e : Fin n =>
          couponAttemptNodeValue P Φ (K.step a e))).sum ≤
      n * Φ a)
    (hstart : ∀ s, K.valid s → Φ (K.start s) ≤ P) :
    ∀ s, K.valid s → ∀ T,
      D * costNumerator (Prob.attemptStepper K)
          (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
          (.active (K.start s)) T +
        P * retryCount K (.active (K.start s)) T ≤
      n ^ T * P := by
  intro s hs T
  rw [Prob.attempt_costNumerator_eq]
  have h := coupon_attempt_budget_from_drift
    K D P Φ hdrift (.active (K.start s)) T
  exact Nat.le_trans h
    (Nat.mul_le_mul_left (n ^ T) (hstart s hs))

/-- Exact concrete hbudget transfer. No actual Φ is claimed here. -/
theorem couponJointBudget_of_potential {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (Φ : CouponSeed fixed × CouponAttemptPhase n → Nat)
    (hdrift : ∀ a,
      (couponGPair (compileAdvice q).t).2 * n +
        (List.ofFn (fun e : Fin n =>
          couponAttemptNodeValue
            (n * (couponGPair (compileAdvice q).t).1) Φ
            ((couponTrialKernel ring fixed s).step a e))).sum ≤
      n * Φ a)
    (hstart : ∀ seed : CouponSeed fixed,
      Φ ((couponTrialKernel ring fixed s).start seed) ≤
        n * (couponGPair (compileAdvice q).t).1) :
    CouponJointBudget ring fixed s := by
  intro seed T
  exact coupon_joint_budget_of_node_potential
    (couponTrialKernel ring fixed s)
    (couponGPair (compileAdvice q).t).2
    (n * (couponGPair (compileAdvice q).t).1)
    Φ hdrift
    (fun child _ => hstart child) seed (by trivial) T

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree LDSinkBoundedKernel

/-!
Common integer scale for the scan probability recursion.

Put F=t!. At fuel f the integer numerator below uses the single
denominator F^f. Its recurrence adds child numerators at a *shared*
scale, unlike the raw product denominators retained in pFuel.

The common level f=2*t+1 is sufficient for every futureUnhit state:
t-j+(futureUnhit t j A).length <= 2*t. A cross-product identity below
shows that this is exactly pPairAt, with no fraction reduction.

The remaining work is the transport of this unhit-language harmonic
equation to the literal tolerantScanStep over the original A list,
and the cover/launch/scan attempt-node potential.
-/

/-- Two integer numerators at a common scale add via pairAdd. -/
theorem coupon_scaled_pairAdd (Q : Nat)
    (a b : Nat × Nat) (u v : Nat)
    (ha : u * a.2 = Q * a.1)
    (hb : v * b.2 = Q * b.1) :
    (u + v) * (pairAdd a b).2 = Q * (pairAdd a b).1 := by
  change (u + v) * (a.2 * b.2) =
    Q * (a.1 * b.2 + b.1 * a.2)
  calc
    (u + v) * (a.2 * b.2) =
        (u * a.2) * b.2 + (v * b.2) * a.2 := by
      rw [Nat.add_mul]
      ac_rfl
    _ = (Q * a.1) * b.2 + (Q * b.1) * a.2 := by
      rw [ha, hb]
    _ = Q * (a.1 * b.2 + b.1 * a.2) := by
      rw [Nat.mul_add]
      ac_rfl

/-- The common scale is preserved through the exact pFuel fold. -/
theorem coupon_scaled_pairFold
    (Q : Nat) (f : Nat → Nat × Nat) (v : Nat → Nat) :
    ∀ (xs : List Nat) (a : Nat × Nat) (u : Nat),
      u * a.2 = Q * a.1 →
      (∀ k, k ∈ xs → v k * (f k).2 = Q * (f k).1) →
      (u + (xs.map v).sum) *
          ((xs.map f).foldl pairAdd a).2 =
        Q * ((xs.map f).foldl pairAdd a).1 := by
  intro xs
  induction xs with
  | nil =>
      intro a u ha _
      simpa only [List.map_nil, List.sum_nil, Nat.add_zero,
        List.foldl_nil] using ha
  | cons k ks ih =>
      intro a u ha hall
      have hhead := coupon_scaled_pairAdd Q a (f k) u (v k)
        ha (hall k (by simp))
      have htail (x : Nat) (hx : x ∈ ks) :
          v x * (f x).2 = Q * (f x).1 :=
        hall x (by simp [hx])
      have h := ih (pairAdd a (f k)) (u + v k) hhead htail
      simpa only [List.map_cons, List.sum_cons, List.foldl_cons,
        Nat.add_assoc] using h

/-- One common-denominator integer recursion over unhit future edges. -/
def couponScaledScanFuel : Nat → Nat → Nat → List Nat → Nat
  | 0, t, j, _ => if j < t then 0 else 1
  | fuel + 1, t, j, B =>
      if j < t then
        (freshFact t / (t - j)) *
          (couponScaledScanFuel fuel t (j + 1)
              (eraseAvailable (j + 1) B) +
            (B.map (fun k =>
              couponScaledScanFuel fuel t j
                (eraseAvailable k B))).sum)
      else (freshFact t) ^ (fuel + 1)

/-- Explicit successor equation; avoids relying on the equation
compiler's definitional unfolding through local aliases F and d. -/
theorem couponScaledScanFuel_succ (fuel t j : Nat)
    (B : List Nat) (hj : j < t) :
    couponScaledScanFuel (fuel + 1) t j B =
      (freshFact t / (t - j)) *
        (couponScaledScanFuel fuel t (j + 1)
            (eraseAvailable (j + 1) B) +
          (B.map (fun k =>
            couponScaledScanFuel fuel t j (eraseAvailable k B))).sum) := by
  simp only [couponScaledScanFuel, if_pos hj]

/-- Exact Nat cross-product correspondence to the original unreduced
pFuel pair. There is no assumption that its denominator individually
divides (t!)^fuel. -/
theorem coupon_scaledScanFuel_represents :
    ∀ (fuel t j : Nat) (B : List Nat),
      couponScaledScanFuel fuel t j B *
          (pFuel fuel t j B).2 =
        (pFuel fuel t j B).1 * (freshFact t) ^ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro t j B
      by_cases hj : j < t <;>
        simp [couponScaledScanFuel, pFuel, hj]
  | succ fuel ih =>
      intro t j B
      by_cases hj : j < t
      · let F := freshFact t
        let d := t - j
        let a := pFuel fuel t (j + 1)
          (eraseAvailable (j + 1) B)
        let f : Nat → Nat × Nat :=
          fun k => pFuel fuel t j (eraseAvailable k B)
        let u := couponScaledScanFuel fuel t (j + 1)
          (eraseAvailable (j + 1) B)
        let v : Nat → Nat :=
          fun k => couponScaledScanFuel fuel t j (eraseAvailable k B)
        let folded := (B.map f).foldl pairAdd a
        have hprogress : u * a.2 = F ^ fuel * a.1 := by
          calc
            u * a.2 = a.1 * F ^ fuel :=
              ih t (j + 1) (eraseAvailable (j + 1) B)
            _ = F ^ fuel * a.1 := Nat.mul_comm _ _
        have hchild (k : Nat) (hk : k ∈ B) :
            v k * (f k).2 = F ^ fuel * (f k).1 := by
          calc
            v k * (f k).2 = (f k).1 * F ^ fuel :=
              ih t j (eraseAvailable k B)
            _ = F ^ fuel * (f k).1 := Nat.mul_comm _ _
        have hf : (u + (B.map v).sum) * folded.2 =
            F ^ fuel * folded.1 :=
          coupon_scaled_pairFold (F ^ fuel) f v B a u
            hprogress hchild
        have hdiv : (F / d) * d = F := by
          dsimp only [F, d]
          exact Nat.div_mul_cancel
            (coupon_factorial_dvd t (t - j)
              (by omega) (by omega))
        rw [pFuel_first_step fuel t j B hj,
          couponScaledScanFuel_succ fuel t j B hj]
        change (F / d * (u + (B.map v).sum)) *
            (folded.2 * d) = folded.1 * F ^ (fuel + 1)
        calc
          (F / d * (u + (B.map v).sum)) * (folded.2 * d) =
              ((F / d) * d) *
                ((u + (B.map v).sum) * folded.2) := by ac_rfl
          _ = F * (F ^ fuel * folded.1) := by rw [hdiv, hf]
          _ = folded.1 * F ^ (fuel + 1) := by
            rw [Nat.pow_succ]
            ac_rfl
      · simp [couponScaledScanFuel, pFuel, hj]

theorem coupon_scaled_sum_map (Q : Nat) :
    ∀ xs : List Nat,
      (xs.map (fun k => Q * k)).sum = Q * xs.sum := by
  intro xs
  induction xs with
  | nil =>
      simp
  | cons k ks ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

/-- Increasing fuel after the measure has expired just multiplies
the common denominator and numerator by freshFact t. -/
theorem coupon_scaledScanFuel_stable :
    ∀ (fuel t j : Nat) (B : List Nat),
      t - j + B.length ≤ fuel →
      couponScaledScanFuel (fuel + 1) t j B =
        freshFact t * couponScaledScanFuel fuel t j B := by
  intro fuel
  induction fuel with
  | zero =>
      intro t j B h
      have hj : ¬ j < t := by omega
      simp [couponScaledScanFuel, hj]
  | succ fuel ih =>
      intro t j B h
      by_cases hj : j < t
      · let F := freshFact t
        let a := eraseAvailable (j + 1) B
        have haLen := eraseAvailable_length_le (j + 1) B
        have ha : couponScaledScanFuel (fuel + 1)
              t (j + 1) a =
            F * couponScaledScanFuel fuel t (j + 1) a :=
          ih t (j + 1) a (by dsimp only [a]; omega)
        have hb :
            B.map (fun k => couponScaledScanFuel (fuel + 1)
                t j (eraseAvailable k B)) =
            B.map (fun k => F * couponScaledScanFuel fuel
                t j (eraseAvailable k B)) := by
          apply List.map_congr_left
          intro k hk
          have hkLen := eraseAvailable_length_lt_of_mem k B hk
          exact ih t j (eraseAvailable k B) (by omega)
        have hc :
            (B.map (fun k => couponScaledScanFuel (fuel + 1)
                t j (eraseAvailable k B))).sum =
              F * (B.map (fun k => couponScaledScanFuel fuel
                t j (eraseAvailable k B))).sum := by
          rw [hb]
          simpa only [List.map_map, Function.comp_def] using
            (coupon_scaled_sum_map F
              (B.map (fun k => couponScaledScanFuel fuel
                t j (eraseAvailable k B))))
        rw [couponScaledScanFuel_succ (fuel + 1) t j B hj,
          couponScaledScanFuel_succ fuel t j B hj]
        rw [ha, hc, ← Nat.mul_add]
        ac_rfl
      · simp [couponScaledScanFuel, hj, Nat.pow_succ,
          Nat.mul_comm, Nat.mul_assoc]

theorem coupon_futureUnhit_length_le (t j : Nat) (A : List Nat) :
    (futureUnhit t j A).length ≤ t := by
  unfold futureUnhit
  exact Nat.le_trans
    (List.length_filter_le _ _) (by simp)

/-- Common fuel level f=2t+1 and one common integer denominator. -/
def couponScanIntegerDen (t : Nat) : Nat :=
  (freshFact t) ^ (2 * t + 1)

def couponScanIntegerNum (t j : Nat) (A : List Nat) : Nat :=
  couponScaledScanFuel (2 * t + 1) t j (futureUnhit t j A)

theorem couponScanIntegerDen_pos (t : Nat) :
    0 < couponScanIntegerDen t := by
  unfold couponScanIntegerDen
  exact Nat.pow_pos (coupon_factorial_pos t)

/-- For every j and A, including arbitrary duplicate, out-of-range
and stale entries, the integer numerator represents exactly pPairAt
at the universal denominator Q_t=(t!)^(2t+1). -/
theorem couponScanIntegerNum_represents (t j : Nat) (A : List Nat) :
    couponScanIntegerNum t j A * (pPairAt t j A).2 =
      (pPairAt t j A).1 * couponScanIntegerDen t := by
  let B := futureUnhit t j A
  have hlen : B.length ≤ t :=
    coupon_futureUnhit_length_le t j A
  have hfuel : t - j + B.length ≤ 2 * t + 1 := by omega
  have heq : pFuel (2 * t + 1) t j B =
      pFuel (t - j + B.length) t j B :=
    pFuel_stable (2 * t + 1) (t - j + B.length) t j B
      hfuel (Nat.le_refl _)
  change couponScaledScanFuel (2 * t + 1) t j B *
      (pFuel (t - j + B.length) t j B).2 =
    (pFuel (t - j + B.length) t j B).1 *
      (freshFact t) ^ (2 * t + 1)
  rw [← heq]
  exact coupon_scaledScanFuel_represents (2 * t + 1) t j B

theorem couponScanIntegerNum_terminal (t j : Nat) (A : List Nat)
    (hj : t ≤ j) :
    couponScanIntegerNum t j A = couponScanIntegerDen t := by
  have hnot : ¬ j < t := by omega
  change couponScaledScanFuel (2 * t + 1) t j
      (futureUnhit t j A) = (freshFact t) ^ (2 * t + 1)
  simp only [couponScaledScanFuel, if_neg hnot]

/-- The canonical unhit-list recursion satisfies an exact harmonic
first-step equation over a SINGLE common integer scale. This is
not yet the full Fin n summation for the tolerantScanStep(A) machine. -/
theorem couponScaledScanFuel_harmonicB (t j : Nat) (B : List Nat)
    (hj : j < t) (hB : B.length ≤ t) :
    (t - j) * couponScaledScanFuel (2 * t + 1) t j B =
      couponScaledScanFuel (2 * t + 1) t (j + 1)
          (eraseAvailable (j + 1) B) +
        (B.map (fun k => couponScaledScanFuel (2 * t + 1)
          t j (eraseAvailable k B))).sum := by
  let F := freshFact t
  let a := eraseAvailable (j + 1) B
  have haLen := eraseAvailable_length_le (j + 1) B
  have ha : couponScaledScanFuel (2 * t + 1) t (j + 1) a =
      F * couponScaledScanFuel (2 * t) t (j + 1) a :=
    coupon_scaledScanFuel_stable (2 * t) t (j + 1) a
      (by dsimp only [a]; omega)
  have hb :
      B.map (fun k => couponScaledScanFuel (2 * t + 1) t j
          (eraseAvailable k B)) =
      B.map (fun k => F * couponScaledScanFuel (2 * t) t j
          (eraseAvailable k B)) := by
    apply List.map_congr_left
    intro k hk
    have hkLen := eraseAvailable_length_lt_of_mem k B hk
    exact coupon_scaledScanFuel_stable (2 * t) t j
      (eraseAvailable k B) (by omega)
  have hc :
      (B.map (fun k => couponScaledScanFuel (2 * t + 1) t j
          (eraseAvailable k B))).sum =
      F * (B.map (fun k => couponScaledScanFuel (2 * t) t j
          (eraseAvailable k B))).sum := by
    rw [hb]
    simpa only [List.map_map, Function.comp_def] using
      (coupon_scaled_sum_map F (B.map (fun k =>
        couponScaledScanFuel (2 * t) t j (eraseAvailable k B))))
  have hdiv : (t - j) * (F / (t - j)) = F := by
    have hv := Nat.div_mul_cancel
      (coupon_factorial_dvd t (t - j) (by omega) (by omega))
    simpa only [Nat.mul_comm] using hv
  calc
    (t - j) * couponScaledScanFuel (2 * t + 1) t j B =
      (t - j) * (F / (t - j) *
        (couponScaledScanFuel (2 * t) t (j + 1) a +
          (B.map (fun k => couponScaledScanFuel (2 * t)
            t j (eraseAvailable k B))).sum)) := by
              rw [couponScaledScanFuel_succ (2 * t) t j B hj]
    _ = F * (couponScaledScanFuel (2 * t) t (j + 1) a +
          (B.map (fun k => couponScaledScanFuel (2 * t)
            t j (eraseAvailable k B))).sum) := by
              rw [← Nat.mul_assoc, hdiv]
    _ = F * couponScaledScanFuel (2 * t) t (j + 1) a +
          F * (B.map (fun k => couponScaledScanFuel (2 * t)
            t j (eraseAvailable k B))).sum := by
              rw [Nat.mul_add]
    _ = couponScaledScanFuel (2 * t + 1) t (j + 1) a +
          (B.map (fun k => couponScaledScanFuel (2 * t + 1)
            t j (eraseAvailable k B))).sum := by
              rw [ha, hc]

/-- Bounded finite-state summary of chronological last appearances
on the protected coupon set. The live attempt currently retains
the full word; the summary supplies the shorter automaton state
for its later conditional-last-order probability calculation. -/
def couponLastTouchStep {n : Nat}
    (r : Fin n → Bool) (last : List (Fin n)) (e : Fin n) :
    List (Fin n) :=
  if r e then (last.erase e) ++ [e] else last

def couponLastTouch {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n)) :
    List (Fin n) :=
  word.foldl (couponLastTouchStep r) []

theorem couponLastTouch_append {n : Nat}
    (r : Fin n → Bool) (word tail : List (Fin n)) :
    couponLastTouch r (word ++ tail) =
      tail.foldl (couponLastTouchStep r) (couponLastTouch r word) := by
  simp only [couponLastTouch, List.foldl_append]

theorem couponLastTouch_outside {n : Nat}
    (r : Fin n → Bool) (last : List (Fin n))
    (e : Fin n) (h : r e = false) :
    couponLastTouchStep r last e = last := by
  simp [couponLastTouchStep, h]


/-!
The literal scanner's physical edge cases, the
canonical future-unhit membership invariant, and the online
(mask, last-touch-order) cover automaton.

This supplies the pointwise bridge and bounded order state. The
remaining full Fin n harmonic summation and exact attempt-node
superharmonic potential are NOT asserted below.
-/

/-- Erasing k from the visited list preserves every other label. -/
theorem coupon_eraseAvailable_mem_ne (k x : Nat) (hne : x ≠ k) :
    ∀ A : List Nat, x ∈ eraseAvailable k A ↔ x ∈ A := by
  intro A
  induction A with
  | nil =>
      simp [eraseAvailable]
  | cons y ys ih =>
      by_cases hy : y = k
      · subst y
        simp [eraseAvailable, hne]
      · simp [eraseAvailable, hy, ih]

/-- Exact membership criterion of the canonical unhit list. -/
theorem coupon_futureUnhit_mem (t j : Nat) (A : List Nat)
    (x : Nat) :
    x ∈ futureUnhit t j A ↔
      j < x ∧ x < t ∧ x ∉ A := by
  simp only [futureUnhit, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h.2.1, h.1, h.2.2⟩
  · intro h
    exact ⟨h.2.1, ⟨h.1, h.2.2⟩⟩

/-- First premature hit: only the newly observed k is removed
from the canonical future-unhit set. Arbitrary duplicate scratch
in A is allowed. -/
theorem coupon_futureUnhit_first_mem
    (t j : Nat) (A : List Nat) (k x : Nat) :
    x ∈ futureUnhit t j (k :: A) ↔
      x ∈ futureUnhit t j A ∧ x ≠ k := by
  constructor
  · intro h
    obtain ⟨hjx, hxt, hna⟩ :=
      (coupon_futureUnhit_mem t j (k :: A) x).mp h
    have hne : x ≠ k := by
      intro he
      apply hna
      simp [he]
    have ha : x ∉ A := by
      intro hm
      exact hna (List.mem_cons.mpr (Or.inr hm))
    exact ⟨(coupon_futureUnhit_mem t j A x).mpr
      ⟨hjx, hxt, ha⟩, hne⟩
  · rintro ⟨h, hne⟩
    obtain ⟨hjx, hxt, hna⟩ :=
      (coupon_futureUnhit_mem t j A x).mp h
    apply (coupon_futureUnhit_mem t j (k :: A) x).mpr
    refine ⟨hjx, hxt, ?_⟩
    intro hm
    rcases List.mem_cons.mp hm with he | ht
    · exact hne he
    · exact hna ht

/-- A current-edge progress step discards the j+1 boundary label
but changes no other future-unhit membership. -/
theorem coupon_futureUnhit_progress_mem
    (t j : Nat) (A : List Nat) (x : Nat) :
    x ∈ futureUnhit t (j + 1)
        (eraseAvailable (j + 1) A) ↔
      x ∈ futureUnhit t j A ∧ x ≠ j + 1 := by
  constructor
  · intro h
    obtain ⟨hstep, hxt, hna⟩ :=
      (coupon_futureUnhit_mem t (j + 1)
        (eraseAvailable (j + 1) A) x).mp h
    have hne : x ≠ j + 1 := by omega
    have ha : x ∉ A := by
      intro hm
      apply hna
      exact (coupon_eraseAvailable_mem_ne
        (j + 1) x hne A).mpr hm
    exact ⟨(coupon_futureUnhit_mem t j A x).mpr
      ⟨by omega, hxt, ha⟩, hne⟩
  · rintro ⟨h, hne⟩
    obtain ⟨hjx, hxt, hna⟩ :=
      (coupon_futureUnhit_mem t j A x).mp h
    apply (coupon_futureUnhit_mem t (j + 1)
      (eraseAvailable (j + 1) A) x).mpr
    refine ⟨by omega, hxt, ?_⟩
    intro hm
    apply hna
    exact (coupon_eraseAvailable_mem_ne
      (j + 1) x hne A).mp hm

/-- A physical selection of the next required scan edge advances j. -/
theorem coupon_scan_progress_edge {n : Nat}
    (s : Fin n) (t j : Nat) (A : List Nat)
    (hjt : j < t) (hjn : j < n) :
    tolerantScanStep s t (.live j A) (certSite s j) =
      .live (j + 1) (eraseAvailable (j + 1) A) := by
  have hnot : ¬ t ≤ j := by omega
  have he := tolerant_unrotate_site s j hjn
  simp [tolerantScanStep, hnot, he]

/-- A first premature future hit records k exactly once. -/
theorem coupon_scan_first_edge {n : Nat}
    (s : Fin n) (t j k : Nat) (A : List Nat)
    (hjk : j < k) (hkt : k < t)
    (hkn : k < n) (hnot : k ∉ A) :
    tolerantScanStep s t (.live j A) (certSite s k) =
      .live j (k :: A) := by
  have hdone : ¬ t ≤ j := by omega
  have he := tolerant_unrotate_site s k hkn
  have hne : k ≠ j := by omega
  have hf : j < k ∧ k < t := ⟨hjk, hkt⟩
  simp [tolerantScanStep, hdone, he, hne, hf, hnot]

/-- A second premature hit is the actual absorbing failure branch. -/
theorem coupon_scan_second_edge {n : Nat}
    (s : Fin n) (t j k : Nat) (A : List Nat)
    (hjk : j < k) (hkt : k < t)
    (hkn : k < n) (hhit : k ∈ A) :
    tolerantScanStep s t (.live j A) (certSite s k) =
      .failed := by
  have he := tolerant_unrotate_site s k hkn
  exact tolerant_second_hit_failure s t j A (certSite s k)
    (by simpa only [he] using (show j < k ∧ k < t from
      ⟨hjk, hkt⟩))
    (by simpa only [he] using hhit)

/-- Behind and beyond-terminal edges are genuine observer self-loops. -/
theorem coupon_scan_outside_edge {n : Nat}
    (s : Fin n) (t j k : Nat) (A : List Nat)
    (hjt : j < t) (hkn : k < n)
    (hout : k < j ∨ t ≤ k) :
    tolerantScanStep s t (.live j A) (certSite s k) =
      .live j A := by
  have hdone : ¬ t ≤ j := by omega
  have he := tolerant_unrotate_site s k hkn
  have hne : k ≠ j := by omega
  have hf : ¬ (j < k ∧ k < t) := by omega
  simp [tolerantScanStep, hdone, he, hne, hf]

/-- An online two-register coupon observer: remaining mask and
last-touch chronological order. This proof object has no effect
on the physical protocol state. -/
def couponCoverOrderStep {n : Nat}
    (r : Fin n → Bool)
    (a : (Fin n → Bool) × List (Fin n))
    (e : Fin n) : (Fin n → Bool) × List (Fin n) :=
  (maskDrop a.1 e, couponLastTouchStep r a.2 e)

/-- It follows the exact original physical word, not a restarted
or deterministically padded artificial schedule. -/
theorem couponCoverOrder_run {n : Nat}
    (r : Fin n → Bool) :
    ∀ (a : (Fin n → Bool) × List (Fin n))
      (word : List (Fin n)),
      LDSinkBoundedKernel.run (couponCoverOrderStep r) a word =
        (word.foldl maskDrop a.1,
          word.foldl (couponLastTouchStep r) a.2) := by
  intro a word
  induction word generalizing a with
  | nil =>
      rfl
  | cons e word ih =>
      change
        LDSinkBoundedKernel.run (couponCoverOrderStep r)
          (couponCoverOrderStep r a e) word =
        (word.foldl maskDrop (maskDrop a.1 e),
          word.foldl (couponLastTouchStep r)
            (couponLastTouchStep r a.2 e))
      exact ih (couponCoverOrderStep r a e)

/-- The last-touch register is precisely the canonical last-order
summary of the chronological first-cover prefix. -/
theorem couponCoverOrder_run_initial {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n)) :
    LDSinkBoundedKernel.run (couponCoverOrderStep r)
        (r, []) word =
      (word.foldl maskDrop r, couponLastTouch r word) := by
  exact couponCoverOrder_run r (r, []) word

theorem couponLastTouch_snoc {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n)) (e : Fin n) :
    couponLastTouch r (word ++ [e]) =
      couponLastTouchStep r (couponLastTouch r word) e := by
  rw [couponLastTouch_append]
  rfl

/-- In the common L^2 numerator scale, the exact stopped launch
allowance n*(L+1) leaves n*(L-1) slack below 2*n*L. -/
theorem coupon_launch_slack_numerators (n L : Nat) (hL : 0 < L) :
    n * (L + 1) + n * (L - 1) = 2 * n * L := by
  have hs : (L + 1) + (L - 1) = 2 * L := by omega
  calc
    n * (L + 1) + n * (L - 1) =
      n * ((L + 1) + (L - 1)) := (Nat.mul_add _ _ _).symm
    _ = n * (2 * L) := by rw [hs]
    _ = 2 * n * L := by ac_rfl


/-!
Permutation invariance for the
common-denominator scanner, transport through canonical future-unhit
sets, and the resulting original-A first-step equation.

The full rotated Fin n edge sum is not claimed here.
-/

/-- Our first-occurrence eraser is the core List.erase on Nat. -/
theorem coupon_eraseAvailable_eq_erase (k : Nat) :
    ∀ B : List Nat, eraseAvailable k B = B.erase k := by
  intro B
  induction B with
  | nil =>
      rfl
  | cons x xs ih =>
      by_cases hx : x = k
      · subst x
        simp [eraseAvailable]
      · have hb : ¬ (x == k) := by
          simpa only [beq_iff_eq] using hx
        rw [List.erase_cons_tail hb]
        simp only [eraseAvailable, if_neg hx, ih]

/-- Deletion is invariant under any reordering, even with duplicates. -/
theorem coupon_eraseAvailable_perm (k : Nat)
    {B C : List Nat} (hp : List.Perm B C) :
    List.Perm (eraseAvailable k B) (eraseAvailable k C) := by
  rw [coupon_eraseAvailable_eq_erase k B,
    coupon_eraseAvailable_eq_erase k C]
  exact hp.erase k

/-- Exact common-scale scan numerators are independent of the order
of the unhit list, for every finite fuel and arbitrary duplicate data. -/
theorem coupon_scaledScanFuel_perm :
    ∀ (fuel t j : Nat) {B C : List Nat},
      List.Perm B C →
      couponScaledScanFuel fuel t j B =
        couponScaledScanFuel fuel t j C := by
  intro fuel
  induction fuel with
  | zero =>
      intro t j B C _
      simp [couponScaledScanFuel]
  | succ fuel ih =>
      intro t j B C hp
      by_cases hj : j < t
      · have hprogress :
            couponScaledScanFuel fuel t (j + 1)
                (eraseAvailable (j + 1) B) =
              couponScaledScanFuel fuel t (j + 1)
                (eraseAvailable (j + 1) C) :=
          ih t (j + 1) (coupon_eraseAvailable_perm (j + 1) hp)
        have hmap :
            B.map (fun k => couponScaledScanFuel fuel t j
                (eraseAvailable k B)) =
              B.map (fun k => couponScaledScanFuel fuel t j
                (eraseAvailable k C)) := by
          apply List.map_congr_left
          intro k hk
          exact ih t j (coupon_eraseAvailable_perm k hp)
        have hsum :
            (B.map (fun k => couponScaledScanFuel fuel t j
                (eraseAvailable k B))).sum =
              (C.map (fun k => couponScaledScanFuel fuel t j
                (eraseAvailable k C))).sum := by
          rw [hmap]
          exact (hp.map (fun k => couponScaledScanFuel fuel t j
            (eraseAvailable k C))).sum_nat
        rw [couponScaledScanFuel_succ fuel t j B hj,
          couponScaledScanFuel_succ fuel t j C hj,
          hprogress, hsum]
      · simp [couponScaledScanFuel, hj]

/-- On duplicate-free unhit sets, extensional equality suffices. -/
theorem coupon_scaledScanFuel_ext
    (fuel t j : Nat) (B C : List Nat)
    (hB : B.Nodup) (hC : C.Nodup)
    (hmem : ∀ k, k ∈ B ↔ k ∈ C) :
    couponScaledScanFuel fuel t j B =
      couponScaledScanFuel fuel t j C := by
  exact coupon_scaledScanFuel_perm fuel t j
    ((List.perm_ext_iff_of_nodup hB hC).mpr hmem)

/-- The canonical future-unhit filter has no repeated labels. -/
theorem coupon_futureUnhit_nodup (t j : Nat) (A : List Nat) :
    (futureUnhit t j A).Nodup := by
  unfold futureUnhit
  exact List.Nodup.sublist List.filter_sublist
    (List.nodup_range (n := t))

theorem coupon_eraseAvailable_nodup (k : Nat)
    (B : List Nat) (hB : B.Nodup) :
    (eraseAvailable k B).Nodup := by
  rw [coupon_eraseAvailable_eq_erase k B]
  exact hB.erase k

/-- For a duplicate-free list, one deletion removes precisely k. -/
theorem coupon_eraseAvailable_mem_nodup
    (k x : Nat) (B : List Nat) (hB : B.Nodup) :
    x ∈ eraseAvailable k B ↔ x ∈ B ∧ x ≠ k := by
  rw [coupon_eraseAvailable_eq_erase k B]
  have hm : x ∈ B.erase k ↔ x ≠ k ∧ x ∈ B :=
    hB.mem_erase_iff
  exact hm.trans and_comm

/-- The current-progress list is a permutation of erasing the
boundary label from the prior canonical unhit list. -/
theorem coupon_futureUnhit_progress_perm
    (t j : Nat) (A : List Nat) :
    List.Perm
      (futureUnhit t (j + 1) (eraseAvailable (j + 1) A))
      (eraseAvailable (j + 1) (futureUnhit t j A)) := by
  let B := futureUnhit t j A
  have hB : B.Nodup := coupon_futureUnhit_nodup t j A
  apply (List.perm_ext_iff_of_nodup
    (coupon_futureUnhit_nodup t (j + 1)
      (eraseAvailable (j + 1) A))
    (coupon_eraseAvailable_nodup (j + 1) B hB)).mpr
  intro x
  calc
    x ∈ futureUnhit t (j + 1) (eraseAvailable (j + 1) A) ↔
        x ∈ B ∧ x ≠ j + 1 :=
      coupon_futureUnhit_progress_mem t j A x
    _ ↔ x ∈ eraseAvailable (j + 1) B :=
      (coupon_eraseAvailable_mem_nodup (j + 1) x B hB).symm

/-- A first future observation corresponds to deleting that
label from the canonical unhit list. -/
theorem coupon_futureUnhit_first_perm
    (t j : Nat) (A : List Nat) (k : Nat) :
    List.Perm (futureUnhit t j (k :: A))
      (eraseAvailable k (futureUnhit t j A)) := by
  let B := futureUnhit t j A
  have hB : B.Nodup := coupon_futureUnhit_nodup t j A
  apply (List.perm_ext_iff_of_nodup
    (coupon_futureUnhit_nodup t j (k :: A))
    (coupon_eraseAvailable_nodup k B hB)).mpr
  intro x
  calc
    x ∈ futureUnhit t j (k :: A) ↔
        x ∈ B ∧ x ≠ k :=
      coupon_futureUnhit_first_mem t j A k x
    _ ↔ x ∈ eraseAvailable k B :=
      (coupon_eraseAvailable_mem_nodup k x B hB).symm

/-- The common integer numerator transports the actual progress
update into the unhit-list recurrence. -/
theorem couponScanIntegerNum_progress
    (t j : Nat) (A : List Nat) :
    couponScanIntegerNum t (j + 1)
        (eraseAvailable (j + 1) A) =
      couponScaledScanFuel (2 * t + 1) t (j + 1)
        (eraseAvailable (j + 1) (futureUnhit t j A)) := by
  change couponScaledScanFuel (2 * t + 1) t (j + 1)
      (futureUnhit t (j + 1) (eraseAvailable (j + 1) A)) =
    couponScaledScanFuel (2 * t + 1) t (j + 1)
      (eraseAvailable (j + 1) (futureUnhit t j A))
  exact coupon_scaledScanFuel_perm (2 * t + 1) t (j + 1)
    (coupon_futureUnhit_progress_perm t j A)

/-- Likewise for an actual first premature hit, for arbitrary A. -/
theorem couponScanIntegerNum_first
    (t j : Nat) (A : List Nat) (k : Nat) :
    couponScanIntegerNum t j (k :: A) =
      couponScaledScanFuel (2 * t + 1) t j
        (eraseAvailable k (futureUnhit t j A)) := by
  change couponScaledScanFuel (2 * t + 1) t j
      (futureUnhit t j (k :: A)) =
    couponScaledScanFuel (2 * t + 1) t j
      (eraseAvailable k (futureUnhit t j A))
  exact coupon_scaledScanFuel_perm (2 * t + 1) t j
    (coupon_futureUnhit_first_perm t j A k)

/-- The ORIGINAL visited-list machine inherits the common-integer
first-step equation. The sum is over strictly future unhit labels;
the remaining physical edge multiplicities are not included yet. -/
theorem couponScanIntegerNum_harmonicA
    (t j : Nat) (A : List Nat) (hj : j < t) :
    (t - j) * couponScanIntegerNum t j A =
      couponScanIntegerNum t (j + 1)
          (eraseAvailable (j + 1) A) +
        ((futureUnhit t j A).map (fun k =>
          couponScanIntegerNum t j (k :: A))).sum := by
  let B := futureUnhit t j A
  have hBlen : B.length ≤ t :=
    coupon_futureUnhit_length_le t j A
  have hfirst :
      (B.map (fun k => couponScanIntegerNum t j (k :: A))).sum =
        (B.map (fun k => couponScaledScanFuel (2 * t + 1)
          t j (eraseAvailable k B))).sum := by
    have hmap :
        B.map (fun k => couponScanIntegerNum t j (k :: A)) =
          B.map (fun k => couponScaledScanFuel (2 * t + 1)
            t j (eraseAvailable k B)) := by
      apply List.map_congr_left
      intro k hk
      exact couponScanIntegerNum_first t j A k
    exact congrArg List.sum hmap
  change (t - j) * couponScaledScanFuel (2 * t + 1) t j B =
    couponScanIntegerNum t (j + 1) (eraseAvailable (j + 1) A) +
      (B.map (fun k => couponScanIntegerNum t j (k :: A))).sum
  rw [couponScanIntegerNum_progress t j A, hfirst]
  exact couponScaledScanFuel_harmonicB t j B hj hBlen

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree LDSinkBoundedKernel

/-!
The finite rotated-edge
partition for the original tolerantScanStep, its common-scale
harmonic identity, and the finite-horizon p_scan mass equation.
-/

/-- Counting a rotated initial segment uses the already proved
inverse rotation and relabeled canonical-mask cardinality. -/
theorem coupon_scan_prefix_count {n : Nat}
    (s : Fin n) (k : Nat) (hk : k ≤ n) :
    (List.ofFn (fun e : Fin n =>
      if (unrotate s e).val < k then 1 else 0)).sum = k := by
  simpa only [FreshCoupon.maskSize, FreshCoupon.canonicalMask,
    decide_eq_true_eq] using
    (FreshCoupon.relabeled_mask_size
      (rotate s) (unrotate s)
      (unrotate_rotate s) (rotate_unrotate s) k hk)

/-- There are j already-behind labels and n-t outside labels.
Their total is n-(t-j), independent of the rotated anchor. -/
theorem coupon_scan_harmless_count {n : Nat}
    (s : Fin n) (t j : Nat)
    (htn : t ≤ n) (hjt : j < t) :
    (List.ofFn (fun e : Fin n =>
      if (unrotate s e).val < j ∨
          t ≤ (unrotate s e).val then 1 else 0)).sum =
      n - (t - j) := by
  have hjn : j ≤ n := by omega
  have hpj := coupon_scan_prefix_count s j hjn
  have hpt := coupon_scan_prefix_count s t htn
  have hmid :
      (List.ofFn (fun e : Fin n =>
        if j ≤ (unrotate s e).val ∧
            (unrotate s e).val < t then 1 else 0)).sum =
        t - j := by
    have hrow (e : Fin n) :
        (if (unrotate s e).val < j then 1 else 0) +
          (if j ≤ (unrotate s e).val ∧
              (unrotate s e).val < t then 1 else 0) =
          (if (unrotate s e).val < t then 1 else 0) := by
      by_cases hlow : (unrotate s e).val < j
      · have hm : ¬ (j ≤ (unrotate s e).val ∧
            (unrotate s e).val < t) := by omega
        have ht : (unrotate s e).val < t := by omega
        simp [hlow, hm, ht]
      · by_cases ht : (unrotate s e).val < t
        · have hm : j ≤ (unrotate s e).val ∧
              (unrotate s e).val < t := by omega
          simp [hlow, hm, ht]
        · have hm : ¬ (j ≤ (unrotate s e).val ∧
              (unrotate s e).val < t) := by omega
          simp [hlow, hm, ht]
    have hs := ofFn_sum_eq
      (fun e : Fin n =>
        (if (unrotate s e).val < j then 1 else 0) +
          (if j ≤ (unrotate s e).val ∧
            (unrotate s e).val < t then 1 else 0))
      (fun e : Fin n =>
        if (unrotate s e).val < t then 1 else 0)
      hrow
    rw [ofFn_sum_add, hpj, hpt] at hs
    omega
  have htotal :
      (List.ofFn (fun e : Fin n =>
        if (unrotate s e).val < j ∨
            t ≤ (unrotate s e).val then 1 else 0)).sum +
      (List.ofFn (fun e : Fin n =>
        if j ≤ (unrotate s e).val ∧
            (unrotate s e).val < t then 1 else 0)).sum =
        n := by
    have hrow (e : Fin n) :
        (if (unrotate s e).val < j ∨
            t ≤ (unrotate s e).val then 1 else 0) +
        (if j ≤ (unrotate s e).val ∧
            (unrotate s e).val < t then 1 else 0) = 1 := by
      by_cases hm : j ≤ (unrotate s e).val ∧
          (unrotate s e).val < t
      · have ho : ¬ ((unrotate s e).val < j ∨
            t ≤ (unrotate s e).val) := by omega
        simp [hm, ho]
      · have ho : (unrotate s e).val < j ∨
            t ≤ (unrotate s e).val := by omega
        simp [hm, ho]
    have hs := ofFn_sum_eq
      (fun e : Fin n =>
        (if (unrotate s e).val < j ∨
            t ≤ (unrotate s e).val then 1 else 0) +
        (if j ≤ (unrotate s e).val ∧
            (unrotate s e).val < t then 1 else 0))
      (fun _ : Fin n => 1) hrow
    rw [ofFn_sum_add, ofFn_sum_const, hmid] at hs
    rw [hmid]
    simpa only [Nat.mul_one] using hs
  omega

/-- A Nodup list has at most one contribution at a selected key. -/
theorem coupon_scan_select_sum :
    ∀ (B : List Nat), B.Nodup →
      ∀ (v : Nat → Nat) (k : Nat),
        (B.map (fun b => if k = b then v b else 0)).sum =
          if k ∈ B then v k else 0 := by
  intro B
  induction B with
  | nil =>
      intro _ v k
      simp
  | cons b bs ih =>
      intro hB v k
      have hnot : b ∉ bs := (List.nodup_cons.mp hB).1
      have htail : bs.Nodup := (List.nodup_cons.mp hB).2
      by_cases hk : k = b
      · subst k
        simp only [List.map_cons, List.sum_cons]
        rw [ih htail v b]
        simp [hnot]
      · simp only [List.map_cons, List.sum_cons]
        rw [if_neg hk, Nat.zero_add, ih htail v k]
        have hmem : (k ∈ b :: bs) ↔ (k ∈ bs) := by
          constructor
          · intro hm
            rcases List.mem_cons.mp hm with hb | ht
            · exact False.elim (hk hb)
            · exact ht
          · intro ht
            exact List.mem_cons.mpr (Or.inr ht)
        simp only [hmem]

/-- The rotated inverse image of a physical label is a singleton. -/
theorem coupon_scan_unrotated_spike {n : Nat}
    (s : Fin n) (k : Nat) (hk : k < n) (v : Nat) :
    (List.ofFn (fun e : Fin n =>
      if (unrotate s e).val = k then v else 0)).sum = v := by
  have hequiv (e : Fin n) :
      ((unrotate s e).val = k) ↔
        e = certSite s k := by
    constructor
    · intro hh
      have he : unrotate s e = (⟨k, hk⟩ : Fin n) := Fin.ext hh
      calc
        e = rotate s (unrotate s e) :=
          (rotate_unrotate s e).symm
        _ = rotate s (⟨k, hk⟩ : Fin n) := by rw [he]
        _ = certSite s k := rfl
    · intro he
      rw [he]
      exact tolerant_unrotate_site s k hk
  calc
    (List.ofFn (fun e : Fin n =>
        if (unrotate s e).val = k then v else 0)).sum =
      (List.ofFn (fun e : Fin n =>
        if e = certSite s k then v else 0)).sum := by
          apply ofFn_sum_eq
          intro e
          simp only [hequiv e]
    _ = v := FreshFixed.sum_spike n (certSite s k) v

/-- Sum of a list of singleton rotated spikes. No Nodup premise
is needed for this additive identity. -/
theorem coupon_scan_sum_spikes {n : Nat}
    (s : Fin n) (v : Nat → Nat) :
    ∀ B : List Nat, (∀ k, k ∈ B → k < n) →
      (List.ofFn (fun e : Fin n =>
        (B.map (fun k =>
          if (unrotate s e).val = k then v k else 0)).sum)).sum =
        (B.map v).sum := by
  intro B
  induction B with
  | nil =>
      intro _
      simp [ofFn_sum_const]
  | cons b bs ih =>
      intro hbound
      have hb : b < n := hbound b (by simp)
      have htail : ∀ k, k ∈ bs → k < n := by
        intro k hk
        exact hbound k (List.mem_cons.mpr (Or.inr hk))
      change
        (List.ofFn (fun e : Fin n =>
          (if (unrotate s e).val = b then v b else 0) +
            (bs.map (fun k =>
              if (unrotate s e).val = k then v k else 0)).sum)).sum =
          v b + (bs.map v).sum
      rw [ofFn_sum_add,
        coupon_scan_unrotated_spike s b hb (v b), ih htail]

/-- Unhit-list sum equals the physical sum of first-hit payoffs. -/
theorem coupon_scan_sum_future {n : Nat}
    (s : Fin n) (B : List Nat)
    (hB : B.Nodup)
    (hbound : ∀ k, k ∈ B → k < n)
    (v : Nat → Nat) :
    (List.ofFn (fun e : Fin n =>
      if (unrotate s e).val ∈ B then
        v (unrotate s e).val else 0)).sum =
      (B.map v).sum := by
  have hrow (e : Fin n) :
      (if (unrotate s e).val ∈ B then
        v (unrotate s e).val else 0) =
      (B.map (fun k =>
        if (unrotate s e).val = k then v k else 0)).sum :=
    (coupon_scan_select_sum B hB v (unrotate s e).val).symm
  calc
    _ = (List.ofFn (fun e : Fin n =>
      (B.map (fun k =>
        if (unrotate s e).val = k then v k else 0)).sum)).sum :=
      ofFn_sum_eq _ _ hrow
    _ = (B.map v).sum :=
      coupon_scan_sum_spikes s v B hbound

/-- The common-scale value on the literal paper scanner. -/
def couponScanIntegerWeight (t : Nat) :
    TolerantScanState → Nat
  | .failed => 0
  | .live j A => couponScanIntegerNum t j A

/-- Physical edge classification, before taking any finite sum. -/
theorem coupon_scan_live_row {n : Nat}
    (s : Fin n) (t j : Nat) (A : List Nat)
    (hj : j < t) (e : Fin n) :
    couponScanIntegerWeight t
        (tolerantScanStep s t (.live j A) e) =
      (if (unrotate s e).val < j ∨
          t ≤ (unrotate s e).val
       then couponScanIntegerNum t j A else 0) +
      (if (unrotate s e).val = j
       then couponScanIntegerNum t (j + 1)
          (eraseAvailable (j + 1) A) else 0) +
      (if (unrotate s e).val ∈ futureUnhit t j A
       then couponScanIntegerNum t j ((unrotate s e).val :: A)
       else 0) := by
  have hdone : ¬ t ≤ j := by omega
  by_cases he : (unrotate s e).val = j
  · have ho : ¬ ((unrotate s e).val < j ∨
        t ≤ (unrotate s e).val) := by omega
    have hb : (unrotate s e).val ∉ futureUnhit t j A := by
      intro hm
      have hh := (coupon_futureUnhit_mem t j A _).mp hm
      omega
    have hbj : j ∉ futureUnhit t j A := he ▸ hb
    simp [couponScanIntegerWeight, tolerantScanStep,
      hdone, he, ho, hb, hbj]
  · by_cases hf : j < (unrotate s e).val ∧
        (unrotate s e).val < t
    · have ho : ¬ ((unrotate s e).val < j ∨
          t ≤ (unrotate s e).val) := by omega
      by_cases ha : (unrotate s e).val ∈ A
      · have hb :
            (unrotate s e).val ∉ futureUnhit t j A := by
          intro hm
          exact ((coupon_futureUnhit_mem t j A _).mp hm).2.2 ha
        simp [couponScanIntegerWeight, tolerantScanStep,
          hdone, he, hf, ha, ho, hb]
      · have hb :
            (unrotate s e).val ∈ futureUnhit t j A :=
          (coupon_futureUnhit_mem t j A _).mpr
            ⟨hf.1, hf.2, ha⟩
        simp [couponScanIntegerWeight, tolerantScanStep,
          hdone, he, hf, ha, ho, hb]
    · have ho : (unrotate s e).val < j ∨
          t ≤ (unrotate s e).val := by omega
      have hb :
          (unrotate s e).val ∉ futureUnhit t j A := by
        intro hm
        have hh := (coupon_futureUnhit_mem t j A _).mp hm
        exact hf ⟨hh.1, hh.2.1⟩
      simp [couponScanIntegerWeight, tolerantScanStep,
        hdone, he, hf, ho, hb]

/-- Exact required Fin n edge sum, in ORIGINAL once-hit-list
coordinates. Failed future repeats have weight zero. -/
theorem coupon_scan_rotated_edge_sum {n : Nat}
    (s : Fin n) (t j : Nat) (A : List Nat)
    (htn : t ≤ n) (hj : j < t) :
    (List.ofFn (fun e : Fin n =>
      couponScanIntegerWeight t
        (tolerantScanStep s t (.live j A) e))).sum =
      (n - (t - j)) * couponScanIntegerNum t j A +
      couponScanIntegerNum t (j + 1)
        (eraseAvailable (j + 1) A) +
      ((futureUnhit t j A).map (fun k =>
        couponScanIntegerNum t j (k :: A))).sum := by
  have hbound : ∀ k, k ∈ futureUnhit t j A → k < n := by
    intro k hk
    have hh := (coupon_futureUnhit_mem t j A k).mp hk
    omega
  have hmask :
      FreshCoupon.maskSize (fun e : Fin n =>
        decide ((unrotate s e).val < j ∨
          t ≤ (unrotate s e).val)) =
        n - (t - j) := by
    simpa only [FreshCoupon.maskSize, decide_eq_true_eq] using
      (coupon_scan_harmless_count s t j htn hj)
  have hout :
      (List.ofFn (fun e : Fin n =>
        if (unrotate s e).val < j ∨
            t ≤ (unrotate s e).val then
          couponScanIntegerNum t j A else 0)).sum =
        (n - (t - j)) * couponScanIntegerNum t j A := by
    calc
      _ = FreshCoupon.maskSize (fun e : Fin n =>
          decide ((unrotate s e).val < j ∨
            t ≤ (unrotate s e).val)) *
          couponScanIntegerNum t j A := by
            simpa only [decide_eq_true_eq] using
              (FreshFixed.sum_mask n
                (fun e : Fin n =>
                  decide ((unrotate s e).val < j ∨
                    t ≤ (unrotate s e).val))
                (couponScanIntegerNum t j A))
      _ = _ := by rw [hmask]
  have hjn : j < n := by omega
  have hprogress :
      (List.ofFn (fun e : Fin n =>
        if (unrotate s e).val = j then
          couponScanIntegerNum t (j + 1)
            (eraseAvailable (j + 1) A) else 0)).sum =
        couponScanIntegerNum t (j + 1)
          (eraseAvailable (j + 1) A) :=
    coupon_scan_unrotated_spike s j hjn
      (couponScanIntegerNum t (j + 1)
        (eraseAvailable (j + 1) A))
  have hfirst :
      (List.ofFn (fun e : Fin n =>
        if (unrotate s e).val ∈ futureUnhit t j A then
          couponScanIntegerNum t j ((unrotate s e).val :: A)
        else 0)).sum =
      ((futureUnhit t j A).map (fun k =>
        couponScanIntegerNum t j (k :: A))).sum :=
    coupon_scan_sum_future s (futureUnhit t j A)
      (coupon_futureUnhit_nodup t j A) hbound
      (fun k => couponScanIntegerNum t j (k :: A))
  calc
    (List.ofFn (fun e : Fin n =>
      couponScanIntegerWeight t
        (tolerantScanStep s t (.live j A) e))).sum =
      (List.ofFn (fun e : Fin n =>
        (if (unrotate s e).val < j ∨
            t ≤ (unrotate s e).val
         then couponScanIntegerNum t j A else 0) +
        (if (unrotate s e).val = j
         then couponScanIntegerNum t (j + 1)
           (eraseAvailable (j + 1) A) else 0) +
        (if (unrotate s e).val ∈ futureUnhit t j A
         then couponScanIntegerNum t j ((unrotate s e).val :: A)
         else 0))).sum := by
            apply ofFn_sum_eq
            intro e
            exact coupon_scan_live_row s t j A hj e
    _ = (n - (t - j)) * couponScanIntegerNum t j A +
        couponScanIntegerNum t (j + 1)
          (eraseAvailable (j + 1) A) +
        ((futureUnhit t j A).map (fun k =>
          couponScanIntegerNum t j (k :: A))).sum := by
            rw [ofFn_sum_add, ofFn_sum_add,
              hout, hprogress, hfirst]

/-- Unconditional one-step harmonic equation, including failed
and already-terminal states. -/
theorem coupon_scan_integer_harmonic {n : Nat}
    (s : Fin n) (t : Nat) (htn : t ≤ n) :
    ∀ x : TolerantScanState,
      (List.ofFn (fun e : Fin n =>
        couponScanIntegerWeight t (tolerantScanStep s t x e))).sum =
      n * couponScanIntegerWeight t x := by
  intro x
  cases x with
  | failed =>
      change (List.ofFn (fun _ : Fin n => (0 : Nat))).sum =
        n * 0
      exact ofFn_sum_const n 0
  | live j A =>
      by_cases hj : j < t
      · change
          (List.ofFn (fun e : Fin n =>
            couponScanIntegerWeight t
              (tolerantScanStep s t (.live j A) e))).sum =
            n * couponScanIntegerNum t j A
        calc
          _ = (n - (t - j)) * couponScanIntegerNum t j A +
              couponScanIntegerNum t (j + 1)
                (eraseAvailable (j + 1) A) +
              ((futureUnhit t j A).map (fun k =>
                couponScanIntegerNum t j (k :: A))).sum :=
            coupon_scan_rotated_edge_sum s t j A htn hj
          _ = (n - (t - j)) * couponScanIntegerNum t j A +
              (couponScanIntegerNum t (j + 1)
                (eraseAvailable (j + 1) A) +
                ((futureUnhit t j A).map (fun k =>
                  couponScanIntegerNum t j (k :: A))).sum) :=
            Nat.add_assoc _ _ _
          _ = (n - (t - j)) * couponScanIntegerNum t j A +
              (t - j) * couponScanIntegerNum t j A := by
                rw [← couponScanIntegerNum_harmonicA t j A hj]
          _ = n * couponScanIntegerNum t j A := by
                calc
                  _ = (n - (t - j) + (t - j)) *
                      couponScanIntegerNum t j A :=
                    (Nat.add_mul _ _ _).symm
                  _ = n * couponScanIntegerNum t j A := by
                    rw [Nat.sub_add_cancel (by omega)]
      · have hdone : t ≤ j := by omega
        change
          (List.ofFn (fun e : Fin n =>
            couponScanIntegerWeight t
              (tolerantScanStep s t (.live j A) e))).sum =
            n * couponScanIntegerNum t j A
        calc
          _ = (List.ofFn (fun _ : Fin n =>
              couponScanIntegerNum t j A)).sum := by
                apply ofFn_sum_eq
                intro e
                simp [couponScanIntegerWeight, tolerantScanStep, hdone]
          _ = _ := ofFn_sum_const n _

/-- Fully instantiated finite-horizon success/running mass
certificate: no local harmonic premise remains. -/
theorem coupon_scan_mass_unconditional {n : Nat}
    (s : Fin n) (t j : Nat) (A : List Nat)
    (htn : t ≤ n) (T : Nat) :
    couponScanIntegerDen t *
      Prob.scheduleSum n T
        (fun w =>
          if tolerantScanSuccess t
              (LDSinkBoundedKernel.run (tolerantScanStep s t)
                (.live j A) w)
          then 1 else 0) +
      Prob.scheduleSum n T
        (fun w =>
          couponScanRunningReward t (couponScanIntegerWeight t)
            (LDSinkBoundedKernel.run (tolerantScanStep s t)
              (.live j A) w)) =
      n ^ T * couponScanIntegerNum t j A := by
  exact coupon_scan_mass_if_harmonic s t
    (couponScanIntegerDen t)
    (couponScanIntegerNum t j A) j A
    (couponScanIntegerWeight t)
    (by rfl)
    (by
      intro k B hk
      exact couponScanIntegerNum_terminal t k B hk)
    (coupon_scan_integer_harmonic s t htn)
    rfl T

/-- The canonical start is the paper's p_scan(t)=p_0(empty).
Its finite-horizon mass equation is now premise-free. -/
theorem coupon_scan_p_scan_mass {n : Nat}
    (s : Fin n) (t : Nat) (htn : t ≤ n) (T : Nat) :
    couponScanIntegerDen t *
      Prob.scheduleSum n T
        (fun w =>
          if tolerantScanSuccess t
              (LDSinkBoundedKernel.run (tolerantScanStep s t)
                (.live 0 []) w)
          then 1 else 0) +
      Prob.scheduleSum n T
        (fun w =>
          couponScanRunningReward t (couponScanIntegerWeight t)
            (LDSinkBoundedKernel.run (tolerantScanStep s t)
              (.live 0 []) w)) =
      n ^ T * couponScanIntegerNum t 0 [] := by
  exact coupon_scan_mass_unconditional s t 0 [] htn T

/-- Exact cross multiplication identifies the common-scale start
with the previously certified rational pPair representation. -/
theorem coupon_scan_p_scan_ratio (t : Nat) :
    couponScanIntegerNum t 0 [] * (pPair t).2 =
      (pPair t).1 * couponScanIntegerDen t := by
  exact couponScanIntegerNum_represents t 0 []

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount)

/-!
The functions below transcribe the earlier integer Phinode for the
existing attempt observer; no protocol row or local state is added.
We stop at the first unproved cover-order drift/soundness lemma.
-/

/-- Exact unreduced G(t) numerator and denominator. -/
def couponNodeNumerator (t : Nat) : Nat :=
  (couponGPair t).1

def couponNodeDenominator (t : Nat) : Nat :=
  (couponGPair t).2

def couponNodeBudget (n t : Nat) : Nat :=
  n * couponNodeNumerator t

/-- Whether the final protected label M-1 remains in the mask.
The +1 condition avoids constructing an out-of-range Fin. -/
def couponNodeFinalUnseen {n : Nat} (s : Fin n)
    (M : Nat) (mask : Fin n → Bool) : Bool :=
  decide ((List.ofFn (fun e : Fin n =>
    if mask e = true ∧ (protectedLabel s e).val + 1 = M
    then (1 : Nat) else 0)).sum ≠ 0)

/-- No remaining unseen protected label below k. -/
def couponNodePrefixSeen {n : Nat} (s : Fin n)
    (mask : Fin n → Bool) (k : Nat) : Bool :=
  decide ((List.ofFn (fun e : Fin n =>
    if mask e = true ∧ (protectedLabel s e).val < k
    then (1 : Nat) else 0)).sum = 0)

/-- Chronological last-touch subsequence restricted to [0,k)
is exactly 0,...,k-1. -/
def couponNodePrefixOrdered {n : Nat} (s : Fin n)
    (M k : Nat) (word : List (Fin n)) : Bool :=
  let prot : Fin n → Bool :=
    fun e => canonicalMask M (protectedLabel s e)
  let last := couponLastTouch prot word
  decide (((last.filter (fun e =>
      decide ((protectedLabel s e).val < k))).map
        (fun e => (protectedLabel s e).val)) = List.range k)

/-- Factorial-weighted last-order numerator S(U,O). -/
def couponNodeCoverWeight {n : Nat} (s : Fin n)
    (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) : Nat :=
  if couponNodeFinalUnseen s M mask then
    ((List.range M).map (fun k =>
      if couponNodePrefixSeen s mask k &&
          couponNodePrefixOrdered s M k word
      then freshFact k else 0)).sum
  else 0

/-- P + n*a*(M! H_m - h*S). -/
def couponNodeCoverPotential {n : Nat} (s : Fin n)
    (t : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) : Nat :=
  couponNodeBudget n t +
      n * (pPair t).1 *
        scaledHarmonic (freshFact (t + 3)) (maskSize mask) -
      n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        couponNodeCoverWeight s (t + 3) mask word

/-- The zero-hit and one-hit launch potentials. -/
def couponNodeLaunchPotential (n t hits : Nat) : Nat :=
  let P := couponNodeBudget n t
  let discount :=
    n * (pPair t).1 * (harmonicPair (t + 3)).1 *
      freshFact (t + 3)
  if hits = 0 then P - discount
  else if hits = 1 then
    P - discount * (t + 2) - n * couponNodeDenominator t
  else P + n * couponNodeDenominator t

/-- P - P*W/Q + D*n*(t-j). -/
def couponNodeScanPotential (n t j : Nat) (A : List Nat) : Nat :=
  let P := couponNodeBudget n t
  if j < t then
    P - P * couponScanIntegerNum t j A /
      couponScanIntegerDen t +
      couponNodeDenominator t * n * (t - j)
  else P + couponNodeDenominator t

/-- The entire observer projection. Active terminal phases never
occur on a genuinely running attempt: couponTrialKernel exits first. -/
def couponNodePotential {n q : Nat} (s : Fin n) :
    CouponAttemptPhase n → Nat
  | .covering mask word =>
      couponNodeCoverPotential s (compileAdvice q).t mask word
  | .launching hits =>
      couponNodeLaunchPotential n (compileAdvice q).t hits
  | .scanning j A =>
      couponNodeScanPotential n (compileAdvice q).t j A
  | .succeeded =>
      couponNodeBudget n (compileAdvice q).t +
        couponNodeDenominator (compileAdvice q).t
  | .failed =>
      couponNodeBudget n (compileAdvice q).t +
        couponNodeDenominator (compileAdvice q).t

/- Closed-kernel arithmetic: 2 and 3 are named widths, not
unproved general divisibility assumptions. -/
theorem couponNodeNumerator_two :
    couponNodeNumerator 2 = 2109120 := by
  decide +kernel

theorem couponNodeNumerator_three :
    couponNodeNumerator 3 = 987905341440 := by
  decide +kernel

theorem couponNodeScanDen_two :
    couponScanIntegerDen 2 = 32 := by
  decide

theorem couponNodeScanDen_three :
    couponScanIntegerDen 3 = 279936 := by
  decide

theorem couponNodeDivides_two :
    couponScanIntegerDen 2 ∣ couponNodeNumerator 2 := by
  rw [couponNodeScanDen_two, couponNodeNumerator_two]
  decide

theorem couponNodeDivides_three :
    couponScanIntegerDen 3 ∣ couponNodeNumerator 3 := by
  rw [couponNodeScanDen_three, couponNodeNumerator_three]
  decide

/-- t=2 integer quotient for ALL j,A, not only canonical scan nodes. -/
theorem couponNodeScanExact_two (n j : Nat) (A : List Nat) :
    couponScanIntegerDen 2 ∣
      couponNodeBudget n 2 * couponScanIntegerNum 2 j A := by
  obtain ⟨k, hk⟩ := couponNodeDivides_two
  refine ⟨n * k * couponScanIntegerNum 2 j A, ?_⟩
  change (n * couponNodeNumerator 2) *
      couponScanIntegerNum 2 j A =
    couponScanIntegerDen 2 *
      (n * k * couponScanIntegerNum 2 j A)
  rw [hk]
  ac_rfl

/-- t=3 integer quotient for ALL j,A. -/
theorem couponNodeScanExact_three (n j : Nat) (A : List Nat) :
    couponScanIntegerDen 3 ∣
      couponNodeBudget n 3 * couponScanIntegerNum 3 j A := by
  obtain ⟨k, hk⟩ := couponNodeDivides_three
  refine ⟨n * k * couponScanIntegerNum 3 j A, ?_⟩
  change (n * couponNodeNumerator 3) *
      couponScanIntegerNum 3 j A =
    couponScanIntegerDen 3 *
      (n * k * couponScanIntegerNum 3 j A)
  rw [hk]
  ac_rfl

/-!
Chosen interface repair (a): a forward-closed actual-reachability
predicate. The witness contains the entire physical seed, not merely
a forged observer scan index. Its closure is a structural append proof.
-/

/-- Snoc for the actual prefix-recursive LDSinkBoundedKernel.run. -/
theorem couponNodeRunSnoc {S : Type} {n : Nat}
    (next : S → Fin n → S) (x : S)
    (word : List (Fin n)) (e : Fin n) :
    LDSinkBoundedKernel.run next x (word ++ [e]) =
      next (LDSinkBoundedKernel.run next x word) e := by
  induction word generalizing x with
  | nil =>
      rfl
  | cons first rest ih =>
      change
        LDSinkBoundedKernel.run next (next x first) (rest ++ [e]) =
          next (LDSinkBoundedKernel.run next (next x first) rest) e
      exact ih (next x first)

/-- Reachability is measured from EVERY Frozen seed, with actual
couponTrialKernel.step transitions and no physical-state reset. -/
def couponNodeReachable {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n) : Prop :=
  ∃ seed : CouponSeed fixed, ∃ word : List (Fin n),
    LDSinkBoundedKernel.run
        (Prob.attemptStepper (couponTrialKernel ring fixed s))
        (.active ((couponTrialKernel ring fixed s).start seed))
        word = .active a

theorem couponNodeReachableStart {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed) :
    couponNodeReachable ring fixed s
      ((couponTrialKernel ring fixed s).start seed) := by
  refine ⟨seed, [], ?_⟩
  rfl

theorem couponNodeReachableClosed {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a b : CouponSeed fixed × CouponAttemptPhase n)
    (e : Fin n)
    (ha : couponNodeReachable ring fixed s a)
    (hstep : (couponTrialKernel ring fixed s).step a e = .active b) :
    couponNodeReachable ring fixed s b := by
  obtain ⟨seed, word, hword⟩ := ha
  refine ⟨seed, word ++ [e], ?_⟩
  rw [couponNodeRunSnoc]
  rw [hword]
  exact hstep

/-!
The good-only drift abstraction is the all-state
finite-horizon induction with Good carried into each active successor.
It is separate from any proof of the machine-specific drift.
-/
theorem couponNodeBudgetFromGoodDrift
    {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (Good : A → Prop) (D P : Nat) (Φ : A → Nat)
    (hclosed : ∀ (a : A) (e : Fin n) (b : A),
      Good a → K.step a e = .active b → Good b)
    (hdrift : ∀ a, Good a →
      D * n +
        (List.ofFn (fun e : Fin n =>
          couponAttemptNodeValue P Φ (K.step a e))).sum ≤ n * Φ a)
    (hstart : ∀ seed, K.valid seed → Good (K.start seed))
    (hvalue : ∀ seed, K.valid seed → Φ (K.start seed) ≤ P) :
    ∀ seed, K.valid seed → ∀ T,
      D * costNumerator (Prob.attemptStepper K)
          (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
          (.active (K.start seed)) T +
        P * retryCount K (.active (K.start seed)) T ≤
      n ^ T * P := by
  have hcore : ∀ T (a : A), Good a →
      D * attemptCostNumerator K (.active a) T +
        P * retryCount K (.active a) T ≤ n ^ T * Φ a := by
    intro T
    induction T with
    | zero =>
        intro a ha
        simp [attemptCostNumerator, retryCount]
    | succ T ih =>
        intro a ha
        have hc (e : Fin n) :
            D * attemptCostNumerator K (K.step a e) T +
              P * retryCount K (K.step a e) T ≤
            n ^ T * couponAttemptNodeValue P Φ (K.step a e) := by
          cases hz : K.step a e with
          | success =>
              cases T <;> simp [attemptCostNumerator, retryCount,
                couponAttemptNodeValue]
          | retry seed =>
              cases T <;> simp [attemptCostNumerator, retryCount,
                couponAttemptNodeValue, Nat.mul_comm]
          | active b =>
              simpa only [hz, couponAttemptNodeValue] using
                ih b (hclosed a e b ha hz)
        have hsum :
            (List.ofFn (fun e : Fin n =>
              D * attemptCostNumerator K (K.step a e) T +
                P * retryCount K (K.step a e) T)).sum ≤
            n ^ T * (List.ofFn (fun e : Fin n =>
              couponAttemptNodeValue P Φ (K.step a e))).sum := by
          have hh := ofFn_sum_le _ _ hc
          simpa only [ofFn_sum_mul_left] using hh
        change
          D * (n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                attemptCostNumerator K (K.step a e) T)).sum) +
            P * (List.ofFn (fun e : Fin n =>
              retryCount K (K.step a e) T)).sum ≤
          n ^ (T + 1) * Φ a
        calc
          D * (n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  attemptCostNumerator K (K.step a e) T)).sum) +
              P * (List.ofFn (fun e : Fin n =>
                retryCount K (K.step a e) T)).sum =
            n ^ T * (D * n) +
              (List.ofFn (fun e : Fin n =>
                D * attemptCostNumerator K (K.step a e) T +
                  P * retryCount K (K.step a e) T)).sum := by
                    simp only [Nat.mul_add, Nat.pow_succ,
                      ofFn_sum_mul_left, ofFn_sum_add]
                    ac_rfl
          _ ≤ n ^ T * (D * n) +
              n ^ T * (List.ofFn (fun e : Fin n =>
                couponAttemptNodeValue P Φ (K.step a e))).sum :=
              Nat.add_le_add_left hsum _
          _ = n ^ T * (D * n +
              (List.ofFn (fun e : Fin n =>
                couponAttemptNodeValue P Φ (K.step a e))).sum) := by
                  rw [Nat.mul_add]
          _ ≤ n ^ T * (n * Φ a) :=
              Nat.mul_le_mul_left _ (hdrift a ha)
          _ = n ^ (T + 1) * Φ a := by
                rw [Nat.pow_succ]
                ac_rfl
  intro seed hv T
  rw [Prob.attempt_costNumerator_eq]
  have h := hcore T (K.start seed) (hstart seed hv)
  exact Nat.le_trans h
    (Nat.mul_le_mul_left (n ^ T) (hvalue seed hv))

/-!
STOP at item (3): the factorial-weighted cover-order harmonic
identity and physical terminal-seen bridge are not yet Lean theorems.
There is deliberately no unsupported CouponJointBudget declaration.
-/

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-!
The t=2 and t=3 cover subtraction is shown not to truncate,
even on arbitrary masks/words. This implies the requested
reachable-state no-truncation property a fortiori.

The outside-protected-edge successor preserves last-touch
order, S(U,O), and the whole cover potential. The remaining
nontrivial cover harmonic identity, including revisits,
first-time protected hits and the last coupon, is NOT proved.
-/

/-- Every conditional factorial summand is at most its
unconditional counterpart. This works for arbitrary Boolean
tests and arbitrary lists. -/
private theorem couponNodeConditionalFactorialSumLe
    (xs : List Nat) (flag : Nat → Bool) :
    (xs.map (fun k => if flag k then freshFact k else 0)).sum ≤
      (xs.map freshFact).sum := by
  induction xs with
  | nil =>
      exact Nat.le_refl _
  | cons k ks ih =>
      change
        (if flag k then freshFact k else 0) +
          (ks.map (fun v => if flag v then freshFact v else 0)).sum ≤
        freshFact k + (ks.map freshFact).sum
      cases hc : flag k <;> simp [hc] <;> omega

/-- An unconditional upper bound on the exact factorial-weighted
last-touch numerator. In particular it requires neither coherent
mask/word scratch nor a reachability hypothesis. -/
theorem couponNodeCoverWeightLeFactorialSum {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) :
    couponNodeCoverWeight s M mask word ≤
      ((List.range M).map freshFact).sum := by
  cases hc : couponNodeFinalUnseen s M mask with
  | false =>
      simp [couponNodeCoverWeight, hc]
  | true =>
      simpa [couponNodeCoverWeight, hc] using
        (couponNodeConditionalFactorialSumLe
          (List.range M)
          (fun k => couponNodePrefixSeen s mask k &&
            couponNodePrefixOrdered s M k word))

theorem couponNodeCoverWeightLeTwo {n : Nat}
    (s : Fin n) (mask : Fin n → Bool)
    (word : List (Fin n)) :
    couponNodeCoverWeight s 5 mask word ≤ 34 := by
  have hb := couponNodeCoverWeightLeFactorialSum s 5 mask word
  have hsum :
      ((List.range 5).map freshFact).sum = 34 := by
        decide
  rw [hsum] at hb
  exact hb

theorem couponNodeCoverWeightLeThree {n : Nat}
    (s : Fin n) (mask : Fin n → Bool)
    (word : List (Fin n)) :
    couponNodeCoverWeight s 6 mask word ≤ 154 := by
  have hb := couponNodeCoverWeightLeFactorialSum s 6 mask word
  have hsum :
      ((List.range 6).map freshFact).sum = 154 := by
        decide
  rw [hsum] at hb
  exact hb

theorem couponNodePairNumeratorTwo :
    (pPair 2).1 = 3 := by
  decide

theorem couponNodePairNumeratorThree :
    (pPair 3).1 = 13248 := by
  decide +kernel

theorem couponNodeHarmonicNumeratorTwo :
    (harmonicPair 5).1 = 274 := by
  decide

theorem couponNodeHarmonicNumeratorThree :
    (harmonicPair 6).1 = 1764 := by
  decide

/-- The subtrahend of the cover potential never exceeds its
minuend at t=2, even for arbitrary inherited mask/word data.
Thus Nat subtraction in couponNodeCoverPotential is exact. -/
theorem couponNodeCoverNoTruncationTwo {n : Nat}
    (s : Fin n) (mask : Fin n → Bool)
    (word : List (Fin n)) :
    n * (pPair 2).1 * (harmonicPair 5).1 *
        couponNodeCoverWeight s 5 mask word ≤
      couponNodeBudget n 2 +
        n * (pPair 2).1 *
          scaledHarmonic (freshFact 5) (maskSize mask) := by
  have hb := couponNodeCoverWeightLeTwo s mask word
  have hlocal :
      (pPair 2).1 * (harmonicPair 5).1 *
          couponNodeCoverWeight s 5 mask word ≤
        couponNodeNumerator 2 := by
          rw [couponNodePairNumeratorTwo,
            couponNodeHarmonicNumeratorTwo,
            couponNodeNumerator_two]
          omega
  have hscaled := Nat.mul_le_mul_left n hlocal
  calc
    n * (pPair 2).1 * (harmonicPair 5).1 *
        couponNodeCoverWeight s 5 mask word =
      n * ((pPair 2).1 * (harmonicPair 5).1 *
        couponNodeCoverWeight s 5 mask word) := by
          ac_rfl
    _ ≤ n * couponNodeNumerator 2 := hscaled
    _ ≤ couponNodeBudget n 2 +
          n * (pPair 2).1 *
            scaledHarmonic (freshFact 5) (maskSize mask) := by
              dsimp only [couponNodeBudget]
              omega

/-- The analogous unconditional no-truncation statement at t=3.
No irrational bound, approximate division, or rounding is used. -/
theorem couponNodeCoverNoTruncationThree {n : Nat}
    (s : Fin n) (mask : Fin n → Bool)
    (word : List (Fin n)) :
    n * (pPair 3).1 * (harmonicPair 6).1 *
        couponNodeCoverWeight s 6 mask word ≤
      couponNodeBudget n 3 +
        n * (pPair 3).1 *
          scaledHarmonic (freshFact 6) (maskSize mask) := by
  have hb := couponNodeCoverWeightLeThree s mask word
  have hlocal :
      (pPair 3).1 * (harmonicPair 6).1 *
          couponNodeCoverWeight s 6 mask word ≤
        couponNodeNumerator 3 := by
          rw [couponNodePairNumeratorThree,
            couponNodeHarmonicNumeratorThree,
            couponNodeNumerator_three]
          omega
  have hscaled := Nat.mul_le_mul_left n hlocal
  calc
    n * (pPair 3).1 * (harmonicPair 6).1 *
        couponNodeCoverWeight s 6 mask word =
      n * ((pPair 3).1 * (harmonicPair 6).1 *
        couponNodeCoverWeight s 6 mask word) := by
          ac_rfl
    _ ≤ n * couponNodeNumerator 3 := hscaled
    _ ≤ couponNodeBudget n 3 +
          n * (pPair 3).1 *
            scaledHarmonic (freshFact 6) (maskSize mask) := by
              dsimp only [couponNodeBudget]
              omega

/-- The requested good-state specialization follows from a
stronger property that already holds for every mask and word.
The reachable and phase hypotheses are retained to expose the
precise intended interface with couponNodeReachable. -/
theorem couponNodeCoverNoTruncationGood
    {n q : Nat} (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (mask : Fin n → Bool) (word : List (Fin n))
    (hgood : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .covering mask word)
    (hwidth : (compileAdvice q).t = 2 ∨
      (compileAdvice q).t = 3) :
    n * (pPair (compileAdvice q).t).1 *
        (harmonicPair ((compileAdvice q).t + 3)).1 *
        couponNodeCoverWeight s ((compileAdvice q).t + 3)
          mask word ≤
      couponNodeBudget n (compileAdvice q).t +
        n * (pPair (compileAdvice q).t).1 *
          scaledHarmonic (freshFact ((compileAdvice q).t + 3))
            (maskSize mask) := by
  rcases hwidth with ht | ht
  · rw [ht]
    exact couponNodeCoverNoTruncationTwo s mask word
  · rw [ht]
    exact couponNodeCoverNoTruncationThree s mask word

/-- If the final protected coupon was previously seen, the
order-acceptance numerator S is exactly zero. -/
theorem couponNodeCoverWeightZeroIfFinalSeen {n : Nat}
    (s : Fin n) (M : Nat)
    (mask : Fin n → Bool) (word : List (Fin n))
    (hseen : couponNodeFinalUnseen s M mask = false) :
    couponNodeCoverWeight s M mask word = 0 := by
  simp [couponNodeCoverWeight, hseen]

/-- An edge outside the protected M labels changes neither the
last-touch record nor the prefix-order predicates. -/
theorem couponNodePrefixOrderedOutside {n : Nat}
    (s : Fin n) (M k : Nat)
    (word : List (Fin n)) (e : Fin n)
    (hout : canonicalMask M (protectedLabel s e) = false) :
    couponNodePrefixOrdered s M k (word ++ [e]) =
      couponNodePrefixOrdered s M k word := by
  have hlast :
      couponLastTouch
          (fun i : Fin n => canonicalMask M (protectedLabel s i))
          (word ++ [e]) =
        couponLastTouch
          (fun i : Fin n => canonicalMask M (protectedLabel s i))
          word := by
            rw [couponLastTouch_snoc]
            exact couponLastTouch_outside
              (fun i : Fin n => canonicalMask M (protectedLabel s i))
              (couponLastTouch
                (fun i : Fin n =>
                  canonicalMask M (protectedLabel s i)) word)
              e hout
  dsimp only [couponNodePrefixOrdered]
  rw [hlast]

/-- Exact S(U,O) equality for the outside-protected-edge
successor class, with no coherence assumption on the mask. -/
theorem couponNodeCoverWeightOutside {n : Nat}
    (s : Fin n) (M : Nat)
    (mask : Fin n → Bool) (word : List (Fin n))
    (e : Fin n)
    (hout : canonicalMask M (protectedLabel s e) = false) :
    couponNodeCoverWeight s M mask (word ++ [e]) =
      couponNodeCoverWeight s M mask word := by
  have heq :
      ((List.range M).map (fun k =>
        if couponNodePrefixSeen s mask k &&
            couponNodePrefixOrdered s M k (word ++ [e])
        then freshFact k else 0)).sum =
      ((List.range M).map (fun k =>
        if couponNodePrefixSeen s mask k &&
            couponNodePrefixOrdered s M k word
        then freshFact k else 0)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro k hk
          rw [couponNodePrefixOrderedOutside s M k word e hout]
  cases hg : couponNodeFinalUnseen s M mask with
  | false =>
      simp [couponNodeCoverWeight, hg]
  | true =>
      simpa [couponNodeCoverWeight, hg] using heq

/-- Complete cover potential equality on a selected outside edge.
The hypothesis mask e = false follows from canonical first-cover
reachability when e is outside the protected physical set. -/
theorem couponNodeCoverPotentialOutside {n : Nat}
    (s : Fin n) (t : Nat)
    (mask : Fin n → Bool) (word : List (Fin n))
    (e : Fin n)
    (hmask : mask e = false)
    (hout : canonicalMask (t + 3) (protectedLabel s e) = false) :
    couponNodeCoverPotential s t (maskDrop mask e) (word ++ [e]) =
      couponNodeCoverPotential s t mask word := by
  rw [coupon_maskDrop_false mask e hmask]
  unfold couponNodeCoverPotential
  rw [couponNodeCoverWeightOutside s (t + 3) mask word e hout]

/-!
STOP: The remaining protected-label successor cases are genuinely
nontrivial. In particular, a revisit can reorder a prefix, a first
hit can change more than one indicator in S(U,O), and the last
missing coupon changes the AttemptNode payoff from an active cover
potential to either P (retry) or the zero-hit launch potential.
The full factorial-weighted harmonic equality and cover drift
are not established by the outside-edge lemma above.

No theorem for the complete cover drift, seen-flag soundness,
launch/scan drift or CouponJointBudget is declared here.
-/

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount)

/-!
Part A is the corrected *scope* of the joint retry budget. It is
deliberately a new definition: CouponJointBudget is not edited.
Every new consumer makes ht/hn/hroot/hbad explicit and forwards the
same unchanged integer cost/retry inequality through the old chain.

Part B supplies the elementary factorial coefficient/telescoping
lemma for the conditional last-touch cover calculation. It does
not pretend to have formalized the crucial prefix-indicator
transition under protected revisits and first-time discoveries.
The latter is the first unfinished item.
-/

/-- Failure-scoped joint budget. The same *exact* D-cost plus
P-retry inequality as CouponJointBudget, but only when the rootless
frozen word fails at least one of the three raw relations.
The width and ring-size hypotheses are the same as the existing
coupon_clear_expected_if_joint_budget consumer. -/
def CouponJointBudgetOnFailure {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n) : Prop :=
  ∀ (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s),
    ∀ seed : CouponSeed fixed, ∀ T : Nat,
      (couponGPair (compileAdvice q).t).2 *
        costNumerator (Prob.attemptStepper
          (couponTrialKernel ring fixed s))
          (fun node => Prob.attemptGood node ∨ Prob.attemptFail node)
          (.active ((couponTrialKernel ring fixed s).start seed)) T +
        (n * (couponGPair (compileAdvice q).t).1) *
          retryCount (couponTrialKernel ring fixed s)
            (.active ((couponTrialKernel ring fixed s).start seed)) T ≤
        n ^ T * (n * (couponGPair (compileAdvice q).t).1)

/-- Under the *exact* consumer premises, the conditional budget
gives the original inequality, without weakening any constant. -/
theorem couponJointBudgetOnFailure_elim {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (hbudget : CouponJointBudgetOnFailure ring fixed s) :
    CouponJointBudget ring fixed s := by
  intro seed T
  exact hbudget ht hn hroot hbad seed T

/-- The new first consumer: the physical scaled cost retains
the same D=(couponGPair t).2 and P=n*(couponGPair t).1. -/
theorem couponGhost_scaled_of_joint_budget_on_failure {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (hbudget : CouponJointBudgetOnFailure ring fixed s) :
    ∀ T,
      (couponGPair (compileAdvice q).t).2 *
        costNumerator (freshGhostStep ring fixed s)
          freshGhostGood z T ≤
        n ^ T * (n * (couponGPair (compileAdvice q).t).1) := by
  exact couponGhost_scaled_of_joint_budget ring fixed s z hz
    (couponJointBudgetOnFailure_elim ring fixed s
      ht hn hroot hbad hbudget)

/-- The unchanged exact rational bridge, with failure hypotheses
threaded to the scaled-cost consumer. -/
theorem couponGhost_expected_of_joint_budget_on_failure {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (hbudget : CouponJointBudgetOnFailure ring fixed s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (freshGhostStep ring fixed s) freshGhostGood z
      ((n : Rat) * couponG (compileAdvice q).t) := by
  exact couponGhost_expected_of_joint_budget ring fixed s hn z hz
    (couponJointBudgetOnFailure_elim ring fixed s
      ht hn hroot hbad hbudget)

/-- Same public hypotheses and SAME scaled bound as the old
coupon_clear_scaled_if_joint_budget. No rootless assumption is hidden. -/
theorem coupon_clear_scaled_if_joint_budget_on_failure {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (hbudget : CouponJointBudgetOnFailure ring fixed s) :
    ∀ T,
      (couponGPair (compileAdvice q).t).2 *
        costNumerator (freshGhostStep ring fixed s)
          freshGhostGood z T ≤
        n ^ T * (n * (couponGPair (compileAdvice q).t).1) := by
  exact couponGhost_scaled_of_joint_budget_on_failure
    ring fixed s ht hn hroot hbad z hz hbudget

/-- Same precise expected hitting-time conclusion as the old
coupon_clear_expected_if_joint_budget, now with failure-scoped budget. -/
theorem coupon_clear_expected_if_joint_budget_on_failure {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (hbudget : CouponJointBudgetOnFailure ring fixed s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (freshGhostStep ring fixed s) freshGhostGood z
      ((n : Rat) * couponG (compileAdvice q).t) := by
  exact couponGhost_expected_of_joint_budget_on_failure
    ring fixed s ht hn hroot hbad z hz hbudget

/-- Explicit bridge from the good-only induction to
the NEW conditional interface. It is a transfer theorem, not a
claim that the concrete Phinode already satisfies the drift. -/
theorem couponJointBudgetOnFailure_of_reachable_potential {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (Phi : CouponSeed fixed × CouponAttemptPhase n → Nat)
    (hdrift :
      ∀ (ht : 2 ≤ (compileAdvice q).t)
        (hn : (compileAdvice q).t + 3 ≤ n)
        (hroot : ∀ i : Fin n, (fixed i).l = false)
        (hbad :
          ¬ NonzeroRelation
            (certificateWordOfAgents (compileAdvice q) fixed) s ∨
          ¬ RecurrenceRelation
            (certificateWordOfAgents (compileAdvice q) fixed) s ∨
          ¬ MarkerRelation
            (certificateWordOfAgents (compileAdvice q) fixed) s),
        ∀ a : CouponSeed fixed × CouponAttemptPhase n,
          couponNodeReachable ring fixed s a →
          (couponGPair (compileAdvice q).t).2 * n +
            (List.ofFn (fun e : Fin n =>
              couponAttemptNodeValue
                (n * (couponGPair (compileAdvice q).t).1) Phi
                ((couponTrialKernel ring fixed s).step a e))).sum ≤
            n * Phi a)
    (hstart :
      ∀ seed : CouponSeed fixed,
        Phi ((couponTrialKernel ring fixed s).start seed) ≤
          n * (couponGPair (compileAdvice q).t).1) :
    CouponJointBudgetOnFailure ring fixed s := by
  intro ht hn hroot hbad seed T
  exact couponNodeBudgetFromGoodDrift
    (couponTrialKernel ring fixed s)
    (couponNodeReachable ring fixed s)
    (couponGPair (compileAdvice q).t).2
    (n * (couponGPair (compileAdvice q).t).1) Phi
    (fun a e b ha hstep =>
      couponNodeReachableClosed ring fixed s a b e ha hstep)
    (fun a ha => hdrift ht hn hroot hbad a ha)
    (fun child _ => couponNodeReachableStart ring fixed s child)
    (fun child _ => hstart child)
    seed (by trivial) T

/-!
Part B: the exact factorial coefficient which remains after
partitioning the last-touch indicator update by e (selected label)
and k (accepted increasing prefix length).

For k<M, the k! term is preserved by M-1-k later-label choices
and recreated as (k+1)! by selecting label k. This is the purely
algebraic heart of M*S = sum_e S(next_e). The other missing part is
the *combinatorial* prefix-indicator update itself.
-/

/-- Factorial coefficient for the revisit / first-hit split.
No rational arithmetic or combinatorial independence premise. -/
theorem couponNodeCoverFactorialCoefficient (M k : Nat)
    (hk : k < M) :
    (M - 1 - k) * freshFact k + freshFact (k + 1) =
      M * freshFact k := by
  have hs : M - 1 - k + (k + 1) = M := by omega
  calc
    (M - 1 - k) * freshFact k + freshFact (k + 1) =
      (M - 1 - k) * freshFact k +
        (k + 1) * freshFact k := by rfl
    _ = (M - 1 - k + (k + 1)) * freshFact k :=
      (Nat.add_mul _ _ _).symm
    _ = M * freshFact k := by rw [hs]

/-- At |U|=1 the final first hit pays M!, exactly the missing
last k=M-1 term in the weighted coefficient sum. -/
theorem couponNodeCoverTerminalFactorial (M : Nat)
    (hM : 0 < M) :
    M * freshFact (M - 1) = freshFact M := by
  cases M with
  | zero =>
      omega
  | succ m =>
      rfl

/-- Weighted version of the factorial cancellation, for ANY
abstract prefix indicator coefficients F(k). This is the portion
of the conditional harmonic identity needing only arithmetic. -/
theorem couponNodeCoverFactorialTelescoping
    (M : Nat) (F : Nat → Nat) :
    ((List.range (M - 1)).map (fun k =>
      ((M - 1 - k) * freshFact k + freshFact (k + 1)) *
        F k)).sum =
      M * ((List.range (M - 1)).map
        (fun k => freshFact k * F k)).sum := by
  have hpoint (k : Nat) (hk : k ∈ List.range (M - 1)) :
      ((M - 1 - k) * freshFact k + freshFact (k + 1)) *
          F k =
        M * (freshFact k * F k) := by
    have hkm : k < M := by
      have hh : k < M - 1 := List.mem_range.mp hk
      omega
    rw [couponNodeCoverFactorialCoefficient M k hkm]
    ac_rfl
  have hfactor (xs : List Nat) :
      (xs.map (fun k => M * (freshFact k * F k))).sum =
        M * (xs.map (fun k => freshFact k * F k)).sum := by
    induction xs with
    | nil =>
        simp
    | cons k ks ih =>
        simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]
  calc
    ((List.range (M - 1)).map (fun k =>
        ((M - 1 - k) * freshFact k + freshFact (k + 1)) *
          F k)).sum =
      ((List.range (M - 1)).map
        (fun k => M * (freshFact k * F k))).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro k hk
        exact hpoint k hk
    _ = M * ((List.range (M - 1)).map
          (fun k => freshFact k * F k)).sum :=
      hfactor (List.range (M - 1))

/-!
STOP: The first missing B lemma is a theorem that extracts
coherent first-cover history from couponNodeReachable and proves
the per-label prefix-indicator update:
for 0 <= e < M-1, the indicators F_k after touching e agree
with the old F_k for k<=e, equal F_e for k=e+1, and vanish for
k>e+1. This requires the last-touch list to be a nodup
permutation of the seen protected labels, and the current mask
to be precisely the original protected mask after the word.

The terminal case e=M-1 must identify lastAccept M of the
completed mapped word with F_(M-1) of the previous state.
The factorial coefficient and terminal coefficient are
proved above; the actual mask/last-touch update and
finite protected/unprotected edge-sum transport are not.

No statement of conditional cover drift, seen-flag soundness,
launch/scan drift or CouponJointBudgetOnFailure for t=2,3
is asserted without a proof.
-/

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount)

/-!
We first establish an exact mask-fold trace for every live cover
node of the actual couponTrialKernel, by a forward induction on its
AttemptNode run. Then we establish Nodup of the last-touch register
by a separate induction on the chronological list.

These statements do not require hbad, because they concern only
the proof-side coupon observer. The next pointwise relation between
lastAccept and that last-touch register is not yet formalized;
this is the first unfinished item. No full cover drift is claimed.
-/

/-- The surviving true bits in a first-cover mask are exactly
the initial true bits that have not yet appeared in the word.
This is the pointwise form of "original mask minus covered labels". -/
theorem couponNodeMaskFoldMembership {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n)) (i : Fin n) :
    (word.foldl maskDrop r) i = true ↔
      r i = true ∧ i ∉ word := by
  induction word generalizing r with
  | nil =>
      simp
  | cons e rest ih =>
      change
        (rest.foldl maskDrop (maskDrop r e)) i = true ↔
          r i = true ∧ i ∉ (e :: rest)
      rw [ih (maskDrop r e)]
      by_cases hie : i = e
      · subst i
        simp [maskDrop]
      · have hei : e ≠ i := Ne.symm hie
        simp [maskDrop, hie, hei]

/-- The phase-only invariant required to project a reached active
cover onto its complete chronological word. -/
def couponNodeCoverHistory {n q : Nat} (s : Fin n) :
    CouponAttemptPhase n → Prop
  | .covering mask word =>
      mask = word.foldl maskDrop
        (fun e : Fin n =>
          canonicalMask ((compileAdvice q).t + 3)
            (protectedLabel s e))
  | _ => True

/-- One actual observer step preserves the cover mask/word history.
A launch or scan phase never re-enters covering in this attempt. -/
theorem couponNodeCoverHistoryStep {n q : Nat}
    (s : Fin n) (phase : CouponAttemptPhase n) (e : Fin n)
    (h : couponNodeCoverHistory (q := q) s phase) :
    couponNodeCoverHistory (q := q) s
      (couponAttemptPhaseNext (q := q) s phase e) := by
  cases phase with
  | covering mask word =>
      change
        mask = word.foldl maskDrop
          (fun i : Fin n =>
            canonicalMask ((compileAdvice q).t + 3)
              (protectedLabel s i)) at h
      by_cases hzero : maskSize (maskDrop mask e) = 0
      · simp [couponAttemptPhaseNext, hzero]
        split <;> trivial
      · have hfold :
            maskDrop mask e =
              (word ++ [e]).foldl maskDrop
                (fun i : Fin n =>
                  canonicalMask ((compileAdvice q).t + 3)
                    (protectedLabel s i)) := by
          rw [List.foldl_append]
          change
            maskDrop mask e =
              maskDrop
                (word.foldl maskDrop
                  (fun i : Fin n =>
                    canonicalMask ((compileAdvice q).t + 3)
                      (protectedLabel s i))) e
          rw [h]
        simpa [couponAttemptPhaseNext, hzero,
          couponNodeCoverHistory] using hfold
  | launching hits =>
      simp [couponAttemptPhaseNext]
      repeat' split
      all_goals trivial
  | scanning j A =>
      simp [couponAttemptPhaseNext]
      repeat' split
      all_goals trivial
  | succeeded =>
      trivial
  | failed =>
      trivial

/-- The same history predicate lifted to the genuine RetryKernel
attempt node: the absorbing terminals satisfy it vacuously. -/
def couponNodeCoverHistoryAtNode {n q : Nat}
    (fixed : (protocol q).Configuration n) (s : Fin n) :
    AttemptNode
      (CouponSeed fixed × CouponAttemptPhase n)
      (CouponSeed fixed) → Prop
  | .active a => couponNodeCoverHistory (q := q) s a.2
  | .success => True
  | .retry _ => True

/-- The physical kernel may terminate on a real seen bit, but each
active successor's phase is the literal observer phase transition. -/
theorem couponNodeCoverHistoryKernelStep {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (node : AttemptNode
      (CouponSeed fixed × CouponAttemptPhase n)
      (CouponSeed fixed))
    (e : Fin n)
    (h : couponNodeCoverHistoryAtNode fixed s node) :
    couponNodeCoverHistoryAtNode fixed s
      (Prob.attemptStepper
        (couponTrialKernel ring fixed s) node e) := by
  cases node with
  | success =>
      trivial
  | retry seed =>
      trivial
  | active a =>
      cases a with
      | mk seed phase =>
          change couponNodeCoverHistory (q := q) s phase at h
          have hnext :=
            couponNodeCoverHistoryStep (q := q) s phase e h
          cases hp : couponAttemptPhaseNext (q := q) s phase e with
          | succeeded =>
              simp [Prob.attemptStepper, couponTrialKernel, hp]
              split <;> trivial
          | failed =>
              simp [Prob.attemptStepper, couponTrialKernel,
                hp, couponNodeCoverHistoryAtNode]
          | covering mask word =>
              simpa [Prob.attemptStepper, couponTrialKernel,
                hp, couponNodeCoverHistoryAtNode] using hnext
          | launching hits =>
              simpa [Prob.attemptStepper, couponTrialKernel,
                hp, couponNodeCoverHistoryAtNode] using hnext
          | scanning j once =>
              simpa [Prob.attemptStepper, couponTrialKernel,
                hp, couponNodeCoverHistoryAtNode] using hnext

/-- Dedicated induction on the actual attempt-word witness.
This does not replace a physical step by an observer step. -/
theorem couponNodeCoverHistoryRun {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n) :
    ∀ (node : AttemptNode
        (CouponSeed fixed × CouponAttemptPhase n)
        (CouponSeed fixed))
      (word : List (Fin n)),
      couponNodeCoverHistoryAtNode fixed s node →
      couponNodeCoverHistoryAtNode fixed s
        (LDSinkBoundedKernel.run
          (Prob.attemptStepper (couponTrialKernel ring fixed s))
          node word) := by
  intro node word
  induction word generalizing node with
  | nil =>
      intro h
      exact h
  | cons e rest ih =>
      intro h
      change
        couponNodeCoverHistoryAtNode fixed s
          (LDSinkBoundedKernel.run
            (Prob.attemptStepper (couponTrialKernel ring fixed s))
            (Prob.attemptStepper
              (couponTrialKernel ring fixed s) node e) rest)
      exact ih _
        (couponNodeCoverHistoryKernelStep
          ring fixed s node e h)

/-- First requested reached-state invariant. Every genuinely
reached active covering phase has exactly the original protected
mask after all selections in its stored chronological word. -/
theorem couponNodeReachableCoverMaskFold {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (mask : Fin n → Bool) (word : List (Fin n))
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .covering mask word) :
    mask =
      word.foldl maskDrop
        (fun e : Fin n =>
          canonicalMask ((compileAdvice q).t + 3)
            (protectedLabel s e)) := by
  obtain ⟨seed, schedule, hrun⟩ := hreach
  have hstart :
      couponNodeCoverHistoryAtNode fixed s
        (.active ((couponTrialKernel ring fixed s).start seed)) := by
    rfl
  have hstate :=
    couponNodeCoverHistoryRun ring fixed s
      (.active ((couponTrialKernel ring fixed s).start seed))
      schedule hstart
  rw [hrun] at hstate
  change couponNodeCoverHistory (q := q) s a.2 at hstate
  rw [hphase] at hstate
  exact hstate

/-- Pointwise mask identity, including a previously visited
protected label and every initially unprotected physical edge. -/
theorem couponNodeReachableCoverMaskMembership {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (mask : Fin n → Bool) (word : List (Fin n))
    (i : Fin n)
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .covering mask word) :
    mask i = true ↔
      canonicalMask ((compileAdvice q).t + 3)
        (protectedLabel s i) = true ∧ i ∉ word := by
  rw [couponNodeReachableCoverMaskFold
    ring fixed s a mask word hreach hphase]
  exact couponNodeMaskFoldMembership
    (fun e : Fin n =>
      canonicalMask ((compileAdvice q).t + 3)
        (protectedLabel s e)) word i

/-- The cover-potential outside-edge hypothesis now follows
from genuine reachability; no additional mask premise is needed. -/
theorem couponNodeReachableCoverOutsideFalse {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (mask : Fin n → Bool) (word : List (Fin n))
    (e : Fin n)
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .covering mask word)
    (hout : canonicalMask ((compileAdvice q).t + 3)
      (protectedLabel s e) = false) :
    mask e = false := by
  have hh :=
    couponNodeReachableCoverMaskMembership
      ring fixed s a mask word e hreach hphase
  cases hm : mask e with
  | false =>
      rfl
  | true =>
      have h : canonicalMask ((compileAdvice q).t + 3)
          (protectedLabel s e) = true := (hh.mp hm).1
      rw [hout] at h
      cases h

/-- Moving one protected label to the newest position preserves
Nodup; previously present labels are erased before appending. -/
theorem couponNodeLastTouchStepNodup {n : Nat}
    (r : Fin n → Bool) (last : List (Fin n))
    (e : Fin n) (hNo : last.Nodup) :
    (couponLastTouchStep r last e).Nodup := by
  cases hr : r e with
  | false =>
      simpa [couponLastTouchStep, hr] using hNo
  | true =>
      rw [show couponLastTouchStep r last e =
        (last.erase e) ++ [e] by
          simp [couponLastTouchStep, hr]]
      have hErase : (last.erase e).Nodup := hNo.erase e
      have hAbsent : e ∉ last.erase e := hNo.not_mem_erase
      apply List.nodup_append.mpr
      refine ⟨hErase, by simp, ?_⟩
      intro x hx y hy hxy
      have hye : y = e := by simpa using hy
      rw [hxy, hye] at hx
      exact hAbsent hx

/-- Second, independent induction: every fold of last-touch
steps preserves a Nodup initial register. -/
theorem couponNodeLastTouchFoldNodup {n : Nat}
    (r : Fin n → Bool) :
    ∀ (word last : List (Fin n)),
      last.Nodup →
        (word.foldl (couponLastTouchStep r) last).Nodup := by
  intro word
  induction word with
  | nil =>
      intro last h
      exact h
  | cons e rest ih =>
      intro last h
      change
        (rest.foldl (couponLastTouchStep r)
          (couponLastTouchStep r last e)).Nodup
      exact ih _
        (couponNodeLastTouchStepNodup r last e h)

/-- The chronological last-touch summary always contains distinct
protected physical edges, even for an arbitrary schedule word. -/
theorem couponNodeLastTouchNodup {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n)) :
    (couponLastTouch r word).Nodup := by
  change (word.foldl (couponLastTouchStep r) []).Nodup
  exact couponNodeLastTouchFoldNodup r word [] (by simp)

/-- Requested reached-state Nodup invariant. It is a corollary
of the stronger unconditional word-induction certificate. -/
theorem couponNodeReachableCoverLastTouchNodup {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (mask : Fin n → Bool) (word : List (Fin n))
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .covering mask word) :
    (couponLastTouch
      (fun e : Fin n =>
        canonicalMask ((compileAdvice q).t + 3)
          (protectedLabel s e)) word).Nodup := by
  exact couponNodeLastTouchNodup
    (fun e : Fin n =>
      canonicalMask ((compileAdvice q).t + 3)
        (protectedLabel s e)) word


/-- Selected protected touches preserve the set of earlier
last-touched labels and add the selected label. -/
theorem couponNodeLastTouchStepMembership {n : Nat}
    (r : Fin n → Bool) (last : List (Fin n))
    (e i : Fin n) :
    i ∈ couponLastTouchStep r last e ↔
      i ∈ last ∨ (r e = true ∧ i = e) := by
  cases hr : r e with
  | false =>
      simp [couponLastTouchStep, hr]
  | true =>
      rw [show couponLastTouchStep r last e =
        last.erase e ++ [e] by
          simp [couponLastTouchStep, hr]]
      constructor
      · intro hi
        rcases List.mem_append.mp hi with he | ht
        · exact Or.inl (List.mem_of_mem_erase he)
        · have heq : i = e := by simpa using ht
          exact Or.inr ⟨rfl, heq⟩
      · intro hi
        rcases hi with hl | ⟨_, heq⟩
        · by_cases hie : i = e
          · subst i
            exact List.mem_append.mpr (Or.inr (by simp))
          · exact List.mem_append.mpr
              (Or.inl ((List.mem_erase_of_ne hie).mpr hl))
        · subst i
          exact List.mem_append.mpr (Or.inr (by simp))

/-- Independent word induction: the touched set after any
suffix is the union of the initial register and the protected
labels occurring within the suffix. -/
theorem couponNodeLastTouchFoldMembership {n : Nat}
    (r : Fin n → Bool) :
    ∀ (word last : List (Fin n)) (i : Fin n),
      i ∈ word.foldl (couponLastTouchStep r) last ↔
        i ∈ last ∨ (r i = true ∧ i ∈ word) := by
  intro word
  induction word with
  | nil =>
      intro last i
      simp
  | cons e rest ih =>
      intro last i
      change
        i ∈ rest.foldl (couponLastTouchStep r)
          (couponLastTouchStep r last e) ↔
        i ∈ last ∨ (r i = true ∧ i ∈ (e :: rest))
      rw [ih (couponLastTouchStep r last e) i]
      rw [couponNodeLastTouchStepMembership r last e i]
      constructor
      · intro h
        rcases h with h | h
        · rcases h with hl | ⟨hre, hie⟩
          · exact Or.inl hl
          · subst i
            exact Or.inr ⟨hre, by simp⟩
        · exact Or.inr ⟨h.1, by simp [h.2]⟩
      · intro h
        rcases h with hl | ⟨hri, him⟩
        · exact Or.inl (Or.inl hl)
        · have hh : i = e ∨ i ∈ rest := by
            simpa only [List.mem_cons] using him
          rcases hh with he | hrest
          · subst i
            exact Or.inl (Or.inr ⟨hri, rfl⟩)
          · exact Or.inr ⟨hri, hrest⟩

/-- Membership of the actual last-touch list is equivalent to
having been selected while the corresponding mask was protected. -/
theorem couponNodeLastTouchMembership {n : Nat}
    (r : Fin n → Bool) (word : List (Fin n))
    (i : Fin n) :
    i ∈ couponLastTouch r word ↔
      r i = true ∧ i ∈ word := by
  have hh := couponNodeLastTouchFoldMembership r word [] i
  simpa [couponLastTouch] using hh

/-- A reachable cover has touched precisely the protected
physical edges no longer present in its remaining mask. -/
theorem couponNodeReachableCoverTouchedIff {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (mask : Fin n → Bool) (word : List (Fin n))
    (i : Fin n)
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .covering mask word) :
    i ∈ couponLastTouch
        (fun e : Fin n =>
          canonicalMask ((compileAdvice q).t + 3)
            (protectedLabel s e)) word ↔
      canonicalMask ((compileAdvice q).t + 3)
        (protectedLabel s i) = true ∧ mask i = false := by
  rw [couponNodeLastTouchMembership
    (fun e : Fin n =>
      canonicalMask ((compileAdvice q).t + 3)
        (protectedLabel s e)) word i]
  have hm := couponNodeReachableCoverMaskMembership
    ring fixed s a mask word i hreach hphase
  constructor
  · intro ⟨hr, hi⟩
    refine ⟨hr, ?_⟩
    cases hmask : mask i with
    | false =>
        rfl
    | true =>
        have hnot : i ∉ word := (hm.mp hmask).2
        exact False.elim (hnot hi)
  · intro ⟨hr, hmask⟩
    refine ⟨hr, ?_⟩
    by_cases hi : i ∈ word
    · exact hi
    · have hp : mask i = true := hm.mpr ⟨hr, hi⟩
      rw [hmask] at hp
      cases hp

/-- Highest final selected coupon: the reverse recognizer
removes that label from the outstanding threshold. -/
theorem couponNodeLastAcceptLargestLast {n : Nat}
    (M : Nat) (word : List (Fin n)) (e : Fin n)
    (he : e.val + 1 = M) :
    lastAccept M (word ++ [e]) =
      orderedAccept (M - 1) word.reverse := by
  simp only [lastAccept, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append,
    orderedAccept, if_pos he]

/-- A final selected label outside the first M coupons
is invisible to the reverse last-order recognizer. -/
theorem couponNodeLastAcceptOutsideLast {n : Nat}
    (M : Nat) (word : List (Fin n)) (e : Fin n)
    (hout : M ≤ e.val) :
    lastAccept M (word ++ [e]) = lastAccept M word := by
  have hne : ¬ e.val + 1 = M := by omega
  simp only [lastAccept, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append,
    orderedAccept, if_neg hne, if_pos hout]

/-- Selecting a required label below M-1 as the final label
makes the increasing last-occurrence condition false. -/
theorem couponNodeLastAcceptWrongLast {n : Nat}
    (M : Nat) (word : List (Fin n)) (e : Fin n)
    (hlow : e.val + 1 < M) :
    lastAccept M (word ++ [e]) = 0 := by
  have hne : ¬ e.val + 1 = M := by omega
  have hnot : ¬ M ≤ e.val := by omega
  simp only [lastAccept, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append,
    orderedAccept, if_neg hne, if_neg hnot]

/-!
STOP at item (1), the final pointwise ordering invariant. The missing theorem is the
pointwise equivalence, for a completed first-cover word,

  lastAccept M (word.map (protectedLabel s)) = 1
    iff the rotated protected last-touch register is [0,...,M-1].

It requires a separate induction linking the reverse-scanning
orderedAccept recognizer to chronological last-touch updates, and
the proof that the last-touch register contains exactly the visited
protected labels. The two proved invariant families above do not
alone imply the ordered equality.

Do not replace that local equivalence by the
protected_coupon_factorial or coupon_first_cover_factorial
total-word count: a global counting identity does not prove the
needed successor-wise terminal payoff.

Consequently the conditional F_k transition, its complete
cover drift, seen-flag soundness, launch/scan drift, start-value
certificate, and final CouponJointBudgetOnFailure t=2,3 instances
are not asserted here.
-/

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount)

/-!
This section supplies the independent lastAccept/lastTouch order
induction, its coherent F_k transition, the physical finite-edge
partition, the terminal-aware order harmonic equation, and exact
cover drift at widths two and three.

The next requested item, failure-scoped seen-flag soundness, is
refuted by the preserved launch transition. Complete concrete
counterexample candidates appear after the cover drift. No positive
seen-soundness, launch/scan drift, start-budget or final joint-budget
theorem is asserted here.
-/

/-- A chronological word induction whose induction step appends
one selected edge. -/
theorem couponNodeWordSnocInduction {n : Nat}
    (P : List (Fin n) → Prop)
    (hnil : P [])
    (hsnoc : ∀ (word : List (Fin n)) (e : Fin n),
      P word → P (word ++ [e]))
    (word : List (Fin n)) : P word := by
  have hreverse : ∀ xs : List (Fin n), P xs.reverse := by
    intro xs
    induction xs with
    | nil =>
        exact hnil
    | cons e xs ih =>
        simpa only [List.reverse_cons] using
          hsnoc xs.reverse e ih
  have h := hreverse word.reverse
  simpa only [List.reverse_reverse] using h

/-- Restricting a last-touch register commutes with one touch.
This identity does not need Nodup. -/
theorem couponNodeLastTouchStepFilter {n : Nat}
    (r p : Fin n → Bool)
    (last : List (Fin n)) (e : Fin n) :
    (couponLastTouchStep r last e).filter p =
      couponLastTouchStep (fun i => r i && p i)
        (last.filter p) e := by
  cases hr : r e with
  | false =>
      simp [couponLastTouchStep, hr]
  | true =>
      cases hp : p e with
      | false =>
          have he : e ∉ last.filter p := by
            intro hmem
            have htrue := (List.mem_filter.mp hmem).2
            rw [hp] at htrue
            cases htrue
          have herase :
              (last.erase e).filter p = last.filter p := by
            rw [← List.erase_filter]
            exact List.erase_of_not_mem he
          simpa [couponLastTouchStep, hr, hp,
            List.filter_append] using herase
      | true =>
          simp [couponLastTouchStep, hr, hp,
            List.filter_append, List.erase_filter]

/-- Restricting the chronological last-touch fold is the same
as restricting its protected predicate. -/
theorem couponNodeLastTouchFilter {n : Nat}
    (r p : Fin n → Bool) (word : List (Fin n)) :
    (couponLastTouch r word).filter p =
      couponLastTouch (fun i => r i && p i) word := by
  refine couponNodeWordSnocInduction
    (fun w : List (Fin n) =>
      (couponLastTouch r w).filter p =
        couponLastTouch (fun i => r i && p i) w)
    ?_ ?_ word
  · simp [couponLastTouch]
  · intro w e ih
    rw [couponLastTouch_snoc, couponNodeLastTouchStepFilter,
      ih, couponLastTouch_snoc]

/-- A lower canonical threshold can be extracted from any
higher-threshold last-touch register. -/
theorem couponNodeLastTouchThreshold {n : Nat}
    (M k : Nat) (word : List (Fin n)) (hk : k ≤ M) :
    (couponLastTouch (canonicalMask M) word).filter
        (canonicalMask k) =
      couponLastTouch (canonicalMask k) word := by
  have hmask :
      (fun e : Fin n => canonicalMask M e && canonicalMask k e) =
        canonicalMask k := by
    funext e
    by_cases he : e.val < k
    · have heM : e.val < M := by omega
      simp [canonicalMask, he, heM]
    · simp [canonicalMask, he]
  rw [couponNodeLastTouchFilter, hmask]

/-- Erasing the highest protected label leaves exactly the
last-touch register for the next lower threshold. -/
theorem couponNodeLastTouchTopErase {n : Nat}
    (M : Nat) (word : List (Fin n)) (e : Fin n)
    (he : e.val + 1 = M) :
    (couponLastTouch (canonicalMask M) word).erase e =
      couponLastTouch (canonicalMask (M - 1)) word := by
  have hfilter :
      (couponLastTouch (canonicalMask M) word).filter
          (fun x => x != e) =
        (couponLastTouch (canonicalMask M) word).filter
          (canonicalMask (M - 1)) := by
    apply List.filter_congr
    intro x hx
    have hxM : x.val < M := by
      have hprotected :=
        (couponNodeLastTouchMembership
          (canonicalMask M) word x).mp hx
      simpa [canonicalMask] using hprotected.1
    by_cases hxe : x = e
    · have hfalse : ¬ e.val < M - 1 := by omega
      simp [hxe, canonicalMask, hfalse]
    · have hxne : x.val ≠ e.val := by
        intro hval
        exact hxe (Fin.ext hval)
      have hsmall : x.val < M - 1 := by omega
      simp [canonicalMask, hxe, hsmall]
  calc
    (couponLastTouch (canonicalMask M) word).erase e =
        (couponLastTouch (canonicalMask M) word).filter
          (fun x => x != e) :=
      (couponNodeLastTouchNodup
        (canonicalMask M) word).erase_eq_filter e
    _ = (couponLastTouch (canonicalMask M) word).filter
          (canonicalMask (M - 1)) := hfilter
    _ = couponLastTouch (canonicalMask (M - 1)) word :=
      couponNodeLastTouchThreshold
        M (M - 1) word (by omega)

/-- The final entry of a nonempty canonical increasing list. -/
theorem couponNodeRangeLast (M : Nat) (hM : 0 < M) :
    List.range M = List.range (M - 1) ++ [M - 1] := by
  have hsucc : M = Nat.succ (M - 1) := by omega
  calc
    List.range M = List.range (Nat.succ (M - 1)) :=
      congrArg List.range hsucc
    _ = List.range (M - 1) ++ [M - 1] :=
      List.range_succ

/-- Pointwise order invariant, proved by its own chronological
word induction. It holds for every word and every threshold. -/
theorem couponNodeLastAcceptLastTouchIff {n : Nat}
    (M : Nat) (word : List (Fin n)) :
    lastAccept M word = 1 ↔
      (couponLastTouch (canonicalMask M) word).map
        (fun e => e.val) = List.range M := by
  have hword :
      ∀ k : Nat,
        lastAccept k word = 1 ↔
          (couponLastTouch (canonicalMask k) word).map
            (fun e => e.val) = List.range k := by
    refine couponNodeWordSnocInduction
      (fun w : List (Fin n) =>
        ∀ k : Nat,
          lastAccept k w = 1 ↔
            (couponLastTouch (canonicalMask k) w).map
              (fun e => e.val) = List.range k)
      ?_ ?_ word
    · intro k
      cases k with
      | zero =>
          simp [lastAccept, orderedAccept, couponLastTouch]
      | succ k =>
          simp [lastAccept, orderedAccept, couponLastTouch,
            List.range_succ_eq_map]
    · intro w e ih k
      by_cases htop : e.val + 1 = k
      · have hmask : canonicalMask k e = true := by
          have hlt : e.val < k := by omega
          simp [canonicalMask, hlt]
        have herase :=
          couponNodeLastTouchTopErase k w e htop
        have htouch :
            couponLastTouch (canonicalMask k) (w ++ [e]) =
              couponLastTouch (canonicalMask (k - 1)) w ++ [e] := by
          rw [couponLastTouch_snoc]
          simpa [couponLastTouchStep, hmask] using
            congrArg (fun last : List (Fin n) => last ++ [e])
              herase
        have hsub : k - 1 = e.val := by omega
        have hrange :
            List.range k = List.range (k - 1) ++ [e.val] := by
          calc
            List.range k = List.range (e.val + 1) :=
              congrArg List.range htop.symm
            _ = List.range e.val ++ [e.val] :=
              List.range_succ
            _ = List.range (k - 1) ++ [e.val] := by
              rw [hsub]
        rw [couponNodeLastAcceptLargestLast k w e htop]
        change lastAccept (k - 1) w = 1 ↔
          (couponLastTouch (canonicalMask k) (w ++ [e])).map
            (fun x => x.val) = List.range k
        rw [ih (k - 1), htouch, List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [hrange]
        constructor
        · intro h
          rw [h]
        · intro h
          exact List.append_inj_left' h rfl
      · by_cases hout : k ≤ e.val
        · have hmask : canonicalMask k e = false := by
            have hnot : ¬ e.val < k := by omega
            simp [canonicalMask, hnot]
          have htouch :
              couponLastTouch (canonicalMask k) (w ++ [e]) =
                couponLastTouch (canonicalMask k) w := by
            rw [couponLastTouch_snoc]
            exact couponLastTouch_outside
              (canonicalMask k)
              (couponLastTouch (canonicalMask k) w) e hmask
          rw [couponNodeLastAcceptOutsideLast k w e hout, htouch]
          exact ih k
        · have hlow : e.val + 1 < k := by omega
          have hmask : canonicalMask k e = true := by
            have hlt : e.val < k := by omega
            simp [canonicalMask, hlt]
          have htouch :
              couponLastTouch (canonicalMask k) (w ++ [e]) =
                (couponLastTouch (canonicalMask k) w).erase e ++ [e] := by
            rw [couponLastTouch_snoc]
            simp [couponLastTouchStep, hmask]
          rw [couponNodeLastAcceptWrongLast k w e hlow]
          constructor
          · intro h
            omega
          · intro h
            rw [htouch, List.map_append,
              couponNodeRangeLast k (by omega)] at h
            have hs :
                ((couponLastTouch (canonicalMask k) w).erase e).map
                    (fun x => x.val) ++ [e.val] =
                  List.range (k - 1) ++ [k - 1] := by
              simpa only [List.map_cons, List.map_nil] using h
            have hlast : [e.val] = [k - 1] :=
              List.append_inj_right' hs rfl
            have hval : e.val = k - 1 :=
              (List.cons.inj hlast).1
            omega
  exact hword M


/-- Injective relabeling commutes with erasing one label. -/
theorem couponOrderMapErase {n m : Nat}
    (f : Fin n → Fin m)
    (hf : ∀ a b : Fin n, f a = f b → a = b)
    (e : Fin n) :
    ∀ xs : List (Fin n),
      (xs.erase e).map f = (xs.map f).erase (f e) := by
  intro xs
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      by_cases hxe : x = e
      · subst x
        simp
      · have hfe : f x ≠ f e := by
          intro h
          exact hxe (hf x e h)
        have hb : ¬ (x == e) := by
          simpa only [beq_iff_eq] using hxe
        have hfb : ¬ (f x == f e) := by
          simpa only [beq_iff_eq] using hfe
        simp only [List.map_cons, List.erase_cons_tail hb,
          List.erase_cons_tail hfb, ih]

theorem couponOrderLastTouchStepMap {n m : Nat}
    (f : Fin n → Fin m)
    (hf : ∀ a b : Fin n, f a = f b → a = b)
    (p : Fin m → Bool) (last : List (Fin n)) (e : Fin n) :
    (couponLastTouchStep (fun i => p (f i)) last e).map f =
      couponLastTouchStep p (last.map f) (f e) := by
  cases hp : p (f e) with
  | false =>
      simp [couponLastTouchStep, hp]
  | true =>
      simp [couponLastTouchStep, hp, couponOrderMapErase f hf]

theorem couponOrderLastTouchFoldMap {n m : Nat}
    (f : Fin n → Fin m)
    (hf : ∀ a b : Fin n, f a = f b → a = b)
    (p : Fin m → Bool) :
    ∀ word last : List (Fin n),
      (word.foldl (couponLastTouchStep (fun i => p (f i))) last).map f =
        (word.map f).foldl (couponLastTouchStep p) (last.map f) := by
  intro word
  induction word with
  | nil =>
      intro last
      rfl
  | cons e rest ih =>
      intro last
      change
        (rest.foldl (couponLastTouchStep (fun i => p (f i)))
          (couponLastTouchStep (fun i => p (f i)) last e)).map f =
        (rest.map f).foldl (couponLastTouchStep p)
          (couponLastTouchStep p (last.map f) (f e))
      rw [ih, couponOrderLastTouchStepMap f hf p last e]

theorem couponOrderLastTouchMap {n m : Nat}
    (f : Fin n → Fin m)
    (hf : ∀ a b : Fin n, f a = f b → a = b)
    (p : Fin m → Bool) (word : List (Fin n)) :
    (couponLastTouch (fun i => p (f i)) word).map f =
      couponLastTouch p (word.map f) := by
  exact couponOrderLastTouchFoldMap f hf p word []

theorem couponOrderProtectedLabelInjective {n : Nat}
    (s : Fin n) (x y : Fin n)
    (h : protectedLabel s x = protectedLabel s y) : x = y := by
  have hh := congrArg (rotate (certSite s (n - 2))) h
  simpa only [protectedLabel, rotate_unrotate] using hh

/-- Rotation preserves the entire chronological last-touch register. -/
theorem couponNodeRotatedLastTouchMap {n : Nat}
    (s : Fin n) (M : Nat) (word : List (Fin n)) :
    (couponLastTouch
      (fun e : Fin n => canonicalMask M (protectedLabel s e))
      word).map (protectedLabel s) =
      couponLastTouch (canonicalMask M) (word.map (protectedLabel s)) := by
  exact couponOrderLastTouchMap (protectedLabel s)
    (couponOrderProtectedLabelInjective s) (canonicalMask M) word

theorem couponOrderFilterMap {n m : Nat}
    (f : Fin n → Fin m) (p : Fin m → Bool) :
    ∀ xs : List (Fin n),
      (xs.filter (fun e => p (f e))).map f =
        (xs.map f).filter p := by
  intro xs
  induction xs with
  | nil =>
      rfl
  | cons e xs ih =>
      cases hp : p (f e) with
      | false =>
          simp [hp, ih]
      | true =>
          simp [hp, ih]

/-- The requested pointwise order invariant, strengthened to all words.
Neither a first-cover hypothesis nor an aggregate counting theorem is used. -/
theorem couponNodeRotatedLastAcceptLastTouchIff {n : Nat}
    (s : Fin n) (M : Nat) (word : List (Fin n)) :
    lastAccept M (word.map (protectedLabel s)) = 1 ↔
      (couponLastTouch
        (fun e : Fin n => canonicalMask M (protectedLabel s e))
        word).map (fun e => (protectedLabel s e).val) = List.range M := by
  rw [couponNodeLastAcceptLastTouchIff,
    ← couponNodeRotatedLastTouchMap s M word]
  simp only [List.map_map] <;> rfl

/-- A prefix-order indicator is the same reverse recognizer at its
own threshold, including incomplete chronological words. -/
theorem couponNodePrefixOrderedIff {n : Nat}
    (s : Fin n) (M k : Nat) (word : List (Fin n))
    (hkm : k ≤ M) :
    couponNodePrefixOrdered s M k word = true ↔
      lastAccept k (word.map (protectedLabel s)) = 1 := by
  have hlist :
      ((couponLastTouch
        (fun e : Fin n => canonicalMask M (protectedLabel s e))
        word).filter
          (fun e => decide ((protectedLabel s e).val < k))).map
            (fun e => (protectedLabel s e).val) =
        (couponLastTouch (canonicalMask k)
          (word.map (protectedLabel s))).map (fun e => e.val) := by
    calc
      ((couponLastTouch
          (fun e : Fin n => canonicalMask M (protectedLabel s e))
          word).filter
            (fun e => decide ((protectedLabel s e).val < k))).map
              (fun e => (protectedLabel s e).val) =
          (((couponLastTouch
            (fun e : Fin n => canonicalMask M (protectedLabel s e))
            word).filter
              (fun e => canonicalMask k (protectedLabel s e))).map
                (protectedLabel s)).map (fun e => e.val) := by
              simp only [List.map_map, canonicalMask] <;> rfl
      _ = (((couponLastTouch
            (fun e : Fin n => canonicalMask M (protectedLabel s e))
            word).map (protectedLabel s)).filter
              (canonicalMask k)).map (fun e => e.val) := by
            rw [couponOrderFilterMap]
      _ = ((couponLastTouch (canonicalMask M)
            (word.map (protectedLabel s))).filter
              (canonicalMask k)).map (fun e => e.val) := by
            rw [couponNodeRotatedLastTouchMap]
      _ = (couponLastTouch (canonicalMask k)
            (word.map (protectedLabel s))).map (fun e => e.val) := by
            rw [couponNodeLastTouchThreshold M k
              (word.map (protectedLabel s)) hkm]
  unfold couponNodePrefixOrdered
  dsimp only
  rw [hlist]
  simp only [decide_eq_true_eq]
  exact (couponNodeLastAcceptLastTouchIff k
    (word.map (protectedLabel s))).symm


/-- With the exact first-cover mask, an ordered prefix has no
remaining unseen label below its threshold. -/
theorem couponNodePrefixOrderedImpliesSeen {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (k : Nat)
    (hmask : mask = word.foldl maskDrop
      (fun e : Fin n => canonicalMask M (protectedLabel s e)))
    (hordered : couponNodePrefixOrdered s M k word = true) :
    couponNodePrefixSeen s mask k = true := by
  have hlist :
      (((couponLastTouch
        (fun e : Fin n => canonicalMask M (protectedLabel s e))
        word).filter
          (fun e => decide ((protectedLabel s e).val < k))).map
            (fun e => (protectedLabel s e).val)) = List.range k := by
    exact of_decide_eq_true hordered
  have hrow (i : Fin n) :
      (if mask i = true ∧ (protectedLabel s i).val < k
        then (1 : Nat) else 0) = 0 := by
    by_cases hi : mask i = true ∧ (protectedLabel s i).val < k
    · have hrange :
          (protectedLabel s i).val ∈ List.range k :=
        List.mem_range.mpr hi.2
      rw [← hlist] at hrange
      obtain ⟨e, he, hei⟩ := List.mem_map.mp hrange
      have hlabel :
          protectedLabel s e = protectedLabel s i :=
        Fin.ext hei
      have hsame : e = i := by
        have hh :=
          congrArg (rotate (certSite s (n - 2))) hlabel
        simpa only [protectedLabel, rotate_unrotate] using hh
      have heword : e ∈ word :=
        ((couponNodeLastTouchMembership
          (fun a : Fin n =>
            canonicalMask M (protectedLabel s a))
          word e).mp (List.mem_filter.mp he).1).2
      have hiword : i ∈ word := by
        rw [← hsame]
        exact heword
      have hbit :
          (word.foldl maskDrop
            (fun e : Fin n =>
              canonicalMask M (protectedLabel s e))) i = true := by
        rw [← hmask]
        exact hi.1
      have hnot : i ∉ word :=
        ((couponNodeMaskFoldMembership
          (fun e : Fin n =>
            canonicalMask M (protectedLabel s e))
          word i).mp hbit).2
      exact False.elim (hnot hiword)
    · simp [hi]
  have hsum :
      (List.ofFn (fun e : Fin n =>
        if mask e = true ∧ (protectedLabel s e).val < k
        then (1 : Nat) else 0)).sum = 0 := by
    calc
      _ = (List.ofFn (fun _ : Fin n => (0 : Nat))).sum :=
        ofFn_sum_eq _ _ hrow
      _ = 0 := by
        simp only [ofFn_sum_const, Nat.mul_zero]
  simp [couponNodePrefixSeen, hsum]

/-- The exact Boolean F_k used in couponNodeCoverWeight. -/
def couponNodePrefixIndicator {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (k : Nat) : Bool :=
  couponNodePrefixSeen s mask k &&
    couponNodePrefixOrdered s M k word

/-- Coherence makes the seen test redundant once the complete
increasing prefix is present in the last-touch register. -/
theorem couponNodePrefixIndicatorEqOrdered {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (k : Nat)
    (hmask : mask = word.foldl maskDrop
      (fun e : Fin n => canonicalMask M (protectedLabel s e))) :
    couponNodePrefixIndicator s M mask word k =
      couponNodePrefixOrdered s M k word := by
  cases ho : couponNodePrefixOrdered s M k word with
  | false =>
      simp [couponNodePrefixIndicator, ho]
  | true =>
      have hs := couponNodePrefixOrderedImpliesSeen
        s M mask word k hmask ho
      simp [couponNodePrefixIndicator, hs, ho]

/-- Pointwise recognizer identity for a coherent cover prefix. -/
theorem couponNodePrefixIndicatorIff {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (k : Nat)
    (hmask : mask = word.foldl maskDrop
      (fun e : Fin n => canonicalMask M (protectedLabel s e)))
    (hkm : k ≤ M) :
    couponNodePrefixIndicator s M mask word k = true ↔
      lastAccept k (word.map (protectedLabel s)) = 1 := by
  rw [couponNodePrefixIndicatorEqOrdered
    s M mask word k hmask]
  exact couponNodePrefixOrderedIff s M k word hkm

/-- Exact cover coherence is preserved also at the final touch. -/
theorem couponNodeCoverMaskFoldSnoc {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (e : Fin n)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i))) :
    maskDrop mask e = (word ++ [e]).foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)) := by
  rw [List.foldl_append]
  change maskDrop mask e =
    maskDrop
      (word.foldl maskDrop
        (fun i : Fin n => canonicalMask M (protectedLabel s i))) e
  rw [hmask]

theorem couponNodeBoolEqOfTrueIff (a b : Bool)
    (h : (a = true ↔ b = true)) : a = b := by
  cases a <;> cases b <;> simp at h ⊢

/-- A touch whose rotated label is at least k leaves F_k fixed. -/
theorem couponNodePrefixIndicatorNextOutside {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (e : Fin n) (k : Nat)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (hkm : k ≤ M) (hout : k ≤ (protectedLabel s e).val) :
    couponNodePrefixIndicator s M (maskDrop mask e)
        (word ++ [e]) k =
      couponNodePrefixIndicator s M mask word k := by
  apply couponNodeBoolEqOfTrueIff
  rw [couponNodePrefixIndicatorIff
    s M (maskDrop mask e) (word ++ [e]) k
    (couponNodeCoverMaskFoldSnoc s M mask word e hmask) hkm,
    couponNodePrefixIndicatorIff s M mask word k hmask hkm]
  rw [List.map_append, List.map_cons, List.map_nil,
    couponNodeLastAcceptOutsideLast
      k (word.map (protectedLabel s)) (protectedLabel s e) hout]

/-- Touching rotated label k-1 replaces F_k by the old F_(k-1). -/
theorem couponNodePrefixIndicatorNextLargest {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (e : Fin n) (k : Nat)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (hkm : k ≤ M) (htop : (protectedLabel s e).val + 1 = k) :
    couponNodePrefixIndicator s M (maskDrop mask e)
        (word ++ [e]) k =
      couponNodePrefixIndicator s M mask word (k - 1) := by
  have hprev : k - 1 ≤ M := by omega
  apply couponNodeBoolEqOfTrueIff
  rw [couponNodePrefixIndicatorIff
    s M (maskDrop mask e) (word ++ [e]) k
    (couponNodeCoverMaskFoldSnoc s M mask word e hmask) hkm,
    couponNodePrefixIndicatorIff
      s M mask word (k - 1) hmask hprev]
  rw [List.map_append, List.map_cons, List.map_nil,
    couponNodeLastAcceptLargestLast
      k (word.map (protectedLabel s)) (protectedLabel s e) htop] <;> rfl

/-- A touch below k-1 makes the newest prefix label too small. -/
theorem couponNodePrefixIndicatorNextWrong {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (e : Fin n) (k : Nat)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (hkm : k ≤ M) (hlow : (protectedLabel s e).val + 1 < k) :
    couponNodePrefixIndicator s M (maskDrop mask e)
        (word ++ [e]) k = false := by
  apply couponNodeBoolEqOfTrueIff
  rw [couponNodePrefixIndicatorIff
    s M (maskDrop mask e) (word ++ [e]) k
    (couponNodeCoverMaskFoldSnoc s M mask word e hmask) hkm]
  rw [List.map_append, List.map_cons, List.map_nil,
    couponNodeLastAcceptWrongLast
      k (word.map (protectedLabel s)) (protectedLabel s e) hlow]
  simp

/-- The complete coherent F_k update for one selected physical edge. -/
theorem couponNodePrefixIndicatorNext {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (e : Fin n) (k : Nat)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (hkm : k ≤ M) :
    couponNodePrefixIndicator s M (maskDrop mask e)
        (word ++ [e]) k =
      if k ≤ (protectedLabel s e).val then
        couponNodePrefixIndicator s M mask word k
      else if k = (protectedLabel s e).val + 1 then
        couponNodePrefixIndicator s M mask word
          (protectedLabel s e).val
      else false := by
  by_cases hout : k ≤ (protectedLabel s e).val
  · rw [if_pos hout]
    exact couponNodePrefixIndicatorNextOutside
      s M mask word e k hmask hkm hout
  · rw [if_neg hout]
    by_cases htop : k = (protectedLabel s e).val + 1
    · rw [if_pos htop]
      have hprev : k - 1 = (protectedLabel s e).val := by omega
      have hh := couponNodePrefixIndicatorNextLargest
        s M mask word e k hmask hkm htop.symm
      simpa only [hprev] using hh
    · rw [if_neg htop]
      have hlow : (protectedLabel s e).val + 1 < k := by omega
      exact couponNodePrefixIndicatorNextWrong
        s M mask word e k hmask hkm hlow

/-- The final coupon's last-order payoff is the previous F_(M-1). -/
theorem couponNodeCoverTerminalOrderIff {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (e : Fin n)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (htop : (protectedLabel s e).val + 1 = M) :
    lastAccept M ((word ++ [e]).map (protectedLabel s)) = 1 ↔
      couponNodePrefixIndicator s M mask word (M - 1) = true := by
  rw [← couponNodePrefixIndicatorIff
    s M (maskDrop mask e) (word ++ [e]) M
    (couponNodeCoverMaskFoldSnoc s M mask word e hmask)
    (Nat.le_refl M)]
  rw [couponNodePrefixIndicatorNextLargest
    s M mask word e M hmask (Nat.le_refl M) htop]

/-- Reachability supplies the exact mask/word coherence. -/
theorem couponNodeReachablePrefixIndicatorNext {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (mask : Fin n → Bool) (word : List (Fin n))
    (e : Fin n) (k : Nat)
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .covering mask word)
    (hkm : k ≤ (compileAdvice q).t + 3) :
    couponNodePrefixIndicator s ((compileAdvice q).t + 3)
        (maskDrop mask e) (word ++ [e]) k =
      if k ≤ (protectedLabel s e).val then
        couponNodePrefixIndicator s ((compileAdvice q).t + 3)
          mask word k
      else if k = (protectedLabel s e).val + 1 then
        couponNodePrefixIndicator s ((compileAdvice q).t + 3)
          mask word (protectedLabel s e).val
      else false := by
  exact couponNodePrefixIndicatorNext
    s ((compileAdvice q).t + 3) mask word e k
    (couponNodeReachableCoverMaskFold
      ring fixed s a mask word hreach hphase) hkm


/-- The final-label indicator is precisely the bit at its
unique physical edge. -/
theorem couponNodeFinalUnseenAtTop {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (top : Fin n)
    (htop : (protectedLabel s top).val + 1 = M) :
    couponNodeFinalUnseen s M mask = mask top := by
  have hinj (i : Fin n)
      (hi : (protectedLabel s i).val + 1 = M) : i = top := by
    have hv : (protectedLabel s i).val =
        (protectedLabel s top).val := by omega
    have he : protectedLabel s i = protectedLabel s top :=
      Fin.ext hv
    calc
      i = rotate (certSite s (n - 2)) (protectedLabel s i) :=
        (rotate_unrotate (certSite s (n - 2)) i).symm
      _ = rotate (certSite s (n - 2)) (protectedLabel s top) :=
        congrArg (rotate (certSite s (n - 2))) he
      _ = top := rotate_unrotate (certSite s (n - 2)) top
  have hrow (i : Fin n) :
      (if mask i = true ∧ (protectedLabel s i).val + 1 = M
        then (1 : Nat) else 0) =
      (if i = top then (if mask top = true then 1 else 0) else 0) := by
    by_cases hi : i = top
    · rw [hi]
      simp [htop]
    · have hne : ¬ (protectedLabel s i).val + 1 = M := by
        intro hl
        exact hi (hinj i hl)
      simp [hi, hne]
  have hs := ofFn_sum_eq _ _ hrow
  rw [FreshFixed.sum_spike] at hs
  unfold couponNodeFinalUnseen
  rw [hs]
  cases hm : mask top <;> simp [hm]

/-- The unique physical top edge has rotated label M-1. -/
theorem couponNodeProtectedTopLabel {n : Nat}
    (s : Fin n) (M : Nat) (hM : 0 < M) (hn : M ≤ n) :
    (protectedLabel s (certSite s (n - 2 + (M - 1)))).val + 1 = M := by
  let top : Fin n := ⟨M - 1, by omega⟩
  have he : rotate (certSite s (n - 2)) top =
      certSite s (n - 2 + (M - 1)) :=
    certSite_add s (n - 2) (M - 1)
  change (unrotate (certSite s (n - 2))
    (certSite s (n - 2 + (M - 1)))).val + 1 = M
  rw [← he, unrotate_rotate]
  change M - 1 + 1 = M
  omega

theorem couponNodeFinalUnseenCanonical {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (hM : 0 < M) (hn : M ≤ n) :
    couponNodeFinalUnseen s M mask =
      mask (certSite s (n - 2 + (M - 1))) := by
  exact couponNodeFinalUnseenAtTop s M mask
    (certSite s (n - 2 + (M - 1)))
    (couponNodeProtectedTopLabel s M hM hn)

/-- Pointwise meaning of the no-unseen-prefix test. -/
theorem couponNodePrefixSeenIff {n : Nat}
    (s : Fin n) (mask : Fin n → Bool) (k : Nat) :
    couponNodePrefixSeen s mask k = true ↔
      ∀ i : Fin n, (protectedLabel s i).val < k → mask i = false := by
  let r : Fin n → Bool :=
    fun i => if (protectedLabel s i).val < k then mask i else false
  have hs :
      (List.ofFn (fun i : Fin n =>
        if mask i = true ∧ (protectedLabel s i).val < k
        then (1 : Nat) else 0)).sum = maskSize r := by
    unfold maskSize
    apply ofFn_sum_eq
    intro i
    by_cases hi : (protectedLabel s i).val < k
    · simp [r, hi]
    · simp [r, hi]
  unfold couponNodePrefixSeen
  rw [hs]
  simp only [decide_eq_true_eq, maskSize_eq_zero_iff]
  constructor
  · intro h i hi
    simpa [r, hi] using h i
  · intro h i
    by_cases hi : (protectedLabel s i).val < k
    · simpa [r, hi] using h i hi
    · simp [r, hi]

/-- A coherent surviving mask bit is necessarily protected. -/
theorem couponNodeCoherentMaskProtected {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n))
    (hcoh : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (i : Fin n) (hi : mask i = true) :
    (protectedLabel s i).val < M := by
  have hh : mask i = true ↔
      canonicalMask M (protectedLabel s i) = true ∧ i ∉ word := by
    rw [hcoh]
    exact couponNodeMaskFoldMembership
      (fun j : Fin n => canonicalMask M (protectedLabel s j)) word i
  have hp := (hh.mp hi).1
  simpa [canonicalMask] using hp

theorem couponNodeMaskSizePositiveOfTrue {n : Nat}
    (mask : Fin n → Bool) (i : Fin n) (hi : mask i = true) :
    0 < maskSize mask := by
  have h := coupon_maskDrop_true mask i hi
  omega

/-- Completing a nonempty mask must select a surviving bit. -/
theorem couponNodeMaskDropHitOfCompletes {n : Nat}
    (mask : Fin n → Bool) (e : Fin n)
    (hpos : 0 < maskSize mask)
    (hzero : maskSize (maskDrop mask e) = 0) :
    mask e = true := by
  cases hm : mask e with
  | false =>
      rw [coupon_maskDrop_false mask e hm] at hzero
      omega
  | true =>
      rfl

theorem couponNodeFinalUnseenDrop {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (top e : Fin n)
    (htop : (protectedLabel s top).val + 1 = M) :
    couponNodeFinalUnseen s M (maskDrop mask e) =
      if e = top then false else couponNodeFinalUnseen s M mask := by
  rw [couponNodeFinalUnseenAtTop s M (maskDrop mask e) top htop,
    couponNodeFinalUnseenAtTop s M mask top htop]
  by_cases he : e = top
  · rw [he]
    simp [maskDrop]
  · have hne : top ≠ e := Ne.symm he
    simp [maskDrop, he, hne]


/-- The kth factorial summand in the coherent order numerator. -/
def couponNodeOrderWeight (F : Nat → Bool) (k : Nat) : Nat :=
  if F k then freshFact k else 0

/-- The weight contributed when label k becomes the newest prefix label. -/
def couponNodeOrderNextWeight (F : Nat → Bool) (k : Nat) : Nat :=
  if F k then freshFact (k + 1) else 0

/-- The complete order numerator after selecting a label below M-1. -/
def couponNodeOrderRow (F : Nat → Bool) (e : Nat) : Nat :=
  ((List.range (e + 1)).map (couponNodeOrderWeight F)).sum +
    couponNodeOrderNextWeight F e

theorem couponNodeOrderNextWeightMul (F : Nat → Bool) (k : Nat) :
    couponNodeOrderNextWeight F k =
      (k + 1) * couponNodeOrderWeight F k := by
  cases h : F k <;>
    simp [couponNodeOrderNextWeight, couponNodeOrderWeight, h, freshFact]
end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount)

/-- The factorial cancellation with the final-label payoff included.
This is an induction on the threshold, not a double-sum interchange. -/
theorem couponNodeOrderRowSum (F : Nat → Bool) (R : Nat) :
    ((List.range R).map (couponNodeOrderRow F)).sum +
        couponNodeOrderNextWeight F R =
      (R + 1) *
        ((List.range (R + 1)).map (couponNodeOrderWeight F)).sum := by
  induction R with
  | zero =>
      simp [couponNodeOrderNextWeight, couponNodeOrderWeight,
        freshFact, List.range_succ]
  | succ R ih =>
      have hpre :
          ((List.range (R + 1 + 1)).map
            (couponNodeOrderWeight F)).sum =
          ((List.range (R + 1)).map
            (couponNodeOrderWeight F)).sum +
              couponNodeOrderWeight F (R + 1) := by
        rw [List.range_succ, List.map_append, List.sum_append]
        simp only [List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Nat.add_zero]
      have hrows :
          ((List.range (R + 1)).map
            (couponNodeOrderRow F)).sum =
          ((List.range R).map (couponNodeOrderRow F)).sum +
            (((List.range (R + 1)).map
              (couponNodeOrderWeight F)).sum +
                couponNodeOrderNextWeight F R) := by
        rw [List.range_succ, List.map_append, List.sum_append]
        simp only [List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Nat.add_zero, couponNodeOrderRow]
        rw [List.range_succ]
      change
        ((List.range (R + 1)).map (couponNodeOrderRow F)).sum +
            couponNodeOrderNextWeight F (R + 1) =
          (R + 1 + 1) *
            ((List.range (R + 1 + 1)).map
              (couponNodeOrderWeight F)).sum
      rw [hrows, hpre, couponNodeOrderNextWeightMul F (R + 1)]
      calc
        _ = (((List.range R).map (couponNodeOrderRow F)).sum +
              couponNodeOrderNextWeight F R) +
            ((List.range (R + 1)).map
              (couponNodeOrderWeight F)).sum +
            (R + 1 + 1) * couponNodeOrderWeight F (R + 1) := by
              ac_rfl
        _ = (R + 1) *
              ((List.range (R + 1)).map
                (couponNodeOrderWeight F)).sum +
            ((List.range (R + 1)).map
              (couponNodeOrderWeight F)).sum +
            (R + 1 + 1) * couponNodeOrderWeight F (R + 1) := by
              rw [ih]
        _ = _ := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul] <;> ac_rfl

/-- Summing the complete F_k recurrence leaves the unchanged
initial segment and one new factorial summand. -/
theorem couponNodeOrderUpdatedSum (F : Nat → Bool) (M e : Nat)
    (he : e + 1 < M) :
    ((List.range M).map (fun k =>
      if (if k ≤ e then F k
          else if k = e + 1 then F e else false)
      then freshFact k else 0)).sum =
        couponNodeOrderRow F e := by
  revert he
  induction M with
  | zero =>
      intro he
      omega
  | succ M ih =>
      intro he
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero]
      by_cases hM : M = e + 1
      · subst M
        have hprefix :
            ((List.range (e + 1)).map (fun k =>
              if (if k ≤ e then F k
                  else if k = e + 1 then F e else false)
              then freshFact k else 0)).sum =
            ((List.range (e + 1)).map
              (couponNodeOrderWeight F)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro k hk
          have hkle : k ≤ e := by
            have hlt : k < e + 1 := List.mem_range.mp hk
            omega
          simp only [if_pos hkle, couponNodeOrderWeight]
        rw [hprefix]
        have hnot : ¬ e + 1 ≤ e := by omega
        simp only [if_neg hnot, ↓reduceIte,
          couponNodeOrderRow, couponNodeOrderNextWeight]
      · have hlt : e + 1 < M := by omega
        have hnot : ¬ M ≤ e := by omega
        have hneq : ¬ M = e + 1 := hM
        rw [ih hlt]
        simp [hnot, hneq]


/-- Each protected rotated label contributes exactly one physical edge. -/
theorem couponNodeProtectedLabelSum {n : Nat}
    (s : Fin n) (M : Nat) (hM : M ≤ n) (v : Nat → Nat) :
    (List.ofFn (fun e : Fin n =>
      if (protectedLabel s e).val < M
      then v (protectedLabel s e).val else 0)).sum =
      ((List.range M).map v).sum := by
  have hbound : ∀ k, k ∈ List.range M → k < n := by
    intro k hk
    have hkm : k < M := List.mem_range.mp hk
    omega
  have hrow (e : Fin n) :
      (if (protectedLabel s e).val < M
       then v (protectedLabel s e).val else 0) =
      (if (unrotate (certSite s (n - 2)) e).val ∈ List.range M
       then v (unrotate (certSite s (n - 2)) e).val else 0) := by
    by_cases hlt : (unrotate (certSite s (n - 2)) e).val < M
    · simp [protectedLabel, List.mem_range, hlt]
    · simp [protectedLabel, List.mem_range, hlt]
  calc
    (List.ofFn (fun e : Fin n =>
      if (protectedLabel s e).val < M
      then v (protectedLabel s e).val else 0)).sum =
        (List.ofFn (fun e : Fin n =>
          if (unrotate (certSite s (n - 2)) e).val ∈ List.range M
          then v (unrotate (certSite s (n - 2)) e).val else 0)).sum :=
            ofFn_sum_eq _ _ hrow
    _ = ((List.range M).map v).sum :=
      coupon_scan_sum_future (certSite s (n - 2))
        (List.range M) (List.nodup_range (n := M)) hbound v

/-- The physical complement of the protected labels has n-M edges. -/
theorem couponNodeUnprotectedConstantSum {n : Nat}
    (s : Fin n) (M c : Nat) (hM : M ≤ n) :
    (List.ofFn (fun e : Fin n =>
      if (protectedLabel s e).val < M then 0 else c)).sum =
      (n - M) * c := by
  let r : Fin n → Bool :=
    fun e => canonicalMask M (protectedLabel s e)
  have hr : maskSize r = M := by
    exact relabeled_mask_size
      (rotate (certSite s (n - 2)))
      (unrotate (certSite s (n - 2)))
      (unrotate_rotate (certSite s (n - 2)))
      (rotate_unrotate (certSite s (n - 2))) M hM
  have hs := coupon_mask_split_sum r c 0
  rw [hr] at hs
  simpa only [r, canonicalMask, decide_eq_true_eq,
    Nat.mul_zero, Nat.add_zero] using hs

/-- Exact protected/unprotected split of the original Fin n edge sum. -/
theorem couponNodeProtectedUnprotectedSum {n : Nat}
    (s : Fin n) (M c : Nat) (hM : M ≤ n) (v : Nat → Nat) :
    (List.ofFn (fun e : Fin n =>
      if (protectedLabel s e).val < M
      then v (protectedLabel s e).val else c)).sum =
      ((List.range M).map v).sum + (n - M) * c := by
  have hrow (e : Fin n) :
      (if (protectedLabel s e).val < M
       then v (protectedLabel s e).val else c) =
      (if (protectedLabel s e).val < M
       then v (protectedLabel s e).val else 0) +
      (if (protectedLabel s e).val < M then 0 else c) := by
    by_cases he : (protectedLabel s e).val < M <;> simp [he]
  calc
    _ = (List.ofFn (fun e : Fin n =>
        (if (protectedLabel s e).val < M
         then v (protectedLabel s e).val else 0) +
        (if (protectedLabel s e).val < M then 0 else c))).sum :=
      ofFn_sum_eq _ _ hrow
    _ = ((List.range M).map v).sum + (n - M) * c := by
      rw [ofFn_sum_add, couponNodeProtectedLabelSum s M hM v,
        couponNodeUnprotectedConstantSum s M c hM]

/-- The split applied to an arbitrary physical payoff that is constant
on all unprotected edges. The protected terms use the paper's sites. -/
theorem couponNodePhysicalEdgeSum {n : Nat}
    (s : Fin n) (M c : Nat) (hM : M ≤ n) (payoff : Fin n → Nat)
    (hout : ∀ e : Fin n,
      M ≤ (protectedLabel s e).val → payoff e = c) :
    (List.ofFn payoff).sum =
      ((List.range M).map
        (fun k => payoff (certSite s (n - 2 + k)))).sum +
      (n - M) * c := by
  have hdecode (e : Fin n) :
      certSite s (n - 2 + (protectedLabel s e).val) = e := by
    calc
      _ = rotate (certSite s (n - 2)) (protectedLabel s e) :=
        (certSite_add s (n - 2) (protectedLabel s e).val).symm
      _ = e := rotate_unrotate (certSite s (n - 2)) e
  calc
    _ = (List.ofFn (fun e : Fin n =>
        if (protectedLabel s e).val < M
        then payoff (certSite s
          (n - 2 + (protectedLabel s e).val)) else c)).sum := by
      apply ofFn_sum_eq
      intro e
      by_cases he : (protectedLabel s e).val < M
      · rw [if_pos he, hdecode e]
      · rw [if_neg he]
        exact hout e (by omega)
    _ = _ :=
      couponNodeProtectedUnprotectedSum s M c hM
        (fun k => payoff (certSite s (n - 2 + k)))


/-- The final first-cover touch substitutes M! times the literal
lastAccept indicator for the ended live-cover weight. -/
def couponNodeCoverOrderPayoff {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (e : Fin n) : Nat :=
  if maskSize (maskDrop mask e) = 0 then
    freshFact M *
      lastAccept M ((word ++ [e]).map (protectedLabel s))
  else
    couponNodeCoverWeight s M (maskDrop mask e) (word ++ [e])

/-- If all lower coupons have been seen, touching the final
coupon completes the coherent mask. -/
theorem couponNodeCoherentTopCompletesOfPrefix {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (top : Fin n)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (htop : (protectedLabel s top).val + 1 = M)
    (hprefix :
      couponNodePrefixIndicator s M mask word (M - 1) = true) :
    maskSize (maskDrop mask top) = 0 := by
  have hseen : couponNodePrefixSeen s mask (M - 1) = true := by
    have hh := hprefix
    simp only [couponNodePrefixIndicator, Bool.and_eq_true] at hh
    exact hh.1
  have hclear := (couponNodePrefixSeenIff s mask (M - 1)).mp hseen
  apply (maskSize_eq_zero_iff _).mpr
  intro i
  by_cases hitop : i = top
  · subst i
    simp [maskDrop]
  · have hilow : (protectedLabel s i).val < M - 1 ∨ mask i = false := by
      cases hi : mask i with
      | false =>
          exact Or.inr rfl
      | true =>
          have hiprot :=
            couponNodeCoherentMaskProtected s M mask word hmask i hi
          have hne :
              (protectedLabel s i).val ≠
                (protectedLabel s top).val := by
            intro hh
            exact hitop
              (couponOrderProtectedLabelInjective s i top (Fin.ext hh))
          exact Or.inl (by omega)
    have hfalse : mask i = false := by
      rcases hilow with hl | hf
      · exact hclear i hl
      · exact hf
    simp [maskDrop, hitop, hfalse]

/-- The final protected label contributes the old F_(M-1),
including the live/terminal case split. -/
theorem couponNodeCoverOrderPayoffTop {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (top : Fin n)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (htop : (protectedLabel s top).val + 1 = M) :
    couponNodeCoverOrderPayoff s M mask word top =
      couponNodeOrderNextWeight
        (couponNodePrefixIndicator s M mask word) (M - 1) := by
  have hpred : M - 1 + 1 = M := by omega
  have hiff :=
    couponNodeCoverTerminalOrderIff s M mask word top hmask htop
  by_cases hprefix :
      couponNodePrefixIndicator s M mask word (M - 1) = true
  · have hzero :=
      couponNodeCoherentTopCompletesOfPrefix
        s M mask word top hmask htop hprefix
    have haccept := hiff.mpr hprefix
    simp only [List.map_append, List.map_cons, List.map_nil] at haccept
    simp [couponNodeCoverOrderPayoff, hzero, haccept,
      couponNodeOrderNextWeight, hprefix, hpred]
  · have haccept :
        lastAccept M ((word ++ [top]).map (protectedLabel s)) = 0 := by
      rcases orderedAccept_range M
        (((word ++ [top]).map (protectedLabel s)).reverse) with hz | ho
      · exact hz
      · exact False.elim (hprefix (hiff.mp ho))
    have hfinal :
        couponNodeFinalUnseen s M (maskDrop mask top) = false := by
      rw [couponNodeFinalUnseenAtTop s M (maskDrop mask top) top htop]
      simp [maskDrop]
    by_cases hzero : maskSize (maskDrop mask top) = 0
    · simp only [List.map_append, List.map_cons, List.map_nil] at haccept
      simp [couponNodeCoverOrderPayoff, hzero, haccept,
        couponNodeOrderNextWeight, hprefix]
    · simp [couponNodeCoverOrderPayoff, hzero,
        couponNodeCoverWeight, hfinal,
        couponNodeOrderNextWeight, hprefix]

/-- A nonfinal protected touch cannot complete while the final
coupon is unseen; its payoff is the exact factorial F row. -/
theorem couponNodeCoverOrderPayoffBelow {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (top e : Fin n)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (htop : (protectedLabel s top).val + 1 = M)
    (hbelow : (protectedLabel s e).val + 1 < M)
    (hfinal : couponNodeFinalUnseen s M mask = true) :
    couponNodeCoverOrderPayoff s M mask word e =
      couponNodeOrderRow
        (couponNodePrefixIndicator s M mask word)
        (protectedLabel s e).val := by
  have hneq : top ≠ e := by
    intro hh
    have hvalues := congrArg (fun i => (protectedLabel s i).val) hh
    omega
  have htopbit : mask top = true := by
    rw [← couponNodeFinalUnseenAtTop s M mask top htop]
    exact hfinal
  have hnextbit : maskDrop mask e top = true := by
    simp [maskDrop, hneq, htopbit]
  have hnonzero : maskSize (maskDrop mask e) ≠ 0 := by
    intro hz
    have hh := (maskSize_eq_zero_iff _).mp hz top
    rw [hnextbit] at hh
    cases hh
  have hnextfinal :
      couponNodeFinalUnseen s M (maskDrop mask e) = true := by
    rw [couponNodeFinalUnseenAtTop s M (maskDrop mask e) top htop]
    exact hnextbit
  unfold couponNodeCoverOrderPayoff
  rw [if_neg hnonzero]
  unfold couponNodeCoverWeight
  rw [hnextfinal]
  change
    ((List.range M).map (fun k =>
      if couponNodePrefixIndicator s M (maskDrop mask e)
          (word ++ [e]) k
      then freshFact k else 0)).sum =
    couponNodeOrderRow
      (couponNodePrefixIndicator s M mask word)
      (protectedLabel s e).val
  calc
    _ = ((List.range M).map (fun k =>
        if (if k ≤ (protectedLabel s e).val then
              couponNodePrefixIndicator s M mask word k
            else if k = (protectedLabel s e).val + 1 then
              couponNodePrefixIndicator s M mask word
                (protectedLabel s e).val
            else false)
        then freshFact k else 0)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro k hk
      have hkm : k ≤ M := by
        have hh : k < M := List.mem_range.mp hk
        omega
      rw [couponNodePrefixIndicatorNext
        s M mask word e k hmask hkm]
    _ = _ :=
      couponNodeOrderUpdatedSum
        (couponNodePrefixIndicator s M mask word)
        M (protectedLabel s e).val hbelow

/-- Once the final coupon has been seen, every successor order
payoff is zero until the live cover finishes. -/
theorem couponNodeCoverOrderPayoffFinalSeen {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (top e : Fin n)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (htop : (protectedLabel s top).val + 1 = M)
    (hpos : 0 < maskSize mask)
    (hfinal : couponNodeFinalUnseen s M mask = false) :
    couponNodeCoverOrderPayoff s M mask word e = 0 := by
  have htopbit : mask top = false := by
    rw [← couponNodeFinalUnseenAtTop s M mask top htop]
    exact hfinal
  have hnextfinal :
      couponNodeFinalUnseen s M (maskDrop mask e) = false := by
    rw [couponNodeFinalUnseenAtTop s M (maskDrop mask e) top htop]
    simp [maskDrop, htopbit]
  by_cases hzero : maskSize (maskDrop mask e) = 0
  · have hetrue := couponNodeMaskDropHitOfCompletes mask e hpos hzero
    have heprot :=
      couponNodeCoherentMaskProtected s M mask word hmask e hetrue
    have hne :
        (protectedLabel s e).val ≠ (protectedLabel s top).val := by
      intro hh
      have heq :=
        couponOrderProtectedLabelInjective s e top (Fin.ext hh)
      have hfalse : mask e = false := by rw [heq]; exact htopbit
      rw [hfalse] at hetrue
      cases hetrue
    have hlow : (protectedLabel s e).val + 1 < M := by omega
    have haccept :
        lastAccept M ((word ++ [e]).map (protectedLabel s)) = 0 := by
      rw [List.map_append, List.map_cons, List.map_nil]
      exact couponNodeLastAcceptWrongLast M
        (word.map (protectedLabel s)) (protectedLabel s e) hlow
    simp only [List.map_append, List.map_cons, List.map_nil] at haccept
    simp [couponNodeCoverOrderPayoff, hzero, haccept]
  · simp [couponNodeCoverOrderPayoff, hzero,
      couponNodeCoverWeight, hnextfinal]

/-- An unprotected selection has the unchanged live-cover weight. -/
theorem couponNodeCoverOrderPayoffOutside {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (e : Fin n)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (hpos : 0 < maskSize mask)
    (hout : M ≤ (protectedLabel s e).val) :
    couponNodeCoverOrderPayoff s M mask word e =
      couponNodeCoverWeight s M mask word := by
  have hefalse : mask e = false := by
    cases he : mask e with
    | false =>
        rfl
    | true =>
        have hprot :=
          couponNodeCoherentMaskProtected s M mask word hmask e he
        omega
  have hdrop : maskDrop mask e = mask :=
    coupon_maskDrop_false mask e hefalse
  have hnonzero : maskSize mask ≠ 0 := by omega
  have hprotected :
      canonicalMask M (protectedLabel s e) = false := by
    simp [canonicalMask, Nat.not_lt_of_ge hout]
  simp only [couponNodeCoverOrderPayoff, hdrop, if_neg hnonzero]
  exact couponNodeCoverWeightOutside s M mask word e hprotected


/-- The physical site used in the finite edge partition decodes
to exactly its protected rotated label. -/
theorem couponNodeCoverProtectedSiteLabel {n : Nat}
    (s : Fin n) (k : Nat) (hk : k < n) :
    (protectedLabel s (certSite s (n - 2 + k))).val = k := by
  let label : Fin n := ⟨k, hk⟩
  have he : rotate (certSite s (n - 2)) label =
      certSite s (n - 2 + k) :=
    certSite_add s (n - 2) k
  change (unrotate (certSite s (n - 2))
    (certSite s (n - 2 + k))).val = k
  rw [← he, unrotate_rotate] <;> rfl

/-- Complete conditional cover-order harmonic identity over the
actual Fin n scheduler, including its final-cover factorial payoff. -/
theorem couponNodeCoverOrderHarmonic {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n))
    (hM : 0 < M) (hn : M ≤ n)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i)))
    (hpos : 0 < maskSize mask) :
    (List.ofFn (fun e : Fin n =>
      couponNodeCoverOrderPayoff s M mask word e)).sum =
      n * couponNodeCoverWeight s M mask word := by
  let top : Fin n := certSite s (n - 2 + (M - 1))
  have htop : (protectedLabel s top).val + 1 = M :=
    couponNodeProtectedTopLabel s M hM hn
  cases hfinal : couponNodeFinalUnseen s M mask with
  | false =>
      calc
        _ = (List.ofFn (fun _ : Fin n => (0 : Nat))).sum := by
          apply ofFn_sum_eq
          intro e
          exact couponNodeCoverOrderPayoffFinalSeen
            s M mask word top e hmask htop hpos hfinal
        _ = n * couponNodeCoverWeight s M mask word := by
          simp [ofFn_sum_const, couponNodeCoverWeight, hfinal]
  | true =>
      let F : Nat → Bool := couponNodePrefixIndicator s M mask word
      have hweight :
          couponNodeCoverWeight s M mask word =
            ((List.range M).map (couponNodeOrderWeight F)).sum := by
        have hterm :
            ((List.range M).map (fun k =>
              if couponNodePrefixSeen s mask k &&
                  couponNodePrefixOrdered s M k word
              then freshFact k else 0)).sum =
            ((List.range M).map (couponNodeOrderWeight F)).sum := by
          rfl
        simpa only [couponNodeCoverWeight, hfinal, if_true] using hterm
      have hpred : M - 1 + 1 = M := by omega
      have hrange : List.range M = List.range (M - 1) ++ [M - 1] := by
        calc
          List.range M = List.range (M - 1 + 1) :=
            congrArg List.range hpred.symm
          _ = List.range (M - 1) ++ [M - 1] := by
            rw [List.range_succ]
      have hrows :
          ((List.range (M - 1)).map (fun k =>
            couponNodeCoverOrderPayoff s M mask word
              (certSite s (n - 2 + k)))).sum =
          ((List.range (M - 1)).map (couponNodeOrderRow F)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro k hk
        have hkbelow : k + 1 < M := by
          have hh : k < M - 1 := List.mem_range.mp hk
          omega
        have hkn : k < n := by omega
        have hlabel := couponNodeCoverProtectedSiteLabel s k hkn
        have hebelow :
            (protectedLabel s (certSite s (n - 2 + k))).val + 1 < M := by
          rw [hlabel]
          exact hkbelow
        have hh := couponNodeCoverOrderPayoffBelow s M mask word
          top (certSite s (n - 2 + k))
          hmask htop hebelow hfinal
        simpa only [hlabel, F] using hh
      have hlast :
          couponNodeCoverOrderPayoff s M mask word
              (certSite s (n - 2 + (M - 1))) =
            couponNodeOrderNextWeight F (M - 1) := by
        exact couponNodeCoverOrderPayoffTop
          s M mask word top hmask htop
      have hprotected :
          ((List.range M).map (fun k =>
            couponNodeCoverOrderPayoff s M mask word
              (certSite s (n - 2 + k)))).sum =
            M * couponNodeCoverWeight s M mask word := by
        calc
          _ =
              ((List.range (M - 1)).map (fun k =>
                couponNodeCoverOrderPayoff s M mask word
                  (certSite s (n - 2 + k)))).sum +
                couponNodeCoverOrderPayoff s M mask word
                  (certSite s (n - 2 + (M - 1))) := by
            rw [hrange, List.map_append, List.sum_append] <;>
              simp only [List.map_cons, List.map_nil,
                List.sum_cons, List.sum_nil, Nat.add_zero]
          _ = ((List.range (M - 1)).map
                (couponNodeOrderRow F)).sum +
                couponNodeOrderNextWeight F (M - 1) := by
            rw [hrows, hlast]
          _ = M *
              ((List.range M).map (couponNodeOrderWeight F)).sum := by
            simpa only [hpred] using couponNodeOrderRowSum F (M - 1)
          _ = M * couponNodeCoverWeight s M mask word := by
            rw [hweight]
      calc
        _ =
            ((List.range M).map (fun k =>
              couponNodeCoverOrderPayoff s M mask word
                (certSite s (n - 2 + k)))).sum +
            (n - M) * couponNodeCoverWeight s M mask word :=
          couponNodePhysicalEdgeSum s M
            (couponNodeCoverWeight s M mask word) hn
            (couponNodeCoverOrderPayoff s M mask word)
            (fun e he => couponNodeCoverOrderPayoffOutside
              s M mask word e hmask hpos he)
        _ = M * couponNodeCoverWeight s M mask word +
            (n - M) * couponNodeCoverWeight s M mask word := by
          rw [hprotected]
        _ = (M + (n - M)) * couponNodeCoverWeight s M mask word :=
          (Nat.add_mul M (n - M) _).symm
        _ = n * couponNodeCoverWeight s M mask word := by
          have hsum : M + (n - M) = n := by omega
          rw [hsum]


/-- Every live covering phase still has a missing protected coupon. -/
def couponNodeCoverPositive {n : Nat} : CouponAttemptPhase n → Prop
  | .covering mask _ => 0 < maskSize mask
  | _ => True

theorem couponNodeCoverPositiveStep {n q : Nat}
    (s : Fin n) (phase : CouponAttemptPhase n) (e : Fin n)
    (h : couponNodeCoverPositive phase) :
    couponNodeCoverPositive
      (couponAttemptPhaseNext (q := q) s phase e) := by
  cases phase with
  | covering mask word =>
      by_cases hzero : maskSize (maskDrop mask e) = 0
      · simp [couponAttemptPhaseNext, hzero]
        split <;> trivial
      · have hpos : 0 < maskSize (maskDrop mask e) := by omega
        simpa [couponAttemptPhaseNext, hzero,
          couponNodeCoverPositive] using hpos
  | launching hits =>
      simp [couponAttemptPhaseNext]
      repeat' split
      all_goals trivial
  | scanning j once =>
      simp [couponAttemptPhaseNext]
      repeat' split
      all_goals trivial
  | succeeded =>
      trivial
  | failed =>
      trivial

def couponNodeCoverPositiveAtNode {n q : Nat}
    (fixed : (protocol q).Configuration n) :
    AttemptNode
      (CouponSeed fixed × CouponAttemptPhase n)
      (CouponSeed fixed) → Prop
  | .active a => couponNodeCoverPositive a.2
  | .success => True
  | .retry _ => True

theorem couponNodeCoverPositiveKernelStep {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (node : AttemptNode
      (CouponSeed fixed × CouponAttemptPhase n)
      (CouponSeed fixed))
    (e : Fin n)
    (h : couponNodeCoverPositiveAtNode fixed node) :
    couponNodeCoverPositiveAtNode fixed
      (Prob.attemptStepper
        (couponTrialKernel ring fixed s) node e) := by
  cases node with
  | success =>
      trivial
  | retry seed =>
      trivial
  | active a =>
      cases a with
      | mk seed phase =>
          change couponNodeCoverPositive phase at h
          have hnext :=
            couponNodeCoverPositiveStep (q := q) s phase e h
          cases hp : couponAttemptPhaseNext (q := q) s phase e with
          | succeeded =>
              simp [Prob.attemptStepper, couponTrialKernel, hp]
              split <;> trivial
          | failed =>
              simp [Prob.attemptStepper, couponTrialKernel,
                hp, couponNodeCoverPositiveAtNode]
          | covering mask word =>
              simpa [Prob.attemptStepper, couponTrialKernel,
                hp, couponNodeCoverPositiveAtNode] using hnext
          | launching hits =>
              simpa [Prob.attemptStepper, couponTrialKernel,
                hp, couponNodeCoverPositiveAtNode] using hnext
          | scanning j once =>
              simpa [Prob.attemptStepper, couponTrialKernel,
                hp, couponNodeCoverPositiveAtNode] using hnext

theorem couponNodeCoverPositiveRun {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n) :
    ∀ (node : AttemptNode
        (CouponSeed fixed × CouponAttemptPhase n)
        (CouponSeed fixed))
      (word : List (Fin n)),
      couponNodeCoverPositiveAtNode fixed node →
      couponNodeCoverPositiveAtNode fixed
        (LDSinkBoundedKernel.run
          (Prob.attemptStepper (couponTrialKernel ring fixed s))
          node word) := by
  intro node word
  induction word generalizing node with
  | nil =>
      intro h
      exact h
  | cons e rest ih =>
      intro h
      change
        couponNodeCoverPositiveAtNode fixed
          (LDSinkBoundedKernel.run
            (Prob.attemptStepper (couponTrialKernel ring fixed s))
            (Prob.attemptStepper
              (couponTrialKernel ring fixed s) node e) rest)
      exact ih _
        (couponNodeCoverPositiveKernelStep
          ring fixed s node e h)

theorem couponNodeCoverPositiveStart {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (seed : CouponSeed fixed) :
    couponNodeCoverPositiveAtNode fixed
      (.active ((couponTrialKernel ring fixed s).start seed)) := by
  change 0 < maskSize
    (fun e : Fin n =>
      canonicalMask ((compileAdvice q).t + 3)
        (protectedLabel s e))
  have hm :
      maskSize
        (fun e : Fin n =>
          canonicalMask ((compileAdvice q).t + 3)
            (protectedLabel s e)) =
        (compileAdvice q).t + 3 :=
    relabeled_mask_size
      (rotate (certSite s (n - 2)))
      (unrotate (certSite s (n - 2)))
      (unrotate_rotate (certSite s (n - 2)))
      (rotate_unrotate (certSite s (n - 2)))
      ((compileAdvice q).t + 3) hn
  rw [hm]
  omega

theorem couponNodeReachableCoverMaskPositive {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (mask : Fin n → Bool) (word : List (Fin n))
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .covering mask word) :
    0 < maskSize mask := by
  obtain ⟨seed, schedule, hrun⟩ := hreach
  have hstart :=
    couponNodeCoverPositiveStart ring fixed s hn seed
  have hstate :=
    couponNodeCoverPositiveRun ring fixed s
      (.active ((couponTrialKernel ring fixed s).start seed))
      schedule hstart
  rw [hrun] at hstate
  change couponNodeCoverPositive a.2 at hstate
  rw [hphase] at hstate
  exact hstate


theorem couponNodeMaskDropSizeLe {n : Nat}
    (mask : Fin n → Bool) (e : Fin n) :
    maskSize (maskDrop mask e) ≤ maskSize mask := by
  cases he : mask e with
  | false =>
      simpa only [coupon_maskDrop_false mask e he] using
        (Nat.le_refl (maskSize mask))
  | true =>
      have hs := coupon_maskDrop_true mask e he
      omega

theorem couponNodeMaskFoldSizeLe {n : Nat}
    (mask : Fin n → Bool) (word : List (Fin n)) :
    maskSize (word.foldl maskDrop mask) ≤ maskSize mask := by
  induction word generalizing mask with
  | nil =>
      exact Nat.le_refl _
  | cons e rest ih =>
      change maskSize (rest.foldl maskDrop (maskDrop mask e)) ≤
        maskSize mask
      exact Nat.le_trans (ih (maskDrop mask e))
        (couponNodeMaskDropSizeLe mask e)

theorem couponNodeCoherentMaskSizeLe {n : Nat}
    (s : Fin n) (M : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (hn : M ≤ n)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask M (protectedLabel s i))) :
    maskSize mask ≤ M := by
  rw [hmask]
  calc
    maskSize (word.foldl maskDrop
        (fun i : Fin n => canonicalMask M (protectedLabel s i))) ≤
        maskSize
          (fun i : Fin n => canonicalMask M (protectedLabel s i)) :=
      couponNodeMaskFoldSizeLe _ word
    _ = M :=
      relabeled_mask_size
        (rotate (certSite s (n - 2)))
        (unrotate (certSite s (n - 2)))
        (unrotate_rotate (certSite s (n - 2)))
        (rotate_unrotate (certSite s (n - 2))) M hn

/-- Exact mask Bellman row at a scale divisible by its current size. -/
theorem couponNodeScaledHarmonicMaskRow {n : Nat}
    (D : Nat) (mask : Fin n → Bool)
    (hpos : 0 < maskSize mask)
    (hdvd : maskSize mask ∣ D) :
    D + (List.ofFn (fun e : Fin n =>
      scaledHarmonic D (maskSize (maskDrop mask e)))).sum =
      n * scaledHarmonic D (maskSize mask) := by
  let m := maskSize mask
  let v := scaledHarmonic D (m - 1)
  let h := D / m
  have hmle : m ≤ n := coupon_maskSize_le mask
  have hh : scaledHarmonic D m = v + h :=
    scaledHarmonic_step D m hpos
  have hdiv : h * m = D := Nat.div_mul_cancel hdvd
  have hvalue (e : Fin n) :
      scaledHarmonic D (maskSize (maskDrop mask e)) =
        if mask e then v else v + h := by
    by_cases he : mask e = true
    · have hs : maskSize (maskDrop mask e) + 1 = m :=
        coupon_maskDrop_true mask e he
      have hsize : maskSize (maskDrop mask e) = m - 1 := by omega
      simp [he, hsize, v]
    · have hf : mask e = false := by
        cases hv : mask e with
        | false => rfl
        | true => exact False.elim (he hv)
      have hs := coupon_maskDrop_false mask e hf
      simp only [hf, hs, if_false]
      exact hh
  have hsum :
      (List.ofFn (fun e : Fin n =>
        scaledHarmonic D (maskSize (maskDrop mask e)))).sum =
        (n - m) * (v + h) + m * v := by
    calc
      (List.ofFn (fun e : Fin n =>
          scaledHarmonic D (maskSize (maskDrop mask e)))).sum =
          (List.ofFn (fun e : Fin n =>
            if mask e then v else v + h)).sum :=
        ofFn_sum_eq _ _ hvalue
      _ = (n - m) * (v + h) + m * v := by
        simpa only [m] using coupon_mask_split_sum mask (v + h) v
  have hpart : D + m * v = m * (v + h) := by
    calc
      D + m * v = m * h + m * v := by
        rw [← hdiv]
        ac_rfl
      _ = m * (v + h) := by
        rw [Nat.mul_add]
        ac_rfl
  have hsplit : n - m + m = n := Nat.sub_add_cancel hmle
  change D + (List.ofFn (fun e : Fin n =>
    scaledHarmonic D (maskSize (maskDrop mask e)))).sum =
      n * scaledHarmonic D m
  rw [hsum, hh]
  calc
    D + ((n - m) * (v + h) + m * v) =
        (n - m) * (v + h) + (D + m * v) := by ac_rfl
    _ = (n - m) * (v + h) + m * (v + h) := by rw [hpart]
    _ = n * (v + h) := by rw [← Nat.add_mul, hsplit]

theorem couponNodeHarmonicDenFactorial (M : Nat) :
    (harmonicPair M).2 = freshFact M := by
  induction M with
  | zero =>
      rfl
  | succ M ih =>
      change (harmonicPair M).2 * (M + 1) =
        (M + 1) * freshFact M
      rw [ih]
      ac_rfl

theorem couponNodeCoverNoTruncationWidth {n : Nat}
    (s : Fin n) (t : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) (hwidth : t = 2 ∨ t = 3) :
    n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        couponNodeCoverWeight s (t + 3) mask word ≤
      couponNodeBudget n t + n * (pPair t).1 *
        scaledHarmonic (freshFact (t + 3)) (maskSize mask) := by
  rcases hwidth with ht | ht
  · rw [ht]
    exact couponNodeCoverNoTruncationTwo s mask word
  · rw [ht]
    exact couponNodeCoverNoTruncationThree s mask word

/-- The accepted-cover discount fits inside the exact retry budget. -/
theorem couponNodeLaunchZeroNoTruncation (n t : Nat)
    (hwidth : t = 2 ∨ t = 3) :
    n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) ≤ couponNodeBudget n t := by
  have hlocal :
      (pPair t).1 * (harmonicPair (t + 3)).1 *
          freshFact (t + 3) ≤ couponNodeNumerator t := by
    rcases hwidth with ht | ht
    · rw [ht]
      change (pPair 2).1 * (harmonicPair 5).1 * freshFact 5 ≤
        couponNodeNumerator 2
      rw [couponNodePairNumeratorTwo,
        couponNodeHarmonicNumeratorTwo, couponNodeNumerator_two]
      decide
    · rw [ht]
      change (pPair 3).1 * (harmonicPair 6).1 * freshFact 6 ≤
        couponNodeNumerator 3
      rw [couponNodePairNumeratorThree,
        couponNodeHarmonicNumeratorThree, couponNodeNumerator_three]
      decide
  have hs := Nat.mul_le_mul_left n hlocal
  simpa only [couponNodeBudget, Nat.mul_assoc] using hs


/-- Add back the exact order discount to each actual cover successor.
A failed cover pays the retry budget; an accepted cover enters launch zero. -/
theorem couponNodeCoverSuccessorBalance {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed) (mask : Fin n → Bool)
    (word : List (Fin n))
    (hwidth : (compileAdvice q).t = 2 ∨ (compileAdvice q).t = 3)
    (e : Fin n) :
    couponAttemptNodeValue
        (couponNodeBudget n (compileAdvice q).t)
        (fun a : CouponSeed fixed × CouponAttemptPhase n =>
          couponNodePotential (q := q) s a.2)
        ((couponTrialKernel ring fixed s).step
          (seed, .covering mask word) e) +
      n * (pPair (compileAdvice q).t).1 *
        (harmonicPair ((compileAdvice q).t + 3)).1 *
        couponNodeCoverOrderPayoff s ((compileAdvice q).t + 3)
          mask word e =
      couponNodeBudget n (compileAdvice q).t +
        n * (pPair (compileAdvice q).t).1 *
          scaledHarmonic (freshFact ((compileAdvice q).t + 3))
            (maskSize (maskDrop mask e)) := by
  by_cases hzero : maskSize (maskDrop mask e) = 0
  · by_cases haccept :
        lastAccept ((compileAdvice q).t + 3)
          ((word ++ [e]).map (protectedLabel s)) = 1
    · have hnormal :
          lastAccept ((compileAdvice q).t + 3)
            (word.map (protectedLabel s) ++ [protectedLabel s e]) = 1 := by
        simpa only [List.map_append, List.map_cons, List.map_nil]
          using haccept
      have hphase :
          couponAttemptPhaseNext (q := q) s
            (.covering mask word) e = .launching 0 := by
        simp [couponAttemptPhaseNext, hzero, hnormal,
          List.map_append]
      have hstep :
          (couponTrialKernel ring fixed s).step
            (seed, .covering mask word) e =
          .active (couponSeedStep ring fixed s seed e, .launching 0) := by
        simp [couponTrialKernel, hphase]
      have hreward :
          couponNodeCoverOrderPayoff s
              ((compileAdvice q).t + 3) mask word e =
            freshFact ((compileAdvice q).t + 3) := by
        simp only [couponNodeCoverOrderPayoff, if_pos hzero,
          haccept, Nat.mul_one]
      have hlaunch :=
        couponNodeLaunchZeroNoTruncation n (compileAdvice q).t hwidth
      rw [hstep, hreward, hzero]
      exact Nat.sub_add_cancel hlaunch
    · have hacceptzero :
          lastAccept ((compileAdvice q).t + 3)
            ((word ++ [e]).map (protectedLabel s)) = 0 := by
        have hcases :=
          orderedAccept_range ((compileAdvice q).t + 3)
            (((word ++ [e]).map (protectedLabel s)).reverse)
        change
          lastAccept ((compileAdvice q).t + 3)
              ((word ++ [e]).map (protectedLabel s)) = 0 ∨
          lastAccept ((compileAdvice q).t + 3)
              ((word ++ [e]).map (protectedLabel s)) = 1 at hcases
        rcases hcases with hz | ho
        · exact hz
        · exact False.elim (haccept ho)
      have hnormal :
          lastAccept ((compileAdvice q).t + 3)
            (word.map (protectedLabel s) ++ [protectedLabel s e]) = 0 := by
        simpa only [List.map_append, List.map_cons, List.map_nil]
          using hacceptzero
      have hphase :
          couponAttemptPhaseNext (q := q) s
            (.covering mask word) e = .failed := by
        simp [couponAttemptPhaseNext, hzero, hnormal,
          List.map_append]
      have hstep :
          (couponTrialKernel ring fixed s).step
            (seed, .covering mask word) e =
          .retry (couponSeedStep ring fixed s seed e) := by
        simp [couponTrialKernel, hphase]
      have hreward :
          couponNodeCoverOrderPayoff s
              ((compileAdvice q).t + 3) mask word e = 0 := by
        simp only [couponNodeCoverOrderPayoff, if_pos hzero,
          hacceptzero, Nat.mul_zero]
      rw [hstep, hreward, hzero] <;> rfl
  · have hphase :
        couponAttemptPhaseNext (q := q) s
          (.covering mask word) e =
        .covering (maskDrop mask e) (word ++ [e]) := by
      simp [couponAttemptPhaseNext, hzero]
    have hstep :
        (couponTrialKernel ring fixed s).step
          (seed, .covering mask word) e =
        .active (couponSeedStep ring fixed s seed e,
          .covering (maskDrop mask e) (word ++ [e])) := by
      simp [couponTrialKernel, hphase]
    have hreward :
        couponNodeCoverOrderPayoff s
            ((compileAdvice q).t + 3) mask word e =
          couponNodeCoverWeight s ((compileAdvice q).t + 3)
            (maskDrop mask e) (word ++ [e]) := by
      simp only [couponNodeCoverOrderPayoff, if_neg hzero]
    have hcover :=
      couponNodeCoverNoTruncationWidth s (compileAdvice q).t
        (maskDrop mask e) (word ++ [e]) hwidth
    rw [hstep, hreward]
    exact Nat.sub_add_cancel hcover

/-- Exact cover-phase Bellman equality, including the last-coupon
retry/launch payoff and all physical outside edges. -/
theorem couponNodeCoverDrift {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed) (mask : Fin n → Bool)
    (word : List (Fin n))
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hwidth : (compileAdvice q).t = 2 ∨ (compileAdvice q).t = 3)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n => canonicalMask ((compileAdvice q).t + 3)
        (protectedLabel s i)))
    (hpos : 0 < maskSize mask) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .covering mask word) e))).sum =
      n * couponNodeCoverPotential s (compileAdvice q).t mask word := by
  let t := (compileAdvice q).t
  let M := t + 3
  let D := couponNodeDenominator t
  let P := couponNodeBudget n t
  let B := n * (pPair t).1
  let C := B * (harmonicPair M).1
  let H := scaledHarmonic (freshFact M) (maskSize mask)
  let S := couponNodeCoverWeight s M mask word
  let V := couponNodeCoverPotential s t mask word
  let E : Fin n → Nat := fun e =>
    couponAttemptNodeValue P
      (fun a : CouponSeed fixed × CouponAttemptPhase n =>
        couponNodePotential (q := q) s a.2)
      ((couponTrialKernel ring fixed s).step
        (seed, .covering mask word) e)
  let R : Fin n → Nat := fun e =>
    couponNodeCoverOrderPayoff s M mask word e
  let Hnext : Fin n → Nat := fun e =>
    scaledHarmonic (freshFact M) (maskSize (maskDrop mask e))
  have hmle : maskSize mask ≤ M :=
    couponNodeCoherentMaskSizeLe s M mask word hn hmask
  have hdiv : maskSize mask ∣ freshFact M :=
    coupon_factorial_dvd M (maskSize mask) hpos hmle
  have hH : freshFact M + (List.ofFn Hnext).sum = n * H :=
    couponNodeScaledHarmonicMaskRow (freshFact M) mask hpos hdiv
  have horder : (List.ofFn R).sum = n * S :=
    couponNodeCoverOrderHarmonic s M mask word
      (by dsimp only [M]; omega) hn hmask hpos
  have hcoef : D * n = B * freshFact M := by
    change ((harmonicPair M).2 * (pPair t).1) * n =
      (n * (pPair t).1) * freshFact M
    rw [couponNodeHarmonicDenFactorial M]
    ac_rfl
  have hcur : V + C * S = P + B * H :=
    Nat.sub_add_cancel
      (couponNodeCoverNoTruncationWidth s t mask word hwidth)
  have hpoint (e : Fin n) :
      E e + C * R e = P + B * Hnext e :=
    couponNodeCoverSuccessorBalance
      ring fixed s seed mask word hwidth e
  have hsum :
      (List.ofFn E).sum + C * (List.ofFn R).sum =
        n * P + B * (List.ofFn Hnext).sum := by
    calc
      (List.ofFn E).sum + C * (List.ofFn R).sum =
          (List.ofFn (fun e : Fin n => E e + C * R e)).sum := by
        rw [ofFn_sum_add, ofFn_sum_mul_left]
      _ = (List.ofFn (fun e : Fin n => P + B * Hnext e)).sum :=
        ofFn_sum_eq _ _ hpoint
      _ = n * P + B * (List.ofFn Hnext).sum := by
        rw [ofFn_sum_add, ofFn_sum_const, ofFn_sum_mul_left]
  change D * n + (List.ofFn E).sum = n * V
  have hfinish :
      (D * n + (List.ofFn E).sum) + n * (C * S) =
        n * V + n * (C * S) := by
    calc
      (D * n + (List.ofFn E).sum) + n * (C * S) =
          B * freshFact M + ((List.ofFn E).sum + C * (n * S)) := by
        rw [hcoef]
        ac_rfl
      _ = B * freshFact M +
          ((List.ofFn E).sum + C * (List.ofFn R).sum) := by
        rw [horder]
      _ = B * freshFact M +
          (n * P + B * (List.ofFn Hnext).sum) := by
        rw [hsum]
      _ = n * P + B * (freshFact M + (List.ofFn Hnext).sum) := by
        rw [Nat.mul_add]
        ac_rfl
      _ = n * P + B * (n * H) := by rw [hH]
      _ = n * (P + B * H) := by
        rw [Nat.mul_add]
        ac_rfl
      _ = n * (V + C * S) := by rw [hcur]
      _ = n * V + n * (C * S) := by rw [Nat.mul_add]
  exact Nat.add_right_cancel hfinish

/-- Actual reachable cover nodes satisfy exact drift at both
requested widths, with no hidden physical-soundness premise. -/
theorem couponNodeReachableCoverDrift {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hwidth : (compileAdvice q).t = 2 ∨ (compileAdvice q).t = 3)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (mask : Fin n → Bool) (word : List (Fin n))
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .covering mask word) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun b : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s b.2)
          ((couponTrialKernel ring fixed s).step a e))).sum =
      n * couponNodePotential (q := q) s a.2 := by
  have hmask := couponNodeReachableCoverMaskFold
    ring fixed s a mask word hreach hphase
  have hpos := couponNodeReachableCoverMaskPositive
    ring fixed s hn a mask word hreach hphase
  cases a with
  | mk seed phase =>
      change phase = .covering mask word at hphase
      rw [hphase]
      exact couponNodeCoverDrift
        ring fixed s seed mask word hn hwidth hmask hpos


end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open FiniteUniformStoppingTree

/-!
Launch observer.
This is a stop-on-exit projection of the genuine .launching rows
of couponAttemptPhaseNext, with the physical scheduler labels unchanged.
-/

/-- Stop exactly when the launch observer first leaves .launching. -/
def couponNodeLaunchStoppedStep {n q : Nat} (s : Fin n) :
    CouponAttemptPhase n → Fin n → CouponAttemptPhase n
  | .launching hits, e =>
      couponAttemptPhaseNext (q := q) s (.launching hits) e
  | phase, _ => phase

def couponNodeLaunchStoppedRun {n q : Nat} (s : Fin n)
    (phase : CouponAttemptPhase n) (word : List (Fin n)) :
    CouponAttemptPhase n :=
  word.foldl (couponNodeLaunchStoppedStep (q := q) s) phase

theorem couponNodeLaunchStoppedRunAppend {n q : Nat}
    (s : Fin n) (phase : CouponAttemptPhase n)
    (xs ys : List (Fin n)) :
    couponNodeLaunchStoppedRun (q := q) s phase (xs ++ ys) =
      couponNodeLaunchStoppedRun (q := q) s
        (couponNodeLaunchStoppedRun (q := q) s phase xs) ys := by
  simp only [couponNodeLaunchStoppedRun, List.foldl_append]

theorem couponNodeLaunchStoppedRunScan {n q : Nat}
    (s : Fin n) (j : Nat) (A : List Nat) :
    ∀ word : List (Fin n),
      couponNodeLaunchStoppedRun (q := q) s
        (.scanning j A) word = .scanning j A := by
  intro word
  induction word with
  | nil => rfl
  | cons e rest ih =>
      change couponNodeLaunchStoppedRun (q := q) s
        (.scanning j A) rest = .scanning j A
      exact ih

theorem couponNodeLaunchStoppedRunFailed {n q : Nat}
    (s : Fin n) :
    ∀ word : List (Fin n),
      couponNodeLaunchStoppedRun (q := q) s
        .failed word = .failed := by
  intro word
  induction word with
  | nil => rfl
  | cons e rest ih =>
      change couponNodeLaunchStoppedRun (q := q) s
        .failed rest = .failed
      exact ih

/-- A failed launch means the first forbidden (monitored, nonmarked)
letter arrived while the remaining marked-hit count was positive.
The suffix after either terminal event is ignored. -/
def couponNodeLaunchReject {n : Nat}
    (outside : Fin n → Bool) (mark : Fin n) :
    Nat → List (Fin n) → Bool
  | 0, _ => false
  | _ + 1, [] => false
  | k + 1, e :: rest =>
      if e = mark then couponNodeLaunchReject outside mark k rest
      else if outside e then
        couponNodeLaunchReject outside mark (k + 1) rest
      else true

/-- First component: launch accepted and scan entered.
Second component: first forbidden monitored nonmarked hit seen. -/
def couponNodeLaunchPhaseResult {n : Nat} :
    CouponAttemptPhase n → Nat × Bool
  | .scanning _ _ => (1, false)
  | .failed => (0, true)
  | _ => (0, false)

/-- Exact correspondence for both live hit counters. No truncation,
probability, or physical-ghost assumption is involved. -/
theorem couponNodeLaunchStoppedExact {n q : Nat} (s : Fin n) :
    ∀ word : List (Fin n),
      couponNodeLaunchPhaseResult
          (couponNodeLaunchStoppedRun (q := q) s (.launching 0) word) =
        (launchMarkAccept (outsideLaunch (q := q) s)
          (certSite s (n - 1)) 2 word,
         couponNodeLaunchReject (outsideLaunch (q := q) s)
          (certSite s (n - 1)) 2 word) ∧
      couponNodeLaunchPhaseResult
          (couponNodeLaunchStoppedRun (q := q) s (.launching 1) word) =
        (launchMarkAccept (outsideLaunch (q := q) s)
          (certSite s (n - 1)) 1 word,
         couponNodeLaunchReject (outsideLaunch (q := q) s)
          (certSite s (n - 1)) 1 word) := by
  intro word
  induction word with
  | nil =>
      constructor <;> rfl
  | cons e rest ih =>
      by_cases hmark : e = certSite s (n - 1)
      · subst e
        constructor
        · simpa [couponNodeLaunchStoppedRun,
            couponNodeLaunchStoppedStep, couponAttemptPhaseNext,
            launchMarkAccept, couponNodeLaunchReject] using ih.2
        · have hscan :
              couponNodeLaunchPhaseResult
                  (couponNodeLaunchStoppedRun (q := q) s
                    (.scanning 0 []) rest) = (1, false) := by
            rw [couponNodeLaunchStoppedRunScan]
            rfl
          simpa [couponNodeLaunchStoppedRun,
            couponNodeLaunchStoppedStep, couponAttemptPhaseNext,
            launchMarkAccept, couponNodeLaunchReject] using hscan
      · cases hout : outsideLaunch (q := q) s e with
        | true =>
            constructor
            · simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep, couponAttemptPhaseNext,
                launchMarkAccept, couponNodeLaunchReject,
                hmark, hout] using ih.1
            · simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep, couponAttemptPhaseNext,
                launchMarkAccept, couponNodeLaunchReject,
                hmark, hout] using ih.2
        | false =>
            have hfail :
                couponNodeLaunchPhaseResult
                    (couponNodeLaunchStoppedRun (q := q) s
                      .failed rest) = (0, true) := by
              rw [couponNodeLaunchStoppedRunFailed]
              rfl
            constructor
            · simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep, couponAttemptPhaseNext,
                launchMarkAccept, couponNodeLaunchReject,
                hmark, hout] using hfail
            · simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep, couponAttemptPhaseNext,
                launchMarkAccept, couponNodeLaunchReject,
                hmark, hout] using hfail

/-- Full launch word: stopped observer enters scan if and only if the
original two-mark recognizer accepts it. -/
theorem couponNodeLaunchStoppedAcceptIff {n q : Nat}
    (s : Fin n) (word : List (Fin n)) :
    (∃ j A, couponNodeLaunchStoppedRun (q := q) s
      (.launching 0) word = .scanning j A) ↔
    launchMarkAccept (outsideLaunch (q := q) s)
      (certSite s (n - 1)) 2 word = 1 := by
  have hpair := (couponNodeLaunchStoppedExact (q := q) s word).1
  constructor
  · rintro ⟨j, A, heq⟩
    rw [heq] at hpair
    exact (congrArg Prod.fst hpair).symm
  · intro haccept
    have hfirst :
        (couponNodeLaunchPhaseResult
          (couponNodeLaunchStoppedRun (q := q) s
            (.launching 0) word)).1 = 1 := by
      rw [hpair]
      exact haccept
    cases hp : couponNodeLaunchStoppedRun (q := q) s
        (.launching 0) word with
    | scanning j A =>
        exact ⟨j, A, rfl⟩
    | covering mask history =>
        simp [couponNodeLaunchPhaseResult, hp] at hfirst
    | launching hits =>
        simp [couponNodeLaunchPhaseResult, hp] at hfirst
    | succeeded =>
        simp [couponNodeLaunchPhaseResult, hp] at hfirst
    | failed =>
        simp [couponNodeLaunchPhaseResult, hp] at hfirst

/-- Launch failure has precisely the recursive first-bad-letter test;
insufficient marked hits without a bad letter are not a failure. -/
theorem couponNodeLaunchStoppedRejectIff {n q : Nat}
    (s : Fin n) (word : List (Fin n)) :
    couponNodeLaunchStoppedRun (q := q) s (.launching 0) word =
      .failed ↔
    couponNodeLaunchReject (outsideLaunch (q := q) s)
      (certSite s (n - 1)) 2 word = true := by
  have hpair := (couponNodeLaunchStoppedExact (q := q) s word).1
  constructor
  · intro heq
    rw [heq] at hpair
    exact (congrArg Prod.snd hpair).symm
  · intro hreject
    have hsecond :
        (couponNodeLaunchPhaseResult
          (couponNodeLaunchStoppedRun (q := q) s
            (.launching 0) word)).2 = true := by
      rw [hpair]
      exact hreject
    cases hp : couponNodeLaunchStoppedRun (q := q) s
        (.launching 0) word with
    | failed =>
        rfl
    | covering mask history =>
        simp [couponNodeLaunchPhaseResult, hp] at hsecond
    | launching hits =>
        simp [couponNodeLaunchPhaseResult, hp] at hsecond
    | scanning j A =>
        simp [couponNodeLaunchPhaseResult, hp] at hsecond
    | succeeded =>
        simp [couponNodeLaunchPhaseResult, hp] at hsecond

/-- A monitored nonmarked selection before launch completion is a
literal failing edge of the corrected observer. -/
theorem couponNodeLaunchFirstBadStep {n q : Nat}
    (s e : Fin n) (hits : Nat)
    (hmark : e ≠ certSite s (n - 1))
    (hout : outsideLaunch (q := q) s e = false) :
    couponNodeLaunchStoppedStep (q := q) s
      (.launching hits) e = .failed := by
  simp [couponNodeLaunchStoppedStep, couponAttemptPhaseNext,
    hmark, hout]

/-- The first forbidden monitored nonmark persists through every
subsequent scheduler suffix; previous letters are genuine physical edges. -/
theorem couponNodeLaunchFirstBadForcesFailure {n q : Nat}
    (s : Fin n) (before after : List (Fin n))
    (e : Fin n) (hits : Nat)
    (hbefore :
      couponNodeLaunchStoppedRun (q := q) s
        (.launching 0) before = .launching hits)
    (hmark : e ≠ certSite s (n - 1))
    (hout : outsideLaunch (q := q) s e = false) :
    couponNodeLaunchStoppedRun (q := q) s
      (.launching 0) (before ++ [e] ++ after) = .failed := by
  have hsingle :
      couponNodeLaunchStoppedRun (q := q) s
        (.launching hits) [e] = .failed := by
    change couponNodeLaunchStoppedStep (q := q) s
      (.launching hits) e = .failed
    exact couponNodeLaunchFirstBadStep s e hits hmark hout
  calc
    couponNodeLaunchStoppedRun (q := q) s
        (.launching 0) (before ++ [e] ++ after) =
      couponNodeLaunchStoppedRun (q := q) s
        (couponNodeLaunchStoppedRun (q := q) s
          (.launching 0) before) ([e] ++ after) := by
            rw [List.append_assoc]
            exact couponNodeLaunchStoppedRunAppend s
              (.launching 0) before ([e] ++ after)
    _ = couponNodeLaunchStoppedRun (q := q) s
          (.launching hits) ([e] ++ after) := by rw [hbefore]
    _ = couponNodeLaunchStoppedRun (q := q) s
          (couponNodeLaunchStoppedRun (q := q) s
            (.launching hits) [e]) after :=
          couponNodeLaunchStoppedRunAppend s
            (.launching hits) [e] after
    _ = .failed := by
      rw [hsingle, couponNodeLaunchStoppedRunFailed]


/-- For either reachable launch hit counter, any stopped failure has
a *first* bad selected edge. All earlier scheduler letters leave the
observer in a live launching state. -/
theorem couponNodeLaunchFailureHasFirstBad {n q : Nat}
    (s : Fin n) :
    ∀ (word : List (Fin n)) (hits : Nat),
      hits ≤ 1 →
      couponNodeLaunchStoppedRun (q := q) s
        (.launching hits) word = .failed →
      ∃ (before : List (Fin n)) (bad : Fin n)
        (after : List (Fin n)) (remaining : Nat),
        word = before ++ [bad] ++ after ∧
        couponNodeLaunchStoppedRun (q := q) s
          (.launching hits) before = .launching remaining ∧
        bad ≠ certSite s (n - 1) ∧
        outsideLaunch (q := q) s bad = false := by
  intro word
  induction word with
  | nil =>
      intro hits hle hfail
      cases hfail
  | cons e rest ih =>
      intro hits hle hfail
      by_cases hmark : e = certSite s (n - 1)
      · subst e
        cases hits with
        | zero =>
            have htail :
                couponNodeLaunchStoppedRun (q := q) s
                  (.launching 1) rest = .failed := by
              simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep,
                couponAttemptPhaseNext] using hfail
            obtain ⟨before, bad, after, remaining,
                hword, hbefore, hnot, hout⟩ :=
              ih 1 (by omega) htail
            refine ⟨certSite s (n - 1) :: before,
              bad, after, remaining, ?_, ?_, hnot, hout⟩
            · simpa only [List.cons_append] using
                congrArg (List.cons (certSite s (n - 1))) hword
            · simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep,
                couponAttemptPhaseNext] using hbefore
        | succ k =>
            have hk : k = 0 := by omega
            subst k
            have himpossible :
                couponNodeLaunchStoppedRun (q := q) s
                  (.scanning 0 []) rest = .failed := by
              simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep,
                couponAttemptPhaseNext] using hfail
            rw [couponNodeLaunchStoppedRunScan] at himpossible
            cases himpossible
      · cases hout : outsideLaunch (q := q) s e with
        | false =>
            exact ⟨[], e, rest, hits, rfl, rfl, hmark, hout⟩
        | true =>
            have htail :
                couponNodeLaunchStoppedRun (q := q) s
                  (.launching hits) rest = .failed := by
              simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep,
                couponAttemptPhaseNext, hmark, hout] using hfail
            obtain ⟨before, bad, after, remaining,
                hword, hbefore, hnot, hbad⟩ :=
              ih hits hle htail
            refine ⟨e :: before, bad, after, remaining,
              ?_, ?_, hnot, hbad⟩
            · simpa only [List.cons_append] using
                congrArg (List.cons e) hword
            · simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep, couponAttemptPhaseNext,
                hmark, hout] using hbefore

/-- Exact first-bad-edge criterion, not just the executable recursive
Boolean reject recognizer. The bad edge belongs to the monitored launch
family but is not the marked site; every earlier edge has left the
stopped observer in a live .launching state. -/
theorem couponNodeLaunchFailedIffFirstBad {n q : Nat}
    (s : Fin n) (word : List (Fin n)) :
    couponNodeLaunchStoppedRun (q := q) s
        (.launching 0) word = .failed ↔
      ∃ (before : List (Fin n)) (bad : Fin n)
        (after : List (Fin n)) (hits : Nat),
        word = before ++ [bad] ++ after ∧
        couponNodeLaunchStoppedRun (q := q) s
          (.launching 0) before = .launching hits ∧
        bad ≠ certSite s (n - 1) ∧
        outsideLaunch (q := q) s bad = false := by
  constructor
  · intro hfailed
    exact couponNodeLaunchFailureHasFirstBad s word 0
      (by omega) hfailed
  · rintro ⟨before, bad, after, hits, hword, hbefore,
      hnot, hout⟩
    rw [hword]
    exact couponNodeLaunchFirstBadForcesFailure
      s before after bad hits hbefore hnot hout

/-- The accepted stopped launch admits the two literal marked edges,
with only outsideLaunch edges before and between them. -/
theorem couponNodeLaunchStoppedTwoMarkSplit {n q : Nat}
    (s : Fin n) (word : List (Fin n))
    (h :
      ∃ j A, couponNodeLaunchStoppedRun (q := q) s
        (.launching 0) word = .scanning j A) :
    ∃ before between after : List (Fin n),
      word = before ++ [certSite s (n - 1)] ++
        between ++ [certSite s (n - 1)] ++ after ∧
      (∀ e, e ∈ before → outsideLaunch (q := q) s e = true) ∧
      (∀ e, e ∈ between → outsideLaunch (q := q) s e = true) := by
  exact launch_two_mark_prefix
    (outsideLaunch (q := q) s) (certSite s (n - 1)) word
    ((couponNodeLaunchStoppedAcceptIff s word).mp h)

/-- Conditional physical second launch: it consumes an *actual*
accepted clear word and actual stopped launch observer word. This
does not yet assert their decomposition from all reached attempts. -/
theorem couponNodeLaunchReadyFromStoppedObserver {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (seed : CouponSeed fixed)
    (clear launch : List (Fin n))
    (hclear : lastAccept ((compileAdvice q).t + 3)
      (clear.map (protectedLabel s)) = 1)
    (hlaunch :
      ∃ j A, couponNodeLaunchStoppedRun (q := q) s
        (.launching 0) launch = .scanning j A) :
    ∃ before between after : List (Fin n),
      launch = before ++ [certSite s (n - 1)] ++
        between ++ [certSite s (n - 1)] ++ after ∧
      CouponLaunchReady fixed s ht
        (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
          (LDSinkBoundedKernel.run
            (freshGhostStep ring fixed s) seed.1 clear)
          (before ++ [certSite s (n - 1)] ++
            between ++ [certSite s (n - 1)])) := by
  exact two_hit_launch_after_cover ring fixed s ht hn hroot
    seed.1 seed.2 clear launch hclear
    ((couponNodeLaunchStoppedAcceptIff s launch).mp hlaunch)

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (AttemptNode RetryKernel)

/-!
Provenance for the genuinely reached physical attempt word.
No proof-local aliases or added assumptions on the initial frozen seed.
-/

def couponNodeSeedRun {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (origin : CouponSeed fixed) (word : List (Fin n)) :
    CouponSeed fixed :=
  word.foldl (couponSeedStep ring fixed s) origin

def couponNodeObserverRun {n q : Nat}
    (s : Fin n) (word : List (Fin n)) : CouponAttemptPhase n :=
  word.foldl (couponAttemptPhaseNext (q := q) s)
    (couponAttemptStart (q := q) s)

def couponNodeScanRun {n q : Nat}
    (s : Fin n) (word : List (Fin n)) : CouponAttemptPhase n :=
  word.foldl (couponAttemptPhaseNext (q := q) s) (.scanning 0 [])

theorem couponNodeSeedRunSnoc {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (origin : CouponSeed fixed) (word : List (Fin n)) (e : Fin n) :
    couponNodeSeedRun ring fixed s origin (word ++ [e]) =
      couponSeedStep ring fixed s
        (couponNodeSeedRun ring fixed s origin word) e := by
  simp only [couponNodeSeedRun, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem couponNodeObserverRunSnoc {n q : Nat}
    (s : Fin n) (word : List (Fin n)) (e : Fin n) :
    couponNodeObserverRun (q := q) s (word ++ [e]) =
      couponAttemptPhaseNext (q := q) s
        (couponNodeObserverRun (q := q) s word) e := by
  simp only [couponNodeObserverRun, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem couponNodeScanRunSnoc {n q : Nat}
    (s : Fin n) (word : List (Fin n)) (e : Fin n) :
    couponNodeScanRun (q := q) s (word ++ [e]) =
      couponAttemptPhaseNext (q := q) s
        (couponNodeScanRun (q := q) s word) e := by
  simp only [couponNodeScanRun, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- Each active observer has exactly one chronological stage shape.
In the scan constructor the launch word is MINIMAL: the observer was
still launching with exactly one mark immediately before the final
marked edge, so the scan suffix begins only after the second mark. -/
inductive CouponNodeStageHistory {n q : Nat} (s : Fin n) :
    List (Fin n) → CouponAttemptPhase n → Prop where
  | covering (clear : List (Fin n)) (mask : Fin n → Bool)
      (hmask :
        mask = clear.foldl maskDrop
          (fun e : Fin n =>
            canonicalMask ((compileAdvice q).t + 3)
              (protectedLabel s e))) :
      CouponNodeStageHistory s clear (.covering mask clear)
  | launching (clear launch : List (Fin n)) (hits : Nat)
      (hclear :
        lastAccept ((compileAdvice q).t + 3)
          (clear.map (protectedLabel s)) = 1)
      (hlaunch :
        couponNodeLaunchStoppedRun (q := q) s
          (.launching 0) launch = .launching hits)
      (hhits : hits = 0 ∨ hits = 1) :
      CouponNodeStageHistory s (clear ++ launch) (.launching hits)
  | scanning (clear launch scan : List (Fin n))
      (j : Nat) (once : List Nat)
      (hclear :
        lastAccept ((compileAdvice q).t + 3)
          (clear.map (protectedLabel s)) = 1)
      (hbefore :
        couponNodeLaunchStoppedRun (q := q) s
          (.launching 0) launch = .launching 1)
      (hscan :
        couponNodeScanRun (q := q) s scan = .scanning j once) :
      CouponNodeStageHistory s
        (clear ++ launch ++ [certSite s (n - 1)] ++ scan)
        (.scanning j once)

/-- An active kernel successor cannot have a terminal failed phase. -/
theorem couponNodeActiveNotFailed {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a b : CouponSeed fixed × CouponAttemptPhase n) (e : Fin n)
    (hstep :
      (couponTrialKernel ring fixed s).step a e = .active b) :
    couponAttemptPhaseNext (q := q) s a.2 e ≠ .failed := by
  intro hfailed
  have hterminal :
      (couponTrialKernel ring fixed s).step a e =
        .retry (couponSeedStep ring fixed s a.1 e) := by
    simp [couponTrialKernel, hfailed]
  rw [hterminal] at hstep
  cases hstep

/-- An active kernel successor cannot have a terminal success phase,
regardless of whether the physical sticky seen bit was set. -/
theorem couponNodeActiveNotSucceeded {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a b : CouponSeed fixed × CouponAttemptPhase n) (e : Fin n)
    (hstep :
      (couponTrialKernel ring fixed s).step a e = .active b) :
    couponAttemptPhaseNext (q := q) s a.2 e ≠ .succeeded := by
  intro hsuccess
  cases hseen :
      (couponSeedStep ring fixed s a.1 e).1.2.seen with
  | false =>
      have hterminal :
          (couponTrialKernel ring fixed s).step a e =
            .retry (couponSeedStep ring fixed s a.1 e) := by
        simp [couponTrialKernel, hsuccess, hseen]
      rw [hterminal] at hstep
      cases hstep
  | true =>
      have hterminal :
          (couponTrialKernel ring fixed s).step a e = .success := by
        simp [couponTrialKernel, hsuccess, hseen]
      rw [hterminal] at hstep
      cases hstep

/-- Active successors advance both projections along the same e. -/
theorem couponNodeActivePair {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a b : CouponSeed fixed × CouponAttemptPhase n) (e : Fin n)
    (hstep :
      (couponTrialKernel ring fixed s).step a e = .active b) :
    (couponSeedStep ring fixed s a.1 e,
      couponAttemptPhaseNext (q := q) s a.2 e) = b := by
  cases hp : couponAttemptPhaseNext (q := q) s a.2 e with
  | succeeded =>
      exact False.elim
        ((couponNodeActiveNotSucceeded ring fixed s a b e hstep) hp)
  | failed =>
      exact False.elim
        ((couponNodeActiveNotFailed ring fixed s a b e hstep) hp)
  | covering mask word =>
      simpa [couponTrialKernel, hp] using hstep
  | launching hits =>
      simpa [couponTrialKernel, hp] using hstep
  | scanning j once =>
      simpa [couponTrialKernel, hp] using hstep


end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (AttemptNode RetryKernel)

/-- The cover / live launch / minimal second mark / scan partition
is stable under every actual nonterminal observer step. -/
theorem couponNodeStageHistoryStep {n q : Nat}
    (s : Fin n) (word : List (Fin n))
    (phase : CouponAttemptPhase n)
    (h : CouponNodeStageHistory (q := q) s word phase)
    (e : Fin n)
    (hnotSuccess :
      couponAttemptPhaseNext (q := q) s phase e ≠ .succeeded)
    (hnotFailure :
      couponAttemptPhaseNext (q := q) s phase e ≠ .failed) :
    CouponNodeStageHistory (q := q) s (word ++ [e])
      (couponAttemptPhaseNext (q := q) s phase e) := by
  cases h with
  | covering _ mask hmask =>
      by_cases hzero : maskSize (maskDrop mask e) = 0
      · by_cases haccept :
          lastAccept ((compileAdvice q).t + 3)
            ((word ++ [e]).map (protectedLabel s)) = 1
        · have hnormal :
              lastAccept ((compileAdvice q).t + 3)
                (word.map (protectedLabel s) ++ [protectedLabel s e]) = 1 := by
            simpa only [List.map_append, List.map_cons, List.map_nil]
              using haccept
          have hphase :
              couponAttemptPhaseNext (q := q) s
                (.covering mask word) e = .launching 0 := by
            simp [couponAttemptPhaseNext, hzero, hnormal,
              List.map_append]
          rw [hphase]
          simpa only [List.append_nil] using
            (CouponNodeStageHistory.launching (q := q)
              (word ++ [e]) [] 0 haccept rfl (Or.inl rfl))
        · have hnormal :
              ¬ lastAccept ((compileAdvice q).t + 3)
                (word.map (protectedLabel s) ++ [protectedLabel s e]) = 1 := by
            simpa only [List.map_append, List.map_cons, List.map_nil]
              using haccept
          have hphase :
              couponAttemptPhaseNext (q := q) s
                (.covering mask word) e = .failed := by
            simp [couponAttemptPhaseNext, hzero, hnormal,
              List.map_append]
          exact False.elim (hnotFailure hphase)
      · have hphase :
            couponAttemptPhaseNext (q := q) s
              (.covering mask word) e =
              .covering (maskDrop mask e) (word ++ [e]) := by
          simp [couponAttemptPhaseNext, hzero]
        have hmaskNext :
            maskDrop mask e =
              (word ++ [e]).foldl maskDrop
                (fun i : Fin n =>
                  canonicalMask ((compileAdvice q).t + 3)
                    (protectedLabel s i)) := by
          rw [List.foldl_append]
          change maskDrop mask e =
            maskDrop
              (word.foldl maskDrop
                (fun i : Fin n =>
                  canonicalMask ((compileAdvice q).t + 3)
                    (protectedLabel s i))) e
          rw [← hmask]
        rw [hphase]
        exact CouponNodeStageHistory.covering (q := q)
          (word ++ [e]) (maskDrop mask e) hmaskNext
  | launching clear launch hits hclear hlaunch hhits =>
      by_cases hmark : e = certSite s (n - 1)
      · subst e
        rcases hhits with hzero | hone
        · subst hits
          have hphase :
              couponAttemptPhaseNext (q := q) s
                (.launching 0) (certSite s (n - 1)) =
                .launching 1 := by
            simp [couponAttemptPhaseNext]
          have hlaunchNext :
              couponNodeLaunchStoppedRun (q := q) s
                (.launching 0)
                (launch ++ [certSite s (n - 1)]) = .launching 1 := by
            rw [couponNodeLaunchStoppedRunAppend, hlaunch]
            simp [couponNodeLaunchStoppedRun, couponNodeLaunchStoppedStep,
              couponAttemptPhaseNext]
          rw [hphase]
          simpa only [List.append_assoc] using
            (CouponNodeStageHistory.launching (q := q)
              clear (launch ++ [certSite s (n - 1)])
              1 hclear hlaunchNext (Or.inr rfl))
        · subst hits
          have hphase :
              couponAttemptPhaseNext (q := q) s
                (.launching 1) (certSite s (n - 1)) =
                .scanning 0 [] := by
            simp [couponAttemptPhaseNext]
          rw [hphase]
          simpa only [List.append_assoc, List.append_nil] using
            (CouponNodeStageHistory.scanning (q := q)
              clear launch [] 0 [] hclear hlaunch rfl)
      · cases hout : outsideLaunch (q := q) s e with
        | true =>
            have hphase :
                couponAttemptPhaseNext (q := q) s
                  (.launching hits) e = .launching hits := by
              simp [couponAttemptPhaseNext, hmark, hout]
            have hlaunchNext :
                couponNodeLaunchStoppedRun (q := q) s
                  (.launching 0) (launch ++ [e]) =
                    .launching hits := by
              rw [couponNodeLaunchStoppedRunAppend, hlaunch]
              simp [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep,
                couponAttemptPhaseNext, hmark, hout]
            rw [hphase]
            simpa only [List.append_assoc] using
              (CouponNodeStageHistory.launching (q := q)
                clear (launch ++ [e]) hits
                hclear hlaunchNext hhits)
        | false =>
            have hphase :
                couponAttemptPhaseNext (q := q) s
                  (.launching hits) e = .failed := by
              simp [couponAttemptPhaseNext, hmark, hout]
            exact False.elim (hnotFailure hphase)
  | scanning clear launch scan j once hclear hbefore hscan =>
      cases htolerant :
          tolerantScanStep s (compileAdvice q).t
            (.live j once) e with
      | failed =>
          have hphase :
              couponAttemptPhaseNext (q := q) s
                (.scanning j once) e = .failed := by
            simp [couponAttemptPhaseNext, htolerant]
          exact False.elim (hnotFailure hphase)
      | live k onceNext =>
          by_cases hdone : (compileAdvice q).t ≤ k
          · have hphase :
                couponAttemptPhaseNext (q := q) s
                  (.scanning j once) e = .succeeded := by
              simp [couponAttemptPhaseNext, htolerant, hdone]
            exact False.elim (hnotSuccess hphase)
          · have hphase :
                couponAttemptPhaseNext (q := q) s
                  (.scanning j once) e = .scanning k onceNext := by
              simp [couponAttemptPhaseNext, htolerant, hdone]
            have hscanNext :
                couponNodeScanRun (q := q) s (scan ++ [e]) =
                  .scanning k onceNext := by
              rw [couponNodeScanRunSnoc, hscan, hphase]
            rw [hphase]
            simpa only [List.append_assoc] using
              (CouponNodeStageHistory.scanning (q := q)
                clear launch (scan ++ [e])
                k onceNext hclear hbefore hscanNext)

/-- Structural elimination on a VARIABLE indexed history avoids
dependent-elimination errors at a fixed scanning expression. -/
theorem couponNodeStageHistoryScanWitness {n q : Nat}
    (s : Fin n) (word : List (Fin n))
    (phase : CouponAttemptPhase n) (j : Nat) (once : List Nat)
    (h : CouponNodeStageHistory (q := q) s word phase)
    (hphase : phase = .scanning j once) :
    ∃ (clear launch scan : List (Fin n)),
      word = clear ++ launch ++ [certSite s (n - 1)] ++ scan ∧
      lastAccept ((compileAdvice q).t + 3)
        (clear.map (protectedLabel s)) = 1 ∧
      couponNodeLaunchStoppedRun (q := q) s
        (.launching 0) launch = .launching 1 ∧
      couponNodeScanRun (q := q) s scan = .scanning j once := by
  cases h with
  | covering _ mask hmask =>
      cases hphase
  | launching clear launch hits hclear hlaunch hhits =>
      cases hphase
  | scanning clear launch scan index seen hclear hlaunch hscan =>
      cases hphase
      exact ⟨clear, launch, scan, rfl, hclear, hlaunch, hscan⟩

/-- A terminal-success edge from a history-carrying active observer
must originate in the scanning stage, not covering or launching. -/
theorem couponNodeStageHistorySuccessOrigin {n q : Nat}
    (s : Fin n) (word : List (Fin n))
    (phase : CouponAttemptPhase n) (e : Fin n)
    (h : CouponNodeStageHistory (q := q) s word phase)
    (hsuccess :
      couponAttemptPhaseNext (q := q) s phase e = .succeeded) :
    ∃ (j : Nat) (once : List Nat), phase = .scanning j once := by
  cases h with
  | covering _ mask hmask =>
      simp [couponAttemptPhaseNext] at hsuccess
      (repeat' split at hsuccess) <;> cases hsuccess
  | launching clear launch hits hclear hlaunch hhits =>
      simp [couponAttemptPhaseNext] at hsuccess
      (repeat' split at hsuccess) <;> cases hsuccess
  | scanning clear launch scan j once hclear hlaunch hscan =>
      exact ⟨j, once, rfl⟩

/-- Complete physically reached active-node history. -/
def CouponNodeTrace {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (origin : CouponSeed fixed)
    (word : List (Fin n))
    (a : CouponSeed fixed × CouponAttemptPhase n) : Prop :=
  a.1 = couponNodeSeedRun ring fixed s origin word ∧
  a.2 = couponNodeObserverRun (q := q) s word ∧
  CouponNodeStageHistory (q := q) s word a.2

/-- The same physical edge extends all three provenance certificates. -/
theorem couponNodeTraceStep {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (origin : CouponSeed fixed) (word : List (Fin n))
    (a b : CouponSeed fixed × CouponAttemptPhase n) (e : Fin n)
    (h : CouponNodeTrace ring fixed s origin word a)
    (hstep :
      (couponTrialKernel ring fixed s).step a e = .active b) :
    CouponNodeTrace ring fixed s origin (word ++ [e]) b := by
  obtain ⟨hseed, hphase, hstage⟩ := h
  have hpair := couponNodeActivePair ring fixed s a b e hstep
  have hseedNext :
      b.1 = couponSeedStep ring fixed s a.1 e :=
    (congrArg Prod.fst hpair).symm
  have hphaseNext :
      b.2 = couponAttemptPhaseNext (q := q) s a.2 e :=
    (congrArg Prod.snd hpair).symm
  have hstageNext :=
    couponNodeStageHistoryStep (q := q) s word a.2 hstage e
      (couponNodeActiveNotSucceeded ring fixed s a b e hstep)
      (couponNodeActiveNotFailed ring fixed s a b e hstep)
  constructor
  · rw [hseedNext, couponNodeSeedRunSnoc, ← hseed]
  constructor
  · rw [hphaseNext, couponNodeObserverRunSnoc, ← hphase]
  · rw [hphaseNext]
    exact hstageNext

/-- Absorbing single-attempt terminal tags carry no active history. -/
def CouponNodeTraceAtNode {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (origin : CouponSeed fixed) (word : List (Fin n)) :
    AttemptNode
      (CouponSeed fixed × CouponAttemptPhase n)
      (CouponSeed fixed) → Prop
  | .active a => CouponNodeTrace ring fixed s origin word a
  | .retry _ => True
  | .success => True

theorem couponNodeTraceAtNodeStep {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (origin : CouponSeed fixed) (word : List (Fin n))
    (node : AttemptNode
      (CouponSeed fixed × CouponAttemptPhase n)
      (CouponSeed fixed))
    (e : Fin n)
    (h : CouponNodeTraceAtNode ring fixed s origin word node) :
    CouponNodeTraceAtNode ring fixed s origin (word ++ [e])
      (Prob.attemptStepper
        (couponTrialKernel ring fixed s) node e) := by
  cases node with
  | success =>
      trivial
  | retry seed =>
      trivial
  | active a =>
      change CouponNodeTrace ring fixed s origin word a at h
      cases hk : (couponTrialKernel ring fixed s).step a e with
      | success =>
          simpa only [Prob.attemptStepper, hk,
            CouponNodeTraceAtNode] using True.intro
      | retry seed =>
          simpa only [Prob.attemptStepper, hk,
            CouponNodeTraceAtNode] using True.intro
      | active b =>
          have hnext := couponNodeTraceStep
            ring fixed s origin word a b e h hk
          simpa only [Prob.attemptStepper, hk,
            CouponNodeTraceAtNode] using hnext

/-- Own induction over the literal scheduler witness, not a guessed
future phase or an independent regenerated physical seed. -/
theorem couponNodeTraceRun {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (origin : CouponSeed fixed) :
    ∀ (node : AttemptNode
        (CouponSeed fixed × CouponAttemptPhase n)
        (CouponSeed fixed))
      (beforeWord rest : List (Fin n)),
      CouponNodeTraceAtNode ring fixed s origin beforeWord node →
      CouponNodeTraceAtNode ring fixed s origin (beforeWord ++ rest)
        (LDSinkBoundedKernel.run
          (Prob.attemptStepper (couponTrialKernel ring fixed s))
          node rest) := by
  intro node beforeWord rest
  induction rest generalizing node beforeWord with
  | nil =>
      intro h
      simpa only [List.append_nil, LDSinkBoundedKernel.run] using h
  | cons e rest ih =>
      intro h
      have hstep :=
        couponNodeTraceAtNodeStep
          ring fixed s origin beforeWord node e h
      have htail := ih
        (Prob.attemptStepper
          (couponTrialKernel ring fixed s) node e)
        (beforeWord ++ [e]) hstep
      change CouponNodeTraceAtNode ring fixed s origin
        (beforeWord ++ (e :: rest))
        (LDSinkBoundedKernel.run
          (Prob.attemptStepper (couponTrialKernel ring fixed s))
          (Prob.attemptStepper (couponTrialKernel ring fixed s)
            node e) rest)
      have hword :
          beforeWord ++ (e :: rest) =
            (beforeWord ++ [e]) ++ rest := by
        simp only [List.append_assoc, List.singleton_append,
          List.nil_append]
      rw [hword]
      exact htail

/-- The actual starting physical seed and initial cover are unchanged. -/
theorem couponNodeTraceStart {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (origin : CouponSeed fixed) :
    CouponNodeTraceAtNode ring fixed s origin []
      (.active ((couponTrialKernel ring fixed s).start origin)) := by
  change CouponNodeTrace ring fixed s origin []
    (origin, couponAttemptStart (q := q) s)
  refine ⟨rfl, rfl, ?_⟩
  change CouponNodeStageHistory (q := q) s []
    (.covering
      (fun e : Fin n =>
        canonicalMask ((compileAdvice q).t + 3)
          (protectedLabel s e)) [])
  exact CouponNodeStageHistory.covering (q := q) []
    (fun e : Fin n =>
      canonicalMask ((compileAdvice q).t + 3)
        (protectedLabel s e)) rfl

/-- Reachability yields a chronological source seed and a single
physical/observer history along the original stopped scheduler word. -/
theorem couponNodeReachableTrace {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (hreach : couponNodeReachable ring fixed s a) :
    ∃ (origin : CouponSeed fixed) (word : List (Fin n)),
      LDSinkBoundedKernel.run
        (Prob.attemptStepper (couponTrialKernel ring fixed s))
        (.active ((couponTrialKernel ring fixed s).start origin))
        word = .active a ∧
      CouponNodeTrace ring fixed s origin word a := by
  obtain ⟨origin, word, hrun⟩ := hreach
  have hstart := couponNodeTraceStart ring fixed s origin
  have hhistory :=
    couponNodeTraceRun ring fixed s origin
      (.active ((couponTrialKernel ring fixed s).start origin))
      [] word hstart
  simp only [List.nil_append] at hhistory
  rw [hrun] at hhistory
  change CouponNodeTrace ring fixed s origin word a at hhistory
  exact ⟨origin, word, hrun, hhistory⟩

/-- The scan phase is genuinely reached from an accepted cover and a
minimal launch traceWord ending with its FIRST second marked edge. -/
theorem couponNodeReachableScanHistory {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (j : Nat) (once : List Nat)
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .scanning j once) :
    ∃ (origin : CouponSeed fixed)
      (clear launch scan : List (Fin n)),
      lastAccept ((compileAdvice q).t + 3)
        (clear.map (protectedLabel s)) = 1 ∧
      couponNodeLaunchStoppedRun (q := q) s
        (.launching 0) launch = .launching 1 ∧
      couponNodeScanRun (q := q) s scan = .scanning j once ∧
      a.1 = couponNodeSeedRun ring fixed s origin
        (clear ++ launch ++ [certSite s (n - 1)] ++ scan) ∧
      a.2 = couponNodeObserverRun (q := q) s
        (clear ++ launch ++ [certSite s (n - 1)] ++ scan) := by
  obtain ⟨origin, word, _, htrace⟩ :=
    couponNodeReachableTrace ring fixed s a hreach
  obtain ⟨hseed, hobserver, hstage⟩ := htrace
  obtain ⟨clear, launch, scan, hword, hclear, hlaunch, hscan⟩ :=
    couponNodeStageHistoryScanWitness (q := q)
      s word a.2 j once hstage hphase
  refine ⟨origin, clear, launch, scan,
    hclear, hlaunch, hscan, ?_, ?_⟩
  · rw [hword] at hseed
    exact hseed
  · rw [hword] at hobserver
    exact hobserver

/-- Physical projection of the seed fold onto the unchanged
freshGhostStep dynamics, including all private scratch fields. -/
theorem couponNodeSeedRunPhysical {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (origin : CouponSeed fixed) (word : List (Fin n)) :
    (couponNodeSeedRun ring fixed s origin word).1 =
      LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
        origin.1 word := by
  induction word generalizing origin with
  | nil =>
      rfl
  | cons e rest ih =>
      change
        (couponNodeSeedRun ring fixed s
          (couponSeedStep ring fixed s origin e) rest).1 =
        LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
          (freshGhostStep ring fixed s origin.1 e) rest
      exact ih (couponSeedStep ring fixed s origin e)

theorem couponNodeSeedRunAppend {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (origin : CouponSeed fixed) (xs ys : List (Fin n)) :
    couponNodeSeedRun ring fixed s origin (xs ++ ys) =
      couponNodeSeedRun ring fixed s
        (couponNodeSeedRun ring fixed s origin xs) ys := by
  simp only [couponNodeSeedRun, List.foldl_append]

/-- The second marked edge is exactly the last selected edge of the
minimal launch traceWord, not a hypothetical next edge after a scan. -/
theorem couponNodeMinimalLaunchStops {n q : Nat}
    (s : Fin n) (launch : List (Fin n))
    (hbefore :
      couponNodeLaunchStoppedRun (q := q) s
        (.launching 0) launch = .launching 1) :
    couponNodeLaunchStoppedRun (q := q) s (.launching 0)
      (launch ++ [certSite s (n - 1)]) = .scanning 0 [] := by
  rw [couponNodeLaunchStoppedRunAppend, hbefore]
  simp [couponNodeLaunchStoppedRun, couponNodeLaunchStoppedStep,
    couponAttemptPhaseNext]

/-- Physical launch derived from a *reached* scan node rather than a
future invented scan state: the clear boundary is an actual physical
traceWord from the original seed, and the recognizer is the exact online
launch observer. This theorem deliberately retains any after suffix
from two_hit_launch_after_cover instead of silently discarding it. -/
theorem couponNodeReachableScanLaunchReady {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (j : Nat) (once : List Nat)
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .scanning j once) :
    ∃ (origin : CouponSeed fixed)
      (clear launch scan before between after : List (Fin n)),
      a.1 = couponNodeSeedRun ring fixed s origin
        (clear ++ launch ++ [certSite s (n - 1)] ++ scan) ∧
      launch ++ [certSite s (n - 1)] =
        before ++ [certSite s (n - 1)] ++
          between ++ [certSite s (n - 1)] ++ after ∧
      CouponLaunchReady fixed s ht
        (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
          (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
            origin.1 clear)
          (before ++ [certSite s (n - 1)] ++
            between ++ [certSite s (n - 1)])) := by
  obtain ⟨origin, clear, launch, scan,
      hclear, hbefore, _, hseed, _⟩ :=
    couponNodeReachableScanHistory ring fixed s
      a j once hreach hphase
  have hstop := couponNodeMinimalLaunchStops s launch hbefore
  obtain ⟨before, between, after, hsplit, hready⟩ :=
    couponNodeLaunchReadyFromStoppedObserver
      ring fixed s ht hn hroot origin clear
      (launch ++ [certSite s (n - 1)])
      hclear ⟨0, [], hstop⟩
  exact ⟨origin, clear, launch, scan, before, between, after,
    hseed, hsplit, hready⟩


/-- A stopped live one-hit launch cannot contain any marked or
monitored nonmarked edge: only outside delays preserve that state. -/
theorem couponNodeLaunchLiveOneAllOutside {n q : Nat}
    (s : Fin n) :
    ∀ word : List (Fin n),
      couponNodeLaunchStoppedRun (q := q) s
          (.launching 1) word = .launching 1 →
      ∀ e, e ∈ word → outsideLaunch (q := q) s e = true := by
  intro word
  induction word with
  | nil =>
      intro _ e he
      cases he
  | cons first rest ih =>
      intro h e he
      by_cases hmark : first = certSite s (n - 1)
      · subst first
        have hbad :
            couponNodeLaunchStoppedRun (q := q) s
              (.scanning 0 []) rest = .launching 1 := by
          simpa [couponNodeLaunchStoppedRun,
            couponNodeLaunchStoppedStep,
            couponAttemptPhaseNext] using h
        rw [couponNodeLaunchStoppedRunScan] at hbad
        cases hbad
      · cases hout : outsideLaunch (q := q) s first with
        | false =>
            have hbad :
                couponNodeLaunchStoppedRun (q := q) s
                  .failed rest = .launching 1 := by
              simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep,
                couponAttemptPhaseNext, hmark, hout] using h
            rw [couponNodeLaunchStoppedRunFailed] at hbad
            cases hbad
        | true =>
            have htail :
                couponNodeLaunchStoppedRun (q := q) s
                  (.launching 1) rest = .launching 1 := by
              simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep,
                couponAttemptPhaseNext, hmark, hout] using h
            rcases List.mem_cons.mp he with heq | hrest
            · subst e
              exact hout
            · exact ih htail e hrest

/-- The live one-mark traceWord has exactly one designated marked edge.
All edges before and after that first mark are outside the launch
family. This is stronger than the absorbing two-mark recognizer. -/
theorem couponNodeLaunchLiveOneSplit {n q : Nat}
    (s : Fin n) :
    ∀ launch : List (Fin n),
      couponNodeLaunchStoppedRun (q := q) s
          (.launching 0) launch = .launching 1 →
      ∃ before between : List (Fin n),
        launch = before ++ [certSite s (n - 1)] ++ between ∧
        (∀ e, e ∈ before → outsideLaunch (q := q) s e = true) ∧
        (∀ e, e ∈ between → outsideLaunch (q := q) s e = true) := by
  intro launch
  induction launch with
  | nil =>
      intro h
      cases h
  | cons first rest ih =>
      intro h
      by_cases hmark : first = certSite s (n - 1)
      · subst first
        have htail :
            couponNodeLaunchStoppedRun (q := q) s
              (.launching 1) rest = .launching 1 := by
          simpa [couponNodeLaunchStoppedRun,
            couponNodeLaunchStoppedStep,
            couponAttemptPhaseNext] using h
        refine ⟨[], rest, rfl, ?_, ?_⟩
        · intro e he
          cases he
        · exact couponNodeLaunchLiveOneAllOutside s rest htail
      · cases hout : outsideLaunch (q := q) s first with
        | false =>
            have hbad :
                couponNodeLaunchStoppedRun (q := q) s
                  .failed rest = .launching 1 := by
              simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep,
                couponAttemptPhaseNext, hmark, hout] using h
            rw [couponNodeLaunchStoppedRunFailed] at hbad
            cases hbad
        | true =>
            have htail :
                couponNodeLaunchStoppedRun (q := q) s
                  (.launching 0) rest = .launching 1 := by
              simpa [couponNodeLaunchStoppedRun,
                couponNodeLaunchStoppedStep,
                couponAttemptPhaseNext, hmark, hout] using h
            obtain ⟨before, between, hword, hbefore, hbetween⟩ := ih htail
            refine ⟨first :: before, between, ?_, ?_, hbetween⟩
            · simpa only [List.cons_append] using
                congrArg (List.cons first) hword
            · intro e he
              rcases List.mem_cons.mp he with heq | hrest
              · subst e
                exact hout
              · exact hbefore e hrest

/-- Exact physical second launch at the genuine scan-entry boundary,
with no artificial after suffix, using protected_coupon_clears on the
REAL accepted-cover traceWord and the REAL initial physical seed. -/
theorem couponNodeReachableScanReadyAtBoundary {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (j : Nat) (once : List Nat)
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .scanning j once) :
    ∃ (origin : CouponSeed fixed)
      (clear before between scan : List (Fin n)),
      a.1 = couponNodeSeedRun ring fixed s origin
        (clear ++
          (before ++ [certSite s (n - 1)] ++
            between ++ [certSite s (n - 1)]) ++ scan) ∧
      couponNodeScanRun (q := q) s scan = .scanning j once ∧
      CouponLaunchReady fixed s ht
        (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
          (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
            origin.1 clear)
          (before ++ [certSite s (n - 1)] ++
            between ++ [certSite s (n - 1)])) := by
  obtain ⟨origin, clear, launch, scan,
      hclear, hbefore, hscan, hseed, _⟩ :=
    couponNodeReachableScanHistory ring fixed s a j once hreach hphase
  obtain ⟨before, between, hlaunch, houtBefore, houtBetween⟩ :=
    couponNodeLaunchLiveOneSplit s launch hbefore
  have hprojection :
      (LDSinkBoundedKernel.run
        (freshGhostStep ring fixed s) origin.1 clear).1 =
        runList ring fixed origin.1.1 clear :=
    fixedGhostRun_projection ring fixed s origin.1 clear
  have hfrozen : Frozen fixed
      (LDSinkBoundedKernel.run
        (freshGhostStep ring fixed s) origin.1 clear).1 := by
    rw [hprojection]
    exact runList_frozen ring fixed origin.1.1 clear origin.2
  have hslots :
      ∀ k : Fin ((compileAdvice q).t + 2),
        SlotClear
          (LDSinkBoundedKernel.run
            (freshGhostStep ring fixed s) origin.1 clear).1
          (certSite s (n - 1 + k.val)) := by
    intro k
    rw [hprojection]
    exact protected_coupon_clears
      ring fixed origin.1.1 s clear hn hclear k
  have hready :=
    launch_marked_ready ring fixed s ht hn hroot
      (LDSinkBoundedKernel.run
        (freshGhostStep ring fixed s) origin.1 clear)
      hfrozen hslots before between
      (fun e he =>
        (outsideLaunch_true_iff s hn e).mp (houtBefore e he))
      (fun e he =>
        (outsideLaunch_true_iff s hn e).mp (houtBetween e he))
  refine ⟨origin, clear, before, between, scan, ?_, hscan, hready⟩
  rw [hlaunch] at hseed
  simpa only [List.append_assoc] using hseed


/-- The scan phase compresses the terminal live tolerant state into
.succeeded, while failures remain synchronously failed. -/
inductive CouponNodeScanSync (t : Nat) {n : Nat} :
    CouponAttemptPhase n → TolerantScanState → Prop where
  | live (j : Nat) (A : List Nat) (hj : j < t) :
      CouponNodeScanSync t (.scanning j A) (.live j A)
  | success (j : Nat) (A : List Nat) (hj : t ≤ j) :
      CouponNodeScanSync t .succeeded (.live j A)
  | failed :
      CouponNodeScanSync t .failed .failed

/-- Each literal scan observer edge simulates the same
tolerantScanStep edge, including the terminal completion test. -/
theorem couponNodeScanSyncStep {n q : Nat}
    (s : Fin n)
    (phase : CouponAttemptPhase n) (state : TolerantScanState)
    (e : Fin n)
    (h : CouponNodeScanSync (compileAdvice q).t phase state) :
    CouponNodeScanSync (compileAdvice q).t
      (couponAttemptPhaseNext (q := q) s phase e)
      (tolerantScanStep s (compileAdvice q).t state e) := by
  cases h with
  | live j A hj =>
      cases hs :
          tolerantScanStep s (compileAdvice q).t
            (.live j A) e with
      | failed =>
          simpa [couponAttemptPhaseNext, hs] using
            (CouponNodeScanSync.failed
              (t := (compileAdvice q).t) (n := n))
      | live k nextA =>
          by_cases hdone : (compileAdvice q).t ≤ k
          · simpa [couponAttemptPhaseNext, hs, hdone] using
              (CouponNodeScanSync.success (n := n) k nextA hdone)
          · have hlt : k < (compileAdvice q).t := by omega
            simpa [couponAttemptPhaseNext, hs, hdone] using
              (CouponNodeScanSync.live (n := n) k nextA hlt)
  | success j A hj =>
      have hstay :
          tolerantScanStep s (compileAdvice q).t
            (.live j A) e = .live j A := by
        simp [tolerantScanStep, hj]
      simpa [couponAttemptPhaseNext, hstay] using
        (CouponNodeScanSync.success (n := n) j A hj)
  | failed =>
      exact CouponNodeScanSync.failed

/-- General simulation over the actual chronological scan word. -/
theorem couponNodeScanSyncRun {n q : Nat}
    (s : Fin n)
    (phase : CouponAttemptPhase n) (state : TolerantScanState)
    (word : List (Fin n))
    (h : CouponNodeScanSync (compileAdvice q).t phase state) :
    CouponNodeScanSync (compileAdvice q).t
      (word.foldl (couponAttemptPhaseNext (q := q) s) phase)
      (word.foldl (tolerantScanStep s (compileAdvice q).t) state) := by
  induction word generalizing phase state with
  | nil =>
      exact h
  | cons e rest ih =>
      change CouponNodeScanSync (compileAdvice q).t
        (rest.foldl (couponAttemptPhaseNext (q := q) s)
          (couponAttemptPhaseNext (q := q) s phase e))
        (rest.foldl (tolerantScanStep s (compileAdvice q).t)
          (tolerantScanStep s (compileAdvice q).t state e))
      exact ih _ _ (couponNodeScanSyncStep (q := q)
        s phase state e h)

theorem couponNodeFoldRun {S : Type} {n : Nat}
    (step : S → Fin n → S) (x : S) (word : List (Fin n)) :
    word.foldl step x = LDSinkBoundedKernel.run step x word := by
  induction word generalizing x with
  | nil =>
      rfl
  | cons e rest ih =>
      change
        rest.foldl step (step x e) =
          LDSinkBoundedKernel.run step (step x e) rest
      exact ih (step x e)

/-- The scan synchronizer has exactly the same terminal-success
predicate as the underlying tolerant scanner. Both indices are
variables here, so constructor elimination has no dependent mismatch. -/
theorem couponNodeScanSyncSuccessIff {n t : Nat}
    (phase : CouponAttemptPhase n) (state : TolerantScanState)
    (h : CouponNodeScanSync t phase state) :
    phase = .succeeded ↔ tolerantScanSuccess t state := by
  cases h with
  | live j A hj =>
      have hnot : ¬ t ≤ j := by omega
      simp [tolerantScanSuccess, hnot]
  | success j A hj =>
      simp [tolerantScanSuccess, hj]
  | failed =>
      simp [tolerantScanSuccess]

/-- Observer scan success equals the original tolerantAccept
certificate, including an arbitrary terminal suffix. -/
theorem couponNodeScanWordAcceptIff {n q : Nat}
    (s : Fin n) (ht : 0 < (compileAdvice q).t)
    (word : List (Fin n)) :
    couponNodeScanRun (q := q) s word = .succeeded ↔
      tolerantAccept s (compileAdvice q).t word 0 [] = 1 := by
  have hsync :
      CouponNodeScanSync (compileAdvice q).t
        (couponNodeScanRun (q := q) s word)
        (LDSinkBoundedKernel.run
          (tolerantScanStep s (compileAdvice q).t)
          (.live 0 []) word) := by
    have hh := couponNodeScanSyncRun (q := q)
      s (.scanning 0 []) (.live 0 []) word
      (CouponNodeScanSync.live (n := n) 0 [] ht)
    simpa only [couponNodeScanRun, couponNodeFoldRun] using hh
  have hiff := couponNodeScanSyncSuccessIff
    (couponNodeScanRun (q := q) s word)
    (LDSinkBoundedKernel.run
      (tolerantScanStep s (compileAdvice q).t)
      (.live 0 []) word) hsync
  rw [tolerant_accept_eq_chain_success
    s (compileAdvice q).t 0 [] word]
  by_cases hdone :
      tolerantScanSuccess (compileAdvice q).t
        (LDSinkBoundedKernel.run
          (tolerantScanStep s (compileAdvice q).t)
          (.live 0 []) word)
  · simpa [hdone] using hiff
  · simpa [hdone] using hiff

/-- On a genuinely reached scan node, the very scheduler edge that
makes the observer succeeded also sets the REAL sticky ghost seen bit.
The proof uses the exact physical history and the original hbad,
rather than replacing the seed with an independently prepared state. -/
theorem couponNodeReachedScanSeen {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (j : Nat) (once : List Nat) (e : Fin n)
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .scanning j once)
    (hsuccess :
      couponAttemptPhaseNext (q := q) s a.2 e = .succeeded) :
    (couponSeedStep ring fixed s a.1 e).1.2.seen = true := by
  obtain ⟨origin, clear, before, between, scan,
      hseed, hscan, hready⟩ :=
    couponNodeReachableScanReadyAtBoundary
      ring fixed s ht hn hroot a j once hreach hphase
  have hscanStep :
      couponAttemptPhaseNext (q := q) s
        (.scanning j once) e = .succeeded := by
    rw [← hphase]
    exact hsuccess
  have hscanAccepted :
      tolerantAccept s (compileAdvice q).t
        (scan ++ [e]) 0 [] = 1 := by
    apply (couponNodeScanWordAcceptIff
      (q := q) s (by omega) (scan ++ [e])).mp
    rw [couponNodeScanRunSnoc, hscan, hscanStep]
  have hinv : TolerantInvariant fixed s
      ⟨0, by omega⟩ []
      (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
        (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
          origin.1 clear)
        (before ++ [certSite s (n - 1)] ++
          between ++ [certSite s (n - 1)])) :=
    tolerant_invariant_of_launch fixed s ht _ hready
  have hgood :=
    tolerant_scan_word_sound ring fixed s ht hn hroot hbad
      (scan ++ [e]) ⟨0, by omega⟩ []
      (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
        (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
          origin.1 clear)
        (before ++ [certSite s (n - 1)] ++
          between ++ [certSite s (n - 1)]))
      hinv hscanAccepted
  have hphysical : a.1.1 =
      LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
        (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
          (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
            origin.1 clear)
          (before ++ [certSite s (n - 1)] ++
            between ++ [certSite s (n - 1)]))
        scan := by
    have hval := congrArg Subtype.val hseed
    rw [couponNodeSeedRunPhysical] at hval
    calc
      a.1.1 =
          LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
            origin.1
            (clear ++
              (before ++ [certSite s (n - 1)] ++
                between ++ [certSite s (n - 1)]) ++ scan) := hval
      _ = _ := by
        rw [fixedRun_append, fixedRun_append]
  have hlast :
      freshGhostGood (freshGhostStep ring fixed s a.1.1 e) := by
    rw [couponNodeRunSnoc] at hgood
    rw [← hphysical] at hgood
    exact hgood
  change freshGhostGood ((couponSeedStep ring fixed s a.1 e).1)
  rw [couponSeedStep_physical]
  exact hlast

/-- Failure-scoped seen-flag soundness for ALL genuinely reached
observer-success edges, with no forged future scan state. -/
theorem couponNodeSeenFlagSoundnessOnFailure {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (e : Fin n)
    (hreach : couponNodeReachable ring fixed s a)
    (hsuccess :
      couponAttemptPhaseNext (q := q) s a.2 e = .succeeded) :
    (couponSeedStep ring fixed s a.1 e).1.2.seen = true := by
  obtain ⟨origin, word, _, htrace⟩ :=
    couponNodeReachableTrace ring fixed s a hreach
  obtain ⟨_, _, hstage⟩ := htrace
  obtain ⟨j, once, hphase⟩ :=
    couponNodeStageHistorySuccessOrigin
      (q := q) s word a.2 e hstage hsuccess
  exact couponNodeReachedScanSeen
    ring fixed s ht hn hroot hbad a j once e
    hreach hphase hsuccess

/-- Width reduction on a closed small numeral, without asking the
kernel to normalize an arbitrary large Compiled configuration. -/
theorem couponNodeAdviceWidthTwo :
    (compileAdvice 3).t = 2 := by
  rfl

theorem couponNodeAdviceWidthThree :
    (compileAdvice 5).t = 3 := by
  rfl

/-- On the failure-scoped hypotheses, a genuinely reached observer
success takes the concrete success branch of the RetryKernel itself.
There can be no false retry caused by a missing seen flag. -/
theorem couponNodeReachedSuccessKernelStep {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (e : Fin n)
    (hreach : couponNodeReachable ring fixed s a)
    (hsuccess :
      couponAttemptPhaseNext (q := q) s a.2 e = .succeeded) :
    (couponTrialKernel ring fixed s).step a e = .success := by
  have hseen := couponNodeSeenFlagSoundnessOnFailure
    ring fixed s ht hn hroot hbad a e hreach hsuccess
  simp [couponTrialKernel, hsuccess, hseen]


/-- The actual Fin n launch row: a single marked edge is a spike
disjoint from the outsideLaunch Boolean mask. The remaining n-1-|r|
scheduler edges are precisely the monitored, nonmarked failures. -/
theorem couponNodeLaunchSpikeSum {n : Nat}
    (r : Fin n → Bool) (a : Fin n) (ha : r a = false)
    (bad outside mark : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = a then mark else if r e then outside else bad)).sum =
      mark + ((n - 1 - maskSize r) * bad +
        maskSize r * outside) := by
  have hrow (e : Fin n) :
      (if e = a then mark else if r e then outside else bad) =
      (if e = a then mark else 0) +
        (if e = a then 0 else if r e then outside else bad) := by
    by_cases he : e = a <;> simp [he]
  calc
    _ = (List.ofFn (fun e : Fin n =>
          (if e = a then mark else 0) +
            (if e = a then 0 else if r e then outside else bad))).sum :=
        ofFn_sum_eq _ _ hrow
    _ = mark + ((n - 1 - maskSize r) * bad +
          maskSize r * outside) := by
        rw [ofFn_sum_add, FreshFixed.sum_spike,
          coupon_sum_excluding_mask r a ha bad outside]

/-- Exact active/retry value at launch hit count zero on EACH selected
physical edge of the original ring. -/
theorem couponNodeLaunchZeroEdge {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed) (e : Fin n) :
    couponAttemptNodeValue
      (couponNodeBudget n (compileAdvice q).t)
      (fun a : CouponSeed fixed × CouponAttemptPhase n =>
        couponNodePotential (q := q) s a.2)
      ((couponTrialKernel ring fixed s).step
        (seed, .launching 0) e) =
    if e = certSite s (n - 1) then
      couponNodeLaunchPotential n (compileAdvice q).t 1
    else if outsideLaunch (q := q) s e then
      couponNodeLaunchPotential n (compileAdvice q).t 0
    else couponNodeBudget n (compileAdvice q).t := by
  by_cases hmark : e = certSite s (n - 1)
  · subst e
    simp [couponTrialKernel, couponAttemptPhaseNext,
      couponAttemptNodeValue, couponNodePotential]
  · cases hout : outsideLaunch (q := q) s e with
    | true =>
        simp [couponTrialKernel, couponAttemptPhaseNext,
          couponAttemptNodeValue, couponNodePotential, hmark, hout]
    | false =>
        simp [couponTrialKernel, couponAttemptPhaseNext,
          couponAttemptNodeValue, couponNodePotential, hmark, hout]

/-- Full physical launch-zero successor sum, without an independent
launch clock and without a synthetic scheduler window. -/
theorem couponNodeLaunchZeroEdgeSum {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    (List.ofFn (fun e : Fin n =>
      couponAttemptNodeValue
        (couponNodeBudget n (compileAdvice q).t)
        (fun a : CouponSeed fixed × CouponAttemptPhase n =>
          couponNodePotential (q := q) s a.2)
        ((couponTrialKernel ring fixed s).step
          (seed, .launching 0) e))).sum =
      couponNodeLaunchPotential n (compileAdvice q).t 1 +
      ((n - 1 - maskSize (outsideLaunch (q := q) s)) *
        couponNodeBudget n (compileAdvice q).t +
      maskSize (outsideLaunch (q := q) s) *
        couponNodeLaunchPotential n (compileAdvice q).t 0) := by
  calc
    _ = (List.ofFn (fun e : Fin n =>
          if e = certSite s (n - 1) then
            couponNodeLaunchPotential n (compileAdvice q).t 1
          else if outsideLaunch (q := q) s e then
            couponNodeLaunchPotential n (compileAdvice q).t 0
          else couponNodeBudget n (compileAdvice q).t)).sum := by
        apply ofFn_sum_eq
        intro e
        exact couponNodeLaunchZeroEdge ring fixed s seed e
    _ = _ := couponNodeLaunchSpikeSum
      (outsideLaunch (q := q) s) (certSite s (n - 1))
      (outsideLaunch_mark_false s hn)
      (couponNodeBudget n (compileAdvice q).t)
      (couponNodeLaunchPotential n (compileAdvice q).t 0)
      (couponNodeLaunchPotential n (compileAdvice q).t 1)

/-- At launch hit count one, the marked successor is the genuine
initial scanning phase, not a second launch counter. -/
theorem couponNodeLaunchOneEdge {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed) (e : Fin n) :
    couponAttemptNodeValue
      (couponNodeBudget n (compileAdvice q).t)
      (fun a : CouponSeed fixed × CouponAttemptPhase n =>
        couponNodePotential (q := q) s a.2)
      ((couponTrialKernel ring fixed s).step
        (seed, .launching 1) e) =
    if e = certSite s (n - 1) then
      couponNodeScanPotential n (compileAdvice q).t 0 []
    else if outsideLaunch (q := q) s e then
      couponNodeLaunchPotential n (compileAdvice q).t 1
    else couponNodeBudget n (compileAdvice q).t := by
  by_cases hmark : e = certSite s (n - 1)
  · subst e
    simp [couponTrialKernel, couponAttemptPhaseNext,
      couponAttemptNodeValue, couponNodePotential]
  · cases hout : outsideLaunch (q := q) s e with
    | true =>
        simp [couponTrialKernel, couponAttemptPhaseNext,
          couponAttemptNodeValue, couponNodePotential, hmark, hout]
    | false =>
        simp [couponTrialKernel, couponAttemptPhaseNext,
          couponAttemptNodeValue, couponNodePotential, hmark, hout]

/-- Full physical launch-one successor sum for the repaired observer. -/
theorem couponNodeLaunchOneEdgeSum {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    (List.ofFn (fun e : Fin n =>
      couponAttemptNodeValue
        (couponNodeBudget n (compileAdvice q).t)
        (fun a : CouponSeed fixed × CouponAttemptPhase n =>
          couponNodePotential (q := q) s a.2)
        ((couponTrialKernel ring fixed s).step
          (seed, .launching 1) e))).sum =
      couponNodeScanPotential n (compileAdvice q).t 0 [] +
      ((n - 1 - maskSize (outsideLaunch (q := q) s)) *
        couponNodeBudget n (compileAdvice q).t +
      maskSize (outsideLaunch (q := q) s) *
        couponNodeLaunchPotential n (compileAdvice q).t 1) := by
  calc
    _ = (List.ofFn (fun e : Fin n =>
          if e = certSite s (n - 1) then
            couponNodeScanPotential n (compileAdvice q).t 0 []
          else if outsideLaunch (q := q) s e then
            couponNodeLaunchPotential n (compileAdvice q).t 1
          else couponNodeBudget n (compileAdvice q).t)).sum := by
        apply ofFn_sum_eq
        intro e
        exact couponNodeLaunchOneEdge ring fixed s seed e
    _ = _ := couponNodeLaunchSpikeSum
      (outsideLaunch (q := q) s) (certSite s (n - 1))
      (outsideLaunch_mark_false s hn)
      (couponNodeBudget n (compileAdvice q).t)
      (couponNodeLaunchPotential n (compileAdvice q).t 1)
      (couponNodeScanPotential n (compileAdvice q).t 0 [])

/-- Pure natural-number cancellation for the launch-zero Bellman row.
The two hypotheses are exactly the nontruncating credit equations for
the zero-hit and one-hit launch potentials. No rational arithmetic or
independence across attempt stages appears in this identity. -/
theorem couponNodeLaunchZeroCreditAlgebra
    (n L D P C Vzero Vone : Nat)
    (hL : 0 < L) (hLn : L ≤ n)
    (hzero : Vzero + C = P)
    (hone : Vone + (C * L + D * n) = P) :
    D * n +
      (Vone + ((L - 1) * P + (n - L) * Vzero)) =
      n * Vzero := by
  have hcount : L + (n - L) = n := by omega
  have hLP : P + (L - 1) * P = L * P := by
    calc
      _ = (1 + (L - 1)) * P := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = L * P := by
        have heq : 1 + (L - 1) = L := by omega
        rw [heq]
  have hweight :
      L * P + (n - L) * Vzero =
        n * Vzero + L * C := by
    calc
      _ = L * (Vzero + C) + (n - L) * Vzero := by
        rw [hzero]
      _ = (L + (n - L)) * Vzero + L * C := by
        rw [Nat.mul_add, Nat.add_mul]
        ac_rfl
      _ = n * Vzero + L * C := by rw [hcount]
  have hcredit :
      D * n +
          (Vone + ((L - 1) * P + (n - L) * Vzero)) +
        L * C =
      n * Vzero + L * C := by
    calc
      _ = (Vone + (C * L + D * n)) +
            (P * (L - 1) + (n - L) * Vzero) := by
        ac_rfl
      _ = P + (P * (L - 1) + (n - L) * Vzero) := by
        rw [hone]
      _ = L * P + (n - L) * Vzero := by
        rw [Nat.mul_comm P (L - 1)]
        rw [← Nat.add_assoc, hLP]
      _ = n * Vzero + L * C := hweight
  exact Nat.add_right_cancel hcredit

/-- Small closed integer scales; no compileAdvice expression
is evaluated by the kernel decision procedure. -/
theorem couponNodeDenominatorTwo :
    couponNodeDenominator 2 = 360 := by
  decide +kernel

theorem couponNodeDenominatorThree :
    couponNodeDenominator 3 = 9538560 := by
  decide +kernel

/-- Exact sufficient credit for the second marked launch edge.
The unrounded constants are proved separately at each named width. -/
theorem couponNodeLaunchOneNoTruncation (n t : Nat)
    (hwidth : t = 2 ∨ t = 3) :
    n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) * (t + 2) +
      n * couponNodeDenominator t ≤ couponNodeBudget n t := by
  have hlocal :
      (pPair t).1 * (harmonicPair (t + 3)).1 *
          freshFact (t + 3) * (t + 2) +
        couponNodeDenominator t ≤ couponNodeNumerator t := by
    rcases hwidth with ht | ht
    · rw [ht]
      rw [couponNodePairNumeratorTwo,
        couponNodeHarmonicNumeratorTwo,
        couponNodeDenominatorTwo, couponNodeNumerator_two]
      decide
    · rw [ht]
      rw [couponNodePairNumeratorThree,
        couponNodeHarmonicNumeratorThree,
        couponNodeDenominatorThree, couponNodeNumerator_three]
      decide
  have hmul := Nat.mul_le_mul_left n hlocal
  simpa only [couponNodeBudget, Nat.mul_add, Nat.mul_assoc] using hmul

/-- Nontruncating zero-hit credit. -/
theorem couponNodeLaunchZeroCreditExact (n t : Nat)
    (hwidth : t = 2 ∨ t = 3) :
    couponNodeLaunchPotential n t 0 +
      n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) =
      couponNodeBudget n t := by
  change
    (couponNodeBudget n t -
      n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3)) +
      n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) =
      couponNodeBudget n t
  exact Nat.sub_add_cancel
    (couponNodeLaunchZeroNoTruncation n t hwidth)

/-- The one-hit potential's two subtractions are nontruncating at
the paper's two widths, so the discounted launch credit is exact. -/
theorem couponNodeLaunchOneCreditExact (n t : Nat)
    (hwidth : t = 2 ∨ t = 3) :
    couponNodeLaunchPotential n t 1 +
      (n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) * (t + 2) +
      couponNodeDenominator t * n) =
      couponNodeBudget n t := by
  have hbound := couponNodeLaunchOneNoTruncation n t hwidth
  change
    ((couponNodeBudget n t -
        n * (pPair t).1 * (harmonicPair (t + 3)).1 *
          freshFact (t + 3) * (t + 2)) -
      n * couponNodeDenominator t) +
    (n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) * (t + 2) +
      couponNodeDenominator t * n) =
    couponNodeBudget n t
  rw [Nat.mul_comm (couponNodeDenominator t) n]
  rw [Nat.sub_sub]
  exact Nat.sub_add_cancel hbound

/-- Exact zero-hit launch Bellman equality over ALL physical Fin n
selected edges. This remains valid for either named paper width. -/
theorem couponNodeLaunchZeroDrift {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hwidth : (compileAdvice q).t = 2 ∨
      (compileAdvice q).t = 3) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .launching 0) e))).sum =
      n * couponNodeLaunchPotential n (compileAdvice q).t 0 := by
  rw [couponNodeLaunchZeroEdgeSum ring fixed s seed hn,
    outsideLaunch_size s hn]
  have hcount :
      n - 1 - (n - ((compileAdvice q).t + 2)) =
        ((compileAdvice q).t + 2) - 1 := by omega
  rw [hcount]
  exact couponNodeLaunchZeroCreditAlgebra
    n ((compileAdvice q).t + 2)
    (couponNodeDenominator (compileAdvice q).t)
    (couponNodeBudget n (compileAdvice q).t)
    (n * (pPair (compileAdvice q).t).1 *
      (harmonicPair ((compileAdvice q).t + 3)).1 *
      freshFact ((compileAdvice q).t + 3))
    (couponNodeLaunchPotential n (compileAdvice q).t 0)
    (couponNodeLaunchPotential n (compileAdvice q).t 1)
    (by omega) (by omega)
    (couponNodeLaunchZeroCreditExact
      n (compileAdvice q).t hwidth)
    (couponNodeLaunchOneCreditExact
      n (compileAdvice q).t hwidth)

/-- Width-two and width-three scan initial numerators, extracted
from the pPair cross-product identities. No expensive
decision over a general scan word or compiled advice is used. -/
theorem couponNodeScanInitialNumeratorTwo :
    couponScanIntegerNum 2 0 [] = 24 := by
  have hden : (pPair 2).2 = 4 := by
    have h := p_scan_two
    rw [couponNodePairNumeratorTwo] at h
    omega
  have h := couponScanIntegerNum_represents 2 0 []
  change couponScanIntegerNum 2 0 [] * (pPair 2).2 =
    (pPair 2).1 * couponScanIntegerDen 2 at h
  rw [hden, couponNodePairNumeratorTwo, couponNodeScanDen_two] at h
  omega

theorem couponNodeScanInitialNumeratorThree :
    couponScanIntegerNum 3 0 [] = 119232 := by
  have hden : (pPair 3).2 = 31104 := by
    have h := p_scan_three
    rw [couponNodePairNumeratorThree] at h
    omega
  have h := couponScanIntegerNum_represents 3 0 []
  change couponScanIntegerNum 3 0 [] * (pPair 3).2 =
    (pPair 3).1 * couponScanIntegerDen 3 at h
  rw [hden, couponNodePairNumeratorThree,
    couponNodeScanDen_three] at h
  have hr : (13248 * 279936 : Nat) = 119232 * 31104 := by decide
  rw [hr] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide) h

/-- Factor the population size out of a two-step truncated
difference; the closed constant part is checked separately, so no
large literal enters a linear-arithmetic certificate. -/
theorem couponNodeFactorN (n A B C K : Nat) (h : A - B - C = K) :
    n * A - n * B - n * C = n * K := by
  rw [← Nat.mul_sub, ← Nat.mul_sub, h]

/-- The relevant width-two/three values of the actual launch-one and
scan-start potentials; only closed source-width data is reduced. -/
theorem couponNodeLaunchPotentialOneTwo (n : Nat) :
    couponNodeLaunchPotential n 2 1 = n * 1714200 := by
  have hf : freshFact 5 = 120 := by decide
  change
    (couponNodeBudget n 2 -
        n * (pPair 2).1 * (harmonicPair 5).1 *
          freshFact 5 * 4) -
      n * couponNodeDenominator 2 = n * 1714200
  simp only [couponNodeBudget]
  rw [couponNodeNumerator_two, couponNodePairNumeratorTwo,
    couponNodeHarmonicNumeratorTwo, couponNodeDenominatorTwo, hf]
  omega

theorem couponNodeLaunchPotentialOneThree (n : Nat) :
    couponNodeLaunchPotential n 3 1 = n * 903765703680 := by
  have hf : freshFact 6 = 720 := by decide
  unfold couponNodeLaunchPotential
  simp only [couponNodeBudget, Nat.one_ne_zero, ↓reduceIte]
  rw [couponNodeNumerator_three, couponNodePairNumeratorThree,
    couponNodeHarmonicNumeratorThree, couponNodeDenominatorThree, hf]
  simp only [Nat.mul_assoc]
  exact couponNodeFactorN n _ _ _ _ (by decide)

theorem couponNodeScanPotentialStartTwo (n : Nat) :
    couponNodeScanPotential n 2 0 [] = n * 528000 := by
  change
    couponNodeBudget n 2 -
      couponNodeBudget n 2 * couponScanIntegerNum 2 0 [] /
        couponScanIntegerDen 2 +
      couponNodeDenominator 2 * n * 2 = n * 528000
  simp only [couponNodeBudget]
  rw [couponNodeNumerator_two, couponNodeDenominatorTwo,
    couponNodeScanInitialNumeratorTwo, couponNodeScanDen_two]
  omega

theorem couponNodeScanPotentialStartThree (n : Nat) :
    couponNodeScanPotential n 3 0 [] = n * 567159459840 := by
  change
    couponNodeBudget n 3 -
      couponNodeBudget n 3 * couponScanIntegerNum 3 0 [] /
        couponScanIntegerDen 3 +
      couponNodeDenominator 3 * n * 3 = n * 567159459840
  simp only [couponNodeBudget]
  rw [couponNodeNumerator_three, couponNodeDenominatorThree,
    couponNodeScanInitialNumeratorThree, couponNodeScanDen_three]
  omega

/-- The one-hit marked transition pays the actual scan-start
potential. At widths two and three it leaves nonnegative slack. -/
theorem couponNodeLaunchOneCreditRow (n t : Nat)
    (hwidth : t = 2 ∨ t = 3) :
    couponNodeDenominator t * n +
      (couponNodeScanPotential n t 0 [] +
        (t + 1) * couponNodeBudget n t) ≤
      (t + 2) * couponNodeLaunchPotential n t 1 := by
  rcases hwidth with ht | ht
  · rw [ht]
    rw [couponNodeDenominatorTwo,
      couponNodeScanPotentialStartTwo,
      couponNodeLaunchPotentialOneTwo]
    simp only [couponNodeBudget]
    rw [couponNodeNumerator_two]
    omega
  · rw [ht]
    rw [couponNodeDenominatorThree,
      couponNodeScanPotentialStartThree,
      couponNodeLaunchPotentialOneThree]
    simp only [couponNodeBudget]
    rw [couponNodeNumerator_three]
    omega

/-- Full launch-one local Bellman inequality over the original physical
Fin n scheduler, with one marked successor to .scanning 0 []. -/
theorem couponNodeLaunchOneDrift {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hwidth : (compileAdvice q).t = 2 ∨
      (compileAdvice q).t = 3) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .launching 1) e))).sum ≤
      n * couponNodeLaunchPotential n (compileAdvice q).t 1 := by
  rw [couponNodeLaunchOneEdgeSum ring fixed s seed hn,
    outsideLaunch_size s hn]
  have hcount :
      n - 1 - (n - ((compileAdvice q).t + 2)) =
        (compileAdvice q).t + 1 := by omega
  rw [hcount]
  have hrow := couponNodeLaunchOneCreditRow
    n (compileAdvice q).t hwidth
  calc
    _ =
        (couponNodeDenominator (compileAdvice q).t * n +
          (couponNodeScanPotential n (compileAdvice q).t 0 [] +
            ((compileAdvice q).t + 1) *
              couponNodeBudget n (compileAdvice q).t)) +
        (n - ((compileAdvice q).t + 2)) *
          couponNodeLaunchPotential n (compileAdvice q).t 1 := by
            ac_rfl
    _ ≤ ((compileAdvice q).t + 2) *
          couponNodeLaunchPotential n (compileAdvice q).t 1 +
        (n - ((compileAdvice q).t + 2)) *
          couponNodeLaunchPotential n (compileAdvice q).t 1 :=
            Nat.add_le_add_right hrow _
    _ = n * couponNodeLaunchPotential n (compileAdvice q).t 1 := by
          rw [← Nat.add_mul]
          have hsize :
              ((compileAdvice q).t + 2) +
                (n - ((compileAdvice q).t + 2)) = n := by omega
          rw [hsize]

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount)

/-- A live scanning component of the exact same-word scan
synchronization has index strictly below the certificate width. -/
theorem couponNodeScanSyncBelow {n t : Nat}
    (phase : CouponAttemptPhase n) (state : TolerantScanState)
    (j : Nat) (once : List Nat)
    (h : CouponNodeScanSync t phase state)
    (hphase : phase = .scanning j once) : j < t := by
  cases h with
  | live k A hk =>
      cases hphase
      exact hk
  | success k A hk =>
      cases hphase
  | failed =>
      cases hphase

theorem couponNodeScanRunBelow {n q : Nat}
    (s : Fin n) (ht : 0 < (compileAdvice q).t)
    (word : List (Fin n)) (j : Nat) (once : List Nat)
    (hphase : couponNodeScanRun (q := q) s word =
      .scanning j once) : j < (compileAdvice q).t := by
  have hsync :
      CouponNodeScanSync (compileAdvice q).t
        (couponNodeScanRun (q := q) s word)
        (LDSinkBoundedKernel.run
          (tolerantScanStep s (compileAdvice q).t)
          (.live 0 []) word) := by
    have hh := couponNodeScanSyncRun (q := q)
      s (.scanning 0 []) (.live 0 []) word
      (CouponNodeScanSync.live (n := n) 0 [] ht)
    simpa only [couponNodeScanRun, couponNodeFoldRun] using hh
  exact couponNodeScanSyncBelow
    (couponNodeScanRun (q := q) s word)
    (LDSinkBoundedKernel.run
      (tolerantScanStep s (compileAdvice q).t)
      (.live 0 []) word)
    j once hsync hphase

/-- Only genuinely reached active scan nodes are used.
The proof recovers their actual scan word first. -/
theorem couponNodeReachableScanBelow {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (seed : CouponSeed fixed) (j : Nat) (once : List Nat)
    (hreach : couponNodeReachable ring fixed s
      (seed, .scanning j once)) :
    j < (compileAdvice q).t := by
  obtain ⟨origin, clear, launch, scan, _, _, hscan, _, _⟩ :=
    couponNodeReachableScanHistory
      ring fixed s (seed, .scanning j once) j once hreach rfl
  exact couponNodeScanRunBelow s (by omega)
    scan j once hscan

/-- Literal child value of a tolerantScanStep state.
A failed edge retries at P, a completed live edge succeeds at zero,
and only an unfinished live edge has a continuation scan potential. -/
def couponNodeScanChildValue (n t : Nat) :
    TolerantScanState → Nat
  | .failed => couponNodeBudget n t
  | .live k A =>
      if t ≤ k then 0 else couponNodeScanPotential n t k A

/-- Physical success, not just observer success, justifies the
zero value at the completed live scan edge. -/
theorem couponNodeReachableScanEdgeValue {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (seed : CouponSeed fixed) (j : Nat) (once : List Nat)
    (hreach : couponNodeReachable ring fixed s
      (seed, .scanning j once)) (e : Fin n) :
    couponAttemptNodeValue
        (couponNodeBudget n (compileAdvice q).t)
        (fun a : CouponSeed fixed × CouponAttemptPhase n =>
          couponNodePotential (q := q) s a.2)
        ((couponTrialKernel ring fixed s).step
          (seed, .scanning j once) e) =
      couponNodeScanChildValue n (compileAdvice q).t
        (tolerantScanStep s (compileAdvice q).t
          (.live j once) e) := by
  cases hs : tolerantScanStep s (compileAdvice q).t
      (.live j once) e with
  | failed =>
      have hphase :
          couponAttemptPhaseNext (q := q) s
            (.scanning j once) e = .failed := by
        simp [couponAttemptPhaseNext, hs]
      simp [couponTrialKernel, couponAttemptNodeValue,
        couponNodeScanChildValue, hphase, hs]
  | live k newA =>
      by_cases hdone : (compileAdvice q).t ≤ k
      · have hphase :
            couponAttemptPhaseNext (q := q) s
              (.scanning j once) e = .succeeded := by
          simp [couponAttemptPhaseNext, hs, hdone]
        have hphysical :=
          couponNodeReachedSuccessKernelStep
            ring fixed s ht hn hroot hbad
            (seed, .scanning j once) e hreach hphase
        simp [hphysical, couponAttemptNodeValue,
          couponNodeScanChildValue, hs, hdone]
      · have hphase :
            couponAttemptPhaseNext (q := q) s
              (.scanning j once) e =
              .scanning k newA := by
          simp [couponAttemptPhaseNext, hs, hdone]
        simp [couponTrialKernel, couponAttemptNodeValue,
          couponNodeScanChildValue, couponNodePotential,
          hphase, hs, hdone]

/-- Reached-state sum remains over all physical scheduler edges. -/
theorem couponNodeReachableScanEdgeSum {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (seed : CouponSeed fixed) (j : Nat) (once : List Nat)
    (hreach : couponNodeReachable ring fixed s
      (seed, .scanning j once)) :
    (List.ofFn (fun e : Fin n =>
      couponAttemptNodeValue
        (couponNodeBudget n (compileAdvice q).t)
        (fun a : CouponSeed fixed × CouponAttemptPhase n =>
          couponNodePotential (q := q) s a.2)
        ((couponTrialKernel ring fixed s).step
          (seed, .scanning j once) e))).sum =
    (List.ofFn (fun e : Fin n =>
      couponNodeScanChildValue n (compileAdvice q).t
        (tolerantScanStep s (compileAdvice q).t
          (.live j once) e))).sum := by
  apply ofFn_sum_eq
  intro e
  exact couponNodeReachableScanEdgeValue
    ring fixed s ht hn hroot hbad seed j once hreach e

/-- An elementary finite-carrier drift certificate with one
distinguished physical edge carrying a unit decrease. -/
theorem couponNodeOneLowerSum {n : Nat}
    (a : Fin n) (v : Fin n → Nat) (R : Nat)
    (hall : ∀ e, v e ≤ R) (hmark : v a + 1 ≤ R) :
    1 + (List.ofFn v).sum ≤ n * R := by
  have hrow (e : Fin n) :
      v e + (if e = a then 1 else 0) ≤ R := by
    by_cases he : e = a
    · subst e
      simpa using hmark
    · simpa [he] using hall e
  have hsum := ofFn_sum_le
    (fun e : Fin n => v e +
      (if e = a then 1 else 0))
    (fun _ : Fin n => R) hrow
  rw [ofFn_sum_add, FreshFixed.sum_spike,
    ofFn_sum_const] at hsum
  simpa only [Nat.add_comm] using hsum

/-- The stopped tolerant scanner spends one unit of progress on
the original certSite j edge and never increases remaining progress
on any of the other n-1 physical scheduler edges. -/
theorem couponNodeScanRemainingRow {n : Nat}
    (s : Fin n) (t j : Nat) (A : List Nat)
    (htn : t ≤ n) (hj : j < t) :
    1 + (List.ofFn (fun e : Fin n =>
      tolerantRemaining t
        (tolerantScanStep s t (.live j A) e))).sum ≤
        n * (t - j) := by
  have hnot : ¬ tolerantScanDone t (.live j A) := by
    change ¬ t ≤ j
    omega
  exact couponNodeOneLowerSum (tolerantChosen s (.live j A))
    (fun e : Fin n =>
      tolerantRemaining t
        (tolerantScanStep s t (.live j A) e))
    (t - j)
    (fun e => by
      have h := tolerant_remaining_nonincrease
        s t (.live j A) e
      exact h)
    (tolerant_remaining_drop s t htn (.live j A) hnot)


/- Closed finite-state numerator bounds. The raw scan fuel is evaluated
only after the future-unhit list has become a closed list of at most
two numerals. No complete protocol configuration is normalized. -/
theorem couponNodeScanNumeratorBoundTwo
    (j : Nat) (A : List Nat) :
    couponScanIntegerNum 2 j A ≤ couponScanIntegerDen 2 := by
  have hr : List.range 2 = [0, 1] := rfl
  by_cases hdone : 2 ≤ j
  · rw [couponScanIntegerNum_terminal 2 j A hdone]
    exact Nat.le_refl _
  · cases j with
    | zero =>
        by_cases hA : 1 ∈ A
        · have hB : futureUnhit 2 0 A = [] := by
            simp [futureUnhit, hr, hA]
          unfold couponScanIntegerNum
          rw [hB]
          decide +kernel
        · have hB : futureUnhit 2 0 A = [1] := by
            simp [futureUnhit, hr, hA]
          unfold couponScanIntegerNum
          rw [hB]
          decide +kernel
    | succ j =>
        cases j with
        | zero =>
            have hB : futureUnhit 2 1 A = [] := by
              simp [futureUnhit, hr]
            unfold couponScanIntegerNum
            rw [hB]
            decide +kernel
        | succ j =>
            omega

theorem couponNodeScanNumeratorBoundThree
    (j : Nat) (A : List Nat) :
    couponScanIntegerNum 3 j A ≤ couponScanIntegerDen 3 := by
  have hr : List.range 3 = [0, 1, 2] := rfl
  by_cases hdone : 3 ≤ j
  · rw [couponScanIntegerNum_terminal 3 j A hdone]
    exact Nat.le_refl _
  · cases j with
    | zero =>
        by_cases hA : 1 ∈ A
        · by_cases hB : 2 ∈ A
          · have hf : futureUnhit 3 0 A = [] := by
              simp [futureUnhit, hr, hA, hB]
            unfold couponScanIntegerNum
            rw [hf]
            decide +kernel
          · have hf : futureUnhit 3 0 A = [2] := by
              simp [futureUnhit, hr, hA, hB]
            unfold couponScanIntegerNum
            rw [hf]
            decide +kernel
        · by_cases hB : 2 ∈ A
          · have hf : futureUnhit 3 0 A = [1] := by
              simp [futureUnhit, hr, hA, hB]
            unfold couponScanIntegerNum
            rw [hf]
            decide +kernel
          · have hf : futureUnhit 3 0 A = [1, 2] := by
              simp [futureUnhit, hr, hA, hB]
            unfold couponScanIntegerNum
            rw [hf]
            decide +kernel
    | succ j =>
        cases j with
        | zero =>
            by_cases hB : 2 ∈ A
            · have hf : futureUnhit 3 1 A = [] := by
                simp [futureUnhit, hr, hB]
              unfold couponScanIntegerNum
              rw [hf]
              decide +kernel
            · have hf : futureUnhit 3 1 A = [2] := by
                simp [futureUnhit, hr, hB]
              unfold couponScanIntegerNum
              rw [hf]
              decide +kernel
        | succ j =>
            cases j with
            | zero =>
                have hf : futureUnhit 3 2 A = [] := by
                  simp [futureUnhit, hr]
                unfold couponScanIntegerNum
                rw [hf]
                decide +kernel
            | succ j =>
                omega

theorem couponNodeScanNumeratorBoundWidth
    (t j : Nat) (A : List Nat)
    (hwidth : t = 2 ∨ t = 3) :
    couponScanIntegerNum t j A ≤ couponScanIntegerDen t := by
  rcases hwidth with ht | ht
  · rw [ht]
    exact couponNodeScanNumeratorBoundTwo j A
  · rw [ht]
    exact couponNodeScanNumeratorBoundThree j A


theorem couponNodeScanDenDividesNumerator
    (t : Nat) (hwidth : t = 2 ∨ t = 3) :
    couponScanIntegerDen t ∣ couponNodeNumerator t := by
  rcases hwidth with ht | ht
  · rw [ht]
    exact couponNodeDivides_two
  · rw [ht]
    exact couponNodeDivides_three

/-- Dividing the product at a shared positive denominator is exact.
The proof uses division-multiplication cancellation and a positive
factor cancellation, not any real-valued fraction approximation. -/
theorem couponNodeScanDiscountIdentity
    (n Q k W : Nat) (hQ : 0 < Q) :
    n * (Q * k) - (n * (Q * k) * W) / Q =
      (n * k) * (Q - W) := by
  have hdivisible : Q ∣ n * (Q * k) * W := by
    refine ⟨n * k * W, ?_⟩
    ac_rfl
  have hquot :
      (n * (Q * k) * W) / Q = n * k * W := by
    apply Nat.eq_of_mul_eq_mul_right hQ
    calc
      ((n * (Q * k) * W) / Q) * Q =
          n * (Q * k) * W :=
        Nat.div_mul_cancel hdivisible
      _ = (n * k * W) * Q := by ac_rfl
  rw [hquot]
  have hmul : n * (Q * k) = (n * k) * Q := by ac_rfl
  rw [hmul]
  exact (Nat.mul_sub (n * k) Q W).symm

/-- Exact shared-denominator discount for the literal paper budget. -/
theorem couponNodeScanBudgetDiscount
    (n t W k : Nat)
    (hnum :
      couponNodeNumerator t = couponScanIntegerDen t * k) :
    couponNodeBudget n t -
        couponNodeBudget n t * W / couponScanIntegerDen t =
      (n * k) * (couponScanIntegerDen t - W) := by
  unfold couponNodeBudget
  rw [hnum]
  exact couponNodeScanDiscountIdentity
    n (couponScanIntegerDen t) k W
    (couponScanIntegerDen_pos t)

/-- A single uniform child identity includes the three cases:
failed = retry P; finished live = real success 0; unfinished live =
the unreduced integer scan potential. -/
theorem couponNodeScanChildComplement
    (n t k : Nat)
    (hnum :
      couponNodeNumerator t = couponScanIntegerDen t * k)
    (x : TolerantScanState) :
    couponNodeScanChildValue n t x =
      (n * k) *
        (couponScanIntegerDen t - couponScanIntegerWeight t x) +
      couponNodeDenominator t * n * tolerantRemaining t x := by
  cases x with
  | failed =>
      change couponNodeBudget n t =
        (n * k) * (couponScanIntegerDen t - 0) +
          couponNodeDenominator t * n * 0
      simp only [Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
      rw [couponNodeBudget, hnum]
      ac_rfl
  | live j A =>
      by_cases hdone : t ≤ j
      · have hterm := couponScanIntegerNum_terminal t j A hdone
        simp [couponNodeScanChildValue, hdone,
          couponScanIntegerWeight, tolerantRemaining, hterm]
      · have hj : j < t := by omega
        simp only [couponNodeScanChildValue, if_neg hdone,
          couponNodeScanPotential, if_pos hj,
          couponScanIntegerWeight, tolerantRemaining]
        rw [couponNodeScanBudgetDiscount n t
          (couponScanIntegerNum t j A) k hnum]

/-- The complete physical Fin n sum of numerator complements is
transported from the scanner harmonic equation, with
only per-child bounds on the unrounded integer numerators. -/
theorem couponNodeScanComplementSum {n : Nat}
    (Q W : Nat) (v : Fin n → Nat)
    (hQ : W ≤ Q)
    (hall : ∀ e, v e ≤ Q)
    (hsum : (List.ofFn v).sum = n * W) :
    (List.ofFn (fun e : Fin n => Q - v e)).sum =
      n * (Q - W) := by
  have heach (e : Fin n) :
      (Q - v e) + v e = Q :=
    Nat.sub_add_cancel (hall e)
  have htotal :
      (List.ofFn (fun e : Fin n => Q - v e)).sum +
        (List.ofFn v).sum = n * Q := by
    calc
      _ = (List.ofFn (fun e : Fin n =>
            (Q - v e) + v e)).sum := by
              rw [ofFn_sum_add]
      _ = (List.ofFn (fun _ : Fin n => Q)).sum :=
        ofFn_sum_eq _ _ heach
      _ = n * Q := ofFn_sum_const n Q
  rw [hsum] at htotal
  have hidentity :
      n * (Q - W) + n * W = n * Q := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hQ]
  exact Nat.add_right_cancel (htotal.trans hidentity.symm)

/-- The current live scan phase uses the same shared-denominator
complement as its three classes of physical children. -/
theorem couponNodeScanPotentialComplement
    (n t j : Nat) (A : List Nat) (k : Nat)
    (hnum :
      couponNodeNumerator t = couponScanIntegerDen t * k)
    (hj : j < t) :
    couponNodeScanPotential n t j A =
      (n * k) *
        (couponScanIntegerDen t - couponScanIntegerNum t j A) +
      couponNodeDenominator t * n * (t - j) := by
  simp only [couponNodeScanPotential, if_pos hj]
  rw [couponNodeScanBudgetDiscount n t
    (couponScanIntegerNum t j A) k hnum]


/-- Shared-denominator harmonic conservation plus one nominated
physical progress edge yields the complete integer Bellman row.
All arithmetic is in Nat and retains the common scale. -/
theorem couponNodeScanCombinedDrift {n : Nat}
    (D B Q W R : Nat)
    (v rem : Fin n → Nat)
    (hW : W ≤ Q)
    (hall : ∀ e, v e ≤ Q)
    (hharmonic : (List.ofFn v).sum = n * W)
    (hprogress : 1 + (List.ofFn rem).sum ≤ n * R) :
    D * n +
      (List.ofFn (fun e : Fin n =>
        B * (Q - v e) + D * n * rem e)).sum ≤
      n * (B * (Q - W) + D * n * R) := by
  have hcomplement :=
    couponNodeScanComplementSum Q W v hW hall hharmonic
  have hsum :
      (List.ofFn (fun e : Fin n =>
        B * (Q - v e) + D * n * rem e)).sum =
      B * (List.ofFn (fun e : Fin n => Q - v e)).sum +
        (D * n) * (List.ofFn rem).sum := by
    rw [ofFn_sum_add, ofFn_sum_mul_left,
      ofFn_sum_mul_left]
  have hclock :
      D * n + (D * n) * (List.ofFn rem).sum ≤
      (D * n) * (n * R) := by
    calc
      _ = (D * n) * (1 + (List.ofFn rem).sum) := by
        simp only [Nat.mul_add, Nat.mul_one]
      _ ≤ (D * n) * (n * R) :=
        Nat.mul_le_mul_left _ hprogress
  calc
    D * n +
        (List.ofFn (fun e : Fin n =>
          B * (Q - v e) + D * n * rem e)).sum =
      B * (n * (Q - W)) +
        (D * n + (D * n) * (List.ofFn rem).sum) := by
          rw [hsum, hcomplement]
          ac_rfl
    _ ≤ B * (n * (Q - W)) +
        (D * n) * (n * R) :=
      Nat.add_le_add_left hclock _
    _ = n * (B * (Q - W) + D * n * R) := by
      rw [Nat.mul_add]
      ac_rfl

/-- Failure-scoped live scan drift for the genuine reachable active
kernel. Completed scan edges are valued as REAL kernel success, not
as syntactic observer success, via couponNodeReachedSuccessKernelStep.
The integer numerator sums are over all of Fin n. -/
theorem couponNodeReachableScanDrift {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hwidth : (compileAdvice q).t = 2 ∨
      (compileAdvice q).t = 3)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (seed : CouponSeed fixed) (j : Nat) (once : List Nat)
    (hreach : couponNodeReachable ring fixed s
      (seed, .scanning j once)) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .scanning j once) e))).sum ≤
      n * couponNodeScanPotential n (compileAdvice q).t
        j once := by
  obtain ⟨k, hnum⟩ :=
    couponNodeScanDenDividesNumerator
      (compileAdvice q).t hwidth
  have hj : j < (compileAdvice q).t :=
    couponNodeReachableScanBelow ring fixed s ht
      seed j once hreach
  have hweight :
      (List.ofFn (fun e : Fin n =>
        couponScanIntegerWeight (compileAdvice q).t
          (tolerantScanStep s (compileAdvice q).t
            (.live j once) e))).sum =
        n * couponScanIntegerNum (compileAdvice q).t
          j once := by
    exact coupon_scan_integer_harmonic
      s (compileAdvice q).t (by omega) (.live j once)
  have hcurrent :
      couponScanIntegerNum (compileAdvice q).t j once ≤
        couponScanIntegerDen (compileAdvice q).t :=
    couponNodeScanNumeratorBoundWidth
      (compileAdvice q).t j once hwidth
  have hchildren (e : Fin n) :
      couponScanIntegerWeight (compileAdvice q).t
        (tolerantScanStep s (compileAdvice q).t
          (.live j once) e) ≤
        couponScanIntegerDen (compileAdvice q).t := by
    cases hs : tolerantScanStep s (compileAdvice q).t
        (.live j once) e with
    | failed =>
        change 0 ≤ couponScanIntegerDen (compileAdvice q).t
        exact Nat.zero_le _
    | live k A =>
        exact couponNodeScanNumeratorBoundWidth
          (compileAdvice q).t k A hwidth
  have hprogress :=
    couponNodeScanRemainingRow s (compileAdvice q).t j once
      (by omega) hj
  have hcomplement (e : Fin n) :
      couponNodeScanChildValue n (compileAdvice q).t
          (tolerantScanStep s (compileAdvice q).t
            (.live j once) e) =
        (n * k) *
          (couponScanIntegerDen (compileAdvice q).t -
            couponScanIntegerWeight (compileAdvice q).t
              (tolerantScanStep s (compileAdvice q).t
                (.live j once) e)) +
        couponNodeDenominator (compileAdvice q).t * n *
          tolerantRemaining (compileAdvice q).t
            (tolerantScanStep s (compileAdvice q).t
              (.live j once) e) :=
    couponNodeScanChildComplement n
      (compileAdvice q).t k hnum _
  have hsum :
      (List.ofFn (fun e : Fin n =>
        couponNodeScanChildValue n (compileAdvice q).t
          (tolerantScanStep s (compileAdvice q).t
            (.live j once) e))).sum =
      (List.ofFn (fun e : Fin n =>
        (n * k) *
          (couponScanIntegerDen (compileAdvice q).t -
            couponScanIntegerWeight (compileAdvice q).t
              (tolerantScanStep s (compileAdvice q).t
                (.live j once) e)) +
        couponNodeDenominator (compileAdvice q).t * n *
          tolerantRemaining (compileAdvice q).t
            (tolerantScanStep s (compileAdvice q).t
              (.live j once) e))).sum :=
    ofFn_sum_eq _ _ hcomplement
  have hdrift :=
    couponNodeScanCombinedDrift
      (couponNodeDenominator (compileAdvice q).t)
      (n * k)
      (couponScanIntegerDen (compileAdvice q).t)
      (couponScanIntegerNum (compileAdvice q).t j once)
      ((compileAdvice q).t - j)
      (fun e : Fin n =>
        couponScanIntegerWeight (compileAdvice q).t
          (tolerantScanStep s (compileAdvice q).t
            (.live j once) e))
      (fun e : Fin n =>
        tolerantRemaining (compileAdvice q).t
          (tolerantScanStep s (compileAdvice q).t
            (.live j once) e))
      hcurrent hchildren hweight hprogress
  have hstart :
      couponNodeScanPotential n (compileAdvice q).t
          j once =
        (n * k) *
          (couponScanIntegerDen (compileAdvice q).t -
            couponScanIntegerNum (compileAdvice q).t
              j once) +
        couponNodeDenominator (compileAdvice q).t * n *
          ((compileAdvice q).t - j) :=
    couponNodeScanPotentialComplement
      n (compileAdvice q).t j once k hnum hj
  calc
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .scanning j once) e))).sum =
        couponNodeDenominator (compileAdvice q).t * n +
          (List.ofFn (fun e : Fin n =>
            couponNodeScanChildValue n (compileAdvice q).t
              (tolerantScanStep s (compileAdvice q).t
                (.live j once) e))).sum := by
            rw [couponNodeReachableScanEdgeSum
              ring fixed s ht hn hroot hbad seed j once hreach]
    _ = couponNodeDenominator (compileAdvice q).t * n +
          (List.ofFn (fun e : Fin n =>
            (n * k) *
              (couponScanIntegerDen (compileAdvice q).t -
                couponScanIntegerWeight (compileAdvice q).t
                  (tolerantScanStep s (compileAdvice q).t
                    (.live j once) e)) +
            couponNodeDenominator (compileAdvice q).t * n *
              tolerantRemaining (compileAdvice q).t
                (tolerantScanStep s (compileAdvice q).t
                  (.live j once) e))).sum := by rw [hsum]
    _ ≤ n * ((n * k) *
          (couponScanIntegerDen (compileAdvice q).t -
            couponScanIntegerNum (compileAdvice q).t j once) +
        couponNodeDenominator (compileAdvice q).t * n *
          ((compileAdvice q).t - j)) := hdrift
    _ = n * couponNodeScanPotential n (compileAdvice q).t
          j once := by rw [hstart]


/-- The factorial scale is exactly the unnormalised denominator of
the harmonic rational pair; hence the scaled harmonic at M equals
the numerator of harmonicPair M without any rounding. -/
theorem couponNodeScaledHarmonicAtFactorial (M : Nat) :
    scaledHarmonic (freshFact M) M = (harmonicPair M).1 := by
  have hscaled :=
    harmonic_pair_scaled (freshFact M) M
      (fun k hk hkm => coupon_factorial_dvd M k hk hkm)
  rw [couponNodeHarmonicDenFactorial M] at hscaled
  exact Nat.eq_of_mul_eq_mul_right
    (coupon_factorial_pos M) (hscaled.trans (Nat.mul_comm _ _))

theorem couponNodeInitialMaskSize {n : Nat}
    (s : Fin n) (M : Nat) (hM : M ≤ n) :
    maskSize (fun e : Fin n =>
      canonicalMask M (protectedLabel s e)) = M := by
  exact relabeled_mask_size
    (rotate (certSite s (n - 2)))
    (unrotate (certSite s (n - 2)))
    (unrotate_rotate (certSite s (n - 2)))
    (rotate_unrotate (certSite s (n - 2))) M hM

theorem couponNodeInitialFinalUnseen {n : Nat}
    (s : Fin n) (M : Nat) (hM : 0 < M) (hn : M ≤ n) :
    couponNodeFinalUnseen s M
      (fun e : Fin n => canonicalMask M (protectedLabel s e)) =
        true := by
  rw [couponNodeFinalUnseenCanonical s M
    (fun e : Fin n => canonicalMask M (protectedLabel s e)) hM hn]
  have htop := couponNodeProtectedTopLabel s M hM hn
  have hlt :
      (protectedLabel s (certSite s (n - 2 + (M - 1)))).val <
        M := by omega
  simp [canonicalMask, hlt]

/-- Empty chronological word has exactly the empty increasing prefix.
For all positive k its last-touch word cannot equal List.range k. -/
theorem couponNodePrefixOrderedEmpty {n : Nat}
    (s : Fin n) (M k : Nat) :
    couponNodePrefixOrdered s M k [] = decide (k = 0) := by
  cases k with
  | zero =>
      simp [couponNodePrefixOrdered, couponLastTouch]
  | succ k =>
      simp [couponNodePrefixOrdered, couponLastTouch,
        List.range_succ]

theorem couponNodePrefixSeenZero {n : Nat}
    (s : Fin n) (mask : Fin n → Bool) :
    couponNodePrefixSeen s mask 0 = true := by
  simp [couponNodePrefixSeen, ofFn_sum_const]

theorem couponNodeInitialOneWeightSum (M : Nat) (hM : 0 < M) :
    ((List.range M).map
      (fun k => if k = 0 then (1 : Nat) else 0)).sum = 1 := by
  have hsuccess :
      ∀ m : Nat,
        ((List.range (m + 1)).map
          (fun k => if k = 0 then (1 : Nat) else 0)).sum = 1 := by
    intro m
    induction m with
    | zero =>
        decide
    | succ m ih =>
        have hne : m + 1 ≠ 0 := by omega
        rw [List.range_succ, List.map_append, List.sum_append]
        simp only [List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Nat.add_zero]
        rw [ih]
        simp [hne]
  have hpred : M - 1 + 1 = M := by omega
  simpa only [hpred] using hsuccess (M - 1)

/-- One factorial summand, F_0 = 1, remains in the empty-word
order weight. All higher prefix indicators are false. -/
theorem couponNodeInitialCoverWeight {n : Nat}
    (s : Fin n) (M : Nat) (hM : 0 < M) (hn : M ≤ n) :
    couponNodeCoverWeight s M
      (fun e : Fin n => canonicalMask M (protectedLabel s e))
      [] = 1 := by
  have hfinal := couponNodeInitialFinalUnseen s M hM hn
  have hrow (k : Nat) :
      (if couponNodePrefixSeen s
            (fun e : Fin n => canonicalMask M (protectedLabel s e)) k &&
          couponNodePrefixOrdered s M k []
       then freshFact k else 0) =
        (if k = 0 then (1 : Nat) else 0) := by
    cases k with
    | zero =>
        simp [couponNodePrefixSeenZero, couponNodePrefixOrderedEmpty,
          freshFact]
    | succ k =>
        simp [couponNodePrefixOrderedEmpty]
  unfold couponNodeCoverWeight
  rw [hfinal]
  have hmap :
      ((List.range M).map (fun k =>
        if couponNodePrefixSeen s
              (fun e : Fin n =>
                canonicalMask M (protectedLabel s e)) k &&
            couponNodePrefixOrdered s M k []
        then freshFact k else 0)).sum =
      ((List.range M).map
        (fun k => if k = 0 then (1 : Nat) else 0)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    exact hrow k
  rw [hmap]
  exact couponNodeInitialOneWeightSum M hM

/-- Exact initial potential identity, not merely a ceiling
bound. The first-cover factorial credit cancels the full
harmonic premium on a genuinely existing protected mask. -/
theorem couponNodeStartPotentialExact {n q : Nat}
    (s : Fin n) (hn : (compileAdvice q).t + 3 ≤ n) :
    couponNodePotential (q := q) s
      (couponAttemptStart (q := q) s) =
      couponNodeBudget n (compileAdvice q).t := by
  have hM : 0 < (compileAdvice q).t + 3 := by omega
  have hmask :=
    couponNodeInitialMaskSize s ((compileAdvice q).t + 3) hn
  have hweight :=
    couponNodeInitialCoverWeight s
      ((compileAdvice q).t + 3) hM hn
  change couponNodeCoverPotential s (compileAdvice q).t
      (fun e : Fin n =>
        canonicalMask ((compileAdvice q).t + 3)
          (protectedLabel s e)) [] =
      couponNodeBudget n (compileAdvice q).t
  unfold couponNodeCoverPotential
  rw [hmask, hweight,
    couponNodeScaledHarmonicAtFactorial]
  simp only [Nat.mul_one, Nat.add_sub_cancel_right]


/-- Every indexed active history phase is one of the three live
constructors; neither absorbing terminal constructor is reachable. -/
theorem couponNodeStageHistoryNonterminal {n q : Nat}
    (s : Fin n) (word : List (Fin n))
    (phase : CouponAttemptPhase n)
    (h : CouponNodeStageHistory (q := q) s word phase) :
    phase ≠ .succeeded ∧ phase ≠ .failed := by
  cases h with
  | covering _ mask hmask =>
      constructor <;> intro hh <;> cases hh
  | launching clear launch hits hclear hlaunch hhits =>
      constructor <;> intro hh <;> cases hh
  | scanning clear launch scan j once hclear hbefore hscan =>
      constructor <;> intro hh <;> cases hh

/-- A history at a launching phase has a live counter 0 or 1,
not an arbitrary integer counter forged after its second hit. -/
theorem couponNodeStageHistoryLaunchingHits {n q : Nat}
    (s : Fin n) (word : List (Fin n))
    (phase : CouponAttemptPhase n) (hits : Nat)
    (h : CouponNodeStageHistory (q := q) s word phase)
    (hphase : phase = .launching hits) :
    hits = 0 ∨ hits = 1 := by
  cases h with
  | covering _ mask hmask =>
      cases hphase
  | launching clear launch count hclear hlaunch hhits =>
      cases hphase
      exact hhits
  | scanning clear launch scan j once hclear hbefore hscan =>
      cases hphase

theorem couponNodeReachableNonterminal {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (hreach : couponNodeReachable ring fixed s a) :
    a.2 ≠ .succeeded ∧ a.2 ≠ .failed := by
  obtain ⟨origin, word, _, htrace⟩ :=
    couponNodeReachableTrace ring fixed s a hreach
  exact couponNodeStageHistoryNonterminal s word a.2 htrace.2.2

theorem couponNodeReachableLaunchingHits {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed) (hits : Nat)
    (hreach : couponNodeReachable ring fixed s
      (seed, .launching hits)) :
    hits = 0 ∨ hits = 1 := by
  obtain ⟨origin, word, _, htrace⟩ :=
    couponNodeReachableTrace ring fixed s
      (seed, .launching hits) hreach
  exact couponNodeStageHistoryLaunchingHits
    s word (.launching hits) hits htrace.2.2 rfl

/-- The complete locally reached Bellman inequality after the
cover, launch-zero, launch-one and live-scan rows are combined.
All exceptional physical observer terminals have been excluded
by the same-word reachability history. -/
theorem couponNodeReachablePotentialDrift {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hwidth : (compileAdvice q).t = 2 ∨
      (compileAdvice q).t = 3)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (hreach : couponNodeReachable ring fixed s a) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun b : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s b.2)
          ((couponTrialKernel ring fixed s).step a e))).sum ≤
      n * couponNodePotential (q := q) s a.2 := by
  have hterminal :=
    couponNodeReachableNonterminal ring fixed s a hreach
  cases a with
  | mk seed phase =>
      cases phase with
      | covering mask word =>
          exact Nat.le_of_eq
            (couponNodeReachableCoverDrift ring fixed s
              hn hwidth (seed, .covering mask word)
              mask word hreach rfl)
      | launching hits =>
          have hhits :=
            couponNodeReachableLaunchingHits
              ring fixed s seed hits hreach
          rcases hhits with hzero | hone
          · subst hits
            exact Nat.le_of_eq
              (couponNodeLaunchZeroDrift
                ring fixed s seed hn hwidth)
          · subst hits
            exact couponNodeLaunchOneDrift
              ring fixed s seed hn hwidth
      | scanning j once =>
          exact couponNodeReachableScanDrift
            ring fixed s ht hn hwidth hroot hbad
            seed j once hreach
      | succeeded =>
          exact False.elim (hterminal.1 rfl)
      | failed =>
          exact False.elim (hterminal.2 rfl)

/-- The failure hypotheses are threaded into the exact same-word
good-only renewal induction. This scoped version places the initial
potential inequality AFTER the required n ≥ t+3 premise, unlike the
earlier global transfer interface which demands a bound for small
rings as well. -/
theorem couponNodeJointBudgetOnFailureWidth {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (hwidth : (compileAdvice q).t = 2 ∨
      (compileAdvice q).t = 3) :
    CouponJointBudgetOnFailure ring fixed s := by
  intro ht hn hroot hbad seed T
  exact couponNodeBudgetFromGoodDrift
    (couponTrialKernel ring fixed s)
    (couponNodeReachable ring fixed s)
    (couponNodeDenominator (compileAdvice q).t)
    (couponNodeBudget n (compileAdvice q).t)
    (fun a : CouponSeed fixed × CouponAttemptPhase n =>
      couponNodePotential (q := q) s a.2)
    (fun a e b ha hstep =>
      couponNodeReachableClosed ring fixed s a b e ha hstep)
    (fun a ha =>
      couponNodeReachablePotentialDrift ring fixed s
        ht hn hwidth hroot hbad a ha)
    (fun child _ => couponNodeReachableStart ring fixed s child)
    (fun child _ =>
      Nat.le_of_eq (couponNodeStartPotentialExact s hn))
    seed (by trivial) T

/-- Concrete production advice q=3 has compiled width two. -/
theorem couponNodeJointBudgetOnFailureTwo {n : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol 3).Configuration n) (s : Fin n) :
    CouponJointBudgetOnFailure ring fixed s := by
  apply couponNodeJointBudgetOnFailureWidth ring fixed s
  rw [couponNodeAdviceWidthTwo]
  exact Or.inl rfl

/-- Concrete production advice q=5 has compiled width three. -/
theorem couponNodeJointBudgetOnFailureThree {n : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol 5).Configuration n) (s : Fin n) :
    CouponJointBudgetOnFailure ring fixed s := by
  apply couponNodeJointBudgetOnFailureWidth ring fixed s
  rw [couponNodeAdviceWidthThree]
  exact Or.inr rfl

end L3.CouponClear


namespace L3.CouponClear

set_option autoImplicit false
set_option Elab.async false

open FreshReference FreshCoupon FreshFixed
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount)

/-!
Structural all-width arithmetic.
-/

/-- Filtering by a stronger Boolean condition cannot increase length. -/
private theorem couponNodeFilterLengthMonotone {α : Type}
    (p q : α → Bool) :
    ∀ xs : List α,
      (∀ x, p x = true → q x = true) →
      (xs.filter p).length ≤ (xs.filter q).length := by
  intro xs
  induction xs with
  | nil =>
      intro _
      exact Nat.le_refl _
  | cons x xs ih =>
      intro hpq
      have ht := ih hpq
      have hx : p x = true → q x = true := hpq x
      cases hp : p x with
      | false =>
          cases hq : q x <;> simp [hp, hq] <;> omega
      | true =>
          have hq : q x = true := hx hp
          simp [hp, hq]
          omega

/-- Exactly t-(j+1) elements of range t lie strictly beyond j. -/
private theorem couponNodeFutureRangeLength (t j : Nat) :
    ((List.range t).filter (fun k => decide (j < k))).length =
      t - (j + 1) := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      rw [List.range_succ, List.filter_append, List.length_append]
      have hsingleton :
          (([t] : List Nat).filter
            (fun k => decide (j < k))).length =
            (if j < t then 1 else 0) := by
        by_cases hj : j < t <;> simp [hj]
      rw [hsingleton, ih]
      by_cases hj : j < t
      · simp [hj]
        omega
      · simp [hj]
        omega

/-- The canonical future-unhit set has at most t-j-1 members. -/
private theorem couponNodeFutureUnhitCount (t j : Nat)
    (A : List Nat) (hj : j < t) :
    (futureUnhit t j A).length + 1 ≤ t - j := by
  have hpq (k : Nat) :
      decide (j < k ∧ k ∉ A) = true →
        decide (j < k) = true := by
    intro hh
    have h := (decide_eq_true_eq).mp hh
    exact (decide_eq_true_eq).mpr h.1
  have hc := couponNodeFilterLengthMonotone
    (fun k : Nat => decide (j < k ∧ k ∉ A))
    (fun k : Nat => decide (j < k))
    (List.range t) hpq
  change (futureUnhit t j A).length ≤
    ((List.range t).filter (fun k => decide (j < k))).length at hc
  rw [couponNodeFutureRangeLength] at hc
  omega

/-- Finite sum of terms bounded by the common scale. -/
private theorem couponNodeMappedSumBound {α : Type}
    (f : α → Nat) (C : Nat) :
    ∀ xs : List α,
      (∀ x, x ∈ xs → f x ≤ C) →
      (xs.map f).sum ≤ xs.length * C := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro h
      have hx : f x ≤ C := h x (by simp)
      have ht := ih (by
        intro y hy
        exact h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons,
        List.length_cons, Nat.succ_mul]
      omega

/-- Uniform upper bound for the exact common-scale recursion.
    The induction is over fuel, not over a table of widths or subsets. -/
theorem couponNodeScaledScanFuelBound :
    ∀ (fuel t j : Nat) (A : List Nat),
      couponScaledScanFuel fuel t j (futureUnhit t j A) ≤
        (freshFact t) ^ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro t j A
      by_cases hj : j < t <;>
        simp [couponScaledScanFuel, hj]
  | succ fuel ih =>
      intro t j A
      by_cases hj : j < t
      · have hprogress :
            couponScaledScanFuel fuel t (j + 1)
                (eraseAvailable (j + 1) (futureUnhit t j A)) ≤
              (freshFact t) ^ fuel := by
          rw [← coupon_scaledScanFuel_perm fuel t (j + 1)
            (coupon_futureUnhit_progress_perm t j A)]
          exact ih t (j + 1) (eraseAvailable (j + 1) A)
        have hfirst (k : Nat) (hk : k ∈ futureUnhit t j A) :
            couponScaledScanFuel fuel t j
                (eraseAvailable k (futureUnhit t j A)) ≤
              (freshFact t) ^ fuel := by
          rw [← coupon_scaledScanFuel_perm fuel t j
            (coupon_futureUnhit_first_perm t j A k)]
          exact ih t j (k :: A)
        have hsum :
            ((futureUnhit t j A).map (fun k =>
              couponScaledScanFuel fuel t j
                (eraseAvailable k (futureUnhit t j A)))).sum ≤
              (futureUnhit t j A).length * (freshFact t) ^ fuel :=
          couponNodeMappedSumBound
            (fun k => couponScaledScanFuel fuel t j
              (eraseAvailable k (futureUnhit t j A)))
            ((freshFact t) ^ fuel) _ hfirst
        have hcount := couponNodeFutureUnhitCount t j A hj
        have hdiv :
            (freshFact t / (t - j)) * (t - j) = freshFact t :=
          Nat.div_mul_cancel
            (coupon_factorial_dvd t (t - j)
              (by omega) (by omega))
        calc
          couponScaledScanFuel (fuel + 1) t j
              (futureUnhit t j A) =
              (freshFact t / (t - j)) *
                (couponScaledScanFuel fuel t (j + 1)
                    (eraseAvailable (j + 1) (futureUnhit t j A)) +
                  ((futureUnhit t j A).map (fun k =>
                    couponScaledScanFuel fuel t j
                      (eraseAvailable k (futureUnhit t j A)))).sum) :=
            couponScaledScanFuel_succ fuel t j _ hj
          _ ≤ (freshFact t / (t - j)) *
                ((freshFact t) ^ fuel +
                  (futureUnhit t j A).length * (freshFact t) ^ fuel) :=
            Nat.mul_le_mul_left _
              (Nat.add_le_add hprogress hsum)
          _ = (freshFact t / (t - j)) *
                (((futureUnhit t j A).length + 1) *
                  (freshFact t) ^ fuel) := by
            rw [Nat.add_mul, Nat.one_mul]
            ac_rfl
          _ ≤ (freshFact t / (t - j)) *
                ((t - j) * (freshFact t) ^ fuel) :=
            Nat.mul_le_mul_left _
              (Nat.mul_le_mul_right _ hcount)
          _ = (freshFact t) ^ (fuel + 1) := by
            rw [Nat.pow_succ]
            calc
              (freshFact t / (t - j)) *
                  ((t - j) * (freshFact t) ^ fuel) =
                ((freshFact t / (t - j)) * (t - j)) *
                  (freshFact t) ^ fuel := by ac_rfl
              _ = (freshFact t) ^ fuel * freshFact t := by
                rw [hdiv]
                ac_rfl
      · simp only [couponScaledScanFuel, if_neg hj]
        exact Nat.le_refl _

/-- Goal (1): every width, every index and every original once-hit list. -/
theorem couponNodeScanNumeratorBoundAll
    (t j : Nat) (A : List Nat) :
    couponScanIntegerNum t j A ≤ couponScanIntegerDen t := by
  change couponScaledScanFuel (2 * t + 1) t j (futureUnhit t j A) ≤
    (freshFact t) ^ (2 * t + 1)
  exact couponNodeScaledScanFuelBound (2 * t + 1) t j A

/-- One actual erase removes exactly one list element when present. -/
private theorem couponNodeEraseAvailableLength (k : Nat) :
    ∀ B : List Nat, k ∈ B →
      (eraseAvailable k B).length + 1 = B.length := by
  intro B
  induction B with
  | nil =>
      intro h
      cases h
  | cons x xs ih =>
      intro h
      by_cases hx : x = k
      · subst x
        simp [eraseAvailable]
      · have htail : k ∈ xs := by
          rcases List.mem_cons.mp h with hh | hh
          · exact False.elim (hx hh.symm)
          · exact hh
        have ht := ih htail
        simp only [eraseAvailable, if_neg hx, List.length_cons]
        omega

/-- The denominator of pairAdd fold is a product of denominators. -/
private theorem couponNodePairFoldDenominator
    (f : Nat → Nat × Nat) (xs : List Nat) (a : Nat × Nat) :
    ((xs.map f).foldl pairAdd a).2 =
      a.2 * (xs.map (fun k => (f k).2)).prod := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons k ks ih =>
      change ((ks.map f).foldl pairAdd (pairAdd a (f k))).2 =
        a.2 * ((f k).2 * (ks.map (fun x => (f x).2)).prod)
      rw [ih (pairAdd a (f k))]
      change (a.2 * (f k).2) *
          (ks.map (fun x => (f x).2)).prod =
        a.2 * ((f k).2 * (ks.map (fun x => (f x).2)).prod)
      ac_rfl

private theorem couponNodePairFuelDenominatorStep
    (fuel t j : Nat) (B : List Nat) (hj : j < t) :
    (pFuel (fuel + 1) t j B).2 =
      (t - j) *
        (pFuel fuel t (j + 1) (eraseAvailable (j + 1) B)).2 *
        (B.map (fun k =>
          (pFuel fuel t j (eraseAvailable k B)).2)).prod := by
  rw [pFuel_first_step fuel t j B hj]
  change
    ((B.map (fun k => pFuel fuel t j (eraseAvailable k B))).foldl
      pairAdd (pFuel fuel t (j + 1)
        (eraseAvailable (j + 1) B))).2 * (t - j) = _
  rw [couponNodePairFoldDenominator]
  ac_rfl

private theorem couponNodeFactorialStepDifference
    (t j : Nat) (hj : j < t) :
    freshFact (t - j) =
      (t - j) * freshFact (t - (j + 1)) := by
  have hdiff : t - j = t - (j + 1) + 1 := by omega
  rw [hdiff]
  rfl

/-- Mandatory progress spine: every visited j contributes t-j. -/
private theorem couponNodePairFuelDenominatorFact :
    ∀ (fuel t j : Nat) (B : List Nat),
      t - j ≤ fuel →
      freshFact (t - j) ∣ (pFuel fuel t j B).2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro t j B h
      have hj : ¬ j < t := by omega
      have hz : t - j = 0 := by omega
      simp [pFuel, hj, hz, freshFact]
  | succ fuel ih =>
      intro t j B h
      by_cases hj : j < t
      · obtain ⟨v, hv⟩ := ih t (j + 1)
          (eraseAvailable (j + 1) B) (by omega)
        rw [couponNodePairFuelDenominatorStep fuel t j B hj]
        refine ⟨v * (B.map (fun k =>
          (pFuel fuel t j (eraseAvailable k B)).2)).prod, ?_⟩
        rw [hv, couponNodeFactorialStepDifference t j hj]
        ac_rfl
      · have hz : t - j = 0 := by omega
        simp [pFuel, hj, hz, freshFact]

/-- If every factor is divisible by a, their product contains
    a^length. This is only elementary Nat divisibility. -/
private theorem couponNodeProductDivisibility
    (f : Nat → Nat) (a : Nat) :
    ∀ B : List Nat, (∀ k, k ∈ B → a ∣ f k) →
      a ^ B.length ∣ (B.map f).prod := by
  intro B
  induction B with
  | nil =>
      intro _
      simp
  | cons k ks ih =>
      intro hall
      obtain ⟨u, hu⟩ := hall k (by simp)
      obtain ⟨v, hv⟩ := ih (by
        intro x hx
        exact hall x (by simp [hx]))
      refine ⟨u * v, ?_⟩
      simp only [List.length_cons, List.map_cons,
        List.prod_cons, Nat.pow_succ]
      rw [hu, hv]
      ac_rfl

/-- One root and all first-hit children each contain a complete
    factorial progress spine. -/
private theorem couponNodePairFuelDenominatorFirstPower
    (fuel t j : Nat) (B : List Nat)
    (hj : j < t) (hf : t - j + 1 ≤ fuel) :
    (freshFact (t - j)) ^ (B.length + 1) ∣
      (pFuel fuel t j B).2 := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      obtain ⟨u, hu⟩ :=
        couponNodePairFuelDenominatorFact fuel t (j + 1)
          (eraseAvailable (j + 1) B) (by omega)
      have hchild (k : Nat) (hk : k ∈ B) :
          freshFact (t - j) ∣
            (pFuel fuel t j (eraseAvailable k B)).2 :=
        couponNodePairFuelDenominatorFact fuel t j
          (eraseAvailable k B) (by omega)
      obtain ⟨v, hv⟩ := couponNodeProductDivisibility
        (fun k => (pFuel fuel t j (eraseAvailable k B)).2)
        (freshFact (t - j)) B hchild
      rw [couponNodePairFuelDenominatorStep fuel t j B hj]
      refine ⟨u * v, ?_⟩
      rw [hu, hv, couponNodeFactorialStepDifference t j hj,
        Nat.pow_succ]
      ac_rfl

private theorem couponNodeNatPowMultiply (a b c : Nat) :
    (a ^ b) ^ c = a ^ (b * c) := by
  induction c with
  | zero =>
      simp
  | succ c ih =>
      calc
        (a ^ b) ^ (c + 1) = (a ^ b) ^ c * a ^ b := by
          rw [Nat.pow_succ]
        _ = a ^ (b * c) * a ^ b := by rw [ih]
        _ = a ^ (b * (c + 1)) := by
          rw [Nat.mul_succ, Nat.pow_add]

/-- The first two levels of first-hit branches contain
    1 + |B|^2 distinct mandatory factorial spines. -/
private theorem couponNodePairFuelDenominatorSquarePower
    (fuel t j : Nat) (B : List Nat)
    (hj : j < t) (hf : t - j + 2 ≤ fuel) :
    (freshFact (t - j)) ^ (1 + B.length * B.length) ∣
      (pFuel fuel t j B).2 := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      obtain ⟨u, hu⟩ :=
        couponNodePairFuelDenominatorFact fuel t (j + 1)
          (eraseAvailable (j + 1) B) (by omega)
      have hchild (k : Nat) (hk : k ∈ B) :
          (freshFact (t - j)) ^ B.length ∣
            (pFuel fuel t j (eraseAvailable k B)).2 := by
        have hc := couponNodePairFuelDenominatorFirstPower
          fuel t j (eraseAvailable k B) hj (by omega)
        rw [couponNodeEraseAvailableLength k B hk] at hc
        exact hc
      obtain ⟨v, hv⟩ := couponNodeProductDivisibility
        (fun k => (pFuel fuel t j (eraseAvailable k B)).2)
        ((freshFact (t - j)) ^ B.length) B hchild
      rw [couponNodeNatPowMultiply] at hv
      rw [couponNodePairFuelDenominatorStep fuel t j B hj]
      refine ⟨u * v, ?_⟩
      rw [hu, hv, couponNodeFactorialStepDifference t j hj]
      have he : 1 + B.length * B.length =
          B.length * B.length + 1 := by omega
      rw [he, Nat.pow_succ]
      ac_rfl

/-- For t>=4, the raw unreduced paper-pair denominator already
    contains Q_t=(t!)^(2t+1). Widths two and three need the
    additional small-width denominator certificates in the prefix. -/
theorem couponNodePairDenominatorContainsScanScale
    (t : Nat) (ht : 4 ≤ t) :
    couponScanIntegerDen t ∣ (pPair t).2 := by
  have hlen : (futureUnhit t 0 []).length = t - 1 := by
    change ((List.range t).filter
      (fun k => decide (0 < k ∧ k ∉ ([] : List Nat)))).length =
        t - 1
    have heq :
        (fun k : Nat => decide (0 < k ∧ k ∉ ([] : List Nat))) =
          (fun k : Nat => decide (0 < k)) := by
      funext k
      simp
    rw [heq, couponNodeFutureRangeLength]
  have hfuel :
      t - 0 + 2 ≤ t - 0 + (futureUnhit t 0 []).length := by
    omega
  have hlarge :=
    couponNodePairFuelDenominatorSquarePower
      (t - 0 + (futureUnhit t 0 []).length) t 0
      (futureUnhit t 0 []) (by omega) hfuel
  rw [hlen] at hlarge
  have hthree : 3 ≤ t - 1 := by omega
  have hsquare : 3 * (t - 1) ≤ (t - 1) * (t - 1) :=
    Nat.mul_le_mul_right _ hthree
  have hexp : 2 * t + 1 ≤ 1 + (t - 1) * (t - 1) := by
    omega
  have hpower :
      (freshFact t) ^ (2 * t + 1) ∣
        (freshFact t) ^ (1 + (t - 1) * (t - 1)) := by
    refine ⟨(freshFact t) ^
      (1 + (t - 1) * (t - 1) - (2 * t + 1)), ?_⟩
    rw [← Nat.pow_add]
    congr 1
    omega
  change (freshFact t) ^ (2 * t + 1) ∣
    (pFuel (t - 0 + (futureUnhit t 0 []).length)
      t 0 (futureUnhit t 0 [])).2
  exact Nat.dvd_trans hpower (by simpa only [Nat.sub_zero, hlen] using hlarge)

/-- Goal (2): the literal G(t) numerator has the common scan
    denominator as a factor at every production width t>=2. -/
theorem couponNodeScanDenDividesNumeratorAll
    (t : Nat) (ht : 2 ≤ t) :
    couponScanIntegerDen t ∣ couponNodeNumerator t := by
  by_cases hsmall : t ≤ 3
  · have hc : t = 2 ∨ t = 3 := by omega
    exact couponNodeScanDenDividesNumerator t hc
  · have hbig : 4 ≤ t := by omega
    obtain ⟨k, hk⟩ :=
      couponNodePairDenominatorContainsScanScale t hbig
    refine ⟨((harmonicPair (t + 3)).1 * freshFact (t + 3) *
      (t + 2) ^ 2 + (2 * (t + 2) + t) *
        (harmonicPair (t + 3)).2) * k, ?_⟩
    change
      (((harmonicPair (t + 3)).1 * freshFact (t + 3) *
        (t + 2) ^ 2 + (2 * (t + 2) + t) *
          (harmonicPair (t + 3)).2) * (pPair t).2) =
      couponScanIntegerDen t *
        (((harmonicPair (t + 3)).1 * freshFact (t + 3) *
          (t + 2) ^ 2 + (2 * (t + 2) + t) *
            (harmonicPair (t + 3)).2) * k)
    rw [hk]
    ac_rfl

/-- Every discount at the common scan scale is an exact Nat quotient. -/
theorem couponNodeScanExactAll (n t j : Nat) (A : List Nat)
    (ht : 2 ≤ t) :
    couponScanIntegerDen t ∣
      couponNodeBudget n t * couponScanIntegerNum t j A := by
  obtain ⟨k, hk⟩ := couponNodeScanDenDividesNumeratorAll t ht
  refine ⟨n * k * couponScanIntegerNum t j A, ?_⟩
  change (n * couponNodeNumerator t) *
      couponScanIntegerNum t j A =
    couponScanIntegerDen t *
      (n * k * couponScanIntegerNum t j A)
  rw [hk]
  ac_rfl


/-! ## Symbolic launch credit for arbitrary certificate width -/

/-- The paper numerator before division by p_scan, with its harmonic
    denominator already replaced by (t+3)!. -/
def couponNodeCreditCore (H F L t : Nat) : Nat :=
  H * F * L ^ 2 + (2 * L + t) * F

theorem couponNodeNumeratorCore (t : Nat) :
    couponNodeNumerator t =
      couponNodeCreditCore
        (harmonicPair (t + 3)).1 (freshFact (t + 3))
        (t + 2) t * (pPair t).2 := by
  change
    ((harmonicPair (t + 3)).1 * freshFact (t + 3) *
      (t + 2) ^ 2 + (2 * (t + 2) + t) *
      (harmonicPair (t + 3)).2) * (pPair t).2 =
    couponNodeCreditCore
      (harmonicPair (t + 3)).1 (freshFact (t + 3))
      (t + 2) t * (pPair t).2
  rw [couponNodeHarmonicDenFactorial]
  rfl

theorem couponNodeDenominatorCore (t : Nat) :
    couponNodeDenominator t =
      freshFact (t + 3) * (pPair t).1 := by
  change (harmonicPair (t + 3)).2 * (pPair t).1 =
    freshFact (t + 3) * (pPair t).1
  rw [couponNodeHarmonicDenFactorial]

/-- A cross-product, the common scan bound and a positive Q
    prove the unnormalised pPair itself lies in [0,1]. -/
theorem couponNodePairNumeratorLeDenominatorAll (t : Nat) :
    (pPair t).1 ≤ (pPair t).2 := by
  have hW := couponNodeScanNumeratorBoundAll t 0 []
  have hr := couponScanIntegerNum_represents t 0 []
  change couponScanIntegerNum t 0 [] * (pPair t).2 =
    (pPair t).1 * couponScanIntegerDen t at hr
  have hs :
      couponScanIntegerDen t * (pPair t).1 ≤
        couponScanIntegerDen t * (pPair t).2 := by
    calc
      _ = couponScanIntegerNum t 0 [] * (pPair t).2 := by
        rw [hr]
        ac_rfl
      _ ≤ couponScanIntegerDen t * (pPair t).2 :=
        Nat.mul_le_mul_right _ hW
  exact Nat.le_of_mul_le_mul_left hs (couponScanIntegerDen_pos t)

/-- A purely symbolic positive-factor bound, avoiding any
    closed-width arithmetic or evaluation of pPair. -/
private theorem couponNodeCreditCoreBounds
    (H F L t a b : Nat) (hab : a ≤ b) (hL : 1 ≤ L) :
    a * H * F * L + F * a ≤
      couponNodeCreditCore H F L t * b := by
  have hpower : L ≤ L ^ 2 := by
    have h := Nat.mul_le_mul_left L hL
    simpa only [Nat.one_mul, Nat.mul_one, Nat.pow_succ,
      Nat.pow_zero, Nat.pow_one] using h
  have hmain : H * F * L ≤ H * F * L ^ 2 :=
    Nat.mul_le_mul_left (H * F) hpower
  have hcoeff : 1 ≤ 2 * L + t := by omega
  have hminor : F ≤ (2 * L + t) * F := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right F hcoeff
  have hinside :
      H * F * L + F ≤ couponNodeCreditCore H F L t := by
    unfold couponNodeCreditCore
    exact Nat.add_le_add hmain hminor
  calc
    a * H * F * L + F * a =
        a * (H * F * L + F) := by
      rw [Nat.mul_add]
      ac_rfl
    _ ≤ b * (H * F * L + F) :=
      Nat.mul_le_mul_right _ hab
    _ ≤ b * couponNodeCreditCore H F L t :=
      Nat.mul_le_mul_left b hinside
    _ = couponNodeCreditCore H F L t * b := by ac_rfl

theorem couponNodeLaunchOneNoTruncationAll (n t : Nat) :
    n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) * (t + 2) +
      n * couponNodeDenominator t ≤ couponNodeBudget n t := by
  have hc := couponNodeCreditCoreBounds
    (harmonicPair (t + 3)).1 (freshFact (t + 3))
    (t + 2) t (pPair t).1 (pPair t).2
    (couponNodePairNumeratorLeDenominatorAll t) (by omega)
  have hs := Nat.mul_le_mul_left n hc
  calc
    n * (pPair t).1 * (harmonicPair (t + 3)).1 *
          freshFact (t + 3) * (t + 2) +
        n * couponNodeDenominator t =
      n * ((pPair t).1 * (harmonicPair (t + 3)).1 *
          freshFact (t + 3) * (t + 2) +
        freshFact (t + 3) * (pPair t).1) := by
          rw [couponNodeDenominatorCore]
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
            Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm]
    _ ≤ n * (couponNodeCreditCore
        (harmonicPair (t + 3)).1 (freshFact (t + 3))
        (t + 2) t * (pPair t).2) := hs
    _ = couponNodeBudget n t := by
      rw [couponNodeBudget, couponNodeNumeratorCore]

theorem couponNodeLaunchZeroNoTruncationAll (n t : Nat) :
    n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) ≤ couponNodeBudget n t := by
  have hs := couponNodeLaunchOneNoTruncationAll n t
  have hmult :
      n * (pPair t).1 * (harmonicPair (t + 3)).1 *
          freshFact (t + 3) ≤
      n * (pPair t).1 * (harmonicPair (t + 3)).1 *
          freshFact (t + 3) * (t + 2) := by
    have hh := Nat.mul_le_mul_left
      (n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3)) (by omega : 1 ≤ t + 2)
    simpa only [Nat.mul_one] using hh
  omega

theorem couponNodeLaunchZeroCreditExactAll (n t : Nat) :
    couponNodeLaunchPotential n t 0 +
      n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) = couponNodeBudget n t := by
  change
    (couponNodeBudget n t -
      n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3)) +
      n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) = couponNodeBudget n t
  exact Nat.sub_add_cancel (couponNodeLaunchZeroNoTruncationAll n t)

theorem couponNodeLaunchOneCreditExactAll (n t : Nat) :
    couponNodeLaunchPotential n t 1 +
      (n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        freshFact (t + 3) * (t + 2) +
      couponNodeDenominator t * n) =
      couponNodeBudget n t := by
  have hbound := couponNodeLaunchOneNoTruncationAll n t
  change
    ((couponNodeBudget n t -
        n * (pPair t).1 * (harmonicPair (t + 3)).1 *
          freshFact (t + 3) * (t + 2)) -
      n * couponNodeDenominator t) +
    (n * (pPair t).1 * (harmonicPair (t + 3)).1 *
      freshFact (t + 3) * (t + 2) +
      couponNodeDenominator t * n) =
    couponNodeBudget n t
  rw [Nat.mul_comm (couponNodeDenominator t) n, Nat.sub_sub]
  exact Nat.sub_add_cancel hbound

/-- Unnormalised scan probability gives an exact quotient of
    an arbitrary core multiple, even without a reduced fraction. -/
private theorem couponNodeCreditCoreQuotient
    (n H F L t a b W Q : Nat)
    (hQ : 0 < Q) (hr : W * b = a * Q) :
    (n * (couponNodeCreditCore H F L t * b) * W) / Q =
      n * couponNodeCreditCore H F L t * a := by
  have hproduct :
      n * (couponNodeCreditCore H F L t * b) * W =
      (n * couponNodeCreditCore H F L t * a) * Q := by
    calc
      _ = (n * couponNodeCreditCore H F L t) * (W * b) := by
        ac_rfl
      _ = (n * couponNodeCreditCore H F L t) * (a * Q) := by
        rw [hr]
      _ = (n * couponNodeCreditCore H F L t * a) * Q := by
        ac_rfl
  have hdivisible :
      Q ∣ n * (couponNodeCreditCore H F L t * b) * W := by
    refine ⟨n * couponNodeCreditCore H F L t * a, ?_⟩
    calc
      _ = (n * couponNodeCreditCore H F L t * a) * Q := hproduct
      _ = Q * (n * couponNodeCreditCore H F L t * a) := by ac_rfl
  apply Nat.eq_of_mul_eq_mul_right hQ
  calc
    ((n * (couponNodeCreditCore H F L t * b) * W) / Q) * Q =
        n * (couponNodeCreditCore H F L t * b) * W :=
      Nat.div_mul_cancel hdivisible
    _ = (n * couponNodeCreditCore H F L t * a) * Q := hproduct

private theorem couponNodeCreditCoreSplit
    (n H F L t a : Nat) :
    n * couponNodeCreditCore H F L t * a =
      L * (n * a * H * F * L) +
      (2 * L + t) * (F * a * n) := by
  unfold couponNodeCreditCore
  simp only [Nat.add_mul, Nat.mul_add, Nat.pow_succ,
    Nat.pow_one]
  ac_rfl

/-- The exact equality behind the scan-start credit: the scan
    potential is P minus L times the launch credit and 2 L
    denominator units, with no loss from Nat division. -/
private theorem couponNodeCreditCoreScanBalance
    (n H F L t a b W Q : Nat)
    (hQ : 0 < Q) (hab : a ≤ b)
    (hr : W * b = a * Q) :
    (n * (couponNodeCreditCore H F L t * b) -
        n * (couponNodeCreditCore H F L t * b) * W / Q +
      F * a * n * t) +
      L * (n * a * H * F * L) +
      2 * L * (F * a * n) =
    n * (couponNodeCreditCore H F L t * b) := by
  have hquot := couponNodeCreditCoreQuotient
    n H F L t a b W Q hQ hr
  have hle :
      n * couponNodeCreditCore H F L t * a ≤
        n * (couponNodeCreditCore H F L t * b) := by
    have hs := Nat.mul_le_mul_left
      (n * couponNodeCreditCore H F L t) hab
    simpa only [Nat.mul_assoc] using hs
  have hbalance :
      F * a * n * t +
        L * (n * a * H * F * L) +
        2 * L * (F * a * n) =
      n * couponNodeCreditCore H F L t * a := by
    rw [couponNodeCreditCoreSplit]
    rw [Nat.add_mul]
    ac_rfl
  calc
    (n * (couponNodeCreditCore H F L t * b) -
        n * (couponNodeCreditCore H F L t * b) * W / Q +
      F * a * n * t) +
      L * (n * a * H * F * L) +
      2 * L * (F * a * n) =
      (n * (couponNodeCreditCore H F L t * b) -
        n * couponNodeCreditCore H F L t * a) +
      (F * a * n * t +
        L * (n * a * H * F * L) +
        2 * L * (F * a * n)) := by
          rw [hquot]
          ac_rfl
    _ = (n * (couponNodeCreditCore H F L t * b) -
          n * couponNodeCreditCore H F L t * a) +
        n * couponNodeCreditCore H F L t * a := by
          rw [hbalance]
    _ = n * (couponNodeCreditCore H F L t * b) :=
      Nat.sub_add_cancel hle

/-- Scan-start potential identity with explicit factorial and
    unnormalised p_scan factors; holds at every positive width. -/
theorem couponNodeScanStartCreditExactAll (n t : Nat) (ht : 0 < t) :
    couponNodeScanPotential n t 0 [] +
      (t + 2) *
        (n * (pPair t).1 * (harmonicPair (t + 3)).1 *
          freshFact (t + 3) * (t + 2)) +
      2 * (t + 2) * (couponNodeDenominator t * n) =
      couponNodeBudget n t := by
  have hr := couponScanIntegerNum_represents t 0 []
  have hQ := couponScanIntegerDen_pos t
  have hc := couponNodeCreditCoreScanBalance
    n (harmonicPair (t + 3)).1 (freshFact (t + 3))
    (t + 2) t (pPair t).1 (pPair t).2
    (couponScanIntegerNum t 0 []) (couponScanIntegerDen t)
    hQ (couponNodePairNumeratorLeDenominatorAll t) hr
  have hnum := couponNodeNumeratorCore t
  have hden := couponNodeDenominatorCore t
  simpa only [couponNodeScanPotential, if_pos ht,
    couponNodeBudget, hnum, hden, Nat.sub_zero] using hc

/-- Elementary Nat cancellation once launch and scan credits are
    expressed as equalities with the same P and D. -/
private theorem couponNodeLaunchOneCreditAlgebra
    (P scan one C D L : Nat) (hL : 0 < L)
    (hone : one + (C + D) = P)
    (hscan : scan + L * C + 2 * L * D = P) :
    D + (scan + (L - 1) * P) + (L - 1) * D =
      L * one := by
  have hLP : P + (L - 1) * P = L * P := by
    have hs : 1 + (L - 1) = L := by omega
    calc
      _ = (1 + (L - 1)) * P := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = L * P := by rw [hs]
  have hLD : D + (L - 1) * D = L * D := by
    have hs : 1 + (L - 1) = L := by omega
    calc
      _ = (1 + (L - 1)) * D := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = L * D := by rw [hs]
  have hscaled : L * one + L * C + L * D = L * P := by
    have hs := congrArg (fun x : Nat => L * x) hone
    rw [Nat.mul_add, Nat.mul_add] at hs
    omega
  have hscan' : scan + L * C + 2 * (L * D) = P := by
    simpa only [Nat.mul_assoc] using hscan
  omega

/-- The exact (t+1)*n*D_t slack, not just nonnegativity.
    This is the structural launch-one row for all widths. -/
theorem couponNodeLaunchOneCreditRowSlackAll (n t : Nat) (ht : 2 ≤ t) :
    couponNodeDenominator t * n +
      (couponNodeScanPotential n t 0 [] +
        (t + 1) * couponNodeBudget n t) +
      (t + 1) * (couponNodeDenominator t * n) =
      (t + 2) * couponNodeLaunchPotential n t 1 := by
  have hone := couponNodeLaunchOneCreditExactAll n t
  have hscan := couponNodeScanStartCreditExactAll n t
    (by omega)
  have hrow := couponNodeLaunchOneCreditAlgebra
    (couponNodeBudget n t)
    (couponNodeScanPotential n t 0 [])
    (couponNodeLaunchPotential n t 1)
    (n * (pPair t).1 * (harmonicPair (t + 3)).1 *
      freshFact (t + 3) * (t + 2))
    (couponNodeDenominator t * n)
    (t + 2) (by omega) hone hscan
  have hl : t + 2 - 1 = t + 1 := by omega
  simpa only [hl] using hrow

/-- Goal (3), without dropping the exact slack certificate. -/
theorem couponNodeLaunchOneCreditRowAll (n t : Nat) (ht : 2 ≤ t) :
    couponNodeDenominator t * n +
      (couponNodeScanPotential n t 0 [] +
        (t + 1) * couponNodeBudget n t) ≤
      (t + 2) * couponNodeLaunchPotential n t 1 := by
  have hh := couponNodeLaunchOneCreditRowSlackAll n t ht
  omega

/-- The factorial-weighted cover register has a uniform symbolic
    upper bound, removing another small-width numerical table. -/
theorem couponNodeFactorialRangeSumLe (M : Nat) :
    ((List.range M).map freshFact).sum ≤ freshFact M := by
  induction M with
  | zero =>
      simp [freshFact]
  | succ M ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero]
      cases M with
      | zero =>
          decide
      | succ M =>
          have hsum :
              ((List.range (M + 1)).map freshFact).sum +
                  freshFact (M + 1) ≤
                2 * freshFact (M + 1) := by
            have hh := Nat.add_le_add_right ih (freshFact (M + 1))
            omega
          have hcoeff : 2 ≤ M + 2 := by omega
          have hmul :=
            Nat.mul_le_mul_right (freshFact (M + 1)) hcoeff
          change
            ((List.range (M + 1)).map freshFact).sum +
              freshFact (M + 1) ≤
            (M + 2) * freshFact (M + 1)
          omega

/-- General width cover potential subtraction is nontruncating. -/
theorem couponNodeCoverNoTruncationAll {n : Nat}
    (s : Fin n) (t : Nat) (mask : Fin n → Bool)
    (word : List (Fin n)) :
    n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        couponNodeCoverWeight s (t + 3) mask word ≤
      couponNodeBudget n t +
        n * (pPair t).1 *
          scaledHarmonic (freshFact (t + 3)) (maskSize mask) := by
  have hbound := couponNodeCoverWeightLeFactorialSum
    s (t + 3) mask word
  have hf := couponNodeFactorialRangeSumLe (t + 3)
  have hweight : couponNodeCoverWeight s (t + 3) mask word ≤
      freshFact (t + 3) := Nat.le_trans hbound hf
  have hscaled := Nat.mul_le_mul_left
    (n * (pPair t).1 * (harmonicPair (t + 3)).1) hweight
  have hcredit := couponNodeLaunchZeroNoTruncationAll n t
  calc
    n * (pPair t).1 * (harmonicPair (t + 3)).1 *
        couponNodeCoverWeight s (t + 3) mask word ≤
        n * (pPair t).1 * (harmonicPair (t + 3)).1 *
          freshFact (t + 3) := hscaled
    _ ≤ couponNodeBudget n t := hcredit
    _ ≤ couponNodeBudget n t +
          n * (pPair t).1 *
            scaledHarmonic (freshFact (t + 3)) (maskSize mask) :=
      Nat.le_add_right _ _



theorem couponNodeCoverSuccessorBalanceAll {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed) (mask : Fin n → Bool)
    (word : List (Fin n))
    (e : Fin n) :
    couponAttemptNodeValue
        (couponNodeBudget n (compileAdvice q).t)
        (fun a : CouponSeed fixed × CouponAttemptPhase n =>
          couponNodePotential (q := q) s a.2)
        ((couponTrialKernel ring fixed s).step
          (seed, .covering mask word) e) +
      n * (pPair (compileAdvice q).t).1 *
        (harmonicPair ((compileAdvice q).t + 3)).1 *
        couponNodeCoverOrderPayoff s ((compileAdvice q).t + 3)
          mask word e =
      couponNodeBudget n (compileAdvice q).t +
        n * (pPair (compileAdvice q).t).1 *
          scaledHarmonic (freshFact ((compileAdvice q).t + 3))
            (maskSize (maskDrop mask e)) := by
  by_cases hzero : maskSize (maskDrop mask e) = 0
  · by_cases haccept :
        lastAccept ((compileAdvice q).t + 3)
          ((word ++ [e]).map (protectedLabel s)) = 1
    · have hnormal :
          lastAccept ((compileAdvice q).t + 3)
            (word.map (protectedLabel s) ++ [protectedLabel s e]) = 1 := by
        simpa only [List.map_append, List.map_cons, List.map_nil]
          using haccept
      have hphase :
          couponAttemptPhaseNext (q := q) s
            (.covering mask word) e = .launching 0 := by
        simp [couponAttemptPhaseNext, hzero, hnormal,
          List.map_append]
      have hstep :
          (couponTrialKernel ring fixed s).step
            (seed, .covering mask word) e =
          .active (couponSeedStep ring fixed s seed e, .launching 0) := by
        simp [couponTrialKernel, hphase]
      have hreward :
          couponNodeCoverOrderPayoff s
              ((compileAdvice q).t + 3) mask word e =
            freshFact ((compileAdvice q).t + 3) := by
        simp only [couponNodeCoverOrderPayoff, if_pos hzero,
          haccept, Nat.mul_one]
      have hlaunch :=
        couponNodeLaunchZeroNoTruncationAll n (compileAdvice q).t
      rw [hstep, hreward, hzero]
      exact Nat.sub_add_cancel hlaunch
    · have hacceptzero :
          lastAccept ((compileAdvice q).t + 3)
            ((word ++ [e]).map (protectedLabel s)) = 0 := by
        have hcases :=
          orderedAccept_range ((compileAdvice q).t + 3)
            (((word ++ [e]).map (protectedLabel s)).reverse)
        change
          lastAccept ((compileAdvice q).t + 3)
              ((word ++ [e]).map (protectedLabel s)) = 0 ∨
          lastAccept ((compileAdvice q).t + 3)
              ((word ++ [e]).map (protectedLabel s)) = 1 at hcases
        rcases hcases with hz | ho
        · exact hz
        · exact False.elim (haccept ho)
      have hnormal :
          lastAccept ((compileAdvice q).t + 3)
            (word.map (protectedLabel s) ++ [protectedLabel s e]) = 0 := by
        simpa only [List.map_append, List.map_cons, List.map_nil]
          using hacceptzero
      have hphase :
          couponAttemptPhaseNext (q := q) s
            (.covering mask word) e = .failed := by
        simp [couponAttemptPhaseNext, hzero, hnormal,
          List.map_append]
      have hstep :
          (couponTrialKernel ring fixed s).step
            (seed, .covering mask word) e =
          .retry (couponSeedStep ring fixed s seed e) := by
        simp [couponTrialKernel, hphase]
      have hreward :
          couponNodeCoverOrderPayoff s
              ((compileAdvice q).t + 3) mask word e = 0 := by
        simp only [couponNodeCoverOrderPayoff, if_pos hzero,
          hacceptzero, Nat.mul_zero]
      rw [hstep, hreward, hzero] <;> rfl
  · have hphase :
        couponAttemptPhaseNext (q := q) s
          (.covering mask word) e =
        .covering (maskDrop mask e) (word ++ [e]) := by
      simp [couponAttemptPhaseNext, hzero]
    have hstep :
        (couponTrialKernel ring fixed s).step
          (seed, .covering mask word) e =
        .active (couponSeedStep ring fixed s seed e,
          .covering (maskDrop mask e) (word ++ [e])) := by
      simp [couponTrialKernel, hphase]
    have hreward :
        couponNodeCoverOrderPayoff s
            ((compileAdvice q).t + 3) mask word e =
          couponNodeCoverWeight s ((compileAdvice q).t + 3)
            (maskDrop mask e) (word ++ [e]) := by
      simp only [couponNodeCoverOrderPayoff, if_neg hzero]
    have hcover :=
      couponNodeCoverNoTruncationAll s (compileAdvice q).t
        (maskDrop mask e) (word ++ [e])
    rw [hstep, hreward]
    exact Nat.sub_add_cancel hcover

/-- Pure Nat cover Bellman identity. Expensive protocol expressions
    are instantiated only after this arithmetic has been proved on
    abstract symbols and three finite-edge functions. -/
private theorem couponNodeCoverBellmanAlgebra {n : Nat}
    (D P B C H S V F : Nat)
    (E R Hnext : Fin n → Nat)
    (hH : F + (List.ofFn Hnext).sum = n * H)
    (horder : (List.ofFn R).sum = n * S)
    (hcoef : D * n = B * F)
    (hcur : V + C * S = P + B * H)
    (hpoint : ∀ e : Fin n,
      E e + C * R e = P + B * Hnext e) :
    D * n + (List.ofFn E).sum = n * V := by
  have hsum :
      (List.ofFn E).sum + C * (List.ofFn R).sum =
      n * P + B * (List.ofFn Hnext).sum := by
    calc
      (List.ofFn E).sum + C * (List.ofFn R).sum =
          (List.ofFn (fun e : Fin n => E e + C * R e)).sum := by
            rw [ofFn_sum_add, ofFn_sum_mul_left]
      _ = (List.ofFn (fun e : Fin n => P + B * Hnext e)).sum :=
        ofFn_sum_eq _ _ hpoint
      _ = n * P + B * (List.ofFn Hnext).sum := by
        rw [ofFn_sum_add, ofFn_sum_const, ofFn_sum_mul_left]
  have hfinish :
      (D * n + (List.ofFn E).sum) + n * (C * S) =
        n * V + n * (C * S) := by
    calc
      (D * n + (List.ofFn E).sum) + n * (C * S) =
          B * F + ((List.ofFn E).sum + C * (n * S)) := by
            rw [hcoef]
            ac_rfl
      _ = B * F +
          ((List.ofFn E).sum + C * (List.ofFn R).sum) := by
        rw [horder]
      _ = B * F + (n * P + B * (List.ofFn Hnext).sum) := by
        rw [hsum]
      _ = n * P + B * (F + (List.ofFn Hnext).sum) := by
        rw [Nat.mul_add]
        ac_rfl
      _ = n * P + B * (n * H) := by rw [hH]
      _ = n * (P + B * H) := by
        rw [Nat.mul_add]
        ac_rfl
      _ = n * (V + C * S) := by rw [hcur]
      _ = n * V + n * (C * S) := by rw [Nat.mul_add]
  exact Nat.add_right_cancel hfinish

/-- Full cover-phase drift at arbitrary width, with the original
    protected physical labels and the same RetryKernel edges. -/
theorem couponNodeCoverDriftAll {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed) (mask : Fin n → Bool)
    (word : List (Fin n))
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hmask : mask = word.foldl maskDrop
      (fun i : Fin n =>
        canonicalMask ((compileAdvice q).t + 3)
          (protectedLabel s i)))
    (hpos : 0 < maskSize mask) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .covering mask word) e))).sum =
      n * couponNodeCoverPotential s (compileAdvice q).t
        mask word := by
  have hmle : maskSize mask ≤ (compileAdvice q).t + 3 :=
    couponNodeCoherentMaskSizeLe
      s ((compileAdvice q).t + 3) mask word hn hmask
  have hdiv : maskSize mask ∣
      freshFact ((compileAdvice q).t + 3) :=
    coupon_factorial_dvd ((compileAdvice q).t + 3)
      (maskSize mask) hpos hmle
  have hH :
      freshFact ((compileAdvice q).t + 3) +
        (List.ofFn (fun e : Fin n =>
          scaledHarmonic
            (freshFact ((compileAdvice q).t + 3))
            (maskSize (maskDrop mask e)))).sum =
      n * scaledHarmonic
        (freshFact ((compileAdvice q).t + 3))
        (maskSize mask) :=
    couponNodeScaledHarmonicMaskRow
      (freshFact ((compileAdvice q).t + 3))
      mask hpos hdiv
  have horder :
      (List.ofFn (fun e : Fin n =>
        couponNodeCoverOrderPayoff s
          ((compileAdvice q).t + 3) mask word e)).sum =
      n * couponNodeCoverWeight s
        ((compileAdvice q).t + 3) mask word :=
    couponNodeCoverOrderHarmonic s
      ((compileAdvice q).t + 3) mask word
      (by omega) hn hmask hpos
  have hcoef :
      couponNodeDenominator (compileAdvice q).t * n =
        (n * (pPair (compileAdvice q).t).1) *
          freshFact ((compileAdvice q).t + 3) := by
    change
      ((harmonicPair ((compileAdvice q).t + 3)).2 *
        (pPair (compileAdvice q).t).1) * n =
      (n * (pPair (compileAdvice q).t).1) *
        freshFact ((compileAdvice q).t + 3)
    rw [couponNodeHarmonicDenFactorial]
    ac_rfl
  have hcur :
      couponNodeCoverPotential s (compileAdvice q).t
          mask word +
        (n * (pPair (compileAdvice q).t).1 *
          (harmonicPair ((compileAdvice q).t + 3)).1) *
          couponNodeCoverWeight s ((compileAdvice q).t + 3)
            mask word =
      couponNodeBudget n (compileAdvice q).t +
        (n * (pPair (compileAdvice q).t).1) *
          scaledHarmonic (freshFact ((compileAdvice q).t + 3))
            (maskSize mask) := by
    change
      (couponNodeBudget n (compileAdvice q).t +
          n * (pPair (compileAdvice q).t).1 *
            scaledHarmonic
              (freshFact ((compileAdvice q).t + 3))
              (maskSize mask) -
          n * (pPair (compileAdvice q).t).1 *
            (harmonicPair ((compileAdvice q).t + 3)).1 *
            couponNodeCoverWeight s ((compileAdvice q).t + 3)
              mask word) +
        (n * (pPair (compileAdvice q).t).1 *
          (harmonicPair ((compileAdvice q).t + 3)).1) *
          couponNodeCoverWeight s ((compileAdvice q).t + 3)
            mask word =
      couponNodeBudget n (compileAdvice q).t +
        (n * (pPair (compileAdvice q).t).1) *
          scaledHarmonic (freshFact ((compileAdvice q).t + 3))
            (maskSize mask)
    have hbound := couponNodeCoverNoTruncationAll s
      (compileAdvice q).t mask word
    have he :
        n * (pPair (compileAdvice q).t).1 *
          (harmonicPair ((compileAdvice q).t + 3)).1 *
          couponNodeCoverWeight s ((compileAdvice q).t + 3)
            mask word =
        (n * (pPair (compileAdvice q).t).1 *
          (harmonicPair ((compileAdvice q).t + 3)).1) *
          couponNodeCoverWeight s ((compileAdvice q).t + 3)
            mask word := by ac_rfl
    rw [← he]
    exact Nat.sub_add_cancel hbound
  have hpoint (e : Fin n) :
      couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .covering mask word) e) +
        (n * (pPair (compileAdvice q).t).1 *
          (harmonicPair ((compileAdvice q).t + 3)).1) *
          couponNodeCoverOrderPayoff s
            ((compileAdvice q).t + 3) mask word e =
      couponNodeBudget n (compileAdvice q).t +
        (n * (pPair (compileAdvice q).t).1) *
          scaledHarmonic (freshFact ((compileAdvice q).t + 3))
            (maskSize (maskDrop mask e)) := by
    have hh := couponNodeCoverSuccessorBalanceAll
      ring fixed s seed mask word e
    simpa only [Nat.mul_assoc] using hh
  exact couponNodeCoverBellmanAlgebra
    (couponNodeDenominator (compileAdvice q).t)
    (couponNodeBudget n (compileAdvice q).t)
    (n * (pPair (compileAdvice q).t).1)
    (n * (pPair (compileAdvice q).t).1 *
      (harmonicPair ((compileAdvice q).t + 3)).1)
    (scaledHarmonic (freshFact ((compileAdvice q).t + 3))
      (maskSize mask))
    (couponNodeCoverWeight s ((compileAdvice q).t + 3)
      mask word)
    (couponNodeCoverPotential s (compileAdvice q).t
      mask word)
    (freshFact ((compileAdvice q).t + 3))
    (fun e : Fin n => couponAttemptNodeValue
      (couponNodeBudget n (compileAdvice q).t)
      (fun a : CouponSeed fixed × CouponAttemptPhase n =>
        couponNodePotential (q := q) s a.2)
      ((couponTrialKernel ring fixed s).step
        (seed, .covering mask word) e))
    (fun e : Fin n => couponNodeCoverOrderPayoff
      s ((compileAdvice q).t + 3) mask word e)
    (fun e : Fin n => scaledHarmonic
      (freshFact ((compileAdvice q).t + 3))
      (maskSize (maskDrop mask e)))
    hH horder hcoef hcur hpoint


/-- General-width coverReach: structural replacement of the two/three case. -/
theorem couponNodeReachableCoverDriftAll {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (mask : Fin n → Bool) (word : List (Fin n))
    (hreach : couponNodeReachable ring fixed s a)
    (hphase : a.2 = .covering mask word) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun b : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s b.2)
          ((couponTrialKernel ring fixed s).step a e))).sum =
      n * couponNodePotential (q := q) s a.2 := by
  have hmask := couponNodeReachableCoverMaskFold
    ring fixed s a mask word hreach hphase
  have hpos := couponNodeReachableCoverMaskPositive
    ring fixed s hn a mask word hreach hphase
  cases a with
  | mk seed phase =>
      change phase = .covering mask word at hphase
      rw [hphase]
      exact couponNodeCoverDriftAll
        ring fixed s seed mask word hn hmask hpos


/-- General-width launchZero: structural replacement of the two/three case. -/
theorem couponNodeLaunchZeroDriftAll {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .launching 0) e))).sum =
      n * couponNodeLaunchPotential n (compileAdvice q).t 0 := by
  rw [couponNodeLaunchZeroEdgeSum ring fixed s seed hn,
    outsideLaunch_size s hn]
  have hcount :
      n - 1 - (n - ((compileAdvice q).t + 2)) =
        ((compileAdvice q).t + 2) - 1 := by omega
  rw [hcount]
  exact couponNodeLaunchZeroCreditAlgebra
    n ((compileAdvice q).t + 2)
    (couponNodeDenominator (compileAdvice q).t)
    (couponNodeBudget n (compileAdvice q).t)
    (n * (pPair (compileAdvice q).t).1 *
      (harmonicPair ((compileAdvice q).t + 3)).1 *
      freshFact ((compileAdvice q).t + 3))
    (couponNodeLaunchPotential n (compileAdvice q).t 0)
    (couponNodeLaunchPotential n (compileAdvice q).t 1)
    (by omega) (by omega)
    (couponNodeLaunchZeroCreditExactAll
      n (compileAdvice q).t)
    (couponNodeLaunchOneCreditExactAll
      n (compileAdvice q).t)



/-- General-width launchOne: structural replacement of the two/three case. -/
theorem couponNodeLaunchOneDriftAll {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (seed : CouponSeed fixed)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .launching 1) e))).sum ≤
      n * couponNodeLaunchPotential n (compileAdvice q).t 1 := by
  rw [couponNodeLaunchOneEdgeSum ring fixed s seed hn,
    outsideLaunch_size s hn]
  have hcount :
      n - 1 - (n - ((compileAdvice q).t + 2)) =
        (compileAdvice q).t + 1 := by omega
  rw [hcount]
  have hrow := couponNodeLaunchOneCreditRowAll
    n (compileAdvice q).t ht
  calc
    _ =
        (couponNodeDenominator (compileAdvice q).t * n +
          (couponNodeScanPotential n (compileAdvice q).t 0 [] +
            ((compileAdvice q).t + 1) *
              couponNodeBudget n (compileAdvice q).t)) +
        (n - ((compileAdvice q).t + 2)) *
          couponNodeLaunchPotential n (compileAdvice q).t 1 := by
            ac_rfl
    _ ≤ ((compileAdvice q).t + 2) *
          couponNodeLaunchPotential n (compileAdvice q).t 1 +
        (n - ((compileAdvice q).t + 2)) *
          couponNodeLaunchPotential n (compileAdvice q).t 1 :=
            Nat.add_le_add_right hrow _
    _ = n * couponNodeLaunchPotential n (compileAdvice q).t 1 := by
          rw [← Nat.add_mul]
          have hsize :
              ((compileAdvice q).t + 2) +
                (n - ((compileAdvice q).t + 2)) = n := by omega
          rw [hsize]



/-- General-width scan: structural replacement of the two/three case. -/
theorem couponNodeReachableScanDriftAll {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (seed : CouponSeed fixed) (j : Nat) (once : List Nat)
    (hreach : couponNodeReachable ring fixed s
      (seed, .scanning j once)) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .scanning j once) e))).sum ≤
      n * couponNodeScanPotential n (compileAdvice q).t
        j once := by
  obtain ⟨k, hnum⟩ :=
    couponNodeScanDenDividesNumeratorAll
      (compileAdvice q).t ht
  have hj : j < (compileAdvice q).t :=
    couponNodeReachableScanBelow ring fixed s ht
      seed j once hreach
  have hweight :
      (List.ofFn (fun e : Fin n =>
        couponScanIntegerWeight (compileAdvice q).t
          (tolerantScanStep s (compileAdvice q).t
            (.live j once) e))).sum =
        n * couponScanIntegerNum (compileAdvice q).t
          j once := by
    exact coupon_scan_integer_harmonic
      s (compileAdvice q).t (by omega) (.live j once)
  have hcurrent :
      couponScanIntegerNum (compileAdvice q).t j once ≤
        couponScanIntegerDen (compileAdvice q).t :=
    couponNodeScanNumeratorBoundAll
      (compileAdvice q).t j once
  have hchildren (e : Fin n) :
      couponScanIntegerWeight (compileAdvice q).t
        (tolerantScanStep s (compileAdvice q).t
          (.live j once) e) ≤
        couponScanIntegerDen (compileAdvice q).t := by
    cases hs : tolerantScanStep s (compileAdvice q).t
        (.live j once) e with
    | failed =>
        change 0 ≤ couponScanIntegerDen (compileAdvice q).t
        exact Nat.zero_le _
    | live k A =>
        exact couponNodeScanNumeratorBoundAll
          (compileAdvice q).t k A
  have hprogress :=
    couponNodeScanRemainingRow s (compileAdvice q).t j once
      (by omega) hj
  have hcomplement (e : Fin n) :
      couponNodeScanChildValue n (compileAdvice q).t
          (tolerantScanStep s (compileAdvice q).t
            (.live j once) e) =
        (n * k) *
          (couponScanIntegerDen (compileAdvice q).t -
            couponScanIntegerWeight (compileAdvice q).t
              (tolerantScanStep s (compileAdvice q).t
                (.live j once) e)) +
        couponNodeDenominator (compileAdvice q).t * n *
          tolerantRemaining (compileAdvice q).t
            (tolerantScanStep s (compileAdvice q).t
              (.live j once) e) :=
    couponNodeScanChildComplement n
      (compileAdvice q).t k hnum _
  have hsum :
      (List.ofFn (fun e : Fin n =>
        couponNodeScanChildValue n (compileAdvice q).t
          (tolerantScanStep s (compileAdvice q).t
            (.live j once) e))).sum =
      (List.ofFn (fun e : Fin n =>
        (n * k) *
          (couponScanIntegerDen (compileAdvice q).t -
            couponScanIntegerWeight (compileAdvice q).t
              (tolerantScanStep s (compileAdvice q).t
                (.live j once) e)) +
        couponNodeDenominator (compileAdvice q).t * n *
          tolerantRemaining (compileAdvice q).t
            (tolerantScanStep s (compileAdvice q).t
              (.live j once) e))).sum :=
    ofFn_sum_eq _ _ hcomplement
  have hdrift :=
    couponNodeScanCombinedDrift
      (couponNodeDenominator (compileAdvice q).t)
      (n * k)
      (couponScanIntegerDen (compileAdvice q).t)
      (couponScanIntegerNum (compileAdvice q).t j once)
      ((compileAdvice q).t - j)
      (fun e : Fin n =>
        couponScanIntegerWeight (compileAdvice q).t
          (tolerantScanStep s (compileAdvice q).t
            (.live j once) e))
      (fun e : Fin n =>
        tolerantRemaining (compileAdvice q).t
          (tolerantScanStep s (compileAdvice q).t
            (.live j once) e))
      hcurrent hchildren hweight hprogress
  have hstart :
      couponNodeScanPotential n (compileAdvice q).t
          j once =
        (n * k) *
          (couponScanIntegerDen (compileAdvice q).t -
            couponScanIntegerNum (compileAdvice q).t
              j once) +
        couponNodeDenominator (compileAdvice q).t * n *
          ((compileAdvice q).t - j) :=
    couponNodeScanPotentialComplement
      n (compileAdvice q).t j once k hnum hj
  calc
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun a : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s a.2)
          ((couponTrialKernel ring fixed s).step
            (seed, .scanning j once) e))).sum =
        couponNodeDenominator (compileAdvice q).t * n +
          (List.ofFn (fun e : Fin n =>
            couponNodeScanChildValue n (compileAdvice q).t
              (tolerantScanStep s (compileAdvice q).t
                (.live j once) e))).sum := by
            rw [couponNodeReachableScanEdgeSum
              ring fixed s ht hn hroot hbad seed j once hreach]
    _ = couponNodeDenominator (compileAdvice q).t * n +
          (List.ofFn (fun e : Fin n =>
            (n * k) *
              (couponScanIntegerDen (compileAdvice q).t -
                couponScanIntegerWeight (compileAdvice q).t
                  (tolerantScanStep s (compileAdvice q).t
                    (.live j once) e)) +
            couponNodeDenominator (compileAdvice q).t * n *
              tolerantRemaining (compileAdvice q).t
                (tolerantScanStep s (compileAdvice q).t
                  (.live j once) e))).sum := by rw [hsum]
    _ ≤ n * ((n * k) *
          (couponScanIntegerDen (compileAdvice q).t -
            couponScanIntegerNum (compileAdvice q).t j once) +
        couponNodeDenominator (compileAdvice q).t * n *
          ((compileAdvice q).t - j)) := hdrift
    _ = n * couponNodeScanPotential n (compileAdvice q).t
          j once := by rw [hstart]



/-- General-width reachable: structural replacement of the two/three case. -/
theorem couponNodeReachablePotentialDriftAll {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (a : CouponSeed fixed × CouponAttemptPhase n)
    (hreach : couponNodeReachable ring fixed s a) :
    couponNodeDenominator (compileAdvice q).t * n +
      (List.ofFn (fun e : Fin n =>
        couponAttemptNodeValue
          (couponNodeBudget n (compileAdvice q).t)
          (fun b : CouponSeed fixed × CouponAttemptPhase n =>
            couponNodePotential (q := q) s b.2)
          ((couponTrialKernel ring fixed s).step a e))).sum ≤
      n * couponNodePotential (q := q) s a.2 := by
  have hterminal :=
    couponNodeReachableNonterminal ring fixed s a hreach
  cases a with
  | mk seed phase =>
      cases phase with
      | covering mask word =>
          exact Nat.le_of_eq
            (couponNodeReachableCoverDriftAll ring fixed s
              hn (seed, .covering mask word)
              mask word hreach rfl)
      | launching hits =>
          have hhits :=
            couponNodeReachableLaunchingHits
              ring fixed s seed hits hreach
          rcases hhits with hzero | hone
          · subst hits
            exact Nat.le_of_eq
              (couponNodeLaunchZeroDriftAll
                ring fixed s seed hn)
          · subst hits
            exact couponNodeLaunchOneDriftAll
              ring fixed s seed ht hn
      | scanning j once =>
          exact couponNodeReachableScanDriftAll
            ring fixed s ht hn hroot hbad
            seed j once hreach
      | succeeded =>
          exact False.elim (hterminal.1 rfl)
      | failed =>
          exact False.elim (hterminal.2 rfl)


/-- General-width budget: structural replacement of the two/three case. -/
theorem couponNodeJointBudgetOnFailureAll {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n) :
    CouponJointBudgetOnFailure ring fixed s := by
  intro ht hn hroot hbad seed T
  exact couponNodeBudgetFromGoodDrift
    (couponTrialKernel ring fixed s)
    (couponNodeReachable ring fixed s)
    (couponNodeDenominator (compileAdvice q).t)
    (couponNodeBudget n (compileAdvice q).t)
    (fun a : CouponSeed fixed × CouponAttemptPhase n =>
      couponNodePotential (q := q) s a.2)
    (fun a e b ha hstep =>
      couponNodeReachableClosed ring fixed s a b e ha hstep)
    (fun a ha =>
      couponNodeReachablePotentialDriftAll ring fixed s
        ht hn hroot hbad a ha)
    (fun child _ => couponNodeReachableStart ring fixed s child)
    (fun child _ =>
      Nat.le_of_eq (couponNodeStartPotentialExact s hn))
    seed (by trivial) T
end L3.CouponClear


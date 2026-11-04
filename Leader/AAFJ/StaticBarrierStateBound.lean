import Leader.Core.Basic
import Init.Data.List.OfFn
import Init.Data.List.Pairwise
import Init.Data.List.Perm
import Init.Data.Nat.Div.Lemmas
import Init.Data.Nat.Lemmas
import Init.Omega
import Init.RCases

set_option autoImplicit false

namespace StaticBarrierStateBound

/-! ## Least positive nondivisor, by bounded core-only search -/

private def firstNonDivisor (n start fuel : Nat) : Nat :=
  match fuel with
  | 0 => start
  | fuel + 1 =>
      if start ∣ n then
        firstNonDivisor n (start + 1) fuel
      else
        start

/-- Least positive integer not dividing `n` for positive `n`.
At `n = 0` the total bounded search returns `2`; semantic
nondivisibility theorems below explicitly exclude that case. -/
def lnd (n : Nat) : Nat :=
  firstNonDivisor n 2 n

private theorem firstNonDivisor_ge
    (n start fuel : Nat) :
    start ≤ firstNonDivisor n start fuel := by
  induction fuel generalizing start with
  | zero =>
      simp [firstNonDivisor]
  | succ fuel ih =>
      simp only [firstNonDivisor]
      by_cases hs : start ∣ n
      · rw [if_pos hs]
        exact Nat.le_trans (by omega) (ih (start := start + 1))
      · rw [if_neg hs]
        exact Nat.le_refl start

private theorem firstNonDivisor_spec
    (n start fuel : Nat) (hn : 0 < n)
    (hcover : n < start + fuel) :
    start ≤ firstNonDivisor n start fuel ∧
      ¬ firstNonDivisor n start fuel ∣ n ∧
      ∀ j, start ≤ j →
        j < firstNonDivisor n start fuel → j ∣ n := by
  induction fuel generalizing start with
  | zero =>
      simp only [firstNonDivisor]
      refine ⟨Nat.le_refl _, ?_, ?_⟩
      · intro hdiv
        have hle : start ≤ n := Nat.le_of_dvd hn hdiv
        omega
      · intro j hj hjlt
        omega
  | succ fuel ih =>
      simp only [firstNonDivisor]
      by_cases hs : start ∣ n
      · rw [if_pos hs]
        rcases ih (start := start + 1) (by omega) with
          ⟨hlo, hnd, hmin⟩
        refine ⟨by omega, hnd, ?_⟩
        intro j hj hjlt
        by_cases hjs : j = start
        · simpa [hjs] using hs
        · exact hmin j (by omega) hjlt
      · rw [if_neg hs]
        refine ⟨Nat.le_refl _, hs, ?_⟩
        intro j hj hjlt
        omega

private theorem lnd_spec (n : Nat) (hn : 0 < n) :
    2 ≤ lnd n ∧
      ¬ lnd n ∣ n ∧
      ∀ j, 2 ≤ j → j < lnd n → j ∣ n := by
  unfold lnd
  exact firstNonDivisor_spec n 2 n hn (by omega)

/-- The bounded search always returns a positive integer. -/
theorem lnd_pos (n : Nat) : 0 < lnd n := by
  unfold lnd
  have h := firstNonDivisor_ge n 2 n
  omega

/-- For nonzero `n`, the selected value really does not divide `n`. -/
theorem not_dvd_lnd {n : Nat} (hn : n ≠ 0) :
    ¬ lnd n ∣ n := by
  have hnpos : 0 < n := by omega
  exact (lnd_spec n hnpos).2.1

/-- Every positive integer strictly below `lnd n` divides `n`. -/
theorem dvd_of_lt_lnd {n c : Nat}
    (hc : 0 < c) (hclt : c < lnd n) :
    c ∣ n := by
  by_cases hn : n = 0
  · subst n
    exact Nat.dvd_zero c
  · have hnpos : 0 < n := by omega
    by_cases hc1 : c = 1
    · subst c
      exact Nat.one_dvd n
    · exact (lnd_spec n hnpos).2.2 c (by omega) hclt

/-- For `n ≥ 3`, the least nondivisor is at most `n-1`.
The premise cannot be weakened to `2 ≤ n`: `lnd 2 = 3`. -/
theorem lnd_le {n : Nat} (hn : 3 ≤ n) :
    lnd n ≤ n - 1 := by
  have hnpos : 0 < n := by omega
  have hspec := lnd_spec n hnpos
  have hnot : ¬ (n - 1) ∣ n := by
    intro hd
    rcases hd with ⟨q, hq⟩
    by_cases hq0 : q = 0
    · subst q
      simp at hq
      omega
    · by_cases hq1 : q = 1
      · subst q
        simp at hq
        omega
      · have hq2 : 2 ≤ q := by omega
        have hmul :
            (n - 1) * 2 ≤ (n - 1) * q :=
          Nat.mul_le_mul_left (n - 1) hq2
        rw [← hq] at hmul
        omega
  apply Nat.le_of_not_gt
  intro hlt
  exact hnot (hspec.2.2 (n - 1) (by omega) hlt)

/-! ## Static smooth-edge predicates on the directed ring -/

/-- Canonical clockwise successor on `Fin n`. -/
private def succFin {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (by
    have hi : i.val < n := i.isLt
    omega)⟩

/-- Every ring edge is smooth. -/
def ZeroBarrier {n m : Nat}
    (Smooth : Fin m → Fin m → Prop)
    (L : Fin n → Fin m) : Prop :=
  ∀ i : Fin n, Smooth (L i) (L (succFin i))

/-- Exactly one ring edge is nonsmooth. -/
def OneBarrier {n m : Nat}
    (Smooth : Fin m → Fin m → Prop)
    (L : Fin n → Fin m) : Prop :=
  ∃ bad : Fin n,
    ¬ Smooth (L bad) (L (succFin bad)) ∧
    ∀ i : Fin n, i ≠ bad →
      Smooth (L i) (L (succFin i))

/-! ## Core ring arithmetic -/

private theorem mod_succ_eq (k n : Nat) :
    (k % n + 1) % n = (k + 1) % n := by
  rw [Nat.add_mod (k % n) 1 n, Nat.mod_mod]
  exact (Nat.add_mod k 1 n).symm

private def cwPos {n : Nat} (hn : 0 < n)
    (i : Fin n) (t : Nat) : Fin n :=
  ⟨(i.val + t) % n, Nat.mod_lt _ hn⟩

@[simp] private theorem cwPos_zero {n : Nat} (hn : 0 < n)
    (i : Fin n) :
    cwPos hn i 0 = i := by
  apply Fin.ext
  simp [cwPos, Nat.mod_eq_of_lt i.isLt]

@[simp] private theorem cwPos_period {n : Nat} (hn : 0 < n)
    (i : Fin n) :
    cwPos hn i n = i := by
  apply Fin.ext
  simp [cwPos, Nat.mod_eq_of_lt i.isLt]

private theorem cwPos_succ {n : Nat} (hn : 0 < n)
    (i : Fin n) (t : Nat) :
    cwPos hn i (t + 1) = succFin (cwPos hn i t) := by
  apply Fin.ext
  unfold cwPos succFin
  dsimp only
  rw [mod_succ_eq]
  congr 1

private theorem cwPos_succStart {n : Nat} (hn : 0 < n)
    (i : Fin n) (t : Nat) :
    cwPos hn (succFin i) t = cwPos hn i (t + 1) := by
  apply Fin.ext
  unfold cwPos succFin
  dsimp only
  rw [Nat.mod_add_mod]
  congr 1
  omega

private theorem cwPos_bounded_injective {n : Nat} (hn : 0 < n)
    (i : Fin n) (a b : Nat)
    (ha : a < n) (hb : b < n)
    (h : cwPos hn i a = cwPos hn i b) :
    a = b := by
  have hv := congrArg Fin.val h
  unfold cwPos at hv
  dsimp only at hv
  by_cases haWrap : i.val + a < n
  · rw [Nat.mod_eq_of_lt haWrap] at hv
    by_cases hbWrap : i.val + b < n
    · rw [Nat.mod_eq_of_lt hbWrap] at hv
      omega
    · rw [Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)] at hv
      omega
  · rw [Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)] at hv
    by_cases hbWrap : i.val + b < n
    · rw [Nat.mod_eq_of_lt hbWrap] at hv
      omega
    · rw [Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)] at hv
      omega

private theorem cwPos_after_bad_ne_bad_before_last
    {n : Nat} (hn : 0 < n) (bad : Fin n)
    (t : Nat) (ht : t < n - 1) :
    cwPos hn (succFin bad) t ≠ bad := by
  intro h
  have hlast :
      cwPos hn (succFin bad) (n - 1) = bad := by
    rw [cwPos_succStart]
    have hsum : n - 1 + 1 = n := by omega
    rw [hsum, cwPos_period]
  have heq :=
    cwPos_bounded_injective hn (succFin bad) t (n - 1)
      (by omega) (by omega) (h.trans hlast.symm)
  omega

/-! ## Finite pigeonhole, without Fintype/Finset -/

private theorem nodup_ofFn_of_injective
    {q : Nat} {α : Type}
    (f : Fin q → α) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hm
        rw [List.mem_ofFn] at hm
        obtain ⟨i, hi⟩ := hm
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem fin_le_of_injective {a b : Nat}
    (f : Fin a → Fin b) (hf : Function.Injective f) :
    a ≤ b := by
  have hnodup : (List.ofFn f).Nodup :=
    nodup_ofFn_of_injective f hf
  have hsubset :
      List.ofFn f ⊆ List.ofFn (fun i : Fin b => i) := by
    intro color _
    exact List.mem_ofFn.mpr ⟨color, rfl⟩
  have hle := hnodup.length_le_of_subset hsubset
  simpa using hle

private theorem fin_repeat {m : Nat}
    (f : Fin (m + 1) → Fin m) :
    ∃ i j : Fin (m + 1),
      i.val < j.val ∧ f i = f j := by
  have hnotinj : ¬ Function.Injective f := by
    intro hf
    have hle := fin_le_of_injective f hf
    omega
  apply Classical.byContradiction
  intro hnone
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_cases hlt : i.val < j.val
    · exact False.elim (hnone ⟨i, j, hlt, hij⟩)
    · by_cases hgt : j.val < i.val
      · exact False.elim (hnone ⟨j, i, hgt, hij.symm⟩)
      · omega
  exact hnotinj hinj

/-! ## Static state lower bound -/

/-- A static pair predicate that has a one-barrier `n`-ring but no
zero-barrier `n`-ring needs at least `lnd n` local symbols. -/
theorem static_barrier_state_bound
    {n m : Nat}
    (hn : 3 ≤ n)
    (Smooth : Fin m → Fin m → Prop)
    (h1 : ∃ L : Fin n → Fin m, OneBarrier Smooth L)
    (h0 : ¬ ∃ L : Fin n → Fin m, ZeroBarrier Smooth L) :
    lnd n ≤ m := by
  by_cases hlarge : n ≤ m
  · have hl := lnd_le hn
    omega
  · have hmn : m < n := by omega
    apply Nat.le_of_not_gt
    intro hmlnd

    obtain ⟨L, bad, _hbad, hsmooth⟩ := h1
    have hn0 : 0 < n := by omega
    have hlndn : lnd n ≤ n - 1 := lnd_le hn
    have hmLast : m < n - 1 := by omega

    let x : Nat → Fin m :=
      fun t => L (cwPos hn0 (succFin bad) t)

    have hsmoothPath :
        ∀ t : Nat, t < n - 1 →
          Smooth (x t) (x (t + 1)) := by
      intro t ht
      have hne :=
        cwPos_after_bad_ne_bad_before_last hn0 bad t ht
      have hs :=
        hsmooth (cwPos hn0 (succFin bad) t) hne
      change
        Smooth
          (L (cwPos hn0 (succFin bad) t))
          (L (cwPos hn0 (succFin bad) (t + 1)))
      rw [cwPos_succ]
      exact hs

    let f : Fin (m + 1) → Fin m :=
      fun q => x q.val
    obtain ⟨i, j, hij, hfij⟩ := fin_repeat f
    have hxij : x i.val = x j.val := by
      simpa [f] using hfij

    let c := j.val - i.val
    have hcpos : 0 < c := by
      dsimp [c]
      omega
    have hjle : j.val ≤ m := by
      have hjlt := j.isLt
      omega
    have hclem : c ≤ m := by
      dsimp [c]
      omega
    have hclnd : c < lnd n := by
      omega
    have hcdvd : c ∣ n :=
      dvd_of_lt_lnd hcpos hclnd

    have hmodSucc (q : Fin n) :
        (succFin q).val % c =
          (q.val % c + 1) % c := by
      change ((q.val + 1) % n) % c =
        (q.val % c + 1) % c
      calc
        ((q.val + 1) % n) % c =
            (q.val + 1) % c :=
          Nat.mod_mod_of_dvd _ hcdvd
        _ = (q.val % c + 1) % c :=
          (mod_succ_eq q.val c).symm

    let L0 : Fin n → Fin m :=
      fun q => x (i.val + q.val % c)

    have hzero : ZeroBarrier Smooth L0 := by
      unfold ZeroBarrier
      intro q
      change
        Smooth
          (x (i.val + q.val % c))
          (x (i.val + (succFin q).val % c))
      rw [hmodSucc q]
      let r := q.val % c
      have hrlt : r < c := by
        dsimp [r]
        exact Nat.mod_lt _ hcpos
      change
        Smooth
          (x (i.val + r))
          (x (i.val + (r + 1) % c))
      by_cases hnext : r + 1 < c
      · have hmod :
            (r + 1) % c = r + 1 :=
          Nat.mod_eq_of_lt hnext
        rw [hmod]
        apply hsmoothPath
        dsimp [c] at hrlt
        omega
      · have hreq : r + 1 = c := by
          omega
        have hwrap :
            i.val + (r + 1) % c = i.val := by
          rw [hreq, Nat.mod_self, Nat.add_zero]
        rw [hwrap]
        have harg : i.val + r = j.val - 1 := by
          dsimp [c] at hreq
          omega
        rw [harg]
        have hs :=
          hsmoothPath (j.val - 1) (by omega)
        have hjstep : j.val - 1 + 1 = j.val := by
          omega
        rw [hjstep, ← hxij] at hs
        exact hs

    exact h0 ⟨L0, hzero⟩

end StaticBarrierStateBound

#print axioms StaticBarrierStateBound.lnd_pos
#print axioms StaticBarrierStateBound.not_dvd_lnd
#print axioms StaticBarrierStateBound.dvd_of_lt_lnd
#print axioms StaticBarrierStateBound.lnd_le
#print axioms StaticBarrierStateBound.static_barrier_state_bound

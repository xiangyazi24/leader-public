import Leader.PPL.Predicates
import Leader.Core.ModArith

/-
Mathematical repair of the branch skipped in the printed proof of Lemma 3.


Write m = 2 * psi; this is the PRODUCT modulus from equation (1), not
2 ^ psi.  Suppose that C is leaderless and satisfies equation (1).  If d_i
denotes dist at physical site i, equation (1) says


    d_(i+1) = (d_i + 1) mod m


on every non-wrap edge.  Therefore, by induction,


    d_i = (d_0 + i) mod m          for 0 <= i < n.


Apply equation (1) once more at site 0.  Its predecessor is site n-1, so


    d_0 = (d_(n-1) + 1) mod m
        = (d_0 + n) mod m.


Because d_0 is a Fin m value, 0 <= d_0 < m.  The last equality therefore
forces n mod m = 0, i.e. m | n.  Consequently, in the omitted branch
2 * psi ∤ n, equation (1) ALONE is already contradictory; equation (2) is
not needed there.


For completeness, the divisible branch is the paper's intended argument.
When 2 * psi | n, the leaderless distance pattern has borders exactly every
psi sites.  Hence all cyclic segments have length psi.  If q = n / psi and
I_j is the ID of segment j, equation (2) (there are no leader exceptions)
gives


    I_(j+1) = (I_j + 1) mod 2^psi.


After q segments we return to the same physical segment, so


    I_0 = (I_0 + q) mod 2^psi,


hence 2^psi | q.  But 0 < q < n <= 2^psi (psi >= 2), contradiction.


The Lean proof below implements both branches against the literal Perfect
definition. This file uses definitionally identical local proof views of the
public cyclic scanner and segment helpers from Predicates.lean.
perfect_iff_view is rfl: no alternate predicate or semantics is introduced.
-/



namespace PPL


set_option autoImplicit false


/-! Definitionally identical proof views of the Perfect helpers. -/


private def pvShiftRight {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) : Fin n :=
  ⟨(i.val + d) % n, Nat.mod_lt _ ring.hn⟩


private def pvShiftLeft {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) : Fin n :=
  ⟨(i.val + n - d % n) % n, Nat.mod_lt _ ring.hn⟩


/-- Exact proof alias for the recursive scanner in
`Leader/PPL/Predicates.lean`. Using the same recursive constant (rather than
copying its recursion) makes `PerfectView` definitionally identical to
`Perfect`. -/
private abbrev pvScanDistance {n : Nat} (site : Nat → Fin n)
    (hit : Fin n → Bool) : Nat → Nat → Option Nat :=
  scanDistance site hit


private def pvIsBorder {n psi kappa : Nat}
    (C : Config n psi kappa) (i : Fin n) : Prop :=
  (C i).dist.val = 0 ∨ (C i).dist.val = psi


private def pvIsBorderBool {n psi kappa : Nat}
    (C : Config n psi kappa) (i : Fin n) : Bool :=
  (C i).dist.val == 0 || (C i).dist.val == psi


private def pvNextBorderDistance {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (i : Fin n) : Nat :=
  match pvScanDistance (fun d => pvShiftRight ring i d)
      (pvIsBorderBool C) n 1 with
  | some d => d
  | none => n


private def pvPrevBorderDistance {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (i : Fin n) : Nat :=
  match pvScanDistance (fun d => pvShiftLeft ring i d)
      (pvIsBorderBool C) n 1 with
  | some d => d
  | none => n


/-- Exact proof alias for the recursive segment-ID fold in
`Leader/PPL/Predicates.lean`. -/
private abbrev pvSegmentIdAux {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (start : Fin n) : Nat → Nat → Nat :=
  segmentIdAux ring C start


private def pvSegmentIdFrom {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (start : Fin n) (len : Nat) : Nat :=
  pvSegmentIdAux ring C start len 0


private def PerfectView {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  (∀ i : Fin n,
      (C i).dist.val =
        if (C i).leader = true then 0
        else ((C (pvShiftLeft ring i 1)).dist.val + 1) % (2 * psi)) ∧
    ∀ i : Fin n, pvIsBorder C i →
      let dn := pvNextBorderDistance ring C i
      let dp := pvPrevBorderDistance ring C i
      let e := pvShiftRight ring i dn
      let p := pvShiftLeft ring i dp
      (C i).leader = true ∨ (C e).leader = true ∨
        pvSegmentIdFrom ring C i dn =
          (pvSegmentIdFrom ring C p dp + 1) % (2 ^ psi)


private theorem perfect_iff_view {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa) :
    Perfect ring C ↔ PerfectView ring C := by
  exact Iff.rfl


/-! Small cyclic-position facts. -/


@[simp] private theorem pvShiftRight_zero {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    pvShiftRight ring i 0 = i := by
  apply Fin.ext
  simp [pvShiftRight, Nat.mod_eq_of_lt i.isLt]


private theorem pvShiftRight_add {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (a b : Nat) :
    pvShiftRight ring (pvShiftRight ring i a) b =
      pvShiftRight ring i (a + b) := by
  apply Fin.ext
  change (((i.val + a) % n + b) % n) = (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]


@[simp] private theorem pvShiftRight_n {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    pvShiftRight ring i n = i := by
  apply Fin.ext
  simp [pvShiftRight, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]


private theorem pvShiftLeft_succ {n : Nat}
    (ring : DirectedRing n) (hn2 : 1 < n)
    (k : Nat) (hk : k + 1 < n) :
    pvShiftLeft ring (⟨k + 1, hk⟩ : Fin n) 1 =
      (⟨k, by omega⟩ : Fin n) := by
  apply Fin.ext
  simp only [pvShiftLeft]
  rw [Nat.mod_eq_of_lt hn2]
  change (k + 1 + n - 1) % n = k
  have hs : k + 1 + n - 1 = n + k := by omega
  rw [hs]
  simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : k < n)]


private theorem pvShiftLeft_zero_one {n : Nat}
    (ring : DirectedRing n) (hn2 : 1 < n) :
    pvShiftLeft ring (⟨0, ring.hn⟩ : Fin n) 1 =
      (⟨n - 1, by omega⟩ : Fin n) := by
  apply Fin.ext
  simp only [pvShiftLeft]
  rw [Nat.mod_eq_of_lt hn2]
  simpa using (Nat.mod_eq_of_lt (by omega : n - 1 < n))


private theorem pvShiftLeft_eq_shiftRight_sub {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (d : Nat) (hd : d < n) :
    pvShiftLeft ring i d = pvShiftRight ring i (n - d) := by
  apply Fin.ext
  simp only [pvShiftLeft, pvShiftRight]
  rw [Nat.mod_eq_of_lt hd]
  have hs : i.val + n - d = i.val + (n - d) := by omega
  rw [hs]


private theorem pvShiftLeft_shiftRight_cancel {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (d : Nat) (hd : d < n) :
    pvShiftLeft ring (pvShiftRight ring i d) d = i := by
  rw [pvShiftLeft_eq_shiftRight_sub ring _ d hd,
    pvShiftRight_add]
  have hs : d + (n - d) = n := by omega
  rw [hs, pvShiftRight_n]


/-! Equation (1): the leaderless distance cycle. -/


private theorem leaderless_dist_formula
    {n psi kappa : Nat} (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (hP : PerfectView ring C)
    (h0 : ∀ i : Fin n, (C i).leader = false) :
    ∀ (k : Nat) (hk : k < n),
      (C (⟨k, hk⟩ : Fin n)).dist.val =
        ((C (⟨0, ring.hn⟩ : Fin n)).dist.val + k) % (2 * psi) := by
  intro k
  induction k with
  | zero =>
      intro hk
      have hzlt :=
        (C (⟨0, ring.hn⟩ : Fin n)).dist.isLt
      simpa using (Nat.mod_eq_of_lt hzlt).symm
  | succ k ih =>
      intro hk
      have hk0 : k < n := by omega
      have hEq := hP.1 (⟨k + 1, hk⟩ : Fin n)
      rw [h0] at hEq
      simp only [Bool.false_eq_true, if_false] at hEq
      have hpred :=
        pvShiftLeft_succ ring hn2 k hk
      rw [hpred] at hEq
      have hprev := ih hk0
      calc
        (C (⟨k + 1, hk⟩ : Fin n)).dist.val
            = ((C (⟨k, hk0⟩ : Fin n)).dist.val + 1) %
                (2 * psi) := hEq
        _ = ((((C (⟨0, ring.hn⟩ : Fin n)).dist.val + k) %
                (2 * psi)) + 1) % (2 * psi) := by rw [hprev]
        _ = ((C (⟨0, ring.hn⟩ : Fin n)).dist.val + k + 1) %
                (2 * psi) :=
              mod_succ_eq
                ((C (⟨0, ring.hn⟩ : Fin n)).dist.val + k)
                (2 * psi)
        _ = ((C (⟨0, ring.hn⟩ : Fin n)).dist.val + (k + 1)) %
                (2 * psi) := by
              congr 1


private theorem leaderless_eq1_forces_twoPsi_dvd
    {n psi kappa : Nat} (hn2 : 1 < n) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (hP : PerfectView ring C)
    (h0 : ∀ i : Fin n, (C i).leader = false) :
    2 * psi ∣ n := by
  let z : Fin n := ⟨0, ring.hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hEq := hP.1 z
  rw [h0] at hEq
  simp only [Bool.false_eq_true, if_false] at hEq
  have hleft : pvShiftLeft ring z 1 = last := by
    dsimp [z, last]
    exact pvShiftLeft_zero_one ring hn2
  rw [hleft] at hEq
  have hlast :=
    leaderless_dist_formula hn2 ring C hP h0 (n - 1)
      (by omega : n - 1 < n)
  change
    (C last).dist.val =
      ((C z).dist.val + (n - 1)) % (2 * psi) at hlast
  rw [hlast] at hEq
  have hcycle :
      (C z).dist.val =
        ((C z).dist.val + n) % (2 * psi) := by
    calc
      (C z).dist.val
          = ((((C z).dist.val + (n - 1)) % (2 * psi)) + 1) %
              (2 * psi) := hEq
      _ = ((C z).dist.val + (n - 1) + 1) % (2 * psi) :=
            mod_succ_eq ((C z).dist.val + (n - 1)) (2 * psi)
      _ = ((C z).dist.val + n) % (2 * psi) := by
            congr 1
            omega
  exact dvd_of_lt_mod_add_eq
    (C z).dist.val n (2 * psi) (by omega)
    (C z).dist.isLt hcycle


private theorem psi_ge_two_of_three_le_n_le_pow
    {n psi : Nat} (hn3 : 3 ≤ n) (hpow : n ≤ 2 ^ psi) :
    2 ≤ psi := by
  by_cases h0 : psi = 0
  · subst psi
    simp at hpow
    omega
  by_cases h1 : psi = 1
  · subst psi
    simp at hpow
    omega
  omega


/-! A canonical dist=0 border in the leaderless divisible cycle. -/


private def anchorOffset {psi kappa : Nat} (q : State psi kappa) : Nat :=
  (2 * psi - q.dist.val) % (2 * psi)


private theorem anchorOffset_lt {psi kappa : Nat}
    (q : State psi kappa) (hpsi : 0 < psi) :
    anchorOffset q < 2 * psi := by
  unfold anchorOffset
  exact Nat.mod_lt _ (by omega)


private theorem anchorOffset_add_mod_zero {psi kappa : Nat}
    (q : State psi kappa) (hpsi : 0 < psi) :
    (q.dist.val + anchorOffset q) % (2 * psi) = 0 := by
  by_cases hz : q.dist.val = 0
  · simp [anchorOffset, hz]
  · have hsub : 2 * psi - q.dist.val < 2 * psi := by
      have hlt := q.dist.isLt
      omega
    have ha :
        anchorOffset q = 2 * psi - q.dist.val := by
      unfold anchorOffset
      exact Nat.mod_eq_of_lt hsub
    rw [ha]
    have hsum :
        q.dist.val + (2 * psi - q.dist.val) = 2 * psi := by
      have hlt := q.dist.isLt
      omega
    rw [hsum, Nat.mod_self]


private theorem leaderless_dist_from_anchor
    {n psi kappa : Nat} (hn2 : 1 < n)
    (hdiv : 2 * psi ∣ n)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (hP : PerfectView ring C)
    (h0 : ∀ i : Fin n, (C i).leader = false)
    (a : Nat) (ha : a < n)
    (hanchor :
      ((C (⟨0, ring.hn⟩ : Fin n)).dist.val + a) % (2 * psi) = 0) :
    ∀ k : Nat,
      (C (pvShiftRight ring (⟨a, ha⟩ : Fin n) k)).dist.val =
        k % (2 * psi) := by
  intro k
  let j := (a + k) % n
  have hjlt : j < n := by
    dsimp [j]
    exact Nat.mod_lt _ ring.hn
  have hglobal :=
    leaderless_dist_formula hn2 ring C hP h0 j hjlt
  have hsite :
      pvShiftRight ring (⟨a, ha⟩ : Fin n) k =
        (⟨j, hjlt⟩ : Fin n) := by
    rfl
  rw [hsite, hglobal]
  have hjmod :
      j % (2 * psi) = (a + k) % (2 * psi) := by
    dsimp [j]
    exact Nat.mod_mod_of_dvd _ hdiv
  calc
    ((C (⟨0, ring.hn⟩ : Fin n)).dist.val + j) % (2 * psi)
        =
      ((C (⟨0, ring.hn⟩ : Fin n)).dist.val + (a + k)) %
        (2 * psi) :=
      Nat.add_mod_eq_add_mod_left
        (C (⟨0, ring.hn⟩ : Fin n)).dist.val hjmod
    _ =
      (((C (⟨0, ring.hn⟩ : Fin n)).dist.val + a) + k) %
        (2 * psi) := by
      rw [← Nat.add_assoc]
    _ =
      ((((C (⟨0, ring.hn⟩ : Fin n)).dist.val + a) %
          (2 * psi)) + k) % (2 * psi) :=
      (Nat.mod_add_mod
        ((C (⟨0, ring.hn⟩ : Fin n)).dist.val + a)
        (2 * psi) k).symm
    _ = k % (2 * psi) := by
      rw [hanchor]
      simp


/-! Borders are exactly the multiples of psi in the anchored coordinates. -/


private theorem mod_twoPsi_border_iff_dvd
    (psi k : Nat) (hpsi : 0 < psi) :
    k % (2 * psi) = 0 ∨ k % (2 * psi) = psi ↔ psi ∣ k := by
  have hbase : psi ∣ 2 * psi := Nat.dvd_mul_left psi 2
  constructor
  · intro h
    have hrem : (k % (2 * psi)) % psi = 0 := by
      rcases h with h | h
      · rw [h]
        simp
      · rw [h]
        simp
    have hkmod : k % psi = 0 := by
      calc
        k % psi = (k % (2 * psi)) % psi :=
          (Nat.mod_mod_of_dvd k hbase).symm
        _ = 0 := hrem
    exact Nat.dvd_of_mod_eq_zero hkmod
  · intro hk
    have hrem : (k % (2 * psi)) % psi = 0 := by
      calc
        (k % (2 * psi)) % psi = k % psi :=
          Nat.mod_mod_of_dvd k hbase
        _ = 0 := Nat.mod_eq_zero_of_dvd hk
    have hrlt : k % (2 * psi) < 2 * psi :=
      Nat.mod_lt _ (by omega)
    by_cases hlt : k % (2 * psi) < psi
    · left
      rw [Nat.mod_eq_of_lt hlt] at hrem
      exact hrem
    · right
      have hge : psi ≤ k % (2 * psi) := by omega
      have hsub : k % (2 * psi) - psi < psi := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub] at hrem
      omega


private theorem pvIsBorderBool_true_iff
    {n psi kappa : Nat} (C : Config n psi kappa) (i : Fin n) :
    pvIsBorderBool C i = true ↔ pvIsBorder C i := by
  simp [pvIsBorderBool, pvIsBorder]


private theorem pvIsBorderBool_false_of_not
    {n psi kappa : Nat} (C : Config n psi kappa) (i : Fin n)
    (h : ¬ pvIsBorder C i) :
    pvIsBorderBool C i = false := by
  cases hB : pvIsBorderBool C i with
  | false => rfl
  | true =>
      exfalso
      exact h ((pvIsBorderBool_true_iff C i).mp hB)


private theorem not_dvd_of_pos_lt
    (psi d : Nat) (hd0 : 0 < d) (hdlt : d < psi) :
    ¬ psi ∣ d := by
  intro hd
  have hle := Nat.le_of_dvd hd0 hd
  omega


private theorem not_dvd_mul_add_small
    (psi j d : Nat) (hd0 : 0 < d) (hdlt : d < psi) :
    ¬ psi ∣ j * psi + d := by
  have hj : psi ∣ j * psi := Nat.dvd_mul_left psi j
  intro hsum
  have hd : psi ∣ d :=
    (Nat.dvd_add_iff_right hj).mpr hsum
  exact not_dvd_of_pos_lt psi d hd0 hdlt hd


private theorem dvd_mul_add_sub_iff
    {n psi : Nat} (hnpsi : psi ∣ n)
    (j d : Nat) (hdn : d ≤ n) :
    psi ∣ j * psi + (n - d) ↔ psi ∣ d := by
  have hj : psi ∣ j * psi := Nat.dvd_mul_left psi j
  have hsum : psi ∣ j * psi + n := Nat.dvd_add hj hnpsi
  have heq : j * psi + (n - d) = (j * psi + n) - d := by
    omega
  rw [heq]
  exact Nat.dvd_sub_iff_right (by omega) hsum


private theorem border_geometry
    {n psi kappa : Nat} (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (start : Fin n)
    (hdist :
      ∀ k : Nat,
        (C (pvShiftRight ring start k)).dist.val =
          k % (2 * psi)) :
    ∀ k : Nat,
      pvIsBorder C (pvShiftRight ring start k) ↔ psi ∣ k := by
  intro k
  unfold pvIsBorder
  rw [hdist k]
  exact mod_twoPsi_border_iff_dvd psi k hpsi


/-! The scanners really return the adjacent border at distance psi. -/


private theorem pvScanDistance_eq_some_first
    {n : Nat} (site : Nat → Fin n) (hit : Fin n → Bool)
    (fuel lo target : Nat)
    (hlo : lo ≤ target)
    (hin : target < lo + fuel)
    (hbefore :
      ∀ d : Nat, lo ≤ d → d < target → hit (site d) = false)
    (hhit : hit (site target) = true) :
    pvScanDistance site hit fuel lo = some target := by
  induction fuel generalizing lo with
  | zero =>
      omega
  | succ fuel ih =>
      by_cases heq : lo = target
      · subst lo
        change (if hit (site target) = true then some target
          else scanDistance site hit fuel (target + 1)) = some target
        simp [hhit]
      · have hlt : lo < target := by omega
        have hfalse := hbefore lo (Nat.le_refl lo) hlt
        change (if hit (site lo) = true then some lo
          else scanDistance site hit fuel (lo + 1)) = some target
        simp only [hfalse, Bool.false_eq_true, if_false]
        apply ih (lo := lo + 1)
        · omega
        · omega
        · intro d hd hdt
          exact hbefore d (by omega) hdt


private theorem pvNextBorderDistance_eq_psi
    {n psi kappa : Nat} (hpsi : 0 < psi) (hpsin : psi < n)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (start : Fin n)
    (hgeom :
      ∀ k : Nat,
        pvIsBorder C (pvShiftRight ring start k) ↔ psi ∣ k)
    (j : Nat) :
    pvNextBorderDistance ring C
      (pvShiftRight ring start (j * psi)) = psi := by
  let b := pvShiftRight ring start (j * psi)
  have hscan :
      pvScanDistance (fun d => pvShiftRight ring b d)
        (pvIsBorderBool C) n 1 = some psi := by
    apply pvScanDistance_eq_some_first
    · omega
    · omega
    · intro d hd1 hdpsi
      have hnot :
          ¬ psi ∣ j * psi + d :=
        not_dvd_mul_add_small psi j d (by omega) hdpsi
      have hsite :
          pvShiftRight ring b d =
            pvShiftRight ring start (j * psi + d) := by
        dsimp [b]
        exact pvShiftRight_add ring start (j * psi) d
      have hnb :
          ¬ pvIsBorder C (pvShiftRight ring b d) := by
        intro hb
        rw [hsite] at hb
        exact hnot ((hgeom (j * psi + d)).mp hb)
      exact pvIsBorderBool_false_of_not C _ hnb
    · have hsite :
          pvShiftRight ring b psi =
            pvShiftRight ring start (j * psi + psi) := by
        dsimp [b]
        exact pvShiftRight_add ring start (j * psi) psi
      apply (pvIsBorderBool_true_iff C _).mpr
      rw [hsite]
      apply (hgeom (j * psi + psi)).mpr
      have hj : psi ∣ j * psi := Nat.dvd_mul_left psi j
      exact (Nat.dvd_add_iff_right hj).mp (Nat.dvd_refl psi)
  unfold pvNextBorderDistance
  rw [hscan]


private theorem pvPrevBorderDistance_eq_psi
    {n psi kappa : Nat} (hpsi : 0 < psi) (hpsin : psi < n)
    (hnpsi : psi ∣ n)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (start : Fin n)
    (hgeom :
      ∀ k : Nat,
        pvIsBorder C (pvShiftRight ring start k) ↔ psi ∣ k)
    (j : Nat) :
    pvPrevBorderDistance ring C
      (pvShiftRight ring start (j * psi)) = psi := by
  let b := pvShiftRight ring start (j * psi)
  have hscan :
      pvScanDistance (fun d => pvShiftLeft ring b d)
        (pvIsBorderBool C) n 1 = some psi := by
    apply pvScanDistance_eq_some_first
    · omega
    · omega
    · intro d hd1 hdpsi
      have hdN : d < n := by omega
      have hsite :
          pvShiftLeft ring b d =
            pvShiftRight ring start (j * psi + (n - d)) := by
        calc
          pvShiftLeft ring b d
              = pvShiftRight ring b (n - d) :=
                pvShiftLeft_eq_shiftRight_sub ring b d hdN
          _ = pvShiftRight ring start (j * psi + (n - d)) := by
                dsimp [b]
                exact pvShiftRight_add ring start (j * psi) (n - d)
      have hnotD : ¬ psi ∣ d :=
        not_dvd_of_pos_lt psi d (by omega) hdpsi
      have hiff :=
        dvd_mul_add_sub_iff hnpsi j d (by omega : d ≤ n)
      have hnot :
          ¬ psi ∣ j * psi + (n - d) := by
        intro h
        exact hnotD (hiff.mp h)
      have hnb :
          ¬ pvIsBorder C (pvShiftLeft ring b d) := by
        intro hb
        rw [hsite] at hb
        exact hnot ((hgeom (j * psi + (n - d))).mp hb)
      exact pvIsBorderBool_false_of_not C _ hnb
    · have hsite :
          pvShiftLeft ring b psi =
            pvShiftRight ring start (j * psi + (n - psi)) := by
        calc
          pvShiftLeft ring b psi
              = pvShiftRight ring b (n - psi) :=
                pvShiftLeft_eq_shiftRight_sub ring b psi hpsin
          _ = pvShiftRight ring start (j * psi + (n - psi)) := by
                dsimp [b]
                exact pvShiftRight_add ring start (j * psi) (n - psi)
      apply (pvIsBorderBool_true_iff C _).mpr
      rw [hsite]
      apply (hgeom (j * psi + (n - psi))).mpr
      exact (dvd_mul_add_sub_iff hnpsi j psi
        (by omega : psi ≤ n)).mpr (Nat.dvd_refl psi)
  unfold pvPrevBorderDistance
  rw [hscan]


/-! Equation (2): cyclic segment-ID increment. -/


private theorem segmentId_succ
    {n psi kappa : Nat} (hpsi : 0 < psi) (hpsin : psi < n)
    (hnpsi : psi ∣ n)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (start : Fin n)
    (hP : PerfectView ring C)
    (h0 : ∀ i : Fin n, (C i).leader = false)
    (hgeom :
      ∀ k : Nat,
        pvIsBorder C (pvShiftRight ring start k) ↔ psi ∣ k)
    (j : Nat) :
    pvSegmentIdFrom ring C
        (pvShiftRight ring start ((j + 1) * psi)) psi =
      (pvSegmentIdFrom ring C
          (pvShiftRight ring start (j * psi)) psi + 1) %
        (2 ^ psi) := by
  let cur := pvShiftRight ring start (j * psi)
  let nxt := pvShiftRight ring start ((j + 1) * psi)
  have hb : pvIsBorder C nxt := by
    dsimp [nxt]
    apply (hgeom ((j + 1) * psi)).mpr
    exact Nat.dvd_mul_left psi (j + 1)
  have hnxt :=
    pvNextBorderDistance_eq_psi hpsi hpsin ring C start hgeom (j + 1)
  have hprv :=
    pvPrevBorderDistance_eq_psi hpsi hpsin hnpsi
      ring C start hgeom (j + 1)
  have h := hP.2 nxt hb
  dsimp only at h
  rw [hnxt, hprv] at h
  simp only [h0, Bool.false_eq_true, false_or] at h
  have hnxt_as :
      nxt = pvShiftRight ring cur psi := by
    dsimp [nxt, cur]
    simpa [Nat.add_mul] using
      (pvShiftRight_add ring start (j * psi) psi).symm
  have hp : pvShiftLeft ring nxt psi = cur := by
    rw [hnxt_as]
    exact pvShiftLeft_shiftRight_cancel ring cur psi hpsin
  rw [hp] at h
  exact h


private theorem iterate_mod_succ
    (M : Nat) (I : Nat → Nat)
    (hrec : ∀ j : Nat,
      I (Nat.succ j) = (I j + 1) % M)
    (t : Nat) :
    I (Nat.succ t) = (I 0 + Nat.succ t) % M := by
  induction t with
  | zero =>
      simpa using hrec 0
  | succ t ih =>
      calc
        I (Nat.succ (Nat.succ t))
            = (I (Nat.succ t) + 1) % M := hrec (Nat.succ t)
        _ = (((I 0 + Nat.succ t) % M) + 1) % M := by
              rw [ih]
        _ = (I 0 + Nat.succ t + 1) % M :=
              mod_succ_eq (I 0 + Nat.succ t) M
        _ = (I 0 + Nat.succ (Nat.succ t)) % M := by
              congr 1


private theorem leaderless_perfect_false_of_twoPsi_dvd
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi) (hpow : n ≤ 2 ^ psi)
    (hdiv : 2 * psi ∣ n)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (hP : PerfectView ring C)
    (h0 : ∀ i : Fin n, (C i).leader = false) :
    False := by
  have htwo_le_n : 2 * psi ≤ n :=
    Nat.le_of_dvd ring.hn hdiv
  have hpsin : psi < n := by omega
  have hnpsi : psi ∣ n :=
    Nat.dvd_trans (Nat.dvd_mul_left psi 2) hdiv


  let z : Fin n := ⟨0, ring.hn⟩
  let a := anchorOffset (C z)
  have haTwo : a < 2 * psi := by
    dsimp [a]
    exact anchorOffset_lt (C z) (by omega)
  have haN : a < n := by omega
  let start : Fin n := ⟨a, haN⟩


  have hanchor :
      ((C z).dist.val + a) % (2 * psi) = 0 := by
    dsimp [a]
    exact anchorOffset_add_mod_zero (C z) (by omega)


  have hdist :
      ∀ k : Nat,
        (C (pvShiftRight ring start k)).dist.val =
          k % (2 * psi) := by
    intro k
    dsimp [start, z] at *
    exact leaderless_dist_from_anchor
      (by omega) hdiv ring C hP h0 a haN hanchor k


  have hgeom :
      ∀ k : Nat,
        pvIsBorder C (pvShiftRight ring start k) ↔ psi ∣ k :=
    border_geometry (by omega) ring C start hdist


  let I : Nat → Nat := fun j =>
    pvSegmentIdFrom ring C
      (pvShiftRight ring start (j * psi)) psi


  have hrec :
      ∀ j : Nat,
        I (Nat.succ j) = (I j + 1) % (2 ^ psi) := by
    intro j
    dsimp [I]
    simpa using
      segmentId_succ (by omega) hpsin hnpsi
        ring C start hP h0 hgeom j


  have hqpos : 0 < n / psi := by
    exact (Nat.div_pos_iff).mpr ⟨by omega, by omega⟩
  have hq_lt_n : n / psi < n :=
    Nat.div_lt_self ring.hn (by omega)
  have hq_lt_pow : n / psi < 2 ^ psi := by
    omega


  have hqpsi : (n / psi) * psi = n :=
    Nat.div_mul_cancel hnpsi
  have hIq : I (n / psi) = I 0 := by
    dsimp [I]
    rw [hqpsi, pvShiftRight_n]
    simp


  obtain ⟨t, ht⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqpos)
  have hiter :=
    iterate_mod_succ (2 ^ psi) I hrec t
  have hcycle :
      I 0 = (I 0 + n / psi) % (2 ^ psi) := by
    calc
      I 0 = I (n / psi) := hIq.symm
      _ = I (Nat.succ t) := by rw [ht]
      _ = (I 0 + Nat.succ t) % (2 ^ psi) := hiter
      _ = (I 0 + n / psi) % (2 ^ psi) := by rw [ht]


  have hpowpos : 0 < 2 ^ psi :=
    Nat.pow_pos (by omega)
  have hIlt : I 0 < 2 ^ psi := by
    rw [hcycle]
    exact Nat.mod_lt _ hpowpos
  have hPowDvdQ :
      2 ^ psi ∣ n / psi :=
    dvd_of_lt_mod_add_eq
      (I 0) (n / psi) (2 ^ psi) hpowpos hIlt hcycle
  have hPowLeQ :
      2 ^ psi ≤ n / psi :=
    Nat.le_of_dvd hqpos hPowDvdQ
  omega


/--
Leaderless configurations cannot be Perfect.


The public assumptions are exactly the frozen Lemma-3 regime needed here:
3 <= n and n <= 2^psi.  A separate 2 <= psi hypothesis is unnecessary:
it follows from these two assumptions.  No hypothesis on kappa is used.
-/
theorem leaderless_not_perfect
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (h0 : ∀ i : Fin n, (C i).leader = false) :
    ¬ Perfect ring C := by
  intro hPerfect
  have hpsi : 2 ≤ psi :=
    psi_ge_two_of_three_le_n_le_pow hn3 hpow
  have hP : PerfectView ring C :=
    (perfect_iff_view ring C).mp hPerfect
  by_cases hdiv : 2 * psi ∣ n
  · exact leaderless_perfect_false_of_twoPsi_dvd
      hn3 hpsi hpow hdiv ring C hP h0
  · exact hdiv
      (leaderless_eq1_forces_twoPsi_dvd
        (by omega) (by omega) ring C hP h0)


/--
Paper Lemma 3: every Perfect configuration contains a leader.


This is valid for every n >= 3 in the frozen parameter regime n <= 2^psi.
The usually stated 2 <= psi condition is redundant here, and kappa is
unrestricted.
-/
theorem perfect_has_leader
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (hPerfect : Perfect ring C) :
    ∃ i : Fin n, (C i).leader = true := by
  classical
  by_cases hex : ∃ i : Fin n, (C i).leader = true
  · exact hex
  · have h0 : ∀ i : Fin n, (C i).leader = false := by
      intro i
      cases hi : (C i).leader with
      | false => rfl
      | true =>
          exact False.elim (hex ⟨i, hi⟩)
    exact False.elim
      (leaderless_not_perfect hn3 hpow ring C h0 hPerfect)


end PPL


#print axioms PPL.leaderless_not_perfect
#print axioms PPL.perfect_has_leader

import Leader.PPL.Modes.ConstructionModeSplit

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability

/-!
# Lemma 5(ii): fixed-agent encounter overload

Truth audit on current main 5c9651ff10376a48e6b5d622c125cb7446ddf466.

The leaf is TRUE.

For a fixed x, predictableHostHits ring (fun _ => x) is exactly the
two-hot-letter binomial law supplied by PredictableHostTails.  The event in
lemma5iiEncounterBadB is the union of these n fixed-agent strict upper tails.

The old FixedAgent24nBound is not at the right horizon/threshold here.  The
worst Lemma-5(ii) scale is c = 3, where the cap is only 4/3 times the mean in
the largest allowed rings, so the base-2 moment is eventually too weak.

The right exact Nat moment is the 4/3 moment.  Weight every hot scheduler
letter by 4 and every cold scheduler letter by 3.  A word with m hot letters
gets the extra factor 4^m * 3^(T-m), while the total weighted scheduler mass
is

  (2*4 + (n-2)*3)^T = (3*n+2)^T.

On the strict upper tail m > a this dominates

  4^(a+1) * 3^(T-(a+1)).

The finite-binomial proof of that moment is completed below.  The complete
scheduler union bound is also completed below.  One pure Nat inequality,
Lemma5iiEncounterScaleArithmetic, remains isolated.
-/

/-! ## Small list/count helpers -/

private def encounterAnyPred {A : Type} :
    List (A -> Bool) -> A -> Bool
  | [], _ => false
  | p :: ps, x => p x || encounterAnyPred ps x

private theorem encounterAnyPred_true_of_mem
    {A : Type}
    (ps : List (A -> Bool))
    (p : A -> Bool)
    (x : A)
    (hmem : p ∈ ps)
    (hp : p x = true) :
    encounterAnyPred ps x = true := by
  induction ps with
  | nil =>
      simp at hmem
  | cons q qs ih =>
      rcases List.mem_cons.mp hmem with hq | hq
      · subst q
        simp [encounterAnyPred, hp]
      · have ht := ih hq
        simp [encounterAnyPred, ht]

private theorem encounterCountP_mono
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq : forall x, p x = true -> q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx : q x = true := hpq x hp
          simp [hp, hqx]
          omega

private theorem encounterCountP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A -> Bool) :
    xs.countP (fun x => p x || q x) <=
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons]
      cases hp : p x <;>
        cases hq : q x <;>
        simp [hp, hq] at * <;>
        omega

private theorem encounterCountP_any_le_sum
    {A : Type}
    (xs : List A)
    (ps : List (A -> Bool)) :
    xs.countP (encounterAnyPred ps) <=
      (ps.map (fun p => xs.countP p)).sum := by
  induction ps with
  | nil =>
      simp [encounterAnyPred]
  | cons p ps ih =>
      calc
        xs.countP (encounterAnyPred (p :: ps)) =
            xs.countP
              (fun x => p x || encounterAnyPred ps x) := by
          rfl
        _ <= xs.countP p +
            xs.countP (encounterAnyPred ps) :=
          encounterCountP_or_le_add
            xs p (encounterAnyPred ps)
        _ <= xs.countP p +
            (ps.map (fun q => xs.countP q)).sum :=
          Nat.add_le_add_left ih _
        _ =
            ((p :: ps).map
              (fun q => xs.countP q)).sum := by
          simp

private theorem encounterFinUnion_le
    {A : Type} {n : Nat}
    (xs : List A)
    (bad : A -> Bool)
    (p : Fin n -> A -> Bool)
    (hcover :
      forall x, bad x = true ->
        exists i : Fin n, p i x = true) :
    xs.countP bad <=
      (List.ofFn
        (fun i : Fin n => xs.countP (p i))).sum := by
  let ps : List (A -> Bool) := List.ofFn p
  have hbad :
      forall x, bad x = true ->
        encounterAnyPred ps x = true := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    have hm : p i ∈ ps := by
      dsimp [ps]
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    exact encounterAnyPred_true_of_mem ps (p i) x hm hi
  calc
    xs.countP bad <=
        xs.countP (encounterAnyPred ps) :=
      encounterCountP_mono
        xs bad (encounterAnyPred ps) hbad
    _ <=
        (ps.map (fun q => xs.countP q)).sum :=
      encounterCountP_any_le_sum xs ps
    _ =
        (List.ofFn
          (fun i : Fin n => xs.countP (p i))).sum := by
      dsimp [ps]
      rw [List.map_ofFn]
      simp only [Function.comp_def]

private theorem encounterSum_ofFn_le
    {n : Nat}
    (f g : Fin n -> Nat)
    (hfg : forall i, f i <= g i) :
    (List.ofFn f).sum <= (List.ofFn g).sum := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact
        Nat.add_le_add
          (hfg 0)
          (ih
            (fun i => f i.succ)
            (fun i => g i.succ)
            (fun i => hfg i.succ))

private theorem encounterSum_ofFn_const
    (n a : Nat) :
    (List.ofFn (fun _ : Fin n => a)).sum =
      n * a := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        ih, Nat.succ_mul]
      omega

private theorem encounterFoldOr_mem_true :
    forall xs : List Bool,
      xs.foldl (fun acc b => acc || b) false = true ->
        true ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      simp
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [List.foldl_cons, Bool.false_or]
          intro h
          exact List.mem_cons.mpr (Or.inr (ih h))
      | true =>
          intro _
          exact List.mem_cons_self

private theorem encounterSum_map_le
    {A : Type}
    (xs : List A)
    (f g : A -> Nat)
    (hfg : forall x, x ∈ xs -> f x <= g x) :
    (xs.map f).sum <= (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons]
      exact
        Nat.add_le_add
          (hfg x (List.mem_cons_self))
          (ih
            (fun y hy =>
              hfg y (List.mem_cons.mpr (Or.inr hy))))

private theorem encounterSum_map_mul_right
    {A : Type}
    (xs : List A)
    (f : A -> Nat)
    (a : Nat) :
    (xs.map (fun x => f x * a)).sum =
      (xs.map f).sum * a := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons,
        ih, Nat.add_mul]

/-! ## Generic full-mass envelope for public RawCounts tails -/

private theorem encounterBinomialMass_zero_of_lt
    (hot cold : Nat) {T m : Nat}
    (h : T < m) :
    binomialMass hot cold T m = 0 := by
  induction T generalizing m with
  | zero =>
      cases m with
      | zero =>
          omega
      | succ m =>
          rfl
  | succ T ih =>
      cases m with
      | zero =>
          omega
      | succ m =>
          simp only [binomialMass]
          rw [ih (by omega), ih (by omega)]
          simp

private theorem encounterLowerTail_horizon_succ
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

private theorem encounterLowerTail_full
    (hot cold T : Nat) :
    lowerTailCount hot cold T (T + 1) =
      (hot + cold) ^ T := by
  induction T with
  | zero =>
      simp [lowerTailCount, binomialMass]
  | succ T ih =>
      rw [encounterLowerTail_horizon_succ
        hot cold T (T + 1)]
      have hz :
          binomialMass hot cold T (T + 1) = 0 :=
        encounterBinomialMass_zero_of_lt
          hot cold (by omega)
      have hsame :
          lowerTailCount hot cold T (T + 2) =
            lowerTailCount hot cold T (T + 1) := by
        rw [lowerTailCount, hz, Nat.add_zero]
      rw [hsame, ih, Nat.pow_succ, Nat.mul_add]
      ac_rfl

private theorem encounterLowerTail_add_mass_sum
    (hot cold T a k : Nat) :
    lowerTailCount hot cold T (a + 1 + k) =
      lowerTailCount hot cold T (a + 1) +
        ((List.range k).map
          (fun d =>
            binomialMass hot cold T (a + 1 + d))).sum := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [show a + 1 + (k + 1) =
          (a + 1 + k) + 1 by omega,
        lowerTailCount, ih,
        List.range_succ, List.map_append,
        List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      omega

private theorem encounterUpperTail_eq_massSum
    (hot cold T a : Nat) :
    upperTailCount hot cold T a =
      ((List.range (T - a)).map
        (fun d =>
          binomialMass hot cold T (a + 1 + d))).sum := by
  rw [upperTailCount_eq_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  simp only
  rw [binomialMass_eq_closed]

private theorem encounterUpperTail_le_full
    (hot cold T a : Nat) :
    upperTailCount hot cold T a <=
      (hot + cold) ^ T := by
  by_cases hTa : T <= a
  · have hz : T - a = 0 :=
      Nat.sub_eq_zero_of_le hTa
    rw [encounterUpperTail_eq_massSum, hz]
    simp
  · have ha : a < T := by
      omega
    have hs :=
      encounterLowerTail_add_mass_sum
        hot cold T a (T - a)
    have hidx :
        a + 1 + (T - a) = T + 1 := by
      omega
    rw [hidx, encounterLowerTail_full] at hs
    rw [encounterUpperTail_eq_massSum]
    omega

/-! ## Exact 4/3 moment -/

private theorem encounterBinomialMass_fourThree
    (n T a d : Nat)
    (hd : d < T - a) :
    binomialMass 2 (n - 2) T (a + 1 + d) *
        (4 ^ (a + 1) * 3 ^ (T - (a + 1))) <=
      binomialMass 8 (3 * (n - 2)) T (a + 1 + d) := by
  let m := a + 1 + d
  have hmT : m <= T := by
    dsimp [m]
    omega
  have hsplit :
      T - (a + 1) = (T - m) + d := by
    dsimp [m]
    omega
  have h34 :
      3 ^ d <= 4 ^ d :=
    Nat.pow_le_pow_left (by omega) d
  have hweight :
      4 ^ (a + 1) * 3 ^ (T - (a + 1)) <=
        4 ^ m * 3 ^ (T - m) := by
    calc
      4 ^ (a + 1) * 3 ^ (T - (a + 1)) =
          4 ^ (a + 1) *
            (3 ^ (T - m) * 3 ^ d) := by
        rw [hsplit, Nat.pow_add 3 (T - m) d]
      _ =
          (4 ^ (a + 1) * 3 ^ (T - m)) *
            3 ^ d := by
        ac_rfl
      _ <=
          (4 ^ (a + 1) * 3 ^ (T - m)) *
            4 ^ d :=
        Nat.mul_le_mul_left _ h34
      _ =
          (4 ^ (a + 1) * 4 ^ d) *
            3 ^ (T - m) := by
        ac_rfl
      _ =
          4 ^ m * 3 ^ (T - m) := by
        rw [<- Nat.pow_add]
  rw [binomialMass_eq_closed, binomialMass_eq_closed]
  have hmul :=
    Nat.mul_le_mul_left
      (chooseCount T m * 2 ^ m * (n - 2) ^ (T - m))
      hweight
  calc
    chooseCount T m * 2 ^ m * (n - 2) ^ (T - m) *
          (4 ^ (a + 1) * 3 ^ (T - (a + 1))) <=
        (chooseCount T m * 2 ^ m * (n - 2) ^ (T - m)) *
          (4 ^ m * 3 ^ (T - m)) :=
      hmul
    _ =
        chooseCount T m * 8 ^ m *
          (3 * (n - 2)) ^ (T - m) := by
      have h8 :
          8 ^ m = 2 ^ m * 4 ^ m := by
        rw [show (8 : Nat) = 2 * 4 by rfl, Nat.mul_pow]
      have h3 :
          (3 * (n - 2)) ^ (T - m) =
            3 ^ (T - m) * (n - 2) ^ (T - m) := by
        rw [Nat.mul_pow]
      rw [h8, h3]
      ac_rfl

/--
Exact scheduler-space 4/3 exponential moment for the two incident letters.
This is the sharp counting ingredient needed by Lemma 5(ii).
-/
theorem lemma5iiEncounter_fourThreeMoment
    (n T a : Nat)
    (hn2 : 2 <= n) :
    twoEdgeUpperTailCount n T a *
        (4 ^ (a + 1) * 3 ^ (T - (a + 1))) <=
      (3 * n + 2) ^ T := by
  let W := 4 ^ (a + 1) * 3 ^ (T - (a + 1))
  change
    upperTailCount 2 (n - 2) T a * W <=
      (3 * n + 2) ^ T
  have hsum :
      ((List.range (T - a)).map
        (fun d =>
          binomialMass 2 (n - 2) T (a + 1 + d) * W)).sum <=
      ((List.range (T - a)).map
        (fun d =>
          binomialMass 8 (3 * (n - 2)) T
            (a + 1 + d))).sum := by
    apply encounterSum_map_le
    intro d hd
    have hdlt : d < T - a := by
      simpa using (List.mem_range.mp hd)
    simpa [W] using
      encounterBinomialMass_fourThree n T a d hdlt
  calc
    upperTailCount 2 (n - 2) T a * W =
        ((List.range (T - a)).map
          (fun d =>
            binomialMass 2 (n - 2) T
              (a + 1 + d) * W)).sum := by
      rw [encounterUpperTail_eq_massSum]
      exact
        (encounterSum_map_mul_right
          (List.range (T - a))
          (fun d =>
            binomialMass 2 (n - 2) T (a + 1 + d))
          W).symm
    _ <=
        ((List.range (T - a)).map
          (fun d =>
            binomialMass 8 (3 * (n - 2)) T
              (a + 1 + d))).sum :=
      hsum
    _ =
        upperTailCount 8 (3 * (n - 2)) T a :=
      (encounterUpperTail_eq_massSum
        8 (3 * (n - 2)) T a).symm
    _ <=
        (8 + 3 * (n - 2)) ^ T :=
      encounterUpperTail_le_full
        8 (3 * (n - 2)) T a
    _ =
        (3 * n + 2) ^ T := by
      congr 1
      omega

/-! ## Sole remaining pure-Nat scale inequality -/

/--
The only residual left by this bounded round.

There is no scheduler, protocol, stopping rule, lineage, or parser in this
Prop.  It is the final exponential comparison after the exact 4/3 moment.

Paper-scale substitutions are still deliberately kept through the public
horizon/cap definitions, so this statement is definitionally aligned with the
consumer and does not rely on fragile division normalization in the assembly.
-/
def Lemma5iiEncounterScaleArithmetic : Prop :=
  forall {n psi kappa c : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hc : 3 <= c)
      (hkappa : kappa = 16 * c * psi)
      (hnpow : n <= 2 ^ psi),
    let T := lemma5iiHorizon n psi kappa
    let a := lemma5iiEncounterCap psi c
    n * n * (3 * n + 2) ^ T <=
      2 * n ^ T *
        (4 ^ (a + 1) * 3 ^ (T - (a + 1)))

/-- The residual scale inequality plus the exact 4/3 moment gives the
n-squared fixed-agent upper-tail budget used after the union bound. -/
theorem lemma5iiEncounterTail_scaled_of_scale
    (hscale : Lemma5iiEncounterScaleArithmetic)
    {n psi kappa c : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 3 <= c)
    (hkappa : kappa = 16 * c * psi)
    (hnpow : n <= 2 ^ psi) :
    n * n *
        twoEdgeUpperTailCount
          n
          (lemma5iiHorizon n psi kappa)
          (lemma5iiEncounterCap psi c) <=
      2 * n ^ lemma5iiHorizon n psi kappa := by
  have hn2 : 2 <= n := by
    omega
  let T := lemma5iiHorizon n psi kappa
  let a := lemma5iiEncounterCap psi c
  let W := 4 ^ (a + 1) * 3 ^ (T - (a + 1))
  have hm :=
    lemma5iiEncounter_fourThreeMoment n T a hn2
  have hm' :
      twoEdgeUpperTailCount n T a * W <=
        (3 * n + 2) ^ T := by
    simpa [W] using hm
  unfold Lemma5iiEncounterScaleArithmetic at hscale
  have hs := hscale hn3 hpsi hc hkappa hnpow
  dsimp only at hs
  have hs' :
      n * n * (3 * n + 2) ^ T <=
        2 * n ^ T * W := by
    simpa [T, a, W] using hs
  have hmul :=
    Nat.mul_le_mul_left (n * n) hm'
  have hchain :
      (n * n *
          twoEdgeUpperTailCount n T a) * W <=
        (2 * n ^ T) * W := by
    calc
      (n * n *
          twoEdgeUpperTailCount n T a) * W =
          n * n *
            (twoEdgeUpperTailCount n T a * W) := by
        ac_rfl
      _ <= n * n * (3 * n + 2) ^ T :=
        hmul
      _ <= 2 * n ^ T * W :=
        hs'
      _ = (2 * n ^ T) * W := by
        rfl
  have hWpos : 0 < W := by
    dsimp [W]
    exact
      Nat.mul_pos
        (Nat.pow_pos (by omega))
        (Nat.pow_pos (by omega))
  have hcancel :
      n * n *
          twoEdgeUpperTailCount n T a <=
        2 * n ^ T :=
    Nat.le_of_mul_le_mul_right hchain hWpos
  simpa [T, a] using hcancel

/-! ## Union over all fixed agents -/

theorem lemma5iiEncounterCount_of_scale
    (hscale : Lemma5iiEncounterScaleArithmetic) :
    Lemma5iiEncounterCount := by
  intro n psi kappa c
  intro hn3 hpsi hc hkappa hnpow
  intro ring htails

  have hn2 : 2 <= n := by
    omega

  let T := lemma5iiHorizon n psi kappa
  let a := lemma5iiEncounterCap psi c
  let words := allSchedules n T
  let p : Fin n -> DetSchedule n -> Bool :=
    fun x word =>
      decide
        (a <
          predictableHostHits
            ring (fun _ => x) word)

  have hcover :
      forall word,
        lemma5iiEncounterBadB psi c ring word = true ->
          exists x : Fin n, p x word = true := by
    intro word hbad
    unfold lemma5iiEncounterBadB at hbad
    have hm :=
      encounterFoldOr_mem_true
        (List.ofFn
          (fun x : Fin n =>
            decide
              (lemma5iiEncounterCap psi c <
                predictableHostHits
                  ring (fun _ => x) word)))
        hbad
    rw [List.mem_ofFn] at hm
    obtain ⟨x, hx⟩ := hm
    exact ⟨x, by simpa [p, a] using hx⟩

  have hunion :
      lemma5iiEncounterFailureCount
          (psi := psi) (kappa := kappa) ring c <=
        (List.ofFn
          (fun x : Fin n =>
            words.countP (p x))).sum := by
    change
      words.countP
          (lemma5iiEncounterBadB psi c ring) <=
        (List.ofFn
          (fun x : Fin n =>
            words.countP (p x))).sum
    exact
      encounterFinUnion_le
        words
        (lemma5iiEncounterBadB psi c ring)
        p hcover

  have hpoint :
      forall x : Fin n,
        words.countP (p x) <=
          twoEdgeUpperTailCount n T a := by
    intro x
    have heq :=
      (htails n T a hn2 ring
        (fun _ => x)).1
    change
      predictableHostUpperTailCount
          ring (fun _ => x) T a <=
        twoEdgeUpperTailCount n T a
    exact Nat.le_of_eq heq

  have hsum :
      (List.ofFn
        (fun x : Fin n =>
          words.countP (p x))).sum <=
        n * twoEdgeUpperTailCount n T a := by
    calc
      (List.ofFn
        (fun x : Fin n =>
          words.countP (p x))).sum <=
          (List.ofFn
            (fun _ : Fin n =>
              twoEdgeUpperTailCount n T a)).sum :=
        encounterSum_ofFn_le
          (fun x : Fin n =>
            words.countP (p x))
          (fun _ : Fin n =>
            twoEdgeUpperTailCount n T a)
          hpoint
      _ =
          n * twoEdgeUpperTailCount n T a :=
        encounterSum_ofFn_const
          n (twoEdgeUpperTailCount n T a)

  have hunion' :
      lemma5iiEncounterFailureCount
          (psi := psi) (kappa := kappa) ring c <=
        n * twoEdgeUpperTailCount n T a :=
    Nat.le_trans hunion hsum

  have htail :=
    lemma5iiEncounterTail_scaled_of_scale
      hscale hn3 hpsi hc hkappa hnpow

  have hmul :=
    Nat.mul_le_mul_left n hunion'

  calc
    n *
        lemma5iiEncounterFailureCount
          (psi := psi) (kappa := kappa) ring c <=
        n * (n * twoEdgeUpperTailCount n T a) :=
      hmul
    _ =
        n * n * twoEdgeUpperTailCount n T a := by
      ac_rfl
    _ <=
        2 * n ^ T := by
      simpa [T, a] using htail
    _ =
        2 * n ^ lemma5iiHorizon n psi kappa := by
      rfl

#print axioms PPL.Modes.Lemma5.lemma5iiEncounter_fourThreeMoment
#print axioms PPL.Modes.Lemma5.lemma5iiEncounterTail_scaled_of_scale
#print axioms PPL.Modes.Lemma5.lemma5iiEncounterCount_of_scale

end PPL.Modes.Lemma5

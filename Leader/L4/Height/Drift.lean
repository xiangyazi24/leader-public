import Leader.L4.Height.Core
import Leader.L4.Height.Window
import Leader.L4.Height.Constants

namespace L4.Height

open L4.Compiler.Native

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero =>
      exact Nat.succ_pos 0
  | succ n ih =>
      change 0 < (n + 1) * fact n
      exact Nat.mul_pos (Nat.succ_pos n) ih

/-- The integer replacement for `122880*m*(1-1/k)`. -/
def Vpot (m k : Nat) : Nat :=
  122880 * m * (k - 1) * (fact m / k)

/-- The window length `T_G = 64*(ceil(10*m/k)+1)`, with ceiling
implemented by Nat division. This definition is used only for `k > 0`. -/
def gapWindowLen (m k : Nat) : Nat :=
  64 * (((10 * m + k - 1) / k) + 1)

/-- A bounded height state. Restricting the state space is what allows
the window theorem's all-state drift premise to use the bounded-state
sibling theorem without strengthening that theorem. -/
abbrev HeightBoundedState (m B : Nat) :=
  {x : Fin m → Snapshot // Bounded B x}

/-- The bounded transition induced by one alphabet letter. -/
def boundedHeightNext {m : Nat} (B : Nat) (hm : 0 < m)
    (hpres : ∀ x, Bounded B x → ∀ e : Fin (2 ^ m),
      Bounded B (heightChain B hm x e)) :
    HeightBoundedState m B → Fin (2 ^ m) → HeightBoundedState m B :=
  fun x e => ⟨heightChain B hm x.1 e, hpres x.1 x.2 e⟩

/-- The target on bounded states. -/
def boundedHeightStop {m B : Nat} (hm : 0 < m) :
    HeightBoundedState m B → Prop :=
  fun x => anchorCount hm x.1 = 1

/-- The number of anchors after a bounded-state projection. -/
def boundedAnchorCount {m B : Nat} (hm : 0 < m) :
    HeightBoundedState m B → Nat :=
  fun x => anchorCount hm x.1

/-- Stopping preserves the anchor-count bounds. The upper bound records
that the stopped run cannot increase the count from its starting value. -/
theorem stoppedRun_anchor_bounds
    {α : Type} {n m : Nat}
    (next : α → Fin n → α) (stop : α → Prop) (count : α → Nat)
    (hpos : ∀ x, 1 ≤ count x)
    (hmono : ∀ x e, count (next x e) ≤ count x) :
    ∀ x w, 1 ≤ count (stoppedRun next stop x w) ∧
      count (stoppedRun next stop x w) ≤ count x := by
  intro x w
  induction w generalizing x with
  | nil =>
      simp only [stoppedRun]
      exact ⟨hpos x, Nat.le_refl _⟩
  | cons e w ih =>
      by_cases hs : stop x
      · simp only [stoppedRun, hs, if_pos]
        exact ⟨hpos x, Nat.le_refl _⟩
      · simp only [stoppedRun, hs, if_false]
        have hnext := ih (next x e)
        constructor
        · exact hnext.1
        · exact Nat.le_trans hnext.2 (hmono x e)

/-- Word-sum monotonicity restricted to words of the enumerated length.
The ordinary `wordSum_mono` is pointwise over all lists; here every list
enumerated at level `k` has length `k`. -/
theorem wordSum_mono_length {n : Nat}
    (f g : List (Fin n) → Nat) :
    ∀ k, (∀ w, w.length = k → f w ≤ g w) →
      wordSum f k ≤ wordSum g k := by
  intro k
  induction k generalizing f g with
  | zero =>
      intro h
      simpa only [wordSum] using h [] rfl
  | succ k ih =>
      intro h
      simp only [wordSum]
      apply sum_ofFn_le
      intro e
      apply ih
      intro w hw
      apply h
      simp only [List.length_cons, hw]

/-- Every length-`k` word consumes at most `k` letters before stopping. -/
theorem wordSum_stoppedTime_le
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop)
    (x : α) (k : Nat) :
    wordSum (stoppedTime next stop x) k ≤ k * n ^ k := by
  calc
    wordSum (stoppedTime next stop x) k
        ≤ wordSum (fun _ : List (Fin n) => k) k := by
          apply wordSum_mono_length
          intro w hw
          have ht := stoppedTime_le_length next stop x w
          omega
    _ = n ^ k * k := wordSum_const (n := n) k k
    _ = k * n ^ k := Nat.mul_comm _ _

/-!
## The sibling interfaces

These are hypotheses of the assembly theorem. They are the minimal data
needed from Model, Window, Gap/Fill/Count and Arith. The controller can
replace them with the compiled sibling theorem names.
-/

/-- The aggregate integer-potential step from `Arith.lean`. -/
def WindowStepInterface (m n : Nat) : Prop :=
  ∀ (k L : Nat) (f : List (Fin n) → Nat),
    2 ≤ k → k ≤ m →
    (∀ u, 1 ≤ f u ∧ f u ≤ k) →
    k * L ≤ 768 * m →
    160 * wordSum (fun u => k - f u) L ≥ k * n ^ L →
    fact m * L * n ^ L +
        wordSum (fun u => Vpot m (f u)) L ≤
      Vpot m k * n ^ L

/-- Integer-potential upper bound from `Arith.lean`. -/
def PotentialBoundInterface (m : Nat) : Prop :=
  ∀ k, 1 ≤ k → k ≤ m →
    Vpot m k ≤ (122880 * m) * fact m

/-- The bounded-state and raw-state truncated IID costs agree. -/
theorem iidHitCost_boundedHeight_eq
    {m : Nat} (B : Nat) (hm : 0 < m)
    (hpres : ∀ x, Bounded B x → ∀ e : Fin (2 ^ m),
      Bounded B (heightChain B hm x e)) :
    ∀ t (x : HeightBoundedState m B),
      iidHitCost
          (boundedHeightNext B hm hpres)
          (boundedHeightStop (B := B) hm) t x =
        iidHitCost
          (heightChain B hm)
          (fun y => anchorCount hm y = 1) t x.1 := by
  intro t
  induction t with
  | zero =>
      intro x
      rfl
  | succ t ih =>
      intro x
      by_cases hx : anchorCount hm x.1 = 1
      · have hsx : boundedHeightStop (B := B) hm x := hx
        calc
          iidHitCost
              (boundedHeightNext B hm hpres)
              (boundedHeightStop (B := B) hm) (t + 1) x = 0 :=
            iidHitCost_of_target
              (boundedHeightNext B hm hpres)
              (boundedHeightStop (B := B) hm) x hsx (t + 1)
          _ = iidHitCost
              (heightChain B hm)
              (fun y => anchorCount hm y = 1) (t + 1) x.1 :=
            (iidHitCost_of_target
              (heightChain B hm)
              (fun y => anchorCount hm y = 1) x.1 hx (t + 1)).symm
      · have hsx : ¬ boundedHeightStop (B := B) hm x := by
          intro h
          exact hx h
        simp only [iidHitCost, hsx, hx, if_false]
        apply congrArg (fun q => (2 ^ m) ^ (t + 1) + q)
        apply sum_ofFn_eq
        intro e
        exact ih (boundedHeightNext B hm hpres x e)

/-- Height contraction assembled from the sibling interfaces.

MONO:
* boundedness is preserved;
* anchor count is nonincreasing;
* anchor count is always in `[1,m]`.

WINDOW:
* the exact `expected_of_window` implication, specialized to bounded
  height states.

DRIFT-STEP:
* the expected-loss `wordSum` inequality on every bounded non-target state.

ARITH:
* the gap-window length bound;
* the aggregate integer `window_step`;
* the potential upper bound.
-/
theorem height_contraction_of
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (hpres : ∀ x, Bounded B x → ∀ e : Fin (2 ^ m),
      Bounded B (heightChain B hm x e))
    (hcountMono : ∀ x : HeightBoundedState m B, ∀ e : Fin (2 ^ m),
      boundedAnchorCount (B := B) hm
          (boundedHeightNext B hm hpres x e) ≤
        boundedAnchorCount (B := B) hm x)
    (hcountPos : ∀ x : HeightBoundedState m B,
      1 ≤ boundedAnchorCount (B := B) hm x)
    (hcountLe : ∀ x : HeightBoundedState m B,
      boundedAnchorCount (B := B) hm x ≤ m)
    (hExpectedWindow :
      ∀ (V len : HeightBoundedState m B → Nat) (c : Nat),
        (∀ x, ¬ boundedHeightStop (B := B) hm x → 1 ≤ len x) →
        (∀ x, ¬ boundedHeightStop (B := B) hm x →
          c * wordSum
              (stoppedTime
                (boundedHeightNext B hm hpres)
                (boundedHeightStop (B := B) hm) x)
              (len x) +
            wordSum
              (fun u => V (stoppedRun
                (boundedHeightNext B hm hpres)
                (boundedHeightStop (B := B) hm) x u))
              (len x) ≤
            V x * (2 ^ m) ^ (len x)) →
        ∀ t x,
          c * iidHitCost
            (boundedHeightNext B hm hpres)
            (boundedHeightStop (B := B) hm) t x ≤
          V x * (2 ^ m) ^ t)
    (hDriftStep :
      ∀ x : HeightBoundedState m B,
        2 ≤ boundedAnchorCount (B := B) hm x →
        let k := boundedAnchorCount (B := B) hm x
        160 * wordSum
          (fun u => k - boundedAnchorCount (B := B) hm
            (stoppedRun
              (boundedHeightNext B hm hpres)
              (boundedHeightStop (B := B) hm) x u))
          (gapWindowLen m k) ≥
            k * (2 ^ m) ^ (gapWindowLen m k))
    (hGapLenBound :
      ∀ k, 2 ≤ k → k ≤ m →
        k * gapWindowLen m k ≤ 768 * m)
    (hWindowStep :
      WindowStepInterface m (2 ^ m))
    (hPotentialBound :
      PotentialBoundInterface m) :
    IIDExpectedHittingTimeAtMost
      (heightChain B hm)
      (fun x => anchorCount hm x = 1)
      s (122880 * m) := by
  let next :
      HeightBoundedState m B → Fin (2 ^ m) → HeightBoundedState m B :=
    boundedHeightNext B hm hpres
  let stop : HeightBoundedState m B → Prop :=
    boundedHeightStop (B := B) hm
  let count : HeightBoundedState m B → Nat :=
    boundedAnchorCount (B := B) hm
  let V : HeightBoundedState m B → Nat :=
    fun x => Vpot m (count x)
  let len : HeightBoundedState m B → Nat :=
    fun x => gapWindowLen m (count x)
  have hfactorial : 0 < fact m := fact_pos m
  have hlen : ∀ x, ¬ stop x → 1 ≤ len x := by
    intro x _hx
    change 1 ≤ 64 * (((10 * m + count x - 1) / count x) + 1)
    exact Nat.mul_pos (by decide) (Nat.succ_pos _)
  have hbudget : ∀ x, ¬ stop x →
      fact m * wordSum (stoppedTime next stop x) (len x) +
        wordSum (fun u => V (stoppedRun next stop x u)) (len x) ≤
          V x * (2 ^ m) ^ (len x) := by
    intro x hx
    have hkpos : 1 ≤ count x := by
      simpa only [count] using hcountPos x
    have hkne : count x ≠ 1 := by
      intro he
      apply hx
      simpa only [stop, boundedHeightStop, count, boundedAnchorCount]
        using he
    have hkraw : 2 ≤ count x := by omega
    have hkmraw : count x ≤ m := by
      simpa only [count] using hcountLe x
    let k : Nat := count x
    let L : Nat := gapWindowLen m k
    let f : List (Fin (2 ^ m)) → Nat :=
      fun u => count (stoppedRun next stop x u)
    have hk : 2 ≤ k := by
      simpa only [k] using hkraw
    have hkm : k ≤ m := by
      simpa only [k] using hkmraw
    have hpos' : ∀ y, 1 ≤ count y := by
      intro y
      simpa only [count] using hcountPos y
    have hmono' : ∀ y e, count (next y e) ≤ count y := by
      intro y e
      simpa only [next, count] using hcountMono y e
    have hfrange : ∀ u, 1 ≤ f u ∧ f u ≤ k := by
      intro u
      have hb := stoppedRun_anchor_bounds (m := m)
        next stop count hpos' hmono' x u
      simpa only [f, k] using hb
    have hlenarith : k * L ≤ 768 * m :=
      hGapLenBound k hk hkm
    have hkarg : 2 ≤ boundedAnchorCount (B := B) hm x := by
      simpa only [count, k] using hk
    have hdrift := hDriftStep x hkarg
    change 160 * wordSum (fun u => k - f u) L ≥
      k * (2 ^ m) ^ L at hdrift
    have harith :
        fact m * L * (2 ^ m) ^ L +
            wordSum (fun u => Vpot m (f u)) L ≤
          Vpot m k * (2 ^ m) ^ L :=
      hWindowStep k L f hk hkm hfrange hlenarith hdrift
    change
      fact m * L * (2 ^ m) ^ L +
          wordSum (fun u => V (stoppedRun next stop x u)) L ≤
        V x * (2 ^ m) ^ L at harith
    have htime := wordSum_stoppedTime_le next stop x L
    have htimeScaled :
        fact m * wordSum (stoppedTime next stop x) L ≤
          fact m * (L * (2 ^ m) ^ L) :=
      Nat.mul_le_mul_left (fact m) htime
    change
      fact m * wordSum (stoppedTime next stop x) L +
          wordSum (fun u => V (stoppedRun next stop x u)) L ≤
        V x * (2 ^ m) ^ L
    calc
      fact m * wordSum (stoppedTime next stop x) L +
          wordSum (fun u => V (stoppedRun next stop x u)) L
          ≤ fact m * (L * (2 ^ m) ^ L) +
              wordSum (fun u => V (stoppedRun next stop x u)) L := by
                exact Nat.add_le_add_right htimeScaled _
      _ = fact m * L * (2 ^ m) ^ L +
              wordSum (fun u => V (stoppedRun next stop x u)) L := by
                simp only [Nat.mul_assoc]
      _ ≤ V x * (2 ^ m) ^ L := harith
  have hwindow : ∀ t x,
      fact m * iidHitCost next stop t x ≤
        V x * (2 ^ m) ^ t := by
    exact hExpectedWindow V len (fact m) hlen hbudget
  let start : HeightBoundedState m B := ⟨s, hs⟩
  have hkStartPos : 1 ≤ count start := by
    simpa only [count] using hcountPos start
  have hkStartLe : count start ≤ m := by
    simpa only [count] using hcountLe start
  have hpot :
      Vpot m (count start) ≤ (122880 * m) * fact m :=
    hPotentialBound (count start) hkStartPos hkStartLe
  have hcostBound : ∀ t,
      fact m * iidHitCost next stop t start ≤
        (122880 * m) * fact m * (2 ^ m) ^ t := by
    intro t
    have hpotScaled :=
      Nat.mul_le_mul_right ((2 ^ m) ^ t) hpot
    exact Nat.le_trans (hwindow t start) (by
      simpa only [V] using hpotScaled)
  have hfactorCancel : ∀ t,
      iidHitCost next stop t start ≤
        (122880 * m) * (2 ^ m) ^ t := by
    intro t
    have hmul :
        iidHitCost next stop t start * fact m ≤
          ((122880 * m) * (2 ^ m) ^ t) * fact m := by
      calc
        iidHitCost next stop t start * fact m =
            fact m * iidHitCost next stop t start := Nat.mul_comm _ _
        _ ≤ (122880 * m) * fact m * (2 ^ m) ^ t := hcostBound t
        _ = (122880 * m) * (fact m * (2 ^ m) ^ t) :=
          Nat.mul_assoc _ _ _
        _ = (122880 * m) * ((2 ^ m) ^ t * fact m) := by
          exact congrArg (fun q => (122880 * m) * q)
            (Nat.mul_comm _ _)
        _ = ((122880 * m) * (2 ^ m) ^ t) * fact m :=
          (Nat.mul_assoc _ _ _).symm
    exact Nat.le_of_mul_le_mul_right hmul hfactorial
  unfold IIDExpectedHittingTimeAtMost
  intro t
  calc
    iidHitCost
        (heightChain B hm)
        (fun x => anchorCount hm x = 1) t s =
      iidHitCost next stop t start := by
        symm
        simpa only [next, stop, start] using
          (iidHitCost_boundedHeight_eq B hm hpres t start)
    _ ≤ (122880 * m) * (2 ^ m) ^ t := hfactorCancel t

/-- The sibling-complete theorem: the same interface package as
`height_contraction_of`, now named for the final paper statement. -/
theorem height_contraction
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (hpres : ∀ x, Bounded B x → ∀ e : Fin (2 ^ m),
      Bounded B (heightChain B hm x e))
    (hcountMono : ∀ x : HeightBoundedState m B, ∀ e : Fin (2 ^ m),
      boundedAnchorCount (B := B) hm
          (boundedHeightNext B hm hpres x e) ≤
        boundedAnchorCount (B := B) hm x)
    (hcountPos : ∀ x : HeightBoundedState m B,
      1 ≤ boundedAnchorCount (B := B) hm x)
    (hcountLe : ∀ x : HeightBoundedState m B,
      boundedAnchorCount (B := B) hm x ≤ m)
    (hExpectedWindow :
      ∀ (V len : HeightBoundedState m B → Nat) (c : Nat),
        (∀ x, ¬ boundedHeightStop (B := B) hm x → 1 ≤ len x) →
        (∀ x, ¬ boundedHeightStop (B := B) hm x →
          c * wordSum
              (stoppedTime
                (boundedHeightNext B hm hpres)
                (boundedHeightStop (B := B) hm) x)
              (len x) +
            wordSum
              (fun u => V (stoppedRun
                (boundedHeightNext B hm hpres)
                (boundedHeightStop (B := B) hm) x u))
              (len x) ≤
            V x * (2 ^ m) ^ (len x)) →
        ∀ t x,
          c * iidHitCost
            (boundedHeightNext B hm hpres)
            (boundedHeightStop (B := B) hm) t x ≤
          V x * (2 ^ m) ^ t)
    (hDriftStep :
      ∀ x : HeightBoundedState m B,
        2 ≤ boundedAnchorCount (B := B) hm x →
        let k := boundedAnchorCount (B := B) hm x
        160 * wordSum
          (fun u => k - boundedAnchorCount (B := B) hm
            (stoppedRun
              (boundedHeightNext B hm hpres)
              (boundedHeightStop (B := B) hm) x u))
          (gapWindowLen m k) ≥
            k * (2 ^ m) ^ (gapWindowLen m k))
    (hGapLenBound :
      ∀ k, 2 ≤ k → k ≤ m →
        k * gapWindowLen m k ≤ 768 * m)
    (hWindowStep :
      WindowStepInterface m (2 ^ m))
    (hPotentialBound :
      PotentialBoundInterface m) :
    IIDExpectedHittingTimeAtMost
      (heightChain B hm)
      (fun x => anchorCount hm x = 1)
      s (122880 * m) :=
  height_contraction_of B hm hB s hs hpres hcountMono hcountPos
    hcountLe hExpectedWindow hDriftStep hGapLenBound hWindowStep
    hPotentialBound

end L4.Height

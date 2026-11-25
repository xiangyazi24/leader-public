import Leader.L4.Height.Drift
import Leader.L4.Height.Model

namespace L4.Height

open L4.Compiler.Native

/-- The model's round-preservation theorem, specialized to letters. -/
theorem heightPres {m : Nat} (B : Nat) (hm : 0 < m)
    (hB : m < B) :
    ∀ x, Bounded B x → ∀ e : Fin (2 ^ m),
      Bounded B (heightChain B hm x e) := by
  intro x hx e
  change Bounded B (logicalRound B hm (bitsOf e) x)
  exact bounded_round B hm (by omega) (bitsOf e) x hx

/-- A true predicate at a list member gives a positive Boolean count. -/
theorem countP_pos_of_mem {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), a ∈ l → p a = true →
      1 ≤ l.countP p := by
  intro l a ha hp
  have hpos : 0 < l.countP p := by
    apply List.countP_pos_iff.mpr
    exact ⟨a, ha, hp⟩
  omega

/-- A Boolean count never exceeds list length. -/
theorem countP_le_length {α : Type} (p : α → Bool) :
    ∀ l : List α, l.countP p ≤ l.length := by
  intro l
  exact List.countP_le_length

/-- Positive anchor count on every state of the height cycle. -/
theorem heightAnchorCount_pos {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) : 1 ≤ anchorCount hm s := by
  obtain ⟨i, hi⟩ := anchor_exists hm s
  unfold anchorCount
  apply countP_pos_of_mem
  · simp
  · exact decide_eq_true hi

/-- At most one anchor is counted per site. -/
theorem heightAnchorCount_le {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) : anchorCount hm s ≤ m := by
  unfold anchorCount
  have h := countP_le_length
    (fun i : Fin m => decide (IsAnchor hm s i)) (List.finRange m)
  simpa only [List.length_finRange] using h

/-- Mid-stage contraction: only the loss and arithmetic interfaces remain. -/
theorem height_contraction_mid
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (hDriftStep :
      ∀ x : HeightBoundedState m B,
        2 ≤ boundedAnchorCount (B := B) hm x →
        let k := boundedAnchorCount (B := B) hm x
        160 * wordSum
          (fun u => k - boundedAnchorCount (B := B) hm
            (stoppedRun
              (boundedHeightNext B hm (heightPres B hm hB))
              (boundedHeightStop (B := B) hm) x u))
          (gapWindowLen m k) ≥
            k * (2 ^ m) ^ (gapWindowLen m k))
    (hGapLenBound :
      ∀ k, 2 ≤ k → k ≤ m →
        k * gapWindowLen m k ≤ 768 * m)
    (hWindowStep : WindowStepInterface m (2 ^ m))
    (hPotentialBound : PotentialBoundInterface m) :
    IIDExpectedHittingTimeAtMost
      (heightChain B hm)
      (fun x => anchorCount hm x = 1)
      s (122880 * m) := by
  let hpres := heightPres B hm hB
  have hcountMono :
      ∀ x : HeightBoundedState m B, ∀ e : Fin (2 ^ m),
        boundedAnchorCount (B := B) hm
          (boundedHeightNext B hm hpres x e) ≤
        boundedAnchorCount (B := B) hm x := by
    intro x e
    change anchorCount hm (logicalRound B hm (bitsOf e) x.1) ≤
      anchorCount hm x.1
    exact anchorCount_mono B hm hB (bitsOf e) x.1 x.2
  have hcountPos :
      ∀ x : HeightBoundedState m B,
        1 ≤ boundedAnchorCount (B := B) hm x := by
    intro x
    exact heightAnchorCount_pos hm x.1
  have hcountLe :
      ∀ x : HeightBoundedState m B,
        boundedAnchorCount (B := B) hm x ≤ m := by
    intro x
    exact heightAnchorCount_le hm x.1
  have hExpectedWindow :
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
          V x * (2 ^ m) ^ t := by
    intro V len c hlen H
    exact expected_of_window
      (boundedHeightNext B hm hpres)
      (boundedHeightStop (B := B) hm) V len c hlen H
  exact height_contraction_of B hm hB s hs
    hpres hcountMono hcountPos hcountLe hExpectedWindow
    hDriftStep hGapLenBound hWindowStep hPotentialBound

end L4.Height

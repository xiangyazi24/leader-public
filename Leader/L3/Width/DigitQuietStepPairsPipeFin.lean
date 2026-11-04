import Leader.L3.Width.DigitQuietStepGuard
import Leader.L3.Width.DigitQuietStepWinSrc
import Leader.L3.Width.DigitQuietStepSplit

/-!
# The pair predicate under one letter, block-relative: pipe, fin, field changes

`PQ R vs vt Dp` (WidthDigitQuietStepSplit) is the pair scan on the views `vs` of the source block and
`vt` of the target block.  This module closes it under

* `pq_congr`: any change of the views that keeps the fields the scan reads (the `out` slots of the
  source cells, the in-slot and carry of the target cells);
* `pq_pipe`: a pipe letter inside the source block (`win_pipe` on the window of the two cells);
* `pq_fin`: a fin letter inside the target block (`win_fin` on the window of the two cells, with the
  guard `h + 1 ≤ nxt` supplied by the scan).

Consumer: `WidthDigitQuietStepPairs` (the pairs clause of `QuietStepLaw`).
-/

namespace L3.DigitQuiet

open L3

set_option autoImplicit false

variable {c : Compiled}

/-- `PQ` reads only the `out` slots of the source cells and the in-slot / carry fields of the target
cells.  Consumer: the pair closure for letters off the pair and for the entry letter. -/
theorem pq_congr (R : Nat) (vs vs' vt vt' : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (hs : ∀ q, q < R → (vs q).out = (vs' q).out)
    (ht : ∀ q, q < R → (vt q).input = (vt' q).input ∧ (vt q).carryLive = (vt' q).carryLive ∧
      (vt q).carryBit = (vt' q).carryBit ∧ (vt q).carryError = (vt' q).carryError) :
    PQ R vs vt Dp ↔ PQ R vs' vt' Dp := by
  unfold PQ
  rw [scanTarget_eq_W, scanTarget_eq_W]
  have hsrc : ∀ a, ScanSource vs Dp R a ↔ ScanSource vs' Dp R a := by
    intro a
    rw [scanSource_eq_W, scanSource_eq_W]
    exact scanSourceW_congr_out vs vs' Dp 0 (fun _ => True) R (fun i _ hi => hs i (by omega)) a
  rw [scanTargetW_congr_in R vt vt' Dp 0 _ R (fun i _ hi => ht i (by omega))]
  constructor
  · intro h
    exact scanTargetW_mono R vt' vt' Dp 0 _ _ (fun a _ _ ha => (hsrc a).mp ha) R
      (fun _ _ _ => rfl) _ _ _ h
  · intro h
    exact scanTargetW_mono R vt' vt' Dp 0 _ _ (fun a _ _ ha => (hsrc a).mpr ha) R
      (fun _ _ _ => rfl) _ _ _ h

/-- Equal target views give equivalent pair predicates.  Consumer: `pq_after_letter`. -/
theorem pq_eq_target (R : Nat) (vs vt vt' : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (h : ∀ q, q < R → vt q = vt' q) : PQ R vs vt Dp ↔ PQ R vs vt' Dp :=
  pq_congr R vs vs vt vt' Dp (fun _ _ => rfl)
    (fun q hq => by rw [h q hq]; exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Equal source views give equivalent pair predicates.  Consumer: `pq_after_letter`. -/
theorem pq_eq_source (R : Nat) (vs vs' vt : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (h : ∀ q, q < R → vs q = vs' q) : PQ R vs vt Dp ↔ PQ R vs' vt Dp :=
  pq_congr R vs vs' vt vt Dp (fun q hq => by rw [h q hq]) (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)

/-- **A pipe letter inside the source block keeps the pair predicate.**  Consumer: the pair
closure. -/
theorem pq_pipe (lane : DigitLane) (R : Nat) (vs vs' vt : Nat → DigitLaneView c)
    (Dp : Nat → Fin c.topA) (h : Nat) (hh : h + 1 < R)
    (hlx : (vs h).leader = false) (hly : (vs (h+1)).leader = false)
    (hmx : (vs h).marker = decide (h = 0)) (hmy : (vs (h+1)).marker = false)
    (hdx : (vs h).digit = Dp h)
    (hw0 : vs' h = (laneRow lane (vs h) (vs (h+1))).1)
    (hw1 : vs' (h+1) = (laneRow lane (vs h) (vs (h+1))).2)
    (hrest : ∀ q, q < R → q ≠ h → q ≠ h + 1 → vs' q = vs q) :
    PQ R vs vt Dp → PQ R vs' vt Dp := by
  unfold PQ
  intro hp
  rw [scanTarget_eq_W] at hp ⊢
  have hsrc : ∀ a, ScanSource vs Dp R a → ScanSource vs' Dp R a := by
    intro a ha
    rw [scanSource_eq_W] at ha ⊢
    obtain ⟨t, ht⟩ : ∃ t, R = h + 2 + t := ⟨R - h - 2, by omega⟩
    rw [ht] at ha ⊢
    exact scanSourceW_replace vs vs' Dp h 2 t (fun q hq => (hrest q (by omega) (by omega)
      (by omega)).symm) (fun q h1 h2 => (hrest q (by omega) (by omega) (by omega)).symm)
      (fun K nxt hs => win_pipe lane vs vs' Dp h hlx hly hmx hmy hdx hw0 hw1 K nxt hs)
      (fun _ => True) a ha
  exact scanTargetW_mono R vt vt Dp 0 _ _ (fun a _ _ ha => hsrc a ha) R (fun _ _ _ => rfl) _ _ _ hp

/-- **A fin letter inside the target block keeps the pair predicate.**  The digit hypotheses are the
digits of the target block (`values_digitwise`), used for the comparison error bit.  Consumer: the
pair closure. -/
theorem pq_fin (lane : DigitLane) (R : Nat) (vs vt vt' : Nat → DigitLaneView c)
    (Dp : Nat → Fin c.topA) (h : Nat) (hh : h + 1 < R)
    (hlx : (vt h).leader = false) (hly : (vt (h+1)).leader = false)
    (hmx : (vt h).marker = decide (h = 0)) (hmy : (vt (h+1)).marker = false)
    (hdx : ((vt h).digit).val = ((Dp h).val + (if carryInto Dp h then 1 else 0)) % c.topA)
    (hdy : ((vt (h+1)).digit).val =
      ((Dp (h+1)).val + (if carryInto Dp (h+1) then 1 else 0)) % c.topA)
    (hw0 : vt' h = (laneRow lane (vt h) (vt (h+1))).1)
    (hw1 : vt' (h+1) = (laneRow lane (vt h) (vt (h+1))).2)
    (hrest : ∀ q, q < R → q ≠ h → q ≠ h + 1 → vt' q = vt q) :
    PQ R vs vt Dp → PQ R vs vt' Dp := by
  unfold PQ
  intro hp
  rw [scanTarget_eq_W] at hp ⊢
  obtain ⟨t, ht⟩ : ∃ t, R = h + 2 + t := ⟨R - h - 2, by omega⟩
  subst ht
  exact scanTargetW_replace_guard (h + 2 + t) vt vt' Dp h 2 t
    (fun q hq => (hrest q (by omega) (by omega) (by omega)).symm)
    (fun q h1 h2 => (hrest q (by omega) (by omega) (by omega)).symm) (by omega)
    (fun K nxt sawP seen hK hg' hs =>
      win_fin lane (h + 2 + t) vt vt' Dp h hh hlx hly hmx hmy hdx hdy hw0 hw1 K nxt sawP seen
        (by omega) hK hs)
    (fun a _ _ => ScanSource vs Dp (h + 2 + t) a) (fun a d h => h) (h + 2 + t - 1) false false
    (by omega) hp

end L3.DigitQuiet

#print axioms L3.DigitQuiet.pq_congr
#print axioms L3.DigitQuiet.pq_pipe
#print axioms L3.DigitQuiet.pq_fin

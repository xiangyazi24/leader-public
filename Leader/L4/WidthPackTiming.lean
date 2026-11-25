import Leader.L4.WidthPackJoint
import Leader.L4.MonitorRawBridge
import Leader.L4.AllSizeComposition

namespace L4.WidthPackTiming
open PhysicalCustody WidthPackJoint WidthCacheAllSites WidthPackedBridge
open BStarH6WordChart MonitorRawBridge

variable {s n : Nat}

private theorem run_app {X : Type} (f : X → Fin n → X) (x : X)
    (u v : List (Fin n)) : SequentialMarkClock.run f x (u ++ v) = SequentialMarkClock.run f (SequentialMarkClock.run f x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (f x e)

private theorem run_closed {X : Type} (f : X → Fin n → X) (P : X → Prop)
    (closed : ∀ x e, P x → P (f x e)) (x : X) (A : P x) (w : List (Fin n)) :
    P (SequentialMarkClock.run f x w) := by
  induction w generalizing x with
  | nil => exact A
  | cons e w ih => exact ih (f x e) (closed x e A)

/-- Each owner may finish at a different prefix of one literal raw tape.
The receipt predicate must imply membership in the absorbing owner fibre
at that prefix; a historical flag value alone does not suffice. -/
theorem qwidth_of_prefix_receipts
    (P6 : Raw s n → Prop) (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (lower_closed : ∀ y e, P6 y → P6 (rawNext s y e))
    (cache_closed : ∀ y e, WidthCorrect h hh P6 y →
      WidthCorrect h hh P6 (rawNext s y e))
    (OwnerGood : Header h → Raw s n → Prop)
    (owner_closed : ∀ q y e, OwnerGood q y → OwnerGood q (rawNext s y e))
    (x : Raw s n) (lower : P6 x) (cache : WidthCorrect h hh P6 x)
    (Receipt : Header h → List (Fin n) → Prop)
    (credit : ∀ q u, Receipt q u → OwnerGood q (SequentialMarkClock.run (rawNext s) x u))
    (w : List (Fin n))
    (cert : ∀ q, ∃ u v, w = u ++ v ∧ Receipt q u) :
    Qwidth P6 h hh OwnerGood (SequentialMarkClock.run (rawNext s) x w) := by
  refine ⟨run_closed _ _ lower_closed x lower w, run_closed _ _ cache_closed x cache w, ?_⟩
  intro q
  obtain ⟨u,v,E,C⟩ := cert q
  rw [E, run_app]
  exact run_closed _ _ (owner_closed q) _ (credit q u C) v

/-- A post-cache monitor contract on the original physical alphabet.
Its price and the semantic meaning of its receipts are item 16 inputs. -/
structure PaidOwnerMonitor (h : Fin n → Bool)
    (OwnerGood : Header h → Raw s n → Prop) (x : Raw s n) where
  State : Type
  step : State → Fin n → State
  project : State → Raw s n
  start : State
  base : project start = x
  step_project : ∀ z e, project (step z e) = rawNext s (project z) e
  done : State → Prop
  Receipt : Header h → List (Fin n) → Prop
  credit : ∀ q u, Receipt q u → OwnerGood q (SequentialMarkClock.run (rawNext s) x u)
  terminal : ∀ w, done (SequentialMarkClock.run step start w) → ∀ q, ∃ u v, w = u ++ v ∧ Receipt q u
  price : Height.IIDExpectedHittingTimeAtMost step done start (5120*n^2)

/-- Conditional W17.7/8: add the checked cache cost at the first cache hit,
then use the supplied all-owner monitor on the same raw scheduler.
No external switch of tape or independence assumptions are introduced. -/
theorem width_packed_stage_expected (hs : 6 ≤ s) (N : 1 < n)
    (P6 : Raw s n → Prop) (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (lower_closed : ∀ y e, P6 y → P6 (rawNext s y e))
    (mask : ∀ y, P6 y → ∀ i, oldH6 (rows s) y i = h i)
    (spacing : ∀ y, P6 y → CertifiedSpacing y)
    (OwnerGood : Header h → Raw s n → Prop)
    (owner_closed : ∀ q y e, OwnerGood q y → OwnerGood q (rawNext s y e))
    (owner_flags : ∀ q y, OwnerGood q y → OwnerWordFlagsCorrect h hh q y)
    (postcache : ∀ y, WidthCorrect h hh P6 y → Nonempty (PaidOwnerMonitor h OwnerGood y))
    (x : Raw s n) (X : P6 x) :
    IIDExpectedHittingTimeAtMost (rawNext s) (fun z => Nonempty (PackedFiber z))
      x ((s+5132)*n^2) := by
  obtain ⟨cache_closed, cache_mean⟩ := width_raw N h hh P6 lower_closed mask x X
  have start := (height_iff_row (rawNext s) (WidthCorrect h hh P6) x _).mp cache_mean
  rw [show (s+5132)*n^2 = (s+12)*n^2 + 5120*n^2 by
    rw [← Nat.add_mul]]
  refine AllSizeComposition.additive_stage _ _ _ _ _ x start ?_
  intro y Y
  obtain ⟨m⟩ := postcache y Y
  have A : P6 y := Y.1
  have T := expected_of_monitor_words (rawNext s) m.step m.project m.done
    (fun z => Nonempty (PackedFiber z)) m.step_project m.start
    (fun w D => by
      rw [m.base]
      exact packed_of_width_joint hs N P6 h hh lower_closed mask spacing OwnerGood
        owner_closed owner_flags _
        (qwidth_of_prefix_receipts P6 h hh lower_closed cache_closed OwnerGood
          owner_closed y A Y m.Receipt m.credit w (m.terminal w D))) _ m.price
  simpa only [m.base] using T

end L4.WidthPackTiming

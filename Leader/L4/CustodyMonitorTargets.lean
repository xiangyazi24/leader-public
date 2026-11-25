import Leader.L4.MonitorRawBridge
import Leader.L4.ShortTwoPublicationClock
import Leader.L4.ReportCacheAllSites
import Leader.L4.WidthCacheAllSites

namespace L4.CustodyMonitorTargets

open MonitorRawBridge
variable {X J : Type} {n : Nat}

def RawMaximal (r : ShortNORCover.Ring J) (observe : X → J → Bool)
    (Good : X → Prop) (y : X) : Prop :=
  Good y ∧ ShortNORCover.Independent r (observe y) ∧
    ∀ j, ShortNORCover.Dominates r (observe y) j

theorem raw_maximal_closed [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J)
    (r : ShortNORCover.Ring J) (observe : X → J → Bool) (Good : X → Prop)
    (closed : ∀ y e, Good y → Good (advance y e))
    (auth : ∀ y e, Good y → observe (advance y e) =
      match classify y e with
      | none => observe y
      | some j => ShortNORCover.update r (observe y) j) :
    ∀ y e, RawMaximal r observe Good y → RawMaximal r observe Good (advance y e) := by
  intro y e ⟨G,I,D⟩
  refine ⟨closed y e G,?_⟩
  rw [auth y e G]
  cases classify y e with
  | none => exact ⟨I,D⟩
  | some j => exact ShortNORCover.maximal_step r _ j ⟨I,D⟩

private theorem run_foldl (advance : X → Fin n → X) (x : X) (w : List (Fin n)) :
    SequentialMarkClock.run advance x w = w.foldl advance x := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (advance x e)

/-- The finished two-cover monitor is sound for the current raw NOR
target under the genuine classifier and its closed domain. The bound
transfers without charging another factor for the physical scheduler. -/
theorem raw_two_covers_expected [DecidableEq J]
    (advance : X → Fin n → X) (classify : X → Fin n → Option J)
    (r : ShortNORCover.Ring J) (observe : X → J → Bool) (Good : X → Prop)
    (closed : ∀ y e, Good y → Good (advance y e))
    (auth : ∀ y e, Good y → observe (advance y e) =
      match classify y e with
      | none => observe y
      | some j => ShortNORCover.update r (observe y) j)
    (sites : List J) (all : ∀ j, j ∈ sites) (L : sites.length ≤ n)
    (K : Nat) (service : ShortTwoPublicationClock.UniformPublicationMean
      advance classify Good (K*n)) (x : X) (hx : Good x) :
    IIDExpectedHittingTimeAtMost advance (RawMaximal r observe Good) x (2*K*n^2) := by
  let z := SequentialMarkClock.start false (sites++sites) x
  let m := ShortTwoPublicationClock.monitoredNext advance classify
  have relift (y : SequentialMarkClock.State X Bool J) (e : Fin n) :
      (m y e).raw=advance y.raw e :=
    SequentialMarkClock.step_raw advance (ShortTwoPublicationClock.phase advance classify)
      ShortTwoPublicationClock.goal false (fun _ _ _=>rfl) y e
  have sound (w : List (Fin n))
      (D : SequentialMarkClock.finished (SequentialMarkClock.run m z w)) :
      RawMaximal r observe Good (SequentialMarkClock.run advance x w) := by
    have good (v : List (Fin n)) (y : X) (Y : Good y) :
        Good (v.foldl advance y) := by
      induction v generalizing y with
      | nil => exact Y
      | cons e v ih => exact ih (advance y e) (closed y e Y)
    rw [run_foldl]
    exact ⟨good w x hx,ShortTwoPublicationClock.maximal_at_finished advance classify r
      observe Good closed auth sites all x hx w D⟩
  exact expected_of_monitor_words advance m (fun y=>y.raw) SequentialMarkClock.finished
    (RawMaximal r observe Good) relift z sound _ <|
      ShortTwoPublicationClock.two_covers_quadratic advance classify Good closed K service sites L x hx

section Caches
open AllSizeProtocol PhysicalCustody ReportCacheAllSites BStarH6WordChart

theorem report1_raw_mean {s n : Nat} (N : 1<n) (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (closed : ∀ y e,Q y→Q (rawNext s y e))
    (mask : ∀ y,Q y→∀ i,(oldHeaders (rows s) (y i)).h4=h i)
    (x : Raw s n) (A : Q x) :
    IIDExpectedHittingTimeAtMost (rawNext s) (Report1Correct h hh Q) x (4*n^2) :=
  (height_iff_row _ _ _ _).mp (report1_raw N h hh Q closed mask x A).2

theorem report2_raw_mean {s n : Nat} (N : 1<n) (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (closed : ∀ y e,Q y→Q (rawNext s y e))
    (mask : ∀ y,Q y→∀ i,(oldHeaders (rows s) (y i)).h5=h i)
    (x : Raw s n) (A : Q x) :
    IIDExpectedHittingTimeAtMost (rawNext s) (Report2Correct h hh Q) x
      ((max 3 (ell (radiusTwo s+1))+1)*n^2) :=
  (height_iff_row _ _ _ _).mp (report2_raw N h hh Q closed mask x A).2

theorem width_raw_mean {s n : Nat} (N : 1<n) (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (closed : ∀ y e,Q y→Q (rawNext s y e))
    (mask : ∀ y,Q y→∀ i,oldH6 (rows s) y i=h i)
    (x : Raw s n) (A : Q x) :
    IIDExpectedHittingTimeAtMost (rawNext s) (WidthCacheAllSites.WidthCorrect h hh Q)
      x ((s+12)*n^2) :=
  (height_iff_row _ _ _ _).mp (WidthCacheAllSites.width_raw N h hh Q closed mask x A).2

end Caches
end L4.CustodyMonitorTargets

import Leader.L4.ConcreteTail
import Leader.L4.EntranceCover

namespace L4

open TaggedTrace TaggedFront

/-- The nearest upstream root (allowing zero distance) is the shielded
source of this live bullet, and the full clockwise trail is zero-signal.
Under MCOV, testing roots by incoming marks is exact. -/
def RootPeacefulAt {p c1 n : Nat} (x : Config p c1 n) (b : Fin n) : Prop :=
  ∃ incoming : Fin n, ∃ d : Nat,
    let z := rightNeighbor incoming
    d < n ∧ (x incoming).mark = true ∧ (x z).leader = true ∧
      (x z).shield = true ∧ plusOffset z d = b ∧
      (∀ j : Nat, j < d → (x (plusOffset z j)).mark = false) ∧
      (∀ j : Nat, j ≤ d → (x (plusOffset z j)).signal = .zero)

def PeacefulLive {p c1 n : Nat} (x : Config p c1 n) : Prop :=
  ∀ b : Fin n, (x b).bullet = .live → RootPeacefulAt x b

def QuietEntrance {p c1 n : Nat} (x : Config p c1 n) : Prop :=
  MCOV x ∧ COV x ∧ (∃ e : Fin n, (x e).mark = true) ∧ PeacefulLive x

def trackAll {p c1 n : Nat} (s : AllObs p c1 n) : List (Fin n) → AllObs p c1 n
  | [] => s
  | e::w => trackAll (allAdvance s e) w

theorem trackAll_append {p c1 n : Nat} (s : AllObs p c1 n) (u v : List (Fin n)) :
    trackAll s (u++v) = trackAll (trackAll s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih => exact ih (allAdvance s e)

theorem allTrack_config {p c1 n : Nat} (s : AllObs p c1 n)
    (i : Fin n) (w : List (Fin n)) :
    ((trackAll s w) i).config = run (s i).config w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih =>
    change ((trackAll (allAdvance s e) w) i).config = run (step (s i).config e) w
    rw [ih]
    exact congrArg (fun x => run x w) (projection_step (s i) e)

/-- Exact outstanding suffix interface of lem:new-good. Cover and
nonemptiness are NOT assumed here as conclusions; they are proved below. -/
def FreshPeaceAfterExtinction : Prop :=
  ∀ {p c1 n : Nat} (x : Config p c1 n) (w : List (Fin n)),
    2 ≤ p → 12 ≤ c1 → 4 ≤ n → (¬ p ∣ n) → MCOV x → COV x →
    allEnded (trackAll (allInit x) w) → PeacefulLive (run x w)

theorem cover_run {p c1 n : Nat} (hn : 4 ≤ n) (x : Config p c1 n)
    (h : MCOV x ∧ COV x) (w : List (Fin n)) :
    MCOV (run x w) ∧ COV (run x w) := by
  induction w generalizing x with
  | nil => exact h
  | cons e w ih => exact ih (step x e) (EntranceCover.cover_closed hn x e h)

/-- Equivalence of stopping sets only on a forward invariant is sufficient
for equality of all finite-horizon numerator costs at its points. -/
theorem hitCost_equiv_on_invariant {α : Type} {n : Nat}
    (next : α → Fin n → α) (P Q good : α → Prop)
    (hgood : ∀ s e, good s → good (next s e))
    (hst : ∀ s, good s → (P s ↔ Q s)) (t : Nat) (s : α) (hs : good s) :
    iidHitCost next P t s = iidHitCost next Q t s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    by_cases hp : P s
    · rw [iidHitCost_of_target _ _ _ hp, iidHitCost_of_target _ _ _ ((hst s hs).mp hp)]
    · have hq : ¬ Q s := fun h => hp ((hst s hs).mpr h)
      simp only [iidHitCost, hp, hq, if_false]
      have hh : (fun e => iidHitCost next P t (next s e)) =
          (fun e => iidHitCost next Q t (next s e)) := by
        funext e
        exact ih (next s e) (hgood s e hs)
      rw [hh]

/-- Literal L4 entrance conditional on an actual live debt bound and
the new-bullet peacefulness interface. The ordered cover and the all-tag
maximum are both included: no tail or mean is assumed additionally. -/
theorem entrance_mean_of_debt
    (hDebt : ConcreteBarrierDebt) (hPeace : FreshPeaceAfterExtinction)
    {p c1 n : Nat} (x : Config p c1 n) (hp : 2 ≤ p) (hcal : 12 ≤ c1)
    (hn : 4 ≤ n) (hnd : ¬ p ∣ n) :
    IIDExpectedHittingTimeAtMost step QuietEntrance x (151*n^2) := by
  let i : Fin n := ⟨0, by omega⟩
  let project := fun s : AllObs p c1 n => (s i).config
  let target := fun s : AllObs p c1 n => allEnded s ∧ QuietEntrance (project s)
  have hx (x : Config p c1 n) (hm : MCOV x) (hc : COV x) :
      IIDExpectedHittingTimeAtMost allAdvance target (allInit x) (150*n^2) := by
    have hbase := concreteAllTags_mean_of_tail (concreteTagTail_of_debt hDebt)
      x hp hcal hn hnd hm hc
    let good := fun s : AllObs p c1 n => ∃ w, trackAll (allInit x) w = s
    have hnext (s : AllObs p c1 n) (e : Fin n) (hs : good s) : good (allAdvance s e) := by
      obtain ⟨w,rfl⟩ := hs
      exact ⟨w++[e], by rw [trackAll_append]; rfl⟩
    have hstop (s : AllObs p c1 n) (hs : good s) : target s ↔ allEnded s := by
      constructor
      · exact And.left
      · intro hd
        obtain ⟨w,rfl⟩ := hs
        have hproj : project (trackAll (allInit x) w) = run x w :=
          allTrack_config (allInit x) i w
        have ⟨hm',hc'⟩ := cover_run hn x ⟨hm,hc⟩ w
        have hmark := covered_mark_exists_of_not_dvd (run x w) i hm' hnd
        exact ⟨hd, hproj ▸ ⟨hm',hc',hmark,hPeace x w hp hcal hn hnd hm hc hd⟩⟩
    intro t
    rw [hitCost_equiv_on_invariant allAdvance target allEnded good
      hnext hstop t (allInit x) ⟨[],rfl⟩]
    exact hbase t
  have hfinal := EntranceCover.physical_after_cover_bound hn allAdvance allInit
    target QuietEntrance project (fun _ => rfl)
    (fun s e => projection_step (s i) e)
    (fun _ h => h.2) (150*n^2) hx x
  have heq : n*n+150*n^2 = 151*n^2 := by
    rw [show n*n = n^2 by rw [Nat.pow_succ,Nat.pow_one]]
    omega
  rwa [heq] at hfinal

end L4

#print axioms L4.allTrack_config
#print axioms L4.cover_run
#print axioms L4.hitCost_equiv_on_invariant
#print axioms L4.entrance_mean_of_debt

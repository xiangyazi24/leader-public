import Leader.L4.ShortSequentialClean

namespace L4.SequentialMarkClock

variable {X A J : Type} {n : Nat}

/-- No proper prefix of this segment satisfies the monitored goal. -/
def ClearBefore (stepZ : X × A → Fin n → X × A) (goal : X × A → Prop) :
    X × A → List (Fin n) → Prop
  | _, [] => True
  | z, e::w => ¬ goal z ∧ ClearBefore stepZ goal (stepZ z e) w

/-- Ordered nonempty receipts, each ending at that phase's *first* hit
from its own fresh observer cut. -/
def FirstHitReceipts (phase : J → X × A → Fin n → X × A)
    (goal : J → X × A → Prop) (fresh : A) :
    List J → X × A → List (Fin n) → Prop
  | [], _, _ => True
  | j::js, x, w => ∃ u v : List (Fin n), w = u ++ v ∧ u ≠ [] ∧
      ClearBefore (phase j) (goal j) x u ∧ goal j (run (phase j) x u) ∧
      FirstHitReceipts phase goal fresh js ((run (phase j) x u).1, fresh) v

def BeforeCurrent (goal : J → X × A → Prop) (z : State X A J) : Prop :=
  match z.todo with
  | [] => True
  | j::_ => ¬ goal j (z.raw,z.aux)

theorem first_hit_receipts_of_finished (advance : X → Fin n → X)
    (phase : J → X × A → Fin n → X × A)
    (goal : J → X × A → Prop) (fresh : A)
    (fresh_not_goal : ∀ j x, ¬ goal j (x,fresh))
    (z : State X A J) (w : List (Fin n)) (start_before : BeforeCurrent goal z)
    (done : finished (run (step advance phase goal fresh) z w)) :
    FirstHitReceipts phase goal fresh z.todo (z.raw,z.aux) w := by
  classical
  induction w generalizing z with
  | nil =>
    have h : z.todo = [] := done
    simp [FirstHitReceipts,h]
  | cons e w ih =>
    cases z with
    | mk x a todo =>
      cases todo with
      | nil => trivial
      | cons j js =>
        have HH : ¬goal j (x,a) := start_before
        have D : finished (run (step advance phase goal fresh)
          (step advance phase goal fresh ⟨x,a,j::js⟩ e) w) := done
        by_cases H : goal j (phase j (x,a) e)
        · rw [show step advance phase goal fresh ⟨x,a,j::js⟩ e =
              ⟨(phase j (x,a) e).1,fresh,js⟩ by simp [step,H]] at D
          have Before : BeforeCurrent goal
              ⟨(phase j (x,a) e).1,fresh,js⟩ := by
            cases js with
            | nil => trivial
            | cons k rest => exact fresh_not_goal k _
          exact ⟨[e],w,rfl,by simp,⟨HH,trivial⟩,H,ih _ Before D⟩
        · rw [show step advance phase goal fresh ⟨x,a,j::js⟩ e =
              ⟨(phase j (x,a) e).1,(phase j (x,a) e).2,j::js⟩ by simp [step,H]] at D
          have B : BeforeCurrent goal ⟨(phase j (x,a) e).1,(phase j (x,a) e).2,j::js⟩ := by
            change ¬goal j ((phase j (x,a) e).1,(phase j (x,a) e).2)
            simpa only [Prod.eta] using H
          obtain ⟨u,v,E,_,Cu,U,V⟩ := ih _ B D
          exact ⟨e::u,v,congrArg (List.cons e) E,by simp,⟨HH,Cu⟩,U,V⟩

end L4.SequentialMarkClock

namespace L4.ShortAllOwnerClock
set_option exponentiation.threshold 8100
open PhysicalCustody ShortResetMIS1Ring ShortSequentialClean

/-- Enumerate the entire frozen selected-H1 set in physical index order. -/
def roots {n : Nat} (h : Fin n → Bool) : List (Fin n) :=
  (List.finRange n).filter h

theorem mem_roots {n : Nat} (h : Fin n → Bool) (r : Fin n) :
    r ∈ roots h ↔ h r = true := by simp [roots]

theorem roots_nodup {n : Nat} (h : Fin n → Bool) : (roots h).Nodup :=
  (List.nodup_finRange n).filter _

theorem roots_length_le {n : Nat} (h : Fin n → Bool) : (roots h).length ≤ n := by
  have L := List.length_filter_le h (List.finRange n)
  simpa only [roots,List.length_finRange] using L

/-- A quadratic clock for one genuine historical reset receipt per
selected H1 owner, not a simultaneously empty physical state. -/
theorem all_owner_expected {s n : Nat} (N : 9 < n) (x : Raw s n) (X : H2Ready x) :
    ∃ cs : List (Certified s n (header x)),
      cs.map (fun c=>c.chart.root) = roots (header x) ∧
        Height.IIDExpectedHittingTimeAtMost next SequentialMarkClock.finished
          (SequentialMarkClock.start false cs x) ((10^8095+19)*n^2) := by
  obtain ⟨cs, E⟩ := chart_list N x X (roots (header x))
    (fun r R=>(mem_roots (header x) r).mp R)
  refine ⟨cs,E,?_⟩
  have L : cs.length ≤ n := by
    have T := congrArg List.length E
    rw [List.length_map] at T
    rw [T]
    exact roots_length_le (header x)
  have U := expected (by omega : 5 ≤ n) x ⟨X,fun _=>rfl⟩ cs
  have B : cs.length * baseCost n ≤ (10^8095+19)*n^2 := calc
    _ ≤ n * baseCost n := Nat.mul_le_mul_right _ L
    _ = _ := by unfold baseCost; rw [Nat.pow_two]; ac_rfl
  intro t
  exact Nat.le_trans (U t) (Nat.mul_le_mul_right _ B)

/-- The stopped monitor is driven by every original mark and yields
ordered nonempty receipt segments on that very tape. No owner is
required still to be in its completion state at the final cut. -/
theorem all_owner_actual_receipts {s n : Nat} {h : Fin n → Bool} (x : Raw s n)
    (cs : List (Certified s n h)) (w : List (Fin n))
    (E : cs.map (fun c=>c.chart.root) = roots h)
    (D : SequentialMarkClock.finished
      (SequentialMarkClock.run next (SequentialMarkClock.start false cs x) w)) :
    (SequentialMarkClock.run next (SequentialMarkClock.start false cs x) w).raw =
        SequentialMarkClock.run (rawNext s) x w ∧
      (∀ r : Fin n, h r = true ↔ ∃ c∈cs, c.chart.root = r) ∧
      (cs.map (fun c=>c.chart.root)).Nodup ∧
      SequentialMarkClock.Receipts phase goal false cs (x,false) w := by
  refine ⟨SequentialMarkClock.run_raw (rawNext s) phase goal false (fun _ _ _=>rfl) _ _,
    ?_, ?_, actual_receipts x cs w D⟩
  · intro r
    rw [← mem_roots h r, ←E]
    exact List.mem_map
  · rw [E]
    exact roots_nodup h

theorem all_owner_first_hit_receipts {s n : Nat} {h : Fin n → Bool} (x : Raw s n)
    (cs : List (Certified s n h)) (w : List (Fin n))
    (E : cs.map (fun c=>c.chart.root) = roots h)
    (D : SequentialMarkClock.finished
      (SequentialMarkClock.run next (SequentialMarkClock.start false cs x) w)) :
    (∀ r : Fin n, h r = true ↔ ∃ c∈cs, c.chart.root = r) ∧
    SequentialMarkClock.FirstHitReceipts phase goal false cs (x,false) w := by
  have no : ∀ (c : Certified s n h) (y : Raw s n), ¬ goal c (y,false) :=
    fun _ _ Y=>Bool.noConfusion Y.1
  have before : SequentialMarkClock.BeforeCurrent goal (SequentialMarkClock.start false cs x) := by
    cases cs with
    | nil => trivial
    | cons c rest => exact no c x
  exact ⟨(all_owner_actual_receipts x cs w E D).2.1,
    SequentialMarkClock.first_hit_receipts_of_finished (rawNext s) phase goal false
      no _ w before D⟩

end L4.ShortAllOwnerClock

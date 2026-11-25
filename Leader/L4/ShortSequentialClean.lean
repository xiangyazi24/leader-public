import Leader.L4.ShortArbitraryClean
import Leader.L4.SequentialMarkClock

namespace L4.ShortSequentialClean
set_option exponentiation.threshold 8100
open PhysicalCustody ShortResetMIS1Ring ShortResetCycle L4.Height

def Fiber {s n : Nat} (h : Fin n → Bool) (x : Raw s n) : Prop :=
  H2Ready x ∧ ∀ q, header x q=h q

def baseCost (n : Nat) : Nat := (10^8095+19)*n

structure Certified (s n : Nat) (h : Fin n → Bool) where
  chart : Chart h
  uniform : ∀ y : Raw s n, Fiber h y →
    Height.IIDExpectedHittingTimeAtMost (ShortActualIssueClock.step chart)
      (ShortActualIssueClock.Goal chart) (y,false) (baseCost n)

def phase {s n : Nat} {h : Fin n → Bool} (c : Certified s n h) :=
  ShortActualIssueClock.step (s:=s) c.chart

def goal {s n : Nat} {h : Fin n → Bool} (c : Certified s n h) :=
  ShortActualIssueClock.Goal (s:=s) c.chart

noncomputable def next {s n : Nat} {h : Fin n → Bool} :=
  SequentialMarkClock.step (rawNext s) (phase (s:=s) (h:=h)) goal false

theorem actual_raw_step {s n : Nat} {h : Fin n → Bool}
    (z : SequentialMarkClock.State (Raw s n) Bool (Certified s n h)) (e : Fin n) :
    (next z e).raw=rawNext s z.raw e :=
  SequentialMarkClock.step_raw (rawNext s) phase goal false (fun _ _ _=>rfl) z e

/-- The history monitor advances to the next chart on a genuine
old-ISSUE0 reset's completion. Other charts need not remain complete. -/
theorem expected {s n : Nat} {h : Fin n → Bool} (N : 5≤n)
    (x : Raw s n) (X : Fiber h x) (cs : List (Certified s n h)) :
    Height.IIDExpectedHittingTimeAtMost next SequentialMarkClock.finished
      (SequentialMarkClock.start false cs x) (cs.length * baseCost n) := by
  exact SequentialMarkClock.expected (rawNext s) phase goal false (Fiber h)
    (fun _ _ _=>rfl)
    (fun y e Y=>⟨h2_ready_closed N y e Y.1,
      fun i=>(H1.raw_h1_selected_frozen N y e i Y.1.1).trans (Y.2 i)⟩)
    (baseCost n) (fun c y _ Y=>Bool.noConfusion Y.1)
    (fun c y Y=>c.uniform y Y) cs x X

theorem chart_list {s n : Nat} (N : 9<n) (x : Raw s n) (X : H2Ready x)
    (rs : List (Fin n)) (H : ∀ r∈rs, header x r=true) :
    ∃ cs : List (Certified s n (header x)), cs.map (fun c=>c.chart.root)=rs := by
  induction rs with
  | nil => exact ⟨[],rfl⟩
  | cons r rs ih =>
    obtain ⟨cs,E⟩ := ih (fun q Q=>H q (List.mem_cons_of_mem r Q))
    obtain ⟨c,R,_,U⟩ :=
      ShortArbitraryClean.actual_owner_clean_mean x X r (H r (by simp)) N
    let C : Certified s n (header x) := ⟨c, fun y Y=>U y Y.1 Y.2⟩
    exact ⟨C::cs,by simp only [List.map_cons,R,E,C]⟩

/-- Any prescribed list of five selected roots (duplicates allowed) has
five ordered historical clean receipts within the sharper mean. -/
theorem five_expected {s n : Nat} (N : 9<n) (x : Raw s n) (X : H2Ready x)
    (rs : List (Fin n)) (L : rs.length=5) (H : ∀ r∈rs, header x r=true) :
    ∃ cs : List (Certified s n (header x)), cs.map (fun c=>c.chart.root)=rs ∧
      Height.IIDExpectedHittingTimeAtMost next SequentialMarkClock.finished
        (SequentialMarkClock.start false cs x) (5*(10^8095+19)*n) := by
  obtain ⟨cs,E⟩ := chart_list N x X rs H
  have len : cs.length=5 := by simpa only [List.length_map,L] using congrArg List.length E
  have U := expected (by omega : 5≤n) x ⟨X,fun _=>rfl⟩ cs
  rw [len,baseCost] at U
  have M : 5*((10^8095+19)*n)=5*(10^8095+19)*n := (Nat.mul_assoc _ _ _).symm
  rw [M] at U
  exact ⟨cs,E,U⟩

theorem actual_receipts {s n : Nat} {h : Fin n → Bool} (x : Raw s n)
    (cs : List (Certified s n h)) (w : List (Fin n))
    (D : SequentialMarkClock.finished
      (SequentialMarkClock.run next (SequentialMarkClock.start false cs x) w)) :
    SequentialMarkClock.Receipts phase goal false cs (x,false) w :=
  SequentialMarkClock.receipts_of_finished (rawNext s) phase goal false _ w D

#print axioms actual_receipts
#print axioms actual_raw_step
#print axioms expected
#print axioms chart_list
#print axioms five_expected
end L4.ShortSequentialClean

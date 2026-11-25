import Leader.L4.ShortAllOwnerClock
import Leader.L4.MonitorRawBridge

namespace L4.ShortAllOwnerSound
set_option exponentiation.threshold 8100
open PhysicalCustody ShortResetMIS1Ring ShortSequentialClean ShortAllOwnerClock
open SequentialMarkClock

/-- Finished state relifts to ordered first-hit historical receipts on
this very tape. The endpoint is the actual raw run; no current
owner-safety predicate is hidden in this interface. -/
def HistoricalOn {s n : Nat} (x : Raw s n) (w : List (Fin n)) (y : Raw s n) : Prop :=
  y=rawRun x w ∧ ∃ cs : List (Certified s n (header x)),
    cs.map (fun c=>c.chart.root)=roots (header x) ∧
    (∀ r : Fin n, header x r=true ↔ ∃ c∈cs, c.chart.root=r) ∧
    FirstHitReceipts phase goal false cs (x,false) w

theorem history_on_actual_tape {s n : Nat} (x : Raw s n)
    (cs : List (Certified s n (header x))) (w : List (Fin n))
    (E : cs.map (fun c=>c.chart.root)=roots (header x))
    (D : finished (SequentialMarkClock.run next (start false cs x) w)) :
    HistoricalOn x w (SequentialMarkClock.run next (start false cs x) w).raw := by
  have G := all_owner_actual_receipts x cs w E D
  have F := all_owner_first_hit_receipts x cs w E D
  have same (u : Raw s n) (v : List (Fin n)) :
      SequentialMarkClock.run (rawNext s) u v=rawRun u v := by
    induction v generalizing u with
    | nil => rfl
    | cons e v ih => exact ih (rawNext s u e)
  exact ⟨G.1.trans (same x w),cs,E,F.1,F.2⟩

/-- A proper raw terminal-soundness input. In particular this is not
proved for current OwnerGood by the sequential reset-clock theorem. -/
def ReceiptSound {s n : Nat} (x : Raw s n) (good : Raw s n→Prop) : Prop :=
  ∀ w y, HistoricalOn x w y → good y

theorem word_sound_of_receipts {s n : Nat} (x : Raw s n) (good : Raw s n→Prop)
    (S : ReceiptSound x good) (cs : List (Certified s n (header x)))
    (E : cs.map (fun c=>c.chart.root)=roots (header x)) (w : List (Fin n))
    (D : finished (SequentialMarkClock.run next (start false cs x) w)) :
    good (SequentialMarkClock.run next (start false cs x) w).raw :=
  S w _ (history_on_actual_tape x cs w E D)

theorem word_sound_raw_of_receipts {s n : Nat} (x : Raw s n) (good : Raw s n→Prop)
    (S : ReceiptSound x good) (cs : List (Certified s n (header x)))
    (E : cs.map (fun c=>c.chart.root)=roots (header x)) (w : List (Fin n))
    (D : finished (SequentialMarkClock.run next (start false cs x) w)) :
    good (rawRun x w) := by
  have H := history_on_actual_tape x cs w E D
  exact H.1 ▸ S w _ H


/-- Concrete consumer for all selected H1 owners. It does not
assert that historical receipts imply a currently valid epoch; that
substantive protocol lemma is the explicit ReceiptSound input. -/
theorem raw_expected_of_receipts {s n : Nat} (N : 9<n) (x : Raw s n)
    (X : H2Ready x) (good : Raw s n→Prop) (S : ReceiptSound x good) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) good x ((10^8095+19)*n^2) := by
  obtain ⟨cs,E,B⟩ := all_owner_expected N x X
  let startZ := start false cs x
  have H := MonitorRawBridge.expected_of_monitor_words (rawNext s)
    (next (s:=s) (h:=header x)) SequentialMarkClock.State.raw finished good
    (SequentialMarkClock.step_raw (rawNext s) phase goal false (fun _ _ _=>rfl))
    startZ (fun w D=>?_ ) ((10^8095+19)*n^2) B
  · exact H
  · have G := word_sound_of_receipts x good S cs E w D
    have R := (all_owner_actual_receipts x cs w E D).1
    rwa [R] at G

/-- An anchored raw history target, sound for first hitting as an
existential, but not a substitute for the actual monitor state. -/
def HistoricalEndpoint {s n : Nat} (x y : Raw s n) : Prop :=
  ∃ w, HistoricalOn x w y

theorem historical_endpoint_expected {s n : Nat} (N : 9<n) (x : Raw s n)
    (X : H2Ready x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (HistoricalEndpoint x) x
      ((10^8095+19)*n^2) :=
  raw_expected_of_receipts N x X (HistoricalEndpoint x) (fun w _ H=>⟨w,H⟩)

/-- The projection of an unrestricted fabricated observer is
identically true, even before any physical mark. -/
theorem bare_finished_projection {X A J : Type} (a : A) (x : X) :
    ∃ z : SequentialMarkClock.State X A J, z.raw=x ∧ finished z :=
  ⟨⟨x,a,[]⟩,rfl,rfl⟩

private def toyRaw (_ : Unit) (_ : Fin 1) : Unit := ()
private def toyPhase (_ : Unit) (x : Unit × Bool) (_ : Fin 1) : Unit × Bool :=
  (x.1,true)
private def toyGoal (_ : Unit) (x : Unit × Bool) : Prop := x.2=true
private noncomputable def toyNext := SequentialMarkClock.step toyRaw toyPhase toyGoal false
private def toyStart := start false [()] ()

/-- Even an anchored successful alternative history can project back
to the initial raw state while the actual empty observer history has
not finished. This does not refute a first-hit bound, only the claim
that this existential identifies the actual receipt history. -/
theorem anchored_finished_can_hold_before_receipt :
    (∃ w : List (Fin 1), w≠[] ∧ (SequentialMarkClock.run toyNext toyStart w).raw=toyStart.raw ∧
      finished (SequentialMarkClock.run toyNext toyStart w)) ∧ ¬finished (SequentialMarkClock.run toyNext toyStart []) := by
  constructor
  · refine ⟨[0],by simp,Subsingleton.elim _ _,?_⟩
    simp [toyNext,toyStart,start,SequentialMarkClock.step,SequentialMarkClock.run,toyPhase,toyGoal,finished]
  · simp [toyStart,start,SequentialMarkClock.run,finished]

#print axioms history_on_actual_tape
#print axioms word_sound_raw_of_receipts
#print axioms raw_expected_of_receipts
#print axioms historical_endpoint_expected
#print axioms bare_finished_projection
#print axioms anchored_finished_can_hold_before_receipt
end L4.ShortAllOwnerSound

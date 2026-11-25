import Leader.L4.ResetReturnIID
import Leader.L4.MonitorRawBridge
import Leader.L4.AllSizeComposition

namespace L4.ReportResetEventClock

variable {X : Type} {n : Nat}

open Classical

/-- Counts actual events strictly before first hit, stopping on the
same tape. Events on the finishing mark need no prelaunch credit. -/
noncomputable def events (step : X→Fin n→X) (stop : X→Prop)
    (progress : X→Fin n→Bool) : X→List (Fin n)→Nat
  | _,[] => 0
  | x,e::w =>
    if stop x ∨ stop (step x e) then 0
    else (progress x e).toNat + events step stop progress (step x e) w

/-- A globally bounded event count and a predictable nominated next
label suffice for mean n*(C+1) on the actual raw alphabet. The
nominated label may change after every mark; no forcing word is used. -/
theorem expected_of_counted_events (step : X→Fin n→X) (stop good : X→Prop)
    (progress : X→Fin n→Bool)
    (closed : ∀ y e,good y→good (step y e))
    (nominate : ∀ y,good y→¬stop y→∃ e,stop (step y e) ∨ progress y e=true)
    (x : X) (G : good x) (C : Nat)
    (budget : ∀ w,events step stop progress x w≤C) :
    Height.IIDExpectedHittingTimeAtMost step stop x (n*(C+1)) := by
  let Live := fun y r => good y ∧ ¬stop y ∧
    ∀ w,events step stop progress y w + 1 ≤ r
  have pos (y : X) (r : Nat) (H : Live y r) : 0<r := by
    have T := H.2.2 []
    simp only [events,Nat.zero_add] at T
    omega
  have moves (y : X) (r : Nat) (H : Live y r) :
      ∃ d : Fin n, ∀ e : Fin n, stop (step y e) ∨
        ∃ r',Live (step y e) r' ∧ r'≤r ∧ (e=d→r'<r) := by
    obtain ⟨d,D⟩ := nominate y H.1 H.2.1
    refine ⟨d,fun e=>?_⟩
    by_cases A : stop (step y e)
    · exact .inl A
    · let a := (progress y e).toNat
      refine .inr ⟨r-a,⟨closed y e H.1,A,?_⟩,Nat.sub_le _ _,?_⟩
      · intro w
        have V := H.2.2 (e::w)
        simp only [events,H.2.1,A,or_self,if_false] at V
        change a + events step stop progress (step y e) w + 1 ≤ r at V
        omega
      · intro E
        subst e
        have T := D.resolve_left A
        have B : a=1 := by simp [a,T]
        have P := pos y r H
        omega
  apply ResetReturnIID.iid_of_relational_rank step stop Live pos moves x (C+1)
  by_cases H : stop x
  · exact .inl H
  · exact .inr ⟨G,H,fun w=>Nat.succ_le_succ (budget w)⟩

/-- Pairing with the exact same-tape bridge #7 keeps the event ghost
anchored to the physical stream and preserves the coefficient. -/
theorem raw_expected_from_event_monitor {M : Type}
    (raw : X→Fin n→X) (step : M→Fin n→M)
    (project : M→X) (stop good : M→Prop) (goal : X→Prop)
    (progress : M→Fin n→Bool)
    (relift : ∀ y e,project (step y e)=raw (project y) e)
    (closed : ∀ y e,good y→good (step y e))
    (nominate : ∀ y,good y→¬stop y→∃ e,stop (step y e) ∨ progress y e=true)
    (start : M) (G : good start) (C : Nat)
    (budget : ∀ w,events step stop progress start w≤C)
    (sound : ∀ w,stop (SequentialMarkClock.run step start w) →
      goal (SequentialMarkClock.run raw (project start) w)) :
    IIDExpectedHittingTimeAtMost raw goal (project start) (n*(C+1)) :=
  MonitorRawBridge.expected_of_monitor_words raw step project stop goal relift start sound _
    (expected_of_counted_events step stop good progress closed nominate start G C budget)

def positions (t : Nat) : Nat := 4*t+5

def Cpre (L t : Nat) : Nat :=
  let P := positions t
  2*P+2+(L+P)*(L+2)+(2*L+P)*L+L+L*(L+P)

def resetCoefficient (B t : Nat) : Nat :=
  10*(B+4*t+7)^2+2*B+1

/-- The Cpre polynomial pays separate event labels for source,
forward/race, reverse, and trail clear. This arithmetic does not
establish conservation of those labels in the physical row. -/
theorem cpre_le {L B t : Nat} (W : L≤B) :
    Cpre L t ≤ 10*(B+4*t+7)^2 := by
  let P := positions t
  let q := B+P+2
  have Q : 1≤q := by unfold q; omega
  have Q2 : q≤q*q := by simpa using Nat.mul_le_mul_left q Q
  have A : (L+P)*(L+2)≤q*q := Nat.mul_le_mul
    (by unfold q; omega) (by unfold q; omega)
  have B' : (2*L+P)*L≤(2*q)*q := Nat.mul_le_mul
    (by unfold q; omega) (by unfold q; omega)
  have D : L*(L+P)≤q*q := Nat.mul_le_mul
    (by unfold q; omega) (by unfold q; omega)
  have Q' : q=B+4*t+7 := by unfold q P positions; omega
  change 2*P+2+(L+P)*(L+2)+(2*L+P)*L+L+L*(L+P) ≤ _
  have small : 2*P+2+L≤3*q := by unfold q; omega
  rw [←Q',Nat.pow_two]
  rw [Nat.mul_assoc] at B'
  omega

/-- Chronological first launch then genuine consume; applying it
requires the two monitors' semantic handoff, rather than credit for
an arbitrary D already present at the initial state. -/
theorem after_launch {L B t : Nat} (step : X→Fin n→X)
    (launch receipt : X→Prop) (W : L≤B) (x : X)
    (before : IIDExpectedHittingTimeAtMost step launch x (n*(Cpre L t+1)))
    (after : ∀ y,launch y→IIDExpectedHittingTimeAtMost step receipt y (2*L*n)) :
    IIDExpectedHittingTimeAtMost step receipt x (n*resetCoefficient B t) := by
  have V := AllSizeComposition.additive_stage step launch receipt _ _ x before after
  have N : n*(Cpre L t+1)+2*L*n ≤ n*resetCoefficient B t := by
    have H : Cpre L t+1+2*L≤resetCoefficient B t := by
      have := cpre_le (t:=t) W
      unfold resetCoefficient
      omega
    calc
      _ = n*(Cpre L t+1+2*L) := by
        rw [Nat.mul_comm (2*L) n]
        simp only [Nat.mul_add]
      _ ≤ _ := Nat.mul_le_mul_left _ H
  intro h
  exact Nat.le_trans (V h) (Nat.mul_le_mul_right _ N)

end L4.ReportResetEventClock

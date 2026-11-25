import Leader.L4.ReportResetEventClock
import Leader.L4.ShortAllOwnerClock
import Leader.L4.AdviceBandRadiusBudget

namespace L4.ReportResetCovers
open SequentialMarkClock ReportResetEventClock
open AllSizeProtocol

variable {X A J : Type} {n : Nat}

/-- A cover whose tape ends at its last actual first-hit receipt.
The empty list consumes no marks, so a trailing suffix is not silently
included in the cut between the two covers. -/
def Exact (phase : J→X×A→Fin n→X×A) (goal : J→X×A→Prop) (fresh : A) :
    List J→X×A→List (Fin n)→Prop
  | [],_,w => w=[]
  | j::js,x,w =>
    ∃ u v : List (Fin n), w=u++v ∧ u≠[] ∧
      ClearBefore (phase j) (goal j) x u ∧ goal j (SequentialMarkClock.run (phase j) x u) ∧
      Exact phase goal fresh js ((SequentialMarkClock.run (phase j) x u).1,fresh) v

private theorem runAppend {Z : Type} (step : Z→Fin n→Z) (x : Z)
    (u v : List (Fin n)) : SequentialMarkClock.run step x (u++v)=SequentialMarkClock.run step (SequentialMarkClock.run step x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (step x e)

/-- The first list is consumed to its exact cut. The second list
starts with a fresh observer at that actual physical endpoint. -/
theorem split_first_cut (advance : X→Fin n→X)
    (phase : J→X×A→Fin n→X×A) (goal : J→X×A→Prop) (fresh : A)
    (physical : ∀ j w e,(phase j w e).1=advance w.1 e)
    (first second : List J) (x : X) (w : List (Fin n))
    (R : FirstHitReceipts phase goal fresh (first++second) (x,fresh) w) :
    ∃ u v : List (Fin n), w=u++v ∧
      Exact phase goal fresh first (x,fresh) u ∧
      FirstHitReceipts phase goal fresh second (SequentialMarkClock.run advance x u,fresh) v := by
  induction first generalizing x w with
  | nil => exact ⟨[],w,rfl,rfl,R⟩
  | cons j js ih =>
    obtain ⟨a,b,E,N,C,G,H⟩ := R
    have Hraw : (SequentialMarkClock.run (phase j) (x,fresh) a).1=SequentialMarkClock.run advance x a :=
      phase_run_raw advance phase physical j (x,fresh) a
    obtain ⟨u,v,L,U,V⟩ := ih _ b H
    refine ⟨a++u,v,?_,⟨a,u,rfl,N,C,G,U⟩,?_⟩
    · rw [E,L,List.append_assoc]
    · rwa [runAppend,←Hraw]

theorem two_covers_cuts (advance : X→Fin n→X)
    (phase : J→X×A→Fin n→X×A) (goal : J→X×A→Prop) (fresh : A)
    (physical : ∀ j w e,(phase j w e).1=advance w.1 e)
    (initial : ∀ j x,¬goal j (x,fresh))
    (sites : List J) (x : X) (w : List (Fin n))
    (done : finished (SequentialMarkClock.run (SequentialMarkClock.step advance phase goal fresh) (start fresh (sites++sites) x) w)) :
    ∃ u v tail : List (Fin n), w=(u++v)++tail ∧
      Exact phase goal fresh sites (x,fresh) u ∧
      Exact phase goal fresh sites (SequentialMarkClock.run advance x u,fresh) v := by
  have B : BeforeCurrent goal (start fresh (sites++sites) x) := by
    cases H : sites++sites with
    | nil => trivial
    | cons j js => exact initial _ _
  have F := first_hit_receipts_of_finished advance phase goal fresh initial _ w B done
  obtain ⟨u,q,W,U,Q⟩ := split_first_cut advance phase goal fresh physical sites sites x w F
  obtain ⟨v,tail,E,V,_⟩ := split_first_cut advance phase goal fresh physical sites []
    (SequentialMarkClock.run advance x u) q (by simpa only [List.append_nil] using Q)
  exact ⟨u,v,tail,by rw [W,E,List.append_assoc],U,V⟩

/-- Conditional raw mean for two chronological covers, given a
uniform real first-receipt clock and terminal soundness of the cuts. -/
theorem raw_two_covers_mean (advance : X→Fin n→X)
    (phase : J→X×A→Fin n→X×A) (goal : J→X×A→Prop) (fresh : A)
    (Good Done : X→Prop)
    (physical : ∀ j w e,(phase j w e).1=advance w.1 e)
    (closed : ∀ x e,Good x→Good (advance x e))
    (initial : ∀ j x,¬goal j (x,fresh))
    (sites : List J) (Q : sites.length≤n) (K : Nat)
    (budget : ∀ j x,Good x→Height.IIDExpectedHittingTimeAtMost
      (phase j) (goal j) (x,fresh) (n*K))
    (x : X) (G : Good x)
    (sound : ∀ u v tail,Exact phase goal fresh sites (x,fresh) u →
      Exact phase goal fresh sites (SequentialMarkClock.run advance x u,fresh) v →
      Done (SequentialMarkClock.run advance x ((u++v)++tail))) :
    IIDExpectedHittingTimeAtMost advance Done x (2*K*n^2) := by
  let m := SequentialMarkClock.step advance phase goal fresh
  let z := start fresh (sites++sites) x
  have V := SequentialMarkClock.expected advance phase goal fresh Good physical closed
    (n*K) (fun j y _=>initial j y) budget (sites++sites) x G
  have H := MonitorRawBridge.expected_of_monitor_words advance m (fun y=>y.raw) finished
    Done (step_raw advance phase goal fresh physical) z
    (fun w D=>by
      obtain ⟨u,v,tail,E,U,V⟩ := two_covers_cuts advance phase goal fresh physical initial sites x w D
      subst w
      exact sound u v tail U V) _ V
  have upper : (sites++sites).length*(n*K)≤2*K*n^2 := by
    rw [List.length_append]
    calc
      _ ≤ (n+n)*(n*K) := Nat.mul_le_mul_right _ (Nat.add_le_add Q Q)
      _ = _ := by rw [←Nat.two_mul,Nat.pow_two]; ac_rfl
  intro t
  exact Nat.le_trans (H t) (Nat.mul_le_mul_right _ upper)

def E1 : Nat := 2*resetCoefficient 243 1

def E2 (s : Nat) : Nat :=
  2*resetCoefficient (243*(2*s+1)) (ell (PhysicalCustody.radiusTwo s+1))

theorem E1_value : E1=2*(10*254^2+487) := by decide

theorem E2_polynomial {s : Nat} (S : 6≤s) :
    E2 s≤2*(10*(490*s+254)^2+486*(2*s+1)+1) := by
  have C := AdviceBandRadiusBudget.t2_le S
  have E : 243*(2*s+1)+4*ell (PhysicalCustody.radiusTwo s+1)+7≤490*s+254 := by omega
  have F := Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left E 2)
  unfold E2 resetCoefficient
  apply Nat.mul_le_mul_left
  have H : 2*(243*(2*s+1))=486*(2*s+1) := by rw [←Nat.mul_assoc]
  rw [H]
  omega

#print axioms split_first_cut
#print axioms two_covers_cuts
#print axioms raw_two_covers_mean
#print axioms E1_value
#print axioms E2_polynomial
end L4.ReportResetCovers

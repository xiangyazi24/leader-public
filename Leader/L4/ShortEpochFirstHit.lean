import Leader.L4.ShortObservedResetRelease
import Leader.L4.ShortAllOwnerSound

namespace L4.ShortEpochFirstHit
open PhysicalCustody ShortResetMIS1Ring ShortResetCycle
open ShortSequentialClean ShortObservedResetRelease ShortAllOwnerSound
open SequentialMarkClock (FirstHitReceipts ClearBefore)

private theorem raw_append {s n : Nat} (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (rawNext s x e)

/-- The actual observed Goal is carried separately from Parked. The
replacement for E4 cannot weaken this receipt to ReleasedReceipts. -/
theorem first_goal_prefix {s n : Nat} {h : Fin n→Bool}
    (cs : List (Certified s n h)) (x : Raw s n) (w : List (Fin n))
    (R : FirstHitReceipts phase goal false cs (x,false) w)
    (c : Certified s n h) (M : c∈cs) :
    ∃ a u v : List (Fin n), w=a++u++v ∧ u≠[] ∧
      BeforeGoal c.chart (rawRun x a,false) u ∧
      ShortActualIssueClock.Goal c.chart (ShortObservedResetRelease.run c.chart (rawRun x a,false) u) := by
  induction cs generalizing x w with
  | nil => exact (List.not_mem_nil M).elim
  | cons b bs ih =>
    obtain ⟨u,v,W,N,F,G,R'⟩ := R
    rcases List.mem_cons.mp M with E|E
    · subst b
      exact ⟨[],u,v,W,N,F,G⟩
    · change FirstHitReceipts phase goal false bs ((ShortObservedResetRelease.run b.chart (x,false) u).1,false) v at R'
      rw [observed_endpoint_is_literal] at R'
      obtain ⟨a,i,t,V,I,D,P⟩ := ih (rawRun x u) v R' E
      refine ⟨u++a,i,t,?_,I,?_,?_⟩
      · rw [W,V]
        simp only [List.append_assoc]
      · rwa [raw_append]
      · rwa [raw_append]

/-- A nondoor mark from Parked gives a concrete false-positive in the
weaker receipt predicate, while the true issue witness stays false. -/
theorem nondoor_parked_not_first_hit {s n : Nat} {h : Fin n→Bool}
    (c : Certified s n h) (x : Raw s n) (heads : ∀ q,header x q=h q)
    (P : ShortResetHelloSplice.Parked c.chart x)
    (e : Fin n) (E : e≠RearTrace.predecessor c.chart.root) :
    ReleasedReceipts [c] x [e] ∧
    ¬ShortActualIssueClock.Goal c.chart (ShortObservedResetRelease.run c.chart (x,false) [e]) := by
  have A : ¬ ShortActualIssueClock.Goal c.chart (ShortObservedResetRelease.run c.chart (x,false) [e]) := by
    simp [ShortObservedResetRelease.run,SequentialMarkClock.run,ShortActualIssueClock.step,ShortActualIssueClock.Goal,E]
  refine ⟨⟨[e],[],rfl,by simp,?_,ShortResetHelloSplice.parked_nondoor c.chart x heads P e E,trivial⟩,A⟩
  simp [BeforeGoal,ClearBefore,ShortActualIssueClock.Goal]

private theorem epoch_run {s n : Nat} {h : Fin n→Bool}
    (Epoch : Chart h→Raw s n→Prop)
    (step : ∀ c x e, Epoch c x→Epoch c (rawNext s x e))
    (c : Chart h) (x : Raw s n) (w : List (Fin n)) (G : Epoch c x) :
    Epoch c (rawRun x w) := by
  induction w generalizing x with
  | nil => exact G
  | cons e w ih => exact ih _ (step c x e G)

theorem current_epochs_of_first_hits {s n : Nat} {h : Fin n→Bool}
    (Epoch : Chart h→Raw s n→Prop)
    (seed : ∀ (c : Chart h) (x : Raw s n) (u : List (Fin n)),
      u≠[] → BeforeGoal c (x,false) u →
      ShortActualIssueClock.Goal c (ShortObservedResetRelease.run c (x,false) u) → Epoch c (rawRun x u))
    (step : ∀ c x e,Epoch c x→Epoch c (rawNext s x e))
    (cs : List (Certified s n h)) (x : Raw s n) (w : List (Fin n))
    (R : FirstHitReceipts phase goal false cs (x,false) w) :
    ∀ c∈cs,Epoch c.chart (rawRun x w) := by
  intro c M
  obtain ⟨a,u,v,W,N,F,P⟩ := first_goal_prefix cs x w R c M
  have G := seed c.chart (rawRun x a) u N F P
  rw [W,raw_append,raw_append]
  exact epoch_run Epoch step c.chart _ v G

theorem receipt_sound_of_true_goals {s n : Nat}
    (x : Raw s n) (good : Raw s n→Prop)
    (Epoch : Chart (header x)→Raw s n→Prop)
    (seed : ∀ (c : Chart (header x)) (z : Raw s n) (u : List (Fin n)),
      u≠[] → BeforeGoal c (z,false) u →
      ShortActualIssueClock.Goal c (ShortObservedResetRelease.run c (z,false) u) → Epoch c (rawRun z u))
    (step : ∀ c z e,Epoch c z→Epoch c (rawNext s z e))
    (assemble : ∀ (z : Raw s n) (cs : List (Certified s n (header x))),
      cs.map (fun c=>c.chart.root)=ShortAllOwnerClock.roots (header x) →
      (∀ c∈cs, Epoch c.chart z) → good z) :
    ReceiptSound x good := by
  rintro w y ⟨Y,cs,C,_,H⟩
  subst y
  exact assemble _ cs C (current_epochs_of_first_hits Epoch seed step cs x w H)

end L4.ShortEpochFirstHit

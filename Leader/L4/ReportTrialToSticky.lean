import Leader.L4.ReportQuietCovers

namespace L4.ReportTrialToSticky

variable {I : Type}

/-- If a site was tested at least once before the second-window test, its
last test accounts for its current visible bit. No conditional
independence or order of the first-window tests is needed. -/
theorem last_test (paint : Nat→I→Prop) (z : Nat→I→Bool)
    (i : I) (lo hi : Nat)
    (frame : ∀ t,lo≤t → t<hi → ¬paint t i → z (t+1) i=z t i)
    (exists_test : ∃ t,lo≤t ∧ t<hi ∧ paint t i) :
    ∃ t,lo≤t ∧ t<hi ∧ paint t i ∧ z (t+1) i=z hi i := by
  classical
  induction hi with
  | zero => obtain ⟨_,_,V,_⟩ := exists_test; omega
  | succ hi IH =>
    have L : lo≤hi := by
      obtain ⟨_,_,_,_⟩ := exists_test
      omega
    by_cases P : paint hi i
    · exact ⟨hi,L,by omega,P,rfl⟩
    · have H' : ∃ t,lo≤t ∧ t<hi ∧ paint t i := by
        obtain ⟨t,T,V,Q⟩ := exists_test
        have NE : t≠hi := fun E=>P (E ▸ Q)
        exact ⟨t,T,by omega,Q⟩
      have F : z (hi+1) i=z hi i := frame hi L (by omega) P
      obtain ⟨t,T,V,Q,E⟩ := IH (fun a A B=>frame a A (by omega)) H'
      exact ⟨t,T,by omega,Q,E.trans F.symm⟩

/-- Pointwise deterministic two-window reduction. A surviving nearby
centre is certified at its own last test; only if there is none do
we rely on the tested site's insertion. All events refer to the same
physical timeline. `certify` is the post-pulse quiet-cover adapter. -/
theorem sticky_of_two_windows (ball : I→I→Prop) (paint : Nat→I→Prop)
    (z : Nat→I→Bool) (lo endTime : Nat) (i : I) (test : Nat) (sticky : Prop)
    (Symm : ∀ j,ball i j→ball j i) (Refl : ball i i)
    (First : ∀ j,ball i j → j≠i → ∃ t,lo≤t ∧ t<test ∧ paint t j)
    (T : lo≤test) (End : test<endTime) (Second : paint test i)
    (Frame : ∀ t j,lo≤t → t<endTime → ¬paint t j → z (t+1) j=z t j)
    (Decision : ∀ t j,lo≤t → t≤test → t<endTime → ball i j → paint t j →
      (z (t+1) j=true ↔ ∀ k,ball j k → k≠j → z t k=false))
    (Certify : ∀ t j,lo≤t → t≤test → t<endTime → ball j i → paint t j →
      z (t+1) j=true → sticky) :
    sticky := by
  classical
  by_cases B : ∃ j,ball i j ∧ j≠i ∧ z test j=true
  · obtain ⟨j,Near,Ne,On⟩ := B
    obtain ⟨t,Lt,Bt,P,Q⟩ := last_test paint z j lo test
      (fun t L B => Frame t j L (by omega)) (First j Near Ne)
    exact Certify t j Lt (by omega) (by omega) (Symm j Near) P (Q.trans On)
  · have Insert : z (test+1) i=true := by
      apply (Decision test i T (Nat.le_refl _) End Refl Second).mpr
      intro j Near Ne
      cases E : z test j with
      | false => rfl
      | true => exact False.elim (B ⟨j,Near,Ne,E⟩)
    exact Certify test i T (Nat.le_refl _) End Refl Second Insert

/-- Isolation at the actual post-pulse cut. The pulse may coincide with
a report COMMIT, but a gate-disjoint physical label cannot paint a
second relevant gate on that mark. -/
theorem isolated_after_test [DecidableEq I] (ball : I→I→Prop) (paint : Nat→I→Prop)
    (z : Nat→I→Bool) (j : I) (t : Nat) (_P : paint t j) (On : z (t+1) j=true)
    (Decision : z (t+1) j=true ↔ ∀ k,ball j k → k≠j → z t k=false)
    (Exclusive : ∀ k,ball j k → k≠j → ¬paint t k)
    (Frame : ∀ k,ball j k → ¬paint t k → z (t+1) k=z t k) :
    ∀ k,ball j k → z (t+1) k = decide (k=j) := by
  classical
  intro k B
  by_cases E : k=j
  · subst k
    simpa using On
  · rw [Frame k B (Exclusive k B E),(Decision.mp On) k B E]
    simp [E]

end L4.ReportTrialToSticky

import Leader.L4.RearGeometry
import Leader.L4.RearSignalRows

namespace L4.RearTrace

/-- No one-signal in the intersection of the current open rear-to-tag
corridor and the sites actually visited by the advancing original tag. -/
def Swept {p c n : Nat} (x : Config p c n) (b : Fin n) (d N : Nat) : Prop :=
  (∀ k, k < d → k < N → (x (back b k)).signal ≠ .one) ∧
    (0 < N → (x b).signal = .zero)

theorem swept_initial {p c n : Nat} (x : Config p c n) (b : Fin n) (d : Nat) :
    Swept x b d 0 := by
  constructor <;> intros <;> omega

private theorem rn_ne {n : Nat} (hn : 4 ≤ n) (b : Fin n) : rightNeighbor b ≠ b := by
  intro h
  have h' : liftedSite b 1 = liftedSite b 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hb := liftedSite_inj b (by omega : 1<n) (by omega : 0<n) h'
  omega

private theorem swept_source_ordinary {p c n d k : Nat} {x : Config p c n}
    (hc : MCOV x) (b : Fin n) (h : FirstRear x b d) (hk : k < d) (hk0 : 0 < k) :
    rightNeighbor (back b k) = back b (k-1) ∧
      (x (back b (k-1))).leader = false := by
  have hd := h.lt
  have hpred := predecessor_back b (k-1) (by omega)
  rw [show k-1+1=k by omega] at hpred
  have hr : rightNeighbor (back b k) = back b (k-1) := by
    rw [← hpred,right_predecessor]
  refine ⟨hr, Bool.eq_false_iff.mpr ?_⟩
  intro hl
  apply h.before (k-1) (by omega)
  rw [hpred]
  exact hc _ (Or.inl (hr.symm ▸ hl))

/-- A stationary surviving tag cannot select its outgoing edge. Right
service on a surviving tag is resident service; its zero is preserved.
Rear movement may shrink the backwards interval by one (or no change). -/
theorem swept_stationary {p c n d d' N : Nat} {x : Config p c n}
    (hc : MCOV x) (b e : Fin n) (hr : FirstRear x b d) (hs : Swept x b d N)
    (hbound : d' ≤ d) (he : e ≠ b)
    (hResident : rightNeighbor e = b → tagResident (x e) (x b) = true) :
    Swept (step x e) b d' N := by
  refine ⟨?_,?_⟩
  · intro k hk hN
    let S : Fin n → Prop := fun j => ∃ l, l < d' ∧ l < N ∧ back b l = j
    have hpre : ∀ j, S j → (x j).signal ≠ .one := by
      rintro j ⟨l,hl,hN',rfl⟩
      exact hs.1 l (by omega) hN'
    apply rear_swept_step x e S hpre _ _ ⟨k,hk,hN,rfl⟩
    rintro ⟨l,hl,hN',hbe⟩
    have hl0 : 0 < l := by
      apply Nat.pos_of_ne_zero
      intro h'
      have heq : l = 0 := by omega
      subst l
      rw [back_zero] at hbe
      exact he hbe.symm
    obtain ⟨hr',hL⟩ := swept_source_ordinary hc b hr (by omega : l < d) hl0
    rw [hbe] at hr'
    rw [hr']
    exact Or.inl ⟨hs.1 (l-1) (by omega) (by omega),hL⟩
  · intro hN
    by_cases h : rightNeighbor e = b
    · have hz := (freshResident_zero (x e) (x b) (hResident h) (hs.2 hN)).1
      simpa [step,Ne.symm he,h] using hz
    · simpa [step,Ne.symm he,Ne.symm h] using hs.2 hN

/-- Actual advancement introduces a new zero site and retains all previous
swept sites in the now one-unit longer corridor. The old carrier is the
only selected initiator, and it is covered by the exact transfer row. -/
theorem swept_moves {p c n d N : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (b : Fin n) (h : FirstRear x b d) (hs : Swept x b d N)
    (ht : tagTransfer (x b) (x (rightNeighbor b)) = true) :
    Swept (step x b) (rightNeighbor b) (d+1) (N+1) := by
  obtain ⟨hv,hu⟩ := rear_transfer_no_one _ _ ht
  have hz : (step x b (rightNeighbor b)).signal = .zero := by
    simpa [step,rn_ne hn b] using hv
  refine ⟨?_,fun _ => hz⟩
  intro k hk hN
  cases k with
  | zero =>
    rw [back_zero,hz]
    exact Signal.noConfusion
  | succ k =>
    rw [back_after_tag b k (by have := h.lt; omega)]
    let S : Fin n → Prop := fun j => ∃ l, l < d ∧ l < N ∧ back b l = j
    have hpre : ∀ j, S j → (x j).signal ≠ .one := by
      rintro j ⟨l,hl,hN',rfl⟩
      exact hs.1 l hl hN'
    exact rear_swept_step x b S hpre (fun hSb => Or.inr (hu (hpre b hSb))) _
      ⟨k,by omega,by omega,rfl⟩

/-- At the 2n-move cut (and later), any fixed living rear lies strictly
behind the tag and its covered successor lies inside the swept corridor.
The physical rear then remains living, shielded and no-one on this step. -/
theorem swept_fixed_rear {p c n d N : Nat} {x : Config p c n}
    (hc : MCOV x) (b e : Fin n) (h : FirstRear x b d) (hs : Swept x b d N)
    (hd : 0 < d) (hdN : d ≤ N)
    (hL : (x (back b d)).leader = true) (hS : (x (back b d)).shield = true)
    (hZ : (x (back b d)).signal ≠ .one) :
    (step x e (back b d)).leader = true ∧ (step x e (back b d)).shield = true ∧
      (step x e (back b d)).signal ≠ .one := by
  apply rear_fixed_step x e _ hL hS hZ
  intro he
  have hdn := h.lt
  have hpred := predecessor_back b (d-1) (by omega)
  rw [show d-1+1=d by omega] at hpred
  have hr : rightNeighbor e = back b (d-1) := by
    rw [← he, ← hpred, right_predecessor]
  rw [hr]
  refine ⟨hs.1 (d-1) (by omega) (by omega),Bool.eq_false_iff.mpr ?_⟩
  intro hl
  apply h.before (d-1) (by omega)
  rw [hpred,he]
  exact hc _ (Or.inl (hr.symm ▸ hl))

#print axioms swept_initial
#print axioms swept_stationary
#print axioms swept_moves
#print axioms swept_fixed_rear

end L4.RearTrace

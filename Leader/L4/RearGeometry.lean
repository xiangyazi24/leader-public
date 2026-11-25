import Leader.L4.RearTrace

/-! # Reversed cyclic search and the initial rear witness -/

namespace L4.RearTrace

theorem back_zero {n : Nat} (i : Fin n) : back i 0 = i := by
  exact liftedSite_full i

theorem back_surjective {n : Nat} (i j : Fin n) :
    ∃ d : Nat, d < n ∧ back i d = j := by
  obtain ⟨d,hd,he⟩ := liftedSite_of_site i j
  by_cases h : d = 0
  · subst d
    exact ⟨0,hd,(back_zero i).trans ((liftedSite_zero i).symm.trans he)⟩
  · exact ⟨n-d,by omega, by unfold back; rw [show n-(n-d)=d by omega]; exact he⟩

theorem predecessor_right {n : Nat} (i : Fin n) :
    predecessor (rightNeighbor i) = i := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  unfold predecessor back
  rw [liftedSite_advance,show n-1+1=n by omega,liftedSite_full]

theorem right_predecessor {n : Nat} (i : Fin n) :
    rightNeighbor (predecessor i) = i := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  unfold predecessor back
  rw [← liftedSite_succ,show n-1+1=n by omega,liftedSite_full]

structure FirstRear {p c n : Nat} (x : Config p c n) (i : Fin n) (d : Nat) : Prop where
  lt : d < n
  marked : (x (predecessor (back i d))).mark = true
  before : ∀ k : Nat, k < d → (x (predecessor (back i k))).mark ≠ true

private theorem smallest (P : Nat → Prop) (n : Nat) :
    (∃ d, d < n ∧ P d) → ∃ d, d < n ∧ P d ∧ ∀ k, k < d → ¬ P k := by
  induction n with
  | zero => rintro ⟨_,hd,_⟩; omega
  | succ n ih =>
    intro he
    by_cases h : ∃ d, d < n ∧ P d
    · obtain ⟨d,hd,hp,hm⟩ := ih h
      exact ⟨d, by omega,hp,hm⟩
    · obtain ⟨d,hd,hp⟩ := he
      have h' : ¬ d < n := fun hn => h ⟨d,hn,hp⟩
      have eq : d = n := by omega
      subst d
      exact ⟨n,Nat.lt_succ_self _,hp,fun k hk hp' => h ⟨k,hk,hp'⟩⟩

theorem firstRear_exists {p c n : Nat} (x : Config p c n) (i : Fin n)
    (h : ∃ e : Fin n, (x e).mark = true) : ∃ d, FirstRear x i d := by
  obtain ⟨e,he⟩ := h
  obtain ⟨d,hd,hr⟩ := back_surjective i (rightNeighbor e)
  obtain ⟨d',hd',hm,hb⟩ := smallest (fun k => (x (predecessor (back i k))).mark = true)
    n ⟨d,hd,by simpa [hr,predecessor_right] using he⟩
  exact ⟨d',⟨hd',hm,hb⟩⟩

theorem rearAt_eq_back {p c n d : Nat} {x : Config p c n} {i : Fin n}
    (h : FirstRear x i d) : rearAt x i = some (back i d) := by
  unfold rearAt
  have h' : (List.finRange n).find? (fun k => (x (predecessor (back i k.val))).mark)
      = some (⟨d,h.lt⟩ : Fin n) := by
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨h.marked,d,by simpa using h.lt,?_ ,?_⟩
    · simp
    · intro k hk
      simpa using h.before k hk
  simp [h']

theorem rearInit_has_nearest {p c n : Nat} {x : Config p c n} (i : Fin n)
    (hnd : (∃ j : Fin n, (x j).mark = true)) :
    ∃ d, FirstRear x i d ∧ (rearInit x i).rear = some (back i d) := by
  obtain ⟨d,hd⟩ := firstRear_exists x i hnd
  exact ⟨d,hd,rearAt_eq_back hd⟩

/-- Prefixes ending no later than the 2n-move cut require no rear ledger. -/
theorem early_debt {p c n : Nat} (x : Config p c n) (i : Fin n) (w : List (Fin n))
    (h : ¬ TaggedTrace.ended (TaggedTrace.track (TaggedTrace.init x i) w))
    (hN : (TaggedTrace.track (TaggedTrace.init x i) w).moveCount ≤ 2*n) :
    2 * (TaggedTrace.track (TaggedTrace.init x i) w).outHits ≤
      (rearTrack x i w).rearHits + 12*n + 2 := by
  rw [TaggedTrace.hits_eq_moves_on_survival _ _ rfl h]
  omega

theorem predecessor_back {n : Nat} (b : Fin n) (k : Nat) (hk : k+1 < n) :
    predecessor (back b k) = back b (k+1) := by
  have h : rightNeighbor (back b (k+1)) = back b k := by
    unfold back
    rw [← liftedSite_succ,show n-(k+1)+1 = n-k by omega]
  rw [← h,predecessor_right]

theorem back_after_tag {n : Nat} (b : Fin n) (k : Nat) (hk : k < n) :
    back (rightNeighbor b) (k+1) = back b k := by
  unfold back
  rw [liftedSite_advance,show n-(k+1)+1 = n-k by omega]

private theorem right_ne_self {n : Nat} (hn : 4 ≤ n) (b : Fin n) :
    rightNeighbor b ≠ b := by
  intro h
  have h' : liftedSite b 1 = liftedSite b 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hb := liftedSite_inj b (by omega : 1<n) (by omega : 0<n) h'
  omega

private theorem pred_inj {n : Nat} {a b : Fin n} (h : predecessor a = predecessor b) :
    a = b := by
  have h' := congrArg rightNeighbor h
  simpa only [right_predecessor] using h'

theorem paid_was_marked {p c n : Nat} {x : Config p c n} (hc : MCOV x) (e : Fin n)
    (hp : geometricPay (x e) (x (rightNeighbor e)) = true) :
    (x e).mark = true := by
  have h := covered_pair_marks (x e) (x (rightNeighbor e)) (hc e)
  simp only [hp,if_true] at h
  exact h.1

theorem paid_moves_rear_iff {p c n : Nat} {x : Config p c n} (hc : MCOV x)
    (_i e r : Fin n) (s : Observer p c n) (h : s.tag.config = x) :
    rearShifts s e r = true ↔
      e = predecessor r ∧ geometricPay (x e) (x (rightNeighbor e)) = true := by
  unfold rearShifts
  rw [h]
  by_cases hp : geometricPay (x e) (x (rightNeighbor e)) = true
  · have hpm := covered_pair_marks (x e) (x (rightNeighbor e)) (hc e)
    simp only [hp,if_true] at hpm
    simp [hp,hpm.1,hpm.2.1]
  · have hpm := covered_pair_marks (x e) (x (rightNeighbor e)) (hc e)
    simp only [Bool.eq_false_iff.mpr hp,Bool.false_eq_true,if_false] at hpm
    cases hm : (x e).mark <;> simp [hp,hpm.1,hm]

/-- Shift the covered rear witness when the carrier is stationary and
the paid mark does not move that particular rear identity. No P3 can
insert a new root between the rear and the carrier. -/
theorem firstRear_stationary {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (hc : MCOV x) (b e : Fin n) (h : FirstRear x b d)
    (hnop : ¬ (e = predecessor (back b d) ∧
      geometricPay (x e) (x (rightNeighbor e)) = true)) :
    FirstRear (step x e) b d := by
  have hdn := h.lt
  refine ⟨h.lt,?_,?_⟩
  · rw [covered_step_mark hn x hc]
    by_cases hp : geometricPay (x e) (x (rightNeighbor e)) = true
    · have he : predecessor (back b d) ≠ e := fun he => hnop ⟨he.symm,hp⟩
      simp [hp,he,h.marked]
    · simp [hp,h.marked]
  · intro k hk
    rw [covered_step_mark hn x hc]
    by_cases hp : geometricPay (x e) (x (rightNeighbor e)) = true
    · have hw : predecessor (back b k) ≠ rightNeighbor e := by
        intro he
        have hEq : e = predecessor (back b (k+1)) := by
          have he' := congrArg predecessor he
          rw [predecessor_right,predecessor_back b k (by omega : k+1<n)] at he'
          exact he'.symm
        by_cases hk' : k+1 = d
        · rw [hk'] at hEq
          exact hnop ⟨hEq,hp⟩
        · have hh := paid_was_marked hc e hp
          rw [hEq] at hh
          exact h.before (k+1) (by omega) hh
      by_cases he : predecessor (back b k) = e
      · simp [hp,he]
      · simp [hp,he,hw,h.before k hk]
    · simp [hp,h.before k hk]

/-- The selected mark moves the particular old rear. If it was also
the carrier site, the carrier is immediately behind a marked root. -/
theorem firstRear_moves {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (hc : MCOV x) (b : Fin n) (h : FirstRear x b d)
    (hp : geometricPay (x (predecessor (back b d))) (x (back b d)) = true) :
    let e := predecessor (back b d)
    if d = 0 then (step x e b).mark = true else
      FirstRear (step x e) b (d-1) ∧ back b (d-1) = rightNeighbor (back b d) := by
  dsimp
  have hdn := h.lt
  have hp' : geometricPay (x (predecessor (back b d)))
      (x (rightNeighbor (predecessor (back b d)))) = true := by simpa [right_predecessor] using hp
  have hmark : (step x (predecessor (back b d)) (back b d)).mark = true := by
    rw [covered_step_mark hn x hc]
    have he : back b d ≠ predecessor (back b d) := by
      intro he
      have he' := congrArg rightNeighbor he
      exact right_ne_self hn (back b d) (by simpa [right_predecessor] using he')
    simp [hp,he,right_predecessor]
  by_cases hz : d=0
  · simpa [hz,back_zero] using hmark
  · have hd : d-1+1=d := by omega
    have hrel : predecessor (back b (d-1)) = back b d := by
      rw [predecessor_back b (d-1) (by omega : d-1+1<n),hd]
    refine if_neg hz ▸ ?_
    refine ⟨⟨by omega,by rw [hrel]; exact hmark,?_⟩,?_⟩
    · intro k hk
      have hnew : predecessor (back b k) ≠ back b d := by
        intro he
        have h' : (x (predecessor (back b (k+1)))).mark = true := by
          rw [← predecessor_back b k (by omega : k+1<n),he]
          exact h.marked
        exact h.before (k+1) (by omega) h'
      rw [covered_step_mark hn x hc]
      by_cases he : predecessor (back b k) = predecessor (back b d)
      · simp [hp,he,right_predecessor]
      · simp [hp,he,right_predecessor,hnew,h.before k (by omega)]
    · have hh := congrArg rightNeighbor hrel
      simpa only [right_predecessor] using hh

/-- A surviving actual tag transport preserves all marks and increases
the rear distance by one. The ring seam cannot be crossed into the rear. -/
theorem firstRear_tag_moves {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (hc : MCOV x) (b : Fin n) (h : FirstRear x b d)
    (ht : tagTransfer (x b) (x (rightNeighbor b)) = true) :
    FirstRear (step x b) (rightNeighbor b) (d+1) ∧
      back (rightNeighbor b) (d+1) = back b d := by
  have hm := ((tagTransfer_iff _ _).mp ht).2.2.2.1
  have hp : geometricPay (x b) (x (rightNeighbor b)) = false := by
    cases he : geometricPay (x b) (x (rightNeighbor b))
    · rfl
    · have hh := paid_was_marked hc b he
      simp [hm] at hh
  have hd : d+1<n := by
    by_cases h' : d+1<n
    · exact h'
    exfalso
    have hdn := h.lt
    have h'' : n-d=1 := by omega
    have hEq : predecessor (back b d) = b := by
      have hEq' : back b d = rightNeighbor b := by
        unfold back
        rw [h'',liftedSite_succ b 0,liftedSite_zero]
      rw [hEq',predecessor_right]
    have hh := h.marked
    simp [hEq,hm] at hh
  have he := back_after_tag b d h.lt
  refine ⟨⟨hd,?_,?_⟩, he⟩
  · rw [covered_step_mark hn x hc,hp,he]
    exact h.marked
  · intro k hk
    rw [covered_step_mark hn x hc]
    simp only [hp,Bool.false_eq_true,if_false]
    cases k with
    | zero => rw [back_zero,predecessor_right,hm]; decide
    | succ k => rw [back_after_tag b k (by omega : k<n)]; exact h.before k (by omega)

end L4.RearTrace

#print axioms L4.RearTrace.firstRear_exists
#print axioms L4.RearTrace.rearInit_has_nearest
#print axioms L4.RearTrace.early_debt

#print axioms L4.RearTrace.firstRear_stationary
#print axioms L4.RearTrace.firstRear_moves
#print axioms L4.RearTrace.firstRear_tag_moves

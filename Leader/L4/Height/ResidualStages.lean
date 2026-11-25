import Leader.L4.Height.ResidualPotential

namespace L4.Height.ResidualStages

/-- Discharge the four rival releases in a fixed order, then the target
residual release and its fresh publication. Each stage may stop early on
publication. The next-stage starting set includes the actual past, so a
rival already released when its turn starts incurs zero delay. -/
theorem stage_list {S : Type} {n : Nat} (hn : 0<n) (next : S → Fin n → S)
    (pub : S → Prop) (A : Nat) (start : Nat → S → Prop)
    (finish : ∀ y, start 0 y → pub y)
    (m : Nat) (step : ∀ k, k<m → ∀ y, start (k+1) y →
      IIDExpectedHittingTimeAtMost next (fun z => start k z ∨ pub z) y A)
    (x : S) (hx : start m x) : IIDExpectedHittingTimeAtMost next pub x (m*A) := by
  induction m generalizing x with
  | zero =>
    intro t
    rw [iidHitCost_of_target next pub x (finish x hx)]
    exact Nat.zero_le _
  | succ m ih =>
    rw [Nat.succ_mul,Nat.add_comm (m*A) A]
    apply iid_stage_le next hn x (start m) pub A (m*A) (step m (by omega) x hx)
    intro y h
    exact ih (fun k hk => step k (by omega)) y h

/-- Each stage potential may depend on its physical starting prefix. The
six stop relations need only identify its target and its physical successor. -/
theorem six_residuals {S : Type} {n W : Nat} (hn : 0<n) (next : S → Fin n → S)
    (pub : S → Prop) (start : Nat → S → Prop) (finish : ∀ y, start 0 y → pub y)
    (cycles : ∀ k, k<6 → ∀ y, start (k+1) y →
      ∃ D : ResidualPotentialData (S:=S) (n:=n), D.next=next ∧
        D.P=(fun z => start k z ∨ pub z) ∧ D.Q y ∧ D.Phi y≤2^15*n*W)
    (x : S) (hx : start 6 x) : IIDExpectedHittingTimeAtMost next pub x (6*(2^15*n*W)) := by
  apply stage_list hn next pub _ start finish 6 _ x hx
  intro k hk y hy
  obtain ⟨D,same,stop,ok,bounded⟩ := cycles k hk y hy
  rw [←same,←stop]
  exact residual_expected_le D y ok _ bounded

/-- A cycle can keep its own escrow and cursor memory, resetting them at a
stopped prefix. One projection identifies its physical transition at every
candidate and its actual stopping event on the invariant. -/
theorem projected_residual {U S : Type} {n A : Nat}
    (D : ResidualPotentialData (S:=U) (n:=n)) (proj : U → S)
    (next : S → Fin n → S) (finish : S → Prop)
    (commute : ∀ z, D.Q z → ∀ e, proj (D.next z e)=next (proj z) e)
    (sound : ∀ z, D.Q z → D.P z → finish (proj z))
    (z : U) (q : D.Q z) (cap : D.Phi z≤A) :
    IIDExpectedHittingTimeAtMost next finish (proj z) A := by
  have path (y : U) (v : List (Fin n)) (qy : D.Q y) :
      stoppedTime next finish (proj y) v ≤ stoppedTime D.next D.P y v := by
    induction v generalizing y with
    | nil => exact Nat.le_refl _
    | cons e v ih =>
      by_cases hit : finish (proj y)
      · simp [stoppedTime,hit]
      · have off : ¬D.P y := fun h => hit (sound y qy h)
        simp only [stoppedTime,if_neg hit,if_neg off,←commute y qy e]
        exact Nat.succ_le_succ (ih _ (D.closed y e qy))
  intro t
  have upper := residual_expected_le D z q A cap t
  rw [iidHitCost_eq_wordSum] at upper ⊢
  exact Nat.le_trans (wordSum_mono _ _ (fun v => path z v q) t) upper

/-- For a sticky local stop it suffices to identify its first entrance with
a physical cut. Later states can keep the latch after leaving that cut. -/
theorem projected_first_entrance {U S : Type} {n A : Nat}
    (D : ResidualPotentialData (S:=U) (n:=n)) (proj : U → S)
    (next : S → Fin n → S) (finish : S → Prop)
    (commute : ∀ z,D.Q z → ¬D.P z → ∀ e,proj (D.next z e)=next (proj z) e)
    (entrance : ∀ z,D.Q z → ¬D.P z → ∀ e,D.P (D.next z e) → finish (proj (D.next z e)))
    (z : U) (q : D.Q z) (start : D.P z → finish (proj z)) (cap : D.Phi z≤A) :
    IIDExpectedHittingTimeAtMost next finish (proj z) A := by
  have path (y : U) (w : List (Fin n)) (qy : D.Q y) (matchStop : D.P y → finish (proj y)) :
      stoppedTime next finish (proj y) w ≤ stoppedTime D.next D.P y w := by
    induction w generalizing y with
    | nil => exact Nat.le_refl _
    | cons e w ih =>
      by_cases ended : finish (proj y)
      · simp [stoppedTime,ended]
      · have off : ¬D.P y := fun stop => ended (matchStop stop)
        simp only [stoppedTime,if_neg ended,if_neg off,←commute y qy off e]
        exact Nat.succ_le_succ (ih _ (D.closed y e qy) (entrance y qy off e))
  intro t
  have bounded := residual_expected_le D z q A cap t
  rw [iidHitCost_eq_wordSum] at bounded ⊢
  exact Nat.le_trans (wordSum_mono _ _ (fun w => path z w q start) t) bounded

/-- A surviving word has paid the full elapsed time when publication is
latched. The proof inspects the real word rather than assuming uncensored
cycle lengths are independent. -/
theorem wait_on_miss {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop)
    (closed : ∀ y e, P y → P (next y e)) (y : S) (w : List (Fin n))
    (miss : ¬ P (runWord next y w)) : stoppedTime next P y w = w.length := by
  have lasts (x : S) (v : List (Fin n)) (hx : P x) : P (runWord next x v) := by
    induction v generalizing x with
    | nil => exact hx
    | cons e v ih => exact ih _ (closed x e hx)
  induction w generalizing y with
  | nil => rfl
  | cons e w ih =>
    have off : ¬ P y := fun h => miss (lasts y _ h)
    simp only [stoppedTime,if_neg off,List.length_cons]
    exact congrArg Nat.succ (ih (next y e) miss)

#print axioms six_residuals
#print axioms wait_on_miss
end L4.Height.ResidualStages


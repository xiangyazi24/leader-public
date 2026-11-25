import Leader.L4.DirtyPrepRank

namespace L4.DirtyHighRank
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6WordChart
open BStarResetChartTouch BStarClearanceSource DirtyLeastForward
open DirtyPrepRank (no_prefix_refill)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Where every least old forward can be removed by its selected mark,
the whole fixed chart costs one IID hit per possible remaining slot.
The active invariant may be stopped on own release. The last slot
is included, so the result certifies no interpreted forward at all. -/
theorem expected_forward_free_of_local
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (init : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→Held (q (S.getD 0 fall).1).long→∀ e,Q (step q e))
    (pay : ∀ q i,Q q→Held (q (S.getD 0 fall).1).long→i≤len→
      ringF q (S.getD i fall)→(∀ j,j<i→¬ringF q (S.getD j fall)) →
      ∃ e, ¬ringF (step q e) (S.getD i fall)) :
    Height.IIDExpectedHittingTimeAtMost step
      (fun q=>¬Held (q (S.getD 0 fall).1).long ∨ ∀ u∈S,¬ringF q u) x (n*S.length) := by
  classical
  let root := (S.getD 0 fall).1
  let A (q : X) := Held (q root).long
  let F (q : X) (i : Nat) := ringF q (S.getD i fall)
  let least (q : X) (i : Nat) := i≤len ∧ F q i ∧ ∀ j,j<i→¬F q j
  let goal (q : X) := ¬A q ∨ ∀ u∈S,¬ringF q u
  let Live (q : X) (z : Nat) := Q q ∧ A q ∧ ∃ i,least q i ∧ z=S.length-i
  have size := chart.length
  have idx (q : X) (N : ¬goal q) : ∃ i,least q i := by
    have found : ∃ i,i<S.length ∧ F q i := by
      apply Classical.byContradiction
      intro counter
      apply N
      right
      intro u mem forward
      obtain ⟨i,lt,E⟩ := List.mem_iff_getElem.mp mem
      exact counter ⟨i,lt,by dsimp [F]; rwa [←List.getElem_eq_getD (h:=lt) fall,E]⟩
    have choose (k : Nat) : (∃ i,i<k ∧ F q i) → ∃ i,i<k ∧ F q i ∧ ∀ j,j<i→¬F q j := by
      induction k with
      | zero => rintro ⟨i,I,_⟩; omega
      | succ k ih =>
        intro P
        by_cases h : ∃ i,i<k ∧ F q i
        · obtain ⟨i,I,E,N⟩ := ih h
          exact ⟨i,by omega,E,N⟩
        · obtain ⟨i,I,E⟩ := P
          exact ⟨i,I,E,fun j J F=>h ⟨j,by omega,F⟩⟩
    obtain ⟨i,lt,Fq,least⟩ := choose S.length found
    exact ⟨i,by omega,Fq,least⟩
  have pos (q : X) (z : Nat) (L : Live q z) : 0<z := by
    obtain ⟨_,_,i,Li,rfl⟩ := L
    have boundedIndex := Li.1
    omega
  have advance (q : X) (z : Nat) (L : Live q z) :
      ∃ d : Fin n, ∀ e,goal (step q e) ∨
        ∃ z',Live (step q e) z' ∧ z'≤z ∧ (e=d→z'<z) := by
    obtain ⟨Qq,H,i,Mi,rfl⟩ := L
    obtain ⟨d,D⟩ := pay q i Qq H Mi.1 Mi.2.1 Mi.2.2
    refine ⟨d,fun e=>?_⟩
    by_cases hit : goal (step q e)
    · exact .inl hit
    have HA : A (step q e) := Classical.byContradiction (fun h=>hit (.inl h))
    obtain ⟨j,J⟩ := idx (step q e) hit
    have le : i≤j := by
      by_cases k : j<i
      · exact (no_prefix_refill hp chart sep (layout q Qq) H Mi.1 Mi.2.2 e j k J.2.1).elim
      · omega
    refine .inr ⟨S.length-j,⟨closed q Qq H e,HA,j,J,rfl⟩,by omega,?_⟩
    intro eD
    subst e
    have lt : i<j := by
      by_cases E : i=j
      · subst j
        exact (D J.2.1).elim
      · omega
    have boundedIndex := J.1
    omega
  by_cases hit : goal x
  · intro t
    rw [Height.iidHitCost_of_target _ _ _ hit]
    exact Nat.zero_le _
  have H : A x := Classical.byContradiction (fun h=>hit (.inl h))
  obtain ⟨i,Mi⟩ := idx x hit
  have E := ResetReturnIID.iid_of_relational_rank step goal Live pos advance x (S.length-i)
    (.inr ⟨init,H,i,Mi,rfl⟩)
  intro t
  exact Nat.le_trans (E t) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le ..)))

#print axioms expected_forward_free_of_local
end L4.DirtyHighRank

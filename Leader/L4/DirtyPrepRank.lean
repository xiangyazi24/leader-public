import Leader.L4.DirtyFenceFixedCut
import Leader.L4.ResetReturnIID

namespace L4.DirtyPrepRank
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarResetChartTouch
open BStarClearanceSource (Held held_before)
open BStarClearanceIndexedSum (distance distance_idx)
open DirtyLeastForward (ringF ring_origin)
open BStarLongCommand BStarLongToken BStarClearanceGate

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Zero-distance gate debt read at the old frozen geometry. -/
def debt (base x : X) (u : Pos n) : Nat :=
  weight (longGeometry B (base u.1)) u.2
    (bind (longGeometry B (base u.1)) u.2 (atSite (x u.1).long u.2))

theorem debt_le_two (base x : X) (u : Pos n) : debt hp base x u≤2 := by
  unfold debt
  exact bounded _ _ _

/-- The chart prefix cannot refill on a held old-state mark. This is
indexed, unlike the distance-coordinate version of the origin theorem. -/
theorem no_prefix_refill
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (held : Held (x (S.getD 0 fall).1).long)
    {j : Nat} (J : j≤len) (clear : ∀ i,i<j → ¬ringF x (S.getD i fall))
    (e : Fin n) (i : Nat) (ij : i<j) : ¬ringF (step x e) (S.getD i fall) := by
  intro F
  have lenS := chart.length
  have iS : i<S.length := by omega
  have H := held_before hp x (S.getD 0 fall).1 e held
  rw [congrArg Prod.fst chart.root] at H
  have U : S.getD i fall ∈ S := by
    rw [←List.getElem_eq_getD (h:=iS) fall]
    exact List.getElem_mem iS
  rcases ring_origin hp chart layout e (sep e) H _ U F with old|⟨v,V,old,D⟩
  · exact clear i ij old
  · obtain ⟨k,kS,EQ⟩ := List.mem_iff_getElem.mp V
    have E : S.getD k fall=v := (List.getElem_eq_getD (h:=kS) fall).symm.trans EQ
    rw [←EQ,←List.getElem_eq_getD (h:=iS) fall,distance_idx chart.nodup kS,distance_idx chart.nodup iS] at D
    rw [←E] at old
    exact clear k (by omega) old

/-- Actual raw clock reduction. Its two remaining local hypotheses are
precise: a surviving least prep token never gains gate debt, and some
mark either removes that token or lowers its gate debt. The arithmetic
reduction must not be read as discharging those two chart-local hooks. -/
theorem expected_to_high_cut_of_local
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (init : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    {j : Nat} (J : j≤len) :
    let root := (S.getD 0 fall).1
    let A (q : X) := Held (q root).long
    let F (q : X) (i : Nat) := ringF q (S.getD i fall)
    let D (q : X) (i : Nat) := debt hp base q (S.getD i fall)
    let least (q : X) (i : Nat) := i<j ∧ F q i ∧ ∀ k,k<i→¬F q k
    (∀ q i,Q q→A q→least q i→∀ e,F (step q e) i→D (step q e) i≤D q i) →
    (∀ q i,Q q→A q→least q i→∃ e,F (step q e) i→D (step q e) i<D q i) →
    Height.IIDExpectedHittingTimeAtMost step (fun q=>¬A q ∨ ∀ i,i<j→¬F q i) x (n*(3*j+2)) := by
  classical
  dsimp only
  let root := (S.getD 0 fall).1
  let A (q : X) := Held (q root).long
  let F (q : X) (i : Nat) := ringF q (S.getD i fall)
  let D (q : X) (i : Nat) := debt hp base q (S.getD i fall)
  let least (q : X) (i : Nat) := i<j ∧ F q i ∧ ∀ k,k<i→¬F q k
  let goal (q : X) := ¬A q ∨ ∀ i,i<j→¬F q i
  let Live (q : X) (z : Nat) := Q q ∧ A q ∧ ∃ i,least q i ∧ z=3*(j-i)+D q i
  intro weak pay
  have index (q : X) : (∃ i, i<j ∧ F q i) → ∃ i, least q i := by
    have find (k : Nat) : (∃ i,i<k ∧ F q i) →
      ∃ i,i<k ∧ F q i ∧ ∀ h,h<i→¬F q h := by
      induction k with
      | zero =>
          rintro ⟨i,I,_⟩
          omega
      | succ k ih =>
          intro H
          by_cases L : ∃ i,i<k ∧ F q i
          · obtain ⟨i,I,V,M⟩ := ih L
            exact ⟨i,by omega,V,M⟩
          · obtain ⟨i,I,V⟩ := H
            exact ⟨i,I,V,fun h H W => L ⟨h,by omega,W⟩⟩
    exact find j
  have positive (q : X) (z : Nat) (L : Live q z) : 0<z := by
    obtain ⟨_,_,i,L,E⟩ := L
    have P := L.1
    omega
  have advance (q : X) (z : Nat) (L : Live q z) :
      ∃ d : Fin n, ∀ e,goal (step q e) ∨
        ∃ z',Live (step q e) z' ∧ z'≤z ∧ (e=d→z'<z) := by
    obtain ⟨Qq,H,i,Li,rfl⟩ := L
    obtain ⟨d,Hd⟩ := pay q i Qq H Li
    refine ⟨d,fun e=>?_⟩
    by_cases G : goal (step q e)
    · exact .inl G
    · have N : A (step q e) := Classical.byContradiction (fun h=>G (.inl h))
      have someF : ∃ k,k<j ∧ F (step q e) k := by
        apply Classical.byContradiction
        intro no
        exact G (.inr (fun k K Fk => no ⟨k,K,Fk⟩))
      obtain ⟨k,Lk⟩ := index (step q e) someF
      have boundI : i≤len := by have := Li.1; omega
      have ge : i≤k := by
        by_cases E : k<i
        · exact False.elim (no_prefix_refill hp chart sep (layout q Qq) H boundI Li.2.2 e k E Lk.2.1)
        · omega
      refine .inr ⟨3*(j-k)+D (step q e) k, ⟨closed q Qq e,N,k,Lk,rfl⟩,?_⟩
      by_cases E : k=i
      · subst k
        exact ⟨Nat.add_le_add_left (weak q i Qq H Li e Lk.2.1) _,fun K=>by
          subst e
          exact Nat.add_lt_add_left (Hd Lk.2.1) _⟩
      · have Bnd := debt_le_two hp base (step q e) (S.getD k fall)
        have Jk := Lk.1
        change D (step q e) k≤2 at Bnd
        exact ⟨by omega,fun _=>by omega⟩
  by_cases G : goal x
  · intro t
    rw [Height.iidHitCost_of_target _ _ _ G]
    exact Nat.zero_le _
  · have H : A x := Classical.byContradiction (fun h=>G (.inl h))
    have someF : ∃ i,i<j ∧ F x i := by
      apply Classical.byContradiction
      intro no
      exact G (.inr (fun i I Fi => no ⟨i,I,Fi⟩))
    obtain ⟨i,L⟩ := index x someF
    have E := ResetReturnIID.iid_of_relational_rank step goal Live positive advance x
      (3*(j-i)+D x i) (.inr ⟨init,H,i,L,rfl⟩)
    have Bnd := debt_le_two hp base x (S.getD i fall)
    change D x i≤2 at Bnd
    intro t
    exact Nat.le_trans (E t) (Nat.mul_le_mul_right (n^t) (Nat.mul_le_mul_left n (by omega)))

#print axioms no_prefix_refill
#print axioms expected_to_high_cut_of_local
end L4.DirtyPrepRank

import Leader.L4.BStarCopyRightDeposit

namespace L4.BStarCopyRightK2
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarCopyRightStrip BStarCopyDownstream BStarAcquireVisitOrder
open BStarResetChartTouch BStarAcquireLiteralChain BStarResetChartIndex BStarAcquireAnchors

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- The right source K2 tour traverses each nonseam edge with increasing
physical address; the right data stream runs in the opposite direction. -/
theorem k2_body (g : Pair LongGeometry) (body : g.2.axes.h6=false) :
    link (L 2) (R 2)∈orderedCommands g := by
  have fin (I L J : Bool) :
      link (BStarLongClaims.L 2) (R 2)∈orderedCommands (geo false I L,geo false J false) := by
    cases I <;> cases L <;> cases J <;> decide +kernel
  let v := (geo false g.1.inside g.1.last,geo g.2.axes.h6 g.2.inside false)
  change link (L 2) (R 2)∈orderedCommands v
  have E : v=(geo false g.1.inside g.1.last,geo false g.2.inside false) := by simp [v,body]
  rw [E]
  exact fin _ _ _

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- If K2 at a specified source is still unvisited, all strictly
behind right-strip K2 slots are also unvisited. This uses exact
selected-chart edges, not an extra vacancy hypothesis at each slot. -/
theorem all_behind_unvisited {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (a : Fin n) (seam tail i cut : Nat) (C : Strip B base a seam tail)
    (hi : seam≤i)
    (current : Unvisited S fall len cut true (addr a i)) :
    ∀ j, i≤j → j≤tail → Unvisited S fall len cut true (addr a j) := by
  intro j
  induction j with
  | zero =>
    intro J _
    have E : i=0 := by omega
    rwa [E] at current
  | succ j ih =>
    intro J T
    by_cases E : i=j+1
    · rwa [E] at current
    · obtain ⟨q,cq,qloc,Q⟩ := ih (by omega) (by omega)
      have right := BStarCopyRightStrip.addr_next a j
      have body : (oldPair B base (addr a j)).2.axes.h6=false := by
        change oldH6 B base (rightNeighbor (addr a j))=false
        rw [←right]
        exact C.rs_nonheader _ (by omega) T
      let u : Pos n := (addr a j,2)
      let v : Pos n := (addr a (j+1),2)
      have edge : Edge B base u v := by
        refine ⟨addr a j,L 2 |> fun z => link z (R 2),R 2,k2_body _ body,rfl,rfl,?_⟩
        change (addr a (j+1),2)=(rightNeighbor (addr a j),2)
        rw [right]
      have lens := chart.length
      have qs : q<S.length := by omega
      have U : S.getD q fall=u := Q
      have uS : u∈S := by
        rw [←U,←List.getElem_eq_getD (h:=qs)]
        exact List.getElem_mem _
      obtain ⟨k,K,F,G⟩ := chart.edge u v uS edge
      have eq : k=q := (List.getD_inj (by omega) qs chart.nodup).mp (by
        rw [←List.getElem_eq_getD (h:=show k<S.length by omega),F,U])
      subst k
      exact ⟨q+1,by omega,by omega,(List.getElem_eq_getD _).symm.trans G⟩

#print axioms all_behind_unvisited
end L4.BStarCopyRightK2

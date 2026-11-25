import Leader.L4.BStarResetChartTouch
import Leader.L4.RearGeometry

namespace L4.BStarResetChartNomination
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartIndex BStarResetMarkAdapter
open BStarAcquireRailCoverage BStarResetChartTouch BStarSeparatingProgress

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

private theorem departure_exists (base : X)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (u : Pos n) (hu : active (longGeometry B (base u.1)) u.2=true) :
    ∃ e C, C∈orderedCommands (oldPair B base e) ∧
      C.kind≠.door ∧ u=address e C.source := by
  let i := u.1
  let k := u.2
  let j := RearTrace.predecessor i
  let G (v : Fin n) := longGeometry B (base v)
  have J : rightNeighbor j=i := RearTrace.right_predecessor i
  have L : continuation (G j) (G i)=true := by
    have T := cont j
    change continuation (G j) (G (rightNeighbor j))=true at T
    rwa [J] at T
  rcases departure (G j) (G i) (G (rightNeighbor i)) (head i)
      (head (rightNeighbor i)) L (cont i) k hu with ⟨C,hC,hs,hn⟩|⟨C,hC,hs,hn⟩
  · refine ⟨j,C,?_,hn,?_⟩
    · change C∈orderedCommands (G j,G (rightNeighbor j))
      rwa [J]
    · rw [hs]
      change u=(rightNeighbor j,u.2)
      rw [J]
  · exact ⟨i,C,hC,hn,by rw [hs]; rfl⟩

/-- Every bounded chart entry has its mandatory physical service
mark. A nomination extracted from the base chart remains valid in
every snapshot with the same fixed layout. This is a statement
about structural labels, not enabled token dynamics. -/
theorem nominate {base : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (j : Nat) (hj : j≤len) :
    ∃ e : Fin n, ∀ y : X, (∀ i, Layout B base i=Layout B y i) →
      (if j<len then Label.link j else Label.terminal) ∈
        labels hp y e (fun j => S.getD j fallback) len := by
  let adr := fun k => S.getD k fallback
  let u := adr j
  have lenS := chart.length
  have um : u∈S := by
    change S.getD j fallback∈S
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  have ⟨hu,ou⟩ := chart.entries u um
  obtain ⟨e,C,hC,hn,haddr⟩ := departure_exists hp base head cont u hu
  refine ⟨e,?_⟩
  intro y same
  have hCy := command_eq B base y same e ▸ hC
  rcases selected_endpoint_or_link B base y hh same o e C hCy (by rw [haddr] at ou; exact ou) with D|T|F
  · exact (hn D.1).elim
  · have h : adr j=adr len := haddr.trans (T.2.2.trans chart.terminal.symm)
    have eq := (List.getD_inj (by omega) (by omega) chart.nodup).mp h
    have K := BStarAcquireChainEndpoints.terminal _ C hCy T.2.1 hn
    rw [if_neg (by omega)]
    exact (mem_terminal hp y e adr len).mpr ⟨C,hCy,T.1,T.2.1,K.2.2.2,eq ▸ haddr⟩
  · obtain ⟨D,hD,E⟩ := F
    have Ex : Edge B base u (address e D) := haddr ▸ (edge_fixed B base y same _ _).mpr E
    obtain ⟨k,hk,L,R⟩ := chart.edge _ _ um Ex
    have L' : adr k=u := (List.getElem_eq_getD _).symm.trans L
    have eK := (List.getD_inj (by omega) (by omega) chart.nodup).mp L'
    subst k
    rw [if_pos (by omega)]
    exact (mem_link hp y e adr len j).mpr
      ⟨by omega,C,D,hCy,hD,haddr,(List.getElem_eq_getD _).symm.trans R⟩

end L4.BStarResetChartNomination

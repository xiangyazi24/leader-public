import Leader.L4.DirtyForwardSuffix
import Leader.L4.DirtyHighRank
import Leader.L4.DirtyFencePersistence

namespace L4.DirtyForwardEmptyClock
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongTransport BStarLongCommand BStarLongEvents BStarLongWork
open BStarH6WordChart BStarH6Ordinal BStarLongFiberOwner BStarLongFixedRouting
open BStarAcquireVisitOrder BStarAcquireAnchors BStarResetChartTouch BStarAcquireLiteralChain
open BStarAcquireRailCoverage BStarResetMarkAdapter BStarClearanceDataChart
open BStarClearanceOffset BStarClearanceIndexedSum BStarClearanceIndexedWait
open BStarFenceLineGeometry BStarClearanceSource DirtyLeastForward
open BStarClearanceForwardService BStarClearanceCommandFrame

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem expected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; continuation g.1 g.2=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    {l d w : Nat} (dp : 0<d)
    (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=w))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → w≤oldOrdinal B base hh i+1)
    (cutoff : Nat)
    (onPrep : ∀ u∈S, (∃ sh op,sh∈prepSites (longGeometry B (base u.1)) u.2 op) →
      cutoff<distance S u)
    (onRace : ∀ u∈S, u.2.val=1 → cutoff<distance S u)
    (clear : ∀ u∈S, cutoff<distance S u → ¬ringF x u)
    (E : BStarFenceSweepClock.Empty (BStarFenceEmptySuffix.ownedLines
      (S.getD 0 fall).1 (S.getD len fall).1 l d w x)) :
    Height.IIDExpectedHittingTimeAtMost step
      (fun y=>¬Held (y (S.getD 0 fall).1).long ∨ ∀u∈S,¬ringF y u) x (n*S.length) := by
  let root := (S.getD 0 fall).1
  let Empty (q : X) := BStarFenceSweepClock.Empty (BStarFenceEmptySuffix.ownedLines
      (S.getD 0 fall).1 (S.getD len fall).1 l d w q)
  let Cut (q : X) := ∀ u∈S, cutoff<distance S u → ¬ringF q u
  let Inv (q : X) := Q q ∧ Cut q ∧ Empty q
  have req : root=(endpoint (oldH6 B base) hh o 0).1 := congrArg Prod.fst chart.root
  apply DirtyHighRank.expected_forward_free_of_local hp chart sep Inv ⟨I,clear,E⟩
  · exact fun y H=>layout y H.1
  · intro q Y H e
    have hold := held_before hp q root e H
    rw [req] at hold
    refine ⟨closed q e Y.1,?_,?_⟩
    · intro u U D F
      rcases ring_origin hp chart (layout _ Y.1) e (sep e) hold u U F with F|⟨v,V,F,Dv⟩
      · exact Y.2.1 u U D F
      · exact Y.2.1 v V (by omega) F
    · apply DirtyFencePersistence.empty_until_own_service hp chart sep LF RF dp flags notShort [e]
        cutoff onPrep Y.2.1 _ Y.2.2
      intro pre f post T
      have Nt := congrArg List.length T
      have Ne : ([e] : List (Fin n)).length=1 := rfl
      rw [Ne,List.length_append,List.length_cons] at Nt
      have nz : pre.length=0 := by omega
      simp only [List.length_eq_zero_iff] at nz
      subst pre
      have ef : e=f := (List.cons.inj T).1
      subst f
      exact ⟨layout _ Y.1,hold⟩
  · intro q j Y _ hj F _
    have size := chart.length
    have U : S.getD j fall∈S := by
      rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
      exact List.getElem_mem _
    have late : (S.getD j fall).2.val≠1 := fun z=>Y.2.1 _ U (onRace _ U z) F
    obtain ⟨e,C,pay,A,N,O⟩ := DirtyForwardSuffix.nominate_empty hp chart (layout _ Y.1)
      head cont dp LF RF seam (fun i=>(flags i).1) Y.2.2 j hj late F
    exact ⟨e,A ▸ DirtyForwardAdvance.ring_advance_removes_forward hp q e (sep e) C pay O N⟩

end L4.DirtyForwardEmptyClock

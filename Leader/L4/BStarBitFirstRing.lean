import Leader.L4.BStarBitUnmask
import Leader.L4.BStarBitGateGeometry
import Leader.L4.BStarGeneratedOwner

namespace L4.BStarBitFirstRing
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongRouting BStarLongWork BStarLongEvents
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarResetChartTouch BStarResetChartIndex BStarAcquireLiteralChain
open BStarAcquireAnchors BStarLongFiberOwner BStarLongKOne BStarClearanceRaceMark
open BStarResetMarkAdapter BStarGeneratedOwner BStarSeparatingRail BStarAcquireForwardTrace
open BStarClearanceOffset BStarBitGateGeometry BStarBitParity BStarBitUnmask
open BStarBankTrace (sideFlag)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

theorem predecessor_trail {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (i : Fin n) (k : Nat) (idx : S.getD k fall=(i,1))
    (O : oldOrdinal B base hh i=4)
    (now : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k))) :
    atSite (x (RearTrace.predecessor i)).long 1=.trail := by
  let h := oldH6 B base
  let pred := RearTrace.predecessor i
  have eq : rightNeighbor pred=i := RearTrace.right_predecessor _
  have body : h i=false := Bool.eq_false_iff.mpr (fun H => by
    have Z := (ordinal_zero h hh i).mpr H
    change ordinal h hh i=4 at O
    omega)
  have kbound : k≤len := now.2.1.1
  have big := C.length
  have mem : (i,(1:Fin 11))∈S := by
    rw [←idx,←List.getElem_eq_getD (h:=show k<S.length by omega)]
    exact List.getElem_mem _
  have own := (C.entries _ mem).2
  have sameWord : word h i=word h pred := by
    have R := right_word h pred
    rw [eq,body] at R
    obtain ⟨lo,hi⟩ := word_range h pred hh
    simpa only [Bool.toNat_false,Int.natCast_zero,Int.add_zero,Int.emod_eq_of_lt lo hi] using R
  have ownPred : commandOwner h pred 1=o.val := by
    unfold commandOwner at own ⊢
    rw [←sameWord]
    exact own
  have predMem := C.cover (pred,1) (by rfl) ownPred
  let g := oldPair B base pred
  have gbody : g.2.axes.h6=false := by
    change h (rightNeighbor pred)=false
    rw [eq]
    exact body
  have preEdge : Edge B base (pred,1) (i,1) := by
    refine ⟨pred,advance,R 1,(one_mem g advance (by decide)).mpr (by simp [gbody]),rfl,rfl,?_⟩
    change (i,1)=(rightNeighbor pred,1)
    rw [eq]
  obtain ⟨j,H,prev,next⟩ := C.edge (pred,1) (i,1) predMem preEdge
  have N : S.getD (j+1) fall=(i,1) := (List.getElem_eq_getD (h:=H) fall).symm.trans next
  have J : j+1=k := (List.getD_inj H (by omega) C.nodup).mp (N.trans idx.symm)
  have P : S.getD j fall=(pred,1) := (List.getElem_eq_getD (h:=by omega) fall).symm.trans prev
  have T := now.2.1.2.2 j (by omega)
  change atCursor x (S.getD j fall)=.trail at T
  rw [P] at T
  exact T

/-- On the actual generated cursor, either of the distinct incident
labels writes its first-side code, and every nonincident raw label
frames the exact old wire. No extra per-mark mask premise. -/
theorem first_mark {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (ready : correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (idx : S.getD k fall=(i,1))
    (O : oldOrdinal B base hh i=4)
    (now : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k)))
    (v : Payload) (old : bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v)
    (F : v.fault=0) (op : v.opcode.toNat=bitOp) (R1 : v.race=1) :
    (∀ s, atSite (step x (incident i s) i).long 1=.forward {v with race:=firstCode s}) ∧
    (∀ e, e≠incident i .left → e≠incident i .right →
      (step x e i).long=(x i).long) := by
  constructor
  · intro s
    let e := incident i s
    let pair := (x e,x (rightNeighbor e))
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long pair
    have I : site e s=i := incident_site i s
    have geo : geometry g s=longGeometry B (x i) := by
      rw [←I]
      cases s <;> rfl
    have read : readK raw (⟨s,1⟩ : AtK)=atSite (x i).long 1 := by
      rw [←I]
      cases s <;> rfl
    have starts : bound g (readK raw) ⟨s,1⟩=.forward v := by
      change bind (geometry g s) 1 (readK raw ⟨s,1⟩)=.forward v
      rwa [geo,read]
    have gateOn : gate bitOp 1 (geometry g s)=true := by
      rw [geo]
      exact (bit_gate_iff hp hh fixed ready i 1).mpr ⟨rfl,O⟩
    have right : s=.right → g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail := by
      intro E
      subst s
      have bd : oldH6 B base i=false := Bool.eq_false_iff.mpr (fun H => by
        have Z := (ordinal_zero _ hh i).mpr H
        change ordinal _ hh i=4 at O
        omega)
      constructor
      · change oldH6 B x (rightNeighbor e)=false
        rw [show rightNeighbor e=i from RearTrace.right_predecessor i,fixed,bd]
      · have T := predecessor_trail hp C i k idx O now
        change bind (geometry g .left) 1 (atSite (x (RearTrace.predecessor i)).long 1)=.trail
        rw [T]
        rfl
    have out := joined_first k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair s v starts F op R1 gateOn right
    have pairStep : step x e i=lane (sideFlag s) (largePair B pair) := by
      rw [←I]
      cases s with
      | left => simp only [site,AllSizeS1Geometry.step,if_true]; rfl
      | right => simp only [site,AllSizeS1Geometry.step,if_neg (Ne.symm (sep e)),if_true]; rfl
    change atSite (step x e i).long 1=_
    rw [pairStep]
    unfold atSite
    have V : (kField 1).read (lane (sideFlag s) (largePair B pair)).long =
      readRaw (Pair.map LargeSite.long (largePair B pair)) ⟨s,1⟩ := by cases s <;> rfl
    rw [V,out,BStarLongToken.decode_encode]
  · intro e left right
    have L : i≠e := Ne.symm left
    have U : i≠rightNeighbor e := fun E => right (by change e=RearTrace.predecessor i; rw [E,RearTrace.predecessor_right])
    simp [AllSizeS1Geometry.step,L,U]

#print axioms predecessor_trail
#print axioms first_mark
end L4.BStarBitFirstRing

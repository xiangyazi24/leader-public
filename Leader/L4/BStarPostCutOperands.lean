import Leader.L4.BStarAttemptWins
import Leader.L4.BStarCustodyCuts

namespace L4.BStarPostCutOperands
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarGrantBirth BStarGrantWriterHistory BStarCustodyCuts BStarPostCutAttempt
open BStarAttemptWins BStarCommitOperands BStarCutOperandReadout
open BStarAcquireLatch BStarAcquireReadout BStarLongLayout BStarLongGrant

set_option maxRecDepth 8192
set_option maxHeartbeats 2600000
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- All three reads from the actual old COMMIT are precisely the old
physical snapshots from the matching successful, post-A ACQUIRE.
No continuously held grant or no-prior-publication fact is assumed
by the caller. The witnesses also say which physical marks were read. -/
theorem actual_operands {base x : X} (u v tail : List (Fin n))
    (facts : CutFacts hp base x u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (mark center : Fin n)
    (pub : ¬NoPublication hp (run x ((u++v)++tail)) mark center) :
    ∃ (o : Owners (oldH6 B base)) (ackLead : List (Fin n)) (ack root : Fin n),
      ∀ j : Fin 3, ∃ (i : Fin n) (visit : Visit)
          (A : Acquisition hp x u (u++(v++tail)) i j),
        (∃ remainder, ackLead=A.lead++A.mark::remainder) ∧
        i=(endpoint (oldH6 B base) hh o ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1 ∧
        (j=1 → i=center) ∧
        visit.incidence=j ∧
        visit.selector=BStarLongPublication.readSel ((run x A.lead) i).long ∧
        visit.headers=headerBits ((run x A.lead) i).long ∧
        (let src := (step (run x ackLead) ack root).long
         (((capturedSelector j).read src).toNat,((headerBlock j).read src).toNat) =
           (visit.selector.val,visit.headers.toNat)) ∧
        ∀ sites : Fin r → Fin n, WordSites (oldH6 B base) i sites →
          OperandAt (run x ((u++v)++tail)) i sites=OperandAt (run x A.lead) i sites := by
  obtain ⟨o,S,len,fall,pre,reset,lead,flight,door,k,_,_,W,early,_,_,own,C,K,loc,
    _,launch,pc,G0,allow,bank,G,A,F,_,lit⟩ := actual_attempt hp u v tail facts hh sep Q I fiber closed mark center pub
  let cut := pre++reset
  let origin := run x cut
  let root := (S.getD 0 fall).1
  let whole := (u++v)++tail
  have keep (z : X) (w : List (Fin n)) (J : Q z) : Q (run z w) := by
    induction w generalizing z with
    | nil => exact J
    | cons e w ih => exact ih _ (closed z e J)
  have same (w : List (Fin n)) : oldH6 B (run x w)=oldH6 B base :=
    funext (fun i => (congrArg Prod.fst (fiber _ (keep x w I) i)).symm)
  obtain ⟨s,K₀,p,b,loc0,sc,sel,L⟩ := stopping_commit hp (run x whole) mark center pub
  have hc : oldH6 B base center=true := by
    rw [←same whole]
    have left := L.2.1
    rw [loc0]
    cases s <;> exact left
  obtain ⟨leadA,ack,all⟩ := attempt_wins hp C Q (keep x cut I) fiber closed sep
    lead flight door center k K loc own G A launch pc F
  refine ⟨o,cut++leadA,ack,root,?_⟩
  intro j
  obtain ⟨a,b0,suffix,birth,i,visit,matchA,matchC,owned,head,won,live,inc,vs,vh,fields,before⟩ := all j
  let atBirth := cut++a
  have orig (w : List (Fin n)) : run x (cut++w)=run origin w :=
    BStarResetSchedule.run_append step x cut w
  have centerEq : j=1 → i=center := by
    intro E
    have owns : commandOwner (oldH6 B base) i 1=o.val := by
      rw [E] at owned
      exact owned
    have H := (endpoint_spec (oldH6 B base) hh o 1).2.2
    exact congrArg Prod.fst ((H i head owns).trans (H center hc own).symm)
  have split : u++(v++tail)=atBirth++birth::suffix := by
    have R : (u++v)++tail=cut++(lead++door::flight) := by
      simpa only [cut,List.append_assoc] using W
    calc
      u++(v++tail) = (u++v)++tail := (List.append_assoc _ _ _).symm
      _ = cut++(lead++door::flight) := R
      _ = cut++(a++birth::suffix) := congrArg (cut++·) matchC
      _ = atBirth++birth::suffix := (List.append_assoc _ _ _).symm
  have later : u.length≤atBirth.length := by
    simp only [atBirth,cut,List.length_append]
    omega
  have held : Continuous hp (step (run x atBirth) birth) i j suffix :=
    (orig a).symm ▸ live
  have prior : j=1 → BeforePublication hp (step (run x atBirth) birth) i suffix := by
    intro eq
    have siteEq := centerEq eq
    exact siteEq.symm ▸ ((orig a).symm ▸ before)
  let acq : Acquisition hp x u (u++(v++tail)) i j :=
    ⟨atBirth,birth,suffix,split,later,(orig a).symm ▸ won,held,prior⟩
  have atSlot : i=(endpoint (oldH6 B base) hh o ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1 :=
    congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o _).2.2 i head owned)
  refine ⟨i,visit,acq,?_,atSlot,centerEq,inc,?_,?_,?_,?_⟩
  · exact ⟨b0,by change cut++leadA=atBirth++birth::b0; rw [matchA]; simp only [atBirth,List.append_assoc]⟩
  · change visit.selector=BStarLongPublication.readSel ((run x atBirth) i).long
    exact (orig a).symm ▸ vs
  · change visit.headers=headerBits ((run x atBirth) i).long
    exact (orig a).symm ▸ vh
  · exact (orig leadA).symm ▸ fields
  · intro sites H
    have E := operand_at_acquire hp base x u (v++tail) i j sites acq sep
      (fun w => same (u++w)) (fun w e z => facts.body w e z i head) H
    simpa only [List.append_assoc] using E

/-- The three exact operand addresses are the door word, the
next word, and the following word modulo the fixed H6 layout.
This allows all three incidences even when their words alias. -/
theorem operand_word_address {h : Fin n → Bool} (hh : ∃ i,h i=true)
    (o : Owners h) (j : Fin 3) :
    word h (endpoint h hh o ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1=
      (o.val+(j.val : Int))%(total h : Int) := by
  let k : Fin 11 := ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩
  let i := (endpoint h hh o k).1
  have own := (endpoint_spec h hh o k).2.1
  have D : cmdDispl k=(j.val : Int) := by
    have T : ∀ q : Fin 3, cmdDispl ⟨q.val,Nat.lt_trans q.isLt (by decide : 3<11)⟩=(q.val : Int) := by decide +kernel
    exact T j
  change word h i=_
  rw [←D,←own]
  change word h i=addressWord (total h) (owner (total h) (word h i) (cmdDispl k)) (cmdDispl k)
  rw [address_inverse]
  exact (Int.emod_emod _ _).symm

/-- The three physical ports in the large branch correspond to
different cyclic words as soon as the fixed layout has three
headers. The readout itself does not rely on this extra bound. -/
theorem operand_words_injective {h : Fin n → Bool} (hh : ∃ i,h i=true)
    (o : Owners h) (three : 3≤total h) :
    Function.Injective (fun j : Fin 3 => word h (endpoint h hh o
      ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1) := by
  intro j k E
  have EQ : (o.val+(j.val : Int))%(total h : Int)=(o.val+(k.val : Int))%(total h : Int) :=
    (operand_word_address hh o j).symm.trans (E.trans (operand_word_address hh o k))
  have J := j.isLt
  have K := k.isLt
  have cancel (a b : Fin 3) (ha : a.val<3) (hb : b.val<3) (order : b.val≤a.val)
      (eq : (o.val+(a.val : Int))%(total h : Int)=(o.val+(b.val : Int))%(total h : Int)) :
      a.val=b.val := by
    have R := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp eq
    have diff : (o.val+(a.val : Int))-(o.val+(b.val : Int))=(a.val : Int)-(b.val : Int) := by omega
    rw [diff,Int.emod_eq_of_lt (by omega) (by omega)] at R
    omega
  apply Fin.ext
  by_cases L : k.val≤j.val
  · exact cancel j k J K L EQ
  · exact (cancel k j K J (by omega) EQ.symm).symm

#print axioms operand_words_injective
#print axioms operand_word_address
#print axioms actual_operands
end L4.BStarPostCutOperands

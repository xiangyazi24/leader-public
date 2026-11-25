import Leader.L4.BStarNativePortGeometry

namespace L4.BStarNativeLogicalTrace
open AllSizeProtocol BStarTrace BStarLongWork BStarLongFixedRouting BStarH6WordChart
open BStarH6Ordinal BStarAcquireAnchors BStarAcquireLiteralChain BStarCustodyCuts BStarGrantWriterHistory
open BStarNativePortGeometry BStarNativePointwise BStarOperandBank
open BStarLongCommand BStarLongToken BStarCommitReceiptAuth
open L4.Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Receipt authentication is taken on the entire literal prefix ending
just before the marked COMMIT. -/
def ReceiptOn {h : Fin n→Bool} (hh : ∃ i,h i=true) (initial : X)
    (raw : List (Fin n)) (o : Owners h) (receipt : Payload) : Prop :=
  ∃ (prior rest : List (Fin n)) (select : Fin n) (op : Nat)
      (d : BStarLongPublication.Descriptor) (selectedBank : Fin 3),
    raw=prior++select::rest ∧
    let src := run initial prior (endpoint h hh o 0).1
    bind (longGeometry B src) 0 (atSite src.long 0)=.reply receipt ∧
    ReceiptBank op d receipt selectedBank

/-- Any certified alignment emits no logical label on a silent mark,
and one actual receipt-driven logical label on a COMMIT. The raw
prefix is carried forward separately from the emitted list. -/
inductive Align {h : Fin n→Bool} (hh : ∃ i,h i=true) (initial : X) :
    List (Fin n) → List (Fin n) → List (Header h × Bool) → Prop where
  | nil {past} : Align hh initial past [] []
  | silent {past remaining logical} {e : Fin n}
      (N : NoPublication hp (run initial past) e e)
      (R : Align hh initial (past++[e]) remaining logical) :
      Align hh initial past (e::remaining) logical
  | commit {past remaining logical} {e : Fin n} (center : Header h)
      (loc : center.val=e)
      (N : ¬NoPublication hp (run initial past) e e)
      (owner : Owners h) (receipt : Payload)
      (arrived : ReceiptOn hp hh initial past owner receipt)
      (R : Align hh initial (past++[e]) remaining logical) :
      Align hh initial past (e::remaining)
        ((center,(nativeSpec r (bankAt (r:=r) (run initial past)
          (fun j : Fin 3 => (endpoint h hh owner ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1))).1 &&
            decide (receipt.argument.toNat%2=1))::logical)

noncomputable def runLogical {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (x : Header h→NativeRecord) : List (Header h × Bool)→(Header h→NativeRecord)
  | [] => x
  | (i,delta)::tail => runLogical hh (activate (r:=r) hh x i delta) tail

/-- Deterministic trace lifting on every finite suffix after a fixed
completed custody prefix. The list retains one authenticated update per
physical COMMIT and omits every silent mark. -/
theorem lift_suffix {base initial : X} (u v lead suffix : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e)) (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    let H := oldH6 B base
    let decode (w : List (Fin n)) : Header H→NativeRecord :=
      fun i=>readRecord (run initial w) i.val
    ∃ logical, Align hp hh initial ((u++v)++lead) suffix logical ∧
      decode ((u++v)++(lead++suffix))=runLogical (r:=r) hh (decode ((u++v)++lead)) logical := by
  let H := oldH6 B base
  let decode (w : List (Fin n)) : Header H→NativeRecord :=
    fun i=>readRecord (run initial w) i.val
  change ∃ logical, Align hp hh initial ((u++v)++lead) suffix logical ∧ _
  induction suffix generalizing lead with
  | nil =>
    exact ⟨[],.nil,by simp only [List.append_nil,runLogical]⟩
  | cons e suffix ih =>
    obtain ⟨events,E,final⟩ := ih (lead++[e])
    have one := actual_mark_logical hp u v lead cuts hh sep Q I fiber closed e hr flags notShort
    have prefixEq : (u++v)++(lead++[e])=((u++v)++lead)++[e] := (List.append_assoc _ _ _).symm
    have nextEq : run initial ((u++v)++(lead++[e]))=step (run initial ((u++v)++lead)) e := by
      rw [prefixEq,BStarResetSchedule.run_append]
      rfl
    have endEq : lead++e::suffix=(lead++[e])++suffix := by
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    rcases one with ⟨N,hold⟩|⟨Y,center,owner,receipt,whereAt,ports,auth,moved⟩
    · refine ⟨events,.silent N (prefixEq ▸ E),?_⟩
      rw [endEq,final]
      have D : decode ((u++v)++(lead++[e]))=decode ((u++v)++lead) := by
        unfold decode
        exact nextEq.symm ▸ hold
      exact congrArg (fun z=>runLogical (r:=r) hh z events) D
    · let bank := bankAt (r:=r) (run initial ((u++v)++lead))
        (fun j : Fin 3 => (endpoint H hh owner ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1)
      let delta := (nativeSpec r bank).1 && decide (receipt.argument.toNat%2=1)
      refine ⟨(center,delta)::events,.commit center whereAt Y owner receipt auth (prefixEq ▸ E),?_⟩
      have D : decode ((u++v)++(lead++[e]))=
          activate (r:=r) hh (decode ((u++v)++lead)) center delta := by
        unfold decode
        exact nextEq.symm ▸ moved
      rw [endEq,final]
      exact congrArg (fun z=>runLogical (r:=r) hh z events) D

#print axioms lift_suffix
end L4.BStarNativeLogicalTrace

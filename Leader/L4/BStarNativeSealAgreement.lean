import Leader.L4.BStarNativeCompletePublication
import Leader.L4.BStarFirstActualPublication
import Leader.L4.BStarNativeNeedLift

namespace L4.BStarNativeSealAgreement
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarLongEvents BStarLongLiteral BStarLongCommand BStarLongToken
open BStarLongPublication BStarBitNoAbort BStarLongLayout BStarH6WordChart BStarAcquireLiteralChain BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- At a particular physical COMMIT the selected literal descriptor
and the still-sealed old descriptor are the same value. -/
theorem handoff_descriptor {base old x408 : X}
    {slot : Nat→BStarAcquireVisitOrder.Pos n} {len : Nat} {rem rest : List (Fin n)} {i : Fin n}
    (H : BStarNativeActualLoadAccepted.CommitHandoff hp base old x408 slot len rem rest i i)
    {d : Descriptor} (sealed : SealedCenter d (old i).long) :
    H.descriptor=d := by
  obtain ⟨K,payload,offer,literal,dec⟩ := H.selected
  let g := oldPair B old i
  let raw : Pair (BitVec LW) := ((old i).long,(old (rightNeighbor i)).long)
  have km : K∈(actualOffers g raw).map Prod.fst :=
    List.mem_map.mpr ⟨(K,.advance payload),offer,rfl⟩
  rw [actualOffers_claims] at km
  have eq := center_of g K km literal.1
  obtain ⟨_,_,_,_,e,E,_,guarded⟩ := literal
  have same : e=H.descriptor := Option.some.inj (E.symm.trans dec)
  subst e
  rw [eq] at guarded
  change BStarLongPublication.guard true 1 raw.1 H.descriptor H.bank=true at guarded
  have stageEq : readOptional (stage.read raw.1)=some H.descriptor := by
    simp only [BStarLongPublication.guard,typedGuard,Bool.and_eq_true,beq_iff_eq] at guarded
    exact guarded.1.1.2
  exact Option.some.inj (stageEq.symm.trans sealed.2.2.1)

open BStarCustodyCuts BStarGrantWriterHistory BStarOperandBank BStarAcquireAnchors
open BStarNativePortGeometry BStarNativePointwise BStarNativeNeedLift BStarH6Ordinal
open L4.Compiler.Native
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The marked publication with old sealed NEED is an exact native
NEED activation, independently of the sign or representation of the clock. -/
theorem sealed_need_activation {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (i : Fin n) (pub : ¬NoPublication hp (run initial ((u++v)++tail)) i i)
    (hr : 3≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (d : Descriptor) (need : d.need=true)
    (sealed : SealedCenter d ((run initial ((u++v)++tail)) i).long)
    :
    let old := run initial ((u++v)++tail)
    let before : Header (oldH6 B base)→NativeRecord := fun j=>readRecord (r:=r) old j.val
    let after : Header (oldH6 B base)→NativeRecord := fun j=>readRecord (r:=r) (step old i) j.val
    ∃ (center : Header (oldH6 B base)) (bank : Bank) (delta : Bool),
      center.val=i ∧ (∀ q,decodeBank r bank q=before (neighborHeader hh center q)) ∧
      (nativeSpec r bank).1=true ∧ after=activate (r:=r) hh before center delta := by
  classical
  let old := run initial ((u++v)++tail)
  obtain ⟨o,S,len,fall,pre,reset,w,entry,compiler,remainder,rest,_,_,C,
    L,pf,ef,cf,Hf,ready,H,selPre,sel,selAfter,op,receipt,split,reply,auth,needDesc,output⟩ :=
    BStarNativeCompletePublication.with_descriptor_need hp u v tail cuts hh sep Q I fiber closed i i pub hr flags notShort
  let header := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
  let bank := bankAt (r:=r) old header
  have exactNeed : (nativeSpec r bank).1=true :=
    needDesc.symm.trans ((congrArg Descriptor.need (handoff_descriptor hp H sealed)).trans need)
  have mem : S.getD H.cursor fall∈S := by
    rw [←List.getElem_eq_getD (h:=show H.cursor<S.length by rw [C.length]; exact Nat.lt_succ_of_le H.cursor_le)]
    exact List.getElem_mem _
  have own := (C.entries _ mem).2
  rw [H.atCenter] at own
  have mid : i=header 1 :=
    congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o 1).2.2 i H.centerH6 own)
  rcases actual_mark_logical hp u v tail cuts hh sep Q I fiber closed i hr flags notShort with
    ⟨silent,_⟩|⟨_,center,owner,received,loc,ports,_,write⟩
  · exact (pub silent).elim
  let other := bankAt (r:=r) old (fun q : Fin 3 =>
    (endpoint (oldH6 B base) hh owner ⟨q.val,by omega⟩).1)
  have samePorts (q : Fin 3) : decodeBank r other q=decodeBank r bank q :=
    (ports q).trans ((ports_are_neighbors old hh o center (mid.symm.trans loc.symm) q).symm)
  have nativeNeed : (nativeSpec r other).1=true := by
    unfold nativeSpec at exactNeed ⊢
    rwa [samePorts 0,samePorts 1,samePorts 2]
  exact ⟨center,other,(nativeSpec r other).1 && decide (received.argument.toNat%2=1),loc,ports,nativeNeed,write⟩

/-- In the upper-half lift representation the sealed native increment
advances the chosen natural counter by one, including at wrap. -/
theorem sealed_need_increments {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (i : Fin n) (pub : ¬NoPublication hp (run initial ((u++v)++tail)) i i)
    (hr : 3≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (d : Descriptor) (need : d.need=true)
    (sealed : SealedCenter d ((run initial ((u++v)++tail)) i).long)
    (P : Nat) (M : modulus r=2*P) (positive : 0<P)
    (counts : Header (oldH6 B base)→Nat)
    (init : ∀ j,Represents P (readRecord (r:=r) (run initial ((u++v)++tail)) j.val) (counts j)) :
    ∀ j, Represents P (readRecord (r:=r) (step (run initial ((u++v)++tail)) i) j.val)
      (if j.val=i then counts j+1 else counts j) := by
  classical
  obtain ⟨center,bank,delta,loc,ports,nativeNeed,write⟩ :=
    sealed_need_activation hp u v tail cuts hh sep Q I fiber closed i pub hr flags notShort d need sealed
  have result := tagged_native_increment hh _ _ center bank delta
    ports nativeNeed write P M positive counts init
  intro j
  by_cases E : j.val=i
  · have same : j=center := Subtype.ext (E.trans loc.symm)
    rw [if_pos E]
    simpa only [if_pos same] using result.1 j
  · have diff : j≠center := fun D=>E ((congrArg Subtype.val D).trans loc)
    simpa only [if_neg E,if_neg diff] using result.1 j

#print axioms sealed_need_activation
#print axioms sealed_need_increments
#print axioms handoff_descriptor
end L4.BStarNativeSealAgreement

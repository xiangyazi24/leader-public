import Leader.L4.BStarGrantBirth
import Leader.L4.BStarResetIssueClean
import Leader.L4.BStarReleaseOrigin

namespace L4.BStarResetNoAcquire
open AllSizeProtocol BStarTrace BStarLongWork BStarLongTransport BStarLongToken
open BStarLongGrant BStarLongCommandData BStarLongCommand BStarReleaseOrigin
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetChartService BStarResetSchedule BStarSeparatingRail
open BStarResetHealthyService BStarResetIssueClean BStarResetTaggedRows
open BStarAcquireForwardTrace BStarGrantBirth

abbrev slot (j : Fin 3) : Fin 11 := ⟨j.val,by have := j.isLt; omega⟩

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B


def NoAcquireAt (x : X) (i : Fin n) (j : Fin 3) : Prop :=
  ∀ q, atCursor x (i,slot j)=.forward q → ¬ HealthyOp acquire q

theorem no_win_at (x : X) (e i : Fin n) (j : Fin 3)
    (N : NoAcquireAt x i j) : ¬ WonAt hp x e i j := by
  intro H
  rcases H with ⟨side,atSite,_,_,C,q,mem,CS,CJ,hf,op⟩
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have R : requested (round g raw).offered side j acquire=true := by
    apply List.any_eq_true.mpr
    exact ⟨(C,.advance q),mem,by simp [CS,CJ,hf,op]⟩
  obtain ⟨C,p,q,_,sideEq,jEq,_,_,old,healthy⟩ := pre_grant_acquire_origin g raw side j R
  have root : (site e C.source.side,C.source.occurrence)=(i,slot j) :=
    Prod.ext ((congrArg (site e) sideEq).trans atSite) (Fin.ext jEq)
  have rd : oldTokens raw C.source=atCursor x (site e C.source.side,C.source.occurrence) := by
    obtain ⟨s,k⟩ := C.source
    cases s <;> rfl
  exact N q ((congrArg (atCursor x) root).symm.trans (rd.symm.trans old)) healthy

theorem quiet_no_acquire (x : X) (i : Fin n) (j : Fin 3)
    (Q : atCursor x (i,slot j)=.empty ∨ atCursor x (i,slot j)=.trail ∨
      atCursor x (i,slot j)=.forward (resetPayload 2) ∨ ∃ p, atCursor x (i,slot j)=.reply p) :
    NoAcquireAt x i j := by
  intro q H A
  rcases Q with E|T|F|⟨p,D⟩
  · rw [E] at H
    contradiction
  · rw [T] at H
    contradiction
  · have e := Token.forward.inj (F.symm.trans H)
    have x := congrArg (fun z : Payload => z.opcode.toNat) e
    rw [A.2] at x
    contradiction
  · rw [D] at H
    contradiction

/-- Every owned incidence occurs in the active chart (indices 0,1,2
are never dormant). A clean pointed RREL contains no potential own
ACQUIRE at any such address, whether outward or returning. -/
theorem good_no_acquire {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (z : Cursor)
    (G : Good (healthyTag 2) len (project (fun j => S.getD j fall) x) z)
    (clean : CleanSuffix len (project (fun j => S.getD j fall) x) z)
    (i : Fin n) (j : Fin 3)
    (own : commandOwner (oldH6 B base) i (slot j)=o.val) : NoAcquireAt x i j := by
  let u : Pos n := (i,slot j)
  have active : active (longGeometry B (base i)) (slot j)=true := by
    have b := j.isLt
    unfold BStarAcquireRailCoverage.active slot
    simp [show j.val≠8 by omega,show j.val≠9 by omega]
  have m : u∈S := C.cover u active own
  obtain ⟨k,hk,E⟩ := List.getElem_of_mem m
  have idx : S.getD k fall=u := (List.getElem_eq_getD _).symm.trans E
  have L := C.length
  have valid : k≤len := by omega
  let rail := project (fun j => S.getD j fall) x
  have Eq : rail k=atCursor x u := congrArg (atCursor x) idx
  apply quiet_no_acquire
  change atCursor x u=Token.empty ∨ atCursor x u=Token.trail ∨
    atCursor x u=Token.forward (resetPayload 2) ∨ ∃ p,atCursor x u=Token.reply p
  rw [←Eq]
  cases z with
  | out s =>
    rcases Nat.lt_trichotomy k s with lt|rfl|gt
    · exact .inr (.inl (G.2.2 k lt))
    · exact .inr (.inr (.inl G.2.1))
    · exact .inl (clean k gt valid)
  | back s =>
    rcases Nat.lt_trichotomy k s with lt|rfl|gt
    · exact .inr (.inl (G.2.2.1 k lt))
    · exact .inr (.inr (.inr ⟨resetPayload 2, G.2.1⟩))
    · exact .inl (G.2.2.2 k gt valid)

#print axioms good_no_acquire
#print axioms no_win_at
end L4.BStarResetNoAcquire

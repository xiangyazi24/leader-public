import Leader.L4.BStarAcquireForwardTrace
import Leader.L4.BStarResetNoFault
import Leader.L4.BStarLongGrantProjection
import Leader.L4.BStarLongFiberOwner

/-! Literal authority effects of a selected RREL old departure. -/
namespace L4.BStarResetReleaseAuthority
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongGrant BStarLongTransport
open BStarResetTaggedRows BStarResetNoFault

theorem release_requested (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (j : Fin 3)
    (hc : C∈orderedCommands g) (hn : C.kind≠.door)
    (hj : C.source.occurrence.val=j.val)
    (old : readK raw C.source=.forward (resetPayload 2)) :
    requested (round g raw).offered C.source.side j releaseOp=true := by
  have hnd : (C.kind==.door)=false := Bool.eq_false_iff.mpr
    (fun E => hn (beq_iff_eq.mp E))
  have hG := gated_reset g raw C (resetPayload 2) hc hnd old (.inr (.inr (.inl rfl)))
  have safe := reset_no_prep_fault g raw C 2 (.inr (.inr rfl)) hG
  have hit : (C,.advance (resetPayload 2))∈(round g raw).offered := by
    change _ ∈ (gated g raw).map (cancel (round g raw).faults)
    exact List.mem_map.mpr ⟨_,hG,by simp [cancel,safe]⟩
  apply List.any_eq_true.mpr
  exact ⟨_,hit,by simp [hj,resetPayload,releaseOp]⟩

/-- A release beats even a simultaneous acquisition for that same
incidence; it does not grant any newly exposed authority on the
old release mark. This is valid for corrupt old grants as well. -/
theorem result_release (old rel ask : Ports) (j : Fin 3) (H : rel j=true) :
    result old rel ask j=false := by
  unfold result win
  by_cases E : j=1
  · subst j
    simp [H]
  · simp [H,E]

/-- On the exact joined physical pair, selecting a genuine old RREL
at its hardwired incidence clears that old grant independently of
the data bytes, other commands, and outer door repair. This is not
an implication from a returned payload alone. -/
theorem joined_release (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (j : Fin 3) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.kind≠.door →
    C.source.occurrence.val=j.val →
    readK raw C.source=.forward (resetPayload 2) →
    BStarLongGrantProjection.read (Pair.map LargeSite.long (largePair b x)) C.source.side j=0 := by
  dsimp only
  intro hc hn hj old
  rw [BStarLongGrantProjection.joined_grants _ _ _ _ _ _ _ _ _ hp x C.source.side j]
  have H := release_requested _ _ C j hc hn hj old
  unfold BStarLongGrantProjection.grants
  rw [result_release _ _ _ _ H]
  simp

/-- In the absence of a request at an incidence a cleared grant
cannot reappear, including on canonicalization of arbitrary bits. -/
theorem zero_without_request (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (o : Offers) (s : Side) (j : Fin 3)
    (H : original (BStarLongGrant.atOld raw s) j=false)
    (N : requested o s j acquire=false) :
    BStarLongGrantProjection.grants g raw o s j=false := by
  let orig := original (BStarLongGrant.atOld raw s)
  have K : canonical orig j=false := by
    by_cases X : orig 1=true
    · have J : j≠1 := fun E => by subst j; exact Bool.noConfusion (X.symm.trans H)
      have T : (j==1)=false := Bool.eq_false_iff.mpr (fun E => J (beq_iff_eq.mp E))
      simp [canonical,X,T]
    · have Y : orig 1=false := Bool.eq_false_iff.mpr X
      exact (show canonical orig j=orig j by simp [canonical,Y]).trans H
  have W : win orig (fun k => requested o s k releaseOp) (fun k => requested o s k acquire) j=false := by
    by_cases E : j=1
    · subst j
      simp [win,N]
    · simp [win,E,N]
  change ((geometry g s).axes.h6 && result orig (fun k => requested o s k releaseOp) (fun k => requested o s k acquire) j) = false
  simp [result,K,W]

open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace

/-- A physical RREL departure at an indexed outbound occurrence.
This carries the selected old pair, not merely equal decoded bits
at the beginning and the end of a tour. -/
def serviceAt {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (u : Pos n) : Prop :=
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  ∃ C∈orderedCommands (oldPair b x e), C.kind≠.door ∧
    u=(site e C.source.side,C.source.occurrence) ∧ atCursor x u=.forward (resetPayload 2)

/-- Every indexed actual RREL service with occurrence 0/1/2 clears
its one intrinsic incidence grant in the physical ring snapshot. -/
theorem service_zero {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (he : e≠rightNeighbor e) (u : Pos n) (j : Fin 3)
    (idx : u.2.val=j.val) (H : serviceAt hp x e u) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (BStarLongLayout.grant j).read ((AllSizeS1Geometry.step b x e) u.1).long=0 := by
  obtain ⟨C,hc,hn,rfl,H⟩ := H
  dsimp only
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  have old : readK ((x e).long,(x (rightNeighbor e)).long) C.source=.forward (resetPayload 2) := by
    have T : readK ((x e).long,(x (rightNeighbor e)).long) C.source=
      atCursor x (site e C.source.side,C.source.occurrence) := by
      obtain ⟨s,j⟩ := C.source
      cases s <;> rfl
    exact T.trans H
  have K := joined_release k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) C j hc hn idx old
  change (BStarLongLayout.grant j).read ((AllSizeS1Geometry.step b x e) (site e C.source.side)).long=0
  cases S : C.source.side
  · have Q : AllSizeS1Geometry.step b x e e=(largePair b (x e,x (rightNeighbor e))).1 := by
      simp only [AllSizeS1Geometry.step,if_true]
    change (BStarLongLayout.grant j).read ((AllSizeS1Geometry.step b x e) e).long=0
    rw [Q]
    rw [S] at K
    exact K
  · have Q : AllSizeS1Geometry.step b x e (rightNeighbor e)=
        (largePair b (x e,x (rightNeighbor e))).2 := by
      simp only [AllSizeS1Geometry.step,if_neg (Ne.symm he),if_true]
    change (BStarLongLayout.grant j).read ((AllSizeS1Geometry.step b x e) (rightNeighbor e)).long=0
    rw [Q]
    rw [S] at K
    exact K

end L4.BStarResetReleaseAuthority

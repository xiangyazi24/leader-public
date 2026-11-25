import Leader.L4.DirtyPrepRank
import Leader.L4.DirtyForwardAdvance
import Leader.L4.DirtyPrepFrontier

namespace L4.DirtyPrepWeak
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarResetChartTouch BStarResetMarkAdapter BStarLongFiberOwner
open BStarClearanceSource (Held held_before)
open BStarClearanceIndexedSum BStarClearanceIndexedWait BStarClearanceOffset
open BStarLongCommand BStarLongEvents BStarLongTransport BStarLongRouting
open BStarClearanceCommandSum BStarClearanceForward BStarClearanceChartFootprint
open BStarResetQuietTable BStarClearanceNonforward BStarLongDoor BStarResetQuiet
open BStarClearanceGate (forwardRank weight)
open BStarClearanceCommandFrame (forwardCount bind_counts)
open DirtyLeastForward (ringF isForward_iff)
open DirtyPrepRank (debt)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem debt_rank (base x : X) (u : Pos n) :
    debt hp base x u=physicalRank B base x (fun _=>0) u := by
  have E (g : LongGeometry) (j : Fin 11) (t : Token) :
      weight g j t=forwardRank g j 0 t := by cases t <;> simp [forwardRank,weight]
  exact E _ _ _

private theorem only_door_touch (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (H : g.2.axes.h6=true) :
    BStarResetQuiet.avoids (R 0) (BStarResetQuiet.middle g raw) := by
  apply BStarResetQuiet.middle_avoids_of_chart
  intro o ho hslot
  have hc : o.1∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨o,ho,rfl⟩
  have hd : BStarCommitIssue.doorClaim∈orderedCommands g := by
    have D := BStarDoorUnique.claim_door_singleton g H
    exact (List.mem_filter.mp (D.symm ▸ (List.mem_singleton_self _))).1
  have oc := BStarAcquireIncidence.same_claim g o.1 BStarCommitIssue.doorClaim (R 0)
    hc hd hslot (by decide)
  have eg : BStarLongLiteral.gatedAt g raw o.1=.door (bound g (readK raw) (R 0)) := by
    rw [oc]
    rfl
  have od := BStarAcquireNonRouting.actual_door g raw o ho _ eg
  obtain ⟨c,f⟩ := o
  dsimp only at od
  subst f
  intro w hw
  unfold selected at hw
  dsimp only at hw
  split at hw <;> simp at hw

private theorem door_offer_is_door (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (D : C.kind=.door) (hc : C∈orderedCommands g)
    (pay : Payload) : (C,.advance pay)∉actualOffers g raw := by
  intro U
  obtain ⟨E,_,_⟩ := BStarResetChartIndex.selected_door g C hc D
  have H : C=BStarCommitIssue.doorClaim := by
    apply BStarAcquireIncidence.same_claim g C BStarCommitIssue.doorClaim (R 0) hc
    · have Hh := (BStarResetChartIndex.selected_door g C hc D).2.1
      have U' := BStarDoorUnique.claim_door_singleton g Hh
      exact (List.mem_filter.mp (U'.symm ▸ (List.mem_singleton_self _))).1
    · rw [←E]
      simp [Claim.slots]
    · decide
  have G : BStarLongLiteral.gatedAt g raw C=.door (bound g (readK raw) (R 0)) := by
    rw [H]
    rfl
  exact Offer.noConfusion (BStarAcquireNonRouting.actual_door g raw (C,.advance pay) U _ G)

/-- No nonnominated old mark increases gate debt if the least old
prep forward survives. The geometry used for the debt is the fixed
chart snapshot, via the actual clipped-offset certificate. -/
theorem weak_held_least
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (held : Held (x (S.getD 0 fall).1).long)
    {i : Nat} (I : i≤len) (prep : (S.getD i fall).2.val≤5)
    (F : ringF x (S.getD i fall)) (least : ∀ k,k<i → ¬ringF x (S.getD k fall))
    (e : Fin n) (live : ringF (step x e) (S.getD i fall)) :
    debt hp base (step x e) (S.getD i fall)≤debt hp base x (S.getD i fall) := by
  let u := S.getD i fall
  let z := (x e,x (rightNeighbor e))
  let g := oldPair B x e
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  let y := step x e
  have iS : i<S.length := by have := chart.length; omega
  have U : u∈S := by
    dsimp only [u]
    rw [←List.getElem_eq_getD (h:=iS) fall]
    exact List.getElem_mem _
  by_cases cut : u.1=e ∨ u.1=rightNeighbor e
  · obtain ⟨a,eq⟩ : ∃ a : AtK, address e a=u := by
      obtain ⟨p,k⟩ := u
      rcases cut with E|E <;> dsimp only at E <;> subst p
      · exact ⟨L k,rfl⟩
      · exact ⟨R k,rfl⟩
    have ar : address e a∈S := eq ▸ U
    have Wait := held_before hp x (S.getD 0 fall).1 e held
    rw [congrArg Prod.fst chart.root] at Wait
    obtain ⟨part,own,adj⟩ := chart_owner_hypotheses hp chart layout e
    obtain ⟨safe,_⟩ := pre_service_hypotheses hp chart layout e (sep e) Wait
    have oldForward (t : AtK) : (∃ pay,bound g (readK raw) t=.forward pay) ↔ ringF x (address e t) := by
      rcases t with ⟨side,j⟩
      cases side <;> exact isForward_iff _ _ _
    obtain ⟨pay,Fx⟩ := (oldForward a).mpr (eq ▸ F)
    have pred (C : CommandClaim) (hc : C∈orderedCommands g) (ac : C.destination=some a)
        (t : Payload) : bound g (readK raw) C.source≠.forward t := by
      intro Fsrc
      have hslot : a∈C.slots := by simp [Claim.slots,ac]
      have ownC := (footprint_owner B x e C hc a hslot).symm.trans (own a ar)
      have mem : address e C.source ∈ S :=
        part (List.mem_flatten.mpr ⟨_,List.mem_map.mpr
          ⟨C,List.mem_filter.mpr ⟨hc,beq_iff_eq.mpr ownC⟩,rfl⟩,
          List.mem_map.mpr ⟨C.source,by simp [Claim.slots],rfl⟩⟩)
      obtain ⟨k,kS,eqK⟩ := List.mem_iff_getElem.mp mem
      have D := (adj C hc ownC).1 a ac
      erw [eq,←eqK,show u=S[i] from (List.getElem_eq_getD (h:=iS) fall).symm,
        distance_idx chart.nodup kS,distance_idx chart.nodup iS] at D
      have idK : S.getD k fall=address e C.source :=
        (List.getElem_eq_getD (h:=kS) fall).symm.trans eqK
      exact least k (by omega) (idK ▸ (oldForward C.source).mp ⟨t,Fsrc⟩)
    have prepA : a.occurrence.val≤5 := by
      have id := congrArg Prod.snd eq
      change a.occurrence=u.2 at id
      rw [id]
      exact prep
    have R := DirtyPrepFrontier.prep_mark_cases k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      z a pay prepA Fx (safe a ar) pred (fun C hc door src => by
        have ⟨E,H,_⟩ := BStarResetChartIndex.selected_door g C hc door
        subst a
        rw [E]
        exact joined_idle_rank k₁ k₂ t₂ J₁ J₂ r c p c₁ hp z (R 0) 0
          (only_door_touch g raw H) (safe _ (E ▸ ar)))
    rcases R with ⟨C,payC,W,src⟩|R
    · have hc : C∈orderedCommands g := by
        rw [←actualOffers_claims g raw]
        exact List.mem_map.mpr ⟨_,W,rfl⟩
      have nd : C.kind≠.door := fun D => door_offer_is_door g raw C D hc payC W
      exact False.elim (DirtyForwardAdvance.ring_advance_removes_forward hp x e (sep e) C payC W nd
        ((congrArg (address e) src |>.trans eq) ▸ live))
    · have current (b' : X) := rank_fixed hp (oldH6 B base) hh base x b' (fun _ => rfl)
          (fun t => (congrArg Prod.fst (layout t)).symm) cb cx (fun _=>0) u
      rw [debt_rank hp, debt_rank hp,current _,current _,←eq]
      rcases a with ⟨side,j⟩
      cases side
      · simp only [physicalRank,site,AllSizeS1Geometry.step,if_true]
        exact R
      · simp only [physicalRank,site,AllSizeS1Geometry.step,if_neg (Ne.symm (sep e)),if_true]
        exact R
  · have Y : y u.1=x u.1 := by
      simp [y,AllSizeS1Geometry.step,show u.1≠e from fun h => cut (.inl h),show u.1≠rightNeighbor e from fun h => cut (.inr h)]
    change debt hp base y u ≤ debt hp base x u
    simp [debt,Y]

end L4.DirtyPrepWeak

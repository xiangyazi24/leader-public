import Leader.L4.BStarClearanceDTBlock
import Leader.L4.BStarClearanceOwnerDT
import Leader.L4.BStarClearanceIndexedWait
import Leader.L4.BStarClearanceReplyService

namespace L4.BStarClearanceRingDT
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongTransport BStarLongEvents BStarLongCommand BStarLongRouting BStarResetQuiet
open BStarClearanceAggregate BStarClearanceDTBlock BStarClearanceChartFootprint
open BStarH6WordChart hiding total
open BStarLongFiberOwner BStarAcquireVisitOrder
open BStarClearanceReturnCharge
open BStarClearanceCommandFrame

def physicalDT {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (reply : Bool) (dist : Pos n → Nat) (u : Pos n) : Nat :=
  dist u * small reply (atSite (x u.1).long u.2)

theorem owner_DT_sum_paying {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (he : e≠rightNeighbor e) (o : Int) (slots : List (Pos n))
    (reply : Bool) (dist : Pos n → Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let z := (x e,x (rightNeighbor e))
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long z
    let adr := BStarResetMarkAdapter.address e
    let pre := physicalDT x reply dist
    let post := physicalDT (AllSizeS1Geometry.step b x e) reply dist
    let blocks := ownerBlocks b x e o
    slots.Nodup → blocks.flatten ⊆ slots →
    (∀ a, adr a∈slots → physicalOwner (oldH6 b x) e cmdDispl a=o) →
    (∀ a, adr a∈slots → BStarResetQuietTable.DoorSafe g raw a) →
    (∀ C q, (C,.advance q)∈actualOffers g raw →
        physicalOwner (oldH6 b x) e cmdDispl C.source≠o) →
    (∀ C t, (C,.reverse t)∈actualOffers g raw →
      physicalOwner (oldH6 b x) e cmdDispl C.source=o →
      reply=true ∧ ∃ a, C.destination=some a ∧ dist (adr a)=dist (adr C.source)+1) →
    total post slots≤total pre slots ∧
      ((∃ C t, (C,.reverse t)∈actualOffers g raw ∧
        physicalOwner (oldH6 b x) e cmdDispl C.source=o) →
        total post slots<total pre slots) ∧
      ((∃ Q∈blocks, total post Q<total pre Q) → total post slots<total pre slots) := by
  dsimp only
  intro ns sub owns safe noF rev
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let z := (x e,x (rightNeighbor e))
  let g := oldPair b x e
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long z
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b z)
  let adr := BStarResetMarkAdapter.address e
  let pre := physicalDT x reply dist
  let post := physicalDT (AllSizeS1Geometry.step b x e) reply dist
  let blocks := ownerBlocks b x e o
  have pre_eq (a : AtK) : pre (adr a)=dist (adr a)*small reply (readK raw a) := by
    rcases a with ⟨side,k⟩
    cases side <;> rfl
  have post_eq (a : AtK) : post (adr a)=dist (adr a)*small reply (readK y a) := by
    rcases a with ⟨side,k⟩
    cases side
    · simp [post,adr,physicalDT,AllSizeS1Geometry.step,site]; rfl
    · simp [post,adr,physicalDT,AllSizeS1Geometry.step,site,Ne.symm he]; rfl
  have memBlock (C : CommandClaim) (hc : C∈orderedCommands g)
      (ho : physicalOwner (oldH6 b x) e cmdDispl C.source=o) : footprint e C∈blocks := by
    exact List.mem_map.mpr ⟨C,List.mem_filter.mpr ⟨hc,beq_iff_eq.mpr ho⟩,rfl⟩
  have one (C : CommandClaim) (act : Offer) (H : (C,act)∈actualOffers g raw)
      (ho : physicalOwner (oldH6 b x) e cmdDispl C.source=o) :
      total post (footprint e C)≤total pre (footprint e C) ∧
        ∀ t, act=.reverse t → total post (footprint e C)<total pre (footprint e C) := by
    have hc : C∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨_,H,rfl⟩
    have S : ∀ a∈C.slots, BStarResetQuietTable.DoorSafe g raw a := by
      intro a ha
      exact safe a (sub (List.mem_flatten.mpr ⟨_,memBlock C hc ho,List.mem_map.mpr ⟨a,ha,rfl⟩⟩))
    let d := fun a : AtK => dist (adr a)
    let p := fun a : AtK => d a * small reply (readK raw a)
    let q := fun a : AtK => d a * small reply (readK y a)
    have conv (f : Pos n → Nat) (r : AtK → Nat) (E : ∀ a, f (adr a)=r a) :
        total f (footprint e C)=total r C.slots := by
      unfold total footprint
      rw [List.map_map,show f ∘ adr=r from funext E]
    rw [conv post q post_eq,conv pre p pre_eq]
    have distinct (a : AtK) (D : C.destination=some a) : C.source≠a :=
      Ne.symm (BStarAcquireReturn.link_shape g C a hc D).1
    cases act with
    | advance pay => exact (noF C pay H ho).elim
    | hold => exact ⟨joined_hold_block_DT _ _ _ _ _ _ _ _ _ hp z C reply d H S,
        by intro t J; contradiction⟩
    | clear => exact ⟨joined_clear_block_DT _ _ _ _ _ _ _ _ _ hp z C reply d H S distinct,
        by intro t J; contradiction⟩
    | door tok => exact ⟨joined_door_block_DT _ _ _ _ _ _ _ _ _ hp z C tok reply d H S,
        by intro t J; contradiction⟩
    | reverse tok =>
      obtain ⟨E,a,D,J⟩ := rev C tok H ho
      subst reply
      have V (u : AtK) (U : u=C.source ∨ u=a) := (S u (by
        rcases U with rfl|rfl <;> simp [Claim.slots,D])).valid
      have K := joined_reverse_pays _ _ _ _ _ _ _ _ _ hp z C a tok (d C.source) D
        (distinct a D) H V
      have K' : total (fun a => d a*small true (readK y a)) C.slots <
          total (fun a => d a*small true (readK raw a)) C.slots := by
        change d a=d C.source+1 at J
        have KZ (a : AtK) (d : Nat) (w : Pair (BitVec LW)) :
            returnRank g a d (readRaw w a)=d*small true (readK w a) := by
          unfold returnRank
          rw [show returnCount (BStarLongCommand.bind (geometry g a.side) a.occurrence
            (decode (readRaw w a)))=returnCount (readK w a) from
            congrArg (fun t : Nat × Nat × Nat => t.2.1) (bind_counts _ _ _)]
          rfl
        change returnRank g C.source (d C.source) (readRaw y C.source) +
          returnRank g a (d C.source+1) (readRaw y a) <
          returnRank g C.source (d C.source) (readRaw raw C.source) +
          returnRank g a (d C.source+1) (readRaw raw a) at K
        simp only [KZ] at K
        simpa [Claim.slots,D,total,J] using K
      exact ⟨Nat.le_of_lt K',fun _ _ => K'⟩
  have all : ∀ Q∈blocks, total post Q≤total pre Q := by
    intro Q hQ
    obtain ⟨C,H,rfl⟩ := List.mem_map.mp hQ
    obtain ⟨hc,ho⟩ := List.mem_filter.mp H
    change C∈orderedCommands g at hc
    rw [←actualOffers_claims g raw] at hc
    obtain ⟨⟨D,act⟩,hd,ee⟩ := List.mem_map.mp hc
    change D=C at ee
    subst D
    exact (one C act hd (beq_iff_eq.mp ho)).1
  have out : ∀ u∈remainder slots blocks, post u≤pre u := by
    intro u hu
    obtain ⟨hu,H⟩ := List.mem_filter.mp hu
    have off : u∉blocks.flatten := by simpa using H
    have atMark (a : AtK) (A : u=adr a) : post u≤pre u := by
      subst u
      rw [post_eq,pre_eq]
      have Nt : ∀ C∈orderedCommands g, a∉C.slots := by
        intro C hc ha
        have hown := (footprint_owner b x e C hc a ha).symm.trans (owns a hu)
        exact off (List.mem_flatten.mpr ⟨_,memBlock C hc hown,List.mem_map.mpr ⟨a,ha,rfl⟩⟩)
      exact joined_idle_DT k₁ k₂ t₂ J₁ J₂ r c p c₁ hp z a reply (dist (adr a))
        (no_touch_middle g raw a Nt) (safe a hu)
    rcases u with ⟨i,k⟩
    by_cases A : i=e
    · exact atMark (L k) (by simp [A,adr,site,L])
    · by_cases Rr : i=rightNeighbor e
      · exact atMark (R k) (by simp [Rr,adr,site,R])
      · exact Nat.le_of_eq (by simp [post,pre,physicalDT,AllSizeS1Geometry.step,A,Rr])
  have nb := ownerBlocks_nodup b x e he o
  refine ⟨BStarClearanceOwnerDT.chart_weak pre post slots blocks ns nb sub out all,?_,chart_pays pre post slots blocks ns nb sub out all⟩
  rintro ⟨C,t,H,ho⟩
  have hc : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,H,rfl⟩
  exact chart_pays pre post slots blocks ns nb sub out all
    ⟨footprint e C,memBlock C hc ho,(one C (.reverse t) H ho).2 t rfl⟩


theorem owner_DT_sum {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (he : e≠rightNeighbor e) (o : Int) (slots : List (Pos n))
    (reply : Bool) (dist : Pos n → Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let z := (x e,x (rightNeighbor e))
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long z
    let adr := BStarResetMarkAdapter.address e
    let pre := physicalDT x reply dist
    let post := physicalDT (AllSizeS1Geometry.step b x e) reply dist
    let blocks := ownerBlocks b x e o
    slots.Nodup → blocks.flatten ⊆ slots →
    (∀ a, adr a∈slots → physicalOwner (oldH6 b x) e cmdDispl a=o) →
    (∀ a, adr a∈slots → BStarResetQuietTable.DoorSafe g raw a) →
    (∀ C q, (C,.advance q)∈actualOffers g raw →
        physicalOwner (oldH6 b x) e cmdDispl C.source≠o) →
    (∀ C t, (C,.reverse t)∈actualOffers g raw →
      physicalOwner (oldH6 b x) e cmdDispl C.source=o →
      reply=true ∧ ∃ a, C.destination=some a ∧ dist (adr a)=dist (adr C.source)+1) →
    total post slots≤total pre slots ∧
      ((∃ C t, (C,.reverse t)∈actualOffers g raw ∧
        physicalOwner (oldH6 b x) e cmdDispl C.source=o) →
        total post slots<total pre slots) := by
  dsimp only
  intro ns sub owns safe noF rev
  have H := owner_DT_sum_paying hp x e he o slots reply dist ns sub owns safe noF rev
  exact ⟨H.1,H.2.1⟩

open BStarLongCommandData BStarLongDoor BStarResetQuietTable
open BStarAcquireLiteralChain BStarResetChartTouch BStarClearanceOffset
open BStarResetMarkAdapter BStarLongFixedRouting BStarClearanceIndexedSum
open BStarClearanceIndexedWait BStarClearanceReplyService BStarClearanceCommandSum

private def proper (c : CommandClaim) : Offer → Prop
  | .door _ => c.kind=.door
  | .advance _ => c.kind≠.door
  | .reverse _ => c.destination.isSome=true
  | _ => True

private theorem proper_actual (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (a : Offer) (h : (C,a)∈actualOffers g raw) : proper C a := by
  change (C,a)∈(round g raw).offered.map _ at h
  obtain ⟨o,ho,oe⟩ := List.mem_map.mp h
  change o∈(gated g raw).map _ at ho
  obtain ⟨v,hv,ve⟩ := List.mem_map.mp ho
  change proper (C,a).1 (C,a).2
  rw [←oe,←ve]
  obtain ⟨c,t⟩ := v
  have K := (BStarLongLiteral.gated_mem g raw c t).mp hv
  let M := fun a : AtK => bound g (readK raw) a
  have A : proper c (BStarLongLiteral.classifyOld g raw c) := by
    change proper c (classify c (geometry g c.source.side) (M c.source)
      ((c.destination.map M).getD .empty))
    unfold classify
    split
    · rename_i H
      exact beq_iff_eq.mp H
    · rename_i H
      have N : c.kind≠.door := fun E => H (beq_iff_eq.mpr E)
      split
      · split <;> first | exact True.intro | exact N
      · split
        · split <;> exact True.intro
        · split
          · rename_i q Q
            cases E : c.destination <;> simp [E,proper] at Q ⊢
          · split <;> exact True.intro
  have Z := K.2
  change t=checkOffer g (BStarLongPrep.view raw) (c,BStarLongLiteral.classifyOld g raw c) at Z
  have T : proper c t := by
    rw [Z]
    generalize BStarLongLiteral.classifyOld g raw c=w at A ⊢
    cases w <;> try exact A
    change proper c (match checkFence g (BStarLongPrep.view raw) c.source _ with
      | .advance => .advance _ | .hold => .hold | .fault => .advance failedPayload)
    split <;> first | exact A | exact True.intro
  let F := (round g raw).faults
  have Cancel (w : Offer) (W : proper c w) :
      proper (cancel F (c,w)).1 (cancel F (c,w)).2 := by
    cases w <;> try exact W
    by_cases E : c.source∈F <;> simpa only [cancel,E,if_true,if_false,proper] using W
  have Grant (w : CmdOffer) (W : proper w.1 w.2) :
      proper (BStarLongGrant.update g raw (round g raw).offered w).1
        (BStarLongGrant.update g raw (round g raw).offered w).2 := by
    obtain ⟨k,j⟩ := w
    unfold BStarLongGrant.update
    dsimp only
    split
    · cases j <;> try exact W
      rename_i pay
      by_cases A : ((geometry g k.source.side).axes.h6 && pay.fault == 0 && pay.opcode.toNat == acquire)=true <;> simpa only [A,Bool.false_eq_true,if_true,if_false,proper] using W
    · exact W
  exact Grant _ (Cancel t T)

private theorem door_safe_wait (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (hv : LongDoorGuard.valid manifest raw.2=true)
    (hw : (ctrlPhase.read raw.2).toNat=2)
    (hf : bound g (readK raw) (R 0)=.trail ∨
      ∃ pay, bound g (readK raw) (R 0)=.forward pay) : DoorSafe g raw (R 0) := by
  refine ⟨fun _ _ => hv,?_⟩
  intro _ c t ht _
  obtain ⟨rfl,rfl⟩ := BStarK0Frame.door_eq g raw c t ht
  change oldDoor raw.2 (bound g (readK raw) (R 0))=.hold
  rcases hf with T|⟨q,F⟩
  · rw [T]
    exact wait_holds_trail raw.2 hv hw
  · rw [F]
    exact wait_holds_forward raw.2 q hv hw

private theorem door_safe_off_header (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (H : g.2.axes.h6=false) : DoorSafe g raw (R 0) := by
  refine ⟨fun _ E => by rw [H] at E; contradiction,?_⟩
  intro _ C k hc _
  have hC : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,hc,rfl⟩
  have E := (BStarK0Frame.door_eq g raw C k hc).1
  have Q := (BStarResetChartIndex.selected_door g C hC (E ▸ rfl)).2.1
  rw [H] at Q
  contradiction


variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n

set_option maxRecDepth 4096 in
theorem indexed_DT_paying {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (e : Fin n) (he : e≠rightNeighbor e)
    (wait : BeforeOwnService hp x (endpoint (oldH6 B base) hh o 0).1 e) :
    let y := AllSizeS1Geometry.step B x e
    total (physicalRank B base y (distance S)) S=total (physicalRank B base x (distance S)) S →
    total (physicalDT y true (replyDistance S)) S≤total (physicalDT x true (replyDistance S)) S ∧
      ((∃ C t, (C,.reverse t)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) ∧
        physicalOwner (oldH6 B base) e cmdDispl C.source=o.val) →
        total (physicalDT y true (replyDistance S)) S<total (physicalDT x true (replyDistance S)) S) ∧
      (total (physicalDT y true (replyDistance S)) S=total (physicalDT x true (replyDistance S)) S →
       total (physicalDT y false (fun _ => 1)) S≤total (physicalDT x false (fun _ => 1)) S ∧
       ((∃ C, (C,.clear)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) ∧
          address e C.source∈S ∧
          total (physicalDT y false (fun _ => 1)) (footprint e C)<
            total (physicalDT x false (fun _ => 1)) (footprint e C)) →
        total (physicalDT y false (fun _ => 1)) S<total (physicalDT x false (fun _ => 1)) S)) := by
  dsimp only
  intro ftie
  let g := oldPair B x e
  let adr := address e
  let y := AllSizeS1Geometry.step B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let old := oldH6 B base
  let root := endpoint old hh o 0
  have hs : oldH6 B x=oldH6 B base := funext (fun i => (congrArg Prod.fst (same i)).symm)
  have Base (H : g.2.axes.h6=true) : old (rightNeighbor e)=true :=
    (congrArg Prod.fst (same (rightNeighbor e))).trans H
  have atRoot (H : g.2.axes.h6=true)
      (O : physicalOwner old e cmdDispl (R 0)=o.val) : rightNeighbor e=root.1 :=
    congrArg Prod.fst ((endpoint_spec old hh o 0).2.2 _ (Base H) O)
  have safe (a : AtK) (ha : address e a∈S) : DoorSafe g raw a := by
    by_cases Z : a=R 0
    · subst a
      cases H : g.2.axes.h6
      · exact door_safe_off_header g raw H
      · have own : physicalOwner old e cmdDispl (R 0)=o.val := (chart.entries _ ha).2
        obtain ⟨v,w,f⟩ := wait (atRoot H own)
        exact door_safe_wait g raw v w f
    · exact safe_nonright g raw a Z
  obtain ⟨part,owns,_⟩ := chart_owner_hypotheses hp chart same e
  have noF (C q) (H : (C,.advance q)∈actualOffers g raw)
      (own : physicalOwner (oldH6 B x) e cmdDispl C.source=o.val) : False := by
    rw [hs] at own
    have L := (pre_service_sum hp chart same cb cx e he wait).2 ⟨C,q,H,own⟩
    rw [ftie] at L
    exact Nat.lt_irrefl _ L
  have rev (C t) (H : (C,.reverse t)∈actualOffers g raw)
      (own : physicalOwner (oldH6 B x) e cmdDispl C.source=o.val) :
      true=true ∧ ∃ a,C.destination=some a ∧
        replyDistance S (adr a)=replyDistance S (adr C.source)+1 := by
    have hc : C∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨_,H,rfl⟩
    have P := proper_actual g raw C (.reverse t) H
    cases E : C.destination with
    | none => simp [proper,E] at P
    | some a =>
      refine ⟨rfl,a,rfl,?_⟩
      have F : Edge B x (adr C.source) (adr a) := ⟨e,C,a,hc,E,rfl,rfl⟩
      have M : adr C.source∈S := part (by
        apply List.mem_flatten.mpr
        refine ⟨footprint e C,?_,List.mem_map.mpr ⟨_,by simp [Claim.slots],rfl⟩⟩
        exact List.mem_map.mpr ⟨C,List.mem_filter.mpr ⟨hc,beq_iff_eq.mpr own⟩,rfl⟩)
      obtain ⟨j,hj,U,V⟩ := chart.edge _ _ M ((edge_fixed B base x same _ _).mpr F)
      unfold replyDistance
      rw [←U,←V,distance_idx chart.nodup,distance_idx chart.nodup]
      omega
  have D := owner_DT_sum hp x e he o.val S true (replyDistance S)
    chart.nodup part owns safe noF rev
  refine ⟨D.1,?_,?_⟩
  · rintro ⟨C,t,H,O⟩
    exact D.2 ⟨C,t,H,hs.symm ▸ O⟩
  intro tie
  have T := owner_DT_sum_paying hp x e he o.val S false (fun _ => 1) chart.nodup part owns safe noF
    (fun C t H O => False.elim (by
      have E := D.2 ⟨C,t,H,O⟩
      rw [tie] at E
      exact Nat.lt_irrefl _ E))
  refine ⟨T.1,?_⟩
  rintro ⟨C,H,U,K⟩
  have hc : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,H,rfl⟩
  exact T.2.2 ⟨footprint e C,
    List.mem_map.mpr ⟨C,List.mem_filter.mpr ⟨hc,beq_iff_eq.mpr (owns _ U)⟩,rfl⟩,K⟩


set_option maxRecDepth 4096 in
theorem indexed_DT {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (e : Fin n) (he : e≠rightNeighbor e)
    (wait : BeforeOwnService hp x (endpoint (oldH6 B base) hh o 0).1 e) :
    let y := AllSizeS1Geometry.step B x e
    total (physicalRank B base y (distance S)) S=total (physicalRank B base x (distance S)) S →
    total (physicalDT y true (replyDistance S)) S≤total (physicalDT x true (replyDistance S)) S ∧
      (total (physicalDT y true (replyDistance S)) S=total (physicalDT x true (replyDistance S)) S →
       total (physicalDT y false (fun _ => 1)) S≤total (physicalDT x false (fun _ => 1)) S) := by
  dsimp only
  intro F
  have H := indexed_DT_paying hp chart same cb cx e he wait F
  exact ⟨H.1,fun D => (H.2.2 D).1⟩

private theorem terminal_dest_none (g : Pair LongGeometry) (C : CommandClaim)
    (hc : C∈orderedCommands g) (ht : C.kind=.terminal) : C.destination=none := by
  have H := BStarLongFenceTopology.selected_command_raw g C hc
  obtain ⟨x,y⟩ := g
  have E : ∀ c∈commandClaims (x,y), c.kind=.terminal → c.destination=none := by
    unfold commandClaims ends
    simp only
    generalize x.inside=ix
    generalize x.last=lx
    generalize y.axes.h6=hy
    generalize y.inside=iy
    cases ix <;> cases lx <;> cases hy <;> cases iy <;>
      simp [link] <;> grind
  exact E C H ht

/-- Converts the exact old-pair witness returned by nominate_trail into
the strict actual indexed footprint premise. -/
theorem trail_footprint_payment (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (C : CommandClaim) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let y := Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))
    (C,.clear)∈actualOffers g raw →
    ((C.kind=.terminal ∧ trail (readK y C.source)+1=trail (readK raw C.source)) ∨
      ∃ a, C.destination=some a ∧
        (trail (readK y C.source)+trail (readK y a))+1=
          trail (readK raw C.source)+trail (readK raw a)) →
    total (physicalDT (AllSizeS1Geometry.step B x e) false (fun _=>1)) (footprint e C) <
      total (physicalDT x false (fun _=>1)) (footprint e C) := by
  dsimp only
  intro H P
  let g := oldPair B x e
  let y := Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let z := AllSizeS1Geometry.step B x e
  have ht : ∀ w : AtK, physicalDT z false (fun _=>1) (address e w)=trail (readK y w) := by
    rintro ⟨a,j⟩
    cases a <;> simp [physicalDT,z,site,AllSizeS1Geometry.step,
      Ne.symm he,readK,lane,y,Pair.map,small]
  have hr : ∀ w : AtK, physicalDT x false (fun _=>1) (address e w)=trail (readK raw w) := by
    rintro ⟨a,j⟩
    cases a <;> simp [physicalDT,site,readK,lane,raw,small]
  change total (physicalDT z false (fun _=>1)) (footprint e C) <
    total (physicalDT x false (fun _=>1)) (footprint e C)
  simp only [total,footprint,List.map_map,Function.comp_def,ht,hr]
  rcases P with ⟨K,T⟩|⟨a,E,T⟩
  · have hc : C∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨_,H,rfl⟩
    simp [Claim.slots,terminal_dest_none g C hc K]
    exact Nat.lt_of_succ_le (Nat.le_of_eq T)
  · simp [Claim.slots,E]
    exact Nat.lt_of_succ_le (Nat.le_of_eq T)

#print axioms indexed_DT_paying
#print axioms indexed_DT
#print axioms owner_DT_sum
end L4.BStarClearanceRingDT

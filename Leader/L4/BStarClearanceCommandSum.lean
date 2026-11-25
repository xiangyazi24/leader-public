import Leader.L4.BStarClearanceChartFootprint
import Leader.L4.BStarClearanceJoined
import Leader.L4.BStarClearanceNonforward
import Leader.L4.BStarClearanceAggregate

namespace L4.BStarClearanceCommandSum
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongTransport BStarLongEvents BStarLongCommand BStarLongRouting BStarResetQuiet
open BStarClearanceForward BStarClearanceJoined BStarClearanceNonforward
open BStarClearanceAggregate
open BStarLongCommandData

private theorem clear_dst_away (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (a : AtK) (hd : C.destination=some a)
    (HC : (C,.clear)∈actualOffers g raw) (no : C.source≠a) :
    avoids a (middle g raw) := by
  apply middle_avoids_of_chart
  intro o ho ha
  -- The actual offer list has only one offer per command claim.
  obtain ⟨l,r,Q⟩ := List.mem_iff_append.mp HC
  have P : (orderedCommands g).Pairwise (fun u v => ∀ s∈v.slots,s∉u.slots) :=
    select_pairwise Claim.slots [] (offers commandKey (commandClaims g))
  rw [←actualOffers_claims g raw,Q,List.map_append,List.map_cons] at P
  rw [Q] at ho
  have same : o=(C,.clear) := by
    rcases List.mem_append.mp ho with h|h
    · have M : o.1∈l.map Prod.fst := List.mem_map.mpr ⟨_,h,rfl⟩
      exact ((List.pairwise_append.mp P).2.2 _ M C List.mem_cons_self a
        (by simp [Claim.slots,hd]) ha).elim
    · rcases List.mem_cons.mp h with rfl|h
      · rfl
      · have M : o.1∈r.map Prod.fst := List.mem_map.mpr ⟨_,h,rfl⟩
        exact ((List.pairwise_cons.mp (List.pairwise_append.mp P).2.1).1 _ M a ha
          (by simp [Claim.slots,hd])).elim
  subst o
  intro w hw E
  simp [selected,direct] at hw
  cases hw
  exact no E

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

/-- On a real selected command footprint, the sum of rebound
forward ranks is nonincreasing. An actual advance (including a
faulted prep) makes it strictly decrease. Distances are positive
on terminal and decrement by exactly one along selected links.
The separately checked no-ISSUE source door contribution is explicit. -/
theorem block (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (act : Offer) (d : AtK → Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    let before := fun a => ranked g a (d a) (readRaw raw a)
    let after := fun a => ranked g a (d a) (readRaw y a)
    (C,act)∈actualOffers g raw →
    (∀ a∈C.slots, BStarResetQuietTable.DoorSafe g raw a) →
    (∀ a, C.destination=some a → d C.source=d a+1) →
    (C.destination=none → C.kind≠.door → 0<d C.source) →
    (C.kind=.door → after C.source≤before C.source) →
    total after C.slots≤total before C.slots ∧
      (∀ p, act=.advance p → total after C.slots<total before C.slots) := by
  dsimp only
  intro sel safe next pos door
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  let pre := fun a => ranked g a (d a) (readRaw raw a)
  let post := fun a => ranked g a (d a) (readRaw y a)
  have hc : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have sc : C.source∈C.slots := by simp [Claim.slots]
  have valid (a : AtK) (ha : a∈C.slots) := (safe a ha).valid
  have shape (a : AtK) (E : C.destination=some a) := BStarAcquireReturn.link_shape g C a hc E
  change total post C.slots≤total pre C.slots ∧ _
  cases act with
  | hold =>
    refine ⟨sum_mono _ _ _ (fun a h => ?_),by intro q E; contradiction⟩
    exact joined_idle_rank k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a (d a)
      (BStarResetQuietTable.hold_avoids _ _ _ sel _ h) (safe a h)
  | clear =>
    refine ⟨?_,by intro q E; contradiction⟩
    have A : post C.source=0 := joined_clear_rank _ _ _ _ _ _ _ _ _ hp x C (d C.source) sel (valid _ sc)
    cases D : C.destination with
    | none => simp [Claim.slots,D,total,A]
    | some a =>
      have ha : a∈C.slots := by simp [Claim.slots,D]
      have L : post a≤pre a := joined_idle_rank _ _ _ _ _ _ _ _ _ hp x a (d a)
        (clear_dst_away g raw C a D sel (Ne.symm (shape a D).1)) (safe a ha)
      simpa [Claim.slots,D,total,A] using Nat.add_le_add (Nat.zero_le (pre C.source)) L
  | reverse t =>
    refine ⟨?_,by intro q E; contradiction⟩
    cases D : C.destination with
    | none =>
      have H := proper_actual g raw C (.reverse t) sel
      simp [proper,D] at H
    | some a =>
      have ha : a∈C.slots := by simp [Claim.slots,D]
      have H := joined_reverse_rank _ _ _ _ _ _ _ _ _ hp x C a t (d C.source) (d a) D
        (Ne.symm (shape a D).1) sel (fun z eq => by rcases eq with rfl|rfl <;> exact valid _ (by assumption))
      change post C.source=0 ∧ post a=0 at H
      simp [Claim.slots,D,total,H.1,H.2]
  | door t =>
    refine ⟨?_,by intro q E; contradiction⟩
    have H := proper_actual g raw C (.door t) sel
    have D := (BStarResetChartIndex.selected_door g C hc H).2.2
    simpa [Claim.slots,D,total,pre,post] using door H
  | advance pay =>
    obtain ⟨old,front⟩ := BStarClearanceCommandFrame.advance_origin g raw C pay sel
    have strict : total post C.slots<total pre C.slots := by
      cases D : C.destination with
      | none =>
        have hk := BStarAcquireChainEndpoints.terminal g C hc D ?_
        · have H := turn_charge_joined _ _ _ _ _ _ _ _ _ hp x C pay old (d C.source)
            (pos D (by rw [hk.1]; decide)) hk.2.2.2 D sel front
          simpa [Claim.slots,D,total,pre,post] using H
        · exact proper_actual g raw C (.advance pay) sel
      | some a =>
        have H := move_charge_joined _ _ _ _ _ _ _ _ _ hp x C pay old a (d a) D sel front
        have P := next a D
        simpa [Claim.slots,D,total,pre,post,P] using H
    exact ⟨Nat.le_of_lt strict,fun _ _ => strict⟩

open BStarH6WordChart hiding total
open BStarLongFiberOwner BStarClearanceChartFootprint
open BStarAcquireVisitOrder

/-- The physical rebound rank uses the same fixed geometry snapshot
on both sides of a mark. The supplied distance is an owner chart
distance, not a per-command choice of weights. -/
def physicalRank {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
    (b : LargeRows (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (base x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (dist : Pos n → Nat) (u : Pos n) : Nat :=
  let g := longGeometry b (base u.1)
  let old := (x u.1).long
  ranked (g,g) (L u.2) (dist u) (readRaw (old,old) (L u.2))

/-- The actual physical forward sum on a fixed owner footprint
partition. The root's no-ISSUE row law and residual DoorSafe
witness are explicit; all selected old-pair cases are discharged. -/
theorem owner_sum {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (he : e≠rightNeighbor e) (o : Int) (slots : List (Pos n))
    (dist : Pos n → Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let z := (x e,x (rightNeighbor e))
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long z
    let adr := BStarResetMarkAdapter.address e
    let pre := physicalRank b x x dist
    let post := physicalRank b x (AllSizeS1Geometry.step b x e) dist
    let blocks := ownerBlocks b x e o
    slots.Nodup → blocks.flatten ⊆ slots →
    (∀ a, adr a∈slots → physicalOwner (oldH6 b x) e cmdDispl a=o) →
    (∀ a, adr a∈slots → BStarResetQuietTable.DoorSafe g raw a) →
    (∀ C∈orderedCommands g, physicalOwner (oldH6 b x) e cmdDispl C.source=o →
      (∀ a, C.destination=some a → dist (adr C.source)=dist (adr a)+1) ∧
      (C.destination=none → C.kind≠.door → 0<dist (adr C.source)) ∧
      (C.kind=.door → post (adr C.source)≤pre (adr C.source))) →
    total post slots≤total pre slots ∧
      ((∃ C q, (C,.advance q)∈actualOffers g raw ∧
        physicalOwner (oldH6 b x) e cmdDispl C.source=o) →
        total post slots<total pre slots) := by
  dsimp only
  intro ns sub owns safe rules
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let z := (x e,x (rightNeighbor e))
  let g := oldPair b x e
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long z
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b z)
  let adr := BStarResetMarkAdapter.address e
  let pre := physicalRank b x x dist
  let post := physicalRank b x (AllSizeS1Geometry.step b x e) dist
  let blocks := ownerBlocks b x e o
  have pre_eq (a : AtK) : pre (adr a)=ranked g a (dist (adr a)) (readRaw raw a) := by
    rcases a with ⟨side,k⟩
    cases side <;> rfl
  have post_eq (a : AtK) : post (adr a)=ranked g a (dist (adr a)) (readRaw y a) := by
    rcases a with ⟨side,k⟩
    cases side
    · simp [post,adr,physicalRank,AllSizeS1Geometry.step,site]; rfl
    · simp [post,adr,physicalRank,AllSizeS1Geometry.step,site,Ne.symm he]; rfl
  have memBlock (C : CommandClaim) (hc : C∈orderedCommands g)
      (ho : physicalOwner (oldH6 b x) e cmdDispl C.source=o) : footprint e C∈blocks := by
    exact List.mem_map.mpr ⟨C,List.mem_filter.mpr ⟨hc,beq_iff_eq.mpr ho⟩,rfl⟩
  have one (C : CommandClaim) (act : Offer) (H : (C,act)∈actualOffers g raw)
      (ho : physicalOwner (oldH6 b x) e cmdDispl C.source=o) :
      total post (footprint e C)≤total pre (footprint e C) ∧
        ∀ q, act=.advance q → total post (footprint e C)<total pre (footprint e C) := by
    have hc : C∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨_,H,rfl⟩
    have M : ∀ a∈C.slots, adr a∈slots := by
      intro a ha
      exact sub (List.mem_flatten.mpr ⟨_,memBlock C hc ho,List.mem_map.mpr ⟨a,ha,rfl⟩⟩)
    obtain ⟨N,P,D⟩ := rules C hc ho
    have T := block k₁ k₂ t₂ J₁ J₂ r c p c₁ hp z C act (fun a => dist (adr a)) H
      (fun a ha => safe a (M a ha)) N P (fun hk => by
        change ranked g C.source (dist (adr C.source)) (readRaw y C.source) ≤
          ranked g C.source (dist (adr C.source)) (readRaw raw C.source)
        rw [←post_eq,←pre_eq]
        exact D hk)
    let r₁ := fun a : AtK => ranked g a (dist (adr a)) (readRaw raw a)
    let r₂ := fun a : AtK => ranked g a (dist (adr a)) (readRaw y a)
    change total r₂ C.slots≤total r₁ C.slots ∧
      (∀ q, act=.advance q → total r₂ C.slots<total r₁ C.slots) at T
    rw [show r₂=post ∘ adr from funext (fun a => (post_eq a).symm),
        show r₁=pre ∘ adr from funext (fun a => (pre_eq a).symm)] at T
    simpa only [total,footprint,List.map_map] using T
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
      exact joined_idle_rank k₁ k₂ t₂ J₁ J₂ r c p c₁ hp z a (dist (adr a))
        (no_touch_middle g raw a Nt) (safe a hu)
    rcases u with ⟨i,k⟩
    by_cases A : i=e
    · exact atMark (L k) (by simp [A,adr,site,L])
    · by_cases Rr : i=rightNeighbor e
      · exact atMark (R k) (by simp [Rr,adr,site,R])
      · exact Nat.le_of_eq (by simp [post,pre,physicalRank,AllSizeS1Geometry.step,A,Rr])
  have nb := ownerBlocks_nodup b x e he o
  have PP := chart_partition slots blocks ns nb sub
  refine ⟨?_,?_⟩
  · rw [perm_total post PP,perm_total pre PP,total_append,total_append]
    exact Nat.add_le_add (block_total_le _ _ _ all) (sum_mono _ _ _ out)
  · rintro ⟨C,q,H,ho⟩
    have hc : C∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨_,H,rfl⟩
    exact chart_pays pre post slots blocks ns nb sub out all
      ⟨footprint e C,memBlock C hc ho,(one C (.advance q) H ho).2 q rfl⟩

#print axioms block
#print axioms owner_sum
end L4.BStarClearanceCommandSum

import Leader.L4.BStarClearanceRaceMark

namespace L4.BStarClearanceRaceOwner
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongTransport BStarLongEvents BStarLongCommand BStarLongRouting BStarResetQuiet
open BStarClearanceForward BStarClearanceJoined BStarClearanceNonforward
open BStarClearanceAggregate
open BStarLongCommandData
open BStarH6WordChart hiding total
open BStarLongFiberOwner BStarClearanceChartFootprint
open BStarAcquireVisitOrder BStarClearanceCommandSum

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

private theorem sum_lt {A : Type} (x y : A → Nat) (l : List A) (a : A)
    (ha : a∈l) (H : y a<x a) (le : ∀ u∈l, y u≤x u) :
    total y l<total x l := by
  induction l with
  | nil => contradiction
  | cons u l ih =>
    rcases List.mem_cons.mp ha with rfl|mem
    · exact Nat.add_lt_add_of_lt_of_le H (sum_mono x y l (fun v h => le v (List.mem_cons_of_mem _ h)))
    · exact Nat.add_lt_add_of_le_of_lt (le u List.mem_cons_self)
        (ih mem (fun v h => le v (List.mem_cons_of_mem _ h)))

theorem owner_pointwise_pays {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
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
    (∃ u∈slots, post u<pre u) → total post slots<total pre slots := by
  dsimp only
  intro ns sub owns safe rules witness
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
    have T := BStarClearanceCommandSum.block k₁ k₂ t₂ J₁ J₂ r c p c₁ hp z C act (fun a => dist (adr a)) H
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
  obtain ⟨u,hu,D⟩ := witness
  by_cases W : u∈blocks.flatten
  · obtain ⟨Q,hQ,uq⟩ := List.mem_flatten.mp W
    obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hQ
    obtain ⟨hc,ho⟩ := List.mem_filter.mp hC
    change C∈orderedCommands g at hc
    have hC' := hc
    rw [←actualOffers_claims g raw] at hC'
    obtain ⟨⟨C',act⟩,M,eq⟩ := List.mem_map.mp hC'
    change C'=C at eq
    subst C'
    apply chart_pays pre post slots blocks ns nb sub out all
    refine ⟨_,memBlock C hc (beq_iff_eq.mp ho),?_⟩
    cases act
    case advance q => exact (one C (.advance q) M (beq_iff_eq.mp ho)).2 q rfl
    all_goals
      apply sum_lt pre post _ _ uq D
      intro t ht
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
      have ss := safe a (sub (List.mem_flatten.mpr ⟨_,memBlock C hc (beq_iff_eq.mp ho),ht⟩))
      rw [pre_eq,post_eq]
    case hold =>
      exact joined_idle_rank _ _ _ _ _ _ _ _ _ hp z a _ (BStarResetQuietTable.hold_avoids _ _ _ M _ ha) ss
    case clear =>
        by_cases eq : a=C.source
        · subst a
          have Z : ranked g C.source (dist (adr C.source)) (readRaw y C.source)=0 := joined_clear_rank _ _ _ _ _ _ _ _ _ hp z C _ M ss.valid
          rw [Z]
          exact Nat.zero_le _
        · cases hd : C.destination with
          | none => exact (eq (by simpa [Claim.slots,hd] using ha)).elim
          | some v =>
            have E : a=v := (show a=C.source ∨ a=v by simpa [Claim.slots,hd] using ha).resolve_left eq
            subst a
            exact joined_idle_rank _ _ _ _ _ _ _ _ _ hp z v _
              (clear_dst_away _ _ C v hd M (Ne.symm eq)) ss
    case reverse =>
        cases hd : C.destination with
        | none =>
          have old := proper_actual g raw C _ M
          simp [proper,hd] at old
        | some v =>
          have hv : v∈C.slots := by simp [Claim.slots,hd]
          have hs : C.source∈C.slots := by simp [Claim.slots]
          have valid (u : AtK) (h : u=C.source ∨ u=v) := (safe u (sub (List.mem_flatten.mpr
            ⟨_,memBlock C hc (beq_iff_eq.mp ho),List.mem_map.mpr ⟨u,h.elim (· ▸ hs) (· ▸ hv),rfl⟩⟩))).valid
          have R := joined_reverse_rank _ _ _ _ _ _ _ _ _ hp z C v _ (dist (adr C.source))
            (dist (adr v)) hd (Ne.symm (BStarAcquireReturn.link_shape g C v hc hd).1) M valid
          change ranked g C.source (dist (adr C.source)) (readRaw y C.source)=0 ∧
            ranked g v (dist (adr v)) (readRaw y v)=0 at R
          have E : a=C.source ∨ a=v := by simpa [Claim.slots,hd] using ha
          rcases E with rfl|rfl
          · rw [R.1]; exact Nat.zero_le _
          · rw [R.2]; exact Nat.zero_le _
    case door =>
        have hk := proper_actual g raw C _ M
        have hd := (BStarResetChartIndex.selected_door g C hc hk).2.2
        have eq : a=C.source := by simpa [Claim.slots,hd] using ha
        subst a
        rw [←pre_eq,←post_eq]
        exact (rules _ hc (beq_iff_eq.mp ho)).2.2 hk
  · rw [perm_total post PP,perm_total pre PP,total_append,total_append]
    apply Nat.add_lt_add_of_le_of_lt (block_total_le _ _ _ all)
    exact sum_lt pre post _ u (List.mem_filter.mpr ⟨hu,by simpa using W⟩) D out

#print axioms owner_pointwise_pays

/-- On the literal nominated race incidence the full owner F sum
strictly decreases. The hypotheses are exactly the usual owner partition,
fixed distance, door frame, and settled-offset facts. -/
theorem race_owner_sum
    {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (i : Fin n) (j : Fin 11) (u : Payload) (slots : List (Pos n)) (dist : Pos n → Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let G := longGeometry b (x i)
    let o := owner (BStarH6WordChart.total (oldH6 b x)) (word (oldH6 b x) i) (cmdDispl j)
    (∀ z,oldH6 b x z=h z) → BStarClearanceOffset.correct h hh 5 x →
    BStarLongCommand.bind G j (atSite (x i).long j)=.forward u →
    u.fault=0 →
    (j.val==1 && ((u.opcode.toNat==admit && min 5 (BStarH6Ordinal.ordinal h hh i)==2) ||
      (u.opcode.toNat==bitOp && min 5 (BStarH6Ordinal.ordinal h hh i)==4)))=true →
    (u.race.toNat=1 ∨ u.race.toNat=2 ∨ u.race.toNat=3) →
    (∀ e : Fin n,e≠rightNeighbor e) →
    (i,j)∈slots → slots.Nodup →
    (∀ e, (ownerBlocks b x e o).flatten ⊆ slots) →
    (∀ e a, BStarResetMarkAdapter.address e a∈slots → physicalOwner (oldH6 b x) e cmdDispl a=o) →
    (∀ e a, BStarResetMarkAdapter.address e a∈slots →
      BStarResetQuietTable.DoorSafe (oldPair b x e)
        (Pair.map LargeSite.long (x e,x (rightNeighbor e))) a) →
    (∀ e C, C∈orderedCommands (oldPair b x e) →
      physicalOwner (oldH6 b x) e cmdDispl C.source=o →
      let adr := BStarResetMarkAdapter.address e
      (∀ a, C.destination=some a → dist (adr C.source)=dist (adr a)+1) ∧
      (C.destination=none → C.kind≠.door → 0<dist (adr C.source)) ∧
      (C.kind=.door → physicalRank b x (AllSizeS1Geometry.step b x e) dist (adr C.source)≤
        physicalRank b x x dist (adr C.source))) →
    ∃ s, (u.race.toNat=2 → s=.left) ∧ (u.race.toNat=3 → s=.right) ∧
      let e := BStarClearanceRaceMark.incident i s
      total (physicalRank b x (AllSizeS1Geometry.step b x e) dist) slots <
        total (physicalRank b x x dist) slots := by
  dsimp only
  intro same correct old fault gate race sep hs nd sub own safe rules
  obtain ⟨s,L,R,V⟩ :=
    BStarClearanceRaceMark.physical_race hp x h hh i j u dist same correct old fault gate race sep
  refine ⟨s,L,R,?_⟩
  let e := BStarClearanceRaceMark.incident i s
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let o := owner (BStarH6WordChart.total (oldH6 b x)) (word (oldH6 b x) i) (cmdDispl j)
  rcases V with W|⟨C,q,A,E⟩
  · exact owner_pointwise_pays hp x e (sep e) o slots dist nd (sub e) (own e) (safe e) (rules e)
      ⟨(i,j),hs,W⟩
  · have P : physicalOwner (oldH6 b x) e cmdDispl ⟨s,j⟩=o := by
      unfold physicalOwner o
      rw [BStarClearanceRaceMark.incident_site]
    exact (owner_sum hp x e (sep e) o slots dist nd (sub e) (own e) (safe e) (rules e)).2
      ⟨C,q,A,E.trans P⟩

#print axioms race_owner_sum
end L4.BStarClearanceRaceOwner

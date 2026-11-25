import Leader.L4.BStarAcquireHop
import Leader.L4.BStarLongRouting
import Leader.L4.BStarLongEvents
import Leader.L4.BStarLongLiteral

namespace L4.BStarAcquireLandingHop
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongWork BStarLongRouting BStarLongEvents

private theorem advance_slot (g : Pair LongGeometry) (c : CommandClaim) (p : Payload)
    (w : KWrite) (h : w∈advanceK g c p) : w.1∈c.slots := by
  cases H : c.destination with
  | none => simpa [advanceK,H,Claim.slots] using congrArg Prod.fst (List.mem_singleton.mp (show w∈[(c.source,finish p)] from by simpa [advanceK,H] using h))
  | some d =>
    simp only [advanceK,H,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> simp [Claim.slots,H]

private theorem direct_slot (c : CommandClaim) (a : Offer) (w : KWrite)
    (h : w∈direct c a) : w.1∈c.slots := by
  cases a with
  | clear =>
    simp [direct] at h
    subst w
    simp [Claim.slots]
  | reverse t =>
    cases E : c.destination with
    | none => simp [direct,E] at h
    | some d =>
      simp only [direct,E,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl <;> simp [Claim.slots,E]
  | _ => simp [direct] at h

theorem selected_slot (g : Pair LongGeometry) (x : Pair (BitVec LW)) (o : CmdOffer)
    (w : KWrite) (h : w∈(selected g x o).k) : w.1∈o.1.slots := by
  rcases o with ⟨c,a⟩
  cases a with
  | door t =>
    unfold selected at h
    dsimp only at h
    split at h <;> cases h
  | advance p =>
    change w∈advanceK g c _ at h
    exact advance_slot g c _ w h
  | hold => exact direct_slot c .hold w h
  | reverse t => exact direct_slot c (.reverse t) w h
  | clear => exact direct_slot c .clear w h

private theorem selected_fold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : List CmdOffer) (z : Selected) :
    (O.foldl (fun acc o => Selected.append acc (selected g x o)) z).k=
      z.k++O.flatMap (fun o => (selected g x o).k) := by
  induction O generalizing z with
  | nil => simp
  | cons o O ih =>
    simp only [List.foldl_cons,List.flatMap_cons,ih]
    exact List.append_assoc _ _ _

private theorem fold_away (l : List KWrite) (a : AtK) (k : BitVec 52)
    (h : ∀ w∈l, w.1≠a) : l.foldl (fun k t => putRaw k a t) k=k := by
  induction l generalizing k with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons,ih _ (fun w hw => h w (List.mem_cons_of_mem _ hw))]
    simp [putRaw,Ne.symm (h x List.mem_cons_self)]

private theorem no_observation (g : Pair LongGeometry) (old : ReadK) (l : List KWrite)
    (a : AtK) (h : ∃ t, (a,t)∈l) :
    ∀ w∈observations g old l, w.1≠a := by
  rintro ⟨b,t⟩ hw he
  change b=a at he
  subst b
  obtain ⟨q,hq⟩ := h
  exact no_observe_written g old l a t ⟨(a,q),hq,rfl⟩ hw

/-- Both endpoints of an arbiter-selected forward hop are installed
after normalization; neither can be overwritten by the old observer. -/
theorem full_hop {p : Payload} (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK)
    (hp : p.opcode.toNat=acquire)
    (hact : (c,.advance p)∈actualOffers g x)
    (hd : c.destination=some a)
    (k : AtK) (v : Token)
    (hw : (k=c.source ∧ v=.trail ∧ c.source≠a) ∨ (k=a ∧ v=.forward p)) :
    readK (patchPair (longWork g x) x) k=v := by
  let O := actualOffers g x
  let T := fun o : CmdOffer => (selected g x o).k
  let start := normalization g (readK x)
  let ks := start++O.flatMap T
  have HH : T (c,.advance p)=[(c.source,.trail),(a,.forward p)] :=
    BStarAcquireHop.selected_hop g x c a p hd hp
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp hact
  change O=l++(c,.advance p)::r at E
  have occ : k∈c.slots := by
    rcases hw with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp [Claim.slots,hd]
  have R : (orderedCommands g).Pairwise (fun a b => ∀ s∈b.slots,s∉a.slots) :=
    select_pairwise Claim.slots [] (offers commandKey (commandClaims g))
  have D := actualOffers_claims g x
  change O.map Prod.fst=orderedCommands g at D
  rw [←D,E,List.map_append,List.map_cons] at R
  have away (w : KWrite) (hm : w∈r.flatMap T) : w.1≠k := by
    obtain ⟨o,ho,hW⟩ := List.mem_flatMap.mp hm
    have hrel := (List.pairwise_cons.mp (List.pairwise_append.mp R).2.1).1
    have hS := selected_slot g x o w hW
    have H := hrel o.1 (List.mem_map.mpr ⟨o,ho,rfl⟩) w.1 hS
    exact fun he => H (he ▸ occ)
  have hit : (k,v)∈ks := by
    apply List.mem_append_right
    rw [E]
    apply List.mem_flatMap.mpr
    exact ⟨(c,.advance p),List.mem_append_right _ (List.mem_cons_self),by
      rw [HH]
      rcases hw with ⟨rfl,rfl,_⟩|⟨rfl,rfl⟩ <;> simp⟩
  let d := BStarLongCommandData.round g x
  let auth := BStarLongGrant.run g x d.offered
  let sr := O.foldl (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let preWrites := start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
    auth.writes.map Write.patch ++ d.writes.map Write.patch ++ sr.work
  have hs : sr.k=O.flatMap T := selected_fold g x O ⟨[],[],[]⟩
  have ex : (longTrace g x).assignments=
      preWrites++((O.flatMap T)++observations g (readK x) ks).map lowerOne := by
    change preWrites++(sr.k++observations g (readK x) (start++sr.k)).map lowerOne=_
    rw [hs]
  rw [long_exec,ex,List.foldl_append]
  change decode (readRaw (((O.flatMap T ++ observations g (readK x) ks).map lowerOne).foldl
    runWrite (preWrites.foldl runWrite x)) k)=_
  rw [fold_put,List.foldl_append,fold_away _ _ _ (no_observation g (readK x) ks k ⟨_,hit⟩)]
  have K (q : BitVec 52) :
      (O.flatMap T).foldl (fun old t => putRaw old k t) q=encode v := by
    rw [E,List.flatMap_append,List.flatMap_cons,HH]
    simp only [List.foldl_append]
    rw [fold_away _ _ _ away]
    rcases hw with ⟨rfl,rfl,hne⟩|⟨rfl,rfl⟩
    · simp [putRaw,hne]
    · simp [putRaw]
  rw [K,decode_encode]

/-- Exact full literal landing at any selected destination.
Normalization precedes the selected write; another command cannot
write this occurrence, and the old-token observer is suppressed. -/
theorem full_landing {p : Payload} (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK)
    (hp : p.opcode.toNat=acquire)
    (hact : (c,.advance p)∈actualOffers g x)
    (hd : c.destination=some a) :
    readK (patchPair (longWork g x) x) a=.forward p :=
  full_hop g x c a hp hact hd a (.forward p) (.inr ⟨rfl,rfl⟩)

open BStarLongCommandData BStarLongLiteral

private theorem same_source (g : Pair LongGeometry) (a b : CommandClaim)
    (ha : a∈orderedCommands g) (hb : b∈orderedCommands g) (he : a.source=b.source) : a=b := by
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp ha
  have P : (orderedCommands g).Pairwise (fun u v => ∀ s∈v.slots,s∉u.slots) :=
    select_pairwise Claim.slots [] (offers commandKey (commandClaims g))
  rw [E] at P hb
  have one : a.source∈a.slots := by simp [Claim.slots]
  have two : a.source∈b.slots := by simp [Claim.slots,he]
  rcases List.mem_append.mp hb with left|right
  · exact (P.rel_of_mem_append left List.mem_cons_self _ one two).elim
  · rcases List.mem_cons.mp right with hr|hr
    · exact hr.symm
    · exact (((List.pairwise_cons.mp (List.pairwise_append.mp P).2.1).1 b hr) _ two one).elim

private theorem prep_fault_origin (g : Pair LongGeometry) (x : Pair (BitVec LW)) (j : AtK)
    (h : j∈(round g x).faults) :
    ∃ c q, c.source=j ∧ (c,.advance q)∈gated g x ∧
      ∃ op, prepOf q.opcode.toNat=some op := by
  let L := preparedBy g x (gated g x)
  have hf : j∈BStarLongPrep.prepFaults (BStarLongPrep.view x) L := h
  unfold BStarLongPrep.prepFaults at hf
  have selected_mem (o : BStarLongPrep.Offer)
      (h : o∈(BStarLongPrep.arbitration L).1) : o∈L := by
    have H : o∈(offers BStarLongPrep.offerPriority L) := by
      unfold BStarLongPrep.arbitration at h
      rw [BStarLongPrep.arbitrate_winners] at h
      exact (select_sublist _ _ _).subset h
    have general (xs : List BStarLongPrep.Offer) (h : o∈offers BStarLongPrep.offerPriority xs) : o∈xs := by
      induction xs with
      | nil => exact h
      | cons b rest ih =>
        change o∈insert BStarLongPrep.offerPriority b (offers BStarLongPrep.offerPriority rest) at h
        rcases (mem_insert BStarLongPrep.offerPriority b o _).mp h with h|h
        · exact List.mem_cons.mpr (.inl h)
        · exact List.mem_cons_of_mem _ (ih h)
    exact general L H
  have loser_mem (o : BStarLongPrep.Offer) (h : o∈(BStarLongPrep.arbitration L).2) :
      o∈L := by
    have H := (BStarLongPrep.arbitrate_losers [] (offers BStarLongPrep.offerPriority L)).subset h
    have general (xs : List BStarLongPrep.Offer) (h : o∈offers BStarLongPrep.offerPriority xs) : o∈xs := by
      induction xs with
      | nil => exact h
      | cons b rest ih =>
        change o∈insert BStarLongPrep.offerPriority b (offers BStarLongPrep.offerPriority rest) at h
        rcases (mem_insert BStarLongPrep.offerPriority b o _).mp h with h|h
        · exact List.mem_cons.mpr (.inl h)
        · exact List.mem_cons_of_mem _ (ih h)
    exact general L H
  have witness : ∃ o∈L, o.claim.origin=j := by
    rcases List.mem_append.mp hf with H|H
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,loser_mem o ho,rfl⟩
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,selected_mem o (List.mem_filter.mp ho).1,rfl⟩
  obtain ⟨o,ho,he⟩ := witness
  unfold L preparedBy at ho
  obtain ⟨⟨c,s⟩,hc,hO⟩ := List.mem_flatMap.mp ho
  cases s <;> simp only at hO
  all_goals try cases hO
  rename_i q
  unfold fieldOffers at hO
  split at hO
  · cases hO
  · split at hO
    · cases hO
    · rename_i op hOp
      obtain ⟨cl,hcl,rfl⟩ := List.mem_map.mp hO
      obtain ⟨sh,hsh,rfl⟩ := List.mem_map.mp hcl
      exact ⟨c,q,he,hc,op,hOp⟩

/-- The literal FENCE/prep round cannot cancel a checked ACQUIRE
origin: ACQUIRE proposes no prep, and no other actual command shares
the origin. Arbitration therefore supplies this exact actual offer. -/
theorem checked_grant_offer (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload)
    (h : (c,.advance p)∈gated g x) (hp : p.opcode.toNat=acquire) :
    let O := (round g x).offered
    BStarLongGrant.update g x O (c,.advance p)∈actualOffers g x := by
  obtain ⟨hc,E⟩ := (gated_mem g x c (.advance p)).mp h
  have hf : c.source∉(round g x).faults := by
    intro hF
    obtain ⟨b,q,hb,hq,op,hop⟩ := prep_fault_origin g x c.source hF
    obtain ⟨hb',eq⟩ := (gated_mem g x b (.advance q)).mp hq
    have same := same_source g b c hb' hc hb
    subst b
    have qeq := Offer.advance.inj (eq.trans E.symm)
    subst q
    simp [hp,acquire,prepOf] at hop
  change BStarLongGrant.update g x (round g x).offered (c,.advance p)∈actualOffers g x
  unfold actualOffers BStarLongGrant.run
  dsimp only
  apply List.mem_map.mpr
  refine ⟨(c,.advance p),?_,rfl⟩
  change (c,.advance p)∈(gated g x).map (cancel (round g x).faults)
  exact List.mem_map.mpr ⟨(c,.advance p),h,by simp [cancel,hf]⟩

theorem checked_acquire_lands (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK) (p : Payload) (hd : c.destination=some a)
    (h : (c,.advance p)∈gated g x) (hp : BStarAcquireHop.Healthy p) :
    readK (patchPair (longWork g x) x) a=.forward
      (BStarAcquireHop.argUpdate g x (round g x).offered c p) := by
  have H := checked_grant_offer g x c p h hp.2.1
  dsimp only at H
  rw [BStarAcquireHop.grant_update_exact g x _ c p hp.1 hp.2.1] at H
  exact full_landing g x c a
    ((congrArg BitVec.toNat (BStarAcquireHop.argUpdate_fields g x _ c p).2.1).trans hp.2.1)
    H hd

/-- The actual old token is classified as an ACQUIRE advance before grant arbitration. -/
theorem gated_acquire_advance (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (hc : c∈orderedCommands g) (hnd : c.kind≠.door)
    (hread : readK x c.source=.forward p) (hp : BStarAcquireHop.Healthy p) :
    (c,.advance p)∈gated g x := by
  apply (gated_mem g x c (.advance p)).mpr
  refine ⟨hc,?_⟩
  symm
  unfold gatedAt classifyOld
  change BStarLongCommandData.checkOffer g (BStarLongPrep.view x)
    (c,classify c (geometry g c.source.side)
      (BStarLongCommand.bind (geometry g c.source.side) c.source.occurrence
        (readK x c.source)) _) = .advance p
  rw [hread,BStarAcquireHop.bind_exact _ _ p hp,
    BStarAcquireHop.classify_forward _ _ _ _ hnd hp.2.1]
  exact BStarAcquireHop.check_keeps _ _ _ _ hp.2.1

/-- One literal old-pair ACQUIRE hop, starting before classification.
No isolation, observation, cancellation or K0 caveats remain. -/
theorem raw_acquire_lands (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK) (p : Payload)
    (hc : c∈orderedCommands g) (hd : c.destination=some a)
    (hnd : c.kind≠.door) (hread : readK x c.source=.forward p)
    (hp : BStarAcquireHop.Healthy p) :
    readK (patchPair (longWork g x) x) a=.forward
      (BStarAcquireHop.argUpdate g x (round g x).offered c p) := by
  apply checked_acquire_lands g x c a p hd _ hp
  exact gated_acquire_advance g x c p hc hnd hread hp

theorem raw_acquire_departs (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK) (p : Payload)
    (hc : c∈orderedCommands g) (hd : c.destination=some a) (hne : c.source≠a)
    (hnd : c.kind≠.door) (hread : readK x c.source=.forward p)
    (hp : BStarAcquireHop.Healthy p) :
    readK (patchPair (longWork g x) x) c.source=.trail := by
  have H := checked_grant_offer g x c p (gated_acquire_advance g x c p hc hnd hread hp) hp.2.1
  dsimp only at H
  rw [BStarAcquireHop.grant_update_exact g x _ c p hp.1 hp.2.1] at H
  exact full_hop g x c a
    ((congrArg BitVec.toNat (BStarAcquireHop.argUpdate_fields g x _ c p).2.1).trans hp.2.1)
    H hd c.source .trail (.inl ⟨rfl,rfl,hne⟩)

end L4.BStarAcquireLandingHop

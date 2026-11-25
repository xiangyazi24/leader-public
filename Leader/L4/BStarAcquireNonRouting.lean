import Leader.L4.BStarAcquireMarkedSample

/-! Exclude normalization and observations when proving a forward
cursor frames across an incident mark. Actual incoming command writes
are deliberately separate. -/
namespace L4.BStarAcquireNonRouting
open AllSizeProtocol BStarTrace BStarLongToken BStarLongClaims BStarLongTransport
open BStarLongCommand BStarLongWork BStarLongRouting BStarAcquireHop
open BStarLongLayout BStarLongRoutingFrame BStarAcquireJoinedHop

theorem bound_old (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (p : Payload) (old : readK x a=.forward p) (healthy : Healthy p) :
    bound g (readK x) a=.forward p := by
  unfold bound
  rw [old,bind_exact _ _ _ healthy]

theorem observe_none (a : AtK) (g : LongGeometry) (p : Payload)
    (healthy : Healthy p) : observe a g p=none := by
  simp [observe,healthy.2.2.1]

theorem normalization_away (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (p : Payload) (old : readK x a=.forward p) (healthy : Healthy p)
    (retained : a∉discarded g) :
    ∀ w∈normalization g (readK x),w.1≠a := by
  have ha := bound_old g x a p old healthy
  rintro ⟨j,t⟩ hm hj
  change j=a at hj
  subst j
  rcases List.mem_append.mp hm with H|H
  · obtain ⟨j,_,E⟩ := List.mem_filterMap.mp H
    dsimp only at E
    split at E
    · have A : j=a := congrArg Prod.fst (Option.some.inj E)
      subst j
      simp_all [isFault,healthy.1]
    · cases E
  · obtain ⟨j,hs,E⟩ := List.mem_map.mp H
    have J : j=a := congrArg Prod.fst E
    subst j
    exact retained hs

theorem observations_away (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (p : Payload) (old : readK x a=.forward p) (healthy : Healthy p)
    (written : List KWrite) :
    ∀ w∈observations g (readK x) written,w.1≠a := by
  have ha := bound_old g x a p old healthy
  rintro ⟨j,t⟩ hm hj
  change j=a at hj
  subst j
  obtain ⟨j,_,E⟩ := List.mem_filterMap.mp hm
  split at E
  · cases E
  · split at E
    · rename_i q hq
      have J : j=a := by
        cases H : observe j (geometry g j.side) q <;> simp_all
      subst j
      rw [ha] at hq
      cases hq
      simp [observe_none _ _ _ healthy] at E
    · cases E

/-- The immediately preceding Trail and our old healthy F force a
literal hold. An arbitrary old predecessor F would not. -/
theorem incoming_trail_holds (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (a : AtK) (p : Payload)
    (hd : C.destination=some a) (hn : C.kind=.link)
    (hs : readK x C.source=.trail) (ha : readK x a=.forward p)
    (hp : Healthy p) :
    BStarLongLiteral.gatedAt g x C=.hold := by
  unfold BStarLongLiteral.gatedAt BStarLongLiteral.classifyOld
  change BStarLongCommandData.checkOffer g _ (C,classify C _ (bound g (readK x) C.source)
    ((C.destination.map (bound g (readK x))).getD .empty))=.hold
  rw [hd,Option.map_some,Option.getD_some,bound_old g x a p ha hp]
  have T : bound g (readK x) C.source=.trail := by simp [bound,hs,BStarLongCommand.bind]
  rw [T]
  simp [classify,hn,BStarLongCommandData.checkOffer]

/-- At a nonzero occurrence no upper patch or source door acts on K.
This lifts absence from actual routing intents to a full joined frame. -/
theorem joined_untouched_other (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (a : AtK) (nonzero : a.occurrence.val≠0) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (∀ w∈routing g raw,w.1≠a) →
    readK (Pair.map LargeSite.long (largePair b x)) a=readK raw a := by
  dsimp only
  intro away
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  change decode (readRaw (Pair.map LargeSite.long (largePair b x)) a)=decode (readRaw raw a)
  apply congrArg decode
  refine Eq.trans ?_ (untouched_raw g raw a nonzero away)
  obtain ⟨s,j⟩ := a
  cases s
  · change (kField j).read ((w.1.compose q.1).apply raw.1)=(kField j).read (w.1.apply raw.1)
    rw [Patch.compose_apply]
    exact field_kframe _ _ _ (scratch_kframe g raw false)
  · change (kField j).read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      (w.2.compose q.2)).apply raw.2)=(kField j).read (w.2.apply raw.2)
    have W : (kField j).read ((w.2.compose q.2).apply raw.2)=(kField j).read (w.2.apply raw.2) := by
      rw [Patch.compose_apply]
      exact field_kframe _ _ _ (scratch_kframe g raw true)
    cases H : g.2.axes.h6
    · rw [LongDoorGuard.no_authority]; exact W
    · cases V : LongDoorGuard.valid manifest raw.2
      · rw [LongDoorGuard.invalid_override _ _ _ V,Patch.compose_apply]
        exact (read_frame (raw.1,(w.2.compose q.2).apply raw.2) (R j) nonzero
          (true,LongDoorGuard.repair manifest) guard_frame).trans W
      · rw [LongDoorGuard.valid_no_override _ _ _ V]; exact W

/-- For a healthy, non-discarded F it suffices to exclude actual
selected command writes to prove that the entire raw routing list
frames its address. -/
theorem routing_away (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (a : AtK) (p : Payload) (old : readK x a=.forward p) (healthy : Healthy p)
    (retained : a∉discarded g)
    (cs : ∀ o∈BStarLongEvents.actualOffers g x, ∀ w∈(selected g x o).k,w.1≠a) :
    ∀ w∈routing g x,w.1≠a := by
  have loop (ls : List CmdOffer) (z : Selected)
      (hz : ∀ w∈z.k,w.1≠a)
      (hl : ∀ o∈ls, ∀ w∈(selected g x o).k,w.1≠a) :
      ∀ w∈(ls.foldl (fun acc o => Selected.append acc (selected g x o)) z).k,w.1≠a := by
    induction ls generalizing z with
    | nil => exact hz
    | cons o tl ih =>
      apply ih
      · intro w H
        rcases List.mem_append.mp H with P|P
        · exact hz w P
        · exact hl o List.mem_cons_self w P
      · exact fun o ho => hl o (List.mem_cons_of_mem _ ho)
  let ls := BStarLongEvents.actualOffers g x
  let sel := ls.foldl (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let prior := normalization g (readK x) ++ sel.k
  intro w H
  change w∈prior++observations g (readK x) prior at H
  rcases List.mem_append.mp H with hh|hh
  · rcases List.mem_append.mp hh with h|h
    · exact normalization_away g x a p old healthy retained w h
    · exact loop ls ⟨[],[],[]⟩ (by simp) cs w h
  · exact observations_away g x a p old healthy prior w hh

/-- HOLD survives both prep cancellation and grant arbitration. -/
theorem actual_hold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) (ho : o∈BStarLongEvents.actualOffers g x)
    (H : BStarLongLiteral.gatedAt g x o.1=.hold) :
    o.2=.hold := by
  change o∈(BStarLongCommandData.round g x).offered.map _ at ho
  obtain ⟨v,hv,ve⟩ := List.mem_map.mp ho
  change v∈(BStarLongCommandData.gated g x).map _ at hv
  obtain ⟨⟨C,t⟩,ht,te⟩ := List.mem_map.mp hv
  have E : v.1=C := by
    rw [←te]
    cases t <;> simp [BStarLongCommandData.cancel]
    split <;> rfl
  have F : o.1=C := (congrArg Prod.fst ve).symm.trans
    ((BStarLongEvents.update_claim g x _ v).trans E)
  have T := (BStarLongLiteral.gated_mem g x C t).mp ht
  have Q : t=.hold := T.2.trans (F ▸ H)
  subst t
  change (C,.hold)=v at te
  subst v
  simp [BStarLongGrant.update] at ve
  exact (congrArg Prod.snd ve).symm

/-- A door offer survives prep cancellation and grant arbitration. -/
theorem actual_door (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) (ho : o∈BStarLongEvents.actualOffers g x)
    (tok : Token) (H : BStarLongLiteral.gatedAt g x o.1=.door tok) :
    o.2=.door tok := by
  change o∈(BStarLongCommandData.round g x).offered.map _ at ho
  obtain ⟨v,hv,ve⟩ := List.mem_map.mp ho
  change v∈(BStarLongCommandData.gated g x).map _ at hv
  obtain ⟨⟨C,t⟩,ht,te⟩ := List.mem_map.mp hv
  have E : v.1=C := by
    rw [←te]
    cases t <;> simp [BStarLongCommandData.cancel]
    split <;> rfl
  have F : o.1=C := (congrArg Prod.fst ve).symm.trans
    ((BStarLongEvents.update_claim g x _ v).trans E)
  have T := (BStarLongLiteral.gated_mem g x C t).mp ht
  have Q : t=.door tok := T.2.trans (F ▸ H)
  subst t
  change (C,.door tok)=v at te
  subst v
  simp [BStarLongGrant.update] at ve
  exact (congrArg Prod.snd ve).symm

/-- This is the exact local incident-silence obligation: the mark
does not select the forward successor, and its selected predecessor
(if any) is the old Trail. The source door has no routing intents;
its separate WAIT write mask is handled by the K0 frame lemma. -/
theorem row_silent (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (p : Payload) (old : readK x a=.forward p) (healthy : Healthy p)
    (retained : a∉discarded g)
    (noSuccessor : ∀ C∈orderedCommands g,C.source=a → C.kind=.door)
    (predTrail : ∀ C∈orderedCommands g,C.destination=some a → readK x C.source=.trail) :
    ∀ w∈routing g x,w.1≠a := by
  apply routing_away g x a p old healthy retained
  rintro ⟨C,t⟩ ho w hw he
  have M : C∈orderedCommands g := by
    rw [← BStarLongEvents.actualOffers_claims g x]
    exact List.mem_map.mpr ⟨(C,t),ho,rfl⟩
  have Z : a∈C.slots := he ▸ BStarAcquireLandingHop.selected_slot g x (C,t) w hw
  have either : a=C.source ∨ C.destination=some a := by
    cases H : C.destination <;> simp_all [Claim.slots,eq_comm]
  rcases either with hs|hd
  · have door := noSuccessor C M hs.symm
    have H : BStarLongLiteral.gatedAt g x C=.door (bound g (readK x) a) := by
      unfold BStarLongLiteral.gatedAt BStarLongLiteral.classifyOld
      simp [door,classify,hs,BStarLongCommandData.checkOffer,bound,BStarLongTransport.readK,BStarLongCommandData.oldTokens]
    have Q := actual_door g x (C,t) ho _ H
    dsimp only at Q
    subst t
    unfold selected at hw
    dsimp only at hw
    split at hw <;> cases hw
  · have H := incoming_trail_holds g x C a p hd
      (BStarAcquireReturn.link_shape g C a M hd).2.1 (predTrail C M hd) old healthy
    have Q := actual_hold g x (C,t) ho H
    dsimp only at Q
    subst t
    cases hw

end L4.BStarAcquireNonRouting

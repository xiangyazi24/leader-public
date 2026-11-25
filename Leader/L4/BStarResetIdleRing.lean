import Leader.L4.BStarResetQuietTable
import Leader.L4.BStarResetTaggedRows
import Leader.L4.BStarAcquireForwardTrace

namespace L4.BStarResetIdleRing
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongCommand
open BStarLongWork BStarLongClaims BStarLongTransport BStarLongRouting
open BStarLongEvents BStarResetQuiet BStarLongDoor
open BStarResetTaggedRows BStarResetQuietTable

inductive ResetLive : Token → Prop where
  | f (p : Payload) (hp : ResetF p) : ResetLive (.forward p)
  | d (p : Payload) (hp : ResetF p) : ResetLive (finish p)

theorem live_bind (g : LongGeometry) (j : Fin 11) (t : Token) (h : ResetLive t) :
    BStarLongCommand.bind g j t=t := by
  cases h with
  | f p hp => exact bind_reset g j p hp
  | d p hp => exact (bind_finish g j p hp).1

private theorem reset_no_observe (g : LongGeometry) (a : AtK) (p : Payload)
    (h : ResetF p) : observe a g p=none := by
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [resetPayload,BStarLongCommandData.failedPayload,observe,gate,admit,bitOp]

private theorem live_observe (g : Pair LongGeometry) (old : ReadK) (a : AtK)
    (H : ResetLive (old a)) (pre : List KWrite) : avoids a (observations g old pre) := by
  intro w hw E
  rcases w with ⟨b,t⟩
  change b=a at E
  subst b
  obtain ⟨c,_,he⟩ := List.mem_filterMap.mp hw
  split at he
  · contradiction
  · split at he
    all_goals try contradiction
    rename_i p HP
    cases hv : observe c (geometry g c.side) p with
    | none => simp [hv] at he
    | some v =>
      rw [hv] at he
      have ee := congrArg Prod.fst (Option.some.inj he)
      change c=a at ee
      subst c
      have same : bound g old a=old a := live_bind _ _ _ H
      rw [same] at HP
      generalize old a=t at H HP
      cases H with
      | f q hq => injection HP with Hq; subst p; rw [reset_no_observe _ _ _ hq] at hv; contradiction
      | d q hq =>
        obtain ⟨D,HD⟩ := (bind_finish (geometry g a.side) a.occurrence q hq).2
        rw [HD] at HP
        contradiction

private theorem norm_target (g : Pair LongGeometry) (old : ReadK) (a : AtK)
    (hn : a∉discarded g) (t : Token) (hw : (a,t)∈normalization g old) :
      t=bound g old a := by
  simp only [normalization,List.mem_append] at hw
  rcases hw with hw|hw
  · obtain ⟨b,_,H⟩ := List.mem_filterMap.mp hw
    split at H
    · have hh := Option.some.inj H
      have he := congrArg Prod.fst hh
      change b=a at he
      subst b
      exact (congrArg Prod.snd hh).symm
    · contradiction
  · obtain ⟨b,hb,h⟩ := List.mem_map.mp hw
    have he := congrArg Prod.fst h
    change b=a at he
    subst b
    exact (hn hb).elim

private theorem fold_same (a : AtK) (k : BitVec 52) (ws : List KWrite)
    (h : ∀ w∈ws, w.1=a → encode w.2=k) :
    ws.foldl (fun acc w => putRaw acc a w) k=k := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons]
    have J : putRaw k a w=k := by
      by_cases e : a=w.1
      · simp [putRaw,e,h w List.mem_cons_self e.symm]
      · simp [putRaw,e]
    rw [J]
    exact ih (fun w hw => h w (List.mem_cons_of_mem _ hw))

private theorem live_routes (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (hl : ResetLive (readK x a)) (hc : readRaw x a=encode (readK x a))
    (hn : a∉discarded g) (hm : avoids a (middle g x)) :
    (routing g x).foldl (fun acc w => putRaw acc a w) (readRaw x a)=readRaw x a := by
  apply fold_same
  rw [routing_parts]
  rintro ⟨b,t⟩ hw h
  change b=a at h
  subst b
  rcases List.mem_append.mp hw with hh|hh
  · rcases List.mem_append.mp hh with hh|hh
    · rw [norm_target _ _ _ hn _ hh]
      exact (congrArg encode (live_bind _ _ _ hl)).trans hc.symm
    · exact (hm _ hh rfl).elim
  · exact (live_observe _ _ _ hl _ _ hh rfl).elim

theorem joined_live_idle (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    ResetLive (readK raw a) → readRaw raw a=encode (readK raw a) →
    a∉discarded g → avoids a (middle g raw) → DoorSafe g raw a →
    readRaw (Pair.map LargeSite.long (largePair b x)) a=readRaw raw a := by
  dsimp only
  intro hl hc hn hm hs
  rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a hs.valid]
  by_cases h : a.occurrence.val=0
  · obtain ⟨s,j⟩ := a
    have J : j=(0 : Fin 11) := Fin.ext h
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ s (hs.holds h)]
    exact live_routes _ _ _ hl hc hn hm
  · rw [raw_transit _ _ _ h]
    exact live_routes _ _ _ hl hc hn hm


private theorem fold_decode (a : AtK) (k : BitVec 52) (ws : List KWrite) (t : Token)
    (hk : decode k=t) (h : ∀ w∈ws, w.1=a → w.2=t) :
    decode (ws.foldl (fun acc w => putRaw acc a w) k)=t := by
  induction ws generalizing k with
  | nil => exact hk
  | cons w ws ih =>
    apply ih
    · by_cases e : a=w.1
      · simp [putRaw,e,h w List.mem_cons_self e.symm,decode_encode]
      · simp [putRaw,e,hk]
    · exact fun w hw => h w (List.mem_cons_of_mem _ hw)

private theorem live_route_decode (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (hl : ResetLive (readK x a)) (hn : a∉discarded g) (hm : avoids a (middle g x)) :
    decode ((routing g x).foldl (fun acc w => putRaw acc a w) (readRaw x a))=readK x a := by
  apply fold_decode _ _ _ _ rfl
  rw [routing_parts]
  rintro ⟨b,t⟩ hw h
  change b=a at h
  subst b
  rcases List.mem_append.mp hw with hh|hh
  · rcases List.mem_append.mp hh with hh|hh
    · exact (norm_target _ _ _ hn _ hh).trans (live_bind _ _ _ hl)
    · exact (hm _ hh rfl).elim
  · exact (live_observe _ _ _ hl _ _ hh rfl).elim

/-- On dirty raw spare bits a fault may be rewritten, but only to
its same canonical decoded token. -/
theorem joined_idle (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (quiet (readK raw a) ∨ ResetLive (readK raw a)) →
    a∉discarded g → avoids a (middle g raw) → DoorSafe g raw a →
    readK (Pair.map LargeSite.long (largePair b x)) a=readK raw a := by
  dsimp only
  intro state hn hm hs
  rcases state with hq|hl
  · exact congrArg decode (joined_quiet k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a hq hn hm hs.valid hs.holds)
  change decode (readRaw _ a)=_
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a hs.valid]
  by_cases h : a.occurrence.val=0
  · obtain ⟨s,j⟩ := a
    have J : j=(0 : Fin 11) := Fin.ext h
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ s (hs.holds h)]
    exact live_route_decode _ _ _ hl hn hm
  · rw [raw_transit _ _ _ h]
    exact live_route_decode _ _ _ hl hn hm

/-- A returning D at right K0 is excluded: stop or service it. -/
theorem safe_right_wait_forward (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (hv : LongDoorGuard.valid manifest raw.2=true)
    (hw : (ctrlPhase.read raw.2).toNat=2)
    (p : Payload) (ht : bound g (readK raw) (R 0)=.forward p) :
    DoorSafe g raw (R 0) := by
  refine ⟨fun _ _ => hv,?_⟩
  intro _ c k hc _
  obtain ⟨rfl,rfl⟩ := BStarK0Frame.door_eq g raw c k hc
  change BStarLongCommand.bind g.2 0 (atSite raw.2 0)=.forward p at ht
  change oldDoor raw.2 (BStarLongCommand.bind g.2 0 (atSite raw.2 0))=.hold
  simp [ht,oldDoor,hv,hw]

open BStarAcquireForwardTrace BStarH6WordChart BStarAcquireMarkedPath in
theorem idle_at {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁) (e : Fin n)
    (he : e≠rightNeighbor e) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    (quiet (readK raw a) ∨ ResetLive (readK raw a)) →
    a∉discarded g → avoids a (middle g raw) → DoorSafe g raw a →
    atCursor (AllSizeS1Geometry.step b x e) (site e a.side,a.occurrence)=
      atCursor x (site e a.side,a.occurrence) := by
  dsimp only
  intro h hn hm hs
  have R := joined_idle k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) a h hn hm hs
  obtain ⟨s,j⟩ := a
  cases s <;> simp [atCursor,site,AllSizeS1Geometry.step,readK,L,lane,Pair.map,Ne.symm he] at R ⊢ <;> exact R

open BStarAcquireForwardTrace BStarH6WordChart BStarAcquireMarkedPath in
theorem idle_off_pair {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁) (e : Fin n)
    (a : BStarAcquireVisitOrder.Pos n) (hl : a.1≠e) (hr : a.1≠rightNeighbor e) :
    atCursor (AllSizeS1Geometry.step (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x e) a=atCursor x a := by
  unfold atCursor
  rw [BStarAcquireRingFrame.unselected _ _ _ _ hl hr]


open BStarAcquireForwardTrace BStarH6WordChart in
theorem idle_link {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁) (e : Fin n)
    (he : e≠rightNeighbor e) (C : CommandClaim) (d a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    C∈orderedCommands g → C.kind=.link → C.destination=some d →
    LinkHold (bound g (readK raw) C.source) (bound g (readK raw) d) →
    (a=C.source ∨ a=d) → (quiet (readK raw a) ∨ ResetLive (readK raw a)) →
    a∉discarded g → DoorSafe g raw a →
    atCursor (AllSizeS1Geometry.step b x e) (site e a.side,a.occurrence)=
      atCursor x (site e a.side,a.occurrence) := by
  dsimp only
  intro hc hk hd H ha h hn hs
  have I := link_avoids _ _ _ _ hc hk hd H
  apply idle_at hp x e he a h hn _ hs
  rcases ha with rfl|rfl
  · exact I.1
  · exact I.2

open BStarAcquireForwardTrace BStarH6WordChart in
theorem idle_terminal {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁) (e : Fin n)
    (he : e≠rightNeighbor e) (C : CommandClaim) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    C∈orderedCommands g → C.kind=.terminal → TerminalHold (bound g (readK raw) C.source) →
    (quiet (readK raw C.source) ∨ ResetLive (readK raw C.source)) →
    C.source∉discarded g → DoorSafe g raw C.source →
    atCursor (AllSizeS1Geometry.step b x e) (site e C.source.side,C.source.occurrence)=
      atCursor x (site e C.source.side,C.source.occurrence) := by
  dsimp only
  intro hc hk H h hn hs
  exact idle_at hp x e he C.source h hn (terminal_avoids _ _ _ hc hk H) hs

#print axioms joined_live_idle
#print axioms joined_idle
#print axioms idle_at
#print axioms idle_link
#print axioms idle_terminal
end L4.BStarResetIdleRing

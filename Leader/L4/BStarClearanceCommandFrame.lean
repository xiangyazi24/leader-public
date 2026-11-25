import Leader.L4.BStarClearanceForward
import Leader.L4.BStarResetQuietTable

namespace L4.BStarClearanceCommandFrame
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongRouting BStarLongWork BStarLongEvents
open BStarLongCommandData BStarLongLiteral BStarResetQuiet BStarClearanceForward

def live : Token → Nat
  | .forward _ | .reply _ => 1
  | _ => 0

def trail : Token → Nat
  | .trail => 1
  | _ => 0

def forwardCount : Token → Nat
  | .forward _ => 1
  | _ => 0

def returnCount : Token → Nat
  | .reply _ => 1
  | _ => 0

theorem bind_counts (g : LongGeometry) (j : Fin 11) (t : Token) :
    (forwardCount (BStarLongCommand.bind g j t),returnCount (BStarLongCommand.bind g j t),
      trail (BStarLongCommand.bind g j t))=(forwardCount t,returnCount t,trail t) := by
  cases t
  all_goals simp only [BStarLongCommand.bind]
  all_goals repeat' first | rfl | split

theorem bind_live (g : LongGeometry) (j : Fin 11) (t : Token) :
    live (BStarLongCommand.bind g j t)=live t := by
  cases t
  all_goals simp only [BStarLongCommand.bind]
  all_goals repeat' first | rfl | split

private def isAdvance : Offer → Bool
  | .advance _ => true
  | _ => false

private def reverseValue : Offer → Option Token
  | .reverse t => some t
  | _ => none

private theorem updates_kind (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (o : CmdOffer) :
    let out := BStarLongGrant.update g x os o
    out.1=o.1 ∧ isAdvance out.2=isAdvance o.2 ∧ reverseValue out.2=reverseValue o.2 := by
  rcases o with ⟨c,o⟩
  cases o <;> unfold BStarLongGrant.update <;> dsimp only
  all_goals split <;> first | exact ⟨rfl,rfl,rfl⟩ | (split <;> exact ⟨rfl,rfl,rfl⟩)

private theorem cancel_kind (fs : List AtK) (o : CmdOffer) :
    let out := cancel fs o
    out.1=o.1 ∧ isAdvance out.2=isAdvance o.2 ∧ reverseValue out.2=reverseValue o.2 := by
  rcases o with ⟨c,o⟩
  cases o <;> unfold cancel <;> dsimp only
  all_goals first | exact ⟨rfl,rfl,rfl⟩ | (split <;> exact ⟨rfl,rfl,rfl⟩)

private theorem checks_kind (g : Pair LongGeometry) (old : At Sheet → BStarLongPackets.Lane)
    (o : CmdOffer) :
    (isAdvance (checkOffer g old o)=true → isAdvance o.2=true) ∧
      reverseValue (checkOffer g old o)=reverseValue o.2 := by
  rcases o with ⟨c,o⟩
  cases o <;> unfold checkOffer <;> dsimp only
  all_goals first | exact ⟨id,rfl⟩ | (split <;> exact ⟨fun _ => rfl,rfl⟩)

private theorem raw_origins (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (o : Offer) (h : (c,o)∈actualOffers g x) :
    (isAdvance o=true → isAdvance (classifyOld g x c)=true) ∧
      reverseValue o=reverseValue (classifyOld g x c) := by
  unfold actualOffers BStarLongGrant.run round at h
  obtain ⟨a,ha,ea⟩ := List.mem_map.mp h
  obtain ⟨b,hb,eb⟩ := List.mem_map.mp ha
  have hu := updates_kind g x (round g x).offered a
  have hc := cancel_kind (BStarLongPrep.prepFaults (BStarLongPrep.view x) (preparedBy g x (gated g x))) b
  dsimp only at hu hc
  erw [ea] at hu
  erw [eb] at hc
  have cg : b.1=c := hc.1.symm.trans hu.1.symm
  have hg := (gated_mem g x b.1 b.2).mp hb
  have hf := checks_kind g (BStarLongPrep.view x) (b.1,classifyOld g x b.1)
  have hg' := hg.2
  change b.2=checkOffer g (BStarLongPrep.view x) (b.1,classifyOld g x b.1) at hg'
  constructor
  · intro A
    rw [←cg]
    exact hf.1 (hg' ▸ (hc.2.1 ▸ (hu.2.1 ▸ A)))
  · rw [hu.2.2,hc.2.2,hg',hf.2,cg]

theorem advance_origin (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (h : (c,.advance p)∈actualOffers g x) :
    ∃ q, bound g (readK x) c.source=.forward q := by
  have Q := (raw_origins g x c (.advance p) h).1 rfl
  unfold classifyOld at Q
  change isAdvance (classify c _ (bound g (readK x) c.source) _)=true at Q
  cases H : bound g (readK x) c.source with
  | forward q => exact ⟨q,rfl⟩
  | _ => rw [H] at Q; unfold classify at Q; split at Q <;> try contradiction
         repeat' first | contradiction | split at Q

theorem reverse_origin (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK) (t : Token) (hd : c.destination=some a)
    (h : (c,.reverse t)∈actualOffers g x) :
    bound g (readK x) a=t ∧ ∃ q, t=.reply q := by
  have Q := (raw_origins g x c (.reverse t) h).2
  change some t=reverseValue (classify c _ (bound g (readK x) c.source)
    ((c.destination.map (bound g (readK x))).getD .empty)) at Q
  simp only [hd,Option.map_some,Option.getD_some] at Q
  unfold classify at Q
  split at Q
  · contradiction
  split at Q
  · split at Q <;> contradiction
  · split at Q
    · split at Q <;> contradiction
    · split at Q
      · rename_i p H
        exact ⟨(Option.some.inj Q).symm, p, (Option.some.inj Q).trans H⟩
      · split at Q <;> contradiction

/-- A blocked FENCE produces an actual HOLD offer and no command work
or routing writes. Other disjoint selected commands may still execute. -/
theorem blocked_fence (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (hm : c∈orderedCommands g)
    (hf : classifyOld g x c=.advance p)
    (hb : checkFence g (BStarLongPrep.view x) c.source p=.hold) :
    (c,.hold)∈actualOffers g x ∧ (selected g x (c,.hold)).k=[] ∧
      (selected g x (c,.hold)).work=[] := by
  have G : (c,.hold)∈gated g x := (gated_mem g x c _).mpr ⟨hm,by
    unfold gatedAt; rw [hf]; exact (held_on_fence g _ c p hb).symm⟩
  refine ⟨?_,rfl,rfl⟩
  unfold actualOffers BStarLongGrant.run round
  simp only [List.mem_map]
  refine ⟨(c,.hold),⟨(c,.hold),G,rfl⟩,?_⟩
  unfold BStarLongGrant.update
  dsimp only
  split <;> rfl

private theorem live_arrive (g : LongGeometry) (j : Fin 11) (p : Payload) :
    live (arrive g j p)=1 := by unfold arrive; split <;> rfl

private theorem live_finish (p : Payload) : live (finish p)=1 := by
  unfold finish
  dsimp only
  split
  · rfl
  · split
    · split <;> rfl
    · split <;> rfl

theorem link_live (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (a : AtK) (hd : c.destination=some a)
    (ne : c.source≠a) (h : (c,.advance p)∈actualOffers g x) :
    let y := patchPair (longWork g x) x
    live (readK y c.source)+live (readK y a) ≤
      live (readK x c.source)+live (readK x a) := by
  dsimp only
  obtain ⟨u,v⟩ := move_lands g x c p a hd h ne
  obtain ⟨q,E⟩ := advance_origin g x c p h
  have src := (bind_live (geometry g c.source.side) c.source.occurrence (readK x c.source)).symm
  change live (readK x c.source)=live (bound g (readK x) c.source) at src
  change live (decode (readRaw _ c.source))+live (decode (readRaw _ a)) ≤ _
  rw [u,v,decode_encode,decode_encode,src,E,live_arrive]
  exact Nat.le_add_right 1 _

theorem terminal_live (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (hd : c.destination=none)
    (h : (c,.advance p)∈actualOffers g x) :
    live (readK (patchPair (longWork g x) x) c.source)=live (readK x c.source) := by
  obtain ⟨q,E⟩ := advance_origin g x c p h
  have src := (bind_live (geometry g c.source.side) c.source.occurrence (readK x c.source)).symm
  change live (readK x c.source)=live (bound g (readK x) c.source) at src
  change live (decode (readRaw _ c.source))=_
  rw [terminal_finish g x c p hd h,decode_encode,src,E,live_finish]
  rfl

theorem reverse_live (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK) (t : Token) (hd : c.destination=some a)
    (ne : c.source≠a) (h : (c,.reverse t)∈actualOffers g x) :
    let y := patchPair (longWork g x) x
    live (readK y c.source)+live (readK y a) ≤
      live (readK x c.source)+live (readK x a) := by
  dsimp only
  obtain ⟨u,v⟩ := reverse_endpoints g x c a t hd ne h
  obtain ⟨E,q,rfl⟩ := reverse_origin g x c a t hd h
  have dst := (bind_live (geometry g a.side) a.occurrence (readK x a)).symm
  change live (readK x a)=live (bound g (readK x) a) at dst
  change live (decode (readRaw _ c.source))+live (decode (readRaw _ a)) ≤ _
  rw [u,v,decode_encode,decode_encode,dst,E]
  exact Nat.le_add_left 1 _

/-- Trail count is a lower-order component: a selected forward hop
lands a forward and leaves one Trail; its two-output Trail count is
exactly one, including the initially Empty destination case. -/
theorem link_trail (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (a : AtK) (hd : c.destination=some a)
    (ne : c.source≠a) (h : (c,.advance p)∈actualOffers g x) :
    let y := patchPair (longWork g x) x
    trail (readK y c.source)+trail (readK y a)=1 := by
  dsimp only
  obtain ⟨u,v⟩ := move_lands g x c p a hd h ne
  change trail (decode (readRaw _ c.source))+trail (decode (readRaw _ a))=_
  rw [u,v,decode_encode,decode_encode]
  unfold arrive
  split <;> rfl

private theorem live_le_one (t : Token) : live t≤1 := by cases t <;> simp [live]

private theorem quiet_from_zero (t : Token) (h : live t=0) : quiet t := by
  cases t <;> simp [live] at h
  · exact .inl rfl
  · exact .inr rfl

private theorem quiet_norm_no_live (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (h : quiet (readK x a)) (w : KWrite) (hw : w∈normalization g (readK x)) (E : w.1=a) :
    live w.2=0 := by
  rcases w with ⟨b,t⟩
  change b=a at E
  subst b
  simp only [normalization,List.mem_append] at hw
  rcases hw with hw|hw
  · obtain ⟨b,_,he⟩ := List.mem_filterMap.mp hw
    split at he
    · rename_i F
      have E := congrArg Prod.fst (Option.some.inj he)
      change b=a at E
      subst b
      rw [quiet_bound g (readK x) a h] at F
      rcases h with h|h <;> simp [h,isFault] at F
    · contradiction
  · obtain ⟨b,_,he⟩ := List.mem_map.mp hw
    exact congrArg (fun t : KWrite => live t.2) he ▸ rfl

private theorem zero_fold (a : AtK) (ws : List KWrite) (k : BitVec 52)
    (hk : live (decode k)=0) (H : ∀ w∈ws, w.1=a → live w.2=0) :
    live (decode (ws.foldl (fun acc w => putRaw acc a w) k))=0 := by
  induction ws generalizing k with
  | nil => exact hk
  | cons w ws ih =>
    apply ih
    · by_cases e : a=w.1
      · simp [putRaw,e,decode_encode,H w List.mem_cons_self e.symm]
      · simp [putRaw,e,hk]
    · exact fun t ht => H t (List.mem_cons_of_mem _ ht)

private theorem route_no_live_increase (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (h : avoids a (middle g x)) :
    live (decode ((routing g x).foldl (fun acc w => putRaw acc a w) (readRaw x a))) ≤
      live (readK x a) := by
  by_cases Z : live (readK x a)=0
  · rw [Z]
    apply Nat.le_of_eq
    apply zero_fold _ _ _ Z
    intro w hw E
    rw [routing_parts] at hw
    rcases List.mem_append.mp hw with H|H
    · rcases List.mem_append.mp H with H|H
      · exact quiet_norm_no_live g x a (quiet_from_zero _ Z) w H E
      · exact (h w H E).elim
    · exact (quiet_observations g (readK x) a (quiet_from_zero _ Z) _ w H E).elim
  · have H := live_le_one (readK x a)
    exact Nat.le_trans (live_le_one _) (by omega)

/-- Full joined local idle frame for the live count, even for dirty
bits and discarded addresses. The caller checks K0 separately because
a real source issue can add one live token. -/
theorem joined_idle_live (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    avoids a (middle g raw) → BStarResetQuietTable.DoorSafe g raw a →
    live (readK (Pair.map LargeSite.long (largePair b x)) a) ≤ live (readK raw a) := by
  dsimp only
  intro h hs
  change live (decode (readRaw _ a))≤_
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a hs.valid]
  by_cases H : a.occurrence.val=0
  · obtain ⟨s,j⟩ := a
    have J : j=(0 : Fin 11) := Fin.ext H
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ s (hs.holds H)]
    exact route_no_live_increase _ _ _ h
  · rw [raw_transit _ _ _ H]
    exact route_no_live_increase _ _ _ h

/-- Transfer exact two-address live accounting to the full joined row
(including the outer guard) at both chart addresses. -/
theorem joined_link_live (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (C : CommandClaim) (a : AtK) (act : Offer) (hd : C.destination=some a)
    (ne : C.source≠a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    ((∃ p, act=.advance p) ∨ ∃ t, act=.reverse t) →
    (C,act)∈actualOffers g raw →
    (∀ q, (q=C.source ∨ q=a) → q=R 0 → g.2.axes.h6=true →
      LongDoorGuard.valid manifest raw.2=true) →
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    live (readK y C.source)+live (readK y a) ≤
      live (readK raw C.source)+live (readK raw a) := by
  dsimp only
  intro action h hv
  change live (decode (readRaw _ C.source))+live (decode (readRaw _ a)) ≤ _
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source (hv _ (.inl rfl)),
    joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a (hv _ (.inr rfl))]
  rcases action with ⟨p,rfl⟩|⟨t,rfl⟩
  · exact link_live _ _ C p a hd ne h
  · exact reverse_live _ _ C a t hd ne h

end L4.BStarClearanceCommandFrame

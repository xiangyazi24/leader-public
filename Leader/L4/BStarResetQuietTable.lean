import Leader.L4.BStarResetQuiet

/-! Literal no-middle-write rows for the separating-rail mark table.
The guards inspect immutable bound pair tokens; the byte frame applies
only to the Empty/Trail addresses, not to live/fault payloads. -/
namespace L4.BStarResetQuietTable
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongCommand
open BStarLongWork BStarLongClaims BStarLongTransport BStarLongRouting
open BStarLongEvents BStarResetQuiet BStarLongDoor

inductive LinkHold : Token → Token → Prop where
  | tt : LinkHold .trail .trail
  | ee : LinkHold .empty .empty
  | tf (p : Payload) : LinkHold .trail (.forward p)
  | de (p : Payload) : LinkHold (.reply p) .empty

inductive TerminalHold : Token → Prop where
  | d (p : Payload) : TerminalHold (.reply p)
  | e : TerminalHold .empty

theorem link_classifies_hold (c : CommandClaim) (g : LongGeometry)
    (s d : Token) (hk : c.kind=.link) (h : LinkHold s d) :
    classify c g s d=.hold := by
  cases h <;> simp [classify,hk] <;> rfl

theorem terminal_classifies_hold (c : CommandClaim) (g : LongGeometry)
    (s d : Token) (hk : c.kind=.terminal) (h : TerminalHold s) :
    classify c g s d=.hold := by
  cases h <;> simp [classify,hk] <;> rfl

private theorem retain_actual_hold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (hc : c∈orderedCommands g)
    (hv : classify c (geometry g c.source.side) (bound g (readK x) c.source)
        ((c.destination.map (bound g (readK x))).getD .empty)=.hold) :
    (c,.hold)∈actualOffers g x := by
  have C : (c,.hold)∈offersOn g (readK x) := List.mem_map.mpr
    ⟨c,hc,congrArg (Prod.mk c) hv⟩
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round BStarLongCommandData.gated
  simp only [List.mem_map]
  refine ⟨(c,.hold),⟨(c,.hold),⟨(c,.hold),C,rfl⟩,rfl⟩,?_⟩
  unfold BStarLongGrant.update
  dsimp only
  split <;> rfl

theorem actual_link_hold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (d : AtK) (hc : c∈orderedCommands g) (hk : c.kind=.link)
    (hd : c.destination=some d)
    (h : LinkHold (bound g (readK x) c.source) (bound g (readK x) d)) :
    (c,.hold)∈actualOffers g x := by
  apply retain_actual_hold g x c hc
  simpa [hd] using link_classifies_hold c (geometry g c.source.side) _ _ hk h

theorem actual_terminal_hold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (hc : c∈orderedCommands g) (hk : c.kind=.terminal)
    (h : TerminalHold (bound g (readK x) c.source)) :
    (c,.hold)∈actualOffers g x :=
  retain_actual_hold g x c hc (terminal_classifies_hold c _ _ _ hk h)

/-- The literal arbiter reserves both incidences for the selected hold
command; all earlier and later commands have disjoint claim footprints.
Thus even foreign live rows do not enter this address's middle write list. -/
theorem hold_avoids (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (hc : (c,.hold)∈actualOffers g x)
    (a : AtK) (ha : a∈c.slots) :
    avoids a (middle g x) := by
  let O := actualOffers g x
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp hc
  change O=l++(c,.hold)::r at E
  have R : (orderedCommands g).Pairwise (fun a b => ∀ s∈b.slots,s∉a.slots) :=
    select_pairwise Claim.slots [] (offers commandKey (commandClaims g))
  have D := actualOffers_claims g x
  change O.map Prod.fst=orderedCommands g at D
  rw [←D,E,List.map_append,List.map_cons] at R
  intro w hw H
  obtain ⟨o,ho,hW⟩ := List.mem_flatMap.mp hw
  change o∈O at ho
  rw [E] at ho
  have hS : a∈o.1.slots := H ▸ BStarAcquireLandingHop.selected_slot g x o w hW
  rcases List.mem_append.mp ho with hl|hr
  · have rel := (List.pairwise_append.mp R).2.2
    have hl' : o.1∈l.map Prod.fst := List.mem_map.mpr ⟨o,hl,rfl⟩
    exact rel _ hl' c List.mem_cons_self a ha hS
  · rcases List.mem_cons.mp hr with rfl|hr
    · simp [selected,direct] at hW
    · have rel := (List.pairwise_cons.mp (List.pairwise_append.mp R).2.1).1
      exact rel _ (List.mem_map.mpr ⟨o,hr,rfl⟩) a hS ha

theorem link_avoids (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (d : AtK) (hc : c∈orderedCommands g) (hk : c.kind=.link)
    (hd : c.destination=some d)
    (h : LinkHold (bound g (readK x) c.source) (bound g (readK x) d)) :
    avoids c.source (middle g x) ∧ avoids d (middle g x) := by
  have H := actual_link_hold g x c d hc hk hd h
  exact ⟨hold_avoids g x c H _ (by simp [Claim.slots]),
    hold_avoids g x c H _ (by simp [Claim.slots,hd])⟩

theorem terminal_avoids (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (hc : c∈orderedCommands g) (hk : c.kind=.terminal)
    (h : TerminalHold (bound g (readK x) c.source)) :
    avoids c.source (middle g x) :=
  hold_avoids g x c (actual_terminal_hold g x c hc hk h) _ (by simp [Claim.slots])


/-- K0 is special: the old-right source door and outer validity guard
are not part of the ordinary transport write list. -/
structure DoorSafe (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (a : AtK) : Prop where
  valid : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true
  holds : a.occurrence.val=0 → ∀ c k, (c,.door k)∈actualOffers g raw →
    c.source.side=a.side → oldDoor (BStarLongWork.atOld raw c.source) k=.hold

theorem safe_nonright (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (a : AtK)
    (h : a≠R 0) : DoorSafe g raw a := by
  refine ⟨fun he _ => (h he).elim,?_⟩
  intro hz c k hc hs
  have E := (BStarK0Frame.door_eq g raw c k hc).1
  have H : a.side=.right := by rw [E] at hs; exact hs.symm
  obtain ⟨s,j⟩ := a
  have ej : j=(0 : Fin 11) := Fin.ext hz
  change s=.right at H
  subst s
  subst j
  exact (h rfl).elim

theorem safe_right_wait_trail (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (hv : LongDoorGuard.valid manifest raw.2=true)
    (hw : (ctrlPhase.read raw.2).toNat=2)
    (ht : bound g (readK raw) (R 0)=.trail) :
    DoorSafe g raw (R 0) := by
  refine ⟨fun _ _ => hv,?_⟩
  intro _ c k hc _
  obtain ⟨rfl,rfl⟩ := BStarK0Frame.door_eq g raw c k hc
  change BStarLongCommand.bind g.2 0 (atSite raw.2 0)=.trail at ht
  change oldDoor raw.2 (BStarLongCommand.bind g.2 0 (atSite raw.2 0))=.hold
  simp [ht,oldDoor,hv,hw]

/-- The tracked address may be either end of a TT, EE, TF, or DE row,
but it must itself be E or T. In particular, TF preserves the predecessor
T byte even for a canonical fault F; normalization may still change F. -/
theorem joined_link_quiet (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (C : CommandClaim) (d a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.kind=.link → C.destination=some d →
    LinkHold (bound g (readK raw) C.source) (bound g (readK raw) d) →
    (a=C.source ∨ a=d) → quiet (readK raw a) → a∉discarded g → DoorSafe g raw a →
    readRaw (Pair.map LargeSite.long (largePair b x)) a=readRaw raw a := by
  dsimp only
  intro hc hk hd h ha hq hD hs
  have H := link_avoids _ _ _ _ hc hk hd h
  apply joined_quiet k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a hq hD _ hs.valid hs.holds
  rcases ha with rfl|rfl
  · exact H.1
  · exact H.2

theorem joined_terminal_empty (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (C : CommandClaim) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.kind=.terminal → readK raw C.source=.empty →
    C.source∉discarded g → DoorSafe g raw C.source →
    readRaw (Pair.map LargeSite.long (largePair b x)) C.source=readRaw raw C.source := by
  dsimp only
  intro hc hk h hD hs
  apply joined_quiet k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source (.inl h) hD _ hs.valid hs.holds
  exact terminal_avoids _ _ _ hc hk (by rw [quiet_bound _ _ _ (.inl h),h]; exact .e)

#print axioms link_avoids
#print axioms terminal_avoids
#print axioms joined_link_quiet
#print axioms joined_terminal_empty
end L4.BStarResetQuietTable

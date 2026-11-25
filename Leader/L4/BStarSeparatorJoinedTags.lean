import Leader.L4.BStarSeparatorTags
import Leader.L4.BStarSeparatorControl
import Leader.L4.BStarClearanceForward

/-! Actual joined old-pair tag effects for the generic parked separator.
Normalization and observations are accounted for when a held F
preserves its tag, rather than incorrectly claiming the byte is held. -/
namespace L4.BStarSeparatorJoinedTags
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongCommand BStarLongTransport BStarLongRouting BStarLongEvents
open BStarResetQuiet BStarResetQuietTable BStarSeparatorControl BStarSeparatorTags

private theorem raw_forward_of_bound (g : Pair LongGeometry) (old : ReadK) (a : AtK)
    (h : anyTag.F (bound g old a)) : anyTag.F (old a) := by
  rcases h with ⟨p,H⟩
  unfold bound at H
  cases A : old a with
  | forward q => exact ⟨q,rfl⟩
  | empty => rw [A] at H; cases H
  | trail => rw [A] at H; cases H
  | reply q =>
    rw [A] at H
    simp only [BStarLongCommand.bind] at H
    split at H
    · cases H
    · split at H <;> cases H

private theorem fold_forward (a : AtK) (ws : List KWrite) (x : BitVec 52)
    (H : anyTag.F (decode x))
    (W : ∀ w∈ws, w.1=a → anyTag.F w.2) :
    anyTag.F (decode (ws.foldl (fun k t => putRaw k a t) x)) := by
  induction ws generalizing x with
  | nil => exact H
  | cons w ws ih =>
    apply ih
    · by_cases eq : a=w.1
      · simpa [putRaw,eq,decode_encode] using W w List.mem_cons_self eq.symm
      · simpa [putRaw,eq] using H
    · exact fun u hm => W u (List.mem_cons_of_mem _ hm)

private theorem parked_routing (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (c : CommandClaim) (hold : (c,.hold)∈actualOffers g raw)
    (notDiscarded : c.source∉discarded g)
    (old : anyTag.F (bound g (readK raw) c.source)) :
    anyTag.F (decode ((routing g raw).foldl
      (fun k t => putRaw k c.source t) (readRaw raw c.source))) := by
  let a := c.source
  have M := hold_avoids g raw c hold a (by simp [a,Claim.slots])
  apply fold_forward
  · exact raw_forward_of_bound g _ a old
  intro w hw wa
  rw [routing_parts] at hw
  rcases List.mem_append.mp hw with pre|obs
  · rcases List.mem_append.mp pre with norm|mid
    · unfold normalization at norm
      rcases List.mem_append.mp norm with nm|nm
      · obtain ⟨z,_,E⟩ := List.mem_filterMap.mp nm
        change (if isFault (bound g (readK raw) z) then some (z,bound g (readK raw) z)
          else none)=some w at E
        split at E
        · have H := Option.some.inj E; subst w
          change z=a at wa
          subst z
          exact old
        · contradiction
      · obtain ⟨z,hz,E⟩ := List.mem_map.mp nm
        subst w
        exact (notDiscarded (wa ▸ hz)).elim
    · exact (M w mid wa).elim
  · obtain ⟨z,_,E⟩ := List.mem_filterMap.mp obs
    split at E
    · contradiction
    · split at E
      · rename_i p _
        cases EQ : observe z (geometry g z.side) p <;>
          simp only [EQ,Option.map_some,Option.map_none] at E
        · contradiction
        · have Q := Option.some.inj E; subst w; exact ⟨_,rfl⟩
      · contradiction

/-- A held selected F preserves F class through the joined row,
even when canonicalization or race observation changes its bytes. -/
theorem parked_joined (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁))) (c : CommandClaim) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (c,.hold)∈actualOffers g raw → c.source∉discarded g →
    DoorSafe g raw c.source → anyTag.F (bound g (readK raw) c.source) →
    anyTag.F (readK (Pair.map LargeSite.long (largePair b x)) c.source) := by
  dsimp only
  intro hold active safe old
  change anyTag.F (decode (readRaw _ c.source))
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r n p c₁ hp x c.source safe.valid]
  have P := parked_routing _ _ c hold active old
  by_cases hz : c.source.occurrence.val=0
  · generalize c.source=s at *
    rcases s with ⟨side,j⟩
    have E : j=(0:Fin 11) := Fin.ext hz
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ side (safe.holds hz)]
    exact P
  · rw [raw_transit _ _ _ hz]
    exact P

#print axioms parked_joined

private theorem link_safety (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK) (hm : c∈orderedCommands g) (hd : c.destination=some a) :
    c.source≠a ∧ DoorSafe g raw c.source ∧
      (a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) := by
  obtain ⟨ne,_,S⟩ := BStarAcquireReturn.link_shape g c a hm hd
  refine ⟨Ne.symm ne, safe_nonright _ _ _ ?_,?_⟩
  · intro E
    rw [E] at S
    exact S rfl rfl
  · intro E H
    have h0 : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have N := (BStarAcquireJoinedHop.k0_dest g c a hm hd h0).2
    rw [H] at N
    contradiction

private theorem arrived_F (g : LongGeometry) (j : Fin 11) (p : Payload) :
    anyTag.F (arrive g j p) := by
  unfold arrive
  split <;> exact ⟨_,rfl⟩

private theorem finished_D (p : Payload) : anyTag.D (finish p) := by
  unfold finish
  dsimp only
  split
  · exact ⟨_,rfl⟩
  · split
    · split <;> exact ⟨_,rfl⟩
    · split <;> exact ⟨_,rfl⟩

/-- Actual FX law on the selected link. The surviving branch permits
old race/FENCE hold; otherwise source becomes T and destination F. -/
theorem forward_link_joined (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (c : CommandClaim) (a : AtK) (hd : c.destination=some a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c∈orderedCommands g → c.source∉discarded g →
    anyTag.F (readK raw c.source) →
    anyTag.F (readK y c.source) ∨ (readK y c.source=.trail ∧ anyTag.F (readK y a)) := by
  dsimp only
  intro hm active old
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  obtain ⟨ne,S,T⟩ := link_safety g raw c a hm hd
  have oldB : anyTag.F (bound g (readK raw) c.source) := by
    obtain ⟨v,H⟩ := old
    unfold bound
    rw [H]
    exact bound_F _ _ _
  obtain ⟨v,H⟩ := oldB
  have lnk := (BStarAcquireReturn.link_shape g c a hm hd).2.1
  rcases forward_mark g raw c v hm (by simp [lnk]) H with hold|⟨pay,move⟩
  · exact .inl (parked_joined _ _ _ _ _ _ _ _ _ hp x c hold active S ⟨v,H⟩)
  · right
    obtain ⟨L,Rr⟩ := BStarClearanceForward.move_lands g raw c pay a hd move ne
    change decode (readRaw _ c.source)=.trail ∧ anyTag.F (decode (readRaw _ a))
    erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x c.source S.valid,
      joined_work_raw _ _ _ _ _ _ _ _ _ hp x a T]
    rw [L,Rr,decode_encode,decode_encode]
    exact ⟨rfl,arrived_F _ _ _⟩

/-- Actual K10 terminal law for all old forward bytes. A terminal
whose selected command parks remains F, not a spurious D. -/
theorem forward_terminal_joined (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (c : CommandClaim) (kind : c.kind=.terminal) (hd : c.destination=none)
    (h10 : c.source.occurrence.val=10) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c∈orderedCommands g → c.source∉discarded g → anyTag.F (readK raw c.source) →
    anyTag.F (readK y c.source) ∨ anyTag.D (readK y c.source) := by
  dsimp only
  intro hm active old
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have safe : DoorSafe g raw c.source := safe_nonright _ _ _ (by
    intro E; rw [E] at h10; contradiction)
  have oldB : anyTag.F (bound g (readK raw) c.source) := by
    obtain ⟨v,H⟩ := old
    unfold bound
    rw [H]
    exact bound_F _ _ _
  obtain ⟨v,H⟩ := oldB
  rcases forward_mark g raw c v hm (by simp [kind]) H with hold|⟨q,move⟩
  · exact .inl (parked_joined _ _ _ _ _ _ _ _ _ hp x c hold active safe ⟨v,H⟩)
  · right
    change anyTag.D (decode (readRaw _ c.source))
    erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x c.source safe.valid]
    rw [terminal_finish g raw c q hd move,decode_encode]
    exact finished_D _

/-- Actual TD law: old Trail takes any old D, including an inherited
malformed D (bound as a canonical fault), and its prior slot clears. -/
theorem trail_reply_joined (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (c : CommandClaim) (a : AtK) (hd : c.destination=some a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c∈orderedCommands g → readK raw c.source=.trail → anyTag.D (readK raw a) →
    anyTag.D (readK y c.source) ∧ readK y a=.empty := by
  dsimp only
  intro hm oldS oldD
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  obtain ⟨_,S,T⟩ := link_safety g raw c a hm hd
  have qS : quiet (bound g (readK raw) c.source) := by
    unfold bound
    rw [oldS]
    exact .inr rfl
  have qD : anyTag.D (bound g (readK raw) a) := by
    obtain ⟨v,H⟩ := oldD
    unfold bound
    rw [H]
    exact bound_D _ _ _
  obtain ⟨q,H⟩ := qD
  obtain ⟨L,Rr⟩ := reply_lands g raw c a q hm hd qS H
  change anyTag.D (decode (readRaw _ c.source)) ∧ decode (readRaw _ a)=.empty
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x c.source S.valid,
    joined_work_raw _ _ _ _ _ _ _ _ _ hp x a T]
  exact ⟨⟨q,L⟩,Rr⟩

#print axioms forward_link_joined
#print axioms forward_terminal_joined
#print axioms trail_reply_joined
end L4.BStarSeparatorJoinedTags

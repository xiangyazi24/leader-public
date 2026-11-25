import Leader.L4.BStarClearanceReturnCharge
import Leader.L4.BStarClearanceAggregate

namespace L4.BStarClearanceDTBlock
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongCommand BStarLongTransport BStarLongRouting BStarResetQuiet
open BStarLongEvents BStarClearanceCommandFrame BStarResetQuietTable
open BStarClearanceAggregate

def small (reply : Bool) (t : Token) : Nat :=
  if reply then returnCount t else trail t

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

private theorem small_bind (reply : Bool) (g : LongGeometry) (j : Fin 11) (t : Token) :
    small reply (BStarLongCommand.bind g j t)=small reply t := by
  have H := bind_counts g j t
  cases reply
  · exact congrArg (fun x : Nat × Nat × Nat => x.2.2) H
  · exact congrArg (fun x : Nat × Nat × Nat => x.2.1) H

private theorem small_empty (r : Bool) : small r .empty=0 := by cases r <;> rfl
private theorem small_forward (r : Bool) (p : Payload) : small r (.forward p)=0 := by
  cases r <;> rfl

private theorem idle_routing (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (a : AtK)
    (r : Bool) (h : avoids a (middle g raw)) :
    small r (decode ((routing g raw).foldl (fun k t => putRaw k a t) (readRaw raw a))) ≤
      small r (readK raw a) := by
  have fold (xs : List KWrite) (z : BitVec 52)
      (K : small r (decode z)≤small r (readK raw a))
      (W : ∀ w∈xs, w.1=a → small r w.2≤small r (readK raw a)) :
      small r (decode (xs.foldl (fun k t => putRaw k a t) z))≤small r (readK raw a) := by
    induction xs generalizing z with
    | nil => exact K
    | cons w xs ih =>
      apply ih
      · by_cases E : a=w.1
        · simpa only [putRaw,if_pos E,decode_encode] using W w List.mem_cons_self E.symm
        · simpa only [putRaw,if_neg E] using K
      · exact fun t ht => W t (List.mem_cons_of_mem _ ht)
  apply fold _ _ (Nat.le_refl _)
  rw [routing_parts]
  rintro ⟨b,t⟩ hw E
  change b=a at E
  subst b
  rcases List.mem_append.mp hw with H|H
  · rcases List.mem_append.mp H with H|H
    · unfold normalization at H
      rcases List.mem_append.mp H with U|U
      · obtain ⟨j,_,J⟩ := List.mem_filterMap.mp U
        dsimp only at J
        split at J
        · obtain E := Option.some.inj J
          cases E
          rw [bound,small_bind]
          exact Nat.le_refl _
        · contradiction
      · obtain ⟨j,_,J⟩ := List.mem_map.mp U
        cases J
        change small r .empty≤_
        rw [small_empty]
        exact Nat.zero_le _
    · exact (h _ H rfl).elim
  · unfold observations at H
    obtain ⟨j,_,J⟩ := List.mem_filterMap.mp H
    split at J
    · contradiction
    · split at J
      · obtain ⟨q,_,Q⟩ := Option.map_eq_some_iff.mp J
        cases Q
        rw [small_forward]
        exact Nat.zero_le _
      · contradiction

theorem joined_idle_DT (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (a : AtK)
    (reply : Bool) (d : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    avoids a (middle g raw) → DoorSafe g raw a →
    d*small reply (readK y a)≤d*small reply (readK raw a) := by
  dsimp only
  intro h s
  apply Nat.mul_le_mul_left
  change small reply (decode (readRaw _ a))≤_
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a s.valid]
  by_cases H : a.occurrence.val=0
  · obtain ⟨s',j⟩ := a
    have J : j=(0 : Fin 11) := Fin.ext H
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ s' (s.holds H)]
    exact idle_routing _ _ _ _ h
  · rw [raw_transit _ _ _ H]
    exact idle_routing _ _ _ _ h

theorem joined_hold_block_DT (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (C : CommandClaim)
    (reply : Bool) (d : AtK → Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    (C,.hold)∈actualOffers g raw → (∀ a∈C.slots, DoorSafe g raw a) →
    total (fun a => d a*small reply (readK y a)) C.slots ≤
      total (fun a => d a*small reply (readK raw a)) C.slots := by
  dsimp only
  intro H Q
  exact sum_mono _ _ _ fun a ha =>
    joined_idle_DT k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a reply (d a)
      (hold_avoids _ _ _ H _ ha) (Q _ ha)

theorem joined_clear_block_DT (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (C : CommandClaim)
    (reply : Bool) (d : AtK → Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    (C,.clear)∈actualOffers g raw → (∀ a∈C.slots, DoorSafe g raw a) →
    (∀ a, C.destination=some a → C.source≠a) →
    total (fun a => d a*small reply (readK y a)) C.slots ≤
      total (fun a => d a*small reply (readK raw a)) C.slots := by
  dsimp only
  intro H S N
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  change total (fun a => d a*small reply (readK y a)) C.slots ≤ _
  have srcMem : C.source∈C.slots := by simp [Claim.slots]
  have Z : readK y C.source=.empty := by
    change decode (readRaw y C.source)=_
    erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x C.source (S _ srcMem).valid,
      selected_clear _ _ _ H]
    exact decode_encode _
  apply sum_mono
  intro a ha
  by_cases E : a=C.source
  · rw [E,Z,small_empty,Nat.mul_zero]
    exact Nat.zero_le _
  · have D : C.destination=some a := by
      cases J : C.destination <;> simp_all [Claim.slots,eq_comm]
    exact joined_idle_DT _ _ _ _ _ _ _ _ _ hp x a reply (d a)
      (clear_dst_away g raw C a D H (N _ D)) (S a ha)

private theorem owned_avoids (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (chosen : CmdOffer) (hc : chosen∈actualOffers g x)
    (a : AtK) (hm : a∈chosen.1.slots) (h : avoids a (selected g x chosen).k) :
    avoids a (middle g x) := by
  let O := actualOffers g x
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp hc
  change O=l++chosen::r at E
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
    exact rel _ (List.mem_map.mpr ⟨o,hl,rfl⟩) chosen.1 List.mem_cons_self a hm hS
  · rcases List.mem_cons.mp hr with rfl|hr
    · exact h w hW H
    · have rel := (List.pairwise_cons.mp (List.pairwise_append.mp R).2.1).1
      exact rel _ (List.mem_map.mpr ⟨o,hr,rfl⟩) a hS hm

theorem joined_door_block_DT (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (C : CommandClaim)
    (tok : Token) (reply : Bool) (d : AtK → Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    (C,.door tok)∈actualOffers g raw → (∀ a∈C.slots, DoorSafe g raw a) →
    total (fun a => d a*small reply (readK y a)) C.slots ≤
      total (fun a => d a*small reply (readK raw a)) C.slots := by
  dsimp only
  intro H S
  apply sum_mono
  intro a ha
  apply joined_idle_DT _ _ _ _ _ _ _ _ _ hp x a reply (d a) _ (S a ha)
  exact owned_avoids _ _ _ H a ha (by
    intro w hw
    simp only [selected] at hw
    split at hw <;> cases hw)

end L4.BStarClearanceDTBlock

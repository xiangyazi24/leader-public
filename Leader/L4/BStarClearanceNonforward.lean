import Leader.L4.BStarClearanceCommandFrame

namespace L4.BStarClearanceNonforward
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongCommand BStarLongTransport BStarLongRouting BStarResetQuiet
open BStarClearanceGate BStarClearanceForward BStarLongEvents BStarResetQuietTable

private theorem fold_rank (g : Pair LongGeometry) (a : AtK) (d : Nat)
    (xs : List KWrite) (raw : BitVec 52) (m : Nat) (hr : ranked g a d raw≤m)
    (h : ∀ w∈xs, w.1=a → ranked g a d (encode w.2)≤m) :
    ranked g a d (xs.foldl (fun k t => putRaw k a t) raw)≤m := by
  induction xs generalizing raw with
  | nil => exact hr
  | cons x xs ih =>
    apply ih
    · by_cases E : a=x.1
      · simpa only [putRaw,if_pos E] using h x List.mem_cons_self E.symm
      · simpa only [putRaw,if_neg E] using hr
    · exact fun t ht => h t (List.mem_cons_of_mem _ ht)

private theorem norm_rank (g : Pair LongGeometry) (old : ReadK) (a : AtK)
    (d : Nat) (t : Token) (h : (a,t)∈normalization g old) :
    ranked g a d (encode t) ≤ forwardRank (geometry g a.side) a.occurrence d (bound g old a) := by
  unfold normalization at h
  rcases List.mem_append.mp h with H|H
  · obtain ⟨j,_,J⟩ := List.mem_filterMap.mp H
    dsimp only at J
    split at J
    · have E : (j,bound g old j)=(a,t) := Option.some.inj J
      cases E
      simpa only [ranked,decode_encode] using bind_rank (geometry g a.side) a.occurrence d (bound g old a)
    · contradiction
  · obtain ⟨j,_,J⟩ := List.mem_map.mp H
    cases J
    exact Nat.zero_le _

private theorem no_middle_rank (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (d : Nat) (h : avoids a (middle g raw)) :
    ranked g a d ((routing g raw).foldl (fun k t => putRaw k a t) (readRaw raw a))≤
      ranked g a d (readRaw raw a) := by
  apply fold_rank _ _ _ _ _ _ (Nat.le_refl _)
  rw [routing_parts]
  rintro ⟨b,t⟩ hw E
  change b=a at E
  subst b
  rcases List.mem_append.mp hw with H|H
  · rcases List.mem_append.mp H with H|H
    · exact norm_rank _ _ _ d _ H
    · exact (h _ H rfl).elim
  · apply Nat.le_of_lt
    rw [ranked,decode_encode]
    exact
      (observed_assignment_rank g (readK raw) _ a t H d)

/-- Exact joined first-coordinate nonincrease on a slot with no
selected transport write. Normalization and actual race-observation
writes are included. Right K0 needs its separately framed door. -/
theorem joined_idle_rank (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (a : AtK) (d : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    avoids a (middle g raw) → DoorSafe g raw a →
    ranked g a d (readRaw (Pair.map LargeSite.long (largePair b x)) a)≤
      ranked g a d (readRaw raw a) := by
  dsimp only
  intro h hs
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a hs.valid]
  by_cases H : a.occurrence.val=0
  · obtain ⟨s,j⟩ := a
    have J : j=(0 : Fin 11) := Fin.ext H
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ s (hs.holds H)]
    exact no_middle_rank _ _ _ _ h
  · rw [raw_transit _ _ _ H]
    exact no_middle_rank _ _ _ _ h

theorem joined_clear_rank (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (C : CommandClaim) (d : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (C,.clear)∈actualOffers g raw →
    (C.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) →
    ranked g C.source d (readRaw (Pair.map LargeSite.long (largePair b x)) C.source)=0 := by
  dsimp only
  intro h V
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source V,selected_clear _ _ _ h]
  rfl

private theorem reply_zero (g : Pair LongGeometry) (a : AtK) (d : Nat) (p : Payload) :
    ranked g a d (encode (.reply p))=0 := by
  unfold ranked
  rw [decode_encode]
  have H := bind_rank (geometry g a.side) a.occurrence d (.reply p)
  exact Nat.eq_zero_of_le_zero H

theorem joined_reverse_rank (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (C : CommandClaim) (a : AtK) (t : Token) (d₁ d₂ : Nat) (hd : C.destination=some a)
    (ne : C.source≠a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (C,.reverse t)∈actualOffers g raw →
    (∀ q, (q=C.source ∨ q=a) → q=R 0 → g.2.axes.h6=true →
      LongDoorGuard.valid manifest raw.2=true) →
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    ranked g C.source d₁ (readRaw y C.source)=0 ∧ ranked g a d₂ (readRaw y a)=0 := by
  dsimp only
  intro h V
  obtain ⟨pay,rfl⟩ := (BStarClearanceCommandFrame.reverse_origin _ _ C a t hd h).2
  obtain ⟨S,D⟩ := reverse_endpoints _ _ C a (.reply pay) hd ne h
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source (V _ (.inl rfl)),
    joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a (V _ (.inr rfl)),S,D]
  exact ⟨reply_zero _ _ _ _,rfl⟩

#print axioms joined_idle_rank
#print axioms joined_clear_rank
#print axioms joined_reverse_rank
end L4.BStarClearanceNonforward

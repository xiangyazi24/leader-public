import Leader.L4.BStarResetChartTouch
import Leader.L4.BStarResetQuiet
import Leader.L4.BStarClearanceGate

namespace L4.BStarClearanceChartFootprint
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongTransport BStarLongEvents BStarH6WordChart BStarLongFiberOwner
open BStarLongRouting BStarResetQuiet

/-- Physical command footprint of a selected old-pair claim. -/
def footprint {n : Nat} (e : Fin n) (C : CommandClaim) : List (Fin n × Fin 11) :=
  C.slots.map (BStarResetMarkAdapter.address e)

theorem footprint_disjoint {n : Nat} (g : Pair LongGeometry) (e : Fin n)
    (he : e≠rightNeighbor e) (C D : CommandClaim)
    (hc : C∈orderedCommands g) (hd : D∈orderedCommands g) (neq : C≠D) :
    ∀ u∈footprint e C, u∉footprint e D := by
  intro u hcU hdU
  obtain ⟨s,hs,E⟩ := List.mem_map.mp hcU
  obtain ⟨t,ht,F⟩ := List.mem_map.mp hdU
  have eq := BStarResetMarkAdapter.address_inj e he (E.trans F.symm)
  subst t
  exact neq (BStarAcquireIncidence.same_claim g C D s hc hd hs ht)

/-- All addresses of a selected command have its physical chart owner. -/
theorem footprint_owner {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (C : CommandClaim)
    (hc : C∈orderedCommands (oldPair b x e)) (s : AtK) (hs : s∈C.slots) :
    physicalOwner (oldH6 b x) e cmdDispl s =
      physicalOwner (oldH6 b x) e cmdDispl C.source := by
  have H : s=C.source ∨ C.destination=some s := by
    cases J : C.destination <;> simpa [Claim.slots,J,eq_comm] using hs
  rcases H with rfl|H
  · rfl
  · exact (actual_command_owner b x e C s hc H).symm

/-- Actual integer-owner footprints are disjoint from other owners
and retain the pairwise separation even among commands of one owner. -/
theorem distinct_owners_do_not_touch {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (C : CommandClaim)
    (hc : C∈orderedCommands (oldPair b x e)) (s : AtK)
    (H : physicalOwner (oldH6 b x) e cmdDispl s ≠
      physicalOwner (oldH6 b x) e cmdDispl C.source) : s∉C.slots :=
  fun hs => H (footprint_owner b x e C hc s hs)

theorem no_touch_middle (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : AtK) (H : ∀ C∈orderedCommands g, s∉C.slots) :
    avoids s (middle g raw) := by
  apply middle_avoids_of_chart
  intro o ho hs
  have M : o.1 ∈ (actualOffers g raw).map Prod.fst :=
    List.mem_map.mpr ⟨o,ho,rfl⟩
  rw [actualOffers_claims] at M
  exact (H _ M hs).elim

/-- Quiet active slots untouched by all selected footprints retain
their full raw field; the source-door validity/hold obligations
remain separate and explicit. -/
theorem no_touch_frame (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    quiet (readK raw s) → s∉discarded g →
    (∀ C∈orderedCommands g, s∉C.slots) →
    (s=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) →
    (s.occurrence.val=0 → ∀ c k, (c,.door k)∈actualOffers g raw →
      c.source.side=s.side → BStarLongDoor.oldDoor (BStarLongWork.atOld raw c.source) k=.hold) →
    readRaw (Pair.map LargeSite.long (largePair b x)) s=readRaw raw s := by
  dsimp only
  intro h nd H valid door
  exact joined_quiet k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x s h nd (no_touch_middle _ _ _ H) valid door

/-- The lists used in the aggregate are the actual selected old
command footprints of this owner, with no chosen itinerary. -/
def ownerBlocks {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (o : Int) : List (List (Fin n × Fin 11)) :=
  ((orderedCommands (oldPair b x e)).filter
    (fun C => physicalOwner (oldH6 b x) e cmdDispl C.source == o)).map (footprint e)

private theorem flatMap_sub {A B : Type} (f : A → List B) {u v : List A}
    (h : u.Sublist v) : (u.flatMap f).Sublist (v.flatMap f) := by
  induction h with
  | slnil => exact .slnil
  | cons x h ih => exact ih.trans (List.sublist_append_right (f x) _)
  | cons_cons x h ih => exact ih.append_left (f x)

/-- On a non-self selected mark, all physical slots in those blocks
are distinct, including two incidences of one owner at a seam. -/
theorem ownerBlocks_nodup {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (he : e≠rightNeighbor e) (o : Int) :
    (ownerBlocks b x e o).flatten.Nodup := by
  let g := oldPair b x e
  let own := fun C : CommandClaim => physicalOwner (oldH6 b x) e cmdDispl C.source == o
  have all := (List.nodup_append.mp (geometry_exhaustive g.1 g.2).1).1
  have sub : (((orderedCommands g).filter own).flatMap Claim.slots).Nodup :=
    all.sublist (flatMap_sub Claim.slots List.filter_sublist)
  have j := sub.map (S := fun a b => a ≠ b) (BStarResetMarkAdapter.address e) (fun _ _ ne eq => ne (BStarResetMarkAdapter.address_inj e he eq))
  change (((orderedCommands g).filter own).flatMap (fun C => C.slots.map (BStarResetMarkAdapter.address e))).Nodup
  rw [←List.map_flatMap]
  exact j

/-- Every block slot is a physical address of the indicated owner.
Thus foreign selected commands cannot affect an uncovered slot via
their selected writes. -/
theorem ownerBlocks_owner {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (o : Int) (s : AtK)
    (h : BStarResetMarkAdapter.address e s∈(ownerBlocks b x e o).flatten)
    (he : e≠rightNeighbor e) :
    physicalOwner (oldH6 b x) e cmdDispl s=o := by
  unfold ownerBlocks at h
  rw [←List.flatMap_def] at h
  obtain ⟨C,hC,hs⟩ := List.mem_flatMap.mp h
  obtain ⟨hc,own⟩ := List.mem_filter.mp hC
  obtain ⟨d,hd,E⟩ := List.mem_map.mp hs
  have eq := BStarResetMarkAdapter.address_inj e he E
  subst d
  exact (footprint_owner b x e C hc s hd).trans (beq_iff_eq.mp own)

open BStarClearanceGate BStarLongCommand

private theorem fold_le (a : AtK) (f : BitVec 52 → Nat)
    (l : List KWrite) (z : BitVec 52) (cap : Nat) (hz : f z≤cap)
    (H : ∀ w∈l, w.1=a → f (encode w.2)≤cap) :
    f (l.foldl (fun k w => putRaw k a w) z)≤cap := by
  induction l generalizing z with
  | nil => exact hz
  | cons w l ih =>
    apply ih _ _ (fun s hs => H s (List.mem_cons_of_mem _ hs))
    unfold putRaw
    dsimp only
    split
    · rename_i eq
      exact H w List.mem_cons_self eq.symm
    · exact hz

/-- No selected footprint leaves the first coordinate increasing,
even when literal normalization repairs a dirty token or an idle
racing command receives its permitted observation. K0 is excluded;
its source/raw override requires a separate DoorSafe theorem. -/
theorem no_touch_rank_nonzero (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (s : AtK) (hs : s.occurrence.val≠0) (d : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (∀ C∈orderedCommands g, s∉C.slots) →
    forwardRank (geometry g s.side) s.occurrence d (readK (Pair.map LargeSite.long (largePair b x)) s) ≤
      forwardRank (geometry g s.side) s.occurrence d (readK raw s) := by
  dsimp only
  intro H
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let f := fun t : BitVec 52 => forwardRank (geometry g s.side) s.occurrence d (decode t)
  change f (readRaw (Pair.map LargeSite.long (largePair b x)) s) ≤ f (readRaw raw s)
  rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x s
    (fun eq _ => False.elim (hs (congrArg (fun t : AtK => t.occurrence.val) eq))),
    raw_transit g raw s hs]
  apply fold_le _ f _ _ _ (Nat.le_refl _)
  rintro ⟨a,new⟩ hw eq
  change a=s at eq
  subst a
  change forwardRank (geometry g s.side) s.occurrence d (decode (encode new)) ≤ _
  rw [BStarLongToken.decode_encode]
  rw [routing_parts] at hw
  rcases List.mem_append.mp hw with q|q
  · rcases List.mem_append.mp q with norm|mid
    · exact normalization_rank _ _ _ _ norm _
    · exact (no_touch_middle _ _ _ H _ mid rfl).elim
  · unfold observations at q
    obtain ⟨a,_,E⟩ := List.mem_filterMap.mp q
    split at E
    · contradiction
    · cases B : bound g (readK raw) a <;> simp only [B] at E
      · contradiction
      · contradiction
      · rename_i pay
        cases O : observe a (geometry g a.side) pay <;>
          simp only [O,Option.map_none,Option.map_some] at E
        · contradiction
        · rename_i q
          have J := Option.some.inj E
          cases J
          have P := observe_rank s (geometry g s.side) pay _ d O
          have F := bind_rank (geometry g s.side) s.occurrence d (readK raw s)
          change forwardRank (geometry g s.side) s.occurrence d (bound g (readK raw) s) ≤ _ at F
          rw [B] at F
          exact Nat.le_trans (by omega) F
      · contradiction

#print axioms no_touch_rank_nonzero
#print axioms ownerBlocks_nodup
#print axioms footprint_disjoint
#print axioms footprint_owner
#print axioms no_touch_frame
end L4.BStarClearanceChartFootprint

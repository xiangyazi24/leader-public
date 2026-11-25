import Leader.L4.BStarLongCopyFence

namespace L4.BStarLongFencePrefix
open AllSizeProtocol BStarLongClaims BStarLongPackets BStarLongPrep BStarLongCommandData

def Passed (g : Pair LongGeometry) (old : At Sheet → Lane) (s : At Sheet) : Prop :=
  fence (old s) (retains g s)=.advance

theorem passed_empty {g : Pair LongGeometry} {old : At Sheet → Lane} {s : At Sheet}
    (h : Passed g old s) : (old s).mobile=.empty := by
  unfold Passed fence at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i H
      exact Classical.byContradiction fun N => H (bne_iff_ne.mpr N)

private theorem fold_away (A : List (At Sheet × Leaf)) (old : At Sheet → Lane)
    (s : At Sheet) (ha : ∀ a, (s,a)∉A) :
    (A.foldl update old) s=old s := by
  induction A generalizing old with
  | nil => rfl
  | cons a A ih =>
    have ne : s≠a.1 := fun H => ha a.2 (by cases a; simp_all)
    rw [List.foldl_cons,ih (update old a) (fun a h => ha a (List.mem_cons_of_mem _ h))]
    simp [update,ne]

set_option maxHeartbeats 1200000 in
/-- No selected COPY statement changes a passed lane when the old
sender on every selected incoming link to it is empty. Its own old
emptiness rules out a send or END error. Reservation alone is not
the invariant: it must exclude prep and nonempty incoming traffic. -/
theorem passed_lane_frame (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW)) (s : At Sheet)
    (h : Passed g (view x) s)
    (noPrep : s∉reserved (round g x).prep)
    (noIncoming : ∀ c∈orderedData g (reserved (round g x).prep),
      c.destination=some s → (view x c.source).mobile=.empty) :
    view (patchPair (patch g x) x) s=view x s := by
  rw [BStarLongCommandData.round_transfer]
  apply fold_away
  intro a ha
  rcases List.mem_append.mp ha with hp|hd
  · exact noPrep (prep_lane_reserved _ _ _ _ hp)
  · obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp hd
    have hSlot := data_lane_claim g (view x) c s a hd
    obtain ⟨kind,u,v⟩ := c
    change s∈u::v.toList at hSlot
    cases kind with
    | ending =>
      have H : u=s := by
        unfold dataEffects at hd
        simp only at hd
        obtain ⟨b,_,he⟩ := List.mem_map.mp hd
        exact congrArg Prod.fst he
      subst u
      simp [dataEffects,endEffects,passed_empty h] at hd
    | hop =>
      cases v with
      | none => simp [dataEffects] at hd
      | some v =>
        have E : s=u ∨ s=v := by simpa only [Option.toList_some,List.mem_cons,List.not_mem_nil,or_false] using hSlot
        have zero : (view x u).mobile=.empty := by
          rcases E with e|e
          · rw [←e]; exact passed_empty h
          · subst v
            exact noIncoming ⟨.hop,u,some s⟩ hc rfl
        simp only [dataEffects, hopEffects, zero, if_true, List.map_nil, List.nil_append, List.not_mem_nil] at hd

/-- Closure for a passed prefix when selected old-data incidence is
closed into that prefix and no prep reopens any passed lane. Allows
arbitrary writes, failures, and retained data outside the prefix. -/
theorem passed_prefix_step (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (P : At Sheet → Prop)
    (oldPassed : ∀ s, P s → Passed g (view x) s)
    (noPrep : ∀ s, P s → s∉reserved (round g x).prep)
    (incomingClosed : ∀ c∈orderedData g (reserved (round g x).prep),
      ∀ s, P s → c.destination=some s → P c.source) :
    ∀ s, P s → Passed g (view (patchPair (patch g x) x)) s := by
  intro s hs
  have h := oldPassed s hs
  have F := passed_lane_frame g x s h (noPrep s hs)
    (fun c hc hd => passed_empty (oldPassed c.source (incomingClosed c hc s hs hd)))
  simp only [Passed,F]
  exact h

/-- On a genuinely active FENCE (opcode 11, nonfault, mapped sheet),
advancing authenticates readiness of precisely the old physical lane. -/
theorem mapped_fence_passes (g : Pair LongGeometry) (old : At Sheet → Lane)
    (j : At (Fin 11)) (p : BStarLongToken.Payload) (sh : Sheet)
    (hf : p.fault=0) (ho : p.opcode.toNat=11)
    (hm : fenceSheet (BStarLongCommand.geometry g j.side) j.occurrence=some sh) :
    checkFence g old j p=.advance ↔ Passed g old ⟨j.side,sh⟩ := by
  simp [checkFence,hf,ho,hm,Passed]

/-- Progress on the newly admitted prefix endpoint is valid on the
same physical COPY mark if the extended prefix is closed to old
incoming packets and disjoint from selected prep. -/
theorem extend_passed_on_mark (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (P : At Sheet → Prop) (j : At (Fin 11)) (p : BStarLongToken.Payload) (sh : Sheet)
    (hf : p.fault=0) (ho : p.opcode.toNat=11)
    (hm : fenceSheet (BStarLongCommand.geometry g j.side) j.occurrence=some sh)
    (ha : checkFence g (view x) j p=.advance)
    (oldPassed : ∀ s, P s → Passed g (view x) s)
    (noPrep : ∀ s, (P s ∨ s=⟨j.side,sh⟩) → s∉reserved (round g x).prep)
    (incomingClosed : ∀ c∈orderedData g (reserved (round g x).prep),
      ∀ s, (P s ∨ s=⟨j.side,sh⟩) → c.destination=some s →
        P c.source ∨ c.source=⟨j.side,sh⟩) :
    ∀ s, (P s ∨ s=⟨j.side,sh⟩) → Passed g (view (patchPair (patch g x) x)) s := by
  apply passed_prefix_step g x _ _ noPrep incomingClosed
  intro s hs
  rcases hs with h|rfl
  · exact oldPassed s h
  · exact (mapped_fence_passes g (view x) j p sh hf ho hm).mp ha

end L4.BStarLongFencePrefix

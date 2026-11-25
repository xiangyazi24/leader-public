import Leader.L4.BStarLongFencePrefix

/-! Literal old-data tests at the two retaining FENCE endpoints. -/
namespace L4.BStarFenceTerminalData
open AllSizeProtocol BStarLongClaims BStarLongPackets BStarLongCommandData
open BStarLongFencePrefix

theorem passed_retaining {g : Pair LongGeometry} {old : At Sheet → Lane} {s : At Sheet}
    (retaining : retains g s = true) (h : Passed g old s) :
    ∃ d, (old s).retained = .data d := by
  have emp := passed_empty h
  unfold Passed at h
  rw [retaining] at h
  cases hr : (old s).retained with
  | empty => simp [fence, emp, hr, BStarLongPrep.validPayload] at h
  | bad => simp [fence, emp, hr, BStarLongPrep.validPayload] at h
  | data d => exact ⟨d, rfl⟩

private theorem retains_inside (g : Pair LongGeometry) (side : Side)
    (sh : Sheet) (hs : sh = .ld ∨ sh = .rd)
    (hin : (BStarLongCommand.geometry g side).inside = true) :
    retains g ⟨side,sh⟩ = true := by
  rcases hs with rfl | rfl <;> cases side <;>
    simp_all [retains,BStarLongCommand.geometry]

theorem k7_old_left_data (g : Pair LongGeometry) (old : At Sheet → Lane)
    (side : Side) (p : BStarLongToken.Payload)
    (hin : (BStarLongCommand.geometry g side).inside = true)
    (hf : p.fault=0) (ho : p.opcode.toNat=11)
    (ha : checkFence g old ⟨side,7⟩ p = .advance) :
    (old ⟨side,.ld⟩).mobile = .empty ∧ ∃ d, (old ⟨side,.ld⟩).retained = .data d := by
  have hm : fenceSheet (BStarLongCommand.geometry g side) (7 : Fin 11) = some .ld := by
    change (if (BStarLongCommand.geometry g side).inside then some Sheet.ld else none) = _
    rw [hin]; rfl
  have h := (mapped_fence_passes g old ⟨side,7⟩ p .ld hf ho hm).mp ha
  exact ⟨passed_empty h,passed_retaining (retains_inside g side .ld (.inl rfl) hin) h⟩

theorem k10_old_right_data (g : Pair LongGeometry) (old : At Sheet → Lane)
    (side : Side) (p : BStarLongToken.Payload)
    (hin : (BStarLongCommand.geometry g side).inside = true)
    (hf : p.fault=0) (ho : p.opcode.toNat=11)
    (ha : checkFence g old ⟨side,10⟩ p = .advance) :
    (old ⟨side,.rd⟩).mobile = .empty ∧ ∃ d, (old ⟨side,.rd⟩).retained = .data d := by
  have hm : fenceSheet (BStarLongCommand.geometry g side) (10 : Fin 11) = some .rd := rfl
  have h := (mapped_fence_passes g old ⟨side,10⟩ p .rd hf ho hm).mp ha
  exact ⟨passed_empty h,passed_retaining (retains_inside g side .rd (.inr rfl) hin) h⟩

/-- A surviving healthy advance in the actual immutable-old round
cannot have been synthesized by the FENCE fault or prep-cancel paths. -/
theorem surviving_advance_checked (g : Pair LongGeometry)
    (x : Pair (BitVec BStarTrace.LW)) (c : CommandClaim)
    (p : BStarLongToken.Payload) (hf : p.fault = 0)
    (h : (c,.advance p) ∈ (round g x).offered) :
    checkFence g (BStarLongPrep.view x) c.source p = .advance := by
  change (c,.advance p) ∈ (gated g x).map (cancel (round g x).faults) at h
  obtain ⟨⟨b,t⟩,ht,he⟩ := List.mem_map.mp h
  have hc : (c,.advance p) ∈ gated g x := by
    cases t <;> simp [cancel] at he
    rename_i q
    by_cases hb : b.source ∈ (round g x).faults
    · simp [hb] at he
      have H := congrArg BStarLongToken.Payload.fault he.2
      simp [failedPayload,hf] at H
    · simp [hb] at he
      simpa [he.1,he.2] using ht
  unfold gated at hc
  obtain ⟨⟨b,t⟩,_,he⟩ := List.mem_map.mp hc
  simp only [Prod.mk.injEq] at he
  rcases he with ⟨rfl,he⟩
  cases t with
  | hold | door _ | reverse _ | clear => simp [checkOffer] at he
  | advance q =>
    simp only [checkOffer] at he
    cases H : checkFence g (BStarLongPrep.view x) b.source q <;> simp [H] at he
    · subst q
      exact H
    · have hp := congrArg BStarLongToken.Payload.fault he
      simp [failedPayload,hf] at hp

theorem surviving_k7_data (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (c : CommandClaim) (p : BStarLongToken.Payload)
    (hc : c.source.occurrence = 7)
    (hin : (BStarLongCommand.geometry g c.source.side).inside = true)
    (hf : p.fault=0) (ho : p.opcode.toNat=11)
    (h : (c,.advance p) ∈ (round g x).offered) :
    let old := BStarLongPrep.view x ⟨c.source.side,.ld⟩
    old.mobile = .empty ∧ ∃ d, old.retained = .data d := by
  have H := surviving_advance_checked g x c p hf h
  have E : c.source = ⟨c.source.side,7⟩ := by rw [← hc]
  rw [E] at H
  exact k7_old_left_data g (BStarLongPrep.view x) c.source.side p hin hf ho H

theorem surviving_k10_data (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (c : CommandClaim) (p : BStarLongToken.Payload)
    (hc : c.source.occurrence = 10)
    (hin : (BStarLongCommand.geometry g c.source.side).inside = true)
    (hf : p.fault=0) (ho : p.opcode.toNat=11)
    (h : (c,.advance p) ∈ (round g x).offered) :
    let old := BStarLongPrep.view x ⟨c.source.side,.rd⟩
    old.mobile = .empty ∧ ∃ d, old.retained = .data d := by
  have H := surviving_advance_checked g x c p hf h
  have E : c.source = ⟨c.source.side,10⟩ := by rw [← hc]
  rw [E] at H
  exact k10_old_right_data g (BStarLongPrep.view x) c.source.side p hin hf ho H

#print axioms surviving_k7_data
#print axioms surviving_k10_data
#print axioms surviving_advance_checked
#print axioms passed_retaining
#print axioms k7_old_left_data
#print axioms k10_old_right_data
end L4.BStarFenceTerminalData

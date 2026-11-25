import Leader.L4.BStarLongEvents
import Leader.L4.BStarLongDoor

/-! Literal local custody for the generated forward COMMIT lane.
This module deliberately does not infer issue provenance from payload equality. -/
namespace L4.BStarCommitLineage
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand BStarLongTransport

def CommitF (p : Payload) : Prop := p.fault=0 ∧ p.opcode.toNat=commitOp

/-- A valid forward COMMIT has no race gate, on any old geometry or occurrence. -/
theorem commit_not_parked (g : LongGeometry) (j : Fin 11) (p : Payload)
    (h : CommitF p) : gate p.opcode.toNat j g=false := by
  obtain ⟨_,op⟩ := h
  rw [op]
  simp [gate,commitOp,admit,bitOp]

theorem commit_depart_exact (g : LongGeometry) (j : Fin 11) (p : Payload)
    (h : CommitF p) : depart g j p=some p := by
  simp [depart,commit_not_parked g j p h]

theorem commit_arrive_exact (g : LongGeometry) (j : Fin 11) (p : Payload)
    (h : CommitF p) : arrive g j p=.forward p := by
  simp [arrive,commit_not_parked g j p h]

theorem commit_observe_none (a : At (Fin 11)) (g : LongGeometry) (p : Payload)
    (h : CommitF p) : observe a g p=none := by
  simp [observe,commit_not_parked g a.occurrence p h]

/-- On every non-door offer the genuine old forward front is prior to
destination reply handling. This is true even for a parked forward
token not yet allowed to advance. -/
theorem forward_blocks_reverse (c : CommandClaim) (g : LongGeometry) (p : Payload)
    (oldNeighbor : Token) (hd : (c.kind==.door)=false) (r : Token) :
    classify c g (.forward p) oldNeighbor≠.reverse r := by
  intro hh
  simp only [classify,hd,Bool.false_eq_true,if_false] at hh
  split at hh <;> cases hh

/-- For this opcode there is no park: all old downstream tokens,
including inherited matching replies, give the same forward offer. -/
theorem commit_overwrites_old_neighbor (c : CommandClaim) (g : LongGeometry) (p : Payload)
    (h : CommitF p) (oldNeighbor : Token) (hd : (c.kind==.door)=false) :
    classify c g (.forward p) oldNeighbor=.advance p := by
  simp [classify,hd,commit_depart_exact g c.source.occurrence p h]

theorem commit_hop_intent (g : Pair LongGeometry) (c : CommandClaim)
    (dest : AtK) (p : Payload) (h : CommitF p) (hd : c.destination=some dest) :
    advanceK g c p=[(c.source,.trail),(dest,.forward p)] := by
  simp [advanceK,hd,commit_arrive_exact (geometry g dest.side) dest.occurrence p h]

/-- Terminal servicing does not produce a forward opcode. -/
theorem terminal_not_forward (p q : Payload) : finish p≠.forward q := by
  unfold finish
  dsimp only
  split
  · simp [fault]
  · split
    · split <;> simp
    · split <;> simp [fault]

/-- A wiring-generated reverse offer is always the inherited or
generated *reply* at its old destination, never a forward cursor. -/
theorem reverse_origin (c : CommandClaim) (g : LongGeometry)
    (u v t : Token) (h : classify c g u v=.reverse t) :
    ∃ p : Payload, v=.reply p ∧ t=.reply p := by
  by_cases hd : (c.kind==.door)=true
  · simp [classify,hd] at h
  · have d : (c.kind==.door)=false := Bool.eq_false_iff.mpr hd
    cases u with
    | forward q => exact (forward_blocks_reverse c g q v d t h).elim
    | empty | trail | reply =>
      simp only [classify,d,Bool.false_eq_true,if_false] at h
      split at h
      · split at h <;> cases h
      · cases v with
        | reply p => cases h; exact ⟨p,rfl,rfl⟩
        | empty | trail | forward => split at h <;> (try contradiction) <;> cases h

/-- No duplicate source issue while the valid controller waits for
this front or its solid trail; a matching inherited reply remains a
separate case and is intentionally not authenticated by this lemma. -/
theorem wait_while_tag_outbound (x : BitVec LW) (p : Payload)
    (valid : LongDoorGuard.valid manifest x=true)
    (wait : (BStarLongDoor.ctrlPhase.read x).toNat=2) :
    BStarLongDoor.oldDoor x (.forward p)=.hold ∧
    BStarLongDoor.oldDoor x .trail=.hold :=
  ⟨BStarLongDoor.wait_holds_forward x p valid wait,
    BStarLongDoor.wait_holds_trail x valid wait⟩

/-- Exact old-pair raw patch for the isolated custody handoff.
The source becomes T, the destination receives the original payload
unmodified, and every different occurrence holds even its old spare
bytes after readK. Global use must still prove the absence of
overlapping issued intents on these two owned slots. -/
theorem raw_hop_custody (g : Pair LongGeometry) (c : CommandClaim) (dest : AtK)
    (p : Payload) (h : CommitF p) (hd : c.destination=some dest)
    (x : Pair (BitVec LW)) (distinct : c.source≠dest) :
    let y := readK (patchPair (compile (advanceK g c p)) x)
    y c.source=.trail ∧ y dest=.forward p ∧
      ∀ a, a≠c.source → a≠dest → y a=readK x a := by
  rw [exact_k_transfer,commit_hop_intent g c dest p h hd]
  simp only [List.foldl_cons,List.foldl_nil,assign]
  refine ⟨?_,?_,?_⟩
  · simp [distinct]
  · simp
  · intro a h1 h2
    simp [h1,h2]

end L4.BStarCommitLineage

import Leader.L4.BStarClearanceGate
import Leader.L4.BStarResetQuiet

/-! Actual selected forward charge, with the fixed owner distance
decrement supplied by the rail chart. No opcode-specific success
condition is needed for a committed routing assignment. -/
namespace L4.BStarClearanceForward
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongRouting BStarLongWork BStarLongEvents
open BStarClearanceGate

/-- The literal payload after the numeric and outgoing handlers. -/
def carried (g : Pair LongGeometry) (x : Pair (BitVec LW)) (c : CommandClaim) (p : Payload) : Payload :=
  let gg := geometry g c.source.side
  let old := BStarLongWork.atOld x c.source
  match (BStarLongOutgoing.execute gg c.source.occurrence old
      (BStarLongArithmetic.visit gg c.source.occurrence old p).2).carried with
  | .forward q => q
  | _ => ⟨1,0,0,0,0⟩

theorem move_intent (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (a : AtK) (h : c.destination=some a) :
    (selected g x (c,.advance p)).k=
      [(c.source,.trail),(a,arrive (geometry g a.side) a.occurrence (carried g x c p))] := by
  simp only [selected,advanceK,h,carried]
  rfl

theorem move_lands (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (a : AtK) (h : c.destination=some a)
    (sel : (c,.advance p)∈actualOffers g x) (ne : c.source≠a) :
    let y := patchPair (longWork g x) x
    readRaw y c.source=encode .trail ∧
      readRaw y a=encode (arrive (geometry g a.side) a.occurrence (carried g x c p)) := by
  have I := move_intent g x c p a h
  dsimp only
  constructor
  · apply BStarResetQuiet.actual_write g x (c,.advance p) sel
    · rw [I]; exact List.mem_cons_self
    · intro k; rw [I]; simp [putRaw,ne]
  · apply BStarResetQuiet.actual_write g x (c,.advance p) sel
    · rw [I]; simp
    · intro k; rw [I]; simp [putRaw]

/-- Rebound first-coordinate rank of an actual raw slot. -/
def ranked (g : Pair LongGeometry) (a : AtK) (d : Nat) (t : BitVec 52) : Nat :=
  forwardRank (geometry g a.side) a.occurrence d
    (BStarLongCommand.bind (geometry g a.side) a.occurrence (decode t))

private theorem arrival_rank (g : LongGeometry) (j : Fin 11) (d : Nat) (p : Payload) :
    forwardRank g j d (arrive g j p) ≤ 4*d+2 := by
  unfold arrive
  split <;> simp only [forwardRank]
  all_goals have k := bounded g j (.forward p)
  · exact Nat.add_le_add_left (bounded _ _ _) _
  · omega

private theorem terminal_rank (g : LongGeometry) (j : Fin 11) (d : Nat) (p : Payload) :
    forwardRank g j d (BStarLongCommand.bind g j (finish p)) = 0 := by
  have finishR : ∃ q, finish p=.reply q := by
    unfold finish
    dsimp only
    split
    · exact ⟨_,rfl⟩
    · split
      · split <;> exact ⟨_,rfl⟩
      · split <;> exact ⟨_,rfl⟩
  obtain ⟨q,E⟩ := finishR
  rw [E]
  have H := bind_rank g j d (.reply q)
  exact Nat.eq_zero_of_le_zero H

/-- Upper bound on the new rank after moving an arbitrary forward.
In particular moving a prep front pays even if the branch canceled
its payload to a recognizable forward fault. -/
theorem move_charge (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p old : Payload) (a : AtK) (h : c.destination=some a)
    (sel : (c,.advance p)∈actualOffers g x) (ne : c.source≠a) (d : Nat)
    (front : BStarLongCommand.bind (geometry g c.source.side) c.source.occurrence
      (decode (readRaw x c.source))=.forward old) :
    let y := patchPair (longWork g x) x
    ranked g c.source (d+1) (readRaw y c.source) + ranked g a d (readRaw y a) <
      ranked g c.source (d+1) (readRaw x c.source) + ranked g a d (readRaw x a) := by
  dsimp only
  obtain ⟨L,R⟩ := move_lands g x c p a h sel ne
  unfold ranked
  rw [L,R,decode_encode,decode_encode,front]
  have E := Nat.le_trans (bind_rank (geometry g a.side) a.occurrence d
      (arrive (geometry g a.side) a.occurrence (carried g x c p)))
    (arrival_rank _ _ _ _)
  change 0 + forwardRank (geometry g a.side) a.occurrence d
      (BStarLongCommand.bind (geometry g a.side) a.occurrence
        (arrive (geometry g a.side) a.occurrence (carried g x c p))) <
    4*(d+1)+weight (geometry g c.source.side) c.source.occurrence (.forward old)+_
  omega

/-- The chosen terminal emits a reply after every forward, even after
a fault. The owner distance counts this terminal service as positive. -/
theorem turn_charge (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p old : Payload) (h : c.destination=none)
    (sel : (c,.advance p)∈actualOffers g x) (d : Nat) (positive : 0<d)
    (front : BStarLongCommand.bind (geometry g c.source.side) c.source.occurrence
      (decode (readRaw x c.source))=.forward old) :
    let y := patchPair (longWork g x) x
    ranked g c.source d (readRaw y c.source) < ranked g c.source d (readRaw x c.source) := by
  dsimp only
  have E : readRaw (patchPair (longWork g x) x) c.source=encode (finish (carried g x c p)) :=
    BStarResetQuiet.terminal_finish g x c p h sel
  unfold ranked
  rw [E,decode_encode,front,terminal_rank]
  simp only [forwardRank]
  omega

#print axioms move_lands
#print axioms move_charge
#print axioms turn_charge
end L4.BStarClearanceForward

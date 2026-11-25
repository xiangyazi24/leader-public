import Leader.L4.BStarCopyUpstreamCredit

/-! Literal local mobile clearance, including occupied BAD and old
FENCE which holds without bidding for a preparation reservation. -/
namespace L4.BStarClearanceMobile
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarCopyFIFO BStarCopyUpstreamCredit
open BStarLongToken BStarLongCommand

def rank (d : Nat) (x : Lane) : Nat := d*mass x

theorem rank_le (d : Nat) (x : Lane) : rank d x≤d := by
  unfold rank mass
  split <;> simp

/-- A rightmost occupied mobile whose successor is vacant pays by
moving or disposal. Retention may displace an OLD packet, but creates
at most one pending mobile at the closer endpoint. BAD is occupied. -/
theorem vacant_hop_charge (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (sel : c∈orderedData g (reserved (round g x).prep)) (ne : u≠v)
    (occupied : (view x u).mobile≠.empty) (vacant : (view x v).mobile=.empty)
    (d : Nat) :
    rank (d+1) (post g x u)+rank d (post g x v) <
      rank (d+1) (view x u)+rank d (view x v) := by
  have A : (post g x u).mobile=.empty := by
    unfold post
    rw [sender_exact g x u v c hs hd hh sel ne]
    cases G : ((view x u).gate && (view x v).gate) <;>
      simp [hopEffects,occupied,vacant,G,typedLeaves,Leaf.put]
  have B := rank_le d (post g x v)
  have L : rank (d+1) (post g x u)=0 := by simp [rank,mass,A]
  have R : rank (d+1) (view x u)=d+1 := by simp [rank,mass,occupied]
  omega

/-- Disabled links dispose of the occupied source before inspecting
the destination vacancy, so the same charge is valid even if blocked
by another mobile at the receiver. -/
theorem closed_hop_charge (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (sel : c∈orderedData g (reserved (round g x).prep)) (ne : u≠v)
    (occupied : (view x u).mobile≠.empty)
    (closed : ((view x u).gate && (view x v).gate)=false) (d e : Nat) (positive : 0<d) :
    rank d (post g x u)+rank e (post g x v) <
      rank d (view x u)+rank e (view x v) := by
  unfold post
  rw [sender_exact g x u v c hs hd hh sel ne,
    BStarLongCopyFence.receiver_exact g x u v c hs hd hh sel ne,
    hop_disabled _ _ _ occupied closed]
  simp [rank,mass,typedLeaves,Leaf.put,occupied]
  exact Nat.lt_add_of_pos_left positive

/-- A parked, checked old FENCE contributes no preparation offer.
Other origins may still reserve the relevant lane. -/
theorem fence_hold_no_offer (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload)
    (h : checkFence g (view x) c.source p = .hold) :
    preparedBy g x [(c,checkOffer g (view x) (c,.advance p))]=[] := by
  simp [checkOffer,h,preparedBy]

/-- Even an advancing FENCE opcode has no preparation class. -/
theorem fence_advance_no_offer (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (op : p.opcode.toNat=11) :
    preparedBy g x [(c,.advance p)]=[] := by
  by_cases I : p.fault=0 <;> simp [preparedBy,fieldOffers,I,op,prepOf]

private theorem fold_away (A : List (At Sheet × Leaf)) (old : At Sheet → Lane)
    (t : At Sheet) (away : ∀ a, (t,a)∉A) :
    (A.foldl update old) t=old t := by
  induction A generalizing old with
  | nil => rfl
  | cons a A ih =>
    have ne : t≠a.1 := fun H => away a.2 (by cases a; simp_all)
    rw [List.foldl_cons,ih (update old a) (fun a h => away a (List.mem_cons_of_mem _ h))]
    simp [update,ne]

private theorem fold_at' (s : At Sheet) (A : List Leaf) (old : At Sheet → Lane) :
    ((A.map (s,·)).foldl update old) s=typedLeaves (old s) A := by
  induction A generalizing old with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons,List.foldl_cons,ih]
    simp [typedLeaves,update]

/-- Selected END has exactly the literal old-lane effects; exclusive
claim reservation excludes any competing writer. -/
theorem terminal_exact (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (t : At Sheet) (hc : ending t∈orderedData g (reserved (round g x).prep))
    : post g x t=typedLeaves (view x t) (endEffects (view x t)) := by
  let P := (round g x).prep
  let old := view x
  let L := orderedData g (reserved P)
  have slot : t∈(ending t).slots := by simp [Claim.slots,ending]
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp hc
  change L=l++ending t::r at E
  have K := data_reservations g (reserved P)
  have H : L.Pairwise (fun a b => ∀ s∈b.slots, s∉a.slots) := K.1
  rw [E] at H
  have pre (a : Leaf) : (t,a)∉prepAssignments old P :=
    fun m => K.2 (ending t) hc t slot (prep_lane_reserved old P t a m)
  have before (a : Leaf) : (t,a)∉l.flatMap (dataEffects g old) := by
    intro M
    obtain ⟨c,hc,M⟩ := List.mem_flatMap.mp M
    exact (H.rel_of_mem_append hc (by simp : ending t∈ending t::r))
      t slot (data_lane_claim g old c t a M)
  have after (a : Leaf) : (t,a)∉r.flatMap (dataEffects g old) := by
    intro M
    obtain ⟨c,hc,M⟩ := List.mem_flatMap.mp M
    have Q := (List.pairwise_cons.mp (List.pairwise_append.mp H).2.1).1 c hc
    exact Q t (data_lane_claim g old c t a M) slot
  unfold post
  rw [BStarLongCommandData.round_transfer]
  change ((prepAssignments old P ++ L.flatMap (dataEffects g old)).foldl update old) t=_
  rw [E,List.flatMap_append,List.flatMap_cons]
  simp only [List.foldl_append]
  change ((r.flatMap (dataEffects g old)).foldl update
    (((endEffects (old t)).map (t,·)).foldl update
      ((l.flatMap (dataEffects g old)).foldl update ((prepAssignments old P).foldl update old)))) t=_
  rw [fold_away _ _ _ after,fold_at',fold_away _ _ _ before,fold_away _ _ _ pre]

theorem terminal_charge (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (t : At Sheet) (sel : ending t∈orderedData g (reserved (round g x).prep))
    (occupied : (view x t).mobile≠.empty) (d : Nat) (h : 0<d) :
    rank d (post g x t) < rank d (view x t) := by
  rw [terminal_exact g x t sel, end_occupied _ occupied]
  simpa [rank,mass,typedLeaves,Leaf.put,occupied] using h

/-- Inserting a checked FENCE hold anywhere into the offer stream
does not change the prep list or any resulting reservation. -/
theorem fence_hold_reservations (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (l r : List BStarLongWork.CmdOffer) (c : CommandClaim) (p : Payload)
    (h : checkFence g (view x) c.source p=.hold) :
    reserved (preparedBy g x (l++(c,checkOffer g (view x) (c,.advance p))::r)) =
    reserved (preparedBy g x (l++r)) := by
  simp [preparedBy,List.flatMap_append,checkOffer,h]

end L4.BStarClearanceMobile

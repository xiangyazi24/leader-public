import Leader.L4.BStarCopyCapacity
import Leader.L4.BStarLongLiteral

/-! The old tagged INJECT occurrence creates a literal preparation offer
at its own source lane. Arbitration reserves the lane before routing. -/
namespace L4.BStarCopyInjection
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongPackets BStarLongCommandData BStarLongLiteral
open BStarLongPrep BStarLongCommand

def sourceOccurrence (reverse : Bool) : Fin 11 := if reverse then 2 else 5
def sourceLane (reverse : Bool) : Sheet := if reverse then .rs else .ls

def injection (side : Side) (reverse : Bool) : BStarLongPrep.Offer :=
  ⟨⟨.inject,⟨side,sourceOccurrence reverse⟩,⟨side,sourceLane reverse⟩⟩,.empty⟩

/-- A valid old numeric INJECT (opcode 10) at a selected non-door
occurrence is not a FENCE/stationary-race and enters preparation. -/
theorem literal_offer (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (side : Side) (reverse : Bool)
    (selected : c∈orderedCommands g) (door : c.kind≠.door)
    (origin : c.source=⟨side,sourceOccurrence reverse⟩)
    (old : bind (geometry g c.source.side) c.source.occurrence (oldTokens x c.source)=.forward p)
    (clean : p.fault=0) (opcode : p.opcode.toNat=10) (inside : (geometry g side).inside=true) :
    injection side reverse∈(round g x).prep := by
  have E : classifyOld g x c = .advance p := by
    unfold classifyOld classify
    simp [old,door,depart,gate,opcode,admit,bitOp]
  have G : gatedAt g x c=.advance p := by
    unfold gatedAt
    rw [E]
    simp [checkOffer,checkFence,opcode]
  apply List.mem_flatMap.mpr
  refine ⟨(c,.advance p),(gated_mem g x c _).mpr ⟨selected,G.symm⟩,?_⟩
  change injection side reverse ∈ fieldOffers g x c.source p
  rw [origin]
  cases reverse <;> simp [fieldOffers,clean,opcode,prepOf,prepClaims,prepSites,
    injection,sourceOccurrence,sourceLane,inside]

private theorem member_offered {T : Type} (key : T → Nat) (a : T) (L : List T) :
    a∈offers key L ↔ a∈L := by
  induction L with
  | nil => simp [offers]
  | cons x L ih =>
    change a∈BStarLongClaims.insert key x (offers key L) ↔ _
    rw [mem_insert,ih,List.mem_cons]

private theorem exclusive_select (a : BStarLongPrep.Offer) (L : List BStarLongPrep.Offer)
    (used : List (At Sheet)) (haveA : a∈L) (freeA : a.claim.lane∉used)
    (onlyA : ∀ z∈L, z.claim.lane=a.claim.lane → z=a) :
    a∈select (fun z : BStarLongPrep.Offer => [z.claim.lane]) used L := by
  induction L generalizing used with
  | nil => contradiction
  | cons z T ih =>
    by_cases E : z=a
    · subst z
      have A : free used [a.claim.lane]=true := (free_iff ..).mpr (by simpa using freeA)
      simp [select,A]
    · have M : a∈T := by
        rcases List.mem_cons.mp haveA with h|h
        · exact (E h.symm).elim
        · exact h
      have N : z.claim.lane≠a.claim.lane :=
        fun eq => E (onlyA _ List.mem_cons_self eq)
      unfold select
      split
      · exact List.mem_cons_of_mem _ (ih _ M
          (by simpa [Ne.symm N] using freeA)
          (fun t m => onlyA t (List.mem_cons_of_mem _ m)))
      · exact ih _ M freeA (fun t m => onlyA t (List.mem_cons_of_mem _ m))

/-- Exclusivity refers only to the actual same-mark prep offer list at
this lane. Other-owner activity at disjoint lanes is unrestricted. -/
theorem exclusive_winner (a : BStarLongPrep.Offer) (P : List BStarLongPrep.Offer)
    (haveA : a∈P) (unique : ∀ z∈P, z.claim.lane=a.claim.lane → z=a) :
    a∈(arbitration P).1 := by
  unfold arbitration
  rw [arbitrate_winners]
  apply exclusive_select a _ []
  · exact (member_offered _ _ _).mpr haveA
  · simp
  · intro z hz
    exact unique z ((member_offered _ _ _).mp hz)

theorem injection_success (v : Lane) (data : BitVec 36)
    (enabled : v.gate=true) (frozen : v.frozen=.data data) (vacant : v.mobile=.empty) :
    effects v .inject .empty=⟨[.mobile (.data data),.frozen .empty],false⟩ := by
  simp [effects,enabled,frozen,vacant,validPayload]

theorem injection_failure (v : Lane)
    (blocked : v.gate=false ∨ validPayload v.frozen=false ∨ v.mobile≠.empty) :
    effects v .inject .empty=⟨[.error true],true⟩ := by
  rcases blocked with H|H|H <;> simp [effects,H]

private theorem fold_away (A : List (At Sheet × Leaf)) (old : At Sheet → Lane)
    (s : At Sheet) (ha : ∀ a, (s,a)∉A) :
    (A.foldl update old) s=old s := by
  induction A generalizing old with
  | nil => rfl
  | cons a A ih =>
    have ne : s≠a.1 := fun H => ha a.2 (by cases a; simp_all)
    rw [List.foldl_cons,ih (update old a) (fun a h => ha a (List.mem_cons_of_mem _ h))]
    simp [update,ne]

private theorem fold_at (s : At Sheet) (A : List Leaf) (old : At Sheet → Lane) :
    ((A.map (s,·)).foldl update old) s=typedLeaves (old s) A := by
  induction A generalizing old with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons,List.foldl_cons,ih]
    simp [typedLeaves,update]

/-- The winning old-pair preparation is the only writer of that
lane, even on an idempotent or failed write. Its reservation stops
both incoming and outgoing COPY hops on the injection mark. -/
theorem selected_prep_exact (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (a : BStarLongPrep.Offer) (winner : a∈(arbitration (round g x).prep).1) :
    let old := view x
    let s := a.claim.lane
    view (patchPair (patch g x) x) s=typedLeaves (old s) (selectedEffects old a).writes := by
  let P := (round g x).prep
  let old := view x
  let s := a.claim.lane
  let S := (arbitration P).1
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp winner
  change S=l++a::r at E
  have D : S.Pairwise (fun b c : BStarLongPrep.Offer => c.claim.lane≠b.claim.lane) := by
    have M := select_pairwise (fun b : BStarLongPrep.Offer => [b.claim.lane]) []
      (offers offerPriority P)
    unfold S arbitration
    rw [arbitrate_winners]
    exact M.imp (by intro b c h ec; exact h _ List.mem_cons_self (by simp [ec]))
  rw [E] at D
  let eff := fun b : BStarLongPrep.Offer => (selectedEffects old b).writes.map (b.claim.lane,·)
  have aroundL : ∀ t, (s,t)∉l.flatMap eff := by
    intro t H
    obtain ⟨b,hb,hh⟩ := List.mem_flatMap.mp H
    obtain ⟨u,_,he⟩ := List.mem_map.mp hh
    exact (D.rel_of_mem_append hb (by simp : a∈a::r)) (congrArg Prod.fst he).symm
  have aroundR : ∀ t, (s,t)∉r.flatMap eff := by
    intro t H
    obtain ⟨b,hb,hh⟩ := List.mem_flatMap.mp H
    obtain ⟨u,_,he⟩ := List.mem_map.mp hh
    exact (List.pairwise_cons.mp (List.pairwise_append.mp D).2.1).1 b hb (congrArg Prod.fst he)
  have dataAway : ∀ t, (s,t)∉(orderedData g (reserved P)).flatMap (dataEffects g old) := by
    intro t hm
    obtain ⟨c,hc,ht⟩ := List.mem_flatMap.mp hm
    have Rs : s∈reserved P := List.mem_map.mpr ⟨a,winner,rfl⟩
    exact (data_reservations g (reserved P)).2 _ hc _ (data_lane_claim g old _ _ _ ht) Rs
  dsimp only
  rw [BStarLongCommandData.round_transfer]
  change ((S.flatMap eff ++ (orderedData g (reserved P)).flatMap (dataEffects g old)).foldl update old) s=_
  rw [E,List.flatMap_append,List.flatMap_cons]
  simp only [List.foldl_append]
  rw [fold_away _ _ _ dataAway,fold_away _ _ _ aroundR,fold_at,fold_away _ _ _ aroundL]

/-- A tagged owner actually issues literal INJECT into the empty source
mobile and clears the old frozen field. The label is external custody,
not reconstructed from the payload bytes. -/
theorem literal_inject {Label : Type} (digits : Label → BitVec 36) (tag : Label)
    (g : Pair LongGeometry) (x : Pair (BitVec LW)) (c : CommandClaim) (p : Payload)
    (side : Side) (reverse : Bool)
    (selected : c∈orderedCommands g) (door : c.kind≠.door)
    (origin : c.source=⟨side,sourceOccurrence reverse⟩)
    (old : bind (geometry g c.source.side) c.source.occurrence (oldTokens x c.source)=.forward p)
    (clean : p.fault=0) (opcode : p.opcode.toNat=10) (inside : (geometry g side).inside=true)
    (unique : ∀ z∈(round g x).prep, z.claim.lane=(injection side reverse).claim.lane →
      z=injection side reverse)
    (enabled : (view x (injection side reverse).claim.lane).gate=true)
    (frozen : (view x (injection side reverse).claim.lane).frozen=.data (digits tag))
    (vacant : (view x (injection side reverse).claim.lane).mobile=.empty) :
    let a := injection side reverse
    let v := view x a.claim.lane
    selectedEffects (view x) a=⟨[.mobile (.data (digits tag)),.frozen .empty],false⟩ ∧
      view (patchPair (patch g x) x) a.claim.lane =
        {v with mobile:=BStarCopyFIFO.encode digits (some tag),frozen:=.empty} := by
  dsimp only
  let a := injection side reverse
  have M := literal_offer g x c p side reverse selected door origin old clean opcode inside
  have W := exclusive_winner a (round g x).prep M unique
  have E : selectedEffects (view x) a=⟨[.mobile (.data (digits tag)),.frozen .empty],false⟩ :=
    injection_success _ _ enabled frozen vacant
  exact ⟨E,by rw [selected_prep_exact g x a W,E]; rfl⟩

/-- Neither a predecessor nor a successor COPY hop can use a lane
reserved by a winning INJECT in the same old-pair round. -/
theorem same_mark_reserved (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (a : BStarLongPrep.Offer) (w : a∈(arbitration (round g x).prep).1)
    (d : DataClaim) (m : d∈orderedData g (reserved (round g x).prep)) :
    a.claim.lane∉d.slots := by
  intro H
  exact (data_reservations g _).2 d m _ H (List.mem_map.mpr ⟨a,w,rfl⟩)

/-- Independently stored source labels budget the number of leases
released. Payload collisions are irrelevant to the schedule. -/
structure ReleaseHistory (Label : Type) where
  released : List Label
  pending : List Label

def ReleaseHistory.Follows {Label : Type} (plan : List Label) (s : ReleaseHistory Label) : Prop :=
  plan=s.released++s.pending

def ReleaseHistory.init {Label : Type} (plan : List Label) : ReleaseHistory Label := ⟨[],plan⟩

/-- Empty/wait/exterior marks are silent. A real successful release
moves the head of the prescribed injection order into history. -/
inductive ReleaseStep {Label : Type} : ReleaseHistory Label → ReleaseHistory Label → Prop
  | hold (s : ReleaseHistory Label) : ReleaseStep s s
  | inject (done : List Label) (a : Label) (todo : List Label) :
      ReleaseStep ⟨done,a::todo⟩ ⟨done++[a],todo⟩

theorem ReleaseStep.follows {Label : Type}
    (plan : List Label) {s u : ReleaseHistory Label} (h : s.Follows plan) (t : ReleaseStep s u) :
    u.Follows plan := by
  cases t with
  | hold => exact h
  | inject => simpa [ReleaseHistory.Follows,List.append_assoc] using h

/-- Any common prefix with first-receiver arrivals subordinate to
these successful releases meets the initial COPY capacity premise.
This does not infer the subordination from arbitrary raw bytes. -/
theorem first_arrival_cap {Label : Type} (plan : List Label) (s : ReleaseHistory Label)
    (q : BStarCopyFIFO.Queue Label) (H : s.Follows plan)
    (ordered : q.arrivals.length≤s.released.length) :
    q.arrivals.length≤plan.length := by
  have h := congrArg List.length H
  simp only [List.length_append] at h
  omega

end L4.BStarCopyInjection

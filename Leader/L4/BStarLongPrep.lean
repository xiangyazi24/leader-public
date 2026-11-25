import Leader.L4.BStarLongPackets

/-! Literal COPY preparation and data round as consumed by the long binding.
All effects read the immutable old pair. A lane is reserved by the
selected offer, even if the physical prep fails or writes an old value. -/
namespace L4.BStarLongPrep
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets

structure Offer where
  claim : PrepClaim
  payload : Digit9
  deriving DecidableEq, Repr

def propose (g : Pair LongGeometry) (a : At (Fin 11)) (op : Prep) (payload : Digit9) :
    List Offer :=
  let z := match a.side with | .left => g.1 | .right => g.2
  (prepClaims z a op).map (⟨·,payload⟩)

structure Effects where
  writes : List Leaf
  fault : Bool
  deriving DecidableEq, Repr

def validPayload : Digit9 → Bool
  | .data _ => true
  | _ => false

/-- LOAD always assigns frozen and error, including EMPTY failure; an
invalid INJECT assigns only the error latch, preserving the raw packet. -/
def effects (v : Lane) (op : Prep) (payload : Digit9) : Effects :=
  match op with
  | .clear | .rclear => ⟨[.error false,.mobile .empty,.frozen .empty,.retained .empty],false⟩
  | .stop | .rstop => ⟨[.gate false],false⟩
  | .enable => ⟨[.gate true],false⟩
  | .load => ⟨[.frozen payload,.error (v.error || payload.isBad)],!validPayload payload⟩
  | .inject =>
    if !v.gate || !validPayload v.frozen || v.mobile != .empty then
      ⟨[.error true],true⟩
    else ⟨[.mobile v.frozen,.frozen .empty],false⟩

/-- Keep both arms of arbitration; losers are occurrences of offers,
not a set difference that could erase a duplicate loss. -/
def arbitrate (used : List (At Sheet)) : List Offer → Pair (List Offer)
  | [] => ([],[])
  | a::t =>
    if free used [a.claim.lane] then
      let out := arbitrate (a.claim.lane::used) t
      (a::out.1,out.2)
    else
      let out := arbitrate used t
      (out.1,a::out.2)

def offerPriority (a : Offer) : Nat := prepKey a.claim

def arbitration (P : List Offer) : Pair (List Offer) :=
  arbitrate [] (offers offerPriority P)

theorem arbitrate_winners (used : List (At Sheet)) (P : List Offer) :
    (arbitrate used P).1=select (fun a => [a.claim.lane]) used P := by
  induction P generalizing used with
  | nil => rfl
  | cons a t ih =>
    simp only [arbitrate,select]
    split <;> simp [ih]

theorem arbitrate_losers (used : List (At Sheet)) (P : List Offer) :
    (arbitrate used P).2.Sublist P := by
  induction P generalizing used with
  | nil => exact .slnil
  | cons a t ih =>
    unfold arbitrate
    split
    · exact .cons _ (ih _)
    · exact .cons_cons _ (ih _)

theorem arbitrate_partition (used : List (At Sheet)) (P : List Offer) :
    (arbitrate used P).1.length+(arbitrate used P).2.length=P.length := by
  induction P generalizing used with
  | nil => rfl
  | cons a t ih =>
    unfold arbitrate
    split
    · have h := ih (a.claim.lane::used)
      simp only [List.length_cons]
      omega
    · have h := ih used
      simp only [List.length_cons]
      omega

def reserved (P : List Offer) : List (At Sheet) :=
  (arbitration P).1.map (fun a => a.claim.lane)

def selectedEffects (old : At Sheet → Lane) (a : Offer) : Effects :=
  effects (old a.claim.lane) a.claim.op a.payload

def prepAssignments (old : At Sheet → Lane) (P : List Offer) : List (At Sheet × Leaf) :=
  (arbitration P).1.flatMap fun a => (selectedEffects old a).writes.map (a.claim.lane,·)

def prepFaults (old : At Sheet → Lane) (P : List Offer) : List (At (Fin 11)) :=
  (arbitration P).2.map (fun a => a.claim.origin) ++
    ((arbitration P).1.filter (fun a => (selectedEffects old a).fault)).map (fun a => a.claim.origin)

def prepWrites (old : At Sheet → Lane) (P : List Offer) : List (Write LW) :=
  (prepAssignments old P).map (fun (s,a) => writeAt s a)

def assignments (g : Pair LongGeometry) (old : At Sheet → Lane) (P : List Offer) :
    List (At Sheet × Leaf) :=
  prepAssignments old P ++ (orderedData g (reserved P)).flatMap (dataEffects g old)

def writes (g : Pair LongGeometry) (old : At Sheet → Lane) (P : List Offer) :
    List (Write LW) :=
  (assignments g old P).map (fun (s,a) => writeAt s a)

theorem writes_split (g : Pair LongGeometry) (old : At Sheet → Lane) (P : List Offer) :
    writes g old P=prepWrites old P ++ dataWrites g old (reserved P) := by
  simp only [writes,assignments,prepWrites,dataWrites,List.map_append,List.map_flatMap]

theorem prep_lane_reserved (old : At Sheet → Lane) (P : List Offer) (s : At Sheet) (a : Leaf)
    (ha : (s,a)∈prepAssignments old P) : s∈reserved P := by
  obtain ⟨win,hw,hp⟩ := List.mem_flatMap.mp ha
  obtain ⟨leaf,_,e⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨win,hw,congrArg Prod.fst e⟩

theorem data_lane_claim (g : Pair LongGeometry) (old : At Sheet → Lane) (c : DataClaim)
    (s : At Sheet) (a : Leaf) (h : (s,a)∈dataEffects g old c) : s∈c.slots := by
  obtain ⟨k,u,v⟩ := c
  cases k <;> cases v <;> simp [dataEffects,Claim.slots] at h ⊢
  · exact h.2.symm
  · exact Or.inl h.2.symm
  · rcases h with h|h
    · exact .inl h.2.symm
    · exact .inr h.2.symm

theorem prep_data_disjoint (g : Pair LongGeometry) (old : At Sheet → Lane) (P : List Offer)
    (s : At Sheet) (a b : Leaf) (ha : (s,a)∈prepAssignments old P) :
    (s,b)∉(orderedData g (reserved P)).flatMap (dataEffects g old) := by
  intro hb
  obtain ⟨c,hc,hs⟩ := List.mem_flatMap.mp hb
  exact (data_reservations g (reserved P)).2 c hc s (data_lane_claim g old c s b hs)
    (prep_lane_reserved old P s a ha)

theorem failed_winner_faults (old : At Sheet → Lane) (P : List Offer) (a : Offer)
    (ha : a∈(arbitration P).1) (hf : (selectedEffects old a).fault=true) :
    a.claim.lane∈reserved P ∧ a.claim.origin∈prepFaults old P :=
  ⟨List.mem_map.mpr ⟨a,ha,rfl⟩,
   List.mem_append_right _ (List.mem_map.mpr ⟨a,List.mem_filter.mpr ⟨ha,hf⟩,rfl⟩)⟩

#print axioms arbitrate_winners
#print axioms writes_split
#print axioms prep_data_disjoint
#print axioms failed_winner_faults

def view (x : Pair (BitVec LW)) (s : At Sheet) : Lane :=
  readLane (Sheet.index s.occurrence) (lane (s.side == .right) x)

def update (old : At Sheet → Lane) (a : At Sheet × Leaf) : At Sheet → Lane :=
  fun s => if s=a.1 then a.2.put (old s) else old s

private theorem index_injective (a b : Sheet) (h : Sheet.index a=Sheet.index b) : a=b := by
  cases a <;> cases b <;> simp_all [Sheet.index]

theorem write_view (x : Pair (BitVec LW)) (a : At Sheet × Leaf) :
    view (runWrite x (writeAt a.1 a.2).patch)=update (view x) a := by
  obtain ⟨⟨d,sh⟩,v⟩ := a
  funext s
  obtain ⟨ds,ss⟩ := s
  have same : ss≠sh → Sheet.index ss≠Sheet.index sh :=
    fun H J => H (index_injective _ _ J)
  cases d <;> cases ds <;> by_cases h : ss=sh
  all_goals try subst ss
  all_goals simp [view,update,writeAt_patch,runWrite,lane,readLane_assign, *]
  all_goals exact readLane_other _ _ (same h) _ _

theorem fold_view (x : Pair (BitVec LW)) (A : List (At Sheet × Leaf)) :
    view ((A.map (fun a => (writeAt a.1 a.2).patch)).foldl runWrite x) =
      A.foldl update (view x) := by
  induction A generalizing x with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons,List.foldl_cons,ih,write_view]

/-- The issued byte patch refines the literal old-pair payload effect
sequence, with support and held padding digested by the leaf codec. -/
theorem round_transfer (g : Pair LongGeometry) (x : Pair (BitVec LW)) (P : List Offer) :
    let old := view x
    let T : Trace LW Unit := ⟨writes g old P,[]⟩
    view (patchPair T.lower x) = (assignments g old P).foldl update old := by
  dsimp only [Trace.lower,writes]
  rw [lower_apply]
  simpa only [List.map_map,Function.comp_def] using fold_view x (assignments g (view x) P)

private def fixtureLane : Lane := ⟨false,false,.empty,.empty,.bad⟩

theorem failed_load_fixture :
    effects fixtureLane .load .empty=⟨[.frozen .empty,.error false],true⟩ ∧
    effects fixtureLane .inject .bad=⟨[.error true],true⟩ ∧
    effects fixtureLane .stop .bad=⟨[.gate false],false⟩ := by
  decide +kernel

#print axioms round_transfer
#print axioms failed_load_fixture
end L4.BStarLongPrep

import Leader.L4.BStarClearanceIndexedWait

/-! No-fresh-issue least interpreted forward frontier. Every forward
constructor counts, including the normalized canonical forward fault. -/
namespace L4.DirtyLeastForward
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongRouting BStarLongWork BStarLongCommand BStarLongEvents BStarLongTransport BStarResetQuiet
open BStarClearanceForward BStarClearanceGate BStarClearanceAggregate BStarClearanceCommandSum

def IsForward (g : Pair LongGeometry) (a : AtK) (raw : BitVec 52) : Prop :=
  ∃ p, bind (geometry g a.side) a.occurrence (decode raw)=.forward p

theorem forward_lower (g : Pair LongGeometry) (a : AtK) (d : Nat) (raw : BitVec 52)
    (h : IsForward g a raw) : 4*d ≤ ranked g a d raw := by
  obtain ⟨p,E⟩ := h
  unfold ranked
  rw [E]
  exact Nat.le_add_right _ _

theorem no_forward_zero (g : Pair LongGeometry) (a : AtK) (d : Nat) (raw : BitVec 52)
    (h : ¬IsForward g a raw) : ranked g a d raw=0 := by
  unfold ranked
  cases E : bind (geometry g a.side) a.occurrence (decode raw) with
  | forward p => exact (h ⟨p,E⟩).elim
  | empty | trail | reply => rfl

theorem rank_upper (g : Pair LongGeometry) (a : AtK) (d : Nat) (raw : BitVec 52) :
    ranked g a d raw ≤ 4*d+2 := by
  unfold ranked
  cases bind (geometry g a.side) a.occurrence (decode raw) with
  | empty | trail | reply => exact Nat.zero_le _
  | forward p =>
      exact Nat.add_le_add_left (bounded (geometry g a.side) a.occurrence (.forward p)) _

/-- A disjoint actual block containing a forward after the mark
has a forward origin at the same or earlier slot. In particular its
earlier endpoint cannot have obtained a forward from its successor.
Fault normalization is included in the rank used here. -/
theorem link_origin (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (act : Offer) (a : AtK) (hd : C.destination=some a)
    (ne : a≠C.source) (nd : C.kind≠.door) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    (C,act)∈actualOffers g raw →
    (∀ u∈C.slots, BStarResetQuietTable.DoorSafe g raw u) →
    (IsForward g C.source (readRaw y C.source) → IsForward g C.source (readRaw raw C.source)) ∧
    (IsForward g a (readRaw y a) → IsForward g C.source (readRaw raw C.source) ∨
      IsForward g a (readRaw raw a)) := by
  dsimp only
  intro H S
  let d := fun u : AtK => if u=C.source then 2 else 1
  have Q := (BStarClearanceCommandSum.block k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C act d H S
    (by intro u E; have uEq : u=a := Option.some.inj (E.symm.trans hd); subst u; simp [d,ne])
    (by simp [hd]) (fun E => (nd E).elim)).1
  simp only [Claim.slots,hd,Option.toList_some,total,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero,d,if_true,if_neg ne] at Q
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have L := forward_lower _ _ 2 _ h
    have Z := no_forward_zero _ _ 2 _ hn
    have U := rank_upper (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x) a 1 (readRaw (Pair.map LargeSite.long x) a)
    erw [Z,Nat.zero_add] at Q
    have E := Nat.le_trans L (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans Q U))
    omega
  · intro h
    apply Classical.byContradiction
    intro hn
    have L := forward_lower _ _ 1 _ h
    have Z := no_forward_zero _ _ 2 _ (fun v => hn (.inl v))
    have W := no_forward_zero _ _ 1 _ (fun v => hn (.inr v))
    erw [Z,W,Nat.zero_add] at Q
    have E := Nat.le_trans L (Nat.le_trans (Nat.le_add_left _ _) Q)
    omega

theorem singleton_origin (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (act : Offer) (hd : C.destination=none) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    (C,act)∈actualOffers g raw →
    (∀ u∈C.slots, BStarResetQuietTable.DoorSafe g raw u) →
    (C.kind=.door → ranked g C.source 1 (readRaw y C.source)
      ≤ ranked g C.source 1 (readRaw raw C.source)) →
    IsForward g C.source (readRaw y C.source) → IsForward g C.source (readRaw raw C.source) := by
  dsimp only
  intro H S Door F
  have Q := (BStarClearanceCommandSum.block k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C act (fun _ => 1)
    H S (by simp [hd]) (fun _ _ => by decide) Door).1
  simp only [Claim.slots,hd,Option.toList_none,total,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero] at Q
  apply Classical.byContradiction
  intro N
  have Z := no_forward_zero _ _ 1 _ N
  have L := forward_lower _ _ 1 _ F
  erw [Z] at Q
  have E := Nat.le_trans L Q
  omega

theorem idle_origin (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    avoids a (middle g raw) → BStarResetQuietTable.DoorSafe g raw a →
    IsForward g a (readRaw y a) → IsForward g a (readRaw raw a) := by
  dsimp only
  intro H S F
  apply Classical.byContradiction
  intro N
  have Q := BStarClearanceNonforward.joined_idle_rank k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a 1 H S
  have L := forward_lower _ _ 1 _ F
  have Z := no_forward_zero _ _ 1 _ N
  erw [Z] at Q
  have E := Nat.le_trans L Q
  omega

/-- Literal endpoint classifier: the sole exception is the selected
entrance singleton, where the controller may promote a new forward. -/
theorem pair_origin (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    (∀ C∈orderedCommands g, a∈C.slots → ∀ u∈C.slots,
      BStarResetQuietTable.DoorSafe g raw u) →
    BStarResetQuietTable.DoorSafe g raw a →
    IsForward g a (readRaw y a) →
    IsForward g a (readRaw raw a) ∨
    (∃ C∈orderedCommands g, C.destination=some a ∧
      IsForward g C.source (readRaw raw C.source)) ∨
    ∃ C∈orderedCommands g, C.kind=.door ∧ C.source=a := by
  dsimp only
  intro S A F
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  by_cases touch : ∃ C∈orderedCommands g, a∈C.slots
  · obtain ⟨C,hC,ha⟩ := touch
    have H := hC
    rw [←actualOffers_claims g raw] at H
    obtain ⟨⟨C₂,act⟩,H,Eq⟩ := List.mem_map.mp H
    change C₂=C at Eq
    subst C₂
    by_cases D : C.kind=.door
    · have E := (BStarResetChartIndex.selected_door g C hC D).2.2
      exact .inr (.inr ⟨C,hC,D,(by simpa [Claim.slots,E] using ha : a=C.source).symm⟩)
    · cases hd : C.destination with
      | none =>
          have E : a=C.source := by simpa [Claim.slots,hd] using ha
          subst a
          exact .inl (singleton_origin _ _ _ _ _ _ _ _ _ hp x C act hd H
            (S C hC (by simp [Claim.slots])) (fun U => (D U).elim) F)
      | some u =>
          have ne := (BStarAcquireReturn.link_shape g C u hC hd).1
          obtain ⟨P,Q⟩ := link_origin _ _ _ _ _ _ _ _ _ hp x C act u hd ne D H (S C hC ha)
          have E : a=C.source ∨ a=u := by simpa [Claim.slots,hd] using ha
          rcases E with rfl|rfl
          · exact .inl (P F)
          · rcases Q F with V|V
            · exact .inr (.inl ⟨C,hC,hd,V⟩)
            · exact .inl V
  · exact .inl (idle_origin _ _ _ _ _ _ _ _ _ hp x a
      (BStarClearanceChartFootprint.no_touch_middle g raw a (fun C H I => touch ⟨C,H,I⟩)) A F)

/-- Under the rank-at-one source hold hook, the joined actual pair
has no promotion at all. Geometry is evaluated at the same old pair. -/
theorem pair_no_promotion (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (a : AtK) (d : Nat) (hd : 0<d) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    (∀ C∈orderedCommands g, a∈C.slots → ∀ u∈C.slots,
      BStarResetQuietTable.DoorSafe g raw u) →
    BStarResetQuietTable.DoorSafe g raw a →
    (∀ C∈orderedCommands g, C.kind=.door → C.source=a →
      ranked g a d (readRaw y a)≤ranked g a d (readRaw raw a)) →
    IsForward g a (readRaw y a) →
    IsForward g a (readRaw raw a) ∨
    ∃ C∈orderedCommands g, C.destination=some a ∧ IsForward g C.source (readRaw raw C.source) := by
  dsimp only
  intro S A door F
  rcases pair_origin k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a S A F with h|h|⟨C,c,D,U⟩
  · exact .inl h
  · exact .inr h
  · apply Or.inl
    apply Classical.byContradiction
    intro N
    have Q := door C c D U
    have Z := no_forward_zero _ _ d _ N
    have L := forward_lower _ _ d _ F
    erw [Z] at Q
    have E := Nat.le_trans L Q
    omega

theorem isForward_iff (g : Pair LongGeometry) (a : AtK) (raw : BitVec 52) :
    IsForward g a raw ↔ BStarClearanceCommandFrame.forwardCount (decode raw)=1 := by
  have E := congrArg Prod.fst (BStarClearanceCommandFrame.bind_counts
    (geometry g a.side) a.occurrence (decode raw))
  unfold IsForward
  cases H : bind (geometry g a.side) a.occurrence (decode raw) <;>
    simp [H,BStarClearanceCommandFrame.forwardCount] at E ⊢ <;> simp [←E]

open BStarAcquireVisitOrder BStarLongFiberOwner BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFixedRouting BStarClearanceOffset BStarResetMarkAdapter
open BStarClearanceIndexedSum BStarClearanceIndexedWait BStarH6WordChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n

/-- No interpreted F is normalized to any other token class, so the
physical readout uses its raw constructor; coordinates never rebase. -/
def ringF (x : X) (u : Pos n) : Prop :=
  BStarClearanceCommandFrame.forwardCount (atSite (x u.1).long u.2)=1

theorem ring_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i,Layout B base i=Layout B x i)
    (e : Fin n) (he : e≠rightNeighbor e)
    (wait : BeforeOwnService hp x (endpoint (oldH6 B base) hh o 0).1 e)
    (u : Pos n) (us : u∈S) :
    ringF (AllSizeS1Geometry.step B x e) u →
    ringF x u ∨ ∃ v∈S, ringF x v ∧ distance S v=distance S u+1 := by
  intro F
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let z := (x e,x (rightNeighbor e))
  let y := AllSizeS1Geometry.step B x e
  let ar := address e
  by_cases cut : u.1=e ∨ u.1=rightNeighbor e
  · obtain ⟨a,ha⟩ : ∃ a : AtK, ar a=u := by
      obtain ⟨i,j⟩ := u
      rcases cut with h|h <;> dsimp only at h <;> subst i
      · exact ⟨L j,rfl⟩
      · exact ⟨R j,rfl⟩
    subst u
    obtain ⟨part,own,adj⟩ := chart_owner_hypotheses hp chart same e
    obtain ⟨safe,door⟩ := pre_service_hypotheses hp chart same e he wait
    have old (t : AtK) : IsForward g t (readRaw raw t) ↔ ringF x (ar t) := by
      rcases t with ⟨side,j⟩; cases side <;> exact isForward_iff _ _ _
    have new (t : AtK) :
        IsForward g t (readRaw (Pair.map LargeSite.long (largePair B z)) t) ↔ ringF y (ar t) := by
      rw [isForward_iff]
      rcases t with ⟨side,j⟩
      cases side <;> simp [ringF,y,ar,AllSizeS1Geometry.step,site,Ne.symm he,z] <;> rfl
    have mem (C : CommandClaim) (hc : C∈orderedCommands g) (atA : a∈C.slots)
        (t : AtK) (ht : t∈C.slots) : ar t∈S := by
      have oq := (BStarClearanceChartFootprint.footprint_owner B x e C hc a atA).symm.trans (own a us)
      exact part (List.mem_flatten.mpr ⟨_,List.mem_map.mpr ⟨C,
        List.mem_filter.mpr ⟨hc,beq_iff_eq.mpr oq⟩,rfl⟩,List.mem_map.mpr ⟨t,ht,rfl⟩⟩)
    have pos : 0<distance S (ar a) :=
      Nat.sub_pos_of_lt (List.findIdx_lt_length_of_exists ⟨_,us,by simp⟩)
    have nav := pair_no_promotion _ _ _ _ _ _ _ _ _ hp z a (distance S (ar a)) pos
      (fun C hc ha t ht => safe t (mem C hc ha t ht)) (safe a us)
      (fun C hc D H => by
        have DoorRank := door C hc (H ▸ own a us) D
        rw [H] at DoorRank
        rcases a with ⟨side,j⟩
        cases side
        · change BStarClearanceForward.ranked g (L j) _ (readRaw (Pair.map LargeSite.long (largePair B z)) (L j)) ≤ _
          simp only [physicalRank,address,site,AllSizeS1Geometry.step,if_true] at DoorRank
          exact DoorRank
        · change BStarClearanceForward.ranked g (R j) _ (readRaw (Pair.map LargeSite.long (largePair B z)) (R j)) ≤ _
          simp only [physicalRank,address,site,AllSizeS1Geometry.step,if_neg (Ne.symm he),if_true] at DoorRank
          exact DoorRank)
      ((new a).mpr F)
    rcases nav with h|⟨C,hc,edge,V⟩
    · exact .inl ((old a).mp h)
    · have da : a∈C.slots := by simp [Claim.slots,edge]
      have ms := mem C hc da C.source (by simp [Claim.slots])
      exact .inr ⟨ar C.source,ms,(old _).mp V, (adj C hc (own _ ms)).1 _ edge⟩
  · have Y : y u.1=x u.1 := by
      simp [y,AllSizeS1Geometry.step,show u.1≠e from fun h => cut (.inl h),show u.1≠rightNeighbor e from fun h => cut (.inr h)]
    exact .inl (by simpa only [ringF,Y] using (show ringF y u from F))

/-- A suffix of actual pre-service marks cannot send a forward behind
the old frontier. A larger remaining distance means an earlier slot.
If all slots are initially forward-free, use cutoff zero. -/
theorem ring_frontier_run {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (tape : List (Fin n)) (cutoff : Nat)
    (good : ∀ pre e post, tape=pre++e::post →
      let z := pre.foldl (AllSizeS1Geometry.step B) x
      (∀ i,Layout B base i=Layout B z i) ∧
      BeforeOwnService hp z (endpoint (oldH6 B base) hh o 0).1 e)
    (clear : ∀ u∈S, cutoff<distance S u → ¬ringF x u) :
    ∀ u∈S, cutoff<distance S u →
      ¬ringF (tape.foldl (AllSizeS1Geometry.step B) x) u := by
  induction tape generalizing x with
  | nil => exact clear
  | cons e tail ih =>
      apply ih (x:=AllSizeS1Geometry.step B x e)
      · intro pre f post T
        exact good (e::pre) f post (congrArg (List.cons e) T)
      · have H := good [] e tail rfl
        intro u U far F
        rcases ring_origin hp chart H.1 e (sep e) H.2 u U F with old|⟨v,V,old,eq⟩
        · exact clear u U far old
        · exact clear v V (by omega) old

/-- A trace can create a forward only at the same/next chart slot or
through a separately supplied entrance promotion. This predicate is
per actual mark and does not require the entire chart to be clean. -/
def OriginStep (before after : Nat → Prop) (promotion : Prop) : Prop :=
  ∀ j, after j → (promotion ∧ j=0) ∨ before j ∨
    ∃ i, j=i+1 ∧ before i

theorem prefix_absent_step {before after : Nat → Prop} {promotion : Prop}
    (step : OriginStep before after promotion) (no : ¬promotion) (cut : Nat)
    (empty : ∀ j, j<cut → ¬before j) :
    ∀ j, j<cut → ¬after j := by
  intro j hj H
  rcases step j H with h|h|⟨i,rfl,hi⟩
  · exact no h.1
  · exact empty j hj h
  · exact empty i (by omega) hi

theorem prefix_absent_run {S Mark : Type} (next : S → Mark → S)
    (F : S → Nat → Prop) (promoted : S → Mark → Prop)
    (step : ∀ x e, OriginStep (F x) (F (next x e)) (promoted x e))
    (cut : Nat) (x : S) (tape : List Mark)
    (no : ∀ u e v, tape=u++e::v → ¬promoted (u.foldl next x) e)
    (empty : ∀ j, j<cut → ¬F x j) :
    ∀ j, j<cut → ¬F (tape.foldl next x) j := by
  induction tape generalizing x with
  | nil => exact empty
  | cons e tail ih =>
      apply ih (next x e)
      · intro u f v E
        apply no (e::u) f v
        simp only [List.cons_append]
        exact congrArg (List.cons e) E
      · exact prefix_absent_step (step x e) (no [] e tail rfl) cut empty

end L4.DirtyLeastForward

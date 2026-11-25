import Leader.L4.BStarClearanceMobileWeak
import Leader.L4.BStarCopyGateAuthority

/-! A generated owner holding FENCE cannot reserve its own data lanes.
The selected literal hop is dominated by open exclusion on the same
two cells, including BAD mobiles and terminal retention displacement. -/
namespace L4.BStarFenceOccupancy
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarLongFiberOwner BStarH6WordChart
open BStarAcquireAnchors BStarAcquireVisitOrder BStarResetChartTouch BStarGeneratedOwner BStarGeneratedBandScan BStarClearanceMobile
open BStarCopyUpstreamCredit BStarCopyFIFO BStarClearanceDataChart BStarAcquireLiteralChain

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "play" => BStarResetSchedule.run (AllSizeS1Geometry.step (n:=n) B)

/-- Other controllers may reserve lanes on this same physical edge.
Only the lanes of the authenticated opcode-11 owner are excluded. -/
theorem no_reservation {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (pc11 : pc (play x w) (S.getD 0 fall).1=11)
    (e : Fin n) (s : At Sheet)
    (own : dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val) :
    s∉reserved (round (oldPair B (play x w) e)
      (((play x w) e).long,((play x w) (rightNeighbor e)).long)).prep := by
  intro mem
  obtain ⟨a,win,eq⟩ := List.mem_map.mp mem
  have H := BStarCopyGateAuthority.winning_prep_pc hp chart sep hist now layout e a
    (by rw [eq]; exact own) win
  rw [pc11] at H
  change none = some _ at H
  contradiction

/-- It is enough to exclude reservations at the claim's own slots.
There is no contention with any other geometric data claim. -/
theorem select_unreserved (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (D : DataClaim) (nom : D∈orderedData g [])
    (clear : ∀ s∈D.slots, s∉reserved (round g raw).prep) :
    D∈orderedData g (reserved (round g raw).prep) := by
  rw [BStarClearancePrepOwner.orderedData_filter]
  exact List.mem_filter.mpr ⟨nom,(free_iff _ _).mpr clear⟩

/-- Every nominal service of the FENCE owner survives arbitration,
including a terminal END with no destination. -/
theorem owner_nomination_selected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (pc11 : pc (play x w) (S.getD 0 fall).1=11)
    (e : Fin n) (D : DataClaim)
    (nom : D∈orderedData (oldPair B (play x w) e) [])
    (own : dataOwner (oldH6 B base) (site e D.source.side) D.source.occurrence=o.val) :
    D∈orderedData (oldPair B (play x w) e) (reserved (round (oldPair B (play x w) e)
      (((play x w) e).long,((play x w) (rightNeighbor e)).long)).prep) := by
  apply select_unreserved _ _ _ nom
  intro s hs
  apply no_reservation hp chart sep hist now layout pc11 e s
  have slots : s=D.source ∨ D.destination=some s := by
    cases h : D.destination with
    | none => exact Or.inl (by simpa [Claim.slots,h] using hs)
    | some a =>
      have H : s=D.source ∨ s=a := by simpa [Claim.slots,h] using hs
      exact H.imp id (fun eq => by rw [eq])
  rcases slots with hs | hs
  · simpa only [hs] using own
  · have eq := actual_data_owner B (play x w) e [] D s nom hs
    have H : oldH6 B (play x w)=oldH6 B base :=
      funext fun t => (congrArg Prod.fst (layout t)).symm
    rw [H] at eq
    change dataOwner (oldH6 B base) (site e D.source.side) D.source.occurrence =
      dataOwner (oldH6 B base) (site e s.side) s.occurrence at eq
    exact eq.symm.trans own

def occupied (x : Lane) : Bool := decide (x.mobile ≠ .empty)

/-- The actual hop may destroy a mobile, but cannot exceed the occupancy
of the same open-exclusion hop applied to the same old occupancy. -/
theorem local_hop (x y : Lane) (keep : Bool) :
    (occupied (typedLeaves x (hopEffects x y keep).1)=true →
        (occupied x && occupied y)=true) ∧
    (occupied (typedLeaves y (hopEffects x y keep).2)=true →
        (occupied x || occupied y)=true) := by
  by_cases A : x.mobile = .empty
  · simp [occupied,hopEffects,A,typedLeaves]
  · by_cases G : (x.gate && y.gate)=true
    · by_cases D : y.mobile = .empty
      · cases keep <;> simp [occupied,hopEffects,A,G,D,typedLeaves,Leaf.put]
      · simp [occupied,hopEffects,A,G,D,typedLeaves]
    · have Z : (x.gate && y.gate)=false := Bool.eq_false_iff.mpr G
      simp [occupied,hopEffects,A,Z,typedLeaves,Leaf.put]

/-- Same-label comparison against any dominating shadow old pair;
no independence and no validity of retained data are assumed. -/
theorem compare_hop (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (D : DataClaim) (u v : At Sheet) (hs : D.source=u) (hd : D.destination=some v)
    (hk : D.kind=.hop) (ne : u≠v)
    (sel : D∈orderedData g (reserved (round g raw).prep))
    (a b : Bool) (hu : occupied (view raw u)=true → a=true)
    (hv : occupied (view raw v)=true → b=true) :
    (occupied (post g raw u)=true → (a && b)=true) ∧
    (occupied (post g raw v)=true → (a || b)=true) := by
  have h := local_hop (view raw u) (view raw v) (retains g v)
  constructor
  · intro E
    unfold post at E
    rw [sender_exact g raw u v D hs hd hk sel ne] at E
    have D' := Bool.and_eq_true_iff.mp (h.1 E)
    exact Bool.and_eq_true_iff.mpr ⟨hu D'.1,hv D'.2⟩
  · intro E
    unfold post at E
    rw [BStarLongCopyFence.receiver_exact g raw u v D hs hd hk sel ne] at E
    rcases Bool.or_eq_true_iff.mp (h.2 E) with H|H
    · exact Bool.or_eq_true_iff.mpr (.inl (hu H))
    · exact Bool.or_eq_true_iff.mpr (.inr (hv H))

theorem compare_end (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (s : At Sheet)
    (sel : ending s∈orderedData g (reserved (round g raw).prep)) :
    occupied (post g raw s)=false := by
  rw [terminal_exact g raw s sel]
  by_cases E : (view raw s).mobile=.empty <;>
    simp [occupied,endEffects,E,typedLeaves,Leaf.put]

/-- The occupancy comparison is a statement about the joined pair,
not only about a pre-join lane patch. -/
theorem joined_compare_hop (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (D : DataClaim) (u v : At Sheet) (hs : D.source=u) (hd : D.destination=some v)
    (hk : D.kind=.hop) (ne : u≠v) (a b : Bool) :
    let g := Pair.map (longGeometry B) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair B x)
    D∈orderedData g (reserved (round g raw).prep) →
    (occupied (view raw u)=true → a=true) →
    (occupied (view raw v)=true → b=true) →
    (occupied (view y u)=true → (a && b)=true) ∧
      (occupied (view y v)=true → (a || b)=true) := by
  dsimp only
  intro sel hu hv
  erw [BStarClearanceMobileJoined.joined_view _ _ _ _ _ _ _ _ _ hp x]
  exact compare_hop _ _ D u v hs hd hk ne sel a b hu hv

theorem joined_compare_end (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (s : At Sheet) :
    let g := Pair.map (longGeometry B) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair B x)
    ending s∈orderedData g (reserved (round g raw).prep) →
    occupied (view y s)=false := by
  dsimp only
  intro sel
  erw [BStarClearanceMobileJoined.joined_view _ _ _ _ _ _ _ _ _ hp x]
  exact compare_end _ _ s sel

/-- The real ring mark reads the same old two cells and has the
same two lane outputs. The nonaliasing premise excludes n=1. -/
theorem ring_view (x : X) (e : Fin n) (he : e≠rightNeighbor e) :
    let y := AllSizeS1Geometry.step B x e
    view ((y e).long,(y (rightNeighbor e)).long) =
      post (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) := by
  dsimp only
  let y := AllSizeS1Geometry.step B x e
  have pair : (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e))) :
      Pair (BitVec LW)) = ((y e).long,(y (rightNeighbor e)).long) := by
    apply Prod.ext
    · simp [y,AllSizeS1Geometry.step,Pair.map] <;> rfl
    · simp [y,AllSizeS1Geometry.step,Pair.map,Ne.symm he] <;> rfl
  have Q := BStarClearanceMobileJoined.joined_view _ _ _ _ _ _ _ _ _ hp
    (x e,x (rightNeighbor e))
  change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e))))=
    post (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) at Q
  rwa [pair] at Q

/-- One actual physical mark of a generated opcode-11 owner couples
its nominal hop to the same hop of open exclusion. -/
theorem ring_owner_hop {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (pc11 : pc (play x w) (S.getD 0 fall).1=11)
    (e : Fin n) (D : DataClaim) (v : At Sheet)
    (nom : D∈orderedData (oldPair B (play x w) e) [])
    (own : dataOwner (oldH6 B base) (site e D.source.side) D.source.occurrence=o.val)
    (hd : D.destination=some v) (hk : D.kind=.hop) (ne : D.source≠v) (a b : Bool) :
    let q := play x w
    let y := AllSizeS1Geometry.step B q e
    let old := view ((q e).long,(q (rightNeighbor e)).long)
    let nxt := view ((y e).long,(y (rightNeighbor e)).long)
    (occupied (old D.source)=true → a=true) →
    (occupied (old v)=true → b=true) →
    (occupied (nxt D.source)=true → (a && b)=true) ∧
    (occupied (nxt v)=true → (a || b)=true) := by
  dsimp only
  intro hu hv
  rw [ring_view hp _ e (sep e)]
  apply compare_hop _ _ D D.source v rfl hd hk ne _ a b hu hv
  exact owner_nomination_selected hp chart sep hist now layout pc11 e D nom own

/-- Terminal deletion occurs on the very same raw mark; an owner
cannot suppress it with a preparation reservation while on FENCE. -/
theorem ring_owner_end {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (pc11 : pc (play x w) (S.getD 0 fall).1=11)
    (e : Fin n) (s : At Sheet)
    (nom : ending s∈orderedData (oldPair B (play x w) e) [])
    (own : dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val) :
    let q := play x w
    let y := AllSizeS1Geometry.step B q e
    occupied (view ((y e).long,(y (rightNeighbor e)).long) s)=false := by
  dsimp only
  rw [ring_view hp _ e (sep e)]
  apply compare_end
  exact owner_nomination_selected hp chart sep hist now layout pc11 e (ending s) nom own

/-- If no nominal claim touches an owned lane, its full typed
view stays fixed under the selected physical mark. -/
theorem ring_owner_quiet {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (pc11 : pc (play x w) (S.getD 0 fall).1=11)
    (e : Fin n) (s : At Sheet)
    (own : dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val)
    (quiet : ∀ D∈orderedData (oldPair B (play x w) e) [], s∉D.slots) :
    let q := play x w
    let y := AllSizeS1Geometry.step B q e
    view ((y e).long,(y (rightNeighbor e)).long) s =
      view ((q e).long,(q (rightNeighbor e)).long) s := by
  dsimp only
  rw [ring_view hp _ e (sep e)]
  apply BStarClearanceMobileWeak.quiet_lane
  · exact no_reservation hp chart sep hist now layout pc11 e s own
  · intro D h
    rw [BStarClearancePrepOwner.orderedData_filter] at h
    exact quiet D (List.mem_filter.mp h).1

end L4.BStarFenceOccupancy

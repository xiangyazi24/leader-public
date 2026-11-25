import Leader.L4.BStarFreshNumericTrace
import Leader.L4.BStarFenceOccupancy
import Leader.L4.BStarCopyPaddingFrame
import Leader.L4.BStarCopyFenceSaturation

/-! The active drained data footprint of a late owner is sealed by
the literal old data ownership law, including wrapping seam edges. -/
namespace L4.BStarFreshNumericOperands
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarLongCommand BStarLongPrep BStarLongCommandData BStarLongFiberOwner BStarH6WordChart
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedBandScan BStarClearanceDataChart BStarLongFixedRouting
open BStarCopyFenceSaturation BStarFreshNumericTrace BStarFreshNumeric

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Active late-owner sheets. An inactive old packed lane need not be
empty, cannot contribute a literal incoming hop, and is not used by LOAD. -/
def ActiveOwner (base : X) (o : Int) (i : Fin n) (sh : Sheet) : Prop :=
  dataOwner (oldH6 B base) i sh=o ∧ activeSheet (longGeometry B (base i)) sh=true

private theorem endpoint_active (g : Pair LongGeometry) (rs : List (At Sheet))
    (c : DataClaim) (s : At Sheet) (M : c∈orderedData g rs) (S : s∈c.slots) :
    activeSheet (geometry g s.side) s.occurrence=true := by
  cases h : s.occurrence
  · rfl
  · exact BStarCopyPaddingFrame.data_active _ _ _ _ M S (Or.inl h)
  · exact BStarCopyPaddingFrame.data_active _ _ _ _ M S (Or.inr h)
  · rfl

/-- One exact physical late mark has no preparation reservation in
this region, and every incoming real hop still starts in the region. -/
theorem late_region {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle w m)
    (layout : ∀ i,Layout B base i=Layout B (play origin w) i)
    (late : 11≤pc (play origin w) (S.getD 0 fall).1) (e : Fin n) :
    FrozenRegion hp (ActiveOwner hp base o.val) (play origin w) e := by
  let y := play origin w
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  let rs := reserved (round g raw).prep
  refine ⟨?_,?_⟩
  · intro a own
    apply no_prep_late g raw a _ late
    intro offer win eq
    exact BStarCopyGateAuthority.winning_prep_pc hp chart sep hist
      (BStarGeneratedTapeCuts.at_end hp hist) layout e offer (eq.symm ▸ own.1) win
  · intro d M v V land
    have hd := reserved_hop_owner B y e rs d v M land
    have heads : oldH6 B y=oldH6 B base :=
      funext fun i => (congrArg Prod.fst (layout i)).symm
    rw [heads] at hd
    refine ⟨hd.trans V.1,?_⟩
    have active := endpoint_active g rs d d.source M (by simp [Claim.slots])
    have G (s : Side) : geometry g s=longGeometry B (y (site e s)) := by cases s <;> rfl
    rw [G] at active
    have E (i : Fin n) (sh : Sheet) :
        activeSheet (longGeometry B (base i)) sh=activeSheet (longGeometry B (y i)) sh := by
      have J := congrArg (fun v : Bool × Bool × Bool => v.2.1) (layout i)
      cases sh
      · rfl
      · exact J
      · exact J
      · rfl
    exact (E _ _).trans active

/-- K1 visits and both retained sheets have the same exact modular
owner, even across the physical ring seam. -/
theorem operand_owner {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    {k : Nat} (hk : k≤len) (one : (S.getD k fall).2.val=1)
    (inside : (longGeometry B (base (S.getD k fall).1)).inside=true) :
    ActiveOwner hp base o.val (S.getD k fall).1 .ld ∧
      ActiveOwner hp base o.val (S.getD k fall).1 .rd := by
  have lh := chart.length
  have M : S.getD k fall∈S := by
    rw [←List.getElem_eq_getD (h:=show k<S.length by omega)]
    exact List.getElem_mem _
  have O := (chart.entries _ M).2
  have E : (S.getD k fall).2=(1:Fin 11) := Fin.ext one
  rw [E] at O
  exact ⟨⟨O,inside⟩,⟨O,rfl⟩⟩

/-- Exact post-FENCE seed and late generated chart imply retained
operand tags at every old mark of the *same* numeric tape. -/
theorem operand_tape {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w : List (Fin n)) (m : Mode)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle (lead++w) m)
    (layout : ∀ u v,w=u++v → ∀ i,Layout B base i=Layout B (play (play origin lead) u) i)
    (late : ∀ u v,w=u++v → 11≤pc (play (play origin lead) u) (S.getD 0 fall).1)
    (drained : ∀ i sh,ActiveOwner hp base o.val i sh →
      (readLane (Sheet.index sh) ((play origin lead) i).long).mobile=.empty)
    (retained : ∀ i sh,ActiveOwner hp base o.val i sh → (sh=.ld ∨ sh=.rd) →
      ∃ d,(readLane (Sheet.index sh) ((play origin lead) i).long).retained=.data d) :
    OperandTape hp (fun j => S.getD j fall) len (play origin lead) w := by
  let y := play origin lead
  let P := ActiveOwner hp base o.val
  have frame (u v : List (Fin n)) (E : w=u++v) :
      ∀ i sh,P i sh → readLane (Sheet.index sh) (play y u i).long=
        readLane (Sheet.index sh) (y i).long := by
    apply drained_word_frame hp P y u sep drained
    intro a e b A
    have Eq : w=a++(e::b++v) := by rw [E,A,List.append_assoc,List.cons_append]
    have W : lead++w=(lead++a)++(e::b++v) := by rw [Eq,List.append_assoc]
    obtain ⟨mode,pre,_⟩ := BStarGeneratedTapeCuts.split hp (lead++a) (e::b++v) (W ▸ hist)
    have playEq : play origin (lead++a)=play y a := BStarResetSchedule.run_append _ _ _ _
    have F := late_region hp chart sep pre (fun i => playEq.symm ▸ layout a (e::b++v) Eq i)
      (playEq.symm ▸ late a (e::b++v) Eq) e
    rw [playEq] at F
    exact F
  dsimp only [OperandTape]
  intro u e v eq k hk one inside
  have tilt := layout u (e::v) eq (S.getD k fall).1
  have baseInside : (longGeometry B (base (S.getD k fall).1)).inside=true :=
    (congrArg (fun z : Bool × Bool × Bool => z.2.1) tilt).trans inside
  obtain ⟨left,right⟩ := operand_owner hp chart hk one baseInside
  obtain ⟨l,L⟩ := retained _ _ left (.inl rfl)
  obtain ⟨r,R⟩ := retained _ _ right (.inr rfl)
  refine ⟨⟨l,?_⟩,r,?_⟩
  · exact (congrArg Lane.retained (frame u (e::v) eq _ .ld left)).trans L
  · exact (congrArg Lane.retained (frame u (e::v) eq _ .rd right)).trans R

end L4.BStarFreshNumericOperands

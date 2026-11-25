import Leader.L4.BStarCopyActiveVacancy
import Leader.L4.BStarCopyPreIssueEmpty
import Leader.L4.BStarClearanceMobileOwner

namespace L4.BStarCopyActiveEmpty
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarLongCommand
open BStarLongFiberOwner BStarH6WordChart BStarClearanceDataChart
open BStarCopyOperand BStarClearanceMobileOwner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "P" => production k₁ k₂ t₂ J₁ J₂ r c p c₁
local notation "X" => Fin n → LargeSite P
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarCopyEntryGates BStarCopyActiveVacancy BStarLongFixedRouting BStarLongLiteral
private theorem fold_field (T : Lane → Prop) (A : List (At Sheet × Leaf))
    (s : At Sheet) (old : At Sheet → Lane)
    (start : T (old s))
    (safe : ∀ a, (s,a)∈A → ∀ L, T L → T (a.put L)) :
    T ((A.foldl update old) s) := by
  induction A generalizing old with
  | nil => exact start
  | cons a A ih =>
    apply ih
    · unfold update
      split
      · rename_i E
        apply safe a.2 _ _ start
        rcases a with ⟨z,t⟩
        change s=z at E
        subst z
        exact List.mem_cons_self
      · exact start
    · exact fun t m => safe t (List.mem_cons_of_mem _ m)

private theorem prep_no_mobile (old : At Sheet → Lane) (a : BStarLongPrep.Offer)
    (h : a.claim.op≠.inject) :
    ∀ l∈(selectedEffects old a).writes,noMobile l := by
  unfold selectedEffects
  cases t : a.claim.op <;> simp [t,effects,noMobile] at h ⊢


private theorem data_empty_no_effect (g : Pair LongGeometry) (old : At Sheet → Lane)
    (c : DataClaim) (E : (old c.source).mobile=.empty) :
    dataEffects g old c=[] := by
  rcases c with ⟨k,src,dst⟩
  cases k <;> cases dst <;> simp [dataEffects,endEffects,hopEffects,E]

private theorem same_slots (g : Pair LongGeometry) (m w : Int) (rs : List (At Sheet))
    (C : DataClaim) (h : C∈orderedData g rs) (a : At Sheet) (ha : a∈C.slots) :
    pairOwner m w g.2.axes.h6 dataDispl a=pairOwner m w g.2.axes.h6 dataDispl C.source := by
  cases D : C.destination with
  | none =>
    have E : a=C.source := by simpa [Claim.slots,D] using ha
    rw [E]
  | some b =>
    have E : a=C.source ∨ a=b := by simpa [Claim.slots,D] using ha
    rcases E with rfl|rfl
    · rfl
    · exact (data_owner g m w rs C a h D).symm

theorem pair_owner_active_empty (x : Pair (LargeSite P)) (m word own : Int) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    let key := pairOwner m word g.2.axes.h6 dataDispl
    (∀ a, activeSheet (geometry g a.side) a.occurrence=true → key a=own → (view raw a).mobile=.empty) →
    (∀ a∈(arbitration (round g raw).prep).1, key a.claim.lane=own → a.claim.op≠.inject) →
    ∀ a, activeSheet (geometry g a.side) a.occurrence=true → key a=own → (view (Pair.map LargeSite.long (largePair B x)) a).mobile=.empty := by
  dsimp only
  intro empty prep a active ownA
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp,
      BStarLongCommandData.round_transfer]
  apply fold_field (fun L => L.mobile=.empty) _ a _ (empty a active ownA)
  intro l h L H
  have Ok : noMobile l := by
    rcases List.mem_append.mp h with J|J
    · obtain ⟨p,win,E⟩ := List.mem_flatMap.mp J
      obtain ⟨t,mem,res⟩ := List.mem_map.mp E
      have hA : p.claim.lane=a := congrArg Prod.fst res
      have tEq : t=l := congrArg Prod.snd res
      subst t
      exact prep_no_mobile _ p (prep p win (hA.symm ▸ ownA)) l mem
    · obtain ⟨d,hD,hd⟩ := List.mem_flatMap.mp J
      have inSlots := data_lane_claim _ _ d a l hd
      have key := same_slots _ m word _ d hD a inSlots
      let g := Pair.map (longGeometry B) x
      let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
      have activeFrom : activeSheet (geometry g d.source.side) d.source.occurrence=true := by
        cases H : d.source.occurrence
        · rfl
        · exact BStarCopyPaddingFrame.data_active g _ d d.source hD (by simp [Claim.slots]) (.inl H)
        · exact BStarCopyPaddingFrame.data_active g _ d d.source hD (by simp [Claim.slots]) (.inr H)
        · rfl
      have E : (view raw d.source).mobile=.empty := empty d.source activeFrom (key.symm.trans ownA)
      have ex := data_empty_no_effect g (view raw) d E
      change (a,l)∈dataEffects g (view raw) d at hd
      rw [ex] at hd
      exact (List.not_mem_nil hd).elim
  cases l <;> simp_all [noMobile,Leaf.put]

theorem ring_active_empty (base x : X) (e : Fin n) (o : Int) (sep : e≠rightNeighbor e)
    (layout : ∀ i,Layout B base i=Layout B x i)
    (layoutNext : ∀ i,Layout B base i=Layout B (step x e) i)
    (empty : ActiveOwnerEmpty hp base x o) (no : NoOwnerInject hp base x e o) :
    ActiveOwnerEmpty hp base (step x e) o := by
  intro i sh act own
  have same : oldH6 B x=oldH6 B base := funext (fun i => (congrArg Prod.fst (layout i)).symm)
  have sameInside : (longGeometry B (x i)).inside=(longGeometry B (step x e i)).inside :=
    congrArg (fun t : Bool×Bool×Bool => t.2.1) ((layout i).symm.trans (layoutNext i))
  have actOld : activeSheet (longGeometry B (x i)) sh=true := by
    cases sh <;> first | rfl | exact sameInside.trans act
  have touch (s : Side) (E : site e s=i) :
      (readLane (Sheet.index sh) (step x e i).long).mobile=.empty := by
    subst i
    let h := oldH6 B x
    have key (a : At Sheet) :
        pairOwner (total h) (word h e) (oldPair B x e).2.axes.h6 dataDispl a=o ↔
        dataOwner (oldH6 B base) (site e a.side) a.occurrence=o := by
      change pairOwner (total h) (word h e) (h (rightNeighbor e)) dataDispl a=o ↔ _
      rw [←physical_pair_owner]
      change dataOwner (oldH6 B x) _ _ =o ↔ _
      rw [same]
    have q := pair_owner_active_empty hp (x e,x (rightNeighbor e)) (total h) (word h e) o
      (fun a Ha H => by obtain ⟨s,t⟩ := a; cases s <;> exact empty _ t Ha ((key _).mp H))
      (fun a m K => no a m ((key _).mp K)) ⟨s,sh⟩ (by cases s <;> exact actOld) ((key _).mpr own)
    cases s <;> simpa [view,site,lane,BStarTrace.lane,Pair.map,AllSizeS1Geometry.step,Ne.symm sep] using q
  by_cases l : i=e
  · exact touch .left l.symm
  · by_cases rr : i=rightNeighbor e
    · exact touch .right rr.symm
    · rw [show step x e i=x i from by simp [AllSizeS1Geometry.step,l,rr]]
      exact empty i sh actOld own

theorem active_empty_word (base x : X) (w : List (Fin n)) (o : Int)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (empty : ActiveOwnerEmpty hp base x o)
    (same : ∀ pre tail, w=pre++tail → ∀ i,Layout B base i=Layout B (play x pre) i)
    (no : ∀ pre e post, w=pre++e::post → NoOwnerInject hp base (play x pre) e o) :
    ActiveOwnerEmpty hp base (play x w) o := by
  induction w generalizing x with
  | nil => exact empty
  | cons e w ih =>
    exact ih (step x e)
      (ring_active_empty hp base x e o (sep e) (same [] _ rfl) (same [e] w rfl) empty (no [] e w rfl))
      (fun a b E => same (e::a) b (congrArg (List.cons e) E))
      (fun a b c E => no (e::a) b c (congrArg (List.cons e) E))


open BStarResetChartTouch BStarAcquireLiteralChain BStarAcquireVisitOrder
open BStarResetMarkAdapter BStarGeneratedOwner BStarSeparatingRail

open BStarLongDoor BStarClearanceSource

/-- Actual clean launch mark cannot introduce a mobile into the own
vacant rail from another owner, even with arbitrary foreign activity. -/
theorem issue_keeps_active_empty {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (layout : ∀ r, BStarLongFixedRouting.Layout B base r=BStarLongFixedRouting.Layout B x r)
    (layoutNext : ∀ r, Layout B base r=Layout B (step x e) r)
    (idle : Current hp base (fun k => S.getD k fall) len x .idle)
    (empty : ActiveOwnerEmpty hp base x o.val) :
    ActiveOwnerEmpty hp base (step x e) o.val := by
  apply ring_active_empty hp base x e o.val sep layout layoutNext empty
  intro a win own
  have A := BStarCopyOwnedFrozen.safe_idle hp chart layout e (site e a.claim.lane.side) a.claim.lane.occurrence own idle.2
  have Eq : a.claim.lane=⟨a.claim.lane.side,a.claim.lane.occurrence⟩ := by cases a.claim.lane; rfl
  rcases A a.claim.lane.side rfl a win Eq with S|S|S <;> rw [S] <;> decide


#print axioms issue_keeps_active_empty
#print axioms active_empty_word
end L4.BStarCopyActiveEmpty

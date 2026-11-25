import Leader.L4.BStarSeparatorIdleClass
import Leader.L4.BStarSeparatorTags
import Leader.L4.BStarClearanceSource

namespace L4.NonheldPhysical
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken BStarLongTransport
open BStarLongCommand BStarLongLayout BStarLongDoor BStarLongEvents BStarLongLiteral BStarLongCommandData
open BStarResetQuiet BStarResetQuietTable BStarSeparatorIdleClass BStarSeparatorControl
open BStarClearanceSource BStarH6WordChart

def sourceLink (g : Pair LongGeometry) : CommandClaim :=
  link (L 0) (R (if g.2.axes.h6 then 1 else 0))

theorem source_link_mem (g : Pair LongGeometry) : sourceLink g∈orderedCommands g := by
  rcases g with ⟨x,y⟩
  change link (L 0) (R (if y.axes.h6 then 1 else 0)) ∈
    select Claim.slots [] (offers commandKey (commandClaims (x,y)))
  unfold commandClaims ends
  simp only
  generalize y.axes.h6=h
  generalize x.inside=i
  generalize y.inside=j
  generalize x.last=l
  cases h <;> cases i <;> cases j <;> cases l <;> decide +kernel

def QuietED (t : Token) : Prop := t=.empty ∨ ∃ q,t=.reply q

private theorem actual_hold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (hc : c∈orderedCommands g) (hv : gatedAt g x c=.hold) :
    (c,.hold)∈actualOffers g x := by
  have C := (gated_mem g x c _).mpr ⟨hc,hv.symm⟩
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round
  refine List.mem_map.mpr ⟨(c,.hold),List.mem_map.mpr ⟨_,C,rfl⟩,?_⟩
  unfold BStarLongGrant.update
  dsimp only
  split <;> rfl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- The old left K0 is not necessarily conserved bytewise: an old
right reply can replace it by a reply. It cannot become Trail or F. -/
theorem joined_left_ed (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (old : QuietED (atSite x.1.long 0)) :
    QuietED (atSite (largePair B x).1.long 0) := by
  let g := Pair.map (longGeometry B) x
  let raw := Pair.map LargeSite.long x
  let K := sourceLink g
  let dst : AtK := R (if g.2.axes.h6 then 1 else 0)
  have loc : K.source=L 0 := rfl
  have D : K.destination=some dst := rfl
  have mem : K∈orderedCommands g := source_link_mem g
  have read : QuietED (readK raw K.source) := old
  have Bnd : QuietED (bound g (readK raw) K.source) := by
    rcases read with E|⟨q,E⟩
    · left; unfold bound; rw [E]; rfl
    · right; unfold bound; rw [E]; exact bound_D _ _ _
  have route : gatedAt g raw K = match bound g (readK raw) dst with
      | .reply q => .reverse (.reply q)
      | _ => .hold := by
    unfold gatedAt classifyOld
    change checkOffer g (BStarLongPrep.view raw) (K,classify K _
      (bound g (readK raw) K.source) ((K.destination.map (bound g (readK raw))).getD .empty))=_
    rw [D]
    have LK : K.kind=.link := rfl
    rcases Bnd with E|⟨q,E⟩
    all_goals rw [E]; cases T : bound g (readK raw) dst <;> simp [LK,classify,checkOffer,T]
  cases R : bound g (readK raw) dst with
  | reply q =>
    have chosen : (K,.reverse (.reply q))∈gated g raw :=
      (gated_mem g raw K _).mpr ⟨mem,by rw [route,R]⟩
    have ne := (BStarAcquireReturn.link_shape g K dst mem D).1
    have out := BStarAcquireReturn.reverse_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x K dst (.reply q) D ne
      (by intro eq _; rw [loc] at eq; contradiction) chosen
    exact .inr ⟨q,out⟩
  | empty | trail | forward =>
    have hold := actual_hold g raw K mem (by rw [route,R])
    have Q := hold_avoids g raw K hold (L 0) (by rw [←loc]; simp [Claim.slots])
    have nd : L 0∉discarded g := by
      unfold discarded
      split <;> split <;> decide
    have cl := joined_idle_cls k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x (L 0) nd Q
      (safe_nonright g raw _ (by decide))
    have frame := preserves cl
    rcases old with E|⟨q,E⟩
    · exact .inl (frame.2.1 E)
    · exact .inr (frame.2.2.2 ⟨q,E⟩)

#print axioms joined_left_ed

open BStarAcquireWaitControl

/-- Any actual non-door mark preserves nonheld status at an old H6
source. The only incident non-door case is its old outgoing pair. -/
theorem no_reentry (x : X) (root e : Fin n)
    (head : oldH6 B x root=true) (away : e≠RearTrace.predecessor root)
    (old : ¬Held (x root).long) : ¬Held (step x e root).long := by
  have R : root≠rightNeighbor e := fun eq=>away
    ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor eq.symm))
  by_cases E : root=e
  · subst e
    intro H
    simp only [AllSizeS1Geometry.step,if_true] at H
    have C := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x root,x (rightNeighbor root)) head
    have V := (BStarResetWaitRing.valid_of_control_eq _ _ C).symm.trans H.1
    have P := (congrArg (fun s : BitVec 2 × BitVec 9=>s.1.toNat) C).symm.trans H.2.1
    have quiet : QuietED (atSite (x root).long 0) := by
      cases K : atSite (x root).long 0 with
      | empty => exact .inl rfl
      | reply q => exact .inr ⟨q,rfl⟩
      | trail => exact (old ⟨V,P,.inl K⟩).elim
      | forward q => exact (old ⟨V,P,.inr ⟨q,K⟩⟩).elim
    have frame := joined_left_ed hp (x root,x (rightNeighbor root)) quiet
    rcases H.2.2 with trail|⟨q,F⟩
    · rcases frame with K|⟨a,K⟩
      · exact Token.noConfusion (trail.symm.trans K)
      · exact Token.noConfusion (trail.symm.trans K)
    · rcases frame with K|⟨a,K⟩
      · exact Token.noConfusion (F.symm.trans K)
      · exact Token.noConfusion (F.symm.trans K)
  · simpa only [AllSizeS1Geometry.step,if_neg E,if_neg R] using old

#print axioms no_reentry
end L4.NonheldPhysical

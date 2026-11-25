import Leader.L4.BStarNativeEndCache
import Leader.L4.BStarClearanceSettled

namespace L4.BStarNativeOffsetTrace
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarH6Ordinal
open BStarLongClaims BStarLongLiteral BStarLongEvents BStarLongTransport
open BStarNumericChronology BStarNumericConsecutive BStarLongFixedRouting BStarResetMarkAdapter BStarAcquireVisitOrder
open BStarClearanceOffset

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

theorem eff_eq {h : Fin n→Bool} (x : X) (fixed : oldH6 B x=h) (i : Fin n) :
    BStarPhysicalDigitSem.off (longGeometry B (x i))=eff h x i := by
  change (if oldH6 B x i then 0 else min 5 (offsetL (x i).long))=_
  rw [fixed]
  exact congrArg (fun z : Nat => if h i then 0 else z) (Nat.min_eq_right (Nat.min_le_left _ _))

/-- The finite causal witness for a site is the clockwise chain of up to
five predecessor marks in chronological order as a subsequence of the
actual tape. No stop, reset, or absence of competing marks is assumed. -/
inductive Clocked (h : Fin n→Bool) : Nat → Fin n → List (Fin n) → Prop
  | zero (i w) : Clocked h 0 i w
  | header (k i w) : h i=true → Clocked h k i w
  | service {k w} (e : Fin n) : Clocked h k e w →
      Clocked h (k+1) (rightNeighbor e) (w++[e])
  | wait {k i w} (e : Fin n) : e≠RearTrace.predecessor i →
      Clocked h k i w → Clocked h k i (w++[e])

/-- A later unselected-address mark does not disturb a certificate;
a later selected-address mark needs the predecessor certificate on its
own old cut. This is deliberately conservative for arbitrary suffixes. -/
theorem clocked_sound (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (x : X) {k i w}
    (T : Clocked h k i w) (hk : k≤5)
    (same : ∀ u v,w=u++v → oldH6 B (run x u)=h) :
    min k (eff h (run x w) i)=min k (ordinal h hh i) := by
  induction T with
  | zero => simp
  | header k i w H =>
    simp [eff,H,(ordinal_zero h hh i).mpr H]
  | @service k w e T ih =>
    have W : run x (w++[e])=step (run x w) e := by
      rw [BStarResetSchedule.run_append]; rfl
    have H := ih (by omega) (fun a b E => same a (b++[e]) (by rw [E,List.append_assoc]))
    rw [W,responder hp h (run x w) e (sep e)
      (fun j => congrFun (same w [e] rfl) j),ordinal_right]
    cases E : h (rightNeighbor e)
    · simp only [Bool.false_eq_true,if_false]
      have bound : eff h (run x w) e≤5 := by
        unfold eff; split
        · decide
        · exact Nat.min_le_left _ _
      omega
    · rfl
  | @wait k i w e ne T ih =>
    have W : run x (w++[e])=step (run x w) e := by
      rw [BStarResetSchedule.run_append]; rfl
    have N : i≠rightNeighbor e := fun E => ne (by rw [E,RearTrace.predecessor_right])
    rw [W,elsewhere hp h (run x w) e i (BStarClearanceOffsetMask.leftFrame hp _ _) N]
    exact ih (by omega) (fun a b E => same a (b++[e]) (by rw [E,List.append_assoc]))

theorem closed_word (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (x : X) (w : List (Fin n))
    (C : correct h hh 5 x)
    (same : ∀ u v,w=u++v → oldH6 B (run x u)=h) :
    correct h hh 5 (run x w) := by
  induction w generalizing x with
  | nil => exact C
  | cons e w ih =>
    have hs := same [] (e::w) rfl
    have post := stable hp h hh x e (sep e) (congrFun hs)
      (BStarClearanceOffsetMask.leftFrame hp x e) C
    exact ih (step x e) post (fun u v E => same (e::u) v (congrArg (List.cons e) E))

/-- For every actual old significant record of the numeric itinerary,
the installed (not merely newly refreshed) offset is exactly the
clipped immutable ordinal. Global correctness needs to be established
once, before the itinerary; all later raw scheduler marks are allowed. -/
theorem aligned_offset {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {slot : Nat→Pos n} {len op k l : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base slot len op x k w l ds)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (settled : correct (oldH6 B base) hh 5 x)
    (same : ∀ u v,w=u++v → oldH6 B (run x u)=oldH6 B base)
    (d : D) (M : d∈ds.filter (significant hp base slot)) :
    BStarPhysicalDigitSem.off (geom hp d)=min 5 (oldOrdinal B base hh d.mark) := by
  obtain ⟨dm,sm⟩ := List.mem_filter.mp M
  obtain ⟨pre,post,W,_,old⟩ := Aligned.prefix_to hp A d dm
  have C := closed_word hp (oldH6 B base) hh sep x pre settled
    (fun u v E => same u (v++d.mark::post) (by rw [W,E,List.append_assoc]))
  have hi := C d.mark
  rw [old] at hi
  have bound : eff (oldH6 B base) d.old d.mark≤5 := by
    unfold eff; split
    · decide
    · exact Nat.min_le_left _ _
  rw [Nat.min_eq_right bound] at hi
  obtain ⟨V,L,_⟩ := Aligned.record_facts hp A d dm
  have one := (Aligned.record_significant hp A d dm sm).1
  have main : d.claim∈orderedCommands (oldPair B d.old d.mark) := by
    rw [←actualOffers_claims _ ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)]
    exact List.mem_map.mpr ⟨_,V.1,rfl⟩
  have axis : d.claim.source.side=.left := by rw [center_of _ _ main one]; rfl
  have fixed : oldH6 B d.old=oldH6 B base :=
    funext fun i => (congrArg Prod.fst (L i)).symm
  unfold geom
  rw [axis]
  exact (eff_eq hp d.old fixed d.mark).trans hi

#print axioms clocked_sound
#print axioms aligned_offset
end L4.BStarNativeOffsetTrace

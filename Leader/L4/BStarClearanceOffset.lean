import Leader.L4.BStarH6Ordinal
import Leader.L4.AllSizeS1Geometry
import Leader.L4.RearGeometry

/-! Repair and closure of the effective saturated long offsets.
This complements the lower fixed H6/IN/LAST layout. -/
namespace L4.BStarClearanceOffset
open AllSizeProtocol BStarTrace BStarLongWork BStarH6Ordinal BStarH6WordChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
abbrev X (k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat) :=
  Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def eff {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
    (h : Fin n → Bool) (x : X k₁ k₂ t₂ J₁ J₂ r c p c₁ n) (i : Fin n) : Nat :=
  if h i then 0 else offsetL (x i).long

def correct {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
    (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (k : Nat) (x : X k₁ k₂ t₂ J₁ J₂ r c p c₁ n) : Prop :=
  ∀ i, min k (eff h x i)=min k (ordinal h hh i)

private theorem sat_succ (j : Nat) : min 5 (min 5 j + 1)=min 5 (j+1) := by omega

/-- Header offsets are effective zero even before raw repair; no
body is level zero. -/
theorem zero_correct (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (x : X k₁ k₂ t₂ J₁ J₂ r c p c₁ n) : correct h hh 0 x := by
  intro i
  simp

variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "S" => AllSizeS1Geometry.step B
local notation "R" => X k₁ k₂ t₂ J₁ J₂ r c p c₁ n

/-- The only not-yet-discharged packed frame in this repair: the
initiator's effective offset is not changed by the literal long
work patch (the scratch-only left row writes neither offset bit). -/
def LeftFrame (x : R) (e : Fin n) : Prop :=
  offsetL (largePair B (x e,x (rightNeighbor e))).1.long = offsetL (x e).long

/-- The actual joined responder computes the old-neighbor update.
The outer repair and stale right offset do not interfere. -/
theorem responder (h : Fin n → Bool) (x : R) (e : Fin n) (he : e≠rightNeighbor e)
    (same : ∀ i, oldH6 B x i=h i) :
    eff h (S x e) (rightNeighbor e) =
      if h (rightNeighbor e) then 0 else min 5 (eff h x e+1) := by
  have E := (BStarLongSector.joined_offsets k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e))).2
  change offsetL (largePair B (x e,x (rightNeighbor e))).2.long =
    nextOffset (oldPair B x e) at E
  rw [show nextOffset (oldPair B x e) =
    (if oldH6 B x (rightNeighbor e) then 0 else
       min 5 ((if oldH6 B x e then 0 else offsetL (x e).long)+1)) from by
      unfold nextOffset
      change (if oldH6 B x (rightNeighbor e) then 0 else
        min 5 ((if oldH6 B x e then 0 else min 5 (offsetL (x e).long))+1)) = _
      have bound : offsetL (x e).long ≤ 5 := Nat.min_le_left _ _
      rw [Nat.min_eq_right bound], same,same] at E
  simp only [eff,AllSizeS1Geometry.step,if_neg (Ne.symm he),if_true]
  cases H : h (rightNeighbor e)
  · exact E.trans (by simp [H])
  · rfl

private theorem responders_correct (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (x : R) (e : Fin n) (he : e≠rightNeighbor e)
    (same : ∀ i, oldH6 B x i=h i)
    (H : eff h x e = min 5 (ordinal h hh e)) :
    eff h (S x e) (rightNeighbor e)=min 5 (ordinal h hh (rightNeighbor e)) := by
  rw [responder hp h x e he same,H,ordinal_right]
  cases I : h (rightNeighbor e) <;> simp [sat_succ]

/-- If a mark does not write an address as responder, its effective
offset is unchanged. This exposes exactly the joined left frame. -/
theorem elsewhere (h : Fin n → Bool) (x : R) (e i : Fin n)
    (F : LeftFrame hp x e) (ne : i≠rightNeighbor e) :
    eff h (S x e) i=eff h x i := by
  by_cases H : i=e
  · subst i
    have q := F
    unfold LeftFrame at q
    simp [eff,AllSizeS1Geometry.step,q]
  · simp [eff,AllSizeS1Geometry.step,H,ne]

/-- A mark advances the responder's certified precision by one;
every previously certified slot keeps its precision. Clipping both
sides to k gives the lower bound needed at the saturation boundary. -/
theorem mark (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (x : R) (e : Fin n) (he : e≠rightNeighbor e)
    (same : ∀ i, oldH6 B x i=h i) (F : LeftFrame hp x e)
    (k : Nat) (hk : k<5) (C : correct h hh k x) :
    correct h hh k (S x e) ∧
    (∀ i, (i=rightNeighbor e ∨ min (k+1) (eff h x i)=min (k+1) (ordinal h hh i)) →
      min (k+1) (eff h (S x e) i)=min (k+1) (ordinal h hh i)) := by
  have A : ∀ i, (i=rightNeighbor e ∨ min (k+1) (eff h x i)=min (k+1) (ordinal h hh i)) →
      min (k+1) (eff h (S x e) i)=min (k+1) (ordinal h hh i) := by
    intro i old
    by_cases I : i=rightNeighbor e
    · subst i
      rw [responder hp h x e he same,ordinal_right]
      cases T : h (rightNeighbor e)
      · simp only [Bool.false_eq_true,if_false]
        have H := C e
        omega
      · rfl
    · rw [elsewhere hp h x e i F I]
      exact old.resolve_left I
  refine ⟨?_,A⟩
  intro i
  by_cases I : i=rightNeighbor e
  · have H := A i (.inl I)
    omega
  · rw [elsewhere hp h x e i F I]
    exact C i

/-- Run the actual physical marks. -/
def run (x : R) (w : List (Fin n)) : R := w.foldl S x

/-- Under the fixed-header and initiator-frame conditions on the
invariant lower fiber, one complete (not necessarily ordered)
cover raises precision by one. -/
theorem cover (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (he : ∀ e : Fin n, e≠rightNeighbor e)
    (Good : R → Prop) (closed : ∀ x e, Good x → Good (S x e))
    (same : ∀ x, Good x → ∀ i, oldH6 B x i=h i)
    (frame : ∀ x e, Good x → LeftFrame hp x e)
    (k : Nat) (hk : k<5) (x : R) (w : List (Fin n))
    (gx : Good x) (C : correct h hh k x) :
    Good (run hp x w) ∧ correct h hh k (run hp x w) ∧
    ∀ i, (∃ e∈w, rightNeighbor e=i) ∨ min (k+1) (eff h x i)=min (k+1) (ordinal h hh i) →
      min (k+1) (eff h (run hp x w) i)=min (k+1) (ordinal h hh i) := by
  induction w generalizing x with
  | nil => exact ⟨gx,C,by simp [run]⟩
  | cons e w ih =>
    have P := mark hp h hh x e (he e) (same x gx) (frame x e gx) k hk C
    obtain ⟨a,b,T⟩ := ih (S x e) (closed x e gx) P.1
    refine ⟨a,b,?_⟩
    intro i H
    apply T i
    rcases H with ⟨v,hv,V⟩|M
    · rcases List.mem_cons.mp hv with rfl|E
      · exact .inr (P.2 i (.inl V.symm))
      · exact .inl ⟨v,E,V⟩
    · exact .inr (P.2 i (.inr M))

/-- Every certified fully saturated chart remains correct on the
same fixed lower fiber. -/
theorem stable (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (x : R) (e : Fin n) (he : e≠rightNeighbor e)
    (same : ∀ i, oldH6 B x i=h i) (F : LeftFrame hp x e)
    (H : correct h hh 5 x) : correct h hh 5 (S x e) := by
  have H' : correct h hh 4 x := by
    intro i
    have bound := H i
    omega
  have M := mark hp h hh x e he same F 4 (by decide) H'
  intro i
  exact M.2 i (.inr (H i))

/-- Five repetitions of an all-edge cover repair arbitrary long
offsets; the certificate does not assume the old raw offset was
already accurate at entry. -/
theorem five_covers (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (he : ∀ e : Fin n, e≠rightNeighbor e)
    (Good : R → Prop) (closed : ∀ x e, Good x → Good (S x e))
    (same : ∀ x, Good x → ∀ i, oldH6 B x i=h i)
    (frame : ∀ x e, Good x → LeftFrame hp x e)
    (x : R) (gx : Good x) (w : List (Fin n)) (full : ∀ e, e∈w) :
    Good ((List.replicate 5 w).foldl (run hp) x) ∧
      correct h hh 5 ((List.replicate 5 w).foldl (run hp) x) := by
  have aux : ∀ k≤5, Good ((List.replicate k w).foldl (run hp) x) ∧
      correct h hh k ((List.replicate k w).foldl (run hp) x) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨gx,zero_correct h hh x⟩
    | succ k ih =>
      intro hk
      obtain ⟨g,C⟩ := ih (by omega)
      let y := (List.replicate k w).foldl (run hp) x
      have P := cover hp h hh he Good closed same frame k (by omega) y w g C
      have E : List.replicate (k+1) w = List.replicate k w ++ [w] := by
        exact List.replicate_succ'
      rw [E,List.foldl_append,List.foldl_cons,List.foldl_nil]
      refine ⟨P.1,fun i => P.2.2 i (.inl ⟨RearTrace.predecessor i,full _,
        RearTrace.right_predecessor i⟩)⟩
  exact aux 5 (Nat.le_refl _)

/-- At a certified point the physical gate is evaluated at its
fixed ordinal, independent of the token bytes, old inputs, and
raw high bits of the saturated offset. -/
theorem gate_at_ordinal (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (x : R) (same : ∀ i,oldH6 B x i=h i) (C : correct h hh 5 x)
    (i : Fin n) (op : Nat) (j : Fin 11) :
    BStarLongCommand.gate op j (longGeometry B (x i)) =
      (j.val==1 && ((op==BStarLongCommand.admit && min 5 (ordinal h hh i)==2) ||
        (op==BStarLongCommand.bitOp && min 5 (ordinal h hh i)==4))) := by
  have b : eff h x i≤5 := by
    unfold eff
    split
    · decide
    · exact Nat.min_le_left _ _
  have T := C i
  rw [Nat.min_eq_right b] at T
  unfold BStarLongCommand.gate
  suffices E : (if (longGeometry B (x i)).axes.h6 then 0
      else min 5 (longGeometry B (x i)).offset) = min 5 (ordinal h hh i) by rw [E]
  change (if oldH6 B x i then 0 else min 5 (offsetL (x i).long))=_
  rw [same, Nat.min_eq_right (show offsetL (x i).long ≤ 5 from Nat.min_le_left _ _)]
  exact T

#print axioms gate_at_ordinal
#print axioms five_covers
#print axioms stable
end L4.BStarClearanceOffset

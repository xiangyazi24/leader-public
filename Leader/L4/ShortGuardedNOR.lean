import Leader.L4.ShortPublicationClassifier
import Leader.L4.ShortBankProjection
import Leader.L4.ShortReadResult
import Leader.L4.ShortNORCover
import Leader.L4.ShortResetCycle

namespace L4.ShortGuardedNOR
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortPublicationClassifier ShortReadResult ShortReaderMIS1

abbrev Sites {n : Nat} (h : Fin n→Bool) := {i : Fin n // h i=true}

def observe {s n : Nat} {h : Fin n→Bool} (x : Raw s n) (i : Sites h) : Bool :=
  selectedValue (x i.val).mis1

/-- The observer over one fixed H1 fibre. Every mark remains physical. -/
def classifyFixed {s n : Nat} (h : Fin n→Bool) (x : Raw s n) (e : Fin n) :
    Option (Sites h) :=
  match classify x e with
  | none => none
  | some i => if H : h i=true then some ⟨i,H⟩ else none

theorem fixed_some {s n : Nat} {h : Fin n→Bool} (x : Raw s n) (e : Fin n) (i : Sites h) :
    classifyFixed h x e=some i ↔ classify x e=some i.val := by
  constructor
  · intro E
    unfold classifyFixed at E
    split at E
    · contradiction
    · rename_i j V
      split at E
      · have J : j=i.val := congrArg (fun a : Sites h=>a.val) (Option.some.inj E)
        exact V.trans (congrArg some J)
      · contradiction
  · intro E
    rcases i with ⟨i,H⟩
    simp only [classifyFixed,E,H,dif_pos]

/-- After a guarded event, the new actual native value is the descriptor's
NOR whenever its two protected bits are from the current left/right
neighbours. This does not assume any liveness of the guard. -/
theorem recorded_current_nor {s n : Nat} {h : Fin n→Bool}
    (r : ShortNORCover.Ring (Sites h)) (x : Raw s n) (e : Fin n) (i : Sites h)
    (sep : e≠rightNeighbor e) (E : classifyFixed h x e=some i)
    (A : FromProtectedBits (observe x (r.left i)) (observe x (r.right i))
      (oldK (header x e) (x e).mis1 0).payload) :
    observe (rawNext s x e) i= !(ShortNORCover.selectedNeighbors r (observe x) i) := by
  obtain ⟨R,H,G⟩ := recorded_guard x e i.val ((fixed_some _ _ _).mp E)
  have H' : header x (rightNeighbor e)=true := by rw [R]; exact H
  have G' : ShortResetRow.selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1 := by
    rwa [R]
  have V := ShortBankProjection.selected_of_guard_write x e sep H' G'
    (ShortSelectorFlip.selector_responder_raw_publish x e sep H' G')
  obtain ⟨raw,L,P,D⟩ := A
  have B := descriptor_of_protected_reads raw _ _ L P
  rw [D] at B
  change selectedValue (rawNext s x e i.val).mis1 = _
  rwa [R,B] at V

/-- The step contract consumed by the two-cover theorem, with exact
raw observables. The named authentication premise remains separately
to be proved for the actual all-owner READ ancestry and adjacency. -/
theorem raw_step_conditional {s n : Nat} {h : Fin n→Bool}
    (r : ShortNORCover.Ring (Sites h)) (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (heads : ∀ i, header x i=h i)
    (auth : ∀ i : Sites h, classifyFixed h x e=some i →
      FromProtectedBits (observe x (r.left i)) (observe x (r.right i))
        (oldK (header x e) (x e).mis1 0).payload) :
    observe (rawNext s x e) = match classifyFixed h x e with
      | none => observe x
      | some i => ShortNORCover.update r (observe x) i := by
  classical
  cases E : classifyFixed h x e with
  | none =>
    funext j
    have H : header x j.val=true := (heads _).trans j.property
    have no : classify x e≠some j.val := fun S=>by
      have V := (fixed_some x e j).mpr S
      rw [E] at V
      cases V
    exact ShortBankProjection.selector_stutter x e j.val H
      (unrecorded_selector_stutters x e j.val H no)
  | some i =>
    funext j
    by_cases H : j=i
    · subst j
      simp only [ShortNORCover.update,if_true]
      exact recorded_current_nor r x e i sep E (auth i E)
    · simp only [ShortNORCover.update,if_neg H]
      have K : header x j.val=true := (heads _).trans j.property
      have no : classify x e≠some j.val := fun S=>by
        have V := (fixed_some x e j).mpr S
        rw [E] at V
        exact H ((Option.some.inj V).symm)
      exact ShortBankProjection.selector_stutter x e j.val K
        (unrecorded_selector_stutters x e j.val K no)

/-- Direct two-cover consumer for the actual sheet. Good is the
remaining all-owner provenance invariant, heads supplies the frozen
layout, and auth is the remaining guarded current-read certificate. -/
theorem two_publication_covers_conditional {s n : Nat} {h : Fin n→Bool}
    (N : 5≤n) (r : ShortNORCover.Ring (Sites h))
    (Good : Raw s n → Prop)
    (closed : ∀ x e, Good x → Good (rawNext s x e))
    (heads : ∀ x, Good x → ∀ i, header x i=h i)
    (auth : ∀ x e, Good x → ∀ i : Sites h, classifyFixed h x e=some i →
      FromProtectedBits (observe x (r.left i)) (observe x (r.right i))
        (oldK (header x e) (x e).mis1 0).payload)
    (x : Raw s n) (u v : List (Fin n)) (G : Good x)
    (coverU : ∀ i, i ∈ ShortNORCover.publications (rawNext s) (classifyFixed h) x u)
    (coverV : ∀ i, i ∈ ShortNORCover.publications (rawNext s) (classifyFixed h)
      (u.foldl (rawNext s) x) v) :
    let y : Sites h→Bool := observe ((u++v).foldl (rawNext s) x)
    ShortNORCover.Independent r y ∧ ∀ i, ShortNORCover.Dominates r y i := by
  have mid_good (w : List (Fin n)) (z : Raw s n) (H : Good z) : Good (w.foldl (rawNext s) z) := by
    induction w generalizing z with
    | nil => exact H
    | cons e v ih => exact ih _ (closed z e H)
  exact ShortNORCover.maximal_after_two_raw_segments r (rawNext s) (classifyFixed h) observe
    Good closed
    (by
      intro z e H
      have Z := raw_step_conditional r z e (ShortResetCycle.edge_sep (by omega : 1<n) e)
        (heads z H) (auth z e H)
      cases K : classifyFixed h z e <;> rw [K] at Z <;> exact Z)
    x u v G (mid_good u x G) coverU coverV

end L4.ShortGuardedNOR

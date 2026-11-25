import Leader.L4.Height.FencePathEnvelope
import Leader.L4.Height.FenceNominatedQuery

namespace L4.Height.FenceFixedPathEnvelope

open FenceNominatedQuery

/-- A fixed raw dependency path, with multiplicity: adjacent repeated
labels are distinct strictly-next required hits on the original word. -/
noncomputable def pathWait {n : Nat} (p : List (Fin n)) (u : Thru.Word n) : Nat :=
  strictSeq recordHit (p.map (fun mark last=>last=some mark)) none u

/-- The only remaining service input is deterministic domination on
the same candidate word by one of the strict raw dependency paths. -/
theorem fixed_paths_mean {n : Nat} (H horizon : Nat) (hn : 0<n) (hH : 0<H)
    (paths : List (List (Fin n))) (hne : paths≠[])
    (count : paths.length≤2*H*H*2^(2*H-1))
    (length : ∀ p,p∈paths→p.length≤2*(2*H-1))
    (actual : Thru.Word n→Nat)
    (dominated : ∀ w,actual w≤min (Thru.maxWait (paths.map pathWait) w) horizon) :
    Thru.wordSum actual horizon≤92*n*H*n^horizon := by
  let query := fun (mark : Fin n) (last : Option (Fin n))=>last=some mark
  let qs := paths.map (fun p=>p.map query)
  have notnil : qs≠[] := fun E=>hne (List.map_eq_nil_iff.mp E)
  have len : ∀ q,q∈qs→q.length≤2*(2*H-1) := by
    intro q member
    obtain ⟨p,mem,rfl⟩ := List.mem_map.mp member
    simpa only [List.length_map] using length p mem
  have moment : ∀ q,q∈qs→∀ A,A∈q→∀ y,Thru.MomentAt recordHit A (4*n) y := by
    intro q member A belongs y
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp member
    obtain ⟨mark,_,rfl⟩ := List.mem_map.mp belongs
    exact recordHit_moment mark y
  apply FencePathEnvelope.two_line_mean recordHit none H horizon hn hH qs notnil
    (by simpa only [qs,List.length_map] using count) len moment actual
  intro w
  have same : (qs.map (fun q=>strictSeq recordHit q none))=paths.map pathWait := by
    unfold qs
    rw [List.map_map]
    rfl
  rw [same]
  exact dominated w

#print axioms fixed_paths_mean
end L4.Height.FenceFixedPathEnvelope

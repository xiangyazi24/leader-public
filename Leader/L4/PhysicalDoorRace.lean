import Leader.L4.ProjectedDoor
import Leader.L4.Height.Count

namespace L4.PhysicalDoorRace
open PhysicalCustody ProjectedDoor Height

/-- The first k incident labels have all arrived (regardless of their values). -/
def complete {n : Nat} (d : Fin n) : Nat → List (Fin n) → Nat
  | 0,_ => 1
  | _+1,[] => 0
  | k+1,e::w => if DisjointMarks d e then complete d (k+1) w else complete d k w

/-- Success is abandoned at the first wrong incident label, not reset to
seek a later pair on the same authenticated reply. -/
def accepted {n : Nat} (d : Fin n) : Nat → List (Fin n) → Nat
  | 0,_ => 1
  | _+1,[] => 0
  | k+1,e::w =>
    if DisjointMarks d e then accepted d (k+1) w
    else if e=d then accepted d k w else 0

private theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun e => f e+g e)).sum=(l.map f).sum+(l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih]; omega

private theorem sum_mask {α : Type} (l : List α) (p : α → Bool) (v : Nat) :
    (l.map (fun e => if p e then v else 0)).sum=(l.filter p).length*v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : p a <;>
      simp [h, ih, Nat.succ_mul, Nat.add_comm]

private theorem self_nondisjoint {n : Nat} (d : Fin n) : ¬ DisjointMarks d d :=
  fun H => H.1 rfl

private theorem count_single {n : Nat} (d : Fin n) :
    ((List.finRange n).filter (fun e => decide (e=d))).length=1 := by
  have H (l : List (Fin n)) (nd : l.Nodup) (mem : d∈l) :
      (l.filter (fun e => decide (e=d))).length=1 := by
    induction l with
    | nil => exact (List.not_mem_nil mem).elim
    | cons a l ih =>
      have N := List.nodup_cons.mp nd
      by_cases E : a=d
      · subst a
        have empty : l.filter (fun e => decide (e=d))=[] := by
          apply List.filter_eq_nil_iff.mpr
          intro q M
          have nq : q≠d := fun eq => N.1 (eq ▸ M)
          simp [nq]
        simp [empty]
      · have M : d∈l := (List.mem_cons.mp mem).resolve_left (Ne.symm E)
        simpa [E] using ih N.2 M
  exact H _ (List.nodup_finRange n) (List.mem_finRange d)

private theorem complete_recurrence {n : Nat} (hn : 4≤n) (d : Fin n) (k t : Nat) :
    wordSum (complete d (k+1)) (t+1) =
      ((List.finRange n).filter (fun e => decide (DisjointMarks d e))).length *
        wordSum (complete d (k+1)) t + 3 * wordSum (complete d k) t := by
  rw [wordSum]
  let f (e : Fin n) := wordSum (fun w => complete d (k+1) (e::w)) t
  let u (e : Fin n) := if decide (DisjointMarks d e) then wordSum (complete d (k+1)) t else 0
  let v (e : Fin n) := if decide (¬ DisjointMarks d e) then wordSum (complete d k) t else 0
  have E : f = fun e => u e+v e := by
    funext e
    by_cases D : DisjointMarks d e <;> simp [f,u,v,complete,D]
  change (List.ofFn f).sum = _
  rw [show List.ofFn f = (List.finRange n).map f by
    simpa only [List.finRange,Function.comp_def] using
      (List.map_ofFn (f:=fun e : Fin n => e) (g:=f)).symm, E]
  change ((List.finRange n).map (fun e => u e+v e)).sum = _
  rw [sum_map_add,sum_mask (List.finRange n) (fun e => decide (DisjointMarks d e)),
    sum_mask (List.finRange n) (fun e => decide (¬DisjointMarks d e)),door_incident_labels_three hn d]

private theorem accepted_recurrence {n : Nat} (d : Fin n) (k t : Nat) :
    wordSum (accepted d (k+1)) (t+1) =
      ((List.finRange n).filter (fun e => decide (DisjointMarks d e))).length *
        wordSum (accepted d (k+1)) t + wordSum (accepted d k) t := by
  rw [wordSum]
  let f (e : Fin n) := wordSum (fun w => accepted d (k+1) (e::w)) t
  let u (e : Fin n) := if decide (DisjointMarks d e) then wordSum (accepted d (k+1)) t else 0
  let v (e : Fin n) := if decide (e=d) then wordSum (accepted d k) t else 0
  have E : f = fun e => u e+v e := by
    funext e
    by_cases eq : e=d
    · subst e
      simp [f,u,v,accepted,self_nondisjoint d]
    · by_cases D : DisjointMarks d e <;> simp [f,u,v,accepted,D,eq,wordSum_const]
  change (List.ofFn f).sum = _
  rw [show List.ofFn f = (List.finRange n).map f by
    simpa only [List.finRange,Function.comp_def] using
      (List.map_ofFn (f:=fun e : Fin n => e) (g:=f)).symm, E]
  change ((List.finRange n).map (fun e => u e+v e)).sum = _
  rw [sum_map_add,sum_mask (List.finRange n) (fun e => decide (DisjointMarks d e)),
    sum_mask (List.finRange n) (fun e => decide (e=d)),count_single,Nat.one_mul]

/-- At every finite horizon, among words with k incident marks, exactly
one in 3^k has the specified door label at each of the first k. In
particular the one- and two-hit races cost factors 3 and 9. -/
theorem incident_race_exact {n : Nat} (hn : 4≤n) (d : Fin n) (t k : Nat) :
    3^k * wordSum (accepted d k) t = wordSum (complete d k) t := by
  induction t generalizing k with
  | zero =>
    cases k <;> simp [wordSum, accepted, complete]
  | succ t ih =>
    cases k with
    | zero =>
      have E : accepted d 0 = complete d 0 := by
        funext w
        cases w <;> rfl
      rw [E, Nat.pow_zero, Nat.one_mul]
    | succ k =>
      rw [accepted_recurrence, complete_recurrence hn, Nat.mul_add,
        Nat.mul_left_comm (3^(k+1)), ih (k+1), Nat.pow_succ,
        Nat.mul_comm (3^k) 3, Nat.mul_assoc, ih k]

#print axioms incident_race_exact
end L4.PhysicalDoorRace

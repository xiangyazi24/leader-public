import Leader.L4.BStarFenceCrossing

namespace L4.BStarFenceCrossingWait
open BStarFenceCrossing BStarFenceShadow

theorem trace_append {n k : Nat} (port : Fin k→Fin n)
    (z : Fin k→Bool) (ct : Fin k→Nat) (u v : List (Fin n)) :
    trace port z ct (u++v) =
      trace port (trace port z ct u).1 (trace port z ct u).2 v := by
  induction u generalizing z ct with
  | nil => rfl
  | cons e u ih =>
    simp only [List.cons_append,trace]
    exact ih _ _

theorem bump_ge {n k : Nat} (port : Fin k→Fin n) (e : Fin n)
    (z : Fin k→Bool) (ct : Fin k→Nat) (j : Fin k) :
    ct j≤bump port e z ct j := by
  unfold bump
  omega

theorem trace_ge {n k : Nat} (port : Fin k→Fin n)
    (z : Fin k→Bool) (ct : Fin k→Nat) (w : List (Fin n)) (j : Fin k) :
    ct j≤(trace port z ct w).2 j := by
  induction w generalizing z ct with
  | nil => exact Nat.le_refl _
  | cons e w ih => exact Nat.le_trans (bump_ge port e z ct j) (ih _ _)

theorem count_extension {n k : Nat} (port : Fin k→Fin n)
    (z : Fin k→Bool) (ct : Fin k→Nat) (u v : List (Fin n)) (j : Fin k) :
    (trace port z ct u).2 j≤(trace port z ct (u++v)).2 j := by
  rw [trace_append]
  exact trace_ge port _ _ v j

theorem prev_mono {k : Nat} (ct ct' : Fin k→Nat) (H : ∀ j,ct j≤ct' j) (j : Fin k) :
    prev ct j≤prev ct' j := by
  unfold prev
  split
  · exact H _
  · exact Nat.le_refl _

/-- Both parents are counted at the cut. If j's crossing is not yet
paid, the first subsequent occurrence of its own port pays it, even
with arbitrary other emitted marks before and after. -/
theorem crossing_by_mem {n k : Nat} (port : Fin k→Fin n)
    (injective : ∀ a b,port a=port b→a=b)
    (z : Fin k→Bool) (ct : Fin k→Nat) (B : Balance z ct)
    (j : Fin k) (m : Nat) (pos : 0<m)
    (inReady : m-1≤prev ct j)
    (outReady : ∀ h : j.val+1<k,m≤ct (succIdx j h))
    (w : List (Fin n)) (hit : port j∈w) :
    m≤(trace port z ct w).2 j := by
  obtain ⟨lead,tail,E⟩ := List.append_of_mem hit
  let q := trace port z ct lead
  have ge : ∀ i,ct i≤q.2 i := trace_ge port z ct lead
  have Bi : Balance q.1 q.2 := trace_balance port injective z ct lead B
  rw [E,trace_append]
  change m≤(trace port (update port (port j) q.1) (bump port (port j) q.1 q.2) tail).2 j
  apply Nat.le_trans _ (trace_ge port _ _ tail j)
  by_cases paid : m≤q.2 j
  · exact Nat.le_trans paid (bump_ge port _ _ _ _)
  · have isReady := crossing_ready_two Bi j m pos (by omega)
      (Nat.le_trans inReady (prev_mono ct q.2 ge j)) (fun h => Nat.le_trans (outReady h) (ge _))
    have atLeast : m-1≤q.2 j :=
      Nat.le_trans (Nat.le_trans inReady (prev_mono ct q.2 ge j)) (balance_bounds Bi j).1
    unfold bump
    rw [if_pos rfl,isReady]
    change m≤q.2 j+1
    omega

/-- Form explicitly indexed by the existing common-tape cut. -/
theorem crossing_by_mem_after_cut {n k : Nat} (port : Fin k→Fin n)
    (injective : ∀ a b,port a=port b→a=b)
    (j : Fin k) (m : Nat) (pos : 0<m) (u v : List (Fin n))
    (inReady : m-1≤prev (trace port (fun _=>true) (fun _=>0) u).2 j)
    (outReady : ∀ h : j.val+1<k,
      m≤(trace port (fun _=>true) (fun _=>0) u).2 (succIdx j h))
    (hit : port j∈v) :
    m≤(trace port (fun _=>true) (fun _=>0) (u++v)).2 j := by
  rw [trace_append]
  exact crossing_by_mem port injective _ _ (full_balance port injective u)
    j m pos inReady outReady v hit

end L4.BStarFenceCrossingWait

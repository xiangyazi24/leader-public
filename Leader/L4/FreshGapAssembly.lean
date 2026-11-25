import Leader.L4.RankRace

namespace L4.FreshGapAssembly
open RankRenewal TaggedTail

private theorem s_mono {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))

private theorem s_constant (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => simp [sumEdge,List.ofFn_succ,show (List.ofFn (fun _ : Fin n => a)).sum=n*a from ih,
      Nat.succ_mul,Nat.add_comm]

private theorem s_scale {n : Nat} (C : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => C*f e)=C*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    rw [Nat.mul_add]
    exact congrArg (fun z => C*f 0+z) (ih (fun i => f i.succ))

/-- Exact first-entry gluing at common finite horizon. Before entry the
event is false. At a first entry use the uniform scaled endpoint bound
on the remaining suffix. The recurrence is over actual raw marks, so
it never multiplies by the number of possible entry times. -/
theorem scaled_bound_from_first_entry {α : Type} {n : Nat}
    (next : α → Fin n → α) (entered : α → Prop) (score : α → Nat)
    (C : Nat) (admissible : α → Prop)
    (forward : ∀ x e, admissible x → admissible (next x e))
    (absent : ∀ x, admissible x → ¬entered x → score x=0)
    (entryBound : ∀ x, admissible x → entered x →
        ∀ t, C*endpointSum next score t x≤n^t) :
    ∀ t x, admissible x → C*endpointSum next score t x≤n^t := by
  intro t
  induction t with
  | zero =>
    intro x hx
    by_cases hn : entered x
    · exact entryBound x hx hn 0
    · change C*score x≤n^0
      rw [absent x hx hn,Nat.mul_zero]
      exact Nat.zero_le _
  | succ t ih =>
    intro x hx
    by_cases hn : entered x
    · exact entryBound x hx hn (t+1)
    · rw [endpointSum,← s_scale]
      calc
        _ ≤ sumEdge (fun _ : Fin n => n^t) :=
          s_mono (fun i => ih (next x i) (forward x i hx))
        _ = _ := by rw [s_constant, Nat.pow_succ, Nat.mul_comm]

private theorem endpoint_mono {α : Type} {n : Nat} (next : α → Fin n → α)
    (f g : α → Nat) (h : ∀ x, f x≤g x) (t : Nat) (x : α) :
    endpointSum next f t x≤endpointSum next g t x := by
  induction t generalizing x with
  | zero => exact h _
  | succ t ih => exact s_mono (fun e => ih (next x e))

private theorem s_add {n : Nat} (f g : Fin n→Nat) :
    sumEdge (fun i => f i+g i)=sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    have z := ih (fun i => f i.succ) (fun i => g i.succ)
    simp only [sumEdge] at z
    rw [z]
    omega

private theorem endpoint_add {α : Type} {n : Nat} (next : α → Fin n → α)
    (f g : α → Nat) (t : Nat) (x : α) :
    endpointSum next (fun x => f x+g x) t x=endpointSum next f t x+endpointSum next g t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [endpointSum,ih,s_add]

theorem endpoint_two_cause_union {α : Type} {n : Nat} (next : α → Fin n → α)
    (failed early slow : α → Nat) (covered : ∀ x, failed x≤early x+slow x)
    (t : Nat) (x : α) :
    endpointSum next failed t x≤
      endpointSum next early t x+endpointSum next slow t x := by
  rw [← endpoint_add]
  exact endpoint_mono next failed _ covered t x

end L4.FreshGapAssembly

#print axioms L4.FreshGapAssembly.scaled_bound_from_first_entry
#print axioms L4.FreshGapAssembly.endpoint_two_cause_union

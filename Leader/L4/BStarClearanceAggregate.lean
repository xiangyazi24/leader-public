import Std

/-! Combine local nonincrease on a partition of an owner's addresses.
The permutation premise accounts for every address exactly once, not
just membership in a union. The same fold handles a distinguished
paying block and pointwise framing on the untouched addresses. -/
namespace L4.BStarClearanceAggregate

def total {A : Type} (f : A → Nat) (xs : List A) : Nat := (xs.map f).sum

theorem total_append {A : Type} (f : A → Nat) (xs ys : List A) :
    total f (xs++ys)=total f xs+total f ys := by
  simp [total,List.sum_append]

theorem perm_total {A : Type} (f : A → Nat) {xs ys : List A} (h : xs.Perm ys) :
    total f xs=total f ys := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (fun n => f a+n) ih
  | swap a b l =>
    change f _ + (f _ + total f l)=f _ + (f _ + total f l)
    omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem outside_total {A : Type} (before after : A → Nat) (outside : List A)
    (h : ∀ a∈outside, after a=before a) : total after outside=total before outside := by
  induction outside with
  | nil => rfl
  | cons a out ih =>
    change after a+total after out=before a+total before out
    rw [h a List.mem_cons_self,ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem block_total_le {A : Type} (before after : A → Nat) (blocks : List (List A))
    (h : ∀ b∈blocks, total after b≤total before b) :
    total after blocks.flatten≤total before blocks.flatten := by
  induction blocks with
  | nil => exact Nat.le_refl _
  | cons b bs ih =>
    rw [List.flatten_cons,total_append,total_append]
    exact Nat.add_le_add (h b List.mem_cons_self) (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem block_total_lt {A : Type} (before after : A → Nat) (blocks : List (List A))
    (h : ∀ b∈blocks, total after b≤total before b)
    (pays : ∃ b∈blocks, total after b<total before b) :
    total after blocks.flatten<total before blocks.flatten := by
  induction blocks with
  | nil => obtain ⟨_,H,_⟩ := pays; exact (List.not_mem_nil H).elim
  | cons b bs ih =>
    rw [List.flatten_cons,total_append,total_append]
    have tail : ∀ a∈bs, total after a≤total before a := fun a ha => h a (List.mem_cons_of_mem _ ha)
    obtain ⟨d,H,D⟩ := pays
    rcases List.mem_cons.mp H with rfl|H
    · have T := block_total_le before after bs tail
      omega
    · have T := ih tail ⟨_,H,D⟩
      have Q := h b List.mem_cons_self
      omega

theorem aggregate_le {A : Type} (before after : A → Nat)
    (slots outside : List A) (blocks : List (List A))
    (partition : slots.Perm (blocks.flatten++outside))
    (frame : ∀ a∈outside, after a=before a)
    (local_le : ∀ b∈blocks, total after b≤total before b) :
    total after slots≤total before slots := by
  rw [perm_total after partition,perm_total before partition,total_append,total_append,
    outside_total _ _ _ frame]
  exact Nat.add_le_add_right (block_total_le _ _ _ local_le) _

theorem aggregate_lt {A : Type} (before after : A → Nat)
    (slots outside : List A) (blocks : List (List A))
    (partition : slots.Perm (blocks.flatten++outside))
    (frame : ∀ a∈outside, after a=before a)
    (local_le : ∀ b∈blocks, total after b≤total before b)
    (pays : ∃ b∈blocks, total after b<total before b) :
    total after slots<total before slots := by
  rw [perm_total after partition,perm_total before partition,total_append,total_append,
    outside_total _ _ _ frame]
  exact Nat.add_lt_add_right (block_total_lt _ _ _ local_le pays) _

/-- Explicit complement of selected chart occurrences. The only chart
hypotheses are no duplicated occurrence and containment in the owner. -/
def remainder {A : Type} [DecidableEq A] (slots : List A) (blocks : List (List A)) :
    List A := slots.filter fun a => decide (a∉blocks.flatten)

theorem chart_partition {A : Type} [DecidableEq A] (slots : List A) (blocks : List (List A))
    (ns : slots.Nodup) (nb : blocks.flatten.Nodup)
    (sub : blocks.flatten ⊆ slots) :
    slots.Perm (blocks.flatten++remainder slots blocks) := by
  have rem : ∀ a, a∈remainder slots blocks ↔ a∈slots ∧ a∉blocks.flatten := by
    intro a
    simp [remainder]
  have nrem : (remainder slots blocks).Nodup := ns.filter _
  have dis : ∀ a∈blocks.flatten, ∀ b∈remainder slots blocks, a≠b := by
    intro a ha b hb E
    subst b
    exact (rem a).mp hb |>.2 ha
  have nd : (blocks.flatten++remainder slots blocks).Nodup :=
    List.pairwise_append.mpr ⟨nb,nrem,dis⟩
  apply (List.perm_ext_iff_of_nodup ns nd).mpr
  intro a
  rw [List.mem_append,rem]
  by_cases h : a∈blocks.flatten
  · simp [h,sub h]
  · simp [h]

theorem sum_mono {A : Type} (before after : A → Nat) (slots : List A)
    (h : ∀ a∈slots, after a≤before a) : total after slots≤total before slots := by
  induction slots with
  | nil => exact Nat.le_refl _
  | cons a rest ih =>
    exact Nat.add_le_add (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- Outside blocks may even decrease (e.g. discard/normalization).
The strict paying comparison in one selected block still lifts. -/
theorem chart_pays {A : Type} [DecidableEq A] (before after : A → Nat)
    (slots : List A) (blocks : List (List A))
    (ns : slots.Nodup) (nb : blocks.flatten.Nodup) (sub : blocks.flatten ⊆ slots)
    (outside : ∀ a∈remainder slots blocks, after a≤before a)
    (local_le : ∀ b∈blocks, total after b≤total before b)
    (pays : ∃ b∈blocks, total after b<total before b) :
    total after slots<total before slots := by
  have part := chart_partition slots blocks ns nb sub
  rw [perm_total after part,perm_total before part,total_append,total_append]
  exact Nat.add_lt_add_of_lt_of_le (block_total_lt _ _ _ local_le pays)
    (sum_mono _ _ _ outside)

end L4.BStarClearanceAggregate

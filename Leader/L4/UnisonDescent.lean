import Init.Data.List.FinRange
import Init.Data.List.Perm
import Init.Omega

/-! Finite graph arithmetic for the flooding and closing stages of unison. -/
namespace L4.UnisonDescent

/-- Every error above the base has an erroneous, strictly smaller
neighbour. The relation is stated from neighbour to centre. -/
def HasDescent {V : Type} (edge : V → V → Prop)
    (bad : V → Prop) (value : V → Int) (base : Int) : Prop :=
  ∀ v, bad v → base < value v → ∃ u, edge u v ∧ bad u ∧ value u < value v

/-- Every neighbour of an erroneous vertex at or below the cutoff is
at most one level above that vertex. -/
def Flooded {V : Type} (edge : V → V → Prop)
    (bad : V → Prop) (value : V → Int) (cutoff : Int) : Prop :=
  ∀ u v, edge u v → bad u → value u ≤ cutoff → value v ≤ value u+1

/-- The level where an errant descending walk first crosses its target is
exact: the propagation inequality makes skipping that target impossible. -/
theorem exists_at_level {V : Type} (edge : V → V → Prop)
    (bad : V → Prop) (value : V → Int) (base cutoff target : Int)
    (hd : HasDescent edge bad value base) (hf : Flooded edge bad value cutoff)
    (hbase : base ≤ target) (htarget : target ≤ cutoff+1)
    {v : V} (hv : bad v) (ht : target ≤ value v) :
    ∃ u, bad u ∧ value u = target := by
  have aux (k : Nat) : ∀ x : V, bad x → target ≤ value x →
      (value x - target).toNat = k → ∃ u, bad u ∧ value u = target := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro x hx hxval hidx
      by_cases he : value x = target
      · exact ⟨x,hx,he⟩
      obtain ⟨y,hyedge,hy,hyval⟩ := hd x hx (by omega)
      have hyt : target ≤ value y := by
        apply Int.le_of_not_gt
        intro hn
        have H := hf y x hyedge hy (by omega)
        omega
      exact ih _ (by omega) y hy hyt rfl
  exact aux _ v hv ht rfl

/-- On `m` vertices, flooding through the first `m` levels forces every
erroneous level into that range. An error above it would exhibit `m+1`
different erroneous vertices at the levels base through base+m. -/
theorem error_le_of_flooded {m : Nat} (edge : Fin m → Fin m → Prop)
    (bad : Fin m → Prop) (value : Fin m → Int) (base : Int)
    (hd : HasDescent edge bad value base)
    (hf : Flooded edge bad value (base + (m : Int) - 1)) :
    ∀ v, bad v → value v ≤ base+(m : Int)-1 := by
  intro v hv
  apply Int.le_of_not_gt
  intro h
  have existsV (i : Fin (m+1)) : ∃ u, bad u ∧ value u = base+(i.val : Int) :=
    exists_at_level edge bad value base _ _ hd hf (by omega) (by omega) hv (by omega)
  let pick (i : Fin (m+1)) := Classical.choose (existsV i)
  have pickValue (i : Fin (m+1)) : value (pick i)=base+(i.val : Int) :=
    (Classical.choose_spec (existsV i)).2
  have pinj : ∀ {i j}, pick i=pick j → i=j := by
    intro i j h'
    apply Fin.ext
    have H := congrArg value h'
    rw [pickValue,pickValue] at H
    omega
  have distinct : (List.finRange (m+1)).Nodup := List.nodup_finRange _
  have out : ((List.finRange (m+1)).map pick).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact (List.nodup_iff_pairwise_ne.mp distinct).imp (fun hne he => hne (pinj he))
  have H := out.length_le_of_subset (l₂ := List.finRange m)
    (fun a _ => List.mem_finRange a)
  simp at H
  omega

/-- Quiescence at the flooded threshold: there is no erroneous neighbour
that can pull an adjacent vertex down by two or more levels. -/
theorem no_pull_after_flooded {m : Nat} (edge : Fin m → Fin m → Prop)
    (bad : Fin m → Prop) (value : Fin m → Int) (base : Int)
    (hd : HasDescent edge bad value base)
    (hf : Flooded edge bad value (base + (m : Int) - 1))
    {u v : Fin m} (he : edge u v) (hu : bad u) :
    ¬ value u+1 < value v := by
  have H := error_le_of_flooded edge bad value base hd hf u hu
  exact Int.not_lt.mpr (hf u v he hu H)

/-- Local clearing guard at a maximum erroneous level. A correct lower
neighbour cannot have a gap by the all-roots-at-base predicate. An
erroneous lower neighbour is bounded by the already flooded inequality.
The numeric within-one test suffices even if the literal test additionally
admits a wrap pair. -/
theorem max_error_guard {V : Type} (edge : V → V → Prop)
    (bad : V → Prop) (value : V → Int) (cutoff : Int)
    (sym : ∀ {u v}, edge u v → edge v u)
    (hf : Flooded edge bad value cutoff)
    (hcap : ∀ u, bad u → value u≤cutoff)
    (hcorrect : ∀ u v, edge u v → ¬ bad u → value u < value v → value v≤value u+1)
    {v : V} (hv : bad v) (hmax : ∀ u, bad u → value u≤value v) :
    ∀ u, edge u v →
      value u≤value v+1 ∧ value v≤value u+1 ∧ (value v<value u → ¬bad u) := by
  intro u he
  refine ⟨hf v u (sym he) hv (hcap v hv),?_,?_⟩
  · by_cases hu : bad u
    · exact hf u v he hu (hcap u hu)
    · by_cases hlt : value u < value v
      · exact hcorrect u v he hu hlt
      · omega
  · exact fun hlt hu => Int.not_lt.mpr (hmax u hu) hlt

/-- If old erroneous vertices only freeze or clear, and no adjacent
correct word can rise across a surviving error's ceiling, the fully
flooded invariant survives. The condition on values below the cutoff is
then independent of the transition rule on correct vertices. -/
theorem flooded_keep_of_frozen {V : Type} (edge : V → V → Prop)
    (bad bad' : V → Prop) (value value' : V → Int) (cutoff : Int)
    (hf : Flooded edge bad value cutoff)
    (hcap : ∀ u, bad u → value u≤cutoff)
    (freeze : ∀ u, bad' u → bad u ∧ value' u=value u)
    (noCross : ∀ u v, edge u v → bad' u → value v≤value u+1 → value' v≤value u+1) :
    Flooded edge bad' value' cutoff ∧ ∀ u, bad' u → value' u≤cutoff := by
  constructor
  · intro u v he hu _
    obtain ⟨ho,hv⟩ := freeze u hu
    rw [hv]
    exact noCross u v he hu (hf u v he ho (hcap u ho))
  · intro u hu
    obtain ⟨ho,he⟩ := freeze u hu
    rw [he]
    exact hcap u ho

end L4.UnisonDescent


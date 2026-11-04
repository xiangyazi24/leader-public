import Leader.Core.FiniteUniformStoppingTree

/-!
# Exact uniform capture-macro time change

This file isolates the scheduler interface needed between a *capture-stopped
macro kernel* and a virtual uniformly scheduled protocol.  The projection is
a fixed function supplied once; it cannot existentially choose a new corridor
cut or owner after seeing a scheduler child.  The `macroStep` argument is not
one raw radius-one interaction: capture selects an owner, the internal service
tree is hidden and charged separately, and the returned active payload has
already re-entered the free macro domain.

`copies` is a literal capture-fiber multiplicity: each virtual edge contributes
exactly `copies` macro children.  The remaining `n - copies * m` children are
stutters in `ExactUniformOrStutter`.  The weaker
`UniformCoreSafeRemainder` permits a nonuniform remainder only after proving
its potential contribution is no larger than stuttering.  Thus a bare
per-edge probability lower bound is not silently treated as sufficient.

Applying this interface to a raw local-step chain is impossible whenever a
live service state has only projected stutter children.  The theorem
`UniformCoreSafeRemainder.no_stutter_only_state` makes that obstruction
explicit below.

The Bellman lift has physical scale `copies * m * scale` and physical
potential `n * V`.  Consequently its division-free slowdown is

`copies * m * physicalCost <= n^T * (n * virtualBudget)`,

i.e. the normalized slowdown factor is exactly `n / (copies * m)`.
-/

namespace PPLLUniformCompletedEdgeTimeChange

open FiniteUniformStoppingTree

set_option autoImplicit false
set_option warningAsError true

/-- Apply one fixed physical-to-virtual projection without changing either
terminal outcome. -/
def projectNode {P V : Type} (project : P → V) : StopNode P → StopNode V
  | .active state => .active (project state)
  | .success => .success
  | .failure => .failure

/-- Exact uniform virtual core plus literal physical stutters.  Quantifying
over every natural weight makes this an exact child-multiset statement, not a
claim about one chosen Lyapunov function.  All physical children are covered,
including both boundary edges of a represented corridor. -/
structure ExactUniformOrStutter
    {P V : Type} {n m : Nat}
    (macroStep : P → Fin n → StopNode P)
    (virtualStep : V → Fin m → StopNode V)
    (project : P → V) (copies : Nat) : Prop where
  copies_mul_le : copies * m ≤ n
  childSum : ∀ (state : P) (weight : StopNode V → Nat),
    (List.ofFn (fun raw : Fin n =>
      weight (projectNode project (macroStep state raw)))).sum =
      copies * (List.ofFn (fun edge : Fin m =>
        weight (virtualStep (project state) edge))).sum +
      (n - copies * m) * weight (.active (project state))

/-- The precise relaxation usable by a Bellman proof.  It is what a
lower-bounded adaptive scheduler must establish in addition to the numerical
lower bound: its surplus mass must be potential-safe. -/
structure UniformCoreSafeRemainder
    {P V : Type} {n m : Nat}
    (macroStep : P → Fin n → StopNode P)
    (virtualStep : V → Fin m → StopNode V)
    (project : P → V) (copies : Nat)
    (potential : StopNode V → Nat) : Prop where
  copies_mul_le : copies * m ≤ n
  childSum_le : ∀ state,
    (List.ofFn (fun raw : Fin n =>
      potential (projectNode project (macroStep state raw)))).sum ≤
      copies * (List.ofFn (fun edge : Fin m =>
        potential (virtualStep (project state) edge))).sum +
      (n - copies * m) * potential (.active (project state))

theorem ExactUniformOrStutter.toSafe
    {P V : Type} {n m copies : Nat}
    {macroStep : P → Fin n → StopNode P}
    {virtualStep : V → Fin m → StopNode V}
    {project : P → V}
    (h : ExactUniformOrStutter macroStep virtualStep project copies)
    (potential : StopNode V → Nat) :
    UniformCoreSafeRemainder macroStep virtualStep project copies
      potential := by
  exact ⟨h.copies_mul_le, fun state =>
    Nat.le_of_eq (h.childSum state potential)⟩

/-- A positive uniform-core Bellman interface cannot be attached directly to
a raw service state whose every scheduler child is only a projected stutter.
Such states must be hidden inside the separately charged capture service tree;
the `macroStep` domain consists only of free, capture-ready states. -/
theorem UniformCoreSafeRemainder.no_stutter_only_state
    {P V : Type} {n m copies scale : Nat}
    {macroStep : P → Fin n → StopNode P}
    {virtualStep : V → Fin m → StopNode V}
    {project : P → V} {potential : StopNode V → Nat}
    (hrefine : UniformCoreSafeRemainder
      macroStep virtualStep project copies potential)
    (hvirtual : NatBellmanSuperSolution virtualStep scale potential)
    (hcopies : 0 < copies) (hm : 0 < m) (hscale : 0 < scale)
    (state : P)
    (hstutter : ∀ raw,
      projectNode project (macroStep state raw) =
        .active (project state)) : False := by
  let value := potential (.active (project state))
  let virtualSum := (List.ofFn (fun edge : Fin m ↦
    potential (virtualStep (project state) edge))).sum
  let macroSum := (List.ofFn (fun raw : Fin n ↦
    potential (projectNode project (macroStep state raw)))).sum
  have hmacroSum : macroSum = n * value := by
    calc
      macroSum = (List.ofFn (fun _ : Fin n ↦ value)).sum := by
        apply ofFn_sum_eq
        intro raw
        simp only [value]
        rw [hstutter raw]
      _ = n * value := ofFn_sum_const n value
  have hrefineStep : n * value ≤
      copies * virtualSum + (n - copies * m) * value := by
    rw [← hmacroSum]
    exact hrefine.childSum_le state
  have hvirtualStep : scale * m + virtualSum ≤ m * value := by
    exact hvirtual.2.2 (project state)
  have hscaled := Nat.mul_le_mul_left copies hvirtualStep
  have hdecompose : copies * m + (n - copies * m) = n :=
    Nat.add_sub_of_le hrefine.copies_mul_le
  have himpossible : copies * (scale * m) + n * value ≤ n * value := by
    calc
      copies * (scale * m) + n * value ≤
          copies * (scale * m) +
            (copies * virtualSum + (n - copies * m) * value) :=
        Nat.add_le_add_left hrefineStep _
      _ = copies * (scale * m + virtualSum) +
            (n - copies * m) * value := by
        simp [Nat.mul_add, Nat.add_assoc]
      _ ≤ copies * (m * value) +
            (n - copies * m) * value :=
        Nat.add_le_add_right hscaled _
      _ = (copies * m + (n - copies * m)) * value := by
        simp [Nat.add_mul, Nat.mul_assoc]
      _ = n * value := by rw [hdecompose]
  have hpositive : 0 < copies * (scale * m) :=
    Nat.mul_pos hcopies (Nat.mul_pos hscale hm)
  omega

/-- A virtual natural Bellman certificate lifts through a fixed projected
uniform core.  The proof retains the exact multiplicity dimensions: `copies`
per virtual edge, `m` virtual edges, and `n` physical children. -/
theorem natBellmanSuperSolution_lift
    {P V : Type} {n m copies scale : Nat}
    (macroStep : P → Fin n → StopNode P)
    (virtualStep : V → Fin m → StopNode V)
    (project : P → V) (potential : StopNode V → Nat)
    (hrefine : UniformCoreSafeRemainder
      macroStep virtualStep project copies potential)
    (hvirtual : NatBellmanSuperSolution virtualStep scale potential) :
    NatBellmanSuperSolution macroStep (copies * m * scale)
      (fun node => n * potential (projectNode project node)) := by
  rcases hvirtual with ⟨hsuccess, hfailure, hstep⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [projectNode, hsuccess]
  · simp [projectNode, hfailure]
  · intro state
    let virtualSum := (List.ofFn (fun edge : Fin m =>
      potential (virtualStep (project state) edge))).sum
    let physicalSum := (List.ofFn (fun raw : Fin n =>
      potential (projectNode project (macroStep state raw)))).sum
    have hvirtualStep : scale * m + virtualSum ≤
        m * potential (.active (project state)) := hstep (project state)
    have hphysical : physicalSum ≤
        copies * virtualSum +
          (n - copies * m) * potential (.active (project state)) :=
      hrefine.childSum_le state
    have hdecompose : copies * m + (n - copies * m) = n :=
      Nat.add_sub_of_le hrefine.copies_mul_le
    have hinner : copies * (scale * m) + physicalSum ≤
        n * potential (.active (project state)) := by
      calc
        copies * (scale * m) + physicalSum ≤
            copies * (scale * m) +
              (copies * virtualSum +
                (n - copies * m) *
                  potential (.active (project state))) :=
          Nat.add_le_add_left hphysical _
        _ = copies * (scale * m + virtualSum) +
              (n - copies * m) *
                potential (.active (project state)) := by
          simp [Nat.mul_add, Nat.add_assoc]
        _ ≤ copies * (m * potential (.active (project state))) +
              (n - copies * m) *
                potential (.active (project state)) :=
          Nat.add_le_add_right
            (Nat.mul_le_mul_left copies hvirtualStep) _
        _ = (copies * m + (n - copies * m)) *
              potential (.active (project state)) := by
          simp [Nat.add_mul, Nat.mul_assoc]
        _ = n * potential (.active (project state)) := by
          rw [hdecompose]
    rw [ofFn_sum_mul_left]
    calc
      (copies * m * scale) * n + n * physicalSum =
          n * (copies * (scale * m) + physicalSum) := by
        simp [Nat.mul_add]
        ac_rfl
      _ ≤ n * (n * potential (.active (project state))) :=
        Nat.mul_le_mul_left n hinner

/-- Finite-horizon physical cost bound with the scaled virtual potential
retained. -/
theorem truncatedCost_mul_le
    {P V : Type} {n m copies scale T : Nat}
    (macroStep : P → Fin n → StopNode P)
    (virtualStep : V → Fin m → StopNode V)
    (project : P → V) (potential : StopNode V → Nat)
    (hrefine : UniformCoreSafeRemainder
      macroStep virtualStep project copies potential)
    (hvirtual : NatBellmanSuperSolution virtualStep scale potential)
    (initial : StopNode P) :
    (copies * m * scale) *
        truncatedActiveCostNumerator macroStep initial T ≤
      n ^ T * (n * potential (projectNode project initial)) := by
  exact truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    macroStep (copies * m * scale)
      (fun node => n * potential (projectNode project node))
      (natBellmanSuperSolution_lift macroStep virtualStep project
        potential hrefine hvirtual) initial T

/-- Numerator-only slowdown statement.  If the lifted initial virtual
potential is at most `scale * budget`, positivity of `scale` cancels it and
leaves the exact factor `n / (copies * m)`. -/
theorem copies_mul_virtualEdges_mul_truncatedCost_le
    {P V : Type} {n m copies scale budget T : Nat}
    (macroStep : P → Fin n → StopNode P)
    (virtualStep : V → Fin m → StopNode V)
    (project : P → V) (potential : StopNode V → Nat)
    (hrefine : UniformCoreSafeRemainder
      macroStep virtualStep project copies potential)
    (hvirtual : NatBellmanSuperSolution virtualStep scale potential)
    (hscale : 0 < scale) (initial : StopNode P)
    (hinitial : potential (projectNode project initial) ≤ scale * budget) :
    copies * m * truncatedActiveCostNumerator macroStep initial T ≤
      n ^ T * (n * budget) := by
  have hcost := truncatedCost_mul_le (T := T) macroStep virtualStep project
    potential hrefine hvirtual initial
  have hbound : n ^ T *
        (n * potential (projectNode project initial)) ≤
      n ^ T * (n * (scale * budget)) :=
    Nat.mul_le_mul_left (n ^ T)
      (Nat.mul_le_mul_left n hinitial)
  have hscaled : scale *
        (copies * m * truncatedActiveCostNumerator macroStep initial T) ≤
      scale * (n ^ T * (n * budget)) := by
    calc
      scale * (copies * m *
          truncatedActiveCostNumerator macroStep initial T) =
          (copies * m * scale) *
            truncatedActiveCostNumerator macroStep initial T := by
        ac_rfl
      _ ≤ n ^ T *
          (n * potential (projectNode project initial)) := hcost
      _ ≤ n ^ T * (n * (scale * budget)) := hbound
      _ = scale * (n ^ T * (n * budget)) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled hscale

/-- Direct exact-uniform-or-stutter consumer. -/
theorem exact_copies_mul_virtualEdges_mul_truncatedCost_le
    {P V : Type} {n m copies scale budget T : Nat}
    (macroStep : P → Fin n → StopNode P)
    (virtualStep : V → Fin m → StopNode V)
    (project : P → V) (potential : StopNode V → Nat)
    (hrefine : ExactUniformOrStutter
      macroStep virtualStep project copies)
    (hvirtual : NatBellmanSuperSolution virtualStep scale potential)
    (hscale : 0 < scale) (initial : StopNode P)
    (hinitial : potential (projectNode project initial) ≤ scale * budget) :
    copies * m * truncatedActiveCostNumerator macroStep initial T ≤
      n ^ T * (n * budget) := by
  exact copies_mul_virtualEdges_mul_truncatedCost_le
    macroStep virtualStep project potential (hrefine.toSafe potential)
      hvirtual hscale initial hinitial

#print axioms natBellmanSuperSolution_lift
#print axioms UniformCoreSafeRemainder.no_stutter_only_state
#print axioms truncatedCost_mul_le
#print axioms copies_mul_virtualEdges_mul_truncatedCost_le
#print axioms exact_copies_mul_virtualEdges_mul_truncatedCost_le

end PPLLUniformCompletedEdgeTimeChange

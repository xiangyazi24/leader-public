import Leader.Core.PayloadFiniteStoppingTree
import Leader.Wu.Carrier.CaptureTimeChange

/-!
# Capture-stopped compiler interface

The uniform object in a physical compiler is the first raw scheduler draw at
a free macro boundary, not the later commit/completion label.  One distinguished
physical root edge `h * e` captures each virtual edge `e`; all other raw draws
are retries at the same free macro state.  After capture, an endpoint-retaining
raw service tree is charged separately.  Every successful service payload is
indexed by the captured source and edge, refines that exact virtual child, and
returns either a terminal node or another value of the free-state type.

This is an interface, not an instantiation by the current QMAT table.  In
particular, `service_no_failure`, `service_cost_le`, and the current-certificate
production/closure facts remain concrete compiler obligations.
-/

namespace PPLLCaptureStoppedCompiler

open FiniteUniformStoppingTree
open PayloadFiniteStoppingTree
open PPLLUniformCompletedEdgeTimeChange

set_option autoImplicit false
set_option warningAsError true

/-- The unique physical root edge assigned to virtual edge `edge` on an exact
`h * m = n` post-grid ring. -/
def rootCaptureSlot {n h m : Nat} (hh : 0 < h) (hfactor : h * m = n)
    (edge : Fin m) : Fin n :=
  ⟨h * edge.val, by
    rw [← hfactor]
    exact (Nat.mul_lt_mul_left hh).2 edge.isLt⟩

@[simp] theorem rootCaptureSlot_val {n h m : Nat} (hh : 0 < h)
    (hfactor : h * m = n) (edge : Fin m) :
    (rootCaptureSlot hh hfactor edge).val = h * edge.val := rfl

/-- Root capture slots are exactly position zero modulo the packed width. -/
@[simp] theorem rootCaptureSlot_mod {n h m : Nat} (hh : 0 < h)
    (hfactor : h * m = n) (edge : Fin m) :
    (rootCaptureSlot hh hfactor edge).val % h = 0 := by
  exact Nat.mul_mod_right h edge.val

/-- A successful raw service payload for one already selected virtual edge.
The dependent indices prevent a completion for another source or label from
being substituted at the interface. -/
structure CompletionAt
    {Free V : Type} {m : Nat}
    (project : Free → V) (virtualStep : V → Fin m → StopNode V)
    (source : Free) (edge : Fin m) where
  endpoint : StopNode Free
  projects : projectNode project endpoint = virtualStep (project source) edge

/-- If a completion is active, its payload is literally back in `Free`; no
separate postcommit/busy state is smuggled across the macro boundary. -/
theorem CompletionAt.active_reentersFree
    {Free V : Type} {m : Nat}
    {project : Free → V} {virtualStep : V → Fin m → StopNode V}
    {source : Free} {edge : Fin m}
    (completion : CompletionAt project virtualStep source edge)
    {next : Free} (hactive : completion.endpoint = .active next) :
    ∃ free : Free, completion.endpoint = .active free :=
  ⟨next, hactive⟩

/-- Exact capture plus separately charged service.

`capture_partition` is the finite child-occurrence statement for the fixed
root slots.  It is listed explicitly so a concrete position compiler must
prove the scheduler multiplicities rather than appeal to set cardinality.
`service_cost_le` is an every-horizon numerator bound in raw interactions;
it does not count one macro step as one raw interaction.
-/
structure CaptureCompiler
    {Free V : Type} (n h m serviceBound : Nat)
    (virtualStep : V → Fin m → StopNode V) where
  width_pos : 0 < h
  factor : h * m = n
  project : Free → V
  captureOwner : Fin n → Option (Fin m)
  capture_root_iff : ∀ raw edge,
    captureOwner raw = some edge ↔
      raw = rootCaptureSlot width_pos factor edge
  capture_partition : ∀ (edgeWeight : Fin m → Nat) (retryWeight : Nat),
    (List.ofFn (fun raw : Fin n ↦
      match captureOwner raw with
      | some edge => edgeWeight edge
      | none => retryWeight)).sum =
      (List.ofFn edgeWeight).sum + (n - m) * retryWeight
  Pending : Free → Fin m → Type
  serviceStep : ∀ source edge,
    Pending source edge → Fin n →
      PayloadNode (Pending source edge)
        (CompletionAt project virtualStep source edge) PEmpty
  serviceInitial : ∀ source edge,
    PayloadNode (Pending source edge)
      (CompletionAt project virtualStep source edge) PEmpty
  service_no_failure : ∀ source edge T,
    failureMass (serviceStep source edge) (serviceInitial source edge) T = 0
  service_cost_le : ∀ source edge T,
    truncatedActiveCostNumerator
        (eraseStep (serviceStep source edge))
        (serviceInitial source edge).erase T ≤
      n ^ T * serviceBound

theorem CaptureCompiler.virtualEdges_le_raw
    {Free V : Type} {n h m serviceBound : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep) :
    m ≤ n := by
  rw [← compiler.factor]
  exact Nat.le_mul_of_pos_left m compiler.width_pos

/-- The fixed capture fiber of each virtual edge is a singleton. -/
theorem CaptureCompiler.capture_fiber_one
    {Free V : Type} {n h m serviceBound : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep)
    (edge : Fin m) :
    ∃ raw : Fin n, compiler.captureOwner raw = some edge ∧
      ∀ other : Fin n, compiler.captureOwner other = some edge →
        other = raw := by
  let root := rootCaptureSlot compiler.width_pos compiler.factor edge
  refine ⟨root, (compiler.capture_root_iff root edge).2 rfl, ?_⟩
  intro other hother
  exact (compiler.capture_root_iff other edge).1 hother

/-- Proof-side capture child at a free macro node.  Internal service is absent
from this one-draw kernel and is accounted for by `service_cost_le`. -/
def CaptureCompiler.macroCaptureChild
    {Free V : Type} {n h m serviceBound : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep)
    (source : Free) (raw : Fin n) : StopNode V :=
  match compiler.captureOwner raw with
  | some edge => virtualStep (compiler.project source) edge
  | none => .active (compiler.project source)

/-- Exact child-occurrence identity at a free capture boundary: one child per
virtual edge and `n-m` retries. -/
theorem CaptureCompiler.macroCaptureChild_sum
    {Free V : Type} {n h m serviceBound : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep)
    (source : Free) (weight : StopNode V → Nat) :
    (List.ofFn (fun raw : Fin n ↦
      weight (compiler.macroCaptureChild source raw))).sum =
      (List.ofFn (fun edge : Fin m ↦
        weight (virtualStep (compiler.project source) edge))).sum +
      (n - m) * weight (.active (compiler.project source)) := by
  rw [show (List.ofFn (fun raw : Fin n ↦
      weight (compiler.macroCaptureChild source raw))).sum =
      (List.ofFn (fun raw : Fin n ↦
        match compiler.captureOwner raw with
        | some edge => weight (virtualStep (compiler.project source) edge)
        | none => weight (.active (compiler.project source)))).sum by
    apply ofFn_sum_eq
    intro raw
    unfold CaptureCompiler.macroCaptureChild
    cases howner : compiler.captureOwner raw <;> simp]
  exact compiler.capture_partition
    (fun edge ↦ weight (virtualStep (compiler.project source) edge))
    (weight (.active (compiler.project source)))

/-- Bellman inequality at free macro nodes only.  Busy service nodes carry a
zero virtual toll and use the separate service certificate; applying this
statement to every raw service state would contradict
`UniformCoreSafeRemainder.no_stutter_only_state`. -/
theorem CaptureCompiler.free_capture_bellman
    {Free V : Type} {n h m serviceBound scale : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep)
    (potential : StopNode V → Nat)
    (hvirtual : NatBellmanSuperSolution virtualStep scale potential)
    (source : Free) :
    scale * m +
        (List.ofFn (fun raw : Fin n ↦
          potential (compiler.macroCaptureChild source raw))).sum ≤
      n * potential (.active (compiler.project source)) := by
  let value := potential (.active (compiler.project source))
  let childSum := (List.ofFn (fun edge : Fin m ↦
    potential (virtualStep (compiler.project source) edge))).sum
  have hvirtualStep : scale * m + childSum ≤ m * value :=
    hvirtual.2.2 (compiler.project source)
  have hmle := compiler.virtualEdges_le_raw
  have hdecompose : m + (n - m) = n := Nat.add_sub_of_le hmle
  rw [compiler.macroCaptureChild_sum source potential]
  calc
    scale * m + (childSum + (n - m) * value) =
        (scale * m + childSum) + (n - m) * value := by omega
    _ ≤ m * value + (n - m) * value :=
      Nat.add_le_add_right hvirtualStep _
    _ = n * value := by
      rw [← Nat.add_mul, hdecompose]

/-! ## Endpoint-retaining capture/service composition -/

/-- First-hit capture tree.  A non-root raw coordinate retries at the same
free boundary; a root coordinate returns its exact virtual edge label. -/
def CaptureCompiler.captureStep
    {Free V : Type} {n h m serviceBound : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep) :
    Unit → Fin n → PayloadNode Unit (Fin m) PEmpty :=
  fun _ raw =>
    match compiler.captureOwner raw with
    | some edge => .success edge
    | none => .active ()

private def capturePotential (n : Nat) : StopNode Unit → Nat
  | .active _ => n
  | .success => 0
  | .failure => 0

/-- The expected raw wait to one of the `m` root capture edges is `n/m`, in
division-free form. -/
theorem CaptureCompiler.capture_truncatedCost_mul_virtualEdges_le
    {Free V : Type} {n h m serviceBound T : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep) :
    m * truncatedActiveCostNumerator
        (eraseStep compiler.captureStep) (.active ()) T ≤
      n ^ T * n := by
  have hsuper : NatBellmanSuperSolution
      (eraseStep compiler.captureStep) m (capturePotential n) := by
    refine ⟨rfl, rfl, ?_⟩
    intro state
    have hsum :
        (List.ofFn (fun raw : Fin n ↦
          capturePotential n
            (eraseStep compiler.captureStep state raw))).sum =
          (n - m) * n := by
      rw [show (List.ofFn (fun raw : Fin n ↦
          capturePotential n
            (eraseStep compiler.captureStep state raw))).sum =
          (List.ofFn (fun raw : Fin n ↦
            match compiler.captureOwner raw with
            | some _ => 0
            | none => n)).sum by
        apply ofFn_sum_eq
        intro raw
        cases howner : compiler.captureOwner raw <;>
          simp [CaptureCompiler.captureStep, eraseStep,
            PayloadNode.erase, capturePotential, howner]]
      simpa [ofFn_sum_const] using
        compiler.capture_partition (fun _ ↦ 0) n
    change m * n +
        (List.ofFn (fun raw : Fin n ↦
          capturePotential n
            (eraseStep compiler.captureStep state raw))).sum ≤ n * n
    rw [hsum]
    have hdecompose : m + (n - m) = n :=
      Nat.add_sub_of_le compiler.virtualEdges_le_raw
    calc
      m * n + (n - m) * n =
          (m + (n - m)) * n := by rw [Nat.add_mul]
      _ = n * n := by rw [hdecompose]
      _ ≤ n * n := Nat.le_refl _
  exact truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (eraseStep compiler.captureStep) m (capturePotential n) hsuper
      (.active ()) T

/-- Local copy of the endpoint-retaining first-terminal bound. -/
private theorem firstTerminalBindMass_le_uniform
    {A S F : Type} {n U budget : Nat}
    (step : A → Fin n → PayloadNode A S F)
    (continuation : S → Nat)
    (hcontinuation : ∀ endpoint,
      continuation endpoint ≤ n ^ U * budget) :
    ∀ (node : PayloadNode A S F) T,
      firstTerminalBindMass step continuation node T ≤
        n ^ (T + U) * budget := by
  intro node T
  induction T generalizing node with
  | zero =>
      cases node with
      | active state => simp [firstTerminalBindMass]
      | failure endpoint => simp [firstTerminalBindMass]
      | success endpoint =>
          simpa [firstTerminalBindMass] using hcontinuation endpoint
  | succ T ih =>
      cases node with
      | failure endpoint => simp [firstTerminalBindMass]
      | success endpoint =>
          have hmul := Nat.mul_le_mul_left (n ^ (T + 1))
            (hcontinuation endpoint)
          simpa [firstTerminalBindMass, Nat.pow_add, Nat.mul_assoc] using hmul
      | active state =>
          simp only [firstTerminalBindMass]
          calc
            (List.ofFn (fun raw : Fin n ↦
                firstTerminalBindMass step continuation
                  (step state raw) T)).sum ≤
                (List.ofFn (fun _ : Fin n ↦
                  n ^ (T + U) * budget)).sum :=
              ofFn_sum_le _ _ (fun raw ↦ ih (step state raw))
            _ = n * (n ^ (T + U) * budget) :=
              ofFn_sum_const n _
            _ = n ^ ((T + 1) + U) * budget := by
              rw [show (T + 1) + U = (T + U) + 1 by omega,
                Nat.pow_succ]
              ac_rfl

private def stageCostNumerator
    {A S F : Type} {n : Nat}
    (step : A → Fin n → PayloadNode A S F)
    (continuation : S → Nat) (node : PayloadNode A S F)
    (T U : Nat) : Nat :=
  truncatedActiveCostNumerator (eraseStep step) node.erase T * n ^ U +
    firstTerminalBindMass step continuation node T

private theorem stageCostNumerator_le
    {A S F : Type} {n T U firstBudget continuationBudget : Nat}
    (step : A → Fin n → PayloadNode A S F)
    (continuation : S → Nat) (node : PayloadNode A S F)
    (hfirst : truncatedActiveCostNumerator (eraseStep step) node.erase T ≤
      n ^ T * firstBudget)
    (hcontinuation : ∀ endpoint,
      continuation endpoint ≤ n ^ U * continuationBudget) :
    stageCostNumerator step continuation node T U ≤
      n ^ (T + U) * (firstBudget + continuationBudget) := by
  have hfirstPadded := Nat.mul_le_mul_right (n ^ U) hfirst
  have hbind := firstTerminalBindMass_le_uniform
    step continuation hcontinuation node T
  unfold stageCostNumerator
  calc
    truncatedActiveCostNumerator (eraseStep step) node.erase T * n ^ U +
        firstTerminalBindMass step continuation node T ≤
      (n ^ T * firstBudget) * n ^ U +
        n ^ (T + U) * continuationBudget :=
      Nat.add_le_add hfirstPadded hbind
    _ = n ^ (T + U) * (firstBudget + continuationBudget) := by
      rw [Nat.pow_add, Nat.mul_add]
      ac_rfl

/-- Service cost followed by a continuation at the literal completion node.
The continuation receives `completion.endpoint`, not a reconstructed virtual
or canonical physical state. -/
def CaptureCompiler.serviceThenContinuationCost
    {Free V : Type} {n h m serviceBound : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep)
    (source : Free) (edge : Fin m)
    (continuation : StopNode Free → Nat) (U W : Nat) : Nat :=
  stageCostNumerator (compiler.serviceStep source edge)
    (fun completion ↦ continuation completion.endpoint)
    (compiler.serviceInitial source edge) U W

/-- Capture retry cost followed by the edge-indexed raw service tree and then
the actual-endpoint continuation. -/
def CaptureCompiler.captureServiceContinuationCost
    {Free V : Type} {n h m serviceBound : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep)
    (source : Free) (continuation : StopNode Free → Nat)
    (T U W : Nat) : Nat :=
  stageCostNumerator compiler.captureStep
    (fun edge ↦ compiler.serviceThenContinuationCost
      source edge continuation U W)
    (.active ()) T (U + W)

/-- Full division-free one-macro composition.  Capture contributes `n/m` raw
interactions, service contributes `serviceBound`, and the continuation begins
at the retained physical completion endpoint. -/
theorem CaptureCompiler.captureServiceContinuationCost_mul_virtualEdges_le
    {Free V : Type} {n h m serviceBound T U W continuationBudget : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep)
    (source : Free) (continuation : StopNode Free → Nat)
    (hcontinuation : ∀ endpoint,
      continuation endpoint ≤ n ^ W * continuationBudget) :
    m * compiler.captureServiceContinuationCost
        source continuation T U W ≤
      n ^ (T + (U + W)) *
        (n + m * (serviceBound + continuationBudget)) := by
  have hservice : ∀ edge,
      compiler.serviceThenContinuationCost source edge continuation U W ≤
        n ^ (U + W) * (serviceBound + continuationBudget) := by
    intro edge
    exact stageCostNumerator_le
      (compiler.serviceStep source edge)
      (fun completion ↦ continuation completion.endpoint)
      (compiler.serviceInitial source edge)
      (compiler.service_cost_le source edge U)
      (fun completion ↦ hcontinuation completion.endpoint)
  have hbind := firstTerminalBindMass_le_uniform
    compiler.captureStep
    (fun edge ↦ compiler.serviceThenContinuationCost
      source edge continuation U W)
    hservice (.active ()) T
  have hcapture := compiler.capture_truncatedCost_mul_virtualEdges_le
    (T := T)
  have hcapturePadded := Nat.mul_le_mul_right (n ^ (U + W)) hcapture
  unfold CaptureCompiler.captureServiceContinuationCost stageCostNumerator
  have hbindScaled := Nat.mul_le_mul_left m hbind
  calc
    m * (truncatedActiveCostNumerator
          (eraseStep compiler.captureStep) (.active ()) T * n ^ (U + W) +
        firstTerminalBindMass compiler.captureStep
          (fun edge ↦ compiler.serviceThenContinuationCost
            source edge continuation U W) (.active ()) T) =
      (m * truncatedActiveCostNumerator
          (eraseStep compiler.captureStep) (.active ()) T) * n ^ (U + W) +
        m * firstTerminalBindMass compiler.captureStep
          (fun edge ↦ compiler.serviceThenContinuationCost
            source edge continuation U W) (.active ()) T := by
      rw [Nat.mul_add]
      congr 1
      ac_rfl
    _ ≤ (n ^ T * n) * n ^ (U + W) +
        m * (n ^ (T + (U + W)) *
          (serviceBound + continuationBudget)) :=
      Nat.add_le_add hcapturePadded hbindScaled
    _ = n ^ (T + (U + W)) *
        (n + m * (serviceBound + continuationBudget)) := by
      simp only [Nat.pow_add, Nat.mul_add]
      ac_rfl

/-- Using `n = h*m`, the normalized total is exactly bounded by
`h + serviceBound + continuationBudget`. -/
theorem CaptureCompiler.captureServiceContinuationCost_le_width_add
    {Free V : Type} {n h m serviceBound T U W continuationBudget : Nat}
    {virtualStep : V → Fin m → StopNode V}
    (compiler : CaptureCompiler (Free := Free)
      n h m serviceBound virtualStep)
    (hm : 0 < m) (source : Free)
    (continuation : StopNode Free → Nat)
    (hcontinuation : ∀ endpoint,
      continuation endpoint ≤ n ^ W * continuationBudget) :
    compiler.captureServiceContinuationCost source continuation T U W ≤
      n ^ (T + (U + W)) *
        (h + serviceBound + continuationBudget) := by
  have hmain :=
    compiler.captureServiceContinuationCost_mul_virtualEdges_le
      (T := T) (U := U) (W := W)
      (continuationBudget := continuationBudget)
      source continuation hcontinuation
  have hbudget : n + m * (serviceBound + continuationBudget) =
      m * (h + serviceBound + continuationBudget) := by
    rw [← compiler.factor]
    simp [Nat.mul_add]
    ac_rfl
  rw [hbudget] at hmain
  have hscaled : m *
      compiler.captureServiceContinuationCost source continuation T U W ≤
      m * (n ^ (T + (U + W)) *
        (h + serviceBound + continuationBudget)) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmain
  exact Nat.le_of_mul_le_mul_left hscaled hm

#print axioms rootCaptureSlot_mod
#print axioms CaptureCompiler.capture_fiber_one
#print axioms CaptureCompiler.macroCaptureChild_sum
#print axioms CaptureCompiler.free_capture_bellman
#print axioms CaptureCompiler.capture_truncatedCost_mul_virtualEdges_le
#print axioms CaptureCompiler.captureServiceContinuationCost_mul_virtualEdges_le
#print axioms CaptureCompiler.captureServiceContinuationCost_le_width_add

end PPLLCaptureStoppedCompiler

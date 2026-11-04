import Leader.Wu.ShortGap.ChoiceStopping

/-!
# Denial transport across a gap as an explicit stop-and-wait token walk

This file is an explicit token-walk quotient of one denial transport.  It
refines the macro rearm service of `Leader/Wu/ShortGap/ChoiceRestart.lean`, where
one scheduler edge cleared a whole root, into a radius-one carrier that has to
be scheduled once per physical hop.

**Model.**  A gap is a directed physical path of length `h ≥ 1` between a left
root at position `0` and a right root at position `h`.  Its `h` physical edges
are `edgeAt 0, …, edgeAt (h-1)`, where `edgeAt k` joins positions `k` and
`k+1`; the responder of a directed edge is its right endpoint.  One gap runs
through three phases:

1. `declareRight k` (`k < h`): the left root's declaration token sits at
   position `k` and moves clockwise when `edgeAt k` is scheduled.  When the
   token crosses `edgeAt (h-1)` it arrives at the right root, which compares
   it with its own held declaration.
2. The comparison outcome in this file is fixed to a denial (the uniform
   word); the right root holds its receipt and emits a denial token at
   position `h` that moves counterclockwise: `denyLeft k` with `1 ≤ k ≤ h`
   moves to `k-1` when `edgeAt (k-1)` is scheduled.
3. `denyLeft 0`: the left root has received its denial receipt and the gap is
   discharged.

Exactly one scheduler edge advances the carrier of an active gap; every other
edge leaves that gap unchanged.  `m` gaps are run together on `n` scheduler
edges through a `GapLayout` whose edge assignment is injective, so one physical
edge advances at most one gap's carrier.  The service stops in `.success` when
every gap has been discharged and never exposes `.failure`.

**Bound.**  The potential `n * (total remaining hops)` is a
`NatBellmanSuperSolution` with scale `1`; a fresh layout of `m` gaps of length
`h` starts at `n * (m * (2*h))`.  Through `CandidateRearmSpec` this gives a
truncated expected-work numerator of at most `n^T * (2*(n*m)*(1+h))` for
repeated candidate rounds with token-walk rearm.

**Abstraction boundary.**  The file models only the uniform (all-denial)
outcome; the declaration/denial token is a single message carrier with no
forgery, staleness, or interference from unrelated rows; the shared endpoint
root between adjacent gaps is reflected only through disjoint edge sets, not
through a shared-root two-receipt join.  That join lives in the companion file
`Leader/Wu/ShortGap/TwoDenialRearm.lean` (built concurrently, not imported here).
The gap edge sets are given abstractly by an injective `edgeAt`; the file does
not derive them from `Placement.physicalRing` arithmetic.  Nothing here claims
complete leader stabilization or a final complexity bound.
-/

namespace ShortGapDenialTransport

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping

set_option autoImplicit false

private theorem ofFn_sum_lt_of_single_lt
    {n : Nat} (f g : Fin n → Nat) (chosen : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        let previous : Fin n := ⟨chosen.val - 1, by omega⟩
        have hsucc : previous.succ = chosen :=
          Fin.ext (by simp [previous]; omega)
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i => g i.succ) previous
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

/-! ## One gap -/

/-- Phase and position of the single message carrier of one gap of physical
length `h`.  `declareRight k` is the declaration token at position `k < h`
moving toward the right root; `denyLeft k` is the denial token at position
`k ≤ h` moving toward the left root; `denyLeft 0` is the discharged gap. -/
inductive GapDenialState (h : Nat) where
  | declareRight (k : Nat) (hk : k < h)
  | denyLeft (k : Nat) (hk : k ≤ h)

namespace GapDenialState

/-- Remaining carrier hops before the left root receives its denial. -/
def hops {h : Nat} : GapDenialState h → Nat
  | declareRight k _ => (h - k) + h
  | denyLeft k _ => k

/-- The unique gap edge whose scheduling advances the carrier, if any.  A
rightward token at `k` crosses `edgeAt k`; a leftward token at `k+1` crosses
`edgeAt k` (radius one: the edge's endpoints are `k` and `k+1`). -/
def advanceEdge {h : Nat} : GapDenialState h → Option (Fin h)
  | declareRight k hk => some ⟨k, hk⟩
  | denyLeft 0 _ => none
  | denyLeft (k + 1) hk => some ⟨k, by omega⟩

/-- Effect of scheduling the advancing edge.  Arrival at the right root is
folded into the last rightward hop: the right root compares, keeps its
receipt, and the denial token starts at position `h`. -/
def advance {h : Nat} : GapDenialState h → GapDenialState h
  | declareRight k hk =>
      if hk' : k + 1 < h then declareRight (k + 1) hk'
      else denyLeft h (Nat.le_refl h)
  | denyLeft 0 hk => denyLeft 0 hk
  | denyLeft (k + 1) _ => denyLeft k (by omega)

theorem advanceEdge_of_hops_pos {h : Nat} (s : GapDenialState h)
    (hpos : 0 < s.hops) : ∃ a, s.advanceEdge = some a := by
  cases s with
  | declareRight k hk => exact ⟨⟨k, hk⟩, rfl⟩
  | denyLeft k hk =>
      cases k with
      | zero => simp [hops] at hpos
      | succ k => exact ⟨⟨k, by omega⟩, rfl⟩

/-- The advancing edge lowers the remaining hops by exactly one. -/
theorem hops_advance_of_some {h : Nat} (s : GapDenialState h) (a : Fin h)
    (ha : s.advanceEdge = some a) : s.advance.hops + 1 = s.hops := by
  cases s with
  | declareRight k hk =>
      simp only [advance]
      split <;> simp only [hops] <;> omega
  | denyLeft k hk =>
      cases k with
      | zero => simp [advanceEdge] at ha
      | succ k => rfl

/-- One scheduler edge acting on one gap whose physical edges are `edgeAt`. -/
def localStep {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : GapDenialState h) (e : Fin n) : GapDenialState h :=
  match s.advanceEdge with
  | some a => if edgeAt a = e then s.advance else s
  | none => s

theorem hops_localStep_le {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : GapDenialState h) (e : Fin n) :
    (localStep edgeAt s e).hops ≤ s.hops := by
  unfold localStep
  split
  · rename_i a ha
    split
    · have := hops_advance_of_some s a ha
      omega
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem localStep_advanceEdge {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : GapDenialState h) (a : Fin h) (ha : s.advanceEdge = some a) :
    localStep edgeAt s (edgeAt a) = s.advance := by
  simp [localStep, ha]

theorem hops_localStep_advance {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : GapDenialState h) (a : Fin h) (ha : s.advanceEdge = some a) :
    (localStep edgeAt s (edgeAt a)).hops + 1 = s.hops := by
  rw [localStep_advanceEdge edgeAt s a ha]
  exact hops_advance_of_some s a ha

/-- Every edge other than the advancing edge leaves the gap unchanged. -/
theorem localStep_eq_of_ne {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : GapDenialState h) (e : Fin n)
    (hne : ∀ a, s.advanceEdge = some a → edgeAt a ≠ e) :
    localStep edgeAt s e = s := by
  unfold localStep
  split
  · rename_i a ha
    rw [if_neg (hne a ha)]
  · rfl

end GapDenialState

/-! ## `m` gaps on disjoint edge sets -/

/-- Physical layout of `m` gaps of length `h` on `n` scheduler edges.  Gap
`g` owns edges `edgeAt g 0, …, edgeAt g (h-1)` in clockwise order; the
assignment is injective, so one physical edge advances at most one carrier.

Injectivity is on the pair `(gap, position)`, i.e. `edgeAt` is an injection
`Fin m × Fin h ↪ Fin n`; a `GapLayout n h m` therefore presupposes `m*h ≤ n`,
and for `n < m*h` no layout exists, so every statement below quantified over
one is vacuous.  On a ring tiled by `m` uniform gaps this holds with
equality. -/
structure GapLayout (n h m : Nat) where
  hpos : 0 < h
  edgeAt : Fin m → Fin h → Fin n
  edgeAt_injective : ∀ g a g' a', edgeAt g a = edgeAt g' a' → g = g' ∧ a = a'

/-- One gap of length `h` whose `h` physical edges are given injectively. -/
def GapLayout.single {n h : Nat} (hpos : 0 < h) (edgeAt : Fin h → Fin n)
    (hinj : Function.Injective edgeAt) : GapLayout n h 1 where
  hpos := hpos
  edgeAt := fun _ a => edgeAt a
  edgeAt_injective := fun g _ g' _ heq => ⟨Subsingleton.elim g g', hinj heq⟩

/-- Joint carrier state with at least one gap still in transit. -/
structure MultiGapState (h m : Nat) where
  gap : Fin m → GapDenialState h
  hasActive : ∃ g, 0 < (gap g).hops

/-- Total remaining carrier hops over all gaps. -/
def totalHops {h m : Nat} (gap : Fin m → GapDenialState h) : Nat :=
  (List.ofFn (fun g => (gap g).hops)).sum

/-- One scheduler edge acting on every gap through its own edge set. -/
def multiLocalStep {n h m : Nat} (L : GapLayout n h m)
    (gap : Fin m → GapDenialState h) (e : Fin n) :
    Fin m → GapDenialState h :=
  fun g => GapDenialState.localStep (L.edgeAt g) (gap g) e

theorem totalHops_multiLocalStep_le {n h m : Nat} (L : GapLayout n h m)
    (gap : Fin m → GapDenialState h) (e : Fin n) :
    totalHops (multiLocalStep L gap e) ≤ totalHops gap :=
  ofFn_sum_le _ _
    (fun g => GapDenialState.hops_localStep_le (L.edgeAt g) (gap g) e)

/-- The advancing edge of any in-transit gap strictly lowers the total. -/
theorem totalHops_multiLocalStep_lt {n h m : Nat} (L : GapLayout n h m)
    (gap : Fin m → GapDenialState h) (g : Fin m) (a : Fin h)
    (ha : (gap g).advanceEdge = some a) :
    totalHops (multiLocalStep L gap (L.edgeAt g a)) < totalHops gap := by
  apply ofFn_sum_lt_of_single_lt _ _ g
  · intro g'
    exact GapDenialState.hops_localStep_le (L.edgeAt g') (gap g') _
  · have := GapDenialState.hops_localStep_advance (L.edgeAt g) (gap g) a ha
    show (multiLocalStep L gap (L.edgeAt g a) g).hops < (gap g).hops
    simp only [multiLocalStep]
    omega

/-- A gap's advancing edge leaves every other gap unchanged. -/
theorem multiLocalStep_other {n h m : Nat} (L : GapLayout n h m)
    (gap : Fin m → GapDenialState h) (g g' : Fin m) (hne : g' ≠ g)
    (a : Fin h) :
    multiLocalStep L gap (L.edgeAt g a) g' = gap g' := by
  apply GapDenialState.localStep_eq_of_ne
  intro a' _ heq
  exact hne (L.edgeAt_injective g' a' g a heq).1

/-- The token-walk rearm service stops only after every gap is discharged. -/
noncomputable def multiGapStep {n h m : Nat} (L : GapLayout n h m) :
    MultiGapState h m → Fin n → StopNode (MultiGapState h m) :=
  fun state edge =>
    let next := multiLocalStep L state.gap edge
    if hnext : ∃ g, 0 < (next g).hops then
      .active ⟨next, hnext⟩
    else .success

def multiGapPotential {n h m : Nat} :
    StopNode (MultiGapState h m) → Nat
  | .active state => n * totalHops state.gap
  | .success => 0
  | .failure => 0

private theorem multiGapPotential_step_le
    {n h m : Nat} (L : GapLayout n h m)
    (state : MultiGapState h m) (edge : Fin n) :
    multiGapPotential (n := n) (multiGapStep L state edge) ≤
      n * totalHops (multiLocalStep L state.gap edge) := by
  classical
  simp only [multiGapStep]
  split <;> simp [multiGapPotential]

/-- The exact child-sum inequality for remaining carrier hops. -/
theorem totalHops_childSum {n h m : Nat} (L : GapLayout n h m)
    (state : MultiGapState h m) :
    1 + (List.ofFn (fun edge : Fin n =>
      totalHops (multiLocalStep L state.gap edge))).sum ≤
        n * totalHops state.gap := by
  obtain ⟨g, hg⟩ := state.hasActive
  obtain ⟨a, ha⟩ := GapDenialState.advanceEdge_of_hops_pos _ hg
  have hsumlt := ofFn_sum_lt_of_single_lt
    (fun edge : Fin n => totalHops (multiLocalStep L state.gap edge))
    (fun _ : Fin n => totalHops state.gap) (L.edgeAt g a)
    (fun edge => totalHops_multiLocalStep_le L state.gap edge)
    (totalHops_multiLocalStep_lt L state.gap g a ha)
  rw [ofFn_sum_const] at hsumlt
  omega

/-- The token-walk rearm service has expected work at most `n` times the
initial total number of carrier hops. -/
theorem multiGap_natBellmanSuperSolution
    {n h m : Nat} (L : GapLayout n h m) :
    NatBellmanSuperSolution (multiGapStep L) 1
      (multiGapPotential (n := n)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hdebt := totalHops_childSum L state
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        multiGapPotential (n := n) (multiGapStep L state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.gap edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          multiGapPotential (n := n) (multiGapStep L state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          n * totalHops (multiLocalStep L state.gap edge))).sum := by
            apply ofFn_sum_le
            intro edge
            exact multiGapPotential_step_le L state edge
      _ = n * (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.gap edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        multiGapPotential (n := n) (multiGapStep L state edge))).sum ≤
      n + n * (List.ofFn (fun edge : Fin n =>
        totalHops (multiLocalStep L state.gap edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
        totalHops (multiLocalStep L state.gap edge))).sum) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * totalHops state.gap) := hscaled
    _ = n * multiGapPotential (n := n) (.active state) := rfl

theorem multiGapStep_ne_failure {n h m : Nat} (L : GapLayout n h m) :
    ∀ state edge, multiGapStep L state edge ≠ .failure := by
  classical
  intro state edge
  simp only [multiGapStep]
  split <;> simp

/-- Every gap starts with its left root's declaration at position `0`. -/
def allDeclareStart {n h m : Nat} (L : GapLayout n h m) (hm : 0 < m) :
    MultiGapState h m :=
  ⟨fun _ => .declareRight 0 L.hpos,
    ⟨⟨0, hm⟩, by
      have := L.hpos
      simp only [GapDenialState.hops]
      omega⟩⟩

@[simp] theorem totalHops_allDeclare {h m : Nat} (hpos : 0 < h) :
    totalHops (fun _ : Fin m => GapDenialState.declareRight 0 hpos) =
      m * (2 * h) := by
  simp only [totalHops, GapDenialState.hops, ofFn_sum_const, Nat.sub_zero,
    Nat.two_mul]

@[simp] theorem multiGapPotential_allDeclare
    {n h m : Nat} (L : GapLayout n h m) (hm : 0 < m) :
    multiGapPotential (n := n) (.active (allDeclareStart L hm)) =
      n * (m * (2 * h)) := by
  simp [multiGapPotential, allDeclareStart]

/-- Token-walk implementation of the candidate rearm interface for `m` gaps
of physical length `h` on disjoint edge sets. -/
noncomputable def multiGapDenialRearmSpec
    {n h m : Nat} (L : GapLayout n h m) (hm : 0 < m) :
    CandidateRearmSpec n where
  State := MultiGapState h m
  step := multiGapStep L
  start := allDeclareStart L hm
  potential := multiGapPotential (n := n)
  bellman := multiGap_natBellmanSuperSolution L
  noFailure := multiGapStep_ne_failure L

/-- Complete candidate process with token-walk rearm: bare incidence choice,
charged denial transport across every gap, and repetition until the first
persistent candidate. -/
noncomputable def multiGapCandidateRestartStep
    {n h m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (L : GapLayout n h m) (hm : 0 < m) :=
  (multiGapDenialRearmSpec L hm).restartStep ring P hm

private theorem budget_eq (n h m : Nat) :
    2 * (n * m) * (1 + h) = 2 * (n * m) + n * (m * (2 * h)) := by
  rw [Nat.mul_add, Nat.mul_one]
  have hswap : n * (m * (2 * h)) = 2 * (n * m) * h := by ac_rfl
  rw [hswap]

/-- Repeated candidate rounds with token-walk rearm have expected work at
most `2*n*m*(1+h)`: two copies of `n*m` pay for the balanced candidate round
and `2*n*m*h` pays every carrier hop of the `m` gaps of length `h`. -/
theorem multiGapCandidateRestart_truncatedCost_le
    {n h m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m) (T : Nat) :
    truncatedActiveCostNumerator
        (multiGapCandidateRestartStep ring P L (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) * (1 + h)) := by
  have hcost :=
    (multiGapDenialRearmSpec L (by omega)).allRace_truncatedCost_le
      ring hm P hn T
  simp only [multiGapCandidateRestartStep, multiGapDenialRearmSpec,
    multiGapPotential_allDeclare] at hcost ⊢
  rw [budget_eq]
  exact hcost

/-- Exact reciprocal success tail for the complete token-walk process. -/
theorem multiGapCandidateRestart_success_one_minus_inv_factor
    {n h m factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m) :
    (factor - 1) * n ^ (factor * (2 * (n * m) * (1 + h))) ≤
      factor * successCount
        (multiGapCandidateRestartStep ring P L (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (2 * (n * m) * (1 + h))) := by
  have hsuccess :=
    CandidateRearmSpec.allRace_success_one_minus_inv_factor
      (multiGapDenialRearmSpec L (by omega)) ring hm P hn
      (factor := factor)
  simp only [multiGapCandidateRestartStep, multiGapDenialRearmSpec,
    multiGapPotential_allDeclare] at hsuccess ⊢
  rw [budget_eq]
  exact hsuccess

#print axioms GapDenialState.hops_advance_of_some
#print axioms multiLocalStep_other
#print axioms multiGap_natBellmanSuperSolution
#print axioms multiGapCandidateRestart_truncatedCost_le
#print axioms multiGapCandidateRestart_success_one_minus_inv_factor

end ShortGapDenialTransport

import Leader.Wu.Safety.ErasingRefinement
import Leader.Wu.Safety.OperationalLegitimacy

/-!
# Finite comparison-lineage refinement foundations

A comparison proof ghost must satisfy two independent requirements.  It must
be an exact erasing wrapper—never an executable CHECK guard—and it must not
certify arbitrary pre-existing `state`/`path`/`path2` fields merely because
their current values look coherent.

This file builds the reusable physical-first tagged adapter and the first
finite comparison tag.  The three trust bits are deliberately only a *local
field-provenance interface*: they do not yet identify a source group or imply
`CheckBoundarySafe`.  The final section proves why a pointwise local lift cannot
manufacture correct ring positions for identical physical states; source/target
route history therefore needs an edge-aware configuration layer or an
explicitly counted source identifier.
-/

namespace PPLLComparisonLifecycle

open PPLL PPLLRepair PPLLErasingRefinement PPLLRepairRegression
  PPLLOperationalLegitimacy

variable {Physical Ghost Output : Type}

/-! ## Generic physical-first tagged refinements -/

/-- A physical local state paired with proof-only ghost data.  The concrete
projection is the sole input to physical dynamics. -/
structure TaggedState (Physical Ghost : Type) where
  concrete : Physical
  ghost : Ghost
  deriving DecidableEq, Repr

namespace TaggedState

/-- Forget the proof tag. -/
def erase (s : TaggedState Physical Ghost) : Physical := s.concrete

/-- Total pointwise lift with a caller-selected canonical tag. -/
def lift (fresh : Physical → Ghost) (s : Physical) : TaggedState Physical Ghost :=
  ⟨s, fresh s⟩

@[simp] theorem erase_lift (fresh : Physical → Ghost) (s : Physical) :
    erase (lift fresh s) = s := by
  rfl

end TaggedState

/-- A ghost updater sees both tagged prestates and the already-computed physical
result, but returns only ghost data.  Its type prevents it from vetoing or
altering a physical branch. -/
abbrev GhostUpdate (Physical Ghost : Type) :=
  TaggedState Physical Ghost → TaggedState Physical Ghost →
    Physical × Physical → Ghost × Ghost

/-- Run the physical transition first and attach the updater's two proof tags. -/
def taggedTransition
    (T : Physical → Physical → Physical × Physical)
    (update : GhostUpdate Physical Ghost)
    (l r : TaggedState Physical Ghost) :
    TaggedState Physical Ghost × TaggedState Physical Ghost :=
  let q := T l.concrete r.concrete
  let g := update l r q
  (⟨q.1, g.1⟩, ⟨q.2, g.2⟩)

/-- Any ghost updater yields an exact local erasing refinement.  Configuration,
reachability, schedule, output, and safety projection are inherited from
`ErasingLocalRefinement`; this constructor intentionally does not duplicate
those inductions. -/
def mkTaggedRefinement
    (T : Physical → Physical → Physical × Physical)
    (out : Physical → Output) (fresh : Physical → Ghost)
    (update : GhostUpdate Physical Ghost) :
    ErasingLocalRefinement
      Physical (TaggedState Physical Ghost) Output T out where
  refinedTransition := taggedTransition T update
  refinedOutput := fun s => out s.concrete
  erase := TaggedState.erase
  lift := TaggedState.lift fresh
  erase_lift := by intro s; rfl
  transition_erases := by intro l r; exact ⟨rfl, rfl⟩
  output_erases := by intro s; rfl

/-! ## Finite field-provenance tags -/

/-- Independent causal trust flags for the three comparison fields.  Separate
bits are necessary because `path` and `path2` can coexist and move or be cleared
independently, while an arbitrary `MainState` can affect later CHECK behavior
even before a path arrives. -/
structure ComparisonTag where
  stateTrusted : Bool
  pathTrusted : Bool
  path2Trusted : Bool
  deriving DecidableEq, Repr

namespace ComparisonTag

/-- Canonical tag for arbitrary physical input: no active field receives trust
from its current shape alone. -/
def untrusted : ComparisonTag := ⟨false, false, false⟩

/-- Tag used only after all three field lineages have been justified. -/
def allTrusted : ComparisonTag := ⟨true, true, true⟩

/-- Constructive finite certificate for the eight possible trust triples. -/
def certificate : ExhaustiveList ComparisonTag :=
  ExhaustiveList.mapSurjective
    (ExhaustiveList.prod ExhaustiveList.bool
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool))
    (fun x =>
      ({ stateTrusted := x.1, pathTrusted := x.2.1,
         path2Trusted := x.2.2 } : ComparisonTag))
    (by
      intro t
      exact ⟨(t.stateTrusted, (t.pathTrusted, t.path2Trusted)),
        by cases t; rfl⟩)

end ComparisonTag

/-- Finite physical candidate paired with the finite comparison proof tag. -/
abbrev BoundedComparisonAgentState (ψ κ : Nat) :=
  TaggedState (BoundedAgentState ψ κ) ComparisonTag

/-- The tagged bounded local carrier remains constructively finite. -/
def boundedComparisonCertificate (ψ κ : Nat) :
    ExhaustiveList (BoundedComparisonAgentState ψ κ) :=
  ExhaustiveList.mapSurjective
    (ExhaustiveList.prod (PPLLFinite.boundedAgentState ψ κ)
      ComparisonTag.certificate)
    (fun x =>
      ({ concrete := x.1, ghost := x.2 } :
        BoundedComparisonAgentState ψ κ))
    (by
      intro s
      exact ⟨(s.concrete, s.ghost), by cases s; rfl⟩)

/-- Canonical total lift of the finite physical carrier. -/
def comparisonFresh (_s : BoundedAgentState ψ κ) : ComparisonTag :=
  ComparisonTag.untrusted

/-- Exact-erasing finite comparison refinement for an arbitrary ghost updater.
The updater can classify execution history but cannot influence the integrated
bounded physical result. -/
def boundedComparisonRefinement (hψ : ψ > 0) (κ : Nat)
    (update : GhostUpdate (BoundedAgentState ψ κ) ComparisonTag) :
    ErasingLocalRefinement
      (BoundedAgentState ψ κ) (BoundedComparisonAgentState ψ κ)
      LeaderOutput (integratedBoundedTransition hψ κ)
      (fun s => AgentState.outputFn (BoundedAgentState.erase s)) :=
  mkTaggedRefinement (integratedBoundedTransition hψ κ)
    (fun s => AgentState.outputFn (BoundedAgentState.erase s))
    comparisonFresh update

/-! ## Honest local trust obligations -/

/-- A neutral state has no state-lineage obligation; every active comparison
state requires explicit state provenance. -/
def StateTrustOK (s : BoundedComparisonAgentState ψ κ) : Prop :=
  s.concrete.erase.state = .none ∨ s.ghost.stateTrusted = true

/-- An absent comparison path has no provenance obligation; a present path
requires an authenticated lineage bit. -/
def PathTrustOK (s : BoundedComparisonAgentState ψ κ) : Prop :=
  s.concrete.erase.path = .bot ∨ s.ghost.pathTrusted = true

/-- The independently moving comparison-control carrier is treated separately
from `path`. -/
def Path2TrustOK (s : BoundedComparisonAgentState ψ κ) : Prop :=
  s.concrete.erase.path2 = none ∨ s.ghost.path2Trusted = true

/-- Local field-provenance interface.  This is intentionally weaker than a
source route and is not advertised as operational legitimacy. -/
def CarrierTrustOK (s : BoundedComparisonAgentState ψ κ) : Prop :=
  StateTrustOK s ∧ PathTrustOK s ∧ Path2TrustOK s

/-- A canonical lift is locally trusted exactly in the comparison-idle case.
This supplies an inhabited starting surface without certifying active garbage. -/
theorem fresh_carrierTrustOK_iff_idle (s : BoundedAgentState ψ κ) :
    CarrierTrustOK (TaggedState.lift comparisonFresh s) ↔
      s.erase.state = .none ∧ s.erase.path = .bot ∧ s.erase.path2 = none := by
  simp [CarrierTrustOK, StateTrustOK, PathTrustOK, Path2TrustOK,
    TaggedState.lift, comparisonFresh,
    ComparisonTag.untrusted]

/-- T1's canonical finite lift is representable but not trusted: its forged
comparison path cannot acquire provenance from total lifting. -/
theorem t1_canonical_lift_not_trusted :
    ¬(∀ i, CarrierTrustOK
      (TaggedState.lift comparisonFresh (t1FiniteConfig i))) := by
  intro h
  have hidle := (fresh_carrierTrustOK_iff_idle (t1FiniteConfig 2)).mp (h 2)
  have herase := congrFun erase_t1FiniteConfig 2
  change BoundedAgentState.erase (t1FiniteConfig 2) =
    PPLLCounterexample.counterConfig 2 at herase
  rw [herase] at hidle
  have hactive : (PPLLCounterexample.counterConfig 2).path ≠ .bot := by
    decide
  exact hactive hidle.2.1

/-- The latent R12 carrier is rejected for the same causal reason even though
its current CHECK boundary is harmless. -/
theorem latent_canonical_lift_not_trusted :
    ¬(∀ i, CarrierTrustOK
      (TaggedState.lift comparisonFresh (latentFiniteConfig i))) := by
  intro h
  have hidle := (fresh_carrierTrustOK_iff_idle
    (latentFiniteConfig 2)).mp (h 2)
  have herase := congrFun erase_latentFiniteConfig 2
  change BoundedAgentState.erase (latentFiniteConfig 2) = latentConfig 2 at herase
  rw [herase] at hidle
  have hactive : (latentConfig 2).path ≠ .bot := by
    decide
  exact hactive hidle.2.1

/-! ## Local anonymity cannot manufacture global positions -/

/-- A pointwise function of a local physical value cannot recover the correct
configuration index for every occurrence: a constant configuration presents
the same value at positions zero and one.  This rules out attaching a correct
`Fin n` source identity in the canonical local lift; it does not rule out
finite phase/taint ghosts or an edge-aware configuration history. -/
theorem no_pointwise_correct_positions {n : Nat} (hn : 1 < n)
    (x : Physical) (sourceId : Physical → Fin n) :
    ¬∀ (C : Fin n → Physical) (i : Fin n), sourceId (C i) = i := by
  intro h
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hi := h (fun _ => x) i
  have hj := h (fun _ => x) j
  have hij : i = j := hi.symm.trans hj
  have hval := congrArg Fin.val hij
  change 0 = 1 at hval
  omega

end PPLLComparisonLifecycle

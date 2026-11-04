import Leader.Wu.Coherence.SplitStepRefutation
import Leader.Wu.Coherence.SeekFork

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableFacts

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach

variable {n ψ κ τ : Nat}

/-- B-multi causal payload.  There is deliberately no wave-uniqueness clause
and no obligation at all on `.seek`.

* sweep: strict prefix is owned and main-clear;
* commit / sealed / release / scrubL: whole group is owned and main-clear;
* release / scrubL / openR: retain the structural mark/label clauses;
* openR: its freshness window is intrinsically fresh. -/
def ReachablePhaseFactsV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  (∀ i : Fin n, (C i).ctl.tok = .sweep →
      SweptPrefixOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .commit →
      GroupOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.mark = .sealed →
      GroupOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .release →
      (C i).ctl.mark = .releasing ∧
        GroupOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .scrubL →
      (C i).ctl.mark = .releasing ∧
        (raw (C i)).label.val ≠ 0 ∧
          GroupOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .openR →
      (C i).ctl.mark = .releasing ∧
        OpenROwnerFreshV3 ring C i)

instance reachablePhaseFactsV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (ReachablePhaseFactsV31 ring C) := by
  unfold ReachablePhaseFactsV31
  infer_instance

/-- Static projection from the old split into the new payload.  This theorem
is used only at the quarantine base case; no split-step closure is assumed. -/
theorem reachablePhaseFacts_of_split
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : QuarantineSplitV31 ring C) :
    ReachablePhaseFactsV31 ring C := by
  rcases h with ⟨hStruct, hPhase⟩
  rcases hStruct with ⟨hReleaseS, hScrubS, hOpenRS⟩
  rcases hPhase with
    ⟨hSweep, hCommit, hSealed, hReleaseP, hScrubP⟩
  refine ⟨hSweep, hCommit, hSealed, ?_, ?_, hOpenRS⟩
  · intro i hi
    exact ⟨hReleaseS i hi, hReleaseP i hi⟩
  · intro i hi
    rcases hScrubS i hi with ⟨hm, hz⟩
    exact ⟨hm, hz, hScrubP i hi⟩

/-- Exact reachable-domain certificate.  This is intentionally just the
already-installed quarantine reachability predicate under a B-multi name. -/
abbrev QuarantineTraceV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) : Prop :=
  ReachableFromQuarantineV31 hψ h2 ring C

/-- Target invariant: causal phase facts are required only on states carrying
an actual trace from a frozen `BirthEntranceV1`. -/
def ReachableSoundV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    QuarantineTraceV31 hψ h2 ring C →
      ReachablePhaseFactsV31 ring C

/-- Base case.  `BirthEntranceV1` exposes a state equal to
`quarantineInitV31 D`; all tokens are none and every mark is closing, so all
causal clauses are vacuous.  We reuse the already-certified initial split only
as a convenient static packaging of those facts. -/
theorem reachablePhaseFacts_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (hBirth : BirthEntranceV1 hψ h2 ring C) :
    ReachablePhaseFactsV31 ring C := by
  rcases hBirth.1 with ⟨_, D, _, hEq⟩
  rw [hEq]
  exact reachablePhaseFacts_of_split ring
    (quarantineInitV31 D) (quarantineInit_split ring D)

namespace SeekForkPayload

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩

/-- Literal restatement of the private physical fixture. -/
private def literal
    (lab : Fin 3) (leader : Bool := false) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
      leader := leader
      shield := leader
      gen_ws := false
      label := lab
      state := .none
      path := .bot
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false
  }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

private def preQ : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => ⟨literal 0 true,  ⟨.open, .none⟩⟩
  | 1 => ⟨literal 1 false, ⟨.open, .none⟩⟩
  | _ => ⟨literal 2 false, ⟨.open, .none⟩⟩

private def Q : FC 3 3 3 48 :=
  quarantineInitV31 preQ

private def Q1 : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 Q 0

private def Q2 : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 Q1 2

/-- Identification of the state: the two-seek fork really occurred. -/
theorem fork_two_seeks :
    (Q2 0).ctl.tok = .seek ∧
    (Q2 1).ctl.tok = .seek ∧
    (Q2 2).ctl.tok = .none := by
  decide +kernel

/-- The fork is *accepted* by B-multi.  Both non-none tokens are merely
`.seek`, which intentionally carries no debt in `ReachablePhaseFactsV31`;
there are no sweep/commit/release/scrubL/openR tokens or sealed marks. -/
theorem fork_reachablePhaseFacts :
    ReachablePhaseFactsV31 ring3 Q2 := by
  decide +kernel

/-- Combined closed certificate useful for the ledger. -/
theorem fork_two_seeks_and_facts :
    (Q2 0).ctl.tok = .seek ∧
    (Q2 1).ctl.tok = .seek ∧
    ReachablePhaseFactsV31 ring3 Q2 := by
  exact ⟨fork_two_seeks.1, fork_two_seeks.2.1,
    fork_reachablePhaseFacts⟩

end SeekForkPayload

/-- The causal payload statically implies the current controller shape.
This is the same projection pattern as `controllerShapeV3_of_split`, but it
uses only the per-front facts and therefore does not require the false global
split closure. -/
theorem reachablePhaseFacts_implies_shape
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : ReachablePhaseFactsV31 ring C) :
    ControllerShapeV3 ring C := by
  rcases h with
    ⟨_, _, hSealed, hRelease, hScrub, hOpenR⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    exact groupOwnedClear_mainClear ring C i (hSealed i hi)
  · intro i hi
    rcases hRelease i hi with ⟨hm, hg⟩
    exact ⟨hm, groupOwnedClear_mainClear ring C i hg⟩
  · intro i hi
    rcases hScrub i hi with ⟨hm, hz, hg⟩
    exact ⟨hm, hz, groupOwnedClear_mainClear ring C i hg⟩
  · intro i hi
    exact hOpenR i hi

/-- Final reduction.  Once the reachable-domain causal payload is proved for
all traces, every future word from every quarantine entrance has
`ControllerShapeV3`, exactly the definition of `ControllerSoundV3`. -/
theorem controllerSoundV3_of_reachableSound
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hSound : ReachableSoundV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    ∀ C0 : FC n ψ κ τ,
      BirthEntranceV1 hψ h2 ring C0 →
        ControllerSoundV3 hψ h2 ring C0 := by
  unfold ReachableSoundV31 at hSound
  intro C0 hBirth
  unfold ControllerSoundV3
  intro w
  exact reachablePhaseFacts_implies_shape ring _
    (hSound _ ⟨C0, w, hBirth, rfl⟩)

end R2CoherenceV31ReachableFacts

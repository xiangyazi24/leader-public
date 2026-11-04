import Leader.Wu.Birth.CheckPermitRepairLeaf
import Leader.Wu.Birth.CheckChainRing
import Leader.Wu.Birth.CheckChainPerBlock
import Leader.Wu.Birth.TwoStageEscape

set_option autoImplicit false

/-!
# Proof-only provenance lift

The physical cell is exactly `ExpiringAgentState`; erasure returns the
repository's `BirthCheckPermitRepairLeaf.FC`. The physical projection of
`taggedStep` is definitionally the literal R1 `step1`, with the same edge.
No tag is read to choose or modify a physical output.

The concrete observer convention is deliberately small: copy the sender's
metadata to a distinct, initially pathless receiver when the final physical
snapshot contains the sender's old nonempty path at that receiver and no
path at the sender; otherwise retain the existing metadata. This is a
copy-and-retain observer, not a GEN lifecycle census. In particular, this
file does not infer a true GEN event from a net path change, allocate GEN
identities, or claim that a snapshot match proves physical ancestry.
Source, serial, birth time, and uid are observer metadata, not certified
physical facts merely because they inhabit `Tag`. A later semantic observer
can refine `retag`; the erasure/count proofs do not unfold its definition.

`runTagged` uses `List.foldl`, the actual word-run convention used by
`BirthLeaderlessBirthMassRenewal`. The word inductions preserve every
prefix, including the initial and final endpoints. Consequently both
`aliveCount` and `BirthTwoStageEscape.avoidCount` are preserved exactly,
without a finite-state instance for the unbounded ghost carrier.

`ready_window_mass_of_tagged` exports precisely the physical stage-one
premise, requiring a tagged bound only from the canonical initial tagging
of each physical start. The final corollary plugs this into the existing
per-block reduction; it assumes, and does not prove, that mass bound.
-/

namespace B6ReadyMixGhost

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
open BirthCheckChainR1PerBlock BirthLeaderlessBirthMassRenewal
open BirthTwoStageEscape

variable {n ψ κ τ : Nat}

/-- Observer metadata. None of these fields belongs to the physical cell.
The intended interpretation of a noninitial tag must be supplied by a
separate provenance invariant, not by the erasure theorems. -/
structure Tag where
  /-- Generating segment index; `none` is used for initial material. -/
  source : Option Nat
  /-- Generation serial supplied by the observer. -/
  serial : Nat
  /-- Birth time supplied by the observer. -/
  birth : Nat
  /-- Payload identity supplied by the observer. -/
  uid : Nat
  deriving DecidableEq, Repr

/-- The actual cell type of `BirthCheckPermitRepairLeaf.FC`. -/
abbrev FCcell (ψ κ τ : Nat) := ExpiringAgentState ψ κ τ

/-- Unbounded proof-only metadata attached to the unchanged physical cells. -/
abbrev TaggedFC (n ψ κ τ : Nat) :=
  Fin n → (FCcell ψ κ τ × Tag)

/-- Forget all observer metadata. -/
def eraseFC (G : TaggedFC n ψ κ τ) : BirthCheckPermitRepairLeaf.FC n ψ κ τ :=
  fun i => (G i).1

/-- Initial-material metadata, with distinct cell-index identities. -/
def initialTag (i : Nat) : Tag :=
  { source := none, serial := 0, birth := 0, uid := i }

/-- Canonically tag any physical start; no reachability assumption is needed. -/
def initialTagged (C : BirthCheckPermitRepairLeaf.FC n ψ κ τ) : TaggedFC n ψ κ τ :=
  fun i => (C i, initialTag i.val)

theorem erase_initialTagged (C : BirthCheckPermitRepairLeaf.FC n ψ κ τ) :
    eraseFC (initialTagged C) = C := by
  funext i
  rfl

/-- A deterministic, transfer-only snapshot observer.

`D` is the already computed physical successor. The distinct-endpoint
condition also makes this convention unambiguous on a one-cell ring.
All metadata is retained unless the displayed net-transfer test succeeds.
This test is an observer convention, not a theorem identifying a GEN or
SIGMOVE event inside the composite physical row. -/
def retag (ring : DirectedRing n) (G : TaggedFC n ψ κ τ)
    (D : BirthCheckPermitRepairLeaf.FC n ψ κ τ) (e i : Fin n) : Tag :=
  if i = ring.rightNeighbor e ∧
      i ≠ e ∧
      (G e).1.core.erase.core.path ≠ .bot ∧
      (G i).1.core.erase.core.path = .bot ∧
      (D e).core.erase.core.path = .bot ∧
      (D i).core.erase.core.path = (G e).1.core.erase.core.path then
    (G e).2
  else
    (G i).2

/-- Apply the literal physical R1 step, then separately update the observer.
The first component does not depend on the result of `retag`. -/
def taggedStep (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (G : TaggedFC n ψ κ τ) (e : Fin n) : TaggedFC n ψ κ τ :=
  let D := step1 hψ h2 ring (eraseFC G) e
  fun i => (D i, retag ring G D e i)

/-- Exact one-letter erasure, for arbitrary observer metadata. -/
theorem erase_taggedStep (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (G : TaggedFC n ψ κ τ) (e : Fin n) :
    eraseFC (taggedStep hψ h2 ring G e) =
      step1 hψ h2 ring (eraseFC G) e := by
  funext i
  rfl

/-- In particular, changing only the tags cannot change a physical successor. -/
theorem erase_taggedStep_congr (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (G H : TaggedFC n ψ κ τ)
    (hGH : eraseFC G = eraseFC H) (e : Fin n) :
    eraseFC (taggedStep hψ h2 ring G e) =
      eraseFC (taggedStep hψ h2 ring H e) := by
  rw [erase_taggedStep, erase_taggedStep, hGH]

/-- The existing physical outside-the-served-pair frame is unchanged. -/
theorem erase_taggedStep_other (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (G : TaggedFC n ψ κ τ) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    eraseFC (taggedStep hψ h2 ring G e) i = eraseFC G i := by
  rw [erase_taggedStep]
  exact step1_other hψ h2 ring (eraseFC G) e i hi hj

/-- The repository's list-word run, on the tagged state space. -/
def runTagged (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (G : TaggedFC n ψ κ τ) (w : List (Fin n)) : TaggedFC n ψ κ τ :=
  w.foldl (taggedStep hψ h2 ring) G

/-- Erasure of every word run, using the actual `List.foldl` convention. -/
theorem erase_taggedRun (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (G : TaggedFC n ψ κ τ)
    (w : List (Fin n)) :
    eraseFC (runTagged hψ h2 ring G w) =
      w.foldl (step1 hψ h2 ring) (eraseFC G) := by
  unfold runTagged
  induction w generalizing G with
  | nil => rfl
  | cons e w ih =>
      simp only [List.foldl_cons]
      rw [ih, erase_taggedStep]

/-- Readiness inspects only the actual physical components of a window. -/
def TaggedReadyWindow (ring : DirectedRing n)
    (G : TaggedFC n ψ κ τ) : Prop :=
  ∃ s : Fin n, ∀ k, k < ψ → ReadyCell k ((G (cell ring s k)).1)

/-- No source-coherence or tag condition has been added to `ReadyWindow`. -/
theorem readyWindow_erase_iff (ring : DirectedRing n)
    (G : TaggedFC n ψ κ τ) :
    ReadyWindow ring (eraseFC G) ↔ TaggedReadyWindow ring G :=
  Iff.rfl

/-- Leaderlessness is also exactly the physical predicate. -/
def TaggedLeaderless (G : TaggedFC n ψ κ τ) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless (eraseFC G)

/-- Every-prefix preservation for an arbitrary physical predicate. -/
theorem aliveAlong_erase_iff (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (Good : BirthCheckPermitRepairLeaf.FC n ψ κ τ → Prop)
    (G : TaggedFC n ψ κ τ) (w : List (Fin n)) :
    AliveAlong (step1 hψ h2 ring) Good (eraseFC G) w ↔
      AliveAlong (taggedStep hψ h2 ring)
        (fun H => Good (eraseFC H)) G w := by
  induction w generalizing G with
  | nil => rfl
  | cons e w ih =>
      simp only [AliveAlong]
      have ht := ih (taggedStep hψ h2 ring G e)
      rw [erase_taggedStep hψ h2 ring G e] at ht
      constructor
      · intro h
        exact ⟨h.1, ht.mp h.2⟩
      · intro h
        exact ⟨h.1, ht.mpr h.2⟩

/-- Equality of the actual renewal indicators, word by word. -/
theorem aliveBit_erase (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (Good : BirthCheckPermitRepairLeaf.FC n ψ κ τ → Prop)
    (G : TaggedFC n ψ κ τ) (w : List (Fin n)) :
    aliveBit (step1 hψ h2 ring) Good (eraseFC G) w =
      aliveBit (taggedStep hψ h2 ring)
        (fun H => Good (eraseFC H)) G w := by
  classical
  unfold aliveBit
  rw [aliveAlong_erase_iff hψ h2 ring Good G w]

/-- Equality of renewal counts; the counted objects are scheduler words,
not elements of the tagged state space. -/
theorem aliveCount_erase (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (Good : BirthCheckPermitRepairLeaf.FC n ψ κ τ → Prop)
    (G : TaggedFC n ψ κ τ) (B : Nat) :
    aliveCount (step1 hψ h2 ring) Good (eraseFC G) B =
      aliveCount (taggedStep hψ h2 ring)
        (fun H => Good (eraseFC H)) G B := by
  unfold aliveCount
  apply congrArg (FixedSpanRenewalPayload.wordSum n B)
  funext w
  exact aliveBit_erase hψ h2 ring Good G w

/-- Exact preservation of the repository's avoidance predicate.
Both predicates are pulled back by erasure, including at the empty word. -/
theorem avoidAlong_erase_iff (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (Good P : BirthCheckPermitRepairLeaf.FC n ψ κ τ → Prop)
    (G : TaggedFC n ψ κ τ) (w : List (Fin n)) :
    AvoidAlong (step1 hψ h2 ring) Good P (eraseFC G) w ↔
      AvoidAlong (taggedStep hψ h2 ring)
        (fun H => Good (eraseFC H)) (fun H => P (eraseFC H)) G w := by
  induction w generalizing G with
  | nil => rfl
  | cons e w ih =>
      simp only [AvoidAlong]
      have ht := ih (taggedStep hψ h2 ring G e)
      rw [erase_taggedStep hψ h2 ring G e] at ht
      constructor
      · intro h
        exact ⟨h.1, ht.mp h.2⟩
      · intro h
        exact ⟨h.1, ht.mpr h.2⟩

/-- Exact preservation of `BirthTwoStageEscape.avoidBit`. -/
theorem avoidBit_erase (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (Good P : BirthCheckPermitRepairLeaf.FC n ψ κ τ → Prop)
    (G : TaggedFC n ψ κ τ) (w : List (Fin n)) :
    avoidBit (step1 hψ h2 ring) Good P (eraseFC G) w =
      avoidBit (taggedStep hψ h2 ring)
        (fun H => Good (eraseFC H)) (fun H => P (eraseFC H)) G w := by
  classical
  unfold avoidBit
  rw [avoidAlong_erase_iff hψ h2 ring Good P G w]

/-- Exact preservation of avoidance mass, for any two physical predicates.
The induction is on words in `avoidAlong_erase_iff`; this final step applies
congruence to the existing finite scheduler-word sum. -/
theorem avoidCount_erase (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (Good P : BirthCheckPermitRepairLeaf.FC n ψ κ τ → Prop)
    (G : TaggedFC n ψ κ τ) (B : Nat) :
    avoidCount (step1 hψ h2 ring) Good P (eraseFC G) B =
      avoidCount (taggedStep hψ h2 ring)
        (fun H => Good (eraseFC H)) (fun H => P (eraseFC H)) G B := by
  unfold avoidCount
  apply congrArg (FixedSpanRenewalPayload.wordSum n B)
  funext w
  exact avoidBit_erase hψ h2 ring Good P G w

/-- The requested leaderless transfer, with equality rather than only an
inequality. The lambda is definitionally `P` composed with `eraseFC`. -/
theorem leaderless_avoidCount_erase (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (P : BirthCheckPermitRepairLeaf.FC n ψ κ τ → Prop)
    (G : TaggedFC n ψ κ τ) (B : Nat) :
    avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless P (eraseFC G) B =
      avoidCount (taggedStep hψ h2 ring) TaggedLeaderless
        (fun H => P (eraseFC H)) G B :=
  avoidCount_erase hψ h2 ring
    BirthShortDoneTerminalFirstHit.Leaderless P G B

/-- Export exactly the physical stage-one premise of
`BirthCheckChainR1PerBlock.leaf_of_ready_window_mass`.

Only canonical tagged starts are assumed, not arbitrary ghost histories.
No invariant about the observer metadata is smuggled into the physical
quantifier over `C`. -/
theorem ready_window_mass_of_tagged (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (B₁ Q₁ : Nat)
    (hmass : ∀ C : BirthCheckPermitRepairLeaf.FC n ψ κ τ,
      BirthShortDoneTerminalFirstHit.Leaderless C →
        Q₁ * avoidCount (taggedStep hψ h2 ring) TaggedLeaderless
          (fun H => ReadyWindow ring (eraseFC H)) (initialTagged C) B₁ ≤
            (Q₁ - 1) * n ^ B₁) :
    ∀ C : BirthCheckPermitRepairLeaf.FC n ψ κ τ, BirthShortDoneTerminalFirstHit.Leaderless C →
      Q₁ * avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring) C B₁ ≤
          (Q₁ - 1) * n ^ B₁ := by
  intro C hC
  have hm := hmass C hC
  have he := leaderless_avoidCount_erase hψ h2 ring
    (ReadyWindow ring) (initialTagged C) B₁
  rw [erase_initialTagged] at he
  rw [← he] at hm
  exact hm

/-- Direct composition with the already proved per-block reduction.
This theorem keeps its exact horizon and its explicit stage-two cost. -/
theorem leaf_of_tagged_ready_window_mass
    (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n)
    (B₁ Q₁ Q₂ : Nat) (hQ₁ : 1 ≤ Q₁)
    (hQ : (4 * (ψ + 1)) ^ (ψ - 1) ≤ 3 ^ (ψ - 1) * Q₂)
    (hmass : ∀ C : BirthCheckPermitRepairLeaf.FC n ψ κ τ,
      BirthShortDoneTerminalFirstHit.Leaderless C →
        Q₁ * avoidCount (taggedStep hψ (Nat.le_of_lt h3) ring)
          TaggedLeaderless (fun H => ReadyWindow ring (eraseFC H))
          (initialTagged C) B₁ ≤ (Q₁ - 1) * n ^ B₁) :
    UniformEscapeMass
      (step1 (kappa := κ) (tau := τ) hψ (Nat.le_of_lt h3) ring)
      BirthShortDoneTerminalFirstHit.Leaderless
      (3 * (Q₁ * Q₂) * (B₁ + 2 * n * (ψ - 1))) 8 := by
  exact BirthCheckChainR1PerBlock.leaf_of_ready_window_mass
    (κ := κ) (τ := τ) hψ h3 ring hψn B₁ Q₁ Q₂ hQ₁ hQ
    (ready_window_mass_of_tagged hψ (Nat.le_of_lt h3) ring B₁ Q₁ hmass)

end B6ReadyMixGhost

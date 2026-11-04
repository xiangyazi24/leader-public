import Leader.Wu.Coherence.PostBirthStatement
import Leader.Wu.Coherence.BirthEntrance


set_option autoImplicit false
set_option Elab.async false


namespace R2CoherenceV31BirthQuarantine


open R2CoherenceV31
open R2CoherenceV31Closure
open R2CoherenceV31Step
open R2CoherenceV31Mission


variable {n ψ κ τ : Nat}


/-- Handoff: keep the complete V3.1 physical state and replace only
its controller by the all-closing/token-none quarantine initializer. -/
def quarantineInitV31
    (C : FC n ψ κ τ) : FC n ψ κ τ :=
  fun i => setControl (C i) .closing .none


/-- Exact controller shape installed by `quarantineInitV31`. -/
def BirthQuarantineV31
    (C : FC n ψ κ τ) : Prop :=
  ∀ i : Fin n,
    (C i).ctl.mark = .closing ∧ (C i).ctl.tok = .none


/-- Producer-facing CHECK/ID handoff.  The old certified R1 birth output is
retained physically; only the V3.1 controller is reinitialized. -/
def BirthEntranceCheckIdV1
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (Q : FC n ψ κ τ) : Prop :=
  ∃ (C0 : BirthCheckPermitRepairLeaf.FC n ψ κ τ)
    (C : FC n ψ κ τ),
    R2CoherenceV31BirthEntrance.BirthEntranceV31 hψ h2 ring C0 C ∧
      Q = quarantineInitV31 C


/-- Concrete mission entrance.  Election geometry remains an explicit,
independent producer obligation; CHECK/ID coherence is not assumed. -/
def BirthEntranceV1
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (Q : FC n ψ κ τ) : Prop :=
  BirthEntranceCheckIdV1 hψ h2 ring Q ∧
    ElectionGeometryV31 ring Q





/-- Every inherited equality is immediately logically dead at the quarantine
handoff: choose component zero of its current group; that cell is closing. -/
theorem quarantineInit_prefixDead
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.PrefixDead ring
      (eraseCfgV3 (quarantineInitV31 C)) i := by
  unfold R2Coherence.PrefixDead
  refine ⟨⟨0, hψ⟩, ?_⟩
  simp [quarantineInitV31, eraseCfgV3, eraseCellV3, setControl]


/-- Since every equal frontier is `PrefixDead`, current CHECK/ID coherence is
immediate without inspecting any inherited stored bit. -/
theorem quarantineInit_coherent
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) :
    CoherentPrefixesV3 ring (quarantineInitV31 C) := by
  change R2Coherence.CoherentPrefixes ring
    (eraseCfgV3 (quarantineInitV31 C))
  intro i
  exact R2Coherence.freshEqualPrefix_of_dead
    ring (eraseCfgV3 (quarantineInitV31 C)) i
    (quarantineInit_prefixDead hψ ring C i)


/-- Empty-word producer leaf for the concrete entrance. -/
theorem birthEntranceProducerV31V1_holds
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BirthEntranceProducerV31V1
      (κ := κ) (τ := τ)
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 ring)
      hψ ring := by
  intro Q hBirth
  rcases hBirth.1 with ⟨_, C, _, hQ⟩
  refine ⟨hBirth.2, ?_⟩
  rw [hQ]
  exact quarantineInit_coherent hψ ring C





/-- `EntranceClosedBridgeV31V1 (BirthEntranceV1 ...)` with
`CoherenceClosedV31` unfolded.


The first conjunct (`ElectionGeometryV31`) is explicit in `BirthEntranceV1`;
the second (`CoherentPrefixesV3`) is `quarantineInit_coherent`.  The real
implementation work is exactly the third conjunct, `ControllerSoundV3`:
starting from all-closing/token-none quarantine, every configuration reachable
by an arbitrary future `stepV3` word must satisfy `ControllerShapeV3`.


The forged-commit witness and the forged-sweep witness do not
immediately refute this restricted leaf.  The first constructs a standalone
shape-good `commitProxy` that is not `ControllerSoundV3`; the second constructs a
standalone strengthened-shape `sweepProxy` whose terminal sweep breaks V32.
Neither theorem shows that its forged configuration is reachable by any
`stepV3` word from a `quarantineInitV31` state satisfying this concrete
`BirthEntranceV1`.  Reachability from the quarantine entrance is precisely the
remaining proof/refutation question. -/
def BirthQuarantineEntranceClosedBridgeV31V1
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    BirthEntranceV1 hψ h2 ring C →
      ElectionGeometryV31 ring C ∧
        CoherentPrefixesV3 ring C ∧
          ControllerSoundV3 hψ h2 ring C





/-- Assembly instance: once the restricted entrance is in the current closed
domain, the compiled mission assembler applies unchanged. -/
theorem mission_of_bridge
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hBridge : EntranceClosedBridgeV31V1
      (κ := κ) (τ := τ)
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 ring)
      hψ h2 ring)
    (hOpenNoHazard : OpenNoHazardCoherenceV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    PostBirthCheckIdCoherenceMissionV1
      (κ := κ) (τ := τ)
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 ring)
      hψ h2 ring := by
  exact mission_of_bridge_and_openNoHazard
    (κ := κ) (τ := τ)
    (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 ring)
    hψ h2 ring hOpenNoHazard hBridge





end R2CoherenceV31BirthQuarantine

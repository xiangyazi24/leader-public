import Leader.Wu.Entrance.LargeRingLaws
import Leader.Wu.Entrance.EnvelopeInterface
import Leader.Wu.Entrance.EnvelopeHostLaws
import Leader.Wu.Entrance.WriterProtectionWitness
import Leader.Wu.Birth.CheckChainWindowMass

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceApron

open B6LocalReverseFill
open B6EntranceV2 B6EntranceV3

variable {n psi kappa tau : Nat} {P : Type}
variable {ring : DirectedRing n}

/-- Strengthened large-ring domain for a one-cell apron on both sides of the
existing envelope. -/
def LargeRingDomainApron (psi n : Nat) : Prop :=
  2 < psi ∧ B6EntranceV2.envelopeWidth psi + 2 < n

/-- The apron domain is strictly stronger than the accepted large-ring domain,
so every existing consumer of the old domain remains available. -/
theorem largeRingDomain_of_apron
    {psi n : Nat} (hdom : LargeRingDomainApron psi n) :
    B6EntranceLargeRingPackage.LargeRingDomain psi n := by
  exact ⟨hdom.1, by have h := hdom.2; omega⟩

/-- The one physical predecessor immediately to the left of the old envelope. -/
def leftApronCell
    (ring : DirectedRing n) (X : Workspace ring psi) : Fin n :=
  BirthCheckChainR1Mass.leftStart ring X.env.I.first

/-- The one physical successor immediately to the right of the old envelope. -/
def rightApronCell
    (ring : DirectedRing n) (X : Workspace ring psi) : Fin n :=
  BirthCheckChainR1Ring.cell ring X.env.I.first X.env.I.size

/-- The left apron cell is exactly the directed-ring predecessor of the old
first envelope cell. -/
theorem leftApronCell_eq_leftNeighbor
    (ring : DirectedRing n) (X : Workspace ring psi) :
    leftApronCell ring X = ring.leftNeighbor X.env.I.first := by
  apply Fin.ext
  rfl

/-- Symmetric one-cell service/matcher apron around the existing envelope. -/
def apronOf
    (hdom : LargeRingDomainApron psi n)
    (X : Workspace ring psi) : Interval ring where
  first := leftApronCell ring X
  size := X.env.I.size + 2
  nonempty := by omega
  fits := by
    rw [X.env.size_eq]
    exact Nat.le_of_lt hdom.2

@[simp] theorem apronOf_size
    (hdom : LargeRingDomainApron psi n) (X : Workspace ring psi) :
    (apronOf hdom X).size = X.env.I.size + 2 := rfl

@[simp] theorem apronOf_size_eq_envelope
    (hdom : LargeRingDomainApron psi n) (X : Workspace ring psi) :
    (apronOf hdom X).size = envelopeWidth psi + 2 := by
  rw [apronOf_size, X.env.size_eq]

/-- One complete directed sweep of the apron interval has A.size - 1 =
envelopeWidth psi + 1 scheduled internal edges. -/
def apronSweepL (psi : Nat) : Nat :=
  envelopeWidth psi + 1

def apronTrafficTargetL (psi : Nat) : Nat :=
  2 * apronSweepL psi

def apronExpiryTargetL (psi : Nat) : Nat :=
  (16 * psi + 1) * apronSweepL psi

/-- `HostStageWord` with only the service/matcher/HostExit interval widened to
the apron A. The phase predicates still receive the original workspace X, so
their sanitation target remains the old envelope E. -/
def HostApronStageWord
    (hdom : LargeRingDomainApron psi n)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (_WP : WriterProtected ring psi P)
    (From To : Workspace ring psi → PConfig n P → Prop)
    (L : Nat) : Prop :=
  ∀ (X : Workspace ring psi) (C : PConfig n P),
    HostLeaderless view C → From X C →
    ∃ w : List (Fin n),
      InternalWord (apronOf hdom X) w ∧
      w.length ≤ L ∧
      HostExit host view ring (apronOf hdom X) (To X)
        (runHost host ring w C)

/-- Replacement law 3: service is internal to A, but successful reset/echo
sanitation is still required only on the old envelope E. -/
def DirectionalTrafficExitWithinDoubleSweep
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hdom : LargeRingDomainApron psi n) : Prop :=
  let host : B9Host.HostRow (Phys psi psi (16 * psi)) :=
    B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2
  let view : Phys psi psi (16 * psi) → Phys psi psi (16 * psi) :=
    fun q => q
  let WP : WriterProtected ring psi (Phys psi psi (16 * psi)) :=
    B6EntranceLawsWiring2.WPfinal (psi := psi) ring
  HostApronStageWord hdom host view ring WP
    (WriterAt WP)
    (TrafficAtEnv view WP)
    (apronTrafficTargetL psi)

/-- Replacement law 4: service is internal to A, while comparison sanitation
and the K2-source certificate remain statements about the old workspace E. -/
def ComparisonExpiryWithinTimeoutSweep
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hdom : LargeRingDomainApron psi n) : Prop :=
  let host : B9Host.HostRow (Phys psi psi (16 * psi)) :=
    B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2
  let view : Phys psi psi (16 * psi) → Phys psi psi (16 * psi) :=
    fun q => q
  let WP : WriterProtected ring psi (Phys psi psi (16 * psi)) :=
    B6EntranceLawsWiring2.WPfinal (psi := psi) ring
  HostApronStageWord hdom host view ring WP
    (TrafficAtEnv view WP)
    (fun X C =>
      ExpiryAtEnv view WP X C ∧
        R1DrainStableForK2 hpsi h2 host view ring X C)
    (apronExpiryTargetL psi)

end B6EntranceApron

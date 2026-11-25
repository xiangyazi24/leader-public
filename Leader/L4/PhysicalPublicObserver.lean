import Leader.L4.PhysicalClockDisplayMask
import Leader.L4.Height.ObserverEntrance

/-! Public marker handoff on the literal production pair.
The private reference serves only as the all-future anchor for the
observer; the projected public leader need not be at that site. -/
namespace L4.PhysicalPublic

open AllSizeProtocol PhysicalCustody PhysicalClockDisplay
open BStarPublicCodec
local notation "hp" => (show 0 < 2 by decide)

def pubConfig {s n : Nat} (x : Raw s n) : Config 2 12 n :=
  fun i => readPub hp (x i).publicRow

def packedLeader {s n : Nat} (x : Raw s n) (i : Fin n) : Bool :=
  (pubConfig x i).leader

def seed {s n : Nat} (x : Raw s n) (e : Fin n) : Bool :=
  let j := rightNeighbor e
  let y := rawNext s x e
  let ordinary := pairStep (pubConfig x e) (pubConfig x j)
  (H5.row ((x e).guard, (x j).guard)
    (reference (rows s) (x e), reference (rows s) (x j))
    (reference (rows s) (y e), reference (rows s) (y j))
    ((pubConfig x e).mark, (pubConfig x j).mark)
    (ordinary.1.mark, ordinary.2.mark)).seed.1

def Marked {s n : Nat} (x : Raw s n) : Prop :=
  PermanentReference x ∧
  (∀ w : List (Fin n), ∀ e, seed (rawRun x w) e = false) ∧
  RootedEntrance.MarkNonempty (pubConfig x) ∧ MCOV (pubConfig x) ∧ COV (pubConfig x)

theorem marked_agrees {s n : Nat} (x : Raw s n) :
    Marked x ↔ Height.ObserverPhysical.Marked (rows s) hp x := Iff.rfl

theorem marked_closed {s n : Nat} (hn : 4 ≤ n) {x : Raw s n} (e : Fin n) :
    Marked x → Marked (rawNext s x e) :=
  Height.ObserverPhysical.marked_closed hn (rows s) hp rfl e

theorem marked_projects {s n : Nat} (hn : 4 ≤ n) {x : Raw s n} (e : Fin n) :
    Marked x → pubConfig (rawNext s x e) = step (pubConfig x) e :=
  Height.ObserverPhysical.marked_projects hn (rows s) hp rfl e

theorem packed_observer_mean {s n : Nat} (hn : 4 ≤ n) (x : Raw s n) :
    PermanentReference x →
      Height.IIDExpectedHittingTimeAtMost (rawNext s) Marked x (5*n^2+7*n) :=
  Height.ObserverEntrance.physical_mean hn (rows s) hp rfl x

end L4.PhysicalPublic

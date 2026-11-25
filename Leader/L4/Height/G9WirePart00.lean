import Leader.L4.Height.RawServiceCore
import Leader.L4.Height.ProductionCustody
import Leader.L4.Height.AdmissionSteering
import Leader.L4.Height.G9Spine
import Leader.L4.Height.ClockSlice
import Leader.L4.WindowG7Complete
import Leader.L4.Height.ReservedFrontier
import Leader.L4.Height.RawLevel
import Leader.L4.Height.PublicationWords
import Leader.L4.Height.ObserverBudget
import Leader.L4.Height.BoundedDecoder
import Leader.L4.Height.DisplayDeadline
import Leader.L4.Height.CustodyBudget
import Leader.L4.BStarLogicalConjugacy
import Leader.L4.BStarEpochLift
import Leader.L4.BStarJoinedLap
import Leader.L4.RootedEntrance
import Leader.L4.RootedProduct

set_option Elab.async false

/-! Raw-edge wiring for the two production branches. The physical definitions below
are the shared signatures of the four production components. All time bounds count raw marks. -/
namespace L4.Height.G9Wire.CustodySpec
open L4.PhysicalCustody
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart
open BStarLongFixedRouting BStarH6Ordinal BStarCustodyCuts

def radiusHorizon (k : Nat) : Nat := 4096 * (k+2) * streak k * 2^(streak k)
/-- Use literally the same closed numerical expression as the
spine. This avoids forcing gigantic closed powers during elaboration. -/
abbrev packingCoefficient (cgeom : Nat) : Nat :=
  L4.Height.G9Spine.custodyCoeff cgeom

def CustodyReached : Prop :=
  ∃ cgeom : Nat, ∀ {s n : Nat}, 4 ≤ n → 6 ≤ s → s = ell (ell n) →
    ∀ x : Raw s n, Height.IIDExpectedHittingTimeAtMost (rawNext s) Custody x
      (packingCoefficient cgeom * n^2)

end L4.Height.G9Wire.CustodySpec

namespace L4.Height.G9Wire.ClockServiceSpec
open L4.Height L4.PhysicalCustody
open AllSizeProtocol BStarH6WordChart BStarAcquireAnchors BStarGrantWriterHistory
open Classical

noncomputable section

def longBudget : Nat := 2^32
def longScale (n r : Nat) : Nat := 2^(5*longBudget+34)*n*r

abbrev publishes {s n : Nat} (x : Raw s n) (i : Fin n) (w : List (Fin n)) : Prop :=
  Height.RawServiceCore.publishes x i w

abbrev maxWordWidth {s n : Nat} {x : Raw s n} (g : CustodyWitness x) : Nat :=
  Height.ProductionCustody.width g

/-- The amended service export on the deployed advice and actual owner ring. -/
abbrev ProductionStrictBlock : Prop := Height.ProductionCustody.ProductionBlock

/-- The original export also quantifies over non-production advice and singleton rings. -/
def StrictBlock : Prop :=
  ∀ {s n : Nat}, 4 ≤ n → ∀ {x : Raw s n} (g : CustodyWitness x)
    (i : Header (oldH6 (rows s) g.base)),
    let W := maxWordWidth g
    let T := 2^20*n*W
    2^(5*longBudget+1) * wordSum (fun w => if publishes x i.val w then 1 else 0) (2*T)
      ≥ n^(2*T)


/-- The singleton obstruction contradicts the original unrestricted count for
any custody witness whose physical headers all name one site. -/
theorem singleton_excludes_original {s n : Nat} (hn : 4 ≤ n) {x : Raw s n}
    (g : CustodyWitness x)
    (only : ∀ a b : Header (oldH6 (rows s) g.base), a.val = b.val)
    (i : Header (oldH6 (rows s) g.base)) : ¬ StrictBlock := by
  intro original
  exact Nat.not_le_of_gt
    (Height.RawServiceCore.singleton_refutes_block hn g only i (2^(5*longBudget+1))
      (2*(2^20*n*maxWordWidth g))) (original hn g i)

/-- The 81-site singleton fixture lies outside the packed production branch. -/
theorem singleton_fixture_advice : ell (ell 81) = 3 ∧ 81 ≤ 3*1024*radWidth 6 := by decide

end
end L4.Height.G9Wire.ClockServiceSpec

namespace L4.Height.G9Wire.ClockDisplaySpec
open L4.Height L4.PhysicalCustody L4.Height.G9Wire.ClockServiceSpec
open AllSizeProtocol BStarH6WordChart BStarCycleGeometry BStarAcquireAnchors BStarLongFixedRouting
open BStarPhysicalLegitimate BStarPhysicalCoset BStarEpochLift BStarPhysicalLiftAlignment
open Classical

noncomputable def refBit {s n : Nat} (x : Raw s n) (i : Fin n) : Bool :=
  H5.seesReference (AllSizeProtocol.reference (rows s) (x i))

def PermanentReference {s n : Nat} (x : Raw s n) : Prop :=
  ∃ winner : Fin n, ∀ (w : List (Fin n)) (i : Fin n),
    refBit (rawRun x w) i = true ↔ i = winner

noncomputable def projectedRecords {s n : Nat} {x : Raw s n}
    (g : CustodyWitness x) : Fin (total (oldH6 (rows s) g.base)) →
      L4.Compiler.Native.NativeRecord :=
  fun i => BStarNativePointwise.readRecord (r:=radWidth s) x (atIndex g.hh i).val

def RawLegitOfQuiet : Prop :=
  ∀ {s n : Nat} {x : Raw s n} (g : CustodyWitness x),
    (∀ i, (projectedRecords g i).err = false) →
    Recover.StageThree.Quiet (Compiler.Native.modulus (radWidth s))
      (total_pos (oldH6 (rows s) g.base) g.hh) (projectedRecords g) →
    Recover.StageTwo.WellFormed (Compiler.Native.modulus (radWidth s)) (projectedRecords g) →
    ClockLegit (show 0 < 2 by decide) g.base g.hh x

noncomputable def RawDisplayTrial : Prop :=
  ∀ {s n : Nat}, 4 ≤ n → 6 ≤ s → s = AllSizeProtocol.ell (AllSizeProtocol.ell n) →
    ∀ {x : Raw s n} (g : CustodyWitness x), ClockLegit (show 0 < 2 by decide) g.base g.hh x →
    let h := oldH6 (rows s) g.base
    let m := total h
    let L := longScale n (radWidth s)
    let D := 2^29*L*m
    ∃ start : Fin n → Nat, ∃ lo G opening cap : Nat,
      opening = frontier G ∧ cap = opening + 32*(2^19*m) ∧
      cap+1 ≤ lo+(m+233+32*(2^19*m)) ∧
      (∀ w : List (Fin n),
        let tape := ((g.u++g.v)++g.past)++w
        let ticks := traceCount (show 0 < 2 by decide) g.base g.initial g.hh start tape
        RepresentsCoset (show 0 < 2 by decide) g.base (rawRun g.initial tape)
          (L4.Compiler.Native.modulus (radWidth s)/2) ticks ∧
        Coherent g.hh ticks) ∧
      (∀ i : Header h,
        lo ≤ traceCount (show 0 < 2 by decide) g.base g.initial g.hh start
          ((g.u++g.v)++g.past) i.val) ∧
      (∀ i : Fin n,
        traceCount (show 0 < 2 by decide) g.base g.initial g.hh start
          ((g.u++g.v)++g.past) i ≤ G) ∧
      (let miss := fun w : List (Fin n) => ∃ i : Header h,
        traceCount (show 0 < 2 by decide) g.base g.initial g.hh start
          (((g.u++g.v)++g.past)++w) i.val ≤ cap
       let bad := fun w : List (Fin n) => ¬ PermanentReference (rawRun x w)
       4*wordSum (fun w => if bad w then 1 else 0) D ≤
         n^D + 4*wordSum (fun w => if miss w then 1 else 0) D)

end L4.Height.G9Wire.ClockDisplaySpec

namespace L4.Height.G9Wire.PublicSpec
open AllSizeProtocol PhysicalCustody ClockDisplaySpec
open BStarPublicCodec

noncomputable def pubConfig {s n : Nat} (x : Raw s n) : L4.Config 2 12 n :=
  fun i => readPub (p := 2) (c := 12) (show 0 < 2 by decide) (x i).publicRow

noncomputable def packedLeader {s n : Nat} (x : Raw s n) (i : Fin n) : Bool :=
  (pubConfig x i).leader

noncomputable def seed {s n : Nat} (x : Raw s n) (e : Fin n) : Bool :=
  let j := rightNeighbor e
  let rawGuard := ((x e).guard, (x j).guard)
  let oldRef := (AllSizeProtocol.reference (rows s) (x e),
    AllSizeProtocol.reference (rows s) (x j))
  let y := rawNext s x e
  let newRef := (AllSizeProtocol.reference (rows s) (y e),
    AllSizeProtocol.reference (rows s) (y j))
  let left := pubConfig x e
  let right := pubConfig x j
  let ordinary := L4.pairStep left right
  (H5.row rawGuard oldRef newRef (left.mark,right.mark)
    (ordinary.1.mark,ordinary.2.mark)).seed.1

def Marked {s n : Nat} (x : Raw s n) : Prop :=
  PermanentReference x ∧ (∀ w : List (Fin n), ∀ e, seed (rawRun x w) e = false) ∧
  L4.RootedEntrance.MarkNonempty (pubConfig x) ∧
  L4.MCOV (pubConfig x) ∧ L4.COV (pubConfig x)

def PackedElected {s n : Nat} (x : Raw s n) : Prop :=
  L4.RootedProduct.ProductSafe (rawNext s) packedLeader x

def PackedObserverMean : Prop :=
  ∀ {s n : Nat}, 4 ≤ n → ∀ x : Raw s n, PermanentReference x →
    Height.IIDExpectedHittingTimeAtMost (rawNext s) Marked x (5*n^2+7*n)

def boundedN : Nat := 2^32
def boundedP : Nat := boundedN+1
abbrev BoundedCode := Fin (2^48)
abbrev BoundedRaw (n : Nat) := Fin n → BoundedCode

def boundedPairWith (encode : Site boundedP 12 → BoundedCode)
    (decode : BoundedCode → Site boundedP 12) (a b : BoundedCode) :=
  let y := pairStep (decode a) (decode b)
  (encode y.1, encode y.2)

def boundedNextWith (encode : Site boundedP 12 → BoundedCode)
    (decode : BoundedCode → Site boundedP 12) {n : Nat}
    (x : BoundedRaw n) (e : Fin n) : BoundedRaw n :=
  let j := rightNeighbor e
  let y := boundedPairWith encode decode (x e) (x j)
  fun i => if i=e then y.1 else if i=j then y.2 else x i

def boundedLeaderWith (decode : BoundedCode → Site boundedP 12) {n} (x : BoundedRaw n) (i : Fin n) :=
  (decode (x i)).leader

def BoundedElectedWith (encode : Site boundedP 12 → BoundedCode)
    (decode : BoundedCode → Site boundedP 12) {n} (x : BoundedRaw n) :=
  RootedProduct.ProductSafe (boundedNextWith encode decode) (boundedLeaderWith decode) x

end L4.Height.G9Wire.PublicSpec


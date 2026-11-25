import Leader.L4.Height.ServiceCustody
import Leader.L4.BStarCycleGeometry
import Leader.L4.PhysicalClockQuietPorts

namespace L4.PhysicalClockDisplay
open PhysicalCustody
open BStarH6WordChart BStarPhysicalLegitimate BStarNativePointwise
open BStarCycleGeometry
open L4.Compiler.Native L4.Height

noncomputable def projectedRecords {s n : Nat} {x : Raw s n}
    (g : CustodyWitness x) : Fin (total (oldH6 (rows s) g.base)) → NativeRecord :=
  fun i => readRecord (r:=radWidth s) x (atIndex g.hh i).val

/-- The isolated physical-port proof uses byte-identical chart indexing. -/
theorem port_index_abi {n : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (i : Fin (total h)) :
    PhysicalClockPortIndex.atIndex hh i = BStarCycleGeometry.atIndex hh i := rfl

/-- No alternate physical port mapping is introduced by the quiet adapter. -/
theorem port_neighbor_abi {n : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (i : BStarAcquireAnchors.Header h) (q : Fin 3) :
    PhysicalClockPortBase.neighborHeader hh i q =
      BStarNativePortGeometry.neighborHeader hh i q := rfl

/-- Accepted quietness on the projected old records is the archived
physical ClockLegit invariant, with exactly the same old bank and ports. -/
theorem raw_legit_of_quiet {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (errFree : ∀ i, (projectedRecords g i).err=false)
    (quiet : Recover.StageThree.Quiet (modulus (radWidth s))
      (total_pos (oldH6 (rows s) g.base) g.hh) (projectedRecords g))
    (well : Recover.StageTwo.WellFormed (modulus (radWidth s)) (projectedRecords g)) :
    ClockLegit (show 0<2 by decide) g.base g.hh x := by
  exact PhysicalClockQuietPorts.quiet_ports g.hh (modulus (radWidth s))
    (fun i=>readRecord (r:=radWidth s) x i.val) errFree quiet well

end L4.PhysicalClockDisplay

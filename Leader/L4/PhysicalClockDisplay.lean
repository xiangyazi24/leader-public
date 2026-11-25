import Leader.L4.PhysicalClockRawTrial
import Leader.L4.PhysicalClockEpoch
import Leader.L4.PhysicalClockMissQuarter
import Leader.L4.PhysicalClockDisplayLegit

namespace L4.PhysicalClockDisplay
open AllSizeProtocol PhysicalCustody BStarH6WordChart BStarCycleGeometry BStarAcquireAnchors
open BStarTrace BStarPhysicalLegitimate BStarPhysicalCoset BStarEpochLift BStarPhysicalLiftAlignment
open L4.Compiler.Native L4.Height Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
local notation "hp" => (show 0<2 by decide)

/-- The raw trial on the one original custody epoch (no relift after the stop). -/
theorem raw_display_trial {s n : Nat} (_hn : 4≤n) (hs : 6≤s)
    (ha : s=AllSizeProtocol.ell (AllSizeProtocol.ell n)) {x : Raw s n}
    (g : CustodyWitness x) (legit : ClockLegit hp g.base g.hh x) :
    DisplayTrial g := by
  have P := ProductionCustody.production_of_space g hs ha (room_of_advice hs ha)
  obtain ⟨hr,M,_,phase,small,_⟩ := production_clock_bounds g hs ha
  obtain ⟨start,lo,G,_,_,_,_,span,_,repr,lower,upper,_⟩ :=
    PhysicalClockEpoch.epoch_with_extrema g (ProductionCustody.separation P)
      (by omega) _ M small phase legit
  exact trial_of_epoch_bounds g hs ha legit start lo G repr lower upper span

/-- The mass of all-site display failure at the paper deadline is at
most one half. The very same witness chosen by the raw trial controls
the missed-cap mass via strict physical publication service. -/
theorem raw_display_deadline {s n : Nat} (hn : 4≤n) (hs : 6≤s)
    (ha : s=AllSizeProtocol.ell (AllSizeProtocol.ell n)) {x : Raw s n}
    (g : CustodyWitness x) (legit : ClockLegit hp g.base g.hh x) :
    let D := 2^29*displayScale n (radWidth s)*total (oldH6 (rows s) g.base)
    2*wordSum (fun w=>@ite Nat (¬PermanentReference (rawRun x w)) (Classical.propDecidable _) 1 0) D≤n^D := by
  let m := total (oldH6 (rows s) g.base)
  have hm : 0<m := total_pos _ g.hh
  obtain ⟨start,lo,G,opening,cap,_,_,depth,repr,lower,_,split⟩ :=
    raw_display_trial hn hs ha g legit
  obtain ⟨hr,M,pos,phase,_,_⟩ := production_clock_bounds g hs ha
  have d : cap+1-lo≤2^25*m := by
    change cap+1≤lo+(m+233+32*(2^19*m)) at depth
    omega
  have miss := PhysicalClockMissQuarter.miss_quarter hn hs ha (room_of_advice hs ha) g
    _ M pos phase start lo cap (by omega) legit repr lower d
  let D := 2^29*displayScale n (radWidth s)*m
  let bad := fun w : List (Fin n) => ¬PermanentReference (rawRun x w)
  let missed := fun w : List (Fin n) => ∃ i : Header (oldH6 (rows s) g.base),
    traceCount hp g.base g.initial g.hh start (((g.u++g.v)++g.past)++w) i.val≤cap
  let count := fun (E : List (Fin n) → Prop) (w : List (Fin n)) =>
    @ite Nat (E w) (Classical.propDecidable _) 1 0
  have A : 4*wordSum (count bad) D ≤ n^D + 4*wordSum (count missed) D := split
  have B : 4*wordSum (count missed) D ≤ n^D := miss
  change 2*wordSum (count bad) D ≤ n^D
  omega

end L4.PhysicalClockDisplay

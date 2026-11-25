import Leader.L4.BStarRawParallelCount
import Leader.L4.BStarRawActualChildMoment
import Leader.L4.BStarLongServiceBudget
import Leader.L4.PhysicalStrictServiceTail

namespace L4.PhysicalClockMissQuarter
open AllSizeProtocol PhysicalCustody Height BStarTrace BStarLongWork
open BStarAcquireAnchors BStarH6WordChart BStarGrantWriterHistory
open BStarEpochLift BStarPhysicalLegitimate BStarPhysicalCoset
open BStarPhysicalIncrementLedger BStarPhysicalLiftAlignment BStarNativePortGeometry
open BStarRawPublicationHistory BStarRawParallelCount BStarRawActualChildMoment
open BStarRawCausalCut BStarRawCausalCrossing BStarRawBlockDrift BStarRawDisplayBudget
open BStarRawDeadlineBridge BStarRawStopCut BStarRawStopMoment
open BStarLongServiceBudget BStarNativeNeedLift Compiler.Native Classical
private abbrev hp : 0 < 2 := by decide

/-- The archived inclusive wait and the repaired service theorem
are observing the same actual center event on the same raw suffix. -/
theorem publication_wait_eq {s n : Nat} (y : Raw s n) (i : Fin n) (w : List (Fin n)) :
    publicationWait hp y i w=Height.RawServiceCore.strictWait y i w := by
  induction w generalizing y with
  | nil => rfl
  | cons e w ih =>
    dsimp only [publicationWait,Height.RawServiceCore.strictWait]
    rw [ih] <;> rfl

/-- Apply the three-parent raw crossing estimate at exactly the display
deadline. The caller's selected start, cap and historical tape are
unchanged. A raw continuation is supplied only after its actual
predecessor cut, with no independent synthetic epoch or scheduler. -/
theorem miss_quarter {s n : Nat} (hn : 4≤n) (hs : 6≤s)
    (hadvice : s=ell (ell n)) (space : 3*1024*radWidth s<n)
    {x : Raw s n} (g : CustodyWitness x)
    (P : Nat) (M : modulus (radWidth s)=2*P) (pos : 0<P) (phase : 32∣P)
    (start : Fin n→Nat) (lo cap : Nat)
    (width : 3≤radWidth s)
    (legit : ClockLegit hp g.base g.hh x)
    (represent : ∀ a : List (Fin n),
      let tape := ((g.u++g.v)++g.past)++a
      RepresentsCoset hp g.base (rawRun g.initial tape) P (traceCount hp g.base g.initial g.hh start tape) ∧
      Coherent g.hh (traceCount hp g.base g.initial g.hh start tape))
    (lower : ∀ i : Header (oldH6 (rows s) g.base),
      lo≤traceCount hp g.base g.initial g.hh start ((g.u++g.v)++g.past) i.val)
    (depth : cap+1-lo≤2^25*total (oldH6 (rows s) g.base)) :
    let hist := (g.u++g.v)++g.past
    let D := 2^29*longScale n (radWidth s)*total (oldH6 (rows s) g.base)
    let miss := fun w : List (Fin n) => ∃ i : Header (oldH6 (rows s) g.base),
      traceCount hp g.base g.initial g.hh start (hist++w) i.val≤cap
    4*wordSum (massInd miss) D≤n^D := by
  dsimp only
  let L := longScale n (radWidth s)
  let hist := (g.u++g.v)++g.past
  let D := 2^29*L*total (oldH6 (rows s) g.base)
  have Lpos : 0<L :=
    Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (by omega)) (by omega)
  have sep (e : Fin n) : e≠rightNeighbor e := by
    have prod := Height.ProductionCustody.production_of_space g hs hadvice space
    exact Height.ProductionCustody.separation prod e
  have good (a : List (Fin n)) :
      ClockLegit hp g.base g.hh (rawRun g.initial (hist++a)) ∧
      RepresentsCoset hp g.base (rawRun g.initial (hist++a)) P
        (traceCount hp g.base g.initial g.hh start (hist++a)) ∧
      Coherent g.hh (traceCount hp g.base g.initial g.hh start (hist++a)) := by
    refine ⟨?_,represent a⟩
    have initLegit : ClockLegit hp g.base g.hh (rawRun g.initial hist) := g.here.symm ▸ legit
    have H := physical_legit_word hp g.u g.v g.cuts g.hh sep g.Q g.init g.fiber g.closed
      width g.flags g.notShort g.past a initLegit
    unfold PhysicalCustody.rawRun PhysicalCustody.rawNext PhysicalCustody.rows
    simpa only [hist,List.append_assoc] using H
  apply raw_quarter_miss_of_child hp g.initial g.hh start hist L lo cap Lpos lower depth
  intro k i
  dsimp only
  rw [show lo+(k+1)=(lo+k)+1 from (Nat.add_assoc lo k 1).symm]
  have H := actual_child_moment hp g.hh P M pos phase start hist good i (lo+k) L D Lpos
    (fun a t _ => by
      have M := PhysicalStrictServiceTail.actual_prefix_moment hn hs hadvice space g a i t
      change wordSum (fun w=>2^(publicationWait hp (rawRun g.initial (hist++a)) i.val w/L)) t≤2*n^t
      simp only [publication_wait_eq]
      have E : budget=Height.ProductionCustody.longBudget := rfl
      have scaleEq : L=2^(5*Height.ProductionCustody.longBudget+34)*n*radWidth s :=
        congrArg (fun z : Nat => 2^(5*z+34)*n*radWidth s) E
      rw [scaleEq]
      exact M)
  have eqT (l : Nat) (j : Header (oldH6 (rows s) g.base)) (w : List (Fin n)) :
      firstTime (rawLevelTest hp (initial:=g.initial) g.hh start j l) hist w =
        traceCrossing hp g.initial g.hh start hist l j w :=
    firstTime_eq_firstCrossing (fun a => traceCount hp g.base g.initial g.hh start a j.val) l hist w
  change wordSum (fun w=>2^(traceCrossing hp g.initial g.hh start hist ((lo+k)+1) i w/L)) D≤
    4*wordSum (fun w=>2^(max (traceCrossing hp g.initial g.hh start hist (lo+k) (neighborHeader g.hh i 0) w)
      (max (traceCrossing hp g.initial g.hh start hist (lo+k) (neighborHeader g.hh i 1) w)
        (traceCrossing hp g.initial g.hh start hist (lo+k) (neighborHeader g.hh i 2) w))/L)) D
  have self := self_port g.hh i
  unfold PhysicalCustody.rows at self eqT
  erw [self]
  simp only [←eqT,Nat.max_left_comm]
  exact H

end L4.PhysicalClockMissQuarter

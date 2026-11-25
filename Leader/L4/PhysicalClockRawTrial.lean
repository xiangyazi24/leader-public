import Leader.L4.BStarLongServiceBudget
import Leader.L4.BStarLiteralDeadlineSplit
import Leader.L4.PhysicalClockSizing
import Leader.L4.PhysicalClockIndexedDisplay

namespace L4.PhysicalClockDisplay
open AllSizeProtocol PhysicalCustody BStarH6WordChart BStarCycleGeometry BStarAcquireAnchors
open BStarTrace BStarPhysicalLegitimate BStarPhysicalCoset BStarEpochLift BStarPhysicalLiftAlignment
open L4.Compiler.Native L4.Height Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
local notation "hp" => (show 0<2 by decide)

abbrev displayScale (n r : Nat) : Nat := BStarLongServiceBudget.longScale n r

def DisplayTrial {s n : Nat} {x : Raw s n} (g : CustodyWitness x) : Prop :=
    let h := oldH6 (rows s) g.base
    let m := total h
    let L := displayScale n (radWidth s)
    let D := 2^29*L*m
    ∃ start : Fin n → Nat, ∃ lo G opening cap : Nat,
      opening = frontier G ∧ cap = opening + 32*(2^19*m) ∧
      cap+1 ≤ lo+(m+233+32*(2^19*m)) ∧
      (∀ w : List (Fin n),
        let tape := ((g.u++g.v)++g.past)++w
        let ticks := traceCount hp g.base g.initial g.hh start tape
        RepresentsCoset hp g.base (rawRun g.initial tape)
          (L4.Compiler.Native.modulus (radWidth s)/2) ticks ∧
        Coherent g.hh ticks) ∧
      (∀ i : Header h,
        lo ≤ traceCount hp g.base g.initial g.hh start
          ((g.u++g.v)++g.past) i.val) ∧
      (∀ i : Fin n,
        traceCount hp g.base g.initial g.hh start
          ((g.u++g.v)++g.past) i ≤ G) ∧
      (let miss := fun w : List (Fin n) => ∃ i : Header h,
        traceCount hp g.base g.initial g.hh start
          (((g.u++g.v)++g.past)++w) i.val ≤ cap
       let bad := fun w : List (Fin n) => ¬ PermanentReference (rawRun x w)
       4*wordSum (fun w => @ite Nat (bad w) (Classical.propDecidable _) 1 0) D ≤
         n^D + 4*wordSum (fun w => @ite Nat (miss w) (Classical.propDecidable _) 1 0) D)

private theorem raw_run_append {s n : Nat} (y : Raw s n) (u v : List (Fin n)) :
    rawRun y (u++v)=rawRun (rawRun y u) v :=
  BStarResetSchedule.run_append (rawNext s) y u v

theorem trial_of_epoch_bounds {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (hs : 6≤s) (ha : s=ell (ell n))
    (legit : ClockLegit hp g.base g.hh x)
    (start : Fin n→Nat) (lo G : Nat)
    (repr : ∀ w : List (Fin n),
      let tape := ((g.u++g.v)++g.past)++w
      let ticks := traceCount hp g.base g.initial g.hh start tape
      RepresentsCoset hp g.base (rawRun g.initial tape) (modulus (radWidth s)/2) ticks ∧
        Coherent g.hh ticks)
    (lower : ∀ i : Header (oldH6 (rows s) g.base),
      lo≤traceCount hp g.base g.initial g.hh start ((g.u++g.v)++g.past) i.val)
    (upper : ∀ i : Fin n,
      traceCount hp g.base g.initial g.hh start ((g.u++g.v)++g.past) i≤G)
    (span : G≤lo+total (oldH6 (rows s) g.base)/2) :
    DisplayTrial g := by
  let hist := (g.u++g.v)++g.past
  let m := total (oldH6 (rows s) g.base)
  let D := 2^29*displayScale n (radWidth s)*m
  let opening := frontier G
  let cap := opening+32*(2^19*m)
  let miss := fun w : List (Fin n) => ∃ i : Header (oldH6 (rows s) g.base),
    traceCount hp g.base g.initial g.hh start (hist++w) i.val≤cap
  let fail := fun w : List (Fin n) => ¬∃ leader : Fin m,
    ∀ tail : List (Fin n), ∀ j : Fin m,
      BStarLiteralDisplay.anchorReadout (rawRun g.initial (hist++(w++tail)))
        (atIndex g.hh j).val=decide (j=leader)
  let bad := fun w : List (Fin n) => ¬PermanentReference (rawRun x w)
  have P := L4.Height.ProductionCustody.production_of_space g hs ha (room_of_advice hs ha)
  obtain ⟨hr,twice,pos,phase,_,height⟩ := production_clock_bounds g hs ha
  have L : ClockLegit hp g.base g.hh (rawRun g.initial hist) := g.here.symm ▸ legit
  have F := frontier_spec G
  have bound : 4*wordSum (fun w => @ite Nat (fail w) (Classical.propDecidable _) 1 0) D ≤
      n^D+4*wordSum (fun w => @ite Nat (miss w) (Classical.propDecidable _) 1 0) D :=
    BStarLiteralDeadlineSplit.literal_deadline_split hp g.u g.v g.past g.cuts g.hh
      (L4.Height.ProductionCustody.separation P) g.Q g.init g.fiber g.closed g.offset
      (fun y q i _ => g.coherent y q i) hr g.flags g.notShort g.heads g.cont _ twice pos phase start
      L repr lo opening G D lower upper (Nat.le_refl _) F.2.2.1 height
  have implies (w : List (Fin n)) (badW : bad w) : fail w := by
    intro singleton
    obtain ⟨winner,single⟩ := singleton
    let g' := L4.Height.ProductionCustody.extend g w
    apply badW
    refine of_indexed_original g' (atIndex g.hh) ?_ ?_ winner ?_
    · intro j k E
      exact (index_atIndex g.hh j).symm.trans ((congrArg (index g.hh) E).trans (index_atIndex g.hh k))
    · intro i
      exact ⟨index g.hh i,atIndex_index g.hh i⟩
    · intro tail j
      change selectedAnchor (rawRun g.initial
        (((g.u++g.v)++(g.past++w))++tail) (atIndex g.hh j).val).long=_
      rw [show (((g.u++g.v)++(g.past++w))++tail) = hist++(w++tail) by
        simp only [hist,List.append_assoc]]
      exact single tail j
  have loss := wordSum_mono (fun w => @ite Nat (bad w) (Classical.propDecidable _) 1 0)
    (fun w => @ite Nat (fail w) (Classical.propDecidable _) 1 0) (fun w => by
      by_cases h : bad w
      · simp only [if_pos h,if_pos (implies w h),Nat.le_refl]
      · simp only [if_neg h,Nat.zero_le]) D
  have depth : cap+1 ≤ lo+(m+233+32*(2^19*m)) := by
    have T : opening≤G+34 := F.2.1
    unfold cap
    change G≤lo+m/2 at span
    omega
  exact ⟨start,lo,G,opening,cap,rfl,rfl,depth,repr,lower,upper,
    Nat.le_trans (Nat.mul_le_mul_left _ loss) bound⟩

#print axioms trial_of_epoch_bounds
end L4.PhysicalClockDisplay

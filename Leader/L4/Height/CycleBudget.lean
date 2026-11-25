import Leader.L4.Height.RepairTime
import Leader.L4.Height.ProductionClients
import Leader.L4.Height.ProductionCustody
import Leader.L4.Height.ProductionWidths
import Leader.L4.Height.ResidualStages
import Leader.L4.BStarResidualBudget
import Leader.L4.BStarFiveClientBudget

namespace L4.Height.ProductionCustody
open AllSizeProtocol PhysicalCustody BStarH6WordChart BStarAcquireAnchors
open BStarSteeredLikelihood BStarRawBlockDrift
open Classical

noncomputable section

/-- All costs use the same candidate tape. The paid mass counts actual emitted
prescriptions. In particular this consumer does not multiply six success
probabilities or condition the candidate distribution on successful releases. -/
theorem block_of_cycle_costs {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (i : Header (oldH6 (rows s) g.base)) (L H : Nat)
    (link : L ≤ 11*width g) (line : H ≤ 2*width g)
    (mask : Word n → Fin n → Option (Fin n))
    (supported : ∀ a, BStarSteeringSupport.Supported _ g.hh (mask a))
    (cost : Word n → Nat) (client : Fin 5 → Word n → Nat)
    (spent : ∀ w, ¬ RawServiceCore.publishes x i.val (emit (chooseBy mask) [] w) →
      2^20*n*width g ≤ cost w)
    (mean : let t := 2*(2^20*n*width g)
      wordSum cost t ≤ 6*(n*(420*(4*L+10)+128*H))*n^t)
    (pace : ∀ j, let t := 2*(2^20*n*width g)
      wordSum (client j) t ≤ (81*2^20)*n^t)
    (paid : ∀ w, decisions (prescribed mask) [] (emit (chooseBy mask) [] w) ≤
      5+BStarFiveClientBudget.clientTotal client w) :
    let t := 2*(2^20*n*width g)
    n^t ≤ 2^(5*longBudget+1)*wordSum
      (fun w => if RawServiceCore.publishes x i.val w then 1 else 0) t := by
  let t := 2*(2^20*n*width g)
  let A := RawServiceCore.publishes x i.val
  have hn : 0 < n := Nat.zero_lt_of_lt i.val.isLt
  have time := BStarResidualBudget.time_fraction hn (width_bounds g).1 link line cost
    (fun w => ¬ A (emit (chooseBy mask) [] w)) spent mean
  have over := BStarFiveClientBudget.overflow_of_excess t client pace _ paid
  exact raw_block_of_separate_failures _ g.hh mask supported [] A t (5*longBudget) time over

/-- A first-hit bound for six sequential cycles yields the time term of
the raw change of measure. The latch makes every surviving tape pay its
entire observed length. The estimate spends only one of the two windows. -/
theorem time_of_stage_means {s n W : Nat} (hn : 0<n) (hw : 0<W) (x : Raw s n)
    (i : Fin n) (c : Word n → Fin n → Fin n) (stages : Nat → History s n → Prop)
    (finish : ∀ y, stages 0 y → y.published) (init : stages 6 (start x))
    (cycles : ∀ k,k<6 → ∀ y, stages (k+1) y →
      IIDExpectedHittingTimeAtMost (next c i) (fun z => stages k z ∨ z.published) y (2^15*n*W)) :
    let t := 2*(2^20*n*W)
    16 * wordSum (fun w => massInd (fun v => ¬RawServiceCore.publishes x i v)
      (emit c [] w)) t ≤ 3*n^t := by
  let D := 2^20*n*W
  let t := 2*D
  let A := 2^15*n*W
  let time := stoppedTime (next c i) (fun y : History s n => y.published) (start x)
  let miss (w : Word n) := massInd (fun v => ¬RawServiceCore.publishes x i v) (emit c [] w)
  have exp := ResidualStages.stage_list hn (next c i) _ A stages finish 6 cycles _ init t
  rw [iidHitCost_eq_wordSum] at exp
  have pay : D * wordSum miss t ≤ wordSum time t := by
    rw [←wordSum_mul_left]
    apply repair_wordSum_mono_length
    intro w len
    by_cases served : RawServiceCore.publishes x i (emit c [] w)
    · simp [miss,massInd,served]
    · have lost := fun h => served ((run_publication x c i w).mp h)
      have full := ResidualStages.wait_on_miss (next c i) _ (keep_publication c i) (start x) w lost
      change time w=w.length at full
      simp only [miss,massInd,if_pos served,Nat.mul_one]
      rw [full,len]
      dsimp only [t]
      omega
  have C : 16* (6*A) = 3*D := by
    dsimp only [D,A]
    calc
      _ = (16*6*2^15)*(n*W) := by ac_rfl
      _ = (3*2^20)*(n*W) := rfl
      _ = _ := by ac_rfl
  apply Nat.le_of_mul_le_mul_left (c:=D) _ (Nat.mul_pos (Nat.mul_pos (by decide) hn) hw)
  change D*(16*wordSum miss t) ≤ D*(3*n^t)
  calc
    _ = 16*(D*wordSum miss t) := by ac_rfl
    _ ≤ 16*((6*A)*n^t) := Nat.mul_le_mul_left _ (Nat.le_trans pay exp)
    _ = _ := by rw [←Nat.mul_assoc,C]; ac_rfl

theorem block_of_stage_means {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (P : Production g) (i : Header (oldH6 (rows s) g.base))
    (owner : BStarAcquireLiteralChain.Owners (oldH6 (rows s) g.base))
    (live : Fin 5 → Word n → Prop) (stages : Nat → History s n → Prop)
    (finish : ∀ y, stages 0 y → y.published) (init : stages 6 (start x))
    (means : ∀ k,k<6 → ∀ y, stages (k+1) y →
      IIDExpectedHittingTimeAtMost (next (chooseBy (ProductionClients.redirect g owner live)) i.val)
        (fun z => stages k z ∨ z.published) y (2^15*n*width g)) :
    let t := 2*(2^20*n*width g)
    n^t≤2^(5*longBudget+1)*wordSum (fun w =>
      if RawServiceCore.publishes x i.val w then 1 else 0) t := by
  let R := ProductionClients.redirect g owner live
  have mask : ∀ a, BStarSteeringSupport.Supported _ g.hh (R a) :=
    BStarParkedSteering.support_of_fresh (BStarParkedSteering.redirectTo_isFresh _ g.hh _ _)
  have time := time_of_stage_means (Nat.zero_lt_of_lt i.val.isLt) (width_bounds g).1
    x i.val (chooseBy R) stages finish init means
  exact raw_block_of_separate_failures _ g.hh R mask [] _ _ _ time
    (ProductionClients.production_overflow g P owner live)

/-- Six physical stage budgets suffice on this explicit five-client mask.
The decision overflow is discharged from this custody witness on the same tape. -/
theorem block_of_physical_cycles {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (P : Production g) (i : Header (oldH6 (rows s) g.base))
    (owner : BStarAcquireLiteralChain.Owners (oldH6 (rows s) g.base))
    (live : Fin 5 → Word n → Prop) (stages : Nat → History s n → Prop)
    (finish : ∀ y, stages 0 y → y.published) (init : stages 6 (start x))
    (cycles : ∀ k,k<6 → ∀ y, stages (k+1) y →
      ∃ (U : Type) (D : ResidualPotentialData (S:=U) (n:=n)) (proj : U → History s n) (z : U),
        proj z=y ∧ D.Q z ∧ D.Phi z≤2^15*n*width g ∧
        (∀ v,D.Q v → ∀ e,proj (D.next v e)=
          next (chooseBy (ProductionClients.redirect g owner live)) i.val (proj v) e) ∧
        ∀ v,D.Q v → D.P v → stages k (proj v) ∨ (proj v).published) :
    let t := 2*(2^20*n*width g)
    n^t≤2^(5*longBudget+1)*wordSum (fun w =>
      if RawServiceCore.publishes x i.val w then 1 else 0) t := by
  let R := ProductionClients.redirect g owner live
  have means (k : Nat) (h : k<6) (y : History s n) (atY : stages (k+1) y) :
      IIDExpectedHittingTimeAtMost (next (chooseBy R) i.val) (fun v => stages k v ∨ v.published) y
        (2^15*n*width g) := by
    obtain ⟨U,D,proj,z,eq,q,cap,commute,done⟩ := cycles k h y atY
    exact eq ▸ ResidualStages.projected_residual D proj (next (chooseBy R) i.val)
      (fun v => stages k v ∨ v.published) commute done z q cap
  exact block_of_stage_means g P i owner live stages finish init means

end
end L4.Height.ProductionCustody


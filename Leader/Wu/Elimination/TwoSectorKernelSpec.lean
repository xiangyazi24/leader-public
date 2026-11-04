import Leader.Core.FiniteUniformStoppingTree

namespace LDKernelSpec

set_option autoImplicit false

open FiniteUniformStoppingTree

inductive CleanPhase (d : Nat) where
  | ready
  | dummy (p : Nat) (hp : p < d)
  | live (p : Nat) (hp0 : 0 < p) (hp : p < d)
  | ret (q : Nat) (hq0 : 0 < q) (hq : q < d)

namespace CleanPhase

def isReady {d : Nat} : CleanPhase d → Bool
  | .ready => true
  | _ => false

end CleanPhase

inductive BlockRawCase where
  | leftIngress
  | atkInterior
  | middle
  | tgtInterior
  | rightEgress
  | signalProp
  | outside

/-- Data-only adapter.  The concrete four-field protocol instantiates the
lineage predicates from its actual ring cells. -/
structure LDKernel (n a b : Nat) where
  State : Type
  rawStep : State → Fin n → State
  deleted : State → Bool

  atkPhase : State → CleanPhase a
  tgtPhase : State → CleanPhase b

  atkLineage : State → CleanPhase a → Prop
  tgtLineage : State → CleanPhase b → Prop
  middleShared : State → CleanPhase a → CleanPhase b → Prop

  Lj : Fin n
  Rj : Fin n
  Lj_ne_Rj : Lj ≠ Rj

  /-- True exactly for the unique currently required progress edge of the
  target's right-sector shot/return; false at Ready. -/
  targetService : State → Fin n → Bool

  /-- Exhaustive primary-effect classification used only by the literal
  four-field adapter proof. -/
  caseOf : State → Fin n → BlockRawCase

def SealedTwoSector {n a b : Nat} (K : LDKernel n a b)
    (s : K.State) : Prop :=
  K.atkLineage s (K.atkPhase s) ∧
  K.tgtLineage s (K.tgtPhase s) ∧
  K.middleShared s (K.atkPhase s) (K.tgtPhase s)

def survives {n a b : Nat} (K : LDKernel n a b)
    (s : K.State) (e : Fin n) : Prop :=
  K.deleted (K.rawStep s e) ≠ true

/-- These are the seven literal-row obligations.  They are deliberately
smaller than L1 and should be proved directly from the four-field table. -/
structure ClosureCaseLaws {n a b : Nat} (K : LDKernel n a b) : Prop where
  leftIngress : ∀ s e,
    K.caseOf s e = .leftIngress →
    SealedTwoSector K s → survives K s e →
    SealedTwoSector K (K.rawStep s e)
  atkInterior : ∀ s e,
    K.caseOf s e = .atkInterior →
    SealedTwoSector K s → survives K s e →
    SealedTwoSector K (K.rawStep s e)
  middle : ∀ s e,
    K.caseOf s e = .middle →
    SealedTwoSector K s → survives K s e →
    SealedTwoSector K (K.rawStep s e)
  tgtInterior : ∀ s e,
    K.caseOf s e = .tgtInterior →
    SealedTwoSector K s → survives K s e →
    SealedTwoSector K (K.rawStep s e)
  rightEgress : ∀ s e,
    K.caseOf s e = .rightEgress →
    SealedTwoSector K s → survives K s e →
    SealedTwoSector K (K.rawStep s e)
  signalProp : ∀ s e,
    K.caseOf s e = .signalProp →
    SealedTwoSector K s → survives K s e →
    SealedTwoSector K (K.rawStep s e)
  outside : ∀ s e,
    K.caseOf s e = .outside →
    SealedTwoSector K s → survives K s e →
    SealedTwoSector K (K.rawStep s e)

/-- L1: on the no-tagged-deletion event every raw step preserves the sealed
product lineage. -/
theorem sealedTwoSector_closed
    {n a b : Nat} (K : LDKernel n a b) (L : ClosureCaseLaws K)
    (s : K.State) (e : Fin n)
    (hseal : SealedTwoSector K s) (hno : survives K s e) :
    SealedTwoSector K (K.rawStep s e) := by
  cases hcase : K.caseOf s e with
  | leftIngress => exact L.leftIngress s e hcase hseal hno
  | atkInterior => exact L.atkInterior s e hcase hseal hno
  | middle => exact L.middle s e hcase hseal hno
  | tgtInterior => exact L.tgtInterior s e hcase hseal hno
  | rightEgress => exact L.rightEgress s e hcase hseal hno
  | signalProp => exact L.signalProp s e hcase hseal hno
  | outside => exact L.outside s e hcase hseal hno

structure Joint {n a b : Nat} (K : LDKernel n a b) where
  cfg : K.State
  sealed : SealedTwoSector K cfg

def ready {n a b : Nat} (K : LDKernel n a b) (s : K.State) : Bool :=
  (K.tgtPhase s).isReady

def redirect {n a b : Nat} (K : LDKernel n a b)
    (s : K.State) (e : Fin n) : Fin n :=
  if ready K s && (e == K.Rj) then K.Lj else e

/-- The controlled scheduler only changes the raw symbol at Ready. -/
def controlledStep
    {n a b : Nat} (K : LDKernel n a b)
    (hclosed : ∀ s e, SealedTwoSector K s → survives K s e →
      SealedTwoSector K (K.rawStep s e))
    (s : Joint K) (e : Fin n) : StopNode (Joint K) :=
  let ee := redirect K s.cfg e
  let t := K.rawStep s.cfg ee
  if hdel : K.deleted t = true then
    .success
  else
    .active ⟨t, hclosed s.cfg ee s.sealed hdel⟩

/-- Remaining right-sector services until the target is Ready again. -/
def targetDebt (b : Nat) : CleanPhase b → Nat
  | .ready => 0
  | .dummy p _ => 2 * b - p - 1
  | .live p _ _ => 2 * b - p - 1
  | .ret q _ _ => q

/-- Service credit accumulated since the most recent target dummy firing. -/
def targetCredit (b : Nat) (p : CleanPhase b) : Nat :=
  (2 * b - 1) - targetDebt b p

def nodeTargetCredit {n a b : Nat} (K : LDKernel n a b) :
    StopNode (Joint K) → Nat
  | .active s => targetCredit b (K.tgtPhase s.cfg)
  | .success => 0
  | .failure => 0

/-- Under Q, both Ready incident raw symbols are the same dummy firing. -/
def dummyCost {n a b : Nat} (K : LDKernel n a b)
    (s : Joint K) (e : Fin n) : Nat :=
  if ready K s.cfg && ((e == K.Lj) || (e == K.Rj)) then 1 else 0

def serviceCost {n a b : Nat} (K : LDKernel n a b)
    (s : Joint K) (e : Fin n) : Nat :=
  if K.targetService s.cfg (redirect K s.cfg e) then 1 else 0

/-- Exact cost accumulated along the active prefix of one finite scheduler
word; suffix symbols after stopping are ignored. -/
def pathCost {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (cost : S → Fin n → Nat) :
    StopNode S → List (Fin n) → Nat
  | _, [] => 0
  | .active s, e :: es => cost s e + pathCost step cost (step s e) es
  | .success, _ => 0
  | .failure, _ => 0

/-- Edge-cost numerator: exact sum of path costs over all depth-T raw
scheduler words. -/
def edgeCostNumerator {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (cost : S → Fin n → Nat) :
    StopNode S → Nat → Nat
  | _, 0 => 0
  | .success, _ + 1 => 0
  | .failure, _ + 1 => 0
  | .active s, T + 1 =>
      n ^ T * (List.ofFn (fun e : Fin n => cost s e)).sum +
        (List.ofFn (fun e : Fin n =>
          edgeCostNumerator step cost (step s e) T)).sum

/-- Literal target-phase obligations.  `creditStep` is checked by the phase
cases Ready/Dummy/Return (Live is unreachable after the clean-dummy start under
Q, but may be handled monotonically). -/
structure TargetCycleLaws
    {n a b : Nat} (K : LDKernel n a b)
    (hclosed : ∀ s e, SealedTwoSector K s → survives K s e →
      SealedTwoSector K (K.rawStep s e)) : Prop where
  creditStep : ∀ s e,
    (2 * b - 1) * dummyCost K s e +
        nodeTargetCredit K (controlledStep K hclosed s e) ≤
      targetCredit b (K.tgtPhase s.cfg) + serviceCost K s e
  serviceUnique : ∀ s,
    (List.ofFn (fun e : Fin n => serviceCost K s e)).sum ≤ 1

/-- A one-step credit inequality telescopes along every finite active prefix.
The arbitrary initial credit is retained in the induction hypothesis. -/
private theorem pathCost_mul_le_credit_add
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (charge service : S → Fin n → Nat)
    (credit : StopNode S → Nat) (m : Nat)
    (hstep : ∀ s e,
      m * charge s e + credit (step s e) ≤
        credit (.active s) + service s e)
    (x : StopNode S) (w : List (Fin n)) :
    m * pathCost step charge x w ≤
      credit x + pathCost step service x w := by
  induction w generalizing x with
  | nil =>
      simp [pathCost]
  | cons e es ih =>
      cases x with
      | active s =>
          have hhead := hstep s e
          have htail := ih (step s e)
          simp only [pathCost, Nat.mul_add]
          omega
      | success =>
          simp [pathCost]
      | failure =>
          simp [pathCost]

/-- The same credit inequality lifts through a complete finite scheduler tree.
Each depth-T continuation carries one copy of the child's initial credit. -/
private theorem edgeCostNumerator_mul_le_credit_add
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (charge service : S → Fin n → Nat)
    (credit : StopNode S → Nat) (m : Nat)
    (hstep : ∀ s e,
      m * charge s e + credit (step s e) ≤
        credit (.active s) + service s e)
    (x : StopNode S) (T : Nat) :
    m * edgeCostNumerator step charge x T ≤
      n ^ T * credit x + edgeCostNumerator step service x T := by
  induction T generalizing x with
  | zero =>
      simp [edgeCostNumerator]
  | succ T ih =>
      cases x with
      | success =>
          simp [edgeCostNumerator]
      | failure =>
          simp [edgeCostNumerator]
      | active s =>
          have hpoint : ∀ e : Fin n,
              m * (n ^ T * charge s e +
                edgeCostNumerator step charge (step s e) T) ≤
              n ^ T * credit (.active s) +
                (n ^ T * service s e +
                  edgeCostNumerator step service (step s e) T) := by
            intro e
            have hhead := Nat.mul_le_mul_left (n ^ T) (hstep s e)
            have htail := ih (step s e)
            have hswap :
                m * (n ^ T * charge s e) =
                  n ^ T * (m * charge s e) := by
              ac_rfl
            simp only [Nat.mul_add] at hhead ⊢
            rw [hswap]
            omega
          calc
            m * edgeCostNumerator step charge (.active s) (T + 1) =
                (List.ofFn (fun e : Fin n =>
                  m * (n ^ T * charge s e +
                    edgeCostNumerator step charge (step s e) T))).sum := by
              simp only [edgeCostNumerator, ofFn_sum_mul_left, ofFn_sum_add]
            _ ≤ (List.ofFn (fun e : Fin n =>
                  n ^ T * credit (.active s) +
                    (n ^ T * service s e +
                      edgeCostNumerator step service (step s e) T))).sum :=
              ofFn_sum_le _ _ hpoint
            _ = n ^ (T + 1) * credit (.active s) +
                edgeCostNumerator step service (.active s) (T + 1) := by
              simp only [edgeCostNumerator, ofFn_sum_add,
                ofFn_sum_mul_left, ofFn_sum_const, Nat.pow_succ] <;>
                ac_rfl

/-- L2a: exact finite-path counting.  Start is immediately after the initial
clean dummy, so its target credit is zero. -/
theorem target_cycle_path_count
    {n a b : Nat} (K : LDKernel n a b)
    (hclosed : ∀ s e, SealedTwoSector K s → survives K s e →
      SealedTwoSector K (K.rawStep s e))
    (L : TargetCycleLaws K hclosed)
    (start : Joint K) (hb : 0 < b)
    (hstart : K.tgtPhase start.cfg = .dummy 0 hb)
    (w : List (Fin n)) :
    (2 * b - 1) *
        pathCost (controlledStep K hclosed) (dummyCost K) (.active start) w ≤
      pathCost (controlledStep K hclosed) (serviceCost K) (.active start) w := by
  have hcredit : nodeTargetCredit K (.active start) = 0 := by
    simp [nodeTargetCredit, hstart, targetCredit, targetDebt]
  have h := pathCost_mul_le_credit_add
    (controlledStep K hclosed) (dummyCost K) (serviceCost K)
    (nodeTargetCredit K) (2 * b - 1)
    (by
      intro s e
      exact L.creditStep s e)
    (.active start) w
  simpa only [hcredit, Nat.zero_add] using h

/-- L2b: lift the target-cycle credit bound over the complete depth-T
scheduler tree. -/
theorem target_cycle_numerator
    {n a b : Nat} (K : LDKernel n a b)
    (hclosed : ∀ s e, SealedTwoSector K s → survives K s e →
      SealedTwoSector K (K.rawStep s e))
    (L : TargetCycleLaws K hclosed)
    (start : Joint K) (hb : 0 < b)
    (hstart : K.tgtPhase start.cfg = .dummy 0 hb) (T : Nat) :
    (2 * b - 1) *
        edgeCostNumerator (controlledStep K hclosed) (dummyCost K)
          (.active start) T ≤
      edgeCostNumerator (controlledStep K hclosed) (serviceCost K)
        (.active start) T := by
  have hcredit : nodeTargetCredit K (.active start) = 0 := by
    simp [nodeTargetCredit, hstart, targetCredit, targetDebt]
  have h := edgeCostNumerator_mul_le_credit_add
    (controlledStep K hclosed) (dummyCost K) (serviceCost K)
    (nodeTargetCredit K) (2 * b - 1)
    (by
      intro s e
      exact L.creditStep s e)
    (.active start) T
  simpa only [hcredit, Nat.mul_zero, Nat.zero_add] using h

/-- There is at most one service-paying raw scheduler symbol at each active
node, hence service expectation is at most active time divided by n. -/
theorem target_service_numerator_le_active
    {n a b : Nat} (K : LDKernel n a b)
    (hclosed : ∀ s e, SealedTwoSector K s → survives K s e →
      SealedTwoSector K (K.rawStep s e))
    (L : TargetCycleLaws K hclosed) (x : StopNode (Joint K)) (T : Nat) :
    n * edgeCostNumerator (controlledStep K hclosed) (serviceCost K) x T ≤
      truncatedActiveCostNumerator (controlledStep K hclosed) x T := by
  induction T generalizing x with
  | zero =>
      simp [edgeCostNumerator, truncatedActiveCostNumerator]
  | succ T ih =>
      cases x with
      | success =>
          simp [edgeCostNumerator, truncatedActiveCostNumerator]
      | failure =>
          simp [edgeCostNumerator, truncatedActiveCostNumerator]
      | active s =>
          simp only [edgeCostNumerator, truncatedActiveCostNumerator,
            Nat.mul_add]
          apply Nat.add_le_add
          · calc
              n * (n ^ T *
                  (List.ofFn (fun e : Fin n => serviceCost K s e)).sum) =
                  n ^ (T + 1) *
                    (List.ofFn (fun e : Fin n => serviceCost K s e)).sum := by
                rw [Nat.pow_succ]
                ac_rfl
              _ ≤ n ^ (T + 1) * 1 :=
                Nat.mul_le_mul_left _ (L.serviceUnique s)
              _ = n ^ (T + 1) := Nat.mul_one _
          · rw [← ofFn_sum_mul_left]
            exact ofFn_sum_le _ _
              (fun e => ih (controlledStep K hclosed s e))

/-- L2c: exact division-free finite-horizon form of
    (2b-1) E_Q[N_T] ≤ E_Q[tau∧T]/n. -/
theorem redirected_firstMoment_numerator
    {n a b : Nat} (K : LDKernel n a b)
    (hclosed : ∀ s e, SealedTwoSector K s → survives K s e →
      SealedTwoSector K (K.rawStep s e))
    (L : TargetCycleLaws K hclosed)
    (start : Joint K) (hb : 0 < b)
    (hstart : K.tgtPhase start.cfg = .dummy 0 hb) (T : Nat) :
    n * ((2 * b - 1) *
      edgeCostNumerator (controlledStep K hclosed) (dummyCost K)
        (.active start) T) ≤
      truncatedActiveCostNumerator (controlledStep K hclosed)
        (.active start) T := by
  exact Nat.le_trans
    (Nat.mul_le_mul_left n
      (target_cycle_numerator K hclosed L start hb hstart T))
    (target_service_numerator_le_active K hclosed L (.active start) T)

/-- Direct bridge to the repo's Bellman API.  All terms share denominator n^T,
so this is the exact scheduler-tree version of the desired first-moment bound. -/
theorem redirected_firstMoment_of_natSuper
    {n a b : Nat} (K : LDKernel n a b)
    (hclosed : ∀ s e, SealedTwoSector K s → survives K s e →
      SealedTwoSector K (K.rawStep s e))
    (L : TargetCycleLaws K hclosed)
    (start : Joint K) (hb : 0 < b)
    (hstart : K.tgtPhase start.cfg = .dummy 0 hb)
    (V : StopNode (Joint K) → Nat)
    (hV : NatBellmanSuperSolution (controlledStep K hclosed) 1 V)
    (T : Nat) :
    n * ((2 * b - 1) *
      edgeCostNumerator (controlledStep K hclosed) (dummyCost K)
        (.active start) T) ≤
      n ^ T * V (.active start) := by
  have hcost :
      truncatedActiveCostNumerator (controlledStep K hclosed)
          (.active start) T ≤
        n ^ T * V (.active start) := by
    simpa only [Nat.one_mul] using
      truncatedActiveCostNumerator_mul_le_of_natSuperSolution
        (controlledStep K hclosed) 1 V hV (.active start) T
  exact Nat.le_trans
    (redirected_firstMoment_numerator K hclosed L start hb hstart T)
    hcost

#print axioms sealedTwoSector_closed
#print axioms target_cycle_path_count
#print axioms target_cycle_numerator
#print axioms target_service_numerator_le_active
#print axioms redirected_firstMoment_numerator
#print axioms redirected_firstMoment_of_natSuper

end LDKernelSpec

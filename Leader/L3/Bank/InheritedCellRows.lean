import Leader.L3.Bank.InheritedNonarmedRows

/-!
R7 (A): the shaped general-b BANK cell rows.

The inherited site weight is linear in the ghost atom counts. We
divide out the factor n and work on BankCell records: the physical
side is Base.bankPair on the two OLD cells, the ghost side is a
literal BankCell transcription of HeadlineRenewal.renewalBankPairMemory
(definitionally equal to it). The single core inequality

  after + A * armedY <= before + (A - 1) * armedX

is proved by splitting the first-match branches of both functions
in their own order. (A) is its specialisation armedX = 0; the ARMED
rows (B) use the same core in BankInheritedArmedRows.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ### Units: the site weight without the factor n -/

/-- Worker part of the inherited site weight, divided by n. -/
def bankCellWorkerUnits {n : Nat} (b : Nat) (tok : BTok)
    (role nb : Nat) : RenewalBankWorker n → Nat
  | .empty => 0
  | .pending _ => 0
  | .payload p =>
      bankInheritedWorkerPrice b tok role nb * p.atoms.length

/-- Controller part of the inherited site weight, divided by n. -/
def bankCellControllerUnits {n : Nat} (b : Nat) (mode : Mode)
    (lease : Nat) : RenewalBankController n → Nat
  | .empty => 0
  | .active p =>
      (if mode = .ARMED then bankInheritedArmedPrice b
        else bankInheritedComparisonPrice b) * p.atoms.length
  | .waiting atoms =>
      (bankInheritedComparisonPrice b + lease + 1) * atoms.length

/-- Site weight divided by n, read from a BankCell record and an
explicit PACK role (the cell's own role field is not used). -/
def bankCellSiteUnits {n : Nat} (b : Nat) (z : BankCell)
    (role nb : Nat) (s : RenewalBankSite n) : Nat :=
  bankCellWorkerUnits b z.tok role nb s.worker +
    bankCellControllerUnits b z.mode z.lease s.controller

/-- Inherited ARMED-root atom count of an OLD cell. -/
def bankCellArmed {n : Nat} (z : BankCell)
    (s : RenewalBankSite n) : Nat :=
  if z.role = 0 ∧ z.mode = .ARMED then
    bankInheritedControllerAtomCount s.controller
  else 0

@[simp] theorem bankCellWorkerUnitsEmpty {n : Nat} (b : Nat)
    (tok : BTok) (role nb : Nat) :
    bankCellWorkerUnits (n := n) b tok role nb .empty = 0 := rfl

@[simp] theorem bankCellWorkerUnitsPending {n : Nat} (b : Nat)
    (tok : BTok) (role nb : Nat) (r : RenewalBankReceipt n) :
    bankCellWorkerUnits b tok role nb (.pending r) = 0 := rfl

@[simp] theorem bankCellControllerUnitsEmpty {n : Nat} (b : Nat)
    (mode : Mode) (lease : Nat) :
    bankCellControllerUnits (n := n) b mode lease .empty = 0 := rfl

theorem bankCellWorkerUnitsPayload {n : Nat} (b : Nat)
    (tok : BTok) (role nb : Nat) (p : RenewalBankPayload n) :
    bankCellWorkerUnits b tok role nb (.payload p) =
      bankInheritedWorkerPrice b tok role nb * p.atoms.length := rfl

theorem bankCellControllerUnitsActive {n : Nat} (b : Nat)
    (mode : Mode) (lease : Nat) (p : RenewalBankPayload n) :
    bankCellControllerUnits b mode lease (.active p) =
      (if mode = .ARMED then bankInheritedArmedPrice b
        else bankInheritedComparisonPrice b) * p.atoms.length := rfl

theorem bankCellControllerUnitsWaiting {n : Nat} (b : Nat)
    (mode : Mode) (lease : Nat) (xs : List (RenewalBankAtom n)) :
    bankCellControllerUnits b mode lease (.waiting xs) =
      (bankInheritedComparisonPrice b + lease + 1) * xs.length := rfl

/-- A token-E worker weighs nothing, whatever its ghost. -/
@[simp] theorem bankCellWorkerUnitsTokE {n : Nat} (b : Nat)
    (role nb : Nat) (w : RenewalBankWorker n) :
    bankCellWorkerUnits b .E role nb w = 0 := by
  cases w with
  | empty => rfl
  | pending _ => rfl
  | payload p =>
      simp [bankCellWorkerUnits, bankInheritedWorkerPrice,
        bankInheritedWorkerBasePrice, bankInheritedWorkerPhasePrice,
        bankInheritedRRRepairCredit]

theorem bankCellSiteWeightUnits {n : Nat} (c : Compiled)
    (x : Agent c) (nb : Nat) (s : RenewalBankSite n) :
    bankInheritedSiteWeight c x nb s =
      n * bankCellSiteUnits c.b (bankCell x x.pack.val)
        x.pack.val nb s := by
  rcases s with ⟨w, v⟩
  unfold bankCellSiteUnits
  rw [Nat.mul_add]
  unfold bankInheritedSiteWeight
  congr 1
  · cases w with
    | empty => rfl
    | pending _ => rfl
    | payload p => exact Nat.mul_assoc _ _ _
  · cases v with
    | empty => rfl
    | active p => exact Nat.mul_assoc _ _ _
    | waiting xs => exact Nat.mul_assoc _ _ _

theorem bankCellEscrowUnits {n : Nat} (c : Compiled)
    (x : Agent c) (s : RenewalBankSite n) :
    bankInheritedCellEscrow c x s =
      n * (bankInheritedArmedPrice c.b - 1) *
        bankCellArmed (bankCell x x.pack.val) s := rfl

theorem bankCellArmedAgent {n : Nat} (c : Compiled)
    (x : Agent c) (s : RenewalBankSite n) :
    bankInheritedCellArmedAtoms x s =
      bankCellArmed (bankCell x x.pack.val) s := rfl

/-! ### Generic monotonicity facts -/

theorem bankCellWorkerUnitsMono {n : Nat} (b : Nat)
    (t t' : BTok) (r r' nb nb' : Nat) (w : RenewalBankWorker n)
    (h : bankInheritedWorkerPrice b t' r' nb' ≤
      bankInheritedWorkerPrice b t r nb) :
    bankCellWorkerUnits b t' r' nb' w ≤
      bankCellWorkerUnits b t r nb w := by
  cases w with
  | empty => exact Nat.le_refl 0
  | pending _ => exact Nat.le_refl 0
  | payload p =>
      exact Nat.mul_le_mul_right p.atoms.length h

theorem bankCellControllerUnitsLease {n : Nat} (b : Nat)
    (m : Mode) (l l' : Nat) (v : RenewalBankController n)
    (h : l' ≤ l) :
    bankCellControllerUnits b m l' v ≤
      bankCellControllerUnits b m l v := by
  cases v with
  | empty => exact Nat.le_refl 0
  | active p => exact Nat.le_refl _
  | waiting xs =>
      exact Nat.mul_le_mul_right xs.length (by omega)

theorem bankCellSiteUnitsLease {n : Nat} (b : Nat)
    (z z' : BankCell) (role nb : Nat) (s : RenewalBankSite n)
    (ht : z'.tok = z.tok) (hm : z'.mode = z.mode)
    (hl : z'.lease ≤ z.lease) :
    bankCellSiteUnits b z' role nb s ≤
      bankCellSiteUnits b z role nb s := by
  unfold bankCellSiteUnits
  rw [ht, hm]
  exact Nat.add_le_add_left
    (bankCellControllerUnitsLease b z.mode z.lease z'.lease
      s.controller hl) _

theorem bankCellComparisonGe (b : Nat) :
    bankInheritedArmedPrice b ≤ bankInheritedComparisonPrice b := by
  unfold bankInheritedComparisonPrice
  omega

/-- The responder's ARMED escrow, with one more unit per atom, is
covered by its own OLD controller weight. -/
theorem bankCellArmedEscrowLe {n : Nat} (b : Nat) (z : BankCell)
    (s : RenewalBankSite n) :
    bankInheritedArmedPrice b * bankCellArmed z s ≤
      bankCellControllerUnits b z.mode z.lease s.controller := by
  unfold bankCellArmed
  by_cases h : z.role = 0 ∧ z.mode = .ARMED
  · rw [if_pos h]
    rcases s with ⟨w, v⟩
    cases v with
    | empty => exact Nat.le_refl 0
    | active p =>
        show bankInheritedArmedPrice b * p.atoms.length ≤
          (if z.mode = .ARMED then bankInheritedArmedPrice b
            else bankInheritedComparisonPrice b) * p.atoms.length
        rw [if_pos h.2]
        exact Nat.le_refl _
    | waiting xs =>
        show bankInheritedArmedPrice b * xs.length ≤
          (bankInheritedComparisonPrice b + z.lease + 1) * xs.length
        have hc := bankCellComparisonGe b
        exact Nat.mul_le_mul_right xs.length (by omega)
  · rw [if_neg h, Nat.mul_zero]
    exact Nat.zero_le _

/-- At the ring successor determined by the move itself, the RR
repair credit is zero: packNext is idempotent on its own output. -/
theorem bankCellPackNextIdem (a c b : Nat) :
    packNext a (packNext a c b) b = packNext a c b := by
  unfold packNext
  by_cases h1 : a < b
  · simp [h1]
  · by_cases h2 : a = b
    · by_cases h3 : c = 0
      · simp [h2, h3]
      · simp [h2, h3]
    · simp [h1, h2]

theorem bankCellPriceAtPost (b : Nat) (t : BTok) (a c : Nat) :
    bankInheritedWorkerPrice b t a (packNext a c b) ≤
      bankInheritedWorkerPrice b t a c := by
  have h0 : bankInheritedRRRepairCredit b a (packNext a c b) t = 0 := by
    unfold bankInheritedRRRepairCredit
    rw [bankCellPackNextIdem]
    simp
  unfold bankInheritedWorkerPrice
  rw [h0]
  omega

theorem bankCellPackNextLe (a c b : Nat) : packNext a c b ≤ b + 1 := by
  unfold packNext
  split
  · omega
  · split
    · split <;> omega
    · omega

/-! ### The ghost observer on BankCell records -/

/-- Literal BankCell transcription of renewalBankPairMemory: the
same statements in the same order, with bx, cy given as records and
the two OLD sites and the service clock passed explicitly. -/
def bankCellMemory {n : Nat} (b : Nat)
    (sx0 sy0 : RenewalBankSite n) (service : Nat)
    (e dest : Fin n) (bx cy : BankCell) :
    RenewalBankSite n × RenewalBankSite n := Id.run do
  let postRole := packNext bx.role cy.role b
  let changed := postRole != cy.role
  let mut sx := sx0
  let mut sy := sy0
  if changed then
    sy := { worker := .empty, controller := .empty }
  if bx.role != 0 then
    sx := { sx with controller := .empty }
  if postRole != 0 then
    sy := { sy with controller := .empty }
  if !(1 ≤ bx.role && bx.role ≤ b) then
    sx := { sx with worker := .empty }
  if !(1 ≤ postRole && postRole ≤ b) then
    sy := { sy with worker := .empty }
  if postRole == 0 && !changed then
    if cy.grant || cy.mode == .ARMED then
      sy := { sy with controller := .empty }
    else
      sy := { sy with controller :=
        renewalBankWaitSlot cy.mode cy.lease sy.controller }
  if bx.role == 0 then
    if bx.grant then
      sx := { sx with controller := .empty }
      if !changed && postRole == 1 then
        sy := { sy with worker := .empty }
      return (sx, sy)
    if changed then
      if bx.mode == .ARMED || bx.mode == .CSTART then
        sx := { sx with controller := .empty }
      else
        sx := { sx with controller :=
          renewalBankWaitSlot bx.mode bx.lease sx.controller }
      return (sx, sy)
    if postRole != 1 then
      sx := { sx with controller :=
        renewalBankWaitSlot bx.mode bx.lease sx.controller }
      return (sx, sy)
    if bx.mode == .RESET then
      sx := { sx with controller := .waiting [] }
      sy := { sy with worker :=
        (.pending { service := service, root := e }) }
      return (sx, sy)
    if isRetTok cy.tok then
      let oldWorker := sy.worker
      sy := { sy with worker := .empty }
      if cy.tok == .RL && bx.mode == .RWAIT then
        match oldWorker with
        | .pending receipt =>
            sx := { sx with controller := .active ({ atoms := renewalBankWaitingAtoms sx.controller, origin := some { service := service, root := e, receipt := receipt }, heads := 0 }) }
        | _ =>
            sx := { sx with controller := .active (renewalBankReturned sx.controller oldWorker dest) }
        return (sx, sy)
      if cy.tok == .AL && bx.mode == .IWAIT then
        sx := { sx with controller := .active (renewalBankReturned sx.controller oldWorker dest) }
        return (sx, sy)
      if (cy.tok == .CL0 || cy.tok == .CL1) &&
          bx.mode == .CWAIT then
        if cy.tok == .CL0 then
          sx := { sx with controller := .active (renewalBankReturned sx.controller oldWorker dest) }
        else
          sx := { sx with controller := .empty }
        return (sx, sy)
      sx := { sx with controller :=
        renewalBankWaitSlot bx.mode bx.lease sx.controller }
      return (sx, sy)
    if bx.mode == .ARMED then
      if cy.tok != .E then
        sx := { sx with controller := .empty }
        sy := { sy with worker := .empty }
        return (sx, sy)
      if cy.bit == false then
        sx := { sx with controller := .active (renewalBankHead (renewalBankActivePayload sx.controller e)) }
        return (sx, sy)
      sy := { sy with worker := .payload (renewalBankHead (renewalBankActivePayload sx.controller e)) }
      sx := { sx with controller := .waiting [] }
      return (sx, sy)
    if bx.mode == .CSTART then
      if cy.tok != .E then
        sx := { sx with controller := .empty }
        sy := { sy with worker := .empty }
        return (sx, sy)
      sy := { sy with worker := .payload (renewalBankActivePayload sx.controller e) }
      sx := { sx with controller := .waiting [] }
      return (sx, sy)
    if b == 1 then
      if cy.tok == .IR then
        sy := { sy with worker := .empty }
    sx := { sx with controller :=
      renewalBankWaitSlot bx.mode bx.lease sx.controller }
    return (sx, sy)
  if changed then
    if 1 ≤ bx.role && bx.role < b &&
        (bx.tok == .IR || bx.tok == .CR0 || bx.tok == .CR1) then
      sx := { sx with worker := .empty }
    return (sx, sy)
  if bx.role == b && bx.tok == .IR then
    sx := { sx with worker := .empty }
  if postRole == b && cy.tok == .IR then
    sy := { sy with worker := .empty }
  if 1 ≤ bx.role && bx.role < b && postRole == bx.role + 1 then
    if bx.tok == .RR then
      sy := { sy with worker := sx.worker }
      sx := { sx with worker := .empty }
      return (sx, sy)
    if postRole == b && cy.tok == .RR then
      sx := { sx with worker := sy.worker }
      sy := { sy with worker := .empty }
      return (sx, sy)
    if cy.tok == .RL then
      sx := { sx with worker := sy.worker }
      sy := { sy with worker := .empty }
      return (sx, sy)
    if bx.tok != .E &&
        (if postRole == b && cy.tok == .IR then false
         else cy.tok != .E) then
      sx := { sx with worker := .empty }
      sy := { sy with worker := .empty }
      return (sx, sy)
    if postRole == b && (cy.tok == .CR0 || cy.tok == .CR1) then
      sx := { sx with worker := sy.worker }
      sy := { sy with worker := .empty }
      return (sx, sy)
    if cy.tok == .AL || cy.tok == .CL0 || cy.tok == .CL1 then
      sx := { sx with worker := sy.worker }
      sy := { sy with worker := .empty }
      return (sx, sy)
    if bx.tok == .IR then
      sy := { sy with worker := sx.worker }
      sx := { sx with worker := .empty }
      return (sx, sy)
    if bx.tok == .CR0 || bx.tok == .CR1 then
      sy := { sy with worker := sx.worker }
      sx := { sx with worker := .empty }
      return (sx, sy)
  return (sx, sy)

theorem bankCellMemoryEq {n : Nat} (c : Compiled)
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c) :
    renewalBankPairMemory c m e dest x y =
      bankCellMemory c.b (m.sites e) (m.sites dest) m.service
        e dest (bankCell x x.pack.val) (bankCell y y.pack.val) := rfl

/-! ### The cell goal -/

/-- The core cell inequality on BankCell records. -/
def BankCellGoal {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (sx sy : RenewalBankSite n) : Prop :=
  bankCellSiteUnits b
      (bankPair x0 y0 (packNext x0.role y0.role b) b θ).1
      x0.role (packNext x0.role y0.role b)
      (bankCellMemory b sx sy service e dest x0 y0).1 +
    bankCellSiteUnits b
      (bankPair x0 y0 (packNext x0.role y0.role b) b θ).2
      (packNext x0.role y0.role b) k
      (bankCellMemory b sx sy service e dest x0 y0).2 +
    bankInheritedArmedPrice b * bankCellArmed y0 sy ≤
  bankCellSiteUnits b x0 x0.role y0.role sx +
    bankCellSiteUnits b y0 y0.role k sy +
    (bankInheritedArmedPrice b - 1) * bankCellArmed x0 sx

/-! ### Price arithmetic -/

theorem bankCellArmedPriceEq (b : Nat) :
    bankInheritedArmedPrice b = 16 * b + 20 := by
  unfold bankInheritedArmedPrice bankInheritedWorkerCap
  omega

theorem bankCellComparisonPriceEq (b : Nat) :
    bankInheritedComparisonPrice b = 24 * b + 28 := by
  unfold bankInheritedComparisonPrice bankInheritedArmedPrice
    bankInheritedWorkerCap
  omega

theorem bankCellBaseValues (b : Nat) :
    bankInheritedWorkerBasePrice b .RL = bankInheritedArmedPrice b ∧
    bankInheritedWorkerBasePrice b .AL =
      bankInheritedComparisonPrice b ∧
    bankInheritedWorkerBasePrice b .CL0 = bankInheritedArmedPrice b ∧
    bankInheritedWorkerBasePrice b .CL1 = 0 ∧
    bankInheritedWorkerBasePrice b .IR =
      bankInheritedComparisonPrice b ∧
    bankInheritedWorkerBasePrice b .CR0 = bankInheritedArmedPrice b ∧
    bankInheritedWorkerBasePrice b .CR1 = bankInheritedArmedPrice b :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bankCellPriceRet (b r nb : Nat) (t : BTok) (h : r ≤ b)
    (ht : t = .RL ∨ t = .AL ∨ t = .CL0 ∨ t = .CL1) :
    bankInheritedWorkerPrice b t r nb =
      bankInheritedWorkerBasePrice b t + r + 1 := by
  have hm : min r b = r := Nat.min_eq_left h
  rcases ht with rfl | rfl | rfl | rfl <;>
    simp only [bankInheritedWorkerPrice, bankInheritedWorkerPhasePrice,
      bankInheritedRRRepairCredit, hm] <;>
    simp <;> omega

theorem bankCellPriceFwd (b r nb : Nat) (t : BTok)
    (ht : t = .IR ∨ t = .CR0 ∨ t = .CR1) :
    bankInheritedWorkerPrice b t r nb =
      bankInheritedWorkerBasePrice b t + (2 * (b - r) + b + 2) := by
  rcases ht with rfl | rfl | rfl <;>
    simp only [bankInheritedWorkerPrice, bankInheritedWorkerPhasePrice,
      bankInheritedRRRepairCredit] <;>
    simp

theorem bankCellPriceRR (b r nb : Nat) :
    bankInheritedArmedPrice b + (2 * (b - r) + b + 2) ≤
      bankInheritedWorkerPrice b .RR r nb ∧
    bankInheritedWorkerPrice b .RR r nb ≤
      bankInheritedArmedPrice b + (2 * (b - r) + b + 2) + 1 := by
  have h := bankInheritedRRRepairCreditLe b r nb .RR
  have hbase : bankInheritedWorkerBasePrice b .RR =
      bankInheritedArmedPrice b := rfl
  have hphase : bankInheritedWorkerPhasePrice b .RR r =
      2 * (b - r) + b + 2 := rfl
  unfold bankInheritedWorkerPrice
  rw [hbase, hphase]
  omega

theorem bankCellPriceRetBack (b a k : Nat) (t : BTok)
    (ht : t = .RL ∨ t = .AL ∨ t = .CL0 ∨ t = .CL1)
    (h : a + 1 ≤ b) :
    bankInheritedWorkerPrice b t a (a + 1) ≤
      bankInheritedWorkerPrice b t (a + 1) k := by
  rw [bankCellPriceRet b a (a + 1) t (by omega) ht,
    bankCellPriceRet b (a + 1) k t h ht]
  omega

theorem bankCellPriceFwdStep (b a k : Nat) (t t' : BTok)
    (ht : t = .IR ∨ t = .CR0 ∨ t = .CR1)
    (ht' : t' = .IR ∨ t' = .CR0 ∨ t' = .CR1)
    (hbase : bankInheritedWorkerBasePrice b t' =
      bankInheritedWorkerBasePrice b t)
    (h : a < b) :
    bankInheritedWorkerPrice b t' (a + 1) k ≤
      bankInheritedWorkerPrice b t a (a + 1) := by
  rw [bankCellPriceFwd b (a + 1) k t' ht',
    bankCellPriceFwd b a (a + 1) t ht, hbase]
  omega

theorem bankCellPriceIRToAL (b a k : Nat) (h : a < b) :
    bankInheritedWorkerPrice b .AL (a + 1) k ≤
      bankInheritedWorkerPrice b .IR a (a + 1) := by
  rw [bankCellPriceRet b (a + 1) k .AL (by omega) (by simp),
    bankCellPriceFwd b a (a + 1) .IR (by simp)]
  have h1 := (bankCellBaseValues b).2.1
  have h2 := (bankCellBaseValues b).2.2.2.2.1
  rw [h1, h2]
  omega

theorem bankCellPriceRRTop (a k : Nat) :
    bankInheritedWorkerPrice (a + 1) .RL a (a + 1) ≤
      bankInheritedWorkerPrice (a + 1) .RR (a + 1) k := by
  rw [bankCellPriceRet (a + 1) a (a + 1) .RL (by omega) (by simp)]
  have h := (bankCellPriceRR (a + 1) (a + 1) k).1
  have h1 := (bankCellBaseValues (a + 1)).1
  rw [h1]
  omega

theorem bankCellPriceCRTop (a k : Nat) :
    bankInheritedWorkerPrice (a + 1) .CL1 a (a + 1) ≤
      bankInheritedWorkerPrice (a + 1) .CR1 (a + 1) k ∧
    bankInheritedWorkerPrice (a + 1) .CL0 a (a + 1) ≤
      bankInheritedWorkerPrice (a + 1) .CR0 (a + 1) k := by
  rw [bankCellPriceRet (a + 1) a (a + 1) .CL1 (by omega) (by simp),
    bankCellPriceRet (a + 1) a (a + 1) .CL0 (by omega) (by simp),
    bankCellPriceFwd (a + 1) (a + 1) k .CR1 (by simp),
    bankCellPriceFwd (a + 1) (a + 1) k .CR0 (by simp)]
  have hv := bankCellBaseValues (a + 1)
  rw [hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2]
  omega

theorem bankCellPriceRootReturn (b k : Nat) (hb : 1 ≤ b) :
    bankInheritedArmedPrice b ≤ bankInheritedWorkerPrice b .RL 1 k ∧
    bankInheritedComparisonPrice b ≤
      bankInheritedWorkerPrice b .AL 1 k ∧
    bankInheritedArmedPrice b ≤ bankInheritedWorkerPrice b .CL0 1 k := by
  rw [bankCellPriceRet b 1 k .RL hb (by simp),
    bankCellPriceRet b 1 k .AL hb (by simp),
    bankCellPriceRet b 1 k .CL0 hb (by simp)]
  have hv := bankCellBaseValues b
  rw [hv.1, hv.2.1, hv.2.2.1]
  omega

theorem bankCellPriceRootIssue (b k : Nat) :
    bankInheritedWorkerPrice b .CR0 1 k ≤
      bankInheritedComparisonPrice b ∧
    bankInheritedWorkerPrice b .CR1 1 k ≤
      bankInheritedComparisonPrice b := by
  rw [bankCellPriceFwd b 1 k .CR0 (by simp),
    bankCellPriceFwd b 1 k .CR1 (by simp)]
  have hv := bankCellBaseValues b
  rw [hv.2.2.2.2.2.1, hv.2.2.2.2.2.2, bankCellComparisonPriceEq,
    bankCellArmedPriceEq]
  omega

theorem bankCellPriceRootFire (b k : Nat) :
    bankInheritedComparisonPrice b ≤
      bankInheritedArmedPrice b + (bankInheritedArmedPrice b - 1) ∧
    bankInheritedWorkerPrice b .IR 1 k ≤
      bankInheritedArmedPrice b + (bankInheritedArmedPrice b - 1) := by
  rw [bankCellPriceFwd b 1 k .IR (by simp)]
  have hv := bankCellBaseValues b
  rw [hv.2.2.2.2.1, bankCellComparisonPriceEq, bankCellArmedPriceEq]
  omega

/-- Abstract controller bound used by the root return merges. -/
theorem bankCellWaitingAtomsLe {n : Nat} (b : Nat) (mode : Mode)
    (lease : Nat) (v : RenewalBankController n) (q : Nat)
    (hq : q ≤ bankInheritedComparisonPrice b + lease + 1) :
    q * (renewalBankWaitingAtoms v).length ≤
      bankCellControllerUnits b mode lease v := by
  cases v with
  | empty => exact Nat.le_refl 0
  | active p => exact Nat.zero_le _
  | waiting xs => exact Nat.mul_le_mul_right xs.length hq

/-! ### Region: root source, changed responder role -/

theorem bankCellGoalRootChanged {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat) (gx : Bool)
    (c0 : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n) (hb : 2 ≤ b)
    (hc : c0 ≠ 1) :
    BankCellGoal b k θ service e dest
      ⟨0, mx, bitx, tx, lx, gx⟩ ⟨c0, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hpos : 0 < b := by omega
  have hp : packNext 0 c0 b = 1 := by simp [packNext, hpos]
  have hc' : 1 ≠ c0 := fun h => hc h.symm
  have hone : 1 ≤ b := by omega
  have hw := bankCellControllerUnitsLease b mx lx (lx - 1) vX
    (Nat.sub_le lx 1)
  have hesc : bankInheritedArmedPrice b *
      bankCellArmed (⟨c0, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits b my ly vY :=
    bankCellArmedEscrowLe b _ _
  cases gx <;> cases mx <;> by_cases hl : 1 < lx <;>
    simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      bankCellControllerUnitsWaiting,
      renewalBankWaitSlot, isWaitMode, hp, hc, hc', hone, hl] <;>
    omega

/-! ### Region: nonroot source, changed responder role -/

theorem bankCellGoalInteriorChanged {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool) (c0 : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n)
    (ha : 1 ≤ a) (hab : a < b) (hc : c0 ≠ a + 1) :
    BankCellGoal b k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨c0, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hp : packNext a c0 b = a + 1 := by simp [packNext, hab]
  have ha0 : a ≠ 0 := by omega
  have hab' : a ≤ b := by omega
  have hpb : a + 1 ≤ b := by omega
  have hc' : a + 1 ≠ c0 := fun h => hc h.symm
  have hcred : bankCellWorkerUnits b tx a (a + 1) wX ≤
      bankCellWorkerUnits b tx a c0 wX := by
    have h := bankCellPriceAtPost b tx a c0
    rw [hp] at h
    exact bankCellWorkerUnitsMono b tx tx a a c0 (a + 1) wX h
  have hesc : bankInheritedArmedPrice b *
      bankCellArmed (⟨c0, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits b my ly vY :=
    bankCellArmedEscrowLe b _ _
  cases tx <;>
    simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      hp, ha0, ha, hab, hab', hpb, hc, hc'] at hcred ⊢ <;>
    omega

theorem bankCellGoalTopChanged {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool) (c0 : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n) (hb : 2 ≤ b)
    (hc0 : c0 ≠ 0) (hc1 : c0 ≠ b + 1) :
    BankCellGoal b k θ service e dest
      ⟨b, mx, bitx, tx, lx, gx⟩ ⟨c0, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hp : packNext b c0 b = b + 1 := by simp [packNext, hc0]
  have hbz : b ≠ 0 := by omega
  have hone : 1 ≤ b := by omega
  have hout : ¬ b + 1 ≤ b := by omega
  have hc1' : b + 1 ≠ c0 := fun h => hc1 h.symm
  have hcred : bankCellWorkerUnits b tx b (b + 1) wX ≤
      bankCellWorkerUnits b tx b c0 wX := by
    have h := bankCellPriceAtPost b tx b c0
    rw [hp] at h
    exact bankCellWorkerUnitsMono b tx tx b b c0 (b + 1) wX h
  have hesc : bankInheritedArmedPrice b *
      bankCellArmed (⟨c0, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits b my ly vY :=
    bankCellArmedEscrowLe b _ _
  simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
    hp, hbz, hone, hout, hc0, hc1, hc1']
  omega

theorem bankCellGoalBeyondChanged {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool) (c0 : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n)
    (hab : b < a) (hc0 : c0 ≠ 0) :
    BankCellGoal b k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨c0, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hlt : ¬ a < b := by omega
  have hne : a ≠ b := by omega
  have hp : packNext a c0 b = 0 := by simp [packNext, hlt, hne]
  have ha0 : a ≠ 0 := by omega
  have hnle : ¬ a ≤ b := by omega
  have hc0' : 0 ≠ c0 := fun h => hc0 h.symm
  have hesc : bankInheritedArmedPrice b *
      bankCellArmed (⟨c0, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits b my ly vY :=
    bankCellArmedEscrowLe b _ _
  simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
    hp, ha0, hnle, hc0, hc0']
  omega

/-! ### Region: root source onto the first digit (a = 0, c0 = 1) -/

theorem bankCellGoalRootGrant {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n) (hb : 2 ≤ b) :
    BankCellGoal b k θ service e dest
      ⟨0, mx, bitx, tx, lx, true⟩ ⟨1, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hpos : 0 < b := by omega
  have hp : packNext 0 1 b = 1 := by simp [packNext, hpos]
  have hone : 1 ≤ b := by omega
  have hesc : bankInheritedArmedPrice b *
      bankCellArmed (⟨1, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits b my ly vY :=
    bankCellArmedEscrowLe b _ _
  simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
    hp, hone]
  omega

/-- RESET launch, the three return merges, their mismatches and
the plain waiting tick, with the worker shape of the responder. -/
theorem bankCellGoalRootWait {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n) (hb : 2 ≤ b)
    (hmx : mx ≠ .ARMED ∧ mx ≠ .CSTART)
    (hwY : bankInFlightWorkerShape ty wY) :
    BankCellGoal b k θ service e dest
      ⟨0, mx, bitx, tx, lx, false⟩ ⟨1, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hpos : 0 < b := by omega
  have hp : packNext 0 1 b = 1 := by simp [packNext, hpos]
  have hone : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  have hc := bankCellComparisonGe b
  have hw := bankCellControllerUnitsLease b mx lx (lx - 1) vX
    (Nat.sub_le lx 1)
  have hwa := bankCellWaitingAtomsLe b mx lx vX
    (bankInheritedArmedPrice b) (by omega)
  have hwc := bankCellWaitingAtomsLe b mx lx vX
    (bankInheritedComparisonPrice b) (by omega)
  have hprice := bankCellPriceRootReturn b k hone
  rcases wY with _ | r | q
  · have hesc : bankInheritedArmedPrice b *
        bankCellArmed (⟨1, my, bity, ty, ly, gy⟩ : BankCell)
          (⟨.empty, vY⟩ : RenewalBankSite n) ≤
        bankCellControllerUnits b my ly vY :=
      bankCellArmedEscrowLe b _ _
    cases mx <;> cases ty <;> by_cases hl : 1 < lx <;>
      simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      bankCellControllerUnitsWaiting,
        renewalBankWaitSlot, isWaitMode, isRetTok,
        renewalBankReturned, renewalBankWorkerPayload,
        bankInFlightWorkerShape,
        Nat.mul_add, hp, hone, hbne, hl] at hwY hmx ⊢ <;>
      omega
  · have hesc : bankInheritedArmedPrice b *
        bankCellArmed (⟨1, my, bity, ty, ly, gy⟩ : BankCell)
          (⟨.pending r, vY⟩ : RenewalBankSite n) ≤
        bankCellControllerUnits b my ly vY :=
      bankCellArmedEscrowLe b _ _
    cases mx <;> cases ty <;> by_cases hl : 1 < lx <;>
      simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      bankCellControllerUnitsWaiting,
        renewalBankWaitSlot, isWaitMode, isRetTok,
        renewalBankReturned, renewalBankWorkerPayload,
        bankInFlightWorkerShape,
        Nat.mul_add, hp, hone, hbne, hl] at hwY hmx ⊢ <;>
      omega
  · have hesc : bankInheritedArmedPrice b *
        bankCellArmed (⟨1, my, bity, ty, ly, gy⟩ : BankCell)
          (⟨.payload q, vY⟩ : RenewalBankSite n) ≤
        bankCellControllerUnits b my ly vY :=
      bankCellArmedEscrowLe b _ _
    have hq1 := Nat.mul_le_mul_right q.atoms.length hprice.1
    have hq2 := Nat.mul_le_mul_right q.atoms.length hprice.2.1
    have hq3 := Nat.mul_le_mul_right q.atoms.length hprice.2.2
    cases mx <;> cases ty <;> by_cases hl : 1 < lx <;>
      simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      bankCellControllerUnitsWaiting,
        renewalBankWaitSlot, isWaitMode, isRetTok,
        renewalBankReturned, renewalBankWorkerPayload,
        bankInFlightWorkerShape,
        Nat.mul_add, hp, hone, hbne, hl] at hwY hmx ⊢ <;>
      omega

/-- ARMED root: abort, CSTART (bit 0) and IR fire (bit 1); the
root's own escrow pays the price rise of its stock. -/
theorem bankCellGoalRootArmed {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (bitx : Bool) (tx : BTok) (lx : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (p : RenewalBankPayload n)
    (vY : RenewalBankController n) (hb : 2 ≤ b) :
    BankCellGoal b k θ service e dest
      ⟨0, .ARMED, bitx, tx, lx, false⟩ ⟨1, my, bity, ty, ly, gy⟩
      ⟨wX, .active p⟩ ⟨wY, vY⟩ := by
  have hpos : 0 < b := by omega
  have hp : packNext 0 1 b = 1 := by simp [packNext, hpos]
  have hone : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  have hax : bankCellArmed
      (⟨0, .ARMED, bitx, tx, lx, false⟩ : BankCell)
      (⟨wX, .active p⟩ : RenewalBankSite n) = p.atoms.length := rfl
  have hesc : bankInheritedArmedPrice b *
      bankCellArmed (⟨1, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits b my ly vY :=
    bankCellArmedEscrowLe b _ _
  have hfire := bankCellPriceRootFire b k
  have hf1 : bankInheritedComparisonPrice b * p.atoms.length ≤
      bankInheritedArmedPrice b * p.atoms.length +
        (bankInheritedArmedPrice b - 1) * p.atoms.length := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right _ hfire.1
  have hf2 : bankInheritedWorkerPrice b .IR 1 k * p.atoms.length ≤
      bankInheritedArmedPrice b * p.atoms.length +
        (bankInheritedArmedPrice b - 1) * p.atoms.length := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right _ hfire.2
  unfold BankCellGoal
  rw [hax]
  cases ty <;> cases bity <;>
    simp [bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      bankCellControllerUnitsWaiting,
      renewalBankWaitSlot, isWaitMode, isRetTok,
      renewalBankActivePayload, renewalBankHead,
      hp, hone, hbne] <;>
    omega

/-- CSTART root: abort or issue CR0/CR1 at the first digit. -/
theorem bankCellGoalRootCStart {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (bitx : Bool) (tx : BTok) (lx : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (p : RenewalBankPayload n)
    (vY : RenewalBankController n) (hb : 2 ≤ b) :
    BankCellGoal b k θ service e dest
      ⟨0, .CSTART, bitx, tx, lx, false⟩ ⟨1, my, bity, ty, ly, gy⟩
      ⟨wX, .active p⟩ ⟨wY, vY⟩ := by
  have hpos : 0 < b := by omega
  have hp : packNext 0 1 b = 1 := by simp [packNext, hpos]
  have hone : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  have hesc : bankInheritedArmedPrice b *
      bankCellArmed (⟨1, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits b my ly vY :=
    bankCellArmedEscrowLe b _ _
  have hissue := bankCellPriceRootIssue b k
  have hc0 := Nat.mul_le_mul_right p.atoms.length hissue.1
  have hc1 := Nat.mul_le_mul_right p.atoms.length hissue.2
  cases ty <;> cases bity <;> cases hθ : θ 0 <;>
    simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      bankCellControllerUnitsWaiting,
      renewalBankWaitSlot, isWaitMode, isRetTok,
      renewalBankActivePayload, hp, hone, hbne, hθ] <;>
    omega

/-! ### Region: consecutive interior digits (c0 = a + 1) -/

theorem bankCellGoalInteriorStep {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n)
    (ha : 1 ≤ a) (htop : a + 1 < b) :
    BankCellGoal b k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨a + 1, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hab : a < b := by omega
  have hp : packNext a (a + 1) b = a + 1 := by simp [packNext, hab]
  have ha0 : a ≠ 0 := by omega
  have hab' : a ≤ b := by omega
  have hpb : a + 1 ≤ b := by omega
  have hne1 : a ≠ b := by omega
  have hne2 : a + 1 ≠ b := by omega
  have hesc : bankInheritedArmedPrice b *
      bankCellArmed (⟨a + 1, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits b my ly vY :=
    bankCellArmedEscrowLe b _ _
  have hRR := bankCellWorkerUnitsMono b .RR .RR a (a + 1) (a + 1) k wX
    (Nat.le_of_lt (bankInheritedRRForwardPriceLe b a k hab))
  have hRL := bankCellWorkerUnitsMono b .RL .RL (a + 1) a k (a + 1) wY
    (bankCellPriceRetBack b a k .RL (by simp) hpb)
  have hAL := bankCellWorkerUnitsMono b .AL .AL (a + 1) a k (a + 1) wY
    (bankCellPriceRetBack b a k .AL (by simp) hpb)
  have hCL0 := bankCellWorkerUnitsMono b .CL0 .CL0 (a + 1) a k (a + 1) wY
    (bankCellPriceRetBack b a k .CL0 (by simp) hpb)
  have hCL1 := bankCellWorkerUnitsMono b .CL1 .CL1 (a + 1) a k (a + 1) wY
    (bankCellPriceRetBack b a k .CL1 (by simp) hpb)
  have hIR := bankCellWorkerUnitsMono b .IR .IR a (a + 1) (a + 1) k wX
    (bankCellPriceFwdStep b a k .IR .IR (by simp) (by simp) rfl hab)
  have hIA := bankCellWorkerUnitsMono b .IR .AL a (a + 1) (a + 1) k wX
    (bankCellPriceIRToAL b a k hab)
  have hC00 := bankCellWorkerUnitsMono b .CR0 .CR0 a (a + 1) (a + 1) k wX
    (bankCellPriceFwdStep b a k .CR0 .CR0 (by simp) (by simp) rfl hab)
  have hC01 := bankCellWorkerUnitsMono b .CR0 .CR1 a (a + 1) (a + 1) k wX
    (bankCellPriceFwdStep b a k .CR0 .CR1 (by simp) (by simp) rfl hab)
  have hC10 := bankCellWorkerUnitsMono b .CR1 .CR0 a (a + 1) (a + 1) k wX
    (bankCellPriceFwdStep b a k .CR1 .CR0 (by simp) (by simp) rfl hab)
  have hC11 := bankCellWorkerUnitsMono b .CR1 .CR1 a (a + 1) (a + 1) k wX
    (bankCellPriceFwdStep b a k .CR1 .CR1 (by simp) (by simp) rfl hab)
  cases tx <;> cases ty <;>
    simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      hp, ha0, ha, hab, hab', hpb, hne1, hne2] <;>
    (repeat' split) <;>
    omega

theorem bankCellGoalTopStep {n : Nat} (k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n)
    (ha : 1 ≤ a) :
    BankCellGoal (a + 1) k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨a + 1, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hab : a < a + 1 := by omega
  have hp : packNext a (a + 1) (a + 1) = a + 1 := by
    simp [packNext]
  have ha0 : a ≠ 0 := by omega
  have hne1 : a ≠ a + 1 := by omega
  have hesc : bankInheritedArmedPrice (a + 1) *
      bankCellArmed (⟨a + 1, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits (a + 1) my ly vY :=
    bankCellArmedEscrowLe (a + 1) _ _
  have hpb : a + 1 ≤ a + 1 := Nat.le_refl _
  have hRR := bankCellWorkerUnitsMono (a + 1) .RR .RR a (a + 1)
    (a + 1) k wX
    (Nat.le_of_lt (bankInheritedRRForwardPriceLe (a + 1) a k hab))
  have hRL := bankCellWorkerUnitsMono (a + 1) .RL .RL (a + 1) a k
    (a + 1) wY (bankCellPriceRetBack (a + 1) a k .RL (by simp) hpb)
  have hAL := bankCellWorkerUnitsMono (a + 1) .AL .AL (a + 1) a k
    (a + 1) wY (bankCellPriceRetBack (a + 1) a k .AL (by simp) hpb)
  have hCL0 := bankCellWorkerUnitsMono (a + 1) .CL0 .CL0 (a + 1) a k
    (a + 1) wY (bankCellPriceRetBack (a + 1) a k .CL0 (by simp) hpb)
  have hCL1 := bankCellWorkerUnitsMono (a + 1) .CL1 .CL1 (a + 1) a k
    (a + 1) wY (bankCellPriceRetBack (a + 1) a k .CL1 (by simp) hpb)
  have hIR := bankCellWorkerUnitsMono (a + 1) .IR .IR a (a + 1)
    (a + 1) k wX
    (bankCellPriceFwdStep (a + 1) a k .IR .IR (by simp) (by simp)
      rfl hab)
  have hIA := bankCellWorkerUnitsMono (a + 1) .IR .AL a (a + 1)
    (a + 1) k wX (bankCellPriceIRToAL (a + 1) a k hab)
  have hC00 := bankCellWorkerUnitsMono (a + 1) .CR0 .CR0 a (a + 1)
    (a + 1) k wX
    (bankCellPriceFwdStep (a + 1) a k .CR0 .CR0 (by simp) (by simp)
      rfl hab)
  have hC01 := bankCellWorkerUnitsMono (a + 1) .CR0 .CR1 a (a + 1)
    (a + 1) k wX
    (bankCellPriceFwdStep (a + 1) a k .CR0 .CR1 (by simp) (by simp)
      rfl hab)
  have hC10 := bankCellWorkerUnitsMono (a + 1) .CR1 .CR0 a (a + 1)
    (a + 1) k wX
    (bankCellPriceFwdStep (a + 1) a k .CR1 .CR0 (by simp) (by simp)
      rfl hab)
  have hC11 := bankCellWorkerUnitsMono (a + 1) .CR1 .CR1 a (a + 1)
    (a + 1) k wX
    (bankCellPriceFwdStep (a + 1) a k .CR1 .CR1 (by simp) (by simp)
      rfl hab)
  have hRRT := bankCellWorkerUnitsMono (a + 1) .RR .RL (a + 1) a k
    (a + 1) wY (bankCellPriceRRTop a k)
  have hCRT1 := bankCellWorkerUnitsMono (a + 1) .CR1 .CL1 (a + 1) a k
    (a + 1) wY (bankCellPriceCRTop a k).1
  have hCRT0 := bankCellWorkerUnitsMono (a + 1) .CR0 .CL0 (a + 1) a k
    (a + 1) wY (bankCellPriceCRTop a k).2
  cases tx <;> cases ty <;>
    simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      hp, ha0, ha, hne1] <;>
    (repeat' split) <;>
    omega

/-! ### Regions: top or beyond source onto a zero responder -/

theorem bankCellGoalTopZero {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat) (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n) (hb : 2 ≤ b) :
    BankCellGoal b k θ service e dest
      ⟨b, mx, bitx, tx, lx, gx⟩ ⟨0, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hp : packNext b 0 b = 0 := by simp [packNext]
  have hbz : b ≠ 0 := by omega
  have hbz' : 0 ≠ b := by omega
  have hone : 1 ≤ b := by omega
  have hwy := bankCellControllerUnitsLease b my ly (ly - 1) vY
    (Nat.sub_le ly 1)
  have hesc : bankInheritedArmedPrice b *
      bankCellArmed (⟨0, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits b my ly vY :=
    bankCellArmedEscrowLe b _ _
  by_cases htx : tx = .IR
  · subst htx
    cases gy <;> cases my <;> by_cases hl : 1 < ly <;>
      simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        renewalBankWaitSlot, isWaitMode, bankCellArmed,
        hp, hbz, hbz', hone, hl] at hesc ⊢ <;>
      omega
  · cases gy <;> cases my <;> by_cases hl : 1 < ly <;>
      simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        renewalBankWaitSlot, isWaitMode, bankCellArmed,
        hp, hbz, hbz', hone, hl, htx] at hesc ⊢ <;>
      omega

theorem bankCellGoalBeyondZero {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n) (hab : b < a) :
    BankCellGoal b k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨0, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hlt : ¬ a < b := by omega
  have hne : a ≠ b := by omega
  have hp : packNext a 0 b = 0 := by simp [packNext, hlt, hne]
  have ha0 : a ≠ 0 := by omega
  have hnle : ¬ a ≤ b := by omega
  have hwy := bankCellControllerUnitsLease b my ly (ly - 1) vY
    (Nat.sub_le ly 1)
  have hesc : bankInheritedArmedPrice b *
      bankCellArmed (⟨0, my, bity, ty, ly, gy⟩ : BankCell)
        (⟨wY, vY⟩ : RenewalBankSite n) ≤
      bankCellControllerUnits b my ly vY :=
    bankCellArmedEscrowLe b _ _
  cases gy <;> cases my <;> by_cases hl : 1 < ly <;>
    simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      renewalBankWaitSlot, isWaitMode, bankCellArmed,
      hp, ha0, hnle, hne, hl] at hesc ⊢ <;>
    omega

theorem bankCellGoalTopSpacer {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat) (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n) (hb : 2 ≤ b) :
    BankCellGoal b k θ service e dest
      ⟨b, mx, bitx, tx, lx, gx⟩ ⟨b + 1, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hp : packNext b (b + 1) b = b + 1 := by
    simp [packNext]
  have hbz : b ≠ 0 := by omega
  have hout : ¬ b + 1 ≤ b := by omega
  have hone : 1 ≤ b := by omega
  by_cases ht : tx = .IR
  · subst ht
    simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellArmed, hp, hbz, hout, hone]
  · simp [BankCellGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellArmed, hp, hbz, hout, hone, ht]
    omega

/-! ### The core cell inequality over all PACK geometries -/

/-- Core cell inequality: for every OLD BANK cell pair whose source
controller and responder worker have the in-flight shape,
after + A * armedY <= before + (A - 1) * armedX. -/
theorem bankCellCore {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (sx sy : RenewalBankSite n) (hb : 2 ≤ b)
    (hcx : bankInFlightControllerShape x0.role x0.mode sx.controller)
    (hwy : bankInFlightWorkerShape y0.tok sy.worker) :
    BankCellGoal b k θ service e dest x0 y0 sx sy := by
  rcases x0 with ⟨a, mx, bitx, tx, lx, gx⟩
  rcases y0 with ⟨c0, my, bity, ty, ly, gy⟩
  rcases sx with ⟨wX, vX⟩
  rcases sy with ⟨wY, vY⟩
  dsimp only at hcx hwy
  have hpos : 0 < b := by omega
  by_cases hsame : packNext a c0 b = c0
  · by_cases ha0 : a = 0
    · subst ha0
      have hp : packNext 0 c0 b = 1 := by simp [packNext, hpos]
      have hc : c0 = 1 := by omega
      subst hc
      cases gx with
      | true =>
          exact bankCellGoalRootGrant b k θ service e dest mx bitx tx lx
            my bity ty ly gy wX wY vX vY hb
      | false =>
          cases mx with
          | ARMED =>
              have hv : ∃ p, vX = .active p := by
                simpa [bankInFlightControllerShape] using hcx
              obtain ⟨p, rfl⟩ := hv
              exact bankCellGoalRootArmed b k θ service e dest bitx tx lx
                my bity ty ly gy wX wY p vY hb
          | CSTART =>
              have hv : ∃ p, vX = .active p := by
                simpa [bankInFlightControllerShape] using hcx
              obtain ⟨p, rfl⟩ := hv
              exact bankCellGoalRootCStart b k θ service e dest bitx tx lx
                my bity ty ly gy wX wY p vY hb
          | RESET =>
              exact bankCellGoalRootWait b k θ service e dest .RESET bitx
                tx lx my bity ty ly gy wX wY vX vY hb (by simp) hwy
          | RWAIT =>
              exact bankCellGoalRootWait b k θ service e dest .RWAIT bitx
                tx lx my bity ty ly gy wX wY vX vY hb (by simp) hwy
          | IWAIT =>
              exact bankCellGoalRootWait b k θ service e dest .IWAIT bitx
                tx lx my bity ty ly gy wX wY vX vY hb (by simp) hwy
          | CWAIT =>
              exact bankCellGoalRootWait b k θ service e dest .CWAIT bitx
                tx lx my bity ty ly gy wX wY vX vY hb (by simp) hwy
    · by_cases hab : a < b
      · have hp : packNext a c0 b = a + 1 := by simp [packNext, hab]
        have hc : c0 = a + 1 := by omega
        subst hc
        by_cases htop : a + 1 < b
        · exact bankCellGoalInteriorStep b k θ service e dest a mx bitx
            tx lx gx my bity ty ly gy wX wY vX vY (by omega) htop
        · have hbe : b = a + 1 := by omega
          subst hbe
          exact bankCellGoalTopStep k θ service e dest a mx bitx
            tx lx gx my bity ty ly gy wX wY vX vY (by omega)
      · by_cases hab' : a = b
        · subst b
          by_cases hc0 : c0 = 0
          · subst hc0
            exact bankCellGoalTopZero a k θ service e dest mx bitx tx lx gx
              my bity ty ly gy wX wY vX vY hb
          · have hp : packNext a c0 a = a + 1 := by simp [packNext, hc0]
            have hc : c0 = a + 1 := by omega
            subst hc
            exact bankCellGoalTopSpacer a k θ service e dest mx bitx tx lx
              gx my bity ty ly gy wX wY vX vY hb
        · have hlt : ¬ a < b := hab
          have hp : packNext a c0 b = 0 := by simp [packNext, hlt, hab']
          have hc : c0 = 0 := by omega
          subst hc
          exact bankCellGoalBeyondZero b k θ service e dest a mx bitx tx lx
            gx my bity ty ly gy wX wY vX vY (by omega)
  · by_cases ha0 : a = 0
    · subst ha0
      have hp : packNext 0 c0 b = 1 := by simp [packNext, hpos]
      exact bankCellGoalRootChanged b k θ service e dest mx bitx tx lx gx
        c0 my bity ty ly gy wX wY vX vY hb (by omega)
    · by_cases hab : a < b
      · have hp : packNext a c0 b = a + 1 := by simp [packNext, hab]
        exact bankCellGoalInteriorChanged b k θ service e dest a mx bitx
          tx lx gx c0 my bity ty ly gy wX wY vX vY (by omega) hab
          (by omega)
      · by_cases hab' : a = b
        · subst b
          have hc0 : c0 ≠ 0 := by
            intro h
            subst h
            exact hsame (by simp [packNext])
          have hp : packNext a c0 a = a + 1 := by simp [packNext, hc0]
          exact bankCellGoalTopChanged a k θ service e dest mx bitx tx lx
            gx c0 my bity ty ly gy wX wY vX vY hb hc0 (by omega)
        · have hlt : ¬ a < b := hab
          have hp : packNext a c0 b = 0 := by simp [packNext, hlt, hab']
          exact bankCellGoalBeyondChanged b k θ service e dest a mx bitx
            tx lx gx c0 my bity ty ly gy wX wY vX vY (by omega)
            (by omega)

/-! ### From the masked physical pair to the OLD bankPair cells -/

theorem bankCellBaseLease (c : Compiled) (hs : c.useSmall = false)
    (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.lease =
      (copyBank x (bankPair (bankCell x x.pack.val)
        (bankCell y y.pack.val) (packNext x.pack.val y.pack.val c.b)
        c.b c.theta).1).lease ∧
    (baseStep c ev x y).2.lease =
      (copyBank y (bankPair (bankCell x x.pack.val)
        (bankCell y y.pack.val) (packNext x.pack.val y.pack.val c.b)
        c.b c.theta).2).lease := by
  refine ⟨?_, ?_⟩ <;>
    simp [baseStep, hs, Agent.setNative, Agent.setCPriv, copyBank] <;>
    repeat (first | rfl | split)

theorem bankCellBasePack (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.pack = x.pack ∧
      (baseStep c ev x y).2.pack =
        packFin c (packNext x.pack.val y.pack.val c.b) := by
  constructor <;> by_cases hs : c.useSmall <;>
    simp [baseStep, hs, Agent.setNative, Agent.setCPriv, copyBank] <;>
    repeat (first | rfl | split)

theorem bankCellMaskedBase (c : Compiled) (s : Bool) (x y : Agent c) :
    (renewalMaskedPair c s x y).1.tok =
      (baseStep c (certificateStep c x y).2.2 x y).1.tok ∧
    (renewalMaskedPair c s x y).1.mode =
      (baseStep c (certificateStep c x y).2.2 x y).1.mode ∧
    (renewalMaskedPair c s x y).1.lease =
      (baseStep c (certificateStep c x y).2.2 x y).1.lease ∧
    (renewalMaskedPair c s x y).1.pack =
      (baseStep c (certificateStep c x y).2.2 x y).1.pack ∧
    (renewalMaskedPair c s x y).2.tok =
      (baseStep c (certificateStep c x y).2.2 x y).2.tok ∧
    (renewalMaskedPair c s x y).2.mode =
      (baseStep c (certificateStep c x y).2.2 x y).2.mode ∧
    (renewalMaskedPair c s x y).2.lease =
      (baseStep c (certificateStep c x y).2.2 x y).2.lease ∧
    (renewalMaskedPair c s x y).2.pack =
      (baseStep c (certificateStep c x y).2.2 x y).2.pack := by
  cases s <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bankCellCopyBankLease (c : Compiled) (dst : Agent c)
    (src : BankCell) :
    (copyBank dst src).lease.val ≤ src.lease := by
  unfold copyBank
  dsimp only
  split <;> simp

theorem bankCellMaskedResponderPackVal (c : Compiled) (cut : Bool)
    (x y : Agent c) :
    (renewalMaskedPair c cut x y).2.pack.val =
      packNext x.pack.val y.pack.val c.b := by
  obtain ⟨-, -, -, -, -, -, -, h8⟩ := bankCellMaskedBase c cut x y
  have hp := (bankCellBasePack c (certificateStep c x y).2.2 x y).2
  have hle := bankCellPackNextLe x.pack.val y.pack.val c.b
  rw [h8, hp]
  unfold packFin
  rw [dif_pos (by omega)]

theorem bankCellMaskedSourceUnits {n : Nat} (c : Compiled)
    (hs : c.useSmall = false) (cut : Bool) (x y : Agent c)
    (nb : Nat) (s : RenewalBankSite n) :
    bankCellSiteUnits c.b
        (bankCell (renewalMaskedPair c cut x y).1
          (renewalMaskedPair c cut x y).1.pack.val)
        (renewalMaskedPair c cut x y).1.pack.val nb s ≤
      bankCellSiteUnits c.b (Counter.resetBankOld x y).1
        x.pack.val nb s := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := bankCellMaskedBase c cut x y
  have htrip := Counter.resetBaseBankTrip
    (certificateStep c x y).2.2 x y hs
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at htrip
  obtain ⟨⟨hm, -, ht⟩, -⟩ := htrip
  have hl := (bankCellBaseLease c hs (certificateStep c x y).2.2 x y).1
  have hp := (bankCellBasePack c (certificateStep c x y).2.2 x y).1
  have hpack : (renewalMaskedPair c cut x y).1.pack.val = x.pack.val := by
    rw [h4, hp]
  rw [hpack]
  apply bankCellSiteUnitsLease
  · show (renewalMaskedPair c cut x y).1.tok =
      (Counter.resetBankOld x y).1.tok
    rw [h1, ht]
  · show (renewalMaskedPair c cut x y).1.mode =
      (Counter.resetBankOld x y).1.mode
    rw [h2, hm]
  · show (renewalMaskedPair c cut x y).1.lease.val ≤
      (Counter.resetBankOld x y).1.lease
    rw [h3, hl]
    exact bankCellCopyBankLease c x _

theorem bankCellMaskedResponderUnits {n : Nat} (c : Compiled)
    (hs : c.useSmall = false) (cut : Bool) (x y : Agent c)
    (k : Nat) (s : RenewalBankSite n) :
    bankCellSiteUnits c.b
        (bankCell (renewalMaskedPair c cut x y).2
          (renewalMaskedPair c cut x y).2.pack.val)
        (renewalMaskedPair c cut x y).2.pack.val k s ≤
      bankCellSiteUnits c.b (Counter.resetBankOld x y).2
        (renewalMaskedPair c cut x y).2.pack.val k s := by
  obtain ⟨-, -, -, -, h5, h6, h7, -⟩ := bankCellMaskedBase c cut x y
  have htrip := Counter.resetBaseBankTrip
    (certificateStep c x y).2.2 x y hs
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at htrip
  obtain ⟨-, ⟨hm, -, ht⟩⟩ := htrip
  have hl := (bankCellBaseLease c hs (certificateStep c x y).2.2 x y).2
  apply bankCellSiteUnitsLease
  · show (renewalMaskedPair c cut x y).2.tok =
      (Counter.resetBankOld x y).2.tok
    rw [h5, ht]
  · show (renewalMaskedPair c cut x y).2.mode =
      (Counter.resetBankOld x y).2.mode
    rw [h6, hm]
  · show (renewalMaskedPair c cut x y).2.lease.val ≤
      (Counter.resetBankOld x y).2.lease
    rw [h7, hl]
    exact bankCellCopyBankLease c y _

/-! ### The agent-level core and (A) -/

/-- Agent-level core: on any BANK Compiled, for shaped OLD ghosts,
the masked physical pair and the literal ghost observer satisfy
after + n*A*armedY <= before + escrowX. -/
theorem bankInheritedCellCore {n : Nat} (c : Compiled)
    (hs : c.useSmall = false)
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c)
    (k : Nat) (cut : Bool)
    (hcx : bankInFlightControllerShape
      x.pack.val x.mode (m.sites e).controller)
    (hwy : bankInFlightWorkerShape y.tok (m.sites dest).worker) :
    bankInheritedCellPairAfter c m e dest x y k cut +
        n * bankInheritedArmedPrice c.b *
          bankInheritedCellArmedAtoms y (m.sites dest) ≤
      bankInheritedCellPairBefore c m e dest x y k +
        bankInheritedCellEscrow c x (m.sites e) := by
  have hb : 2 ≤ c.b := by
    unfold Compiled.b
    omega
  have hcore :
      bankCellSiteUnits c.b (Counter.resetBankOld x y).1 x.pack.val
          (packNext x.pack.val y.pack.val c.b)
          (renewalBankPairMemory c m e dest x y).1 +
        bankCellSiteUnits c.b (Counter.resetBankOld x y).2
          (packNext x.pack.val y.pack.val c.b) k
          (renewalBankPairMemory c m e dest x y).2 +
        bankInheritedArmedPrice c.b *
          bankCellArmed (bankCell y y.pack.val) (m.sites dest) ≤
      bankCellSiteUnits c.b (bankCell x x.pack.val) x.pack.val
          y.pack.val (m.sites e) +
        bankCellSiteUnits c.b (bankCell y y.pack.val) y.pack.val k
          (m.sites dest) +
        (bankInheritedArmedPrice c.b - 1) *
          bankCellArmed (bankCell x x.pack.val) (m.sites e) :=
    bankCellCore c.b k c.theta m.service e dest
      (bankCell x x.pack.val) (bankCell y y.pack.val)
      (m.sites e) (m.sites dest) hb hcx hwy
  rw [← bankCellMaskedResponderPackVal c cut x y] at hcore
  have hs1 := bankCellMaskedSourceUnits c hs cut x y
    (renewalMaskedPair c cut x y).2.pack.val
    (renewalBankPairMemory c m e dest x y).1
  have hs2 := bankCellMaskedResponderUnits c hs cut x y k
    (renewalBankPairMemory c m e dest x y).2
  unfold bankInheritedCellPairAfter bankInheritedCellPairBefore
  rw [bankCellSiteWeightUnits c (renewalMaskedPair c cut x y).1,
    bankCellSiteWeightUnits c (renewalMaskedPair c cut x y).2,
    bankCellSiteWeightUnits c x, bankCellSiteWeightUnits c y,
    bankCellEscrowUnits, bankCellArmedAgent]
  have hm := Nat.mul_le_mul_left n hcore
  have m1 := Nat.mul_le_mul_left n hs1
  have m2 := Nat.mul_le_mul_left n hs2
  simp only [Nat.mul_add] at hm
  have e1 := Nat.mul_assoc n (bankInheritedArmedPrice c.b)
    (bankCellArmed (bankCell y y.pack.val) (m.sites dest))
  have e2 := Nat.mul_assoc n (bankInheritedArmedPrice c.b - 1)
    (bankCellArmed (bankCell x x.pack.val) (m.sites e))
  omega

/-- (A), the shaped general-b cell rows, for every b. -/
theorem bankInheritedNonarmedCellRowsHolds (b : Nat) :
    BankInheritedNonarmedCellRows b := by
  intro n c _hcb hs m e dest _hne x y k cut hcx _hwx _hcy hwy harm
  have h := bankInheritedCellCore c hs m e dest x y k cut hcx hwy
  have hex : bankInheritedCellEscrow c x (m.sites e) = 0 := by
    unfold bankInheritedCellEscrow
    rw [harm, Nat.mul_zero]
  have hey : bankInheritedCellEscrow c y (m.sites dest) ≤
      n * bankInheritedArmedPrice c.b *
        bankInheritedCellArmedAtoms y (m.sites dest) := by
    unfold bankInheritedCellEscrow
    exact Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left n (Nat.sub_le _ _))
  omega

theorem bankInheritedNonarmedLocalRowsHolds
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankInheritedNonarmedLocalRows ring hbank :=
  bankInheritedNonarmedLocalRowsOfCellRows ring hn hbank
    (bankInheritedNonarmedCellRowsHolds _)

/-- (A) at the edge level, unconditionally. -/
theorem bankInheritedNonarmedEdgeRowsHolds
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankInheritedNonarmedEdgeRows ring hbank :=
  bankInheritedNonarmedEdgeRowsOfCellRows ring hn hbank
    (bankInheritedNonarmedCellRowsHolds _)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankCellCore
#print axioms L3.RenewalReferenceClock.bankInheritedCellCore
#print axioms L3.RenewalReferenceClock.bankInheritedNonarmedCellRowsHolds
#print axioms L3.RenewalReferenceClock.bankInheritedNonarmedLocalRowsHolds
#print axioms L3.RenewalReferenceClock.bankInheritedNonarmedEdgeRowsHolds
#print axioms L3.RenewalReferenceClock.bankCellGoalRootChanged
#print axioms L3.RenewalReferenceClock.bankCellGoalInteriorChanged
#print axioms L3.RenewalReferenceClock.bankCellGoalTopChanged
#print axioms L3.RenewalReferenceClock.bankCellGoalBeyondChanged
#print axioms L3.RenewalReferenceClock.bankCellGoalRootGrant
#print axioms L3.RenewalReferenceClock.bankCellGoalRootWait
#print axioms L3.RenewalReferenceClock.bankCellGoalRootArmed
#print axioms L3.RenewalReferenceClock.bankCellGoalRootCStart
#print axioms L3.RenewalReferenceClock.bankCellGoalInteriorStep
#print axioms L3.RenewalReferenceClock.bankCellGoalTopStep
#print axioms L3.RenewalReferenceClock.bankCellGoalTopZero
#print axioms L3.RenewalReferenceClock.bankCellGoalBeyondZero
#print axioms L3.RenewalReferenceClock.bankCellGoalTopSpacer

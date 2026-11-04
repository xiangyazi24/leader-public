import Leader.L3.Bank.InheritedArmedRows
import Leader.L3.Bank.CounterCold
import Leader.L3.Bank.CellMemoryNonroot
import Leader.L3.Bank.CellMemoryRoot

/-!
R7 (C): `BankInheritedProgressAlternative` on reachable BANK states.

The statement is true on reachable states.  Its only non-paying local
configuration is the zero-atom return-token CSTART stall: a
CSTART root holding inherited atoms whose first digit carries a return
token with no inherited atom.  That configuration is excluded at every
reachable state by the order invariant `BankInheritedOrder` (Part C):
a zero-atom worker (pending receipt or atom-free payload) on digit j of
the window anchored at x forces x's controller to hold no inherited
atom, and every worker on a lower digit of the same window to hold no
inherited atom.  It holds because a zero-atom worker is launched only
from a root whose controller is left atom-free, workers of one window
only move one digit or are deleted, and a controller regains atoms only
by merging the worker on its first digit.

Part A: strict two-cell inequalities (after + 1 <= before, in units of
n) for the six paying holders.  Part B: the lift to the potential.
Part C: the order invariant along every BANK word.  Part D: the
progress alternative.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ## Part A: strict cell inequalities -/

/-- The strict two-cell goal, without ARMED escrow terms.
Consumer: the six holder lemmas and `bankInheritedStrictEdgeOfCell`. -/
def BankCellStrictGoal {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (sx sy : RenewalBankSite n) : Prop :=
  bankCellSiteUnits b
      (bankPair x0 y0 (packNext x0.role y0.role b) b θ).1
      x0.role (packNext x0.role y0.role b)
      (bankCellMemory b sx sy service e dest x0 y0).1 +
    bankCellSiteUnits b
      (bankPair x0 y0 (packNext x0.role y0.role b) b θ).2
      (packNext x0.role y0.role b) k
      (bankCellMemory b sx sy service e dest x0 y0).2 + 1 ≤
  bankCellSiteUnits b x0 x0.role y0.role sx +
    bankCellSiteUnits b y0 y0.role k sy

/-- The strict goal of a nonroot source whose responder keeps a nonzero PACK: both controllers
end empty, so only the worker units after the step remain on the left. -/
private theorem bankCellStrictGoal_nonroot {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (sx sy : RenewalBankSite n) (hx : x0.role ≠ 0)
    (hpy : packNext x0.role y0.role b ≠ 0) :
    BankCellStrictGoal b k θ service e dest x0 y0 sx sy ↔
      bankCellWorkerUnits b (bankPairNR x0 y0 (packNext x0.role y0.role b) b θ).1.tok
          x0.role (packNext x0.role y0.role b)
          (bankMemoryNRW b sx.worker sy.worker x0 y0).1 +
        bankCellWorkerUnits b (bankPairNR x0 y0 (packNext x0.role y0.role b) b θ).2.tok
          (packNext x0.role y0.role b) k
          (bankMemoryNRW b sx.worker sy.worker x0 y0).2 + 1 ≤
      bankCellSiteUnits b x0 x0.role y0.role sx +
        bankCellSiteUnits b y0 y0.role k sy := by
  unfold BankCellStrictGoal
  rw [bankPair_nonroot _ _ _ _ _ hx, bankCellMemory_nonroot _ _ _ _ _ _ _ _ hx]
  simp only [bankCellSiteUnits, bankMemoryCtlY, hpy, and_false, if_false,
    bankCellControllerUnits, Nat.add_zero]

/-- A payload with its atoms removed; every other worker unchanged.
Consumer: `bankCellStrictChanged`. -/
def bankCellAtomFree {n : Nat} : RenewalBankWorker n → RenewalBankWorker n
  | .payload p => .payload { p with atoms := [] }
  | w => w

/-- Removing atoms keeps the in-flight worker shape.
Consumer: `bankCellStrictChanged`. -/
theorem bankCellAtomFreeShape {n : Nat} (t : BTok)
    (w : RenewalBankWorker n) (h : bankInFlightWorkerShape t w) :
    bankInFlightWorkerShape t (bankCellAtomFree w) := by
  cases w with
  | empty => exact h
  | pending r => exact h
  | payload p =>
      cases t <;> simp [bankInFlightWorkerShape, bankCellAtomFree] at h ⊢

/-- An atom-free worker has no units.
Consumer: `bankCellStrictChanged`. -/
theorem bankCellAtomFreeUnits {n : Nat} (b : Nat) (t : BTok)
    (r nb : Nat) (w : RenewalBankWorker n) :
    bankCellWorkerUnits b t r nb (bankCellAtomFree w) = 0 := by
  cases w with
  | empty => rfl
  | pending _ => rfl
  | payload p => simp [bankCellAtomFree, bankCellWorkerUnits]

/-- A changed responder role discards the responder's OLD ghost site.
Consumer: `bankCellStrictChanged`. -/
theorem bankCellMemoryChangedIrrelevant {n : Nat} (b : Nat)
    (sx sy sy' : RenewalBankSite n) (service : Nat) (e dest : Fin n)
    (bx cy : BankCell) (h : packNext bx.role cy.role b ≠ cy.role) :
    bankCellMemory b sx sy service e dest bx cy =
      bankCellMemory b sx sy' service e dest bx cy := by
  simp [bankCellMemory, h]

/-- A source outside its digit roles discards its OLD worker.
Consumer: `bankCellStrictOutside`. -/
theorem bankCellMemoryOutsideIrrelevant {n : Nat} (b : Nat)
    (w w' : RenewalBankWorker n) (v : RenewalBankController n)
    (sy : RenewalBankSite n) (service : Nat) (e dest : Fin n)
    (bx cy : BankCell) (h : ¬ (1 ≤ bx.role ∧ bx.role ≤ b)) :
    bankCellMemory b ⟨w, v⟩ sy service e dest bx cy =
      bankCellMemory b ⟨w', v⟩ sy service e dest bx cy := by
  have h' : (decide (1 ≤ bx.role) && decide (bx.role ≤ b)) = false := by
    by_cases h1 : 1 ≤ bx.role
    · have h2 : ¬ bx.role ≤ b := fun h2 => h ⟨h1, h2⟩
      simp [h1, h2]
    · simp [h1]
  unfold bankCellMemory
  rw [h']
  rfl

/-- Strict cell bound when the responder role changes and the
responder site carries a positive weight.  Consumer: the holder
lemmas P1, P4, P6. -/
theorem bankCellStrictChanged {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (sx sy : RenewalBankSite n) (hb : 2 ≤ b)
    (hcx : bankInFlightControllerShape x0.role x0.mode sx.controller)
    (hwy : bankInFlightWorkerShape y0.tok sy.worker)
    (harmX : bankCellArmed x0 sx = 0)
    (hch : packNext x0.role y0.role b ≠ y0.role)
    (hpos : 1 ≤ bankCellSiteUnits b y0 y0.role k sy) :
    BankCellStrictGoal b k θ service e dest x0 y0 sx sy := by
  let sy' : RenewalBankSite n :=
    ⟨bankCellAtomFree sy.worker, .empty⟩
  have hcore := bankCellCore b k θ service e dest x0 y0 sx sy' hb hcx
    (bankCellAtomFreeShape y0.tok sy.worker hwy)
  have hmem := bankCellMemoryChangedIrrelevant b sx sy sy' service e
    dest x0 y0 hch
  have hzero : bankCellSiteUnits b y0 y0.role k sy' = 0 := by
    simp [sy', bankCellSiteUnits, bankCellAtomFreeUnits]
  have harmY : bankCellArmed y0 sy' = 0 := by
    simp [sy', bankCellArmed, bankInheritedControllerAtomCount]
  unfold BankCellGoal at hcore
  unfold BankCellStrictGoal
  rw [hmem]
  rw [harmY, harmX, hzero] at hcore
  omega

/-- Strict cell bound when the source is outside its digit roles and
its worker carries a positive weight.  Consumer: holder P3. -/
theorem bankCellStrictOutside {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (w : RenewalBankWorker n) (v : RenewalBankController n)
    (sy : RenewalBankSite n) (hb : 2 ≤ b)
    (hcx : bankInFlightControllerShape x0.role x0.mode v)
    (hwy : bankInFlightWorkerShape y0.tok sy.worker)
    (harmX : bankCellArmed x0 (⟨w, v⟩ : RenewalBankSite n) = 0)
    (hout : ¬ (1 ≤ x0.role ∧ x0.role ≤ b))
    (hpos : 1 ≤ bankCellWorkerUnits b x0.tok x0.role y0.role w) :
    BankCellStrictGoal b k θ service e dest x0 y0 ⟨w, v⟩ sy := by
  have hcore := bankCellCore b k θ service e dest x0 y0 ⟨.empty, v⟩ sy
    hb hcx hwy
  have hmem := bankCellMemoryOutsideIrrelevant b w .empty v sy service
    e dest x0 y0 hout
  have harmX' : bankCellArmed x0 (⟨.empty, v⟩ : RenewalBankSite n) = 0 := by
    simpa [bankCellArmed] using harmX
  unfold BankCellGoal at hcore
  unfold BankCellStrictGoal
  rw [hmem]
  rw [harmX'] at hcore
  simp only [bankCellSiteUnits, bankCellWorkerUnitsEmpty] at hcore ⊢
  omega

/-- A ticked waiting slot loses one unit per atom.
Consumer: `bankCellStrictTopZeroY`, `bankCellStrictBeyondZeroY`. -/
theorem bankCellWaitingTickStrict {n : Nat} (b : Nat) (m : Mode)
    (ly : Nat) (v : RenewalBankController n)
    (l : List (RenewalBankAtom n)) (hv : v = .waiting l)
    (hl : 1 ≤ l.length) (hly : 1 < ly) :
    bankCellControllerUnits b m (ly - 1) v + 1 ≤
      bankCellControllerUnits b m ly v := by
  subst hv
  rw [bankCellControllerUnitsWaiting, bankCellControllerUnitsWaiting]
  have hsplit : (bankInheritedComparisonPrice b + ly + 1) * l.length =
      (bankInheritedComparisonPrice b + (ly - 1) + 1) * l.length +
        l.length := by
    have hc : bankInheritedComparisonPrice b + ly + 1 =
        (bankInheritedComparisonPrice b + (ly - 1) + 1) + 1 := by omega
    rw [hc, Nat.add_mul, Nat.one_mul]
  omega

/-- A nonempty waiting slot has a positive unit count.
Consumer: `bankCellStrictTopZeroY`, `bankCellStrictWaitingY`. -/
theorem bankCellWaitingPos {n : Nat} (b : Nat) (m : Mode)
    (ly : Nat) (v : RenewalBankController n)
    (l : List (RenewalBankAtom n)) (hv : v = .waiting l)
    (hl : 1 ≤ l.length) :
    1 ≤ bankCellControllerUnits b m ly v := by
  subst hv
  rw [bankCellControllerUnitsWaiting]
  have h : 1 ≤ bankInheritedComparisonPrice b + ly + 1 := by omega
  calc 1 = 1 * 1 := rfl
    _ ≤ (bankInheritedComparisonPrice b + ly + 1) * l.length :=
      Nat.mul_le_mul h hl

/-- P1 from a top source: an inherited waiting slot on a root
responder is ticked or cleared.  Consumer: `bankCellStrictWaitingY`. -/
theorem bankCellStrictTopZeroY {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat) (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n) (l : List (RenewalBankAtom n))
    (hb : 2 ≤ b) (hvY : vY = .waiting l) (hl : 1 ≤ l.length)
    (hmy : isWaitMode my = true) :
    BankCellStrictGoal b k θ service e dest
      ⟨b, mx, bitx, tx, lx, gx⟩ ⟨0, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hp : packNext b 0 b = 0 := by simp [packNext]
  have hbz : b ≠ 0 := by omega
  have hbz' : 0 ≠ b := by omega
  have hone : 1 ≤ b := by omega
  have hpos := bankCellWaitingPos b my ly vY l hvY hl
  have htick := bankCellWaitingTickStrict b my ly vY l hvY hl
  by_cases htx : tx = .IR
  · subst htx
    cases gy <;> cases my <;> by_cases hly : 1 < ly <;>
      simp [isWaitMode] at hmy <;>
      simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        renewalBankWaitSlot, isWaitMode,
        hp, hbz, hbz', hone, hly] at htick hpos ⊢ <;>
      omega
  · cases gy <;> cases my <;> by_cases hly : 1 < ly <;>
      simp [isWaitMode] at hmy <;>
      simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        renewalBankWaitSlot, isWaitMode,
        hp, hbz, hbz', hone, hly, htx] at htick hpos ⊢ <;>
      omega

/-- P1 from a beyond-top source.  Consumer: `bankCellStrictWaitingY`. -/
theorem bankCellStrictBeyondZeroY {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n) (l : List (RenewalBankAtom n))
    (hab : b < a) (hvY : vY = .waiting l) (hl : 1 ≤ l.length)
    (hmy : isWaitMode my = true) :
    BankCellStrictGoal b k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨0, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨wY, vY⟩ := by
  have hlt : ¬ a < b := by omega
  have hne : a ≠ b := by omega
  have hp : packNext a 0 b = 0 := by simp [packNext, hlt, hne]
  have ha0 : a ≠ 0 := by omega
  have hnle : ¬ a ≤ b := by omega
  have hpos := bankCellWaitingPos b my ly vY l hvY hl
  have htick := bankCellWaitingTickStrict b my ly vY l hvY hl
  cases gy <;> cases my <;> by_cases hly : 1 < ly <;>
    simp [isWaitMode] at hmy <;>
    simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      renewalBankWaitSlot, isWaitMode,
      hp, ha0, hnle, hne, hly] at htick hpos ⊢ <;>
    omega

/-- P1: an inherited waiting slot on a root responder pays on every
incoming edge.  Consumer: `bankInheritedProgressOfWaiting`. -/
theorem bankCellStrictWaitingY {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (sx sy : RenewalBankSite n) (l : List (RenewalBankAtom n))
    (hb : 2 ≤ b)
    (hcx : bankInFlightControllerShape x0.role x0.mode sx.controller)
    (hwy : bankInFlightWorkerShape y0.tok sy.worker)
    (harmX : bankCellArmed x0 sx = 0)
    (hy0 : y0.role = 0) (hvY : sy.controller = .waiting l)
    (hl : 1 ≤ l.length) (hmy : isWaitMode y0.mode = true) :
    BankCellStrictGoal b k θ service e dest x0 y0 sx sy := by
  by_cases hch : packNext x0.role y0.role b = y0.role
  · rw [hy0] at hch
    rcases x0 with ⟨a, mx, bitx, tx, lx, gx⟩
    rcases y0 with ⟨c0, my, bity, ty, ly, gy⟩
    rcases sx with ⟨wX, vX⟩
    rcases sy with ⟨wY, vY⟩
    dsimp only at hy0 hch hvY hmy
    subst hy0
    by_cases hab : a < b
    · simp [packNext, hab] at hch
    · by_cases hae : a = b
      · subst hae
        exact bankCellStrictTopZeroY a k θ service e dest mx bitx tx lx gx
          my bity ty ly gy wX wY vX vY l hb hvY hl hmy
      · exact bankCellStrictBeyondZeroY b k θ service e dest a mx bitx tx
          lx gx my bity ty ly gy wX wY vX vY l (by omega) hvY hl hmy
  · apply bankCellStrictChanged b k θ service e dest x0 y0 sx sy hb hcx
      hwy harmX hch
    unfold bankCellSiteUnits
    have := bankCellWaitingPos b y0.mode y0.lease sy.controller l hvY hl
    omega

/-- Positive units of a nonempty atom list at a positive price.
Consumer: the strict holder lemmas. -/
theorem bankCellUnitsPos (price len : Nat) (hp : 1 ≤ price)
    (hl : 1 ≤ len) : 1 ≤ price * len := by
  calc 1 = 1 * 1 := rfl
    _ ≤ price * len := Nat.mul_le_mul hp hl

/-- A strictly cheaper price on a nonempty list loses a unit.
Consumer: the strict holder lemmas. -/
theorem bankCellUnitsStrict (p p' len : Nat) (hp : p' + 1 ≤ p)
    (hl : 1 ≤ len) : p' * len + 1 ≤ p * len := by
  have h1 : (p' + 1) * len ≤ p * len := Nat.mul_le_mul_right len hp
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-- The comparison price is positive.
Consumer: `bankCellWorkerPricePos`. -/
theorem bankCellComparisonPos (b : Nat) :
    1 ≤ bankInheritedComparisonPrice b := by
  rw [bankCellComparisonPriceEq]
  omega

/-- The ARMED price is positive.
Consumer: `bankCellWorkerPricePos`. -/
theorem bankCellArmedPos (b : Nat) :
    1 ≤ bankInheritedArmedPrice b := by
  rw [bankCellArmedPriceEq]
  omega

/-- The comparison issue is strictly cheaper than the CSTART stock.
Consumer: `bankCellStrictRootCStartX`. -/
theorem bankCellPriceRootIssueStrict (b k : Nat) :
    bankInheritedWorkerPrice b .CR0 1 k + 1 ≤
      bankInheritedComparisonPrice b ∧
    bankInheritedWorkerPrice b .CR1 1 k + 1 ≤
      bankInheritedComparisonPrice b := by
  rw [bankCellPriceFwd b 1 k .CR0 (by simp),
    bankCellPriceFwd b 1 k .CR1 (by simp)]
  have hv := bankCellBaseValues b
  rw [hv.2.2.2.2.2.1, hv.2.2.2.2.2.2, bankCellComparisonPriceEq,
    bankCellArmedPriceEq]
  omega

/-- Every non-E token carries a positive worker price.
Consumer: the strict holder lemmas. -/
theorem bankCellWorkerPricePos (b : Nat) (t : BTok) (r nb : Nat)
    (ht : t ≠ .E) : 1 ≤ bankInheritedWorkerPrice b t r nb := by
  cases t <;>
    simp [bankInheritedWorkerPrice, bankInheritedWorkerBasePrice,
      bankInheritedWorkerPhasePrice] at ht ⊢ <;>
    omega

/-- P2, grant or changed: the CSTART stock is cleared.
Consumer: `bankCellStrictCStartX`. -/
theorem bankCellStrictRootClearX {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (bitx : Bool) (tx : BTok) (lx : Nat) (gx : Bool) (c0 : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (p : RenewalBankPayload n)
    (vY : RenewalBankController n) (hb : 2 ≤ b)
    (hp1 : 1 ≤ p.atoms.length)
    (hclear : gx = true ∨ c0 ≠ 1) :
    BankCellStrictGoal b k θ service e dest
      ⟨0, .CSTART, bitx, tx, lx, gx⟩ ⟨c0, my, bity, ty, ly, gy⟩
      ⟨wX, .active p⟩ ⟨wY, vY⟩ := by
  have hpos : 0 < b := by omega
  have hp : packNext 0 c0 b = 1 := by simp [packNext, hpos]
  have hone : 1 ≤ b := by omega
  have hcomp := bankCellUnitsPos (bankInheritedComparisonPrice b)
    p.atoms.length (bankCellComparisonPos b) hp1
  rcases hclear with hg | hc
  · subst hg
    by_cases hc1 : c0 = 1
    · subst hc1
      simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        bankCellControllerUnitsActive, hp, hone]
      omega
    · have hc' : 1 ≠ c0 := fun h => hc1 h.symm
      simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        bankCellControllerUnitsActive, hp, hone, hc']
      omega
  · have hc' : 1 ≠ c0 := fun h => hc h.symm
    cases gx <;>
      simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        bankCellControllerUnitsActive, hp, hone, hc'] <;>
      omega

/-- P2 on the first digit: the CSTART stock issues a comparator or
is cleared, unless the digit holds a return token, which then carries
an inherited atom and is consumed.  Consumer: `bankCellStrictCStartX`. -/
theorem bankCellStrictRootCStartX {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (bitx : Bool) (tx : BTok) (lx : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX wY : RenewalBankWorker n)
    (p : RenewalBankPayload n)
    (vY : RenewalBankController n) (hb : 2 ≤ b)
    (hp1 : 1 ≤ p.atoms.length)
    (hstall : isRetTok ty = true →
      ∃ q : RenewalBankPayload n, wY = .payload q ∧ 1 ≤ q.atoms.length) :
    BankCellStrictGoal b k θ service e dest
      ⟨0, .CSTART, bitx, tx, lx, false⟩ ⟨1, my, bity, ty, ly, gy⟩
      ⟨wX, .active p⟩ ⟨wY, vY⟩ := by
  have hpos : 0 < b := by omega
  have hp : packNext 0 1 b = 1 := by simp [packNext, hpos]
  have hone : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  have hcomp := bankCellUnitsPos (bankInheritedComparisonPrice b)
    p.atoms.length (bankCellComparisonPos b) hp1
  have hissue := bankCellPriceRootIssueStrict b k
  have hc0 := bankCellUnitsStrict _ _ p.atoms.length hissue.1 hp1
  have hc1 := bankCellUnitsStrict _ _ p.atoms.length hissue.2 hp1
  cases ty
  case E =>
    cases bity <;> cases hθ : θ 0 <;>
      simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
        bankCellControllerUnitsWaiting,
        renewalBankWaitSlot, isWaitMode, isRetTok,
        renewalBankActivePayload, hp, hone, hbne, hθ] <;>
      omega
  case RL =>
    obtain ⟨q, rfl, hq⟩ := hstall rfl
    have hw := bankCellUnitsPos _ q.atoms.length
      (bankCellWorkerPricePos b .RL 1 k (by decide)) hq
    simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      renewalBankWaitSlot, isWaitMode, isRetTok, hp, hone, hbne] at hw ⊢
    omega
  case AL =>
    obtain ⟨q, rfl, hq⟩ := hstall rfl
    have hw := bankCellUnitsPos _ q.atoms.length
      (bankCellWorkerPricePos b .AL 1 k (by decide)) hq
    simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      renewalBankWaitSlot, isWaitMode, isRetTok, hp, hone, hbne] at hw ⊢
    omega
  case CL0 =>
    obtain ⟨q, rfl, hq⟩ := hstall rfl
    have hw := bankCellUnitsPos _ q.atoms.length
      (bankCellWorkerPricePos b .CL0 1 k (by decide)) hq
    simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      renewalBankWaitSlot, isWaitMode, isRetTok, hp, hone, hbne] at hw ⊢
    omega
  case CL1 =>
    obtain ⟨q, rfl, hq⟩ := hstall rfl
    have hw := bankCellUnitsPos _ q.atoms.length
      (bankCellWorkerPricePos b .CL1 1 k (by decide)) hq
    simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      renewalBankWaitSlot, isWaitMode, isRetTok, hp, hone, hbne] at hw ⊢
    omega
  all_goals
    simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
      renewalBankWaitSlot, isWaitMode, isRetTok, hp, hone, hbne]
    omega

/-- P2: an inherited CSTART stock pays on its outgoing edge unless the
first digit holds an atom-free return token.
Consumer: `bankInheritedProgressOfCStart`. -/
theorem bankCellStrictCStartX {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (sx sy : RenewalBankSite n) (p : RenewalBankPayload n)
    (hb : 2 ≤ b) (hx0 : x0.role = 0) (hmx : x0.mode = .CSTART)
    (hvX : sx.controller = .active p) (hp1 : 1 ≤ p.atoms.length)
    (hstall : y0.role = 1 → isRetTok y0.tok = true →
      ∃ q : RenewalBankPayload n, sy.worker = .payload q ∧
        1 ≤ q.atoms.length) :
    BankCellStrictGoal b k θ service e dest x0 y0 sx sy := by
  rcases x0 with ⟨a, mx, bitx, tx, lx, gx⟩
  rcases y0 with ⟨c0, my, bity, ty, ly, gy⟩
  rcases sx with ⟨wX, vX⟩
  rcases sy with ⟨wY, vY⟩
  dsimp only at hx0 hmx hvX hstall
  subst hx0 hmx hvX
  by_cases hclear : gx = true ∨ c0 ≠ 1
  · exact bankCellStrictRootClearX b k θ service e dest bitx tx lx gx c0
      my bity ty ly gy wX wY p vY hb hp1 hclear
  · have hg : gx = false := by
      cases gx
      · rfl
      · exact False.elim (hclear (Or.inl rfl))
    have hc : c0 = 1 := by
      by_cases h : c0 = 1
      · exact h
      · exact False.elim (hclear (Or.inr h))
    subst hg hc
    exact bankCellStrictRootCStartX b k θ service e dest bitx tx lx
      my bity ty ly gy wX wY p vY hb hp1 (hstall rfl)

/-- A return token on the first digit is dearer than the controller
slot it merges into.  Consumer: `bankCellStrictRootWaitY`. -/
theorem bankCellPriceRootReturnStrict (b k : Nat) (hb : 1 ≤ b) :
    bankInheritedArmedPrice b + 1 ≤ bankInheritedWorkerPrice b .RL 1 k ∧
    bankInheritedComparisonPrice b + 1 ≤
      bankInheritedWorkerPrice b .AL 1 k ∧
    bankInheritedArmedPrice b + 1 ≤
      bankInheritedWorkerPrice b .CL0 1 k := by
  rw [bankCellPriceRet b 1 k .RL hb (by simp),
    bankCellPriceRet b 1 k .AL hb (by simp),
    bankCellPriceRet b 1 k .CL0 hb (by simp)]
  have hv := bankCellBaseValues b
  rw [hv.1, hv.2.1, hv.2.2.1]
  omega

/-- A return token one role lower is strictly cheaper.
Consumer: `bankCellStrictInteriorY`, `bankCellStrictTopY`. -/
theorem bankCellPriceRetBackStrict (b a k : Nat) (t : BTok)
    (ht : t = .RL ∨ t = .AL ∨ t = .CL0 ∨ t = .CL1)
    (h : a + 1 ≤ b) :
    bankInheritedWorkerPrice b t a (a + 1) + 1 ≤
      bankInheritedWorkerPrice b t (a + 1) k := by
  rw [bankCellPriceRet b a (a + 1) t (by omega) ht,
    bankCellPriceRet b (a + 1) k t h ht]
  omega

/-- P4, grant source: the first digit's worker is cleared.
Consumer: `bankCellStrictReturnY`. -/
theorem bankCellStrictRootGrantY {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX : RenewalBankWorker n) (q : RenewalBankPayload n)
    (vX vY : RenewalBankController n) (hb : 2 ≤ b)
    (hty : ty ≠ .E) (hq : 1 ≤ q.atoms.length) :
    BankCellStrictGoal b k θ service e dest
      ⟨0, mx, bitx, tx, lx, true⟩ ⟨1, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨.payload q, vY⟩ := by
  have hpos : 0 < b := by omega
  have hp : packNext 0 1 b = 1 := by simp [packNext, hpos]
  have hone : 1 ≤ b := by omega
  have hw := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b ty 1 k hty) hq
  simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
    bankCellWorkerUnitsPayload, hp, hone]
  omega

/-- P4 at a RESET or waiting root: launch overwrite, merge, or
mismatched consumption.  Consumer: `bankCellStrictReturnY`. -/
theorem bankCellStrictRootWaitY {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX : RenewalBankWorker n) (q : RenewalBankPayload n)
    (vX vY : RenewalBankController n) (hb : 2 ≤ b)
    (hmx : mx ≠ .ARMED ∧ mx ≠ .CSTART)
    (hty : isRetTok ty = true) (hq : 1 ≤ q.atoms.length) :
    BankCellStrictGoal b k θ service e dest
      ⟨0, mx, bitx, tx, lx, false⟩ ⟨1, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨.payload q, vY⟩ := by
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
  have hs := bankCellPriceRootReturnStrict b k hone
  have hs1 := bankCellUnitsStrict _ _ q.atoms.length hs.1 hq
  have hs2 := bankCellUnitsStrict _ _ q.atoms.length hs.2.1 hq
  have hs3 := bankCellUnitsStrict _ _ q.atoms.length hs.2.2 hq
  have hd1 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .RL 1 k (by decide)) hq
  have hd2 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .AL 1 k (by decide)) hq
  have hd3 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .CL0 1 k (by decide)) hq
  have hd4 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .CL1 1 k (by decide)) hq
  cases ty <;> simp [isRetTok] at hty <;>
    cases mx <;> by_cases hl : 1 < lx <;>
      simp at hmx <;>
      simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        bankCellWorkerUnitsPayload, bankCellControllerUnitsActive,
        bankCellControllerUnitsWaiting,
        renewalBankWaitSlot, isWaitMode, isRetTok,
        renewalBankReturned, renewalBankWorkerPayload,
        Nat.mul_add, hp, hone, hbne, hl] <;>
      omega

/-- P4 at an ARMED or CSTART root: the return token is consumed.
Consumer: `bankCellStrictReturnY`. -/
theorem bankCellStrictRootActiveY {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX : RenewalBankWorker n) (q : RenewalBankPayload n)
    (vX vY : RenewalBankController n) (hb : 2 ≤ b)
    (hmx : mx = .ARMED ∨ mx = .CSTART)
    (hty : isRetTok ty = true) (hq : 1 ≤ q.atoms.length) :
    BankCellStrictGoal b k θ service e dest
      ⟨0, mx, bitx, tx, lx, false⟩ ⟨1, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨.payload q, vY⟩ := by
  have hpos : 0 < b := by omega
  have hp : packNext 0 1 b = 1 := by simp [packNext, hpos]
  have hone : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  have hd1 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .RL 1 k (by decide)) hq
  have hd2 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .AL 1 k (by decide)) hq
  have hd3 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .CL0 1 k (by decide)) hq
  have hd4 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .CL1 1 k (by decide)) hq
  rcases hmx with rfl | rfl <;>
    cases ty <;> simp [isRetTok] at hty <;>
      simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
        bankCellWorkerUnitsPayload,
        renewalBankWaitSlot, isWaitMode, isRetTok, hp, hone, hbne] <;>
      omega

/-- P4 on an interior digit pair: the return token moves down, is
overwritten, or collides.  Consumer: `bankCellStrictReturnY`. -/
theorem bankCellStrictInteriorY {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX : RenewalBankWorker n) (q : RenewalBankPayload n)
    (vX vY : RenewalBankController n)
    (ha : 1 ≤ a) (htop : a + 1 < b)
    (hty : isRetTok ty = true) (hq : 1 ≤ q.atoms.length) :
    BankCellStrictGoal b k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨a + 1, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨.payload q, vY⟩ := by
  have hab : a < b := by omega
  have hp : packNext a (a + 1) b = a + 1 := by simp [packNext, hab]
  have ha0 : a ≠ 0 := by omega
  have hab' : a ≤ b := by omega
  have hpb : a + 1 ≤ b := by omega
  have hne1 : a ≠ b := by omega
  have hne2 : a + 1 ≠ b := by omega
  have hRR := bankCellWorkerUnitsMono b .RR .RR a (a + 1) (a + 1) k wX
    (Nat.le_of_lt (bankInheritedRRForwardPriceLe b a k hab))
  have hm1 := bankCellUnitsStrict _ _ q.atoms.length
    (bankCellPriceRetBackStrict b a k .RL (by simp) hpb) hq
  have hm2 := bankCellUnitsStrict _ _ q.atoms.length
    (bankCellPriceRetBackStrict b a k .AL (by simp) hpb) hq
  have hm3 := bankCellUnitsStrict _ _ q.atoms.length
    (bankCellPriceRetBackStrict b a k .CL0 (by simp) hpb) hq
  have hm4 := bankCellUnitsStrict _ _ q.atoms.length
    (bankCellPriceRetBackStrict b a k .CL1 (by simp) hpb) hq
  have hd1 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .RL (a + 1) k (by decide)) hq
  have hd2 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .AL (a + 1) k (by decide)) hq
  have hd3 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .CL0 (a + 1) k (by decide)) hq
  have hd4 := bankCellUnitsPos _ q.atoms.length
    (bankCellWorkerPricePos b .CL1 (a + 1) k (by decide)) hq
  rw [bankCellStrictGoal_nonroot _ _ _ _ _ _ _ _ _ _ ha0 (by simp [hp])]
  simp [isRetTok]
  all_goals (cases ty <;> simp [isRetTok] at hty <;>
    cases tx <;>
      simp [bankPairNR, bankMemoryNRW, bankCellSiteUnits,
        bankCellWorkerUnitsPayload,
        hp, ha0, ha, hab, hab', hpb, hne1, hne2] <;>
      (repeat' split) <;>
      omega)

/-- The top turns are strictly cheaper.  Consumer: `bankCellStrictTopY`. -/
theorem bankCellPriceTopTurnStrict (a k : Nat) :
    bankInheritedWorkerPrice (a + 1) .RL a (a + 1) + 1 ≤
      bankInheritedWorkerPrice (a + 1) .RR (a + 1) k ∧
    bankInheritedWorkerPrice (a + 1) .CL1 a (a + 1) + 1 ≤
      bankInheritedWorkerPrice (a + 1) .CR1 (a + 1) k ∧
    bankInheritedWorkerPrice (a + 1) .CL0 a (a + 1) + 1 ≤
      bankInheritedWorkerPrice (a + 1) .CR0 (a + 1) k := by
  rw [bankCellPriceRet (a + 1) a (a + 1) .RL (by omega) (by simp),
    bankCellPriceRet (a + 1) a (a + 1) .CL1 (by omega) (by simp),
    bankCellPriceRet (a + 1) a (a + 1) .CL0 (by omega) (by simp),
    bankCellPriceFwd (a + 1) (a + 1) k .CR1 (by simp),
    bankCellPriceFwd (a + 1) (a + 1) k .CR0 (by simp)]
  have h := (bankCellPriceRR (a + 1) (a + 1) k).1
  have hv := bankCellBaseValues (a + 1)
  rw [hv.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2]
  omega

/-- P4 and P6 on the top digit pair: the responder's return or
outward token moves down, turns, is deleted, or is overwritten.
Consumer: `bankCellStrictReturnY`, `bankCellStrictTopOutwardY`. -/
theorem bankCellStrictTopY {n : Nat} (k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (wX : RenewalBankWorker n) (q : RenewalBankPayload n)
    (vX vY : RenewalBankController n)
    (ha : 1 ≤ a) (hty : ty ≠ .E) (hq : 1 ≤ q.atoms.length) :
    BankCellStrictGoal (a + 1) k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨a + 1, my, bity, ty, ly, gy⟩
      ⟨wX, vX⟩ ⟨.payload q, vY⟩ := by
  have hab : a < a + 1 := by omega
  have hp : packNext a (a + 1) (a + 1) = a + 1 := by
    simp [packNext]
  have ha0 : a ≠ 0 := by omega
  have hne1 : a ≠ a + 1 := by omega
  have hpb : a + 1 ≤ a + 1 := Nat.le_refl _
  have hRR := bankCellWorkerUnitsMono (a + 1) .RR .RR a (a + 1)
    (a + 1) k wX
    (Nat.le_of_lt (bankInheritedRRForwardPriceLe (a + 1) a k hab))
  have hIR := bankCellWorkerUnitsMono (a + 1) .IR .IR a (a + 1)
    (a + 1) k wX
    (bankCellPriceFwdStep (a + 1) a k .IR .IR (by simp) (by simp)
      rfl hab)
  have hIA := bankCellWorkerUnitsMono (a + 1) .IR .AL a (a + 1)
    (a + 1) k wX (bankCellPriceIRToAL (a + 1) a k hab)
  have hC0 := bankCellWorkerUnitsMono (a + 1) .CR0 .CR0 a (a + 1)
    (a + 1) k wX
    (bankCellPriceFwdStep (a + 1) a k .CR0 .CR0 (by simp) (by simp)
      rfl hab)
  have hC1 := bankCellWorkerUnitsMono (a + 1) .CR1 .CR1 a (a + 1)
    (a + 1) k wX
    (bankCellPriceFwdStep (a + 1) a k .CR1 .CR1 (by simp) (by simp)
      rfl hab)
  have hbv := bankCellBaseValues (a + 1)
  have hC10 := bankCellWorkerUnitsMono (a + 1) .CR1 .CR0 a (a + 1)
    (a + 1) k wX
    (bankCellPriceFwdStep (a + 1) a k .CR1 .CR0 (by simp) (by simp)
      (by rw [hbv.2.2.2.2.2.1, hbv.2.2.2.2.2.2]) hab)
  have hC01 := bankCellWorkerUnitsMono (a + 1) .CR0 .CR1 a (a + 1)
    (a + 1) k wX
    (bankCellPriceFwdStep (a + 1) a k .CR0 .CR1 (by simp) (by simp)
      (by rw [hbv.2.2.2.2.2.1, hbv.2.2.2.2.2.2]) hab)
  have hm1 := bankCellUnitsStrict _ _ q.atoms.length
    (bankCellPriceRetBackStrict (a + 1) a k .RL (by simp) hpb) hq
  have hm2 := bankCellUnitsStrict _ _ q.atoms.length
    (bankCellPriceRetBackStrict (a + 1) a k .AL (by simp) hpb) hq
  have hm3 := bankCellUnitsStrict _ _ q.atoms.length
    (bankCellPriceRetBackStrict (a + 1) a k .CL0 (by simp) hpb) hq
  have hm4 := bankCellUnitsStrict _ _ q.atoms.length
    (bankCellPriceRetBackStrict (a + 1) a k .CL1 (by simp) hpb) hq
  have ht := bankCellPriceTopTurnStrict a k
  have ht1 := bankCellUnitsStrict _ _ q.atoms.length ht.1 hq
  have ht2 := bankCellUnitsStrict _ _ q.atoms.length ht.2.1 hq
  have ht3 := bankCellUnitsStrict _ _ q.atoms.length ht.2.2 hq
  have hd : ∀ t : BTok, t ≠ .E →
      1 ≤ bankInheritedWorkerPrice (a + 1) t (a + 1) k * q.atoms.length :=
    fun t h => bankCellUnitsPos _ q.atoms.length
      (bankCellWorkerPricePos (a + 1) t (a + 1) k h) hq
  have hd1 := hd .RR (by decide)
  have hd2 := hd .RL (by decide)
  have hd3 := hd .IR (by decide)
  have hd4 := hd .AL (by decide)
  have hd5 := hd .CR0 (by decide)
  have hd6 := hd .CR1 (by decide)
  have hd7 := hd .CL0 (by decide)
  have hd8 := hd .CL1 (by decide)
  rw [bankCellStrictGoal_nonroot _ _ _ _ _ _ _ _ _ _ ha0 (by simp [hp])]
  simp [bankPairNR, bankMemoryNRW, bankCellSiteUnits, bankCellWorkerUnitsPayload, hp, ha0,
    ha]
  all_goals (cases ty <;> simp at hty <;>
    cases tx <;>
      simp [bankPairNR, bankMemoryNRW, bankCellSiteUnits,
        bankCellWorkerUnitsPayload, hp, ha0, ha] <;>
      (repeat' split) <;>
      omega)

/-- An RR worker facing a wrong neighbour carries one repair unit.
Consumer: `bankCellStrictInteriorChangedX`. -/
theorem bankCellPriceRRCreditStrict (b a c0 : Nat) (hab : a < b)
    (hc : c0 ≠ a + 1) :
    bankInheritedWorkerPrice b .RR a (a + 1) + 1 ≤
      bankInheritedWorkerPrice b .RR a c0 := by
  have hp1 : packNext a (a + 1) b = a + 1 := by simp [packNext, hab]
  have hp2 : packNext a c0 b = a + 1 := by simp [packNext, hab]
  have hc' : a + 1 ≠ c0 := fun h => hc h.symm
  simp [bankInheritedWorkerPrice, bankInheritedRRRepairCredit, hp1, hp2,
    hc']

/-- An outward token one role higher is strictly cheaper.
Consumer: `bankCellStrictInteriorStepX`, `bankCellStrictTopStepX`. -/
theorem bankCellPriceFwdStepStrict (b a k : Nat) (t t' : BTok)
    (ht : t = .IR ∨ t = .CR0 ∨ t = .CR1)
    (ht' : t' = .IR ∨ t' = .CR0 ∨ t' = .CR1)
    (hbase : bankInheritedWorkerBasePrice b t' =
      bankInheritedWorkerBasePrice b t)
    (h : a < b) :
    bankInheritedWorkerPrice b t' (a + 1) k + 1 ≤
      bankInheritedWorkerPrice b t a (a + 1) := by
  rw [bankCellPriceFwd b (a + 1) k t' ht',
    bankCellPriceFwd b a (a + 1) t ht, hbase]
  omega

/-- An IR worker turning into AL one digit higher is strictly cheaper.
Consumer: `bankCellFwdUnitsStrict`. -/
theorem bankCellPriceIRToALStrict (b a k : Nat) (h : a < b) :
    bankInheritedWorkerPrice b .AL (a + 1) k + 1 ≤
      bankInheritedWorkerPrice b .IR a (a + 1) := by
  rw [bankCellPriceRet b (a + 1) k .AL (by omega) (by simp),
    bankCellPriceFwd b a (a + 1) .IR (by simp)]
  have h1 := (bankCellBaseValues b).2.1
  have h2 := (bankCellBaseValues b).2.2.2.2.1
  rw [h1, h2]
  omega

/-- The outward-step strict facts for a positive source worker.
Consumer: `bankCellStrictInteriorStepX`, `bankCellStrictTopStepX`. -/
theorem bankCellFwdUnitsStrict (b a k len : Nat) (h : a < b)
    (hl : 1 ≤ len) :
    bankInheritedWorkerPrice b .RR (a + 1) k * len + 1 ≤
      bankInheritedWorkerPrice b .RR a (a + 1) * len ∧
    bankInheritedWorkerPrice b .IR (a + 1) k * len + 1 ≤
      bankInheritedWorkerPrice b .IR a (a + 1) * len ∧
    bankInheritedWorkerPrice b .AL (a + 1) k * len + 1 ≤
      bankInheritedWorkerPrice b .IR a (a + 1) * len ∧
    bankInheritedWorkerPrice b .CR0 (a + 1) k * len + 1 ≤
      bankInheritedWorkerPrice b .CR0 a (a + 1) * len ∧
    bankInheritedWorkerPrice b .CR1 (a + 1) k * len + 1 ≤
      bankInheritedWorkerPrice b .CR0 a (a + 1) * len ∧
    bankInheritedWorkerPrice b .CR0 (a + 1) k * len + 1 ≤
      bankInheritedWorkerPrice b .CR1 a (a + 1) * len ∧
    bankInheritedWorkerPrice b .CR1 (a + 1) k * len + 1 ≤
      bankInheritedWorkerPrice b .CR1 a (a + 1) * len := by
  have hv := bankCellBaseValues b
  have e01 : bankInheritedWorkerBasePrice b .CR1 =
      bankInheritedWorkerBasePrice b .CR0 := by
    rw [hv.2.2.2.2.2.1, hv.2.2.2.2.2.2]
  refine ⟨bankCellUnitsStrict _ _ len
      (bankInheritedRRForwardPriceLe b a k h) hl,
    bankCellUnitsStrict _ _ len
      (bankCellPriceFwdStepStrict b a k .IR .IR (by simp) (by simp)
        rfl h) hl,
    bankCellUnitsStrict _ _ len (bankCellPriceIRToALStrict b a k h) hl,
    bankCellUnitsStrict _ _ len
      (bankCellPriceFwdStepStrict b a k .CR0 .CR0 (by simp) (by simp)
        rfl h) hl,
    bankCellUnitsStrict _ _ len
      (bankCellPriceFwdStepStrict b a k .CR0 .CR1 (by simp) (by simp)
        e01 h) hl,
    bankCellUnitsStrict _ _ len
      (bankCellPriceFwdStepStrict b a k .CR1 .CR0 (by simp) (by simp)
        e01.symm h) hl,
    bankCellUnitsStrict _ _ len
      (bankCellPriceFwdStepStrict b a k .CR1 .CR1 (by simp) (by simp)
        rfl h) hl⟩

/-- P5 with a changed responder: an outward RR worker loses its
repair unit; any other outward worker is deleted.
Consumer: `bankCellStrictUpX`. -/
theorem bankCellStrictInteriorChangedX {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool) (c0 : Nat)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (q : RenewalBankPayload n) (wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n)
    (ha : 1 ≤ a) (hab : a < b) (hc : c0 ≠ a + 1)
    (htx : tx = .RR ∨ tx = .IR ∨ tx = .CR0 ∨ tx = .CR1)
    (hq : 1 ≤ q.atoms.length) :
    BankCellStrictGoal b k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨c0, my, bity, ty, ly, gy⟩
      ⟨.payload q, vX⟩ ⟨wY, vY⟩ := by
  have hp : packNext a c0 b = a + 1 := by simp [packNext, hab]
  have ha0 : a ≠ 0 := by omega
  have hab' : a ≤ b := by omega
  have hpb : a + 1 ≤ b := by omega
  have hc' : a + 1 ≠ c0 := fun h => hc h.symm
  have hcred := bankCellUnitsStrict _ _ q.atoms.length
    (bankCellPriceRRCreditStrict b a c0 hab hc) hq
  have hd : ∀ t : BTok, t ≠ .E →
      1 ≤ bankInheritedWorkerPrice b t a c0 * q.atoms.length :=
    fun t h => bankCellUnitsPos _ q.atoms.length
      (bankCellWorkerPricePos b t a c0 h) hq
  have hd1 := hd .IR (by decide)
  have hd2 := hd .CR0 (by decide)
  have hd3 := hd .CR1 (by decide)
  rcases htx with rfl | rfl | rfl | rfl <;>
    simp [BankCellStrictGoal, bankPair, bankCellMemory, bankCellSiteUnits,
      bankCellWorkerUnitsPayload,
      hp, ha0, ha, hab, hab', hpb, hc'] <;>
    omega

/-- P5 on an interior digit pair: an outward worker advances.
Consumer: `bankCellStrictUpX`. -/
theorem bankCellStrictInteriorStepX {n : Nat} (b k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (q : RenewalBankPayload n) (wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n)
    (ha : 1 ≤ a) (htop : a + 1 < b)
    (htx : tx = .RR ∨ tx = .IR ∨ tx = .CR0 ∨ tx = .CR1)
    (hq : 1 ≤ q.atoms.length) :
    BankCellStrictGoal b k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨a + 1, my, bity, ty, ly, gy⟩
      ⟨.payload q, vX⟩ ⟨wY, vY⟩ := by
  have hab : a < b := by omega
  have hp : packNext a (a + 1) b = a + 1 := by simp [packNext, hab]
  have ha0 : a ≠ 0 := by omega
  have hab' : a ≤ b := by omega
  have hpb : a + 1 ≤ b := by omega
  have hne1 : a ≠ b := by omega
  have hne2 : a + 1 ≠ b := by omega
  have hRL := bankCellWorkerUnitsMono b .RL .RL (a + 1) a k (a + 1) wY
    (bankCellPriceRetBack b a k .RL (by simp) hpb)
  have hAL := bankCellWorkerUnitsMono b .AL .AL (a + 1) a k (a + 1) wY
    (bankCellPriceRetBack b a k .AL (by simp) hpb)
  have hCL0 := bankCellWorkerUnitsMono b .CL0 .CL0 (a + 1) a k (a + 1) wY
    (bankCellPriceRetBack b a k .CL0 (by simp) hpb)
  have hCL1 := bankCellWorkerUnitsMono b .CL1 .CL1 (a + 1) a k (a + 1) wY
    (bankCellPriceRetBack b a k .CL1 (by simp) hpb)
  have hs := bankCellFwdUnitsStrict b a k q.atoms.length hab hq
  have hd : ∀ t : BTok, t ≠ .E →
      1 ≤ bankInheritedWorkerPrice b t a (a + 1) * q.atoms.length :=
    fun t h => bankCellUnitsPos _ q.atoms.length
      (bankCellWorkerPricePos b t a (a + 1) h) hq
  have hd1 := hd .RR (by decide)
  have hd2 := hd .IR (by decide)
  have hd3 := hd .CR0 (by decide)
  have hd4 := hd .CR1 (by decide)
  rcases hs with ⟨s1, s2, s3, s4, s5, s6, s7⟩
  rw [bankCellStrictGoal_nonroot _ _ _ _ _ _ _ _ _ _ ha0 (by simp [hp])]
  simp [bankPairNR, bankMemoryNRW, bankCellSiteUnits, bankCellWorkerUnitsPayload, hp, ha0,
    ha, hab, hab', hpb, hne1, hne2]
  all_goals (rcases htx with rfl | rfl | rfl | rfl <;> cases ty <;>
    simp [bankPairNR, bankMemoryNRW, bankCellSiteUnits,
      bankCellWorkerUnitsPayload,
      hp, ha0, ha, hab, hab', hpb, hne1, hne2] <;>
    (repeat' split) <;>
    omega)

/-- P5 below the top digit: an outward worker reaches the top.
Consumer: `bankCellStrictUpX`. -/
theorem bankCellStrictTopStepX {n : Nat} (k : Nat)
    (θ : Nat → Bool) (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (q : RenewalBankPayload n) (wY : RenewalBankWorker n)
    (vX vY : RenewalBankController n)
    (ha : 1 ≤ a)
    (htx : tx = .RR ∨ tx = .IR ∨ tx = .CR0 ∨ tx = .CR1)
    (hq : 1 ≤ q.atoms.length) :
    BankCellStrictGoal (a + 1) k θ service e dest
      ⟨a, mx, bitx, tx, lx, gx⟩ ⟨a + 1, my, bity, ty, ly, gy⟩
      ⟨.payload q, vX⟩ ⟨wY, vY⟩ := by
  have hab : a < a + 1 := by omega
  have hp : packNext a (a + 1) (a + 1) = a + 1 := by
    simp [packNext]
  have ha0 : a ≠ 0 := by omega
  have hne1 : a ≠ a + 1 := by omega
  have hpb : a + 1 ≤ a + 1 := Nat.le_refl _
  have hRL := bankCellWorkerUnitsMono (a + 1) .RL .RL (a + 1) a k
    (a + 1) wY (bankCellPriceRetBack (a + 1) a k .RL (by simp) hpb)
  have hAL := bankCellWorkerUnitsMono (a + 1) .AL .AL (a + 1) a k
    (a + 1) wY (bankCellPriceRetBack (a + 1) a k .AL (by simp) hpb)
  have hCL0 := bankCellWorkerUnitsMono (a + 1) .CL0 .CL0 (a + 1) a k
    (a + 1) wY (bankCellPriceRetBack (a + 1) a k .CL0 (by simp) hpb)
  have hCL1 := bankCellWorkerUnitsMono (a + 1) .CL1 .CL1 (a + 1) a k
    (a + 1) wY (bankCellPriceRetBack (a + 1) a k .CL1 (by simp) hpb)
  have hRRT := bankCellWorkerUnitsMono (a + 1) .RR .RL (a + 1) a k
    (a + 1) wY (bankCellPriceRRTop a k)
  have hCRT1 := bankCellWorkerUnitsMono (a + 1) .CR1 .CL1 (a + 1) a k
    (a + 1) wY (bankCellPriceCRTop a k).1
  have hCRT0 := bankCellWorkerUnitsMono (a + 1) .CR0 .CL0 (a + 1) a k
    (a + 1) wY (bankCellPriceCRTop a k).2
  have hs := bankCellFwdUnitsStrict (a + 1) a k q.atoms.length hab hq
  have hd : ∀ t : BTok, t ≠ .E →
      1 ≤ bankInheritedWorkerPrice (a + 1) t a (a + 1) * q.atoms.length :=
    fun t h => bankCellUnitsPos _ q.atoms.length
      (bankCellWorkerPricePos (a + 1) t a (a + 1) h) hq
  have hd1 := hd .RR (by decide)
  have hd2 := hd .IR (by decide)
  have hd3 := hd .CR0 (by decide)
  have hd4 := hd .CR1 (by decide)
  rcases hs with ⟨s1, s2, s3, s4, s5, s6, s7⟩
  rw [bankCellStrictGoal_nonroot _ _ _ _ _ _ _ _ _ _ ha0 (by simp [hp])]
  simp [bankPairNR, bankMemoryNRW, bankCellSiteUnits, bankCellWorkerUnitsPayload, hp, ha0,
    ha]
  all_goals (rcases htx with rfl | rfl | rfl | rfl <;> cases ty <;>
    simp [bankPairNR, bankMemoryNRW, bankCellSiteUnits,
      bankCellWorkerUnitsPayload, hp, ha0, ha] <;>
    (repeat' split) <;>
    omega)

/-- P3: a positive worker outside the digit roles pays on its
outgoing edge.  Consumer: `bankInheritedProgressOfWorker`. -/
theorem bankCellStrictOutsideX {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (sx sy : RenewalBankSite n) (q : RenewalBankPayload n)
    (hb : 2 ≤ b)
    (hcx : bankInFlightControllerShape x0.role x0.mode sx.controller)
    (hwy : bankInFlightWorkerShape y0.tok sy.worker)
    (harmX : bankCellArmed x0 sx = 0)
    (hout : ¬ (1 ≤ x0.role ∧ x0.role ≤ b))
    (hwq : sx.worker = .payload q) (hq : 1 ≤ q.atoms.length)
    (htx : x0.tok ≠ .E) :
    BankCellStrictGoal b k θ service e dest x0 y0 sx sy := by
  rcases sx with ⟨w, v⟩
  dsimp only at hwq hcx
  subst hwq
  exact bankCellStrictOutside b k θ service e dest x0 y0 (.payload q) v sy
    hb hcx hwy harmX hout
    (bankCellUnitsPos _ _ (bankCellWorkerPricePos b x0.tok x0.role
      y0.role htx) hq)

/-- P5: a positive outward worker below the top pays on its
outgoing edge.  Consumer: `bankInheritedProgressOfWorker`. -/
theorem bankCellStrictUpX {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (sx sy : RenewalBankSite n) (q : RenewalBankPayload n)
    (ha : 1 ≤ x0.role) (hab : x0.role < b)
    (hwq : sx.worker = .payload q) (hq : 1 ≤ q.atoms.length)
    (htx : x0.tok = .RR ∨ x0.tok = .IR ∨ x0.tok = .CR0 ∨
      x0.tok = .CR1) :
    BankCellStrictGoal b k θ service e dest x0 y0 sx sy := by
  rcases x0 with ⟨a, mx, bitx, tx, lx, gx⟩
  rcases y0 with ⟨c0, my, bity, ty, ly, gy⟩
  rcases sx with ⟨wX, vX⟩
  rcases sy with ⟨wY, vY⟩
  dsimp only at ha hab hwq htx
  subst hwq
  by_cases hc : c0 = a + 1
  · subst hc
    by_cases htop : a + 1 < b
    · exact bankCellStrictInteriorStepX b k θ service e dest a mx bitx tx
        lx gx my bity ty ly gy q wY vX vY ha htop htx hq
    · obtain rfl : b = a + 1 := by omega
      exact bankCellStrictTopStepX k θ service e dest a mx bitx tx lx gx
        my bity ty ly gy q wY vX vY ha htx hq
  · exact bankCellStrictInteriorChangedX b k θ service e dest a mx bitx tx
      lx gx c0 my bity ty ly gy q wY vX vY ha hab hc htx hq

/-- P4 and P6: a positive digit worker carrying a return token, or
any token on the top digit, pays on its incoming edge.
Consumer: `bankInheritedProgressOfWorker`. -/
theorem bankCellStrictPredY {n : Nat} (b k : Nat) (θ : Nat → Bool)
    (service : Nat) (e dest : Fin n) (x0 y0 : BankCell)
    (sx sy : RenewalBankSite n) (q : RenewalBankPayload n)
    (hb : 2 ≤ b)
    (hcx : bankInFlightControllerShape x0.role x0.mode sx.controller)
    (hwy : bankInFlightWorkerShape y0.tok sy.worker)
    (harmX : bankCellArmed x0 sx = 0)
    (hy1 : 1 ≤ y0.role) (hyb : y0.role ≤ b)
    (hwq : sy.worker = .payload q) (hq : 1 ≤ q.atoms.length)
    (hty : y0.tok ≠ .E)
    (hret : isRetTok y0.tok = true ∨ y0.role = b) :
    BankCellStrictGoal b k θ service e dest x0 y0 sx sy := by
  by_cases hch : packNext x0.role y0.role b = y0.role
  · rcases x0 with ⟨a, mx, bitx, tx, lx, gx⟩
    rcases y0 with ⟨c0, my, bity, ty, ly, gy⟩
    rcases sx with ⟨wX, vX⟩
    rcases sy with ⟨wY, vY⟩
    dsimp only at hy1 hyb hwq hty hret hch
    subst hwq
    have hlt : a < b := by
      by_cases hn : a < b
      · exact hn
      · by_cases hae : a = b
        · subst hae
          by_cases hc0 : c0 = 0
          · omega
          · simp [packNext, hc0] at hch <;> omega
        · simp [packNext, hn, hae] at hch <;> omega
    have hca : c0 = a + 1 := by
      simp [packNext, hlt] at hch <;> omega
    subst hca
    by_cases ha0 : a = 0
    · subst ha0
      have hr : isRetTok ty = true := by
        rcases hret with h | h
        · exact h
        · omega
      cases gx
      · by_cases hmx : mx = .ARMED ∨ mx = .CSTART
        · exact bankCellStrictRootActiveY b k θ service e dest mx bitx tx
            lx my bity ty ly gy wX q vX vY hb hmx hr hq
        · have hmx' : mx ≠ .ARMED ∧ mx ≠ .CSTART :=
            ⟨fun h => hmx (Or.inl h), fun h => hmx (Or.inr h)⟩
          exact bankCellStrictRootWaitY b k θ service e dest mx bitx tx lx
            my bity ty ly gy wX q vX vY hb hmx' hr hq
      · exact bankCellStrictRootGrantY b k θ service e dest mx bitx tx lx
          my bity ty ly gy wX q vX vY hb hty hq
    · by_cases htop : a + 1 < b
      · have hr : isRetTok ty = true := by
          rcases hret with h | h
          · exact h
          · omega
        exact bankCellStrictInteriorY b k θ service e dest a mx bitx tx lx
          gx my bity ty ly gy wX q vX vY (by omega) htop hr hq
      · obtain rfl : b = a + 1 := by omega
        exact bankCellStrictTopY k θ service e dest a mx bitx tx lx gx
          my bity ty ly gy wX q vX vY (by omega) hty hq
  · apply bankCellStrictChanged b k θ service e dest x0 y0 sx sy hb hcx
      hwy harmX hch
    unfold bankCellSiteUnits
    rw [hwq, bankCellWorkerUnitsPayload]
    have := bankCellUnitsPos _ _ (bankCellWorkerPricePos b y0.tok y0.role
      k hty) hq
    omega

/-! ## Part B: from a strict cell to a strict potential drop -/

/-- Agent-level strict core: a strict cell inequality on the OLD
cells gives a drop of n in the two selected scores.
Consumer: `bankInheritedStrictEdgeOfCell`. -/
theorem bankInheritedCellStrictCore {n : Nat} (c : Compiled)
    (hs : c.useSmall = false)
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c)
    (k : Nat) (cut : Bool)
    (h : BankCellStrictGoal c.b k c.theta m.service e dest
      (bankCell x x.pack.val) (bankCell y y.pack.val)
      (m.sites e) (m.sites dest)) :
    bankInheritedCellPairAfter c m e dest x y k cut + n ≤
      bankInheritedCellPairBefore c m e dest x y k := by
  have hcore :
      bankCellSiteUnits c.b (Counter.resetBankOld x y).1 x.pack.val
          (packNext x.pack.val y.pack.val c.b)
          (renewalBankPairMemory c m e dest x y).1 +
        bankCellSiteUnits c.b (Counter.resetBankOld x y).2
          (packNext x.pack.val y.pack.val c.b) k
          (renewalBankPairMemory c m e dest x y).2 + 1 ≤
      bankCellSiteUnits c.b (bankCell x x.pack.val) x.pack.val
          y.pack.val (m.sites e) +
        bankCellSiteUnits c.b (bankCell y y.pack.val) y.pack.val k
          (m.sites dest) := h
  rw [← bankCellMaskedResponderPackVal c cut x y] at hcore
  have hs1 := bankCellMaskedSourceUnits c hs cut x y
    (renewalMaskedPair c cut x y).2.pack.val
    (renewalBankPairMemory c m e dest x y).1
  have hs2 := bankCellMaskedResponderUnits c hs cut x y k
    (renewalBankPairMemory c m e dest x y).2
  unfold bankInheritedCellPairAfter bankInheritedCellPairBefore
  rw [bankCellSiteWeightUnits c (renewalMaskedPair c cut x y).1,
    bankCellSiteWeightUnits c (renewalMaskedPair c cut x y).2,
    bankCellSiteWeightUnits c x, bankCellSiteWeightUnits c y]
  have hm := Nat.mul_le_mul_left n hcore
  have m1 := Nat.mul_le_mul_left n hs1
  have m2 := Nat.mul_le_mul_left n hs2
  simp only [Nat.mul_add, Nat.mul_one] at hm
  omega

/-- The strict cell goal at the selected edge of a reference state.
Consumer: `bankInheritedStrictEdgeOfCell` and Part D. -/
def BankInheritedEdgeCell {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n) : Prop :=
  BankCellStrictGoal (compileAdvice (ceilLogTwo n)).b
    (z.val.1 (ring.rightNeighbor (ring.rightNeighbor e))).pack.val
    (compileAdvice (ceilLogTwo n)).theta z.val.2.service
    e (ring.rightNeighbor e)
    (bankCell (z.val.1 e) (z.val.1 e).pack.val)
    (bankCell (z.val.1 (ring.rightNeighbor e))
      (z.val.1 (ring.rightNeighbor e)).pack.val)
    (z.val.2.sites e) (z.val.2.sites (ring.rightNeighbor e))

/-- A strict cell at edge e drops the literal potential by n.
Consumer: `bankInheritedProgressAlternativeHolds`. -/
theorem bankInheritedStrictEdgeOfCell
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hcell : BankInheritedEdgeCell ring hbank z e) :
    bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) + n ≤
      bankInheritedPotential ring hbank z := by
  have htwo : 2 ≤ n := by omega
  have hpair := rbReferenceSelectedPairFrame ring htwo z.val e
  have hthirdNeSource :
      ring.rightNeighbor (ring.rightNeighbor e) ≠ e :=
    bankInheritedSecondNeighborDistinct ring hn e
  have hthirdNeResponder :
      ring.rightNeighbor (ring.rightNeighbor e) ≠
        ring.rightNeighbor e :=
    Counter.resetRootPortDistinct
      ring (ring.rightNeighbor e) htwo
  have hthird := (rbReferenceOutsideSiteFrame
    ring z.val e
      (ring.rightNeighbor (ring.rightNeighbor e))
      hthirdNeSource hthirdNeResponder).1
  have hstrict := bankInheritedCellStrictCore
    (compileAdvice (ceilLogTwo n)) hbank
    z.val.2 e (ring.rightNeighbor e)
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    (z.val.1 (ring.rightNeighbor (ring.rightNeighbor e))).pack.val
    (renewalBankCut ring z.val.1 z.val.2 e) hcell
  have hafter :
      bankInheritedScore ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) e +
        bankInheritedScore ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) (ring.rightNeighbor e) =
      bankInheritedCellPairAfter
        (compileAdvice (ceilLogTwo n))
        z.val.2 e (ring.rightNeighbor e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
        (z.val.1
          (ring.rightNeighbor (ring.rightNeighbor e))).pack.val
        (renewalBankCut ring z.val.1 z.val.2 e) := by
    change
      bankInheritedSiteWeight (compileAdvice (ceilLogTwo n))
          ((rbRun ring z.val [e]).1 e)
          ((rbRun ring z.val [e]).1
            (ring.rightNeighbor e)).pack.val
          ((rbRun ring z.val [e]).2.sites e) +
        bankInheritedSiteWeight (compileAdvice (ceilLogTwo n))
          ((rbRun ring z.val [e]).1 (ring.rightNeighbor e))
          ((rbRun ring z.val [e]).1
            (ring.rightNeighbor (ring.rightNeighbor e))).pack.val
          ((rbRun ring z.val [e]).2.sites
            (ring.rightNeighbor e)) = _
    rw [hpair.1, hpair.2.1, hpair.2.2.1,
      hpair.2.2.2,
      congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.pack.val) hthird]
    rfl
  have hbefore :
      bankInheritedScore ring hbank z e +
        bankInheritedScore ring hbank z
          (ring.rightNeighbor e) =
      bankInheritedCellPairBefore
        (compileAdvice (ceilLogTwo n))
        z.val.2 e (ring.rightNeighbor e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
        (z.val.1
          (ring.rightNeighbor (ring.rightNeighbor e))).pack.val := by
    rfl
  have hbal := bankInheritedPotentialTwoSiteBalance ring htwo hbank z e
  omega

/-! ## Part C: the order invariant -/

/-- Worker, controller and PACK bookkeeping of one OLD pair, as used
by the order invariant: the source worker is cleared, kept, or
receives the responder's worker; the responder worker is cleared,
kept on an unchanged role, receives the source worker, or is
launched by an atom-free root; the source controller loses atoms
except on a merge of the first digit; the responder controller loses
atoms.  Consumer: `bankOrderStepRel`. -/
def BankOrderCellRel {n : Nat} (b a c0 : Nat)
    (sx sy : RenewalBankSite n)
    (M : RenewalBankSite n × RenewalBankSite n) : Prop :=
  (M.1.worker = .empty ∨ M.1.worker = sx.worker ∨
    (M.1.worker = sy.worker ∧ 1 ≤ a ∧ a < b ∧ c0 = a + 1)) ∧
  (M.2.worker = .empty ∨
    (M.2.worker = sy.worker ∧ packNext a c0 b = c0) ∨
    (M.2.worker = sx.worker ∧ M.1.worker = .empty ∧
      1 ≤ a ∧ a < b ∧ c0 = a + 1) ∨
    (a = 0 ∧ c0 = 1 ∧
      bankInheritedControllerAtomCount M.1.controller = 0 ∧
      bankInheritedWorkerAtomCount M.2.worker ≤
        bankInheritedControllerAtomCount sx.controller)) ∧
  (bankInheritedControllerAtomCount M.1.controller ≤
      bankInheritedControllerAtomCount sx.controller ∨
    (a = 0 ∧ c0 = 1 ∧ M.2.worker = .empty ∧
      bankInheritedControllerAtomCount M.1.controller ≤
        bankInheritedControllerAtomCount sx.controller +
          bankInheritedWorkerAtomCount sy.worker)) ∧
  bankInheritedControllerAtomCount M.2.controller ≤
    bankInheritedControllerAtomCount sy.controller

/-- A wait slot never adds atoms to a controller. -/
private theorem bankOrderWaitSlotCount {n : Nat} (m : Mode) (l : Nat)
    (v : RenewalBankController n) :
    bankInheritedControllerAtomCount (renewalBankWaitSlot m l v) ≤
      bankInheritedControllerAtomCount v := by
  unfold renewalBankWaitSlot
  split
  · split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- Root source on its first digit.  Consumer: `bankOrderCellRelHolds`. -/
theorem bankOrderCellRootStep {n : Nat} (b : Nat)
    (wX wY : RenewalBankWorker n) (vX vY : RenewalBankController n)
    (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat) (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (hb : 2 ≤ b)
    (hcx : bankInFlightControllerShape 0 mx vX)
    (hwy : bankInFlightWorkerShape ty wY) :
    BankOrderCellRel b 0 1 ⟨wX, vX⟩ ⟨wY, vY⟩
      (bankCellMemory b ⟨wX, vX⟩ ⟨wY, vY⟩ service e dest
        ⟨0, mx, bitx, tx, lx, gx⟩ ⟨1, my, bity, ty, ly, gy⟩) := by
  have hp : packNext 0 1 b = 1 := by simp [packNext]; omega
  have hw := bankOrderWaitSlotCount (n := n) mx lx vX
  -- The roles are fixed (source 0, responder 1, PACK unchanged): the root normal form
  -- (BankCellMemoryRoot.lean) has the role guards decided, before the mode and token splits.
  rw [bankCellMemory_rootKeep b _ _ service e dest _ _ rfl rfl hb]
  -- A granted root exits at once (controller cleared, responder worker cleared): no shape split.
  cases gx
  · cases mx <;> simp only [bankInFlightControllerShape, ↓reduceIte] at hcx <;>
      cases ty <;> simp only [bankInFlightWorkerShape] at hwy <;>
      (first | subst hcx | obtain ⟨p, rfl⟩ := hcx) <;>
      (first | subst hwy |
        (cases hwy with
          | inl h => obtain ⟨ρ, rfl⟩ := h
          | inr h => obtain ⟨q, rfl⟩ := h) |
        obtain ⟨q, rfl⟩ := hwy) <;>
      simp [BankOrderCellRel, bankMemoryRootKeep, hp, isRetTok,
        renewalBankReturned, renewalBankWorkerPayload, renewalBankWaitingAtoms,
        renewalBankActivePayload, renewalBankHead,
        bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount,
        bankInheritedPayloadAtomCount] <;>
      (repeat' split) <;>
      simp_all [hp, bankInheritedControllerAtomCount,
        bankInheritedWorkerAtomCount, bankInheritedPayloadAtomCount] <;>
      (try subst_vars) <;>
      (try simp_all [List.length_append]) <;>
      omega
  · simp [BankOrderCellRel, bankMemoryRootKeep, hp, bankInheritedControllerAtomCount,
      bankInheritedWorkerAtomCount]

/-- Root source on a changed responder.
Consumer: `bankOrderCellRelHolds`. -/
theorem bankOrderCellRootChanged {n : Nat} (b : Nat)
    (wX wY : RenewalBankWorker n) (vX vY : RenewalBankController n)
    (service : Nat) (e dest : Fin n)
    (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat) (gx : Bool)
    (c0 : Nat) (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat)
    (gy : Bool) (hb : 2 ≤ b) (hc : c0 ≠ 1) :
    BankOrderCellRel b 0 c0 ⟨wX, vX⟩ ⟨wY, vY⟩
      (bankCellMemory b ⟨wX, vX⟩ ⟨wY, vY⟩ service e dest
        ⟨0, mx, bitx, tx, lx, gx⟩ ⟨c0, my, bity, ty, ly, gy⟩) := by
  have hpos : 0 < b := by omega
  have hp : packNext 0 c0 b = 1 := by simp [packNext, hpos]
  have hc' : 1 ≠ c0 := fun h => hc h.symm
  have hone : 1 ≤ b := by omega
  -- The source is a root and the responder's PACK changes: decide the role guards of
  -- `bankCellMemory` once, before the grant, mode and controller splits.
  simp [bankCellMemory, hp, hc, hc', hone]
  cases gx <;> cases mx <;> cases vX <;> by_cases hl : 1 < lx <;>
    simp [BankOrderCellRel, bankCellMemory, hp, hc, hc', hone, hl,
      isWaitMode, renewalBankWaitSlot,
      bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount] <;>
    (repeat' split) <;>
    simp_all [bankInheritedControllerAtomCount,
      bankInheritedWorkerAtomCount]

/-- Nonroot source on a changed responder.
Consumer: `bankOrderCellRelHolds`. -/
theorem bankOrderCellNonrootChanged {n : Nat} (b : Nat)
    (wX wY : RenewalBankWorker n) (vX vY : RenewalBankController n)
    (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (c0 : Nat) (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat)
    (gy : Bool) (ha : a ≠ 0) (hch : packNext a c0 b ≠ c0) :
    BankOrderCellRel b a c0 ⟨wX, vX⟩ ⟨wY, vY⟩
      (bankCellMemory b ⟨wX, vX⟩ ⟨wY, vY⟩ service e dest
        ⟨a, mx, bitx, tx, lx, gx⟩ ⟨c0, my, bity, ty, ly, gy⟩) := by
  rw [bankCellMemory_nonroot _ _ _ _ _ _ _ _ ha]
  cases vY <;>
  simp [BankOrderCellRel, bankMemoryNRW, bankMemoryCtlY, ha, hch,
    bankInheritedControllerAtomCount, bankInheritedWorkerAtomCount] <;>
    (repeat' split) <;>
    simp_all [bankInheritedControllerAtomCount,
      bankInheritedWorkerAtomCount]

/-- Consecutive digits below or at the top.
Consumer: `bankOrderCellRelHolds`. -/
theorem bankOrderCellDigitStep {n : Nat} (b : Nat)
    (wX wY : RenewalBankWorker n) (vX vY : RenewalBankController n)
    (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat) (gy : Bool)
    (ha : 1 ≤ a) (hab : a < b) :
    BankOrderCellRel b a (a + 1) ⟨wX, vX⟩ ⟨wY, vY⟩
      (bankCellMemory b ⟨wX, vX⟩ ⟨wY, vY⟩ service e dest
        ⟨a, mx, bitx, tx, lx, gx⟩ ⟨a + 1, my, bity, ty, ly, gy⟩) := by
  have hp : packNext a (a + 1) b = a + 1 := by simp [packNext, hab]
  have ha0 : a ≠ 0 := by omega
  have hne1 : a ≠ b := by omega
  have hpb : a + 1 ≤ b := by omega
  have hba : ¬ b < a := by omega
  rw [bankCellMemory_nonroot _ _ _ _ _ _ _ _ ha0]
  by_cases htop : a + 1 = b
  · subst htop
    simp [BankOrderCellRel, bankMemoryNRW, bankMemoryCtlY, hp, ha0, ha, hpb,
      bankInheritedControllerAtomCount]
    all_goals (cases tx <;> cases ty <;>
      simp [BankOrderCellRel, bankMemoryNRW, bankMemoryCtlY, hp, ha0, ha, hpb,
        bankInheritedControllerAtomCount])
  · simp [BankOrderCellRel, bankMemoryNRW, bankMemoryCtlY, hp, ha0, ha, hab, hpb, hne1, htop,
      Ne.symm htop, hba, bankInheritedControllerAtomCount]
    all_goals (cases tx <;> cases ty <;>
      simp [BankOrderCellRel, bankMemoryNRW, bankMemoryCtlY, hp, ha0, ha, hab, hpb, hne1,
        htop, Ne.symm htop, hba, bankInheritedControllerAtomCount])

/-- A source at or beyond the top on an unchanged responder.
Consumer: `bankOrderCellRelHolds`. -/
theorem bankOrderCellBeyondKeep {n : Nat} (b : Nat)
    (wX wY : RenewalBankWorker n) (vX vY : RenewalBankController n)
    (service : Nat) (e dest : Fin n)
    (a : Nat) (mx : Mode) (bitx : Bool) (tx : BTok) (lx : Nat)
    (gx : Bool)
    (c0 : Nat) (my : Mode) (bity : Bool) (ty : BTok) (ly : Nat)
    (gy : Bool) (ha : a ≠ 0) (hab : ¬ a < b)
    (hch : packNext a c0 b = c0) :
    BankOrderCellRel b a c0 ⟨wX, vX⟩ ⟨wY, vY⟩
      (bankCellMemory b ⟨wX, vX⟩ ⟨wY, vY⟩ service e dest
        ⟨a, mx, bitx, tx, lx, gx⟩ ⟨c0, my, bity, ty, ly, gy⟩) := by
  have hc : c0 = 0 ∨ c0 = b + 1 := by
    unfold packNext at hch
    rw [if_neg hab] at hch
    split at hch
    · split at hch <;> omega
    · omega
  have hw := bankOrderWaitSlotCount (n := n) my ly vY
  rw [bankCellMemory_nonroot _ _ _ _ _ _ _ _ ha]
  -- the responder controller reads the grant/ARMED guard of `bankMemoryCtlY`
  by_cases hg : gy = true ∨ my = Mode.ARMED
  all_goals
    rcases hc with rfl | rfl
    · rcases Nat.lt_or_ge b a with hba | hba
      · have h1 : ¬ a ≤ b := by omega
        simp [BankOrderCellRel, bankMemoryNRW, bankMemoryCtlY, hg, ha, hch, hab, h1,
          bankInheritedControllerAtomCount] <;>
          (repeat' split) <;> simp_all [bankInheritedControllerAtomCount]
      · have hab2 : a = b := by omega
        subst hab2
        have h1 : 1 ≤ a := by omega
        simp [BankOrderCellRel, bankMemoryNRW, bankMemoryCtlY, hg, ha, hch, h1, Ne.symm ha,
          bankInheritedControllerAtomCount] <;>
          (repeat' split) <;> simp_all [bankInheritedControllerAtomCount]
    · have hab2 : a = b := by
        unfold packNext at hch
        rw [if_neg hab] at hch
        split at hch
        · assumption
        · omega
      subst hab2
      have hne : a + 1 ≠ 0 := by omega
      have hlt : ¬ a + 1 ≤ a := by omega
      have h1 : 1 ≤ a := by omega
      simp [BankOrderCellRel, bankMemoryNRW, bankMemoryCtlY, hg, ha, hch, hne, hlt, h1,
        bankInheritedControllerAtomCount] <;>
        (repeat' split) <;> simp_all [bankInheritedControllerAtomCount]

/-- A zero-atom worker: a pending receipt or an atom-free payload.
Consumer: `BankOrderAbs`. -/
def bankZeroWorker {n : Nat} : RenewalBankWorker n → Prop
  | .empty => False
  | .pending _ => True
  | .payload p => p.atoms = []

/-- A zero-atom worker holds no inherited atom.
Consumer: `bankOrderAbsStep`. -/
theorem bankZeroWorkerAtoms {n : Nat} (w : RenewalBankWorker n)
    (h : bankZeroWorker w) : bankInheritedWorkerAtomCount w = 0 := by
  cases w with
  | empty => exact h.elim
  | pending _ => rfl
  | payload p =>
      simp [bankZeroWorker] at h
      simp [bankInheritedWorkerAtomCount, bankInheritedPayloadAtomCount, h]

/-- The empty worker is not a zero-atom worker.
Consumer: `bankOrderAbsStep`. -/
theorem bankZeroWorkerNotEmpty {n : Nat} (w : RenewalBankWorker n)
    (h : bankZeroWorker w) (he : w = .empty) : False := by
  subst he
  exact h

/-- The order invariant on abstract PACK roles `P`, workers `W` and
controller atom counts `C`.  (I) a zero-atom worker on digit j of the
window anchored at x forces x's controller to hold no atom; (II) it
forces every lower digit worker of the same window to hold no atom.
Consumer: `bankOrderAbsStep`, `BankInheritedOrder`. -/
def BankOrderAbs {n : Nat} (b : Nat) (P : Fin n → Nat)
    (W : Fin n → RenewalBankWorker n) (C : Fin n → Nat) : Prop :=
  (∀ x d : Fin n, ∀ j : Nat, 1 ≤ j → j ≤ b →
    d.val = (x.val + j) % n → P d = j → bankZeroWorker (W d) →
      C x = 0) ∧
  (∀ x u d : Fin n, ∀ i j : Nat, 1 ≤ i → i < j → j ≤ b →
    u.val = (x.val + i) % n → d.val = (x.val + j) % n →
    P u = i → P d = j → bankZeroWorker (W d) →
      bankInheritedWorkerAtomCount (W u) = 0)

/-- One OLD-pair step on the abstract data.
Consumer: `bankOrderAbsStep`. -/
def BankOrderStepRel {n : Nat} (b : Nat) (e e' : Fin n)
    (P : Fin n → Nat) (W : Fin n → RenewalBankWorker n) (C : Fin n → Nat)
    (P' : Fin n → Nat) (W' : Fin n → RenewalBankWorker n)
    (C' : Fin n → Nat) : Prop :=
  (∀ d : Fin n, d ≠ e → d ≠ e' → P' d = P d ∧ W' d = W d ∧ C' d = C d) ∧
  P' e = P e ∧ P' e' = packNext (P e) (P e') b ∧
  (W' e = .empty ∨ W' e = W e ∨
    (W' e = W e' ∧ 1 ≤ P e ∧ P e < b ∧ P e' = P e + 1)) ∧
  (W' e' = .empty ∨
    (W' e' = W e' ∧ packNext (P e) (P e') b = P e') ∨
    (W' e' = W e ∧ W' e = .empty ∧
      1 ≤ P e ∧ P e < b ∧ P e' = P e + 1) ∨
    (P e = 0 ∧ P e' = 1 ∧ C' e = 0 ∧
      bankInheritedWorkerAtomCount (W' e') ≤ C e)) ∧
  (C' e ≤ C e ∨
    (P e = 0 ∧ P e' = 1 ∧ W' e' = .empty ∧
      C' e ≤ C e + bankInheritedWorkerAtomCount (W e'))) ∧
  C' e' ≤ C e'

/-- Linear form of a ring offset.  Consumer: `bankOrderAbsStep`. -/
theorem bankOffsetLin {n : Nat} (x d : Fin n) (j : Nat) (hj : j < n)
    (h : d.val = (x.val + j) % n) :
    d.val = x.val + j ∨ d.val + n = x.val + j := by
  have hx := x.isLt
  by_cases hlt : x.val + j < n
  · left
    rw [Nat.mod_eq_of_lt hlt] at h
    exact h
  · right
    have hge : n ≤ x.val + j := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- A ring offset from its linear form.  Consumer: `bankOrderAbsStep`. -/
theorem bankOffsetOfLin {n : Nat} (x d : Fin n) (j : Nat) (hj : j < n)
    (h : d.val = x.val + j ∨ d.val + n = x.val + j) :
    d.val = (x.val + j) % n := by
  have hd := d.isLt
  rcases h with h | h
  · rw [← h, Nat.mod_eq_of_lt hd]
  · have hge : n ≤ x.val + j := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Below the top digit the next PACK role is the successor role.
Consumer: `bankOrderAbsStep`, `bankOrderCellRelHolds`. -/
theorem bankPackNextDigit (a c b : Nat) (h : a < b) :
    packNext a c b = a + 1 := by
  simp [packNext, h]

/-- `d` sits at offset `j` from `x` on the ring, as a Prop that `omega` does not read: after
`bankOffsetLin` has given the linear form, the `% n` equation only feeds lemma arguments, and
left in the context it makes every `omega` call case-split on the remainder. -/
private def bankOffsetAt {n : Nat} (x d : Fin n) (j : Nat) : Prop := d.val = (x.val + j) % n

/-- One step back along the ring: `e' = e + 1` and `e'` at offset `i` from `x` put `e` at offset
`i - 1`. -/
private theorem bankOffsetAtPred {n : Nat} (x e e' : Fin n) (i : Nat) (hi : 1 ≤ i) (hin : i < n)
    (hn : 1 < n) (he' : bankOffsetAt e e' 1) (hu : bankOffsetAt x e' i) :
    bankOffsetAt x e (i - 1) := by
  have h1 := bankOffsetLin e e' 1 hn he'
  have h2 := bankOffsetLin x e' i hin hu
  have := e.isLt
  have := x.isLt
  have := e'.isLt
  exact bankOffsetOfLin x e (i - 1) (by omega) (by omega)

/-- One step forward along the ring: `e' = e + 1` and `e` at offset `i` from `x` put `e'` at
offset `i + 1`. -/
private theorem bankOffsetAtSucc {n : Nat} (x e e' : Fin n) (i : Nat) (hin : i + 1 < n)
    (hn : 1 < n) (he' : bankOffsetAt e e' 1) (hu : bankOffsetAt x e i) :
    bankOffsetAt x e' (i + 1) := by
  have h1 := bankOffsetLin e e' 1 hn he'
  have h2 := bankOffsetLin x e i (by omega) hu
  have := e.isLt
  have := x.isLt
  have := e'.isLt
  exact bankOffsetOfLin x e' (i + 1) hin (by omega)

/-- `e' = e + 1` and `e' = x + 1` force `x = e`. -/
private theorem bankOffsetAtOneEq {n : Nat} (x e e' : Fin n) (hn : 1 < n)
    (he' : bankOffsetAt e e' 1) (hx : bankOffsetAt x e' 1) : x = e := by
  have h1 := bankOffsetLin e e' 1 hn he'
  have h2 := bankOffsetLin x e' 1 hn hx
  have := e.isLt
  have := x.isLt
  have := e'.isLt
  exact Fin.ext (by omega)

/-- The order invariant survives one OLD-pair step.
Consumer: `bankInheritedOrderStep`. -/
theorem bankOrderAbsStep {n : Nat} (b : Nat) (hnb : b + 2 ≤ n)
    (hb : 1 ≤ b) (e e' : Fin n) (he' : e'.val = (e.val + 1) % n)
    (P : Fin n → Nat) (W : Fin n → RenewalBankWorker n) (C : Fin n → Nat)
    (P' : Fin n → Nat) (W' : Fin n → RenewalBankWorker n)
    (C' : Fin n → Nat)
    (hinv : BankOrderAbs b P W C)
    (hrel : BankOrderStepRel b e e' P W C P' W' C') :
    BankOrderAbs b P' W' C' := by
  obtain ⟨hI, hII⟩ := hinv
  obtain ⟨hF, hPe, hPe', hL1, hL2, hL3, hL4⟩ := hrel
  have he'l := bankOffsetLin e e' 1 (by omega) he'
  replace he' : bankOffsetAt e e' 1 := he'
  have hel := e.isLt
  have he'lt := e'.isLt
  have hp01 : packNext 0 1 b = 1 := bankPackNextDigit 0 1 b (by omega)
  refine ⟨?_, ?_⟩
  · intro x d j hj1 hjb hd hPd hZ
    have hdl := bankOffsetLin x d j (by omega) hd
    replace hd : bankOffsetAt x d j := hd
    have hx := x.isLt
    have hdlt := d.isLt
    by_cases hde : d.val = e.val
    · have hdeq : d = e := Fin.ext hde
      rw [hdeq] at hPd hZ
      rw [hPe] at hPd
      have hxe : x ≠ e := fun h => by
        have := congrArg Fin.val h
        omega
      have hxe' : x ≠ e' := fun h => by
        have := congrArg Fin.val h
        omega
      rw [(hF x hxe hxe').2.2]
      rcases hL1 with h | h | ⟨h, h1, h2, h3⟩
      · exact (bankZeroWorkerNotEmpty _ hZ h).elim
      · rw [h] at hZ
        exact hI x e j hj1 hjb (by rw [← hdeq]; exact hd) hPd hZ
      · rw [h] at hZ
        exact hI x e' (j + 1) (by omega) (by omega)
          (bankOffsetAtSucc x e e' j (by omega) (by omega) he' (by rw [← hdeq]; exact hd))
          (by omega) hZ
    · by_cases hde' : d.val = e'.val
      · have hdeq : d = e' := Fin.ext hde'
        rw [hdeq] at hPd hZ
        rw [hPe'] at hPd
        have hxe' : x ≠ e' := fun h => by
          have := congrArg Fin.val h
          omega
        rcases hL2 with h | ⟨h, hk⟩ | ⟨h, h0, h1, h2, h3⟩ |
            ⟨h1, h2, h3, h4⟩
        · exact (bankZeroWorkerNotEmpty _ hZ h).elim
        · rw [h] at hZ
          have hC : C x = 0 := hI x e' j hj1 hjb
            (by rw [← hdeq]; exact hd) (by omega) hZ
          by_cases hxe : x.val = e.val
          · have hxeq : x = e := Fin.ext hxe
            rw [hxeq] at hC ⊢
            have hz := bankZeroWorkerAtoms _ hZ
            rcases hL3 with h3 | ⟨_, _, _, h3⟩ <;> omega
          · rw [(hF x (fun h => hxe (congrArg Fin.val h)) hxe').2.2]
            exact hC
        · rw [h] at hZ
          rw [bankPackNextDigit _ _ _ h2] at hPd
          have hxe : x ≠ e := fun h => by
            have := congrArg Fin.val h
            omega
          rw [(hF x hxe hxe').2.2]
          exact hI x e (j - 1) (by omega) (by omega)
            (bankOffsetAtPred x e e' j hj1 (by omega) (by omega) he' (by rw [← hdeq]; exact hd))
            (by omega) hZ
        · rw [h1, h2, hp01] at hPd
          have hxe : x = e := bankOffsetAtOneEq x e e' (by omega) he'
            (by have hj : j = 1 := by omega
                subst hj
                rw [← hdeq]
                exact hd)
          rw [hxe]
          exact h3
      · have hfd := hF d (fun h => hde (congrArg Fin.val h))
          (fun h => hde' (congrArg Fin.val h))
        rw [hfd.1] at hPd
        rw [hfd.2.1] at hZ
        have hC : C x = 0 := hI x d j hj1 hjb hd hPd hZ
        by_cases hxe : x.val = e.val
        · have hxeq : x = e := Fin.ext hxe
          rw [hxeq] at hC ⊢
          rcases hL3 with h3 | ⟨h1, h2, _, h3⟩
          · omega
          · have hw : bankInheritedWorkerAtomCount (W e') = 0 :=
              hII e e' d 1 j (by omega)
                (by
                  rcases hdl with h | h <;> rcases he'l with h' | h' <;>
                    omega)
                hjb he' (by rw [← hxeq]; exact hd) h2 hPd hZ
            omega
        · by_cases hxe' : x.val = e'.val
          · have hxeq : x = e' := Fin.ext hxe'
            rw [hxeq] at hC ⊢
            omega
          · rw [(hF x (fun h => hxe (congrArg Fin.val h))
              (fun h => hxe' (congrArg Fin.val h))).2.2]
            exact hC
  · intro x u d i j hi1 hij hjb hu hd hPu hPd hZ
    have hdl := bankOffsetLin x d j (by omega) hd
    have hul := bankOffsetLin x u i (by omega) hu
    replace hd : bankOffsetAt x d j := hd
    replace hu : bankOffsetAt x u i := hu
    have hx := x.isLt
    have hdlt := d.isLt
    have hult := u.isLt
    -- a zero worker of the OLD state at offset j0 of the same window
    have hsrc : ∃ (d0 : Fin n) (j0 : Nat), 1 ≤ j0 ∧ j0 ≤ b ∧
        d0.val = (x.val + j0) % n ∧ P d0 = j0 ∧ bankZeroWorker (W d0) ∧
        (j ≤ j0 ∨ (j0 + 1 = j ∧ d0 = e ∧ d = e' ∧ W' e = .empty)) := by
      by_cases hde : d.val = e.val
      · have hdeq : d = e := Fin.ext hde
        rw [hdeq] at hPd hZ
        rw [hPe] at hPd
        rcases hL1 with h | h | ⟨h, h1, h2, h3⟩
        · exact (bankZeroWorkerNotEmpty _ hZ h).elim
        · rw [h] at hZ
          exact ⟨e, j, by omega, hjb, by rw [← hdeq]; exact hd, hPd, hZ,
            Or.inl (Nat.le_refl j)⟩
        · rw [h] at hZ
          exact ⟨e', j + 1, by omega, by omega,
            bankOffsetAtSucc x e e' j (by omega) (by omega) he' (by rw [← hdeq]; exact hd),
            by omega, hZ, Or.inl (by omega)⟩
      · by_cases hde' : d.val = e'.val
        · have hdeq : d = e' := Fin.ext hde'
          rw [hdeq] at hPd hZ
          rw [hPe'] at hPd
          rcases hL2 with h | ⟨h, hk⟩ | ⟨h, h0, h1, h2, h3⟩ |
              ⟨h1, h2, h3, h4⟩
          · exact (bankZeroWorkerNotEmpty _ hZ h).elim
          · rw [h] at hZ
            exact ⟨e', j, by omega, hjb, by rw [← hdeq]; exact hd,
              by omega, hZ, Or.inl (Nat.le_refl j)⟩
          · rw [h] at hZ
            rw [bankPackNextDigit _ _ _ h2] at hPd
            exact ⟨e, j - 1, by omega, by omega,
              bankOffsetAtPred x e e' j (by omega) (by omega) (by omega) he'
                (by rw [← hdeq]; exact hd),
              by omega, hZ, Or.inr ⟨by omega, rfl, hdeq, h0⟩⟩
          · rw [h1, h2, hp01] at hPd
            omega
        · have hfd := hF d (fun h => hde (congrArg Fin.val h))
            (fun h => hde' (congrArg Fin.val h))
          rw [hfd.1] at hPd
          rw [hfd.2.1] at hZ
          exact ⟨d, j, by omega, hjb, hd, hPd, hZ, Or.inl (Nat.le_refl j)⟩
    obtain ⟨d0, j0, hj01, hj0b, hd0, hPd0, hZ0, hcase⟩ := hsrc
    have hd0l := bankOffsetLin x d0 j0 (by omega) hd0
    replace hd0 : bankOffsetAt x d0 j0 := hd0
    have hd0lt := d0.isLt
    by_cases hue : u.val = e.val
    · have hueq : u = e := Fin.ext hue
      rw [hueq] at hPu ⊢
      rw [hPe] at hPu
      rcases hcase with hle | ⟨_, _, _, hWe⟩
      · rcases hL1 with h | h | ⟨h, h1, h2, h3⟩
        · rw [h]
          rfl
        · rw [h]
          exact hII x e d0 i j0 hi1 (by omega) hj0b
            (by rw [← hueq]; exact hu) hd0 hPu hPd0 hZ0
        · rw [h]
          by_cases hlast : i + 1 = j0
          · have heq : e' = d0 := Fin.ext (by omega)
            rw [heq]
            exact bankZeroWorkerAtoms _ hZ0
          · exact hII x e' d0 (i + 1) j0 (by omega) (by omega) hj0b
              (bankOffsetAtSucc x e e' i (by omega) (by omega) he' (by rw [← hueq]; exact hu))
              hd0 (by omega) hPd0 hZ0
      · rw [hWe]
        rfl
    · by_cases hue' : u.val = e'.val
      · have hueq : u = e' := Fin.ext hue'
        rw [hueq] at hPu ⊢
        rw [hPe'] at hPu
        -- the responder slot is not the zero worker's slot after the step
        have hdne : ¬ (j0 + 1 = j ∧ d0 = e ∧ d = e' ∧ W' e = .empty) := by
          rintro ⟨_, _, hd', _⟩
          have := congrArg Fin.val hd'
          omega
        have hle : j ≤ j0 := by
          rcases hcase with h | h
          · exact h
          · exact (hdne h).elim
        rcases hL2 with h | ⟨h, hk⟩ | ⟨h, h0, h1, h2, h3⟩ |
            ⟨h1, h2, h3, h4⟩
        · rw [h]
          rfl
        · rw [h]
          exact hII x e' d0 i j0 hi1 (by omega) hj0b
            (by rw [← hueq]; exact hu) hd0 (by omega) hPd0 hZ0
        · rw [h]
          rw [bankPackNextDigit _ _ _ h2] at hPu
          exact hII x e d0 (i - 1) j0 (by omega) (by omega) hj0b
            (bankOffsetAtPred x e e' i hi1 (by omega) (by omega) he' (by rw [← hueq]; exact hu))
            hd0 (by omega) hPd0 hZ0
        · rw [h1, h2, hp01] at hPu
          have hxe : x = e := bankOffsetAtOneEq x e e' (by omega) he'
            (by have hi : i = 1 := by omega
                subst hi
                rw [← hueq]
                exact hu)
          have hC : C x = 0 := hI x d0 j0 hj01 hj0b hd0 hPd0 hZ0
          rw [hxe] at hC
          omega
      · have hfu := hF u (fun h => hue (congrArg Fin.val h))
          (fun h => hue' (congrArg Fin.val h))
        rw [hfu.1] at hPu
        rw [hfu.2.1]
        have hlt : i < j0 := by
          rcases hcase with h | ⟨h, hd0e, _, _⟩
          · omega
          · have := congrArg Fin.val hd0e
            have : i ≠ j0 := fun hij0 => by
              subst hij0
              omega
            omega
        exact hII x u d0 i j0 hi1 hlt hj0b hu hd0 hPu hPd0 hZ0

/-- Dispatcher for the order bookkeeping of one OLD pair.
Consumer: `bankOrderStepRelHolds`. -/
theorem bankOrderCellRelHolds {n : Nat} (b : Nat) (hb : 2 ≤ b)
    (sx sy : RenewalBankSite n) (service : Nat) (e dest : Fin n)
    (x0 y0 : BankCell)
    (hcx : bankInFlightControllerShape x0.role x0.mode sx.controller)
    (hwy : bankInFlightWorkerShape y0.tok sy.worker) :
    BankOrderCellRel b x0.role y0.role sx sy
      (bankCellMemory b sx sy service e dest x0 y0) := by
  rcases x0 with ⟨a, mx, bitx, tx, lx, gx⟩
  rcases y0 with ⟨c0, my, bity, ty, ly, gy⟩
  rcases sx with ⟨wX, vX⟩
  rcases sy with ⟨wY, vY⟩
  dsimp only at hcx hwy ⊢
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hc : c0 = 1
    · subst hc
      exact bankOrderCellRootStep b wX wY vX vY service e dest mx bitx tx
        lx gx my bity ty ly gy hb hcx hwy
    · exact bankOrderCellRootChanged b wX wY vX vY service e dest mx bitx
        tx lx gx c0 my bity ty ly gy hb hc
  · by_cases hch : packNext a c0 b = c0
    · by_cases hab : a < b
      · have hc : c0 = a + 1 := by
          rw [bankPackNextDigit a c0 b hab] at hch
          omega
        subst hc
        exact bankOrderCellDigitStep b wX wY vX vY service e dest a mx bitx
          tx lx gx my bity ty ly gy (by omega) hab
      · exact bankOrderCellBeyondKeep b wX wY vX vY service e dest a mx
          bitx tx lx gx c0 my bity ty ly gy ha0 hab hch
    · exact bankOrderCellNonrootChanged b wX wY vX vY service e dest a mx
        bitx tx lx gx c0 my bity ty ly gy ha0 hch

/-- PACK roles of a BANK reference.  Consumer: `BankInheritedOrder`. -/
def bankOrderP {n : Nat} (r : RenewalBankReference n) (i : Fin n) : Nat :=
  (r.1 i).pack.val

/-- Workers of a BANK reference.  Consumer: `BankInheritedOrder`. -/
def bankOrderW {n : Nat} (r : RenewalBankReference n) (i : Fin n) :
    RenewalBankWorker n :=
  (r.2.sites i).worker

/-- Controller atom counts.  Consumer: `BankInheritedOrder`. -/
def bankOrderC {n : Nat} (r : RenewalBankReference n) (i : Fin n) : Nat :=
  bankInheritedControllerAtomCount (r.2.sites i).controller

/-- The order invariant on a BANK reference.
Consumer: `bankInheritedNoStall`. -/
def BankInheritedOrder {n : Nat} (r : RenewalBankReference n) : Prop :=
  BankOrderAbs (compileAdvice (ceilLogTwo n)).b
    (bankOrderP r) (bankOrderW r) (bankOrderC r)

/-- The literal reference step realizes the abstract step relation.
Consumer: `bankInheritedOrderRun`. -/
theorem bankOrderStepRelHolds {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (r : RenewalBankReference n) (e : Fin n)
    (hal : BankInFlightAligned ring r) :
    BankOrderStepRel (compileAdvice (ceilLogTwo n)).b e
      (ring.rightNeighbor e)
      (bankOrderP r) (bankOrderW r) (bankOrderC r)
      (bankOrderP (rbRun ring r [e])) (bankOrderW (rbRun ring r [e]))
      (bankOrderC (rbRun ring r [e])) := by
  have htwo : 2 ≤ n := by omega
  have hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b := by
    unfold Compiled.b
    omega
  have hpair := rbReferenceSelectedPairFrame ring htwo r e
  have hpack := rbBankReferencePairPack ring htwo r e
  have hcell : BankOrderCellRel (compileAdvice (ceilLogTwo n)).b
      (r.1 e).pack.val (r.1 (ring.rightNeighbor e)).pack.val
      (r.2.sites e) (r.2.sites (ring.rightNeighbor e))
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))) :=
    bankOrderCellRelHolds _ hb _ _ r.2.service e (ring.rightNeighbor e)
      (bankCell (r.1 e) (r.1 e).pack.val)
      (bankCell (r.1 (ring.rightNeighbor e))
        (r.1 (ring.rightNeighbor e)).pack.val)
      (hal e).1 (hal (ring.rightNeighbor e)).2
  obtain ⟨h1, h2, h3, h4⟩ := hcell
  refine ⟨?_, hpack.1, hpack.2, ?_, ?_, ?_, ?_⟩
  · intro d hd hd'
    have hf := rbReferenceOutsideSiteFrame ring r e d hd hd'
    simp [bankOrderP, bankOrderW, bankOrderC, hf.1, hf.2]
  · simp only [bankOrderP, bankOrderW, hpair.2.2.1]
    exact h1
  · simp only [bankOrderP, bankOrderW, bankOrderC, hpair.2.2.1,
      hpair.2.2.2]
    exact h2
  · simp only [bankOrderP, bankOrderW, bankOrderC, hpair.2.2.1,
      hpair.2.2.2]
    exact h3
  · simp only [bankOrderC, hpair.2.2.2]
    exact h4

/-- The BANK band leaves room for a whole digit window.
Consumer: `bankInheritedOrderRun`. -/
theorem bankOrderRingRoom {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (compileAdvice (ceilLogTwo n)).b + 2 ≤ n := by
  have h := Counter.resetColdLargeAtSpatialCutoff n hbank
  have hc : (compileAdvice (ceilLogTwo n)).bankLeaseCap =
      13 * ((compileAdvice (ceilLogTwo n)).b + 2) := rfl
  omega

/-- The order invariant along every aligned run.
Consumer: `bankInheritedOrderWord`. -/
theorem bankInheritedOrderRun {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (pre : List (Fin n)) (r : RenewalBankReference n),
      (∀ k : Nat, BankInFlightAligned ring (rbRun ring r (pre.take k))) →
      BankInheritedOrder r → BankInheritedOrder (rbRun ring r pre) := by
  intro pre
  induction pre with
  | nil => intro r _ h0; exact h0
  | cons e tail ih =>
      intro r hal h0
      have hal0 : BankInFlightAligned ring r := hal 0
      have hb : 1 ≤ (compileAdvice (ceilLogTwo n)).b := by
        unfold Compiled.b
        omega
      have h1 : BankInheritedOrder (rbRun ring r [e]) :=
        bankOrderAbsStep _ (bankOrderRingRoom hbank) hb e
          (ring.rightNeighbor e) rfl _ _ _ _ _ _ h0
          (bankOrderStepRelHolds ring hn r e hal0)
      exact ih (renewalBankNext ring r e) (fun k => hal (k + 1)) h1

/-- The order invariant holds at the start: no worker is atom-free.
Consumer: `bankInheritedOrderWord`. -/
theorem bankInheritedOrderStart {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) :
    BankInheritedOrder (renewalBankStart ring seed) := by
  have hnz : ∀ i : Fin n,
      ¬ bankZeroWorker (bankOrderW (renewalBankStart ring seed) i) := by
    intro i h
    simp only [bankOrderW, renewalBankStart, renewalBankInitialMemory,
      renewalBankInitialSite] at h
    split at h
    · exact h
    · simp [bankZeroWorker, renewalBankEntrancePayload] at h
  exact ⟨fun _ d _ _ _ _ _ hZ => (hnz d hZ).elim,
    fun _ _ d _ _ _ _ _ _ _ _ _ hZ => (hnz d hZ).elim⟩

/-- The order invariant at every BANK word from a rooted seed.
Consumer: `bankInheritedOrderReachable`. -/
theorem bankInheritedOrderWord {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (pre : List (Fin n)) :
    BankInheritedOrder (rbRun ring (renewalBankStart ring seed) pre) :=
  bankInheritedOrderRun ring hn hbank pre (renewalBankStart ring seed)
    (fun k => bankInFlightAlignedWord ring hn seed hbank (pre.take k))
    (bankInheritedOrderStart ring seed)

/-- The order invariant at every reachable BANK reference state.
Consumer: `bankInheritedProgressAlternativeHolds`. -/
theorem bankInheritedOrderReachable {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z) :
    BankInheritedOrder z.val := by
  obtain ⟨_, seed, pre, hrep⟩ := hz
  rw [hrep]
  exact bankInheritedOrderWord ring hn seed hbank pre

/-- The stall is unreachable: a root holding inherited atoms
never faces an atom-free return token on its first digit.
Consumer: `bankInheritedProgressAlternativeHolds`. -/
theorem bankInheritedNoStall {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (hord : BankInheritedOrder r)
    (hal : BankInFlightAligned ring r) (x : Fin n)
    (hb : 1 ≤ (compileAdvice (ceilLogTwo n)).b)
    (hP1 : (r.1 (ring.rightNeighbor x)).pack.val = 1)
    (hret : isRetTok (r.1 (ring.rightNeighbor x)).tok = true)
    (hC : 0 < bankInheritedControllerAtomCount (r.2.sites x).controller) :
    ∃ q : RenewalBankPayload n,
      (r.2.sites (ring.rightNeighbor x)).worker = .payload q ∧
        1 ≤ q.atoms.length := by
  have hzero : ¬ bankZeroWorker (r.2.sites (ring.rightNeighbor x)).worker :=
    fun hZ => by
      have h := hord.1 x (ring.rightNeighbor x) 1 (Nat.le_refl 1) hb rfl
        hP1 hZ
      unfold bankOrderC at h
      omega
  have hw := (hal (ring.rightNeighbor x)).2
  revert hzero hw hret
  generalize (r.2.sites (ring.rightNeighbor x)).worker = w
  generalize (r.1 (ring.rightNeighbor x)).tok = t
  intro hret hzero hw
  cases w with
  | empty =>
      cases t <;> simp [bankInFlightWorkerShape, isRetTok] at hw hret
  | pending ρ => exact (hzero trivial).elim
  | payload q =>
      refine ⟨q, rfl, ?_⟩
      cases hq : q.atoms with
      | nil => exact (hzero (by simp [bankZeroWorker, hq])).elim
      | cons _ _ => simp

/-! ## Part D: the progress alternative -/

/-- A left fold of zeros returns its accumulator.
Consumer: `bankInheritedPositiveSite`. -/
theorem bankFoldlSumZero (l : List Nat) (acc : Nat)
    (h : ∀ a ∈ l, a = 0) :
    l.foldl (fun t a => t + a) acc = acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a tail ih =>
      have ha := h a (List.mem_cons_self ..)
      simp only [List.foldl]
      rw [ha, Nat.add_zero]
      exact ih acc (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A nonzero inherited atom count has a site holding atoms.
Consumer: `bankInheritedProgressAlternativeHolds`. -/
theorem bankInheritedPositiveSite {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (h : bankInheritedStateAtomCount ring hbank z ≠ 0) :
    ∃ i : Fin n, bankInheritedSiteAtomCount (z.val.2.sites i) ≠ 0 := by
  apply Classical.byContradiction
  intro hno
  apply h
  unfold bankInheritedStateAtomCount
  apply bankFoldlSumZero
  intro a ha
  rw [List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  exact Classical.byContradiction (fun hne => hno ⟨i, hne⟩)

/-- The right neighbour of the left neighbour.
Consumer: `bankInheritedEdgeCellPred`. -/
theorem bankLeftRight {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · rw [h0]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt hi]

/-- The ARMED indicator of a reference site, in cell form.
Consumer: the edge helpers below. -/
theorem bankInheritedArmedCell {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (i : Fin n)
    (h : bankInheritedArmedAtoms ring hbank z i = 0) :
    bankCellArmed (bankCell (z.val.1 i) (z.val.1 i).pack.val)
      (z.val.2.sites i) = 0 := h

/-- An edge cell whose responder is site i, at the predecessor edge.
Consumer: `bankInheritedEdgeWaiting`, `bankInheritedEdgePred`. -/
theorem bankInheritedEdgeCellPred {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (i : Fin n)
    (h : BankCellStrictGoal (compileAdvice (ceilLogTwo n)).b
      (z.val.1 (ring.rightNeighbor i)).pack.val
      (compileAdvice (ceilLogTwo n)).theta z.val.2.service
      (ring.leftNeighbor i) i
      (bankCell (z.val.1 (ring.leftNeighbor i))
        (z.val.1 (ring.leftNeighbor i)).pack.val)
      (bankCell (z.val.1 i) (z.val.1 i).pack.val)
      (z.val.2.sites (ring.leftNeighbor i)) (z.val.2.sites i)) :
    BankInheritedEdgeCell ring hbank z (ring.leftNeighbor i) := by
  unfold BankInheritedEdgeCell
  rw [bankLeftRight ring i]
  exact h

/-- P1 at the predecessor edge.
Consumer: `bankInheritedProgressAlternativeHolds`. -/
theorem bankInheritedEdgeWaiting {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hal : BankInFlightAligned ring z.val)
    (harm0 : ∀ r : Fin n, bankInheritedArmedAtoms ring hbank z r = 0)
    (hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b) (i : Fin n)
    (hP : (z.val.1 i).pack.val = 0)
    (hmy : isWaitMode (z.val.1 i).mode = true)
    (l : List (RenewalBankAtom n))
    (hl : (z.val.2.sites i).controller = .waiting l)
    (hc : 1 ≤ l.length) :
    BankInheritedEdgeCell ring hbank z (ring.leftNeighbor i) :=
  bankInheritedEdgeCellPred ring hbank z i
    (bankCellStrictWaitingY (compileAdvice (ceilLogTwo n)).b
      (z.val.1 (ring.rightNeighbor i)).pack.val
      (compileAdvice (ceilLogTwo n)).theta z.val.2.service
      (ring.leftNeighbor i) i
      (bankCell (z.val.1 (ring.leftNeighbor i))
        (z.val.1 (ring.leftNeighbor i)).pack.val)
      (bankCell (z.val.1 i) (z.val.1 i).pack.val)
      (z.val.2.sites (ring.leftNeighbor i)) (z.val.2.sites i) l hb
      (hal (ring.leftNeighbor i)).1 (hal i).2
      (bankInheritedArmedCell ring hbank z _ (harm0 _)) hP hl hc hmy)

/-- P4 and P6 at the predecessor edge.
Consumer: `bankInheritedProgressAlternativeHolds`. -/
theorem bankInheritedEdgePred {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hal : BankInFlightAligned ring z.val)
    (harm0 : ∀ r : Fin n, bankInheritedArmedAtoms ring hbank z r = 0)
    (hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b) (i : Fin n)
    (q : RenewalBankPayload n)
    (hy1 : 1 ≤ (z.val.1 i).pack.val)
    (hyb : (z.val.1 i).pack.val ≤ (compileAdvice (ceilLogTwo n)).b)
    (hq : (z.val.2.sites i).worker = .payload q)
    (hql : 1 ≤ q.atoms.length) (hty : (z.val.1 i).tok ≠ .E)
    (hret : isRetTok (z.val.1 i).tok = true ∨
      (z.val.1 i).pack.val = (compileAdvice (ceilLogTwo n)).b) :
    BankInheritedEdgeCell ring hbank z (ring.leftNeighbor i) :=
  bankInheritedEdgeCellPred ring hbank z i
    (bankCellStrictPredY (compileAdvice (ceilLogTwo n)).b
      (z.val.1 (ring.rightNeighbor i)).pack.val
      (compileAdvice (ceilLogTwo n)).theta z.val.2.service
      (ring.leftNeighbor i) i
      (bankCell (z.val.1 (ring.leftNeighbor i))
        (z.val.1 (ring.leftNeighbor i)).pack.val)
      (bankCell (z.val.1 i) (z.val.1 i).pack.val)
      (z.val.2.sites (ring.leftNeighbor i)) (z.val.2.sites i) q hb
      (hal (ring.leftNeighbor i)).1 (hal i).2
      (bankInheritedArmedCell ring hbank z _ (harm0 _))
      hy1 hyb hq hql hty hret)

/-- P2 at the outgoing edge.
Consumer: `bankInheritedProgressAlternativeHolds`. -/
theorem bankInheritedEdgeCStart {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b) (i : Fin n)
    (hP : (z.val.1 i).pack.val = 0) (hmode : (z.val.1 i).mode = .CSTART)
    (p : RenewalBankPayload n)
    (hp : (z.val.2.sites i).controller = .active p)
    (hp1 : 1 ≤ p.atoms.length)
    (hstall : (z.val.1 (ring.rightNeighbor i)).pack.val = 1 →
      isRetTok (z.val.1 (ring.rightNeighbor i)).tok = true →
      ∃ q : RenewalBankPayload n,
        (z.val.2.sites (ring.rightNeighbor i)).worker = .payload q ∧
          1 ≤ q.atoms.length) :
    BankInheritedEdgeCell ring hbank z i :=
  bankCellStrictCStartX (compileAdvice (ceilLogTwo n)).b
    (z.val.1 (ring.rightNeighbor (ring.rightNeighbor i))).pack.val
    (compileAdvice (ceilLogTwo n)).theta z.val.2.service
    i (ring.rightNeighbor i)
    (bankCell (z.val.1 i) (z.val.1 i).pack.val)
    (bankCell (z.val.1 (ring.rightNeighbor i))
      (z.val.1 (ring.rightNeighbor i)).pack.val)
    (z.val.2.sites i) (z.val.2.sites (ring.rightNeighbor i)) p hb hP hmode
    hp hp1 hstall

/-- P3 at the outgoing edge.
Consumer: `bankInheritedProgressAlternativeHolds`. -/
theorem bankInheritedEdgeOutside {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hal : BankInFlightAligned ring z.val)
    (harm0 : ∀ r : Fin n, bankInheritedArmedAtoms ring hbank z r = 0)
    (hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b) (i : Fin n)
    (q : RenewalBankPayload n)
    (hout : ¬ (1 ≤ (z.val.1 i).pack.val ∧
      (z.val.1 i).pack.val ≤ (compileAdvice (ceilLogTwo n)).b))
    (hq : (z.val.2.sites i).worker = .payload q)
    (hql : 1 ≤ q.atoms.length) (htx : (z.val.1 i).tok ≠ .E) :
    BankInheritedEdgeCell ring hbank z i :=
  bankCellStrictOutsideX (compileAdvice (ceilLogTwo n)).b
    (z.val.1 (ring.rightNeighbor (ring.rightNeighbor i))).pack.val
    (compileAdvice (ceilLogTwo n)).theta z.val.2.service
    i (ring.rightNeighbor i)
    (bankCell (z.val.1 i) (z.val.1 i).pack.val)
    (bankCell (z.val.1 (ring.rightNeighbor i))
      (z.val.1 (ring.rightNeighbor i)).pack.val)
    (z.val.2.sites i) (z.val.2.sites (ring.rightNeighbor i)) q hb
    (hal i).1 (hal (ring.rightNeighbor i)).2
    (bankInheritedArmedCell ring hbank z _ (harm0 _)) hout hq hql htx

/-- P5 at the outgoing edge.
Consumer: `bankInheritedProgressAlternativeHolds`. -/
theorem bankInheritedEdgeUp {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (i : Fin n)
    (q : RenewalBankPayload n)
    (ha : 1 ≤ (z.val.1 i).pack.val)
    (hab : (z.val.1 i).pack.val < (compileAdvice (ceilLogTwo n)).b)
    (hq : (z.val.2.sites i).worker = .payload q)
    (hql : 1 ≤ q.atoms.length)
    (hup : (z.val.1 i).tok = .RR ∨ (z.val.1 i).tok = .IR ∨
      (z.val.1 i).tok = .CR0 ∨ (z.val.1 i).tok = .CR1) :
    BankInheritedEdgeCell ring hbank z i :=
  bankCellStrictUpX (compileAdvice (ceilLogTwo n)).b
    (z.val.1 (ring.rightNeighbor (ring.rightNeighbor i))).pack.val
    (compileAdvice (ceilLogTwo n)).theta z.val.2.service
    i (ring.rightNeighbor i)
    (bankCell (z.val.1 i) (z.val.1 i).pack.val)
    (bankCell (z.val.1 (ring.rightNeighbor i))
      (z.val.1 (ring.rightNeighbor i)).pack.val)
    (z.val.2.sites i) (z.val.2.sites (ring.rightNeighbor i)) q ha hab hq hql
    hup

/-- R7 (C): on every reachable BANK state with inherited atoms,
either an inherited ARMED root exists or some edge drops the literal
potential by n.  Consumer: `bankInheritedRetirementStageHolds`. -/
theorem bankInheritedProgressAlternativeHolds
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankInheritedProgressAlternative ring hbank := by
  intro z hz hatoms
  by_cases harm : ∃ r : Fin n, 0 < bankInheritedArmedAtoms ring hbank z r
  · exact Or.inr harm
  left
  have harm0 : ∀ r : Fin n, bankInheritedArmedAtoms ring hbank z r = 0 :=
    fun r => Classical.byContradiction (fun h => harm ⟨r, by omega⟩)
  have hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b := by
    unfold Compiled.b
    omega
  have hal := bankInheritedReachableInFlightAligned ring hn hbank z hz
  have hord := bankInheritedOrderReachable ring hn hbank z hz
  obtain ⟨i, hi⟩ := bankInheritedPositiveSite ring hbank z hatoms
  suffices hcell : ∃ e : Fin n, BankInheritedEdgeCell ring hbank z e by
    obtain ⟨e, he⟩ := hcell
    exact ⟨e, bankInheritedStrictEdgeOfCell ring hn hbank z e he⟩
  unfold bankInheritedSiteAtomCount at hi
  by_cases hw : bankInheritedWorkerAtomCount (z.val.2.sites i).worker = 0
  · -- a controller holds the atoms
    have hc : 0 < bankInheritedControllerAtomCount
        (z.val.2.sites i).controller := by omega
    have hshape := (hal i).1
    by_cases hP : (z.val.1 i).pack.val = 0
    · unfold bankInFlightControllerShape at hshape
      rw [if_pos hP] at hshape
      have hwait : ∀ l : List (RenewalBankAtom n),
          isWaitMode (z.val.1 i).mode = true →
          (z.val.2.sites i).controller = .waiting l →
          ∃ e : Fin n, BankInheritedEdgeCell ring hbank z e := by
        intro l hm hl
        rw [hl] at hc
        exact ⟨ring.leftNeighbor i, bankInheritedEdgeWaiting ring hbank z hal
          harm0 hb i hP hm l hl (by
            simp only [bankInheritedControllerAtomCount] at hc
            omega)⟩
      revert hshape
      cases hmode : (z.val.1 i).mode with
      | RESET =>
          intro hshape
          rw [hshape] at hc
          exact absurd hc (by simp [bankInheritedControllerAtomCount])
      | RWAIT =>
          intro hshape
          obtain ⟨l, hl⟩ := hshape
          exact hwait l (by rw [hmode]; rfl) hl
      | IWAIT =>
          intro hshape
          obtain ⟨l, hl⟩ := hshape
          exact hwait l (by rw [hmode]; rfl) hl
      | CWAIT =>
          intro hshape
          obtain ⟨l, hl⟩ := hshape
          exact hwait l (by rw [hmode]; rfl) hl
      | ARMED =>
          intro _
          have h := harm0 i
          unfold bankInheritedArmedAtoms at h
          rw [if_pos ⟨hP, hmode⟩] at h
          omega
      | CSTART =>
          intro hshape
          obtain ⟨p, hp⟩ := hshape
          have hp1 : 1 ≤ p.atoms.length := by
            rw [hp] at hc
            simp only [bankInheritedControllerAtomCount,
              bankInheritedPayloadAtomCount] at hc
            omega
          exact ⟨i, bankInheritedEdgeCStart ring hbank z hb i hP hmode p hp
            hp1 (fun h1 hret =>
              bankInheritedNoStall ring z.val hord hal i (by omega) h1
                hret hc)⟩
    · have hempty : (z.val.2.sites i).controller = .empty := by
        unfold bankInFlightControllerShape at hshape
        rw [if_neg hP] at hshape
        exact hshape
      rw [hempty] at hc
      exact absurd hc (by simp [bankInheritedControllerAtomCount])
  · -- a worker holds the atoms
    have hshape := (hal i).2
    obtain ⟨q, hq, hql⟩ : ∃ q : RenewalBankPayload n,
        (z.val.2.sites i).worker = .payload q ∧ 1 ≤ q.atoms.length := by
      cases hwq : (z.val.2.sites i).worker with
      | empty => rw [hwq] at hw; exact absurd rfl hw
      | pending _ => rw [hwq] at hw; exact absurd rfl hw
      | payload q =>
          rw [hwq] at hw
          refine ⟨q, rfl, ?_⟩
          simp only [bankInheritedWorkerAtomCount,
            bankInheritedPayloadAtomCount] at hw
          omega
    have htok : (z.val.1 i).tok ≠ .E := by
      intro hE
      rw [hE, hq] at hshape
      exact absurd hshape (by simp [bankInFlightWorkerShape])
    by_cases hin : 1 ≤ (z.val.1 i).pack.val ∧
        (z.val.1 i).pack.val ≤ (compileAdvice (ceilLogTwo n)).b
    · by_cases hpred : isRetTok (z.val.1 i).tok = true ∨
          (z.val.1 i).pack.val = (compileAdvice (ceilLogTwo n)).b
      · exact ⟨ring.leftNeighbor i, bankInheritedEdgePred ring hbank z hal
          harm0 hb i q hin.1 hin.2 hq hql htok hpred⟩
      · have hlt : (z.val.1 i).pack.val <
            (compileAdvice (ceilLogTwo n)).b := by
          have : (z.val.1 i).pack.val ≠ (compileAdvice (ceilLogTwo n)).b :=
            fun h => hpred (Or.inr h)
          omega
        have hnr : isRetTok (z.val.1 i).tok ≠ true :=
          fun h => hpred (Or.inl h)
        have hup : (z.val.1 i).tok = .RR ∨ (z.val.1 i).tok = .IR ∨
            (z.val.1 i).tok = .CR0 ∨ (z.val.1 i).tok = .CR1 := by
          revert htok hnr
          cases (z.val.1 i).tok <;> simp [isRetTok]
        exact ⟨i, bankInheritedEdgeUp ring hbank z i q hin.1 hlt hq hql hup⟩
    · exact ⟨i, bankInheritedEdgeOutside ring hbank z hal harm0 hb i q hin
        hq hql htok⟩

/-- R7's retirement stage, now unconditional on the BANK band.
Consumer: the BANK clean branch of the L3 headline. -/
theorem bankInheritedRetirementStageHolds
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    StageInheritedAuthorityExtinction
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankInheritedRootedStart ring hbank)
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n) :=
  bankInheritedRetirementStageOfProgress ring hn hbank
    (bankInheritedProgressAlternativeHolds ring hn hbank)
end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankCellAtomFreeShape
#print axioms L3.RenewalReferenceClock.bankCellAtomFreeUnits
#print axioms L3.RenewalReferenceClock.bankCellMemoryChangedIrrelevant
#print axioms L3.RenewalReferenceClock.bankCellMemoryOutsideIrrelevant
#print axioms L3.RenewalReferenceClock.bankCellStrictChanged
#print axioms L3.RenewalReferenceClock.bankCellStrictOutside
#print axioms L3.RenewalReferenceClock.bankCellWaitingTickStrict
#print axioms L3.RenewalReferenceClock.bankCellWaitingPos
#print axioms L3.RenewalReferenceClock.bankCellStrictTopZeroY
#print axioms L3.RenewalReferenceClock.bankCellStrictBeyondZeroY
#print axioms L3.RenewalReferenceClock.bankCellStrictWaitingY
#print axioms L3.RenewalReferenceClock.bankCellUnitsPos
#print axioms L3.RenewalReferenceClock.bankCellUnitsStrict
#print axioms L3.RenewalReferenceClock.bankCellComparisonPos
#print axioms L3.RenewalReferenceClock.bankCellArmedPos
#print axioms L3.RenewalReferenceClock.bankCellPriceRootIssueStrict
#print axioms L3.RenewalReferenceClock.bankCellWorkerPricePos
#print axioms L3.RenewalReferenceClock.bankCellStrictRootClearX
#print axioms L3.RenewalReferenceClock.bankCellStrictRootCStartX
#print axioms L3.RenewalReferenceClock.bankCellStrictCStartX
#print axioms L3.RenewalReferenceClock.bankCellPriceRootReturnStrict
#print axioms L3.RenewalReferenceClock.bankCellPriceRetBackStrict
#print axioms L3.RenewalReferenceClock.bankCellStrictRootGrantY
#print axioms L3.RenewalReferenceClock.bankCellStrictRootWaitY
#print axioms L3.RenewalReferenceClock.bankCellStrictRootActiveY
#print axioms L3.RenewalReferenceClock.bankCellStrictInteriorY
#print axioms L3.RenewalReferenceClock.bankCellPriceTopTurnStrict
#print axioms L3.RenewalReferenceClock.bankCellStrictTopY
#print axioms L3.RenewalReferenceClock.bankCellPriceRRCreditStrict
#print axioms L3.RenewalReferenceClock.bankCellPriceFwdStepStrict
#print axioms L3.RenewalReferenceClock.bankCellPriceIRToALStrict
#print axioms L3.RenewalReferenceClock.bankCellFwdUnitsStrict
#print axioms L3.RenewalReferenceClock.bankCellStrictInteriorChangedX
#print axioms L3.RenewalReferenceClock.bankCellStrictInteriorStepX
#print axioms L3.RenewalReferenceClock.bankCellStrictTopStepX
#print axioms L3.RenewalReferenceClock.bankCellStrictOutsideX
#print axioms L3.RenewalReferenceClock.bankCellStrictUpX
#print axioms L3.RenewalReferenceClock.bankCellStrictPredY
#print axioms L3.RenewalReferenceClock.bankInheritedCellStrictCore
#print axioms L3.RenewalReferenceClock.bankInheritedStrictEdgeOfCell
#print axioms L3.RenewalReferenceClock.bankOrderCellRootStep
#print axioms L3.RenewalReferenceClock.bankOrderCellRootChanged
#print axioms L3.RenewalReferenceClock.bankOrderCellNonrootChanged
#print axioms L3.RenewalReferenceClock.bankOrderCellDigitStep
#print axioms L3.RenewalReferenceClock.bankOrderCellBeyondKeep
#print axioms L3.RenewalReferenceClock.bankZeroWorkerAtoms
#print axioms L3.RenewalReferenceClock.bankZeroWorkerNotEmpty
#print axioms L3.RenewalReferenceClock.bankOffsetLin
#print axioms L3.RenewalReferenceClock.bankOffsetOfLin
#print axioms L3.RenewalReferenceClock.bankPackNextDigit
#print axioms L3.RenewalReferenceClock.bankOrderAbsStep
#print axioms L3.RenewalReferenceClock.bankOrderCellRelHolds
#print axioms L3.RenewalReferenceClock.bankOrderStepRelHolds
#print axioms L3.RenewalReferenceClock.bankOrderRingRoom
#print axioms L3.RenewalReferenceClock.bankInheritedOrderRun
#print axioms L3.RenewalReferenceClock.bankInheritedOrderStart
#print axioms L3.RenewalReferenceClock.bankInheritedOrderWord
#print axioms L3.RenewalReferenceClock.bankInheritedOrderReachable
#print axioms L3.RenewalReferenceClock.bankInheritedNoStall
#print axioms L3.RenewalReferenceClock.bankFoldlSumZero
#print axioms L3.RenewalReferenceClock.bankInheritedPositiveSite
#print axioms L3.RenewalReferenceClock.bankLeftRight
#print axioms L3.RenewalReferenceClock.bankInheritedArmedCell
#print axioms L3.RenewalReferenceClock.bankInheritedEdgeCellPred
#print axioms L3.RenewalReferenceClock.bankInheritedEdgeWaiting
#print axioms L3.RenewalReferenceClock.bankInheritedEdgePred
#print axioms L3.RenewalReferenceClock.bankInheritedEdgeCStart
#print axioms L3.RenewalReferenceClock.bankInheritedEdgeOutside
#print axioms L3.RenewalReferenceClock.bankInheritedEdgeUp
#print axioms L3.RenewalReferenceClock.bankInheritedProgressAlternativeHolds
#print axioms L3.RenewalReferenceClock.bankInheritedRetirementStageHolds

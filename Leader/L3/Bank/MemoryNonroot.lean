import Leader.L3.Headline.Renewal
import Leader.L3.Bank.PairNonroot

/-!
# The BANK ghost memory on a nonroot source

The ghost observer `renewalBankPairMemory` (HeadlineRenewal.lean) follows `bankPair` statement by
statement. As for `bankPair_nonroot` (BankPairNonroot.lean): on a nonroot source its root rows never
run, the source controller ends empty, the responder controller depends only on the PACK change
and the responder's own mode, lease and grant (`bankMemoryCtlY`), and the two workers follow the
token rows (`bankMemoryNRW`, the worker writes verbatim). `renewalBankPairMemory_nonroot` states
this once, at variables; consumers rewrite with it and unfold only the part their statement reads.
The same two definitions describe the record transcription `bankCellMemory`
(BankInheritedCellRows.lean), whose nonroot form is proved where it is used.
-/

namespace L3.HeadlineRenewal

/-- Worker rows of the BANK ghost memory on a nonroot source: the worker writes of
`renewalBankPairMemory` / `bankCellMemory`, in order, without the controller writes. -/
def bankMemoryNRW {n : Nat} (b : Nat) (wx0 wy0 : RenewalBankWorker n)
    (bx cy : BankCell) : RenewalBankWorker n × RenewalBankWorker n := Id.run do
  let postRole := packNext bx.role cy.role b
  let changed := postRole != cy.role
  let mut wx := wx0
  let mut wy := wy0
  if changed then
    wy := .empty
  if !(1 ≤ bx.role && bx.role ≤ b) then
    wx := .empty
  if !(1 ≤ postRole && postRole ≤ b) then
    wy := .empty
  if changed then
    if 1 ≤ bx.role && bx.role < b &&
        (bx.tok == .IR || bx.tok == .CR0 || bx.tok == .CR1) then
      wx := .empty
    return (wx, wy)
  if bx.role == b && bx.tok == .IR then
    wx := .empty
  if postRole == b && cy.tok == .IR then
    wy := .empty
  if 1 ≤ bx.role && bx.role < b && postRole == bx.role + 1 then
    if bx.tok == .RR then
      return (.empty, wx)
    if postRole == b && cy.tok == .RR then
      return (wy, .empty)
    if cy.tok == .RL then
      return (wy, .empty)
    if bx.tok != .E &&
        (if postRole == b && cy.tok == .IR then false
         else cy.tok != .E) then
      return (.empty, .empty)
    if postRole == b && (cy.tok == .CR0 || cy.tok == .CR1) then
      return (wy, .empty)
    if cy.tok == .AL || cy.tok == .CL0 || cy.tok == .CL1 then
      return (wy, .empty)
    if bx.tok == .IR then
      return (.empty, wx)
    if bx.tok == .CR0 || bx.tok == .CR1 then
      return (.empty, wx)
  return (wx, wy)

/-- Responder controller of the BANK ghost memory on a nonroot source. -/
def bankMemoryCtlY {n : Nat} (b : Nat) (c0 : RenewalBankController n)
    (bx cy : BankCell) : RenewalBankController n :=
  if packNext bx.role cy.role b = cy.role ∧ packNext bx.role cy.role b = 0 then
    if cy.grant = true ∨ cy.mode = .ARMED then .empty
    else renewalBankWaitSlot cy.mode cy.lease c0
  else .empty

theorem renewalBankPairMemory_nonroot_workers {n : Nat} (c : Compiled)
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c) (hx : x.pack.val ≠ 0) :
    (renewalBankPairMemory c m e dest x y).1.worker =
        (bankMemoryNRW c.b (m.sites e).worker (m.sites dest).worker
          (bankCell x x.pack.val) (bankCell y y.pack.val)).1 ∧
      (renewalBankPairMemory c m e dest x y).2.worker =
        (bankMemoryNRW c.b (m.sites e).worker (m.sites dest).worker
          (bankCell x x.pack.val) (bankCell y y.pack.val)).2 := by
  -- Name the two cells and read the PACK values through them: the goal is then the record
  -- transcription `bankCellMemory` at variables.
  unfold renewalBankPairMemory
  generalize hbx : bankCell x x.pack.val = bx
  generalize hcy : bankCell y y.pack.val = cy
  have hr : x.pack.val = bx.role := by subst hbx; rfl
  have hs : y.pack.val = cy.role := by subst hcy; rfl
  rw [hr] at hx ⊢
  rw [hs]
  have hx' : (bx.role != 0) = true := by simp [hx]
  have hx'' : (bx.role == 0) = false := by simp [hx]
  simp [bankMemoryNRW, hx, hx', hx'', apply_ite Id.run,
    apply_ite Prod.fst, apply_ite Prod.snd, apply_ite RenewalBankSite.worker,
    apply_ite RenewalBankSite.controller, ite_self]

theorem renewalBankPairMemory_nonroot_controllers {n : Nat} (c : Compiled)
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c) (hx : x.pack.val ≠ 0) :
    (renewalBankPairMemory c m e dest x y).1.controller = .empty ∧
      (renewalBankPairMemory c m e dest x y).2.controller =
        bankMemoryCtlY c.b (m.sites dest).controller
          (bankCell x x.pack.val) (bankCell y y.pack.val) := by
  -- Name the two cells and read the PACK values through them: the goal is then the record
  -- transcription `bankCellMemory` at variables.
  unfold renewalBankPairMemory
  generalize hbx : bankCell x x.pack.val = bx
  generalize hcy : bankCell y y.pack.val = cy
  have hr : x.pack.val = bx.role := by subst hbx; rfl
  have hs : y.pack.val = cy.role := by subst hcy; rfl
  rw [hr] at hx ⊢
  rw [hs]
  have hx' : (bx.role != 0) = true := by simp [hx]
  have hx'' : (bx.role == 0) = false := by simp [hx]
  simp [bankMemoryCtlY, hx, hx', hx'', apply_ite Id.run,
    apply_ite Prod.fst, apply_ite Prod.snd, apply_ite RenewalBankSite.worker,
    apply_ite RenewalBankSite.controller, ite_self] <;>
    by_cases h1 : packNext bx.role cy.role c.b = cy.role <;>
    by_cases h2 : packNext bx.role cy.role c.b = 0 <;> simp_all

/-- **`renewalBankPairMemory` on a nonroot source.** -/
theorem renewalBankPairMemory_nonroot {n : Nat} (c : Compiled)
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c) (hx : x.pack.val ≠ 0) :
    renewalBankPairMemory c m e dest x y =
      (⟨(bankMemoryNRW c.b (m.sites e).worker (m.sites dest).worker
          (bankCell x x.pack.val) (bankCell y y.pack.val)).1, .empty⟩,
       ⟨(bankMemoryNRW c.b (m.sites e).worker (m.sites dest).worker
          (bankCell x x.pack.val) (bankCell y y.pack.val)).2,
        bankMemoryCtlY c.b (m.sites dest).controller
          (bankCell x x.pack.val) (bankCell y y.pack.val)⟩) := by
  have hW := renewalBankPairMemory_nonroot_workers c m e dest x y hx
  have hC := renewalBankPairMemory_nonroot_controllers c m e dest x y hx
  generalize renewalBankPairMemory c m e dest x y = M at hW hC ⊢
  rcases M with ⟨⟨w1, c1⟩, ⟨w2, c2⟩⟩
  simp only at hW hC
  rw [hW.1, hW.2, hC.1, hC.2]

end L3.HeadlineRenewal

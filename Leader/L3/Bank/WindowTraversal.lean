import Leader.L3.Bank.WindowBirth

/-!
Pending-receipt traversal of the BANK window, downstream of BankWindowBirth.

The top-turn pair moves a pending RR receipt one digit back without
reading the receipt's original root.  Hence a traversal invariant that
asks for a complete window at the top turn is not preserved: the root's
PACK can change while the receipt is in flight (PROGRESS, 2026-11-01,
row).  Completeness of a birth must come from the root's own
controller lifecycle instead.
-/

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-- The top-turn OLD pair transports a pending RR receipt to
the predecessor, independently of the PACK or controller at
the receipt's original root. Consumer: the top-turn case of
the proposed BankPendingTraversal induction. -/
theorem bankWindowBirthTopTurnTransfersPendingPair
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (rho : RenewalBankReceipt n)
    (hb : 2 ≤ c.b)
    (hx : x.pack.val + 1 = c.b)
    (hy : y.pack.val = c.b)
    (hsource : x.tok = .E)
    (htop : y.tok = .RR)
    (hpending : (m.sites dest).worker = .pending rho) :
    (renewalBankPairMemory c m e dest x y).1.worker =
      .pending rho ∧
    (renewalBankPairMemory c m e dest x y).2.worker =
      .empty := by
  have hbx : c.b = x.pack.val + 1 := hx.symm
  have hy' : y.pack.val = x.pack.val + 1 := by omega
  have hfirst : 1 ≤ x.pack.val := by omega
  have hpost :
      packNext x.pack.val (x.pack.val + 1) (x.pack.val + 1) =
        x.pack.val + 1 := by
    simp [packNext]
  have hxne : x.pack.val ≠ 0 := by omega
  simp [renewalBankPairMemory, bankCell, hy', hpost, hbx,
    hxne, hfirst, hsource, htop, hpending]

/-- The same top-turn transport is an actual renewalBankNext
ghost transition; it does not test the remote origin root.
Consumer: the failing top-turn row of the word invariant. -/
theorem bankWindowBirthTopTurnTransfersPendingStep
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (rho : RenewalBankReceipt n)
    (hne : ring.rightNeighbor e ≠ e)
    (hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val + 1 =
      (compileAdvice (ceilLogTwo n)).b)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val =
      (compileAdvice (ceilLogTwo n)).b)
    (hsource : (r.1 e).tok = .E)
    (htop : (r.1 (ring.rightNeighbor e)).tok = .RR)
    (hpending :
      (r.2.sites (ring.rightNeighbor e)).worker =
        .pending rho) :
    ((renewalBankNext ring r e).2.sites e).worker =
      .pending rho ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker = .empty := by
  have hpair := bankWindowBirthTopTurnTransfersPendingPair
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) rho
    hb hx hy hsource htop hpending
  have hsrc :
      ((renewalBankNext ring r e).2.sites e).worker =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker := by
    change ((renewalBankMemoryNext ring r.1 r.2 e).sites e).worker = _
    exact congrArg (fun z : RenewalBankSite n => z.worker)
      (if_pos rfl)
  have hdst :
      ((renewalBankNext ring r e).2.sites
          (ring.rightNeighbor e)).worker =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker := by
    change ((renewalBankMemoryNext ring r.1 r.2 e).sites
      (ring.rightNeighbor e)).worker = _
    exact congrArg (fun z : RenewalBankSite n => z.worker)
      ((if_neg hne).trans (if_pos rfl))
  exact ⟨hsrc.trans hpair.1, hdst.trans hpair.2⟩

end L3.BankWindow

#print axioms L3.BankWindow.bankWindowBirthTopTurnTransfersPendingPair
#print axioms L3.BankWindow.bankWindowBirthTopTurnTransfersPendingStep

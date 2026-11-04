import Leader.L3.Bank.MemoryNonroot
import Leader.L3.Bank.PairRoot

/-!
# The BANK ghost memory on a root source with an unchanged first digit

As for `bankPair_rootKeep` (BankPairRoot.lean): on a root source whose responder has PACK 1 and
keeps it, with `2 ≤ b`, every role guard of the ghost observer `renewalBankPairMemory`
(HeadlineRenewal.lean) is decided: the source's worker and the responder's controller are
cleared, and only the root rows `bankMemoryRootKeep` run. `renewalBankPairMemory_rootKeep` states this
once, at variables.
-/

namespace L3.HeadlineRenewal

set_option autoImplicit false

/-- The root rows of the BANK ghost memory on a root source and a responder of PACK 1 that keeps
it, with `2 ≤ b`: the text of `renewalBankPairMemory` after its role guards (source worker and
responder controller cleared). Consumer: `renewalBankPairMemory_rootKeep`. -/
def bankMemoryRootKeep {n : Nat} (service : Nat) (e dest : Fin n)
    (sx0 sy0 : RenewalBankSite n) (bx cy : BankCell) :
    RenewalBankSite n × RenewalBankSite n :=
  let sx : RenewalBankSite n := { sx0 with worker := .empty }
  let sy : RenewalBankSite n := { sy0 with controller := .empty }
  if bx.grant then ({ sx with controller := .empty }, { sy with worker := .empty })
  else if bx.mode == .RESET then
    ({ sx with controller := .waiting [] },
      { sy with worker := .pending { service := service, root := e } })
  else if isRetTok cy.tok then
    if cy.tok == .RL && bx.mode == .RWAIT then
      ({ sx with controller := .active (match sy.worker with
          | .pending receipt => { atoms := renewalBankWaitingAtoms sx.controller, origin := some { service := service, root := e, receipt := receipt }, heads := 0 }
          | _ => renewalBankReturned sx.controller sy.worker dest) },
        { sy with worker := .empty })
    else if cy.tok == .AL && bx.mode == .IWAIT then
      ({ sx with controller := .active (renewalBankReturned sx.controller sy.worker dest) },
        { sy with worker := .empty })
    else if (cy.tok == .CL0 || cy.tok == .CL1) && bx.mode == .CWAIT then
      if cy.tok == .CL0 then
        ({ sx with controller := .active (renewalBankReturned sx.controller sy.worker dest) },
          { sy with worker := .empty })
      else ({ sx with controller := .empty }, { sy with worker := .empty })
    else
      ({ sx with controller := renewalBankWaitSlot bx.mode bx.lease sx.controller },
        { sy with worker := .empty })
  else if bx.mode == .ARMED then
    if cy.tok != .E then ({ sx with controller := .empty }, { sy with worker := .empty })
    else if cy.bit == false then
      ({ sx with controller := .active (renewalBankHead (renewalBankActivePayload sx.controller e)) },
        sy)
    else
      ({ sx with controller := .waiting [] },
        { sy with worker := .payload (renewalBankHead (renewalBankActivePayload sx.controller e)) })
  else if bx.mode == .CSTART then
    if cy.tok != .E then ({ sx with controller := .empty }, { sy with worker := .empty })
    else
      ({ sx with controller := .waiting [] },
        { sy with worker := .payload (renewalBankActivePayload sx.controller e) })
  else ({ sx with controller := renewalBankWaitSlot bx.mode bx.lease sx.controller }, sy)

/-- **`renewalBankPairMemory` on a root source and an unchanged responder of PACK 1.** -/
theorem renewalBankPairMemory_rootKeep {n : Nat} (c : Compiled)
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1) (hb : 2 ≤ c.b) :
    renewalBankPairMemory c m e dest x y =
      bankMemoryRootKeep m.service e dest (m.sites e) (m.sites dest)
        (bankCell x 0) (bankCell y 1) := by
  have hp : packNext 0 1 c.b = 1 := by simp [packNext]; omega
  have hb1 : (c.b == 1) = false := by simp; omega
  have hb2 : 1 ≤ c.b := by omega
  unfold renewalBankPairMemory
  rw [hx, hy, hp]
  generalize m.sites e = sx0
  generalize m.sites dest = sy0
  cases hg : x.grant <;> cases hm : x.mode <;> cases hw : sy0.worker <;>
    simp [bankMemoryRootKeep, bankCell, hb1, hb2, hg, hm, hw, apply_ite Id.run]

end L3.HeadlineRenewal

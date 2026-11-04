import Leader.L3.Bank.InheritedCellRows
import Leader.L3.Bank.MemoryRoot

/-!
# `bankCellMemory` on a root source with an unchanged first digit

`bankCellMemory` (BankInheritedCellRows.lean) is the record transcription of the BANK ghost
memory `renewalBankPairMemory`. As for `renewalBankPairMemory_rootKeep` (BankMemoryRoot.lean): on a
root source whose responder has PACK 1 and keeps it, with `2 ≤ b`, every role guard is decided
and only the root rows `bankMemoryRootKeep` run.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal

set_option autoImplicit false

/-- **`bankCellMemory` on a root source and an unchanged responder of PACK 1.** -/
theorem bankCellMemory_rootKeep {n : Nat} (b : Nat)
    (sx0 sy0 : RenewalBankSite n) (service : Nat) (e dest : Fin n) (bx cy : BankCell)
    (hx : bx.role = 0) (hy : cy.role = 1) (hb : 2 ≤ b) :
    bankCellMemory b sx0 sy0 service e dest bx cy =
      bankMemoryRootKeep service e dest sx0 sy0 bx cy := by
  have hp : packNext 0 1 b = 1 := by simp [packNext]; omega
  have hb1 : (b == 1) = false := by simp; omega
  have hb2 : 1 ≤ b := by omega
  rcases bx with ⟨xr, xm, xb, xt, xl, xg⟩
  rcases cy with ⟨yr, ym, yb, yt, yl, yg⟩
  simp only at hx hy
  subst hx hy
  unfold bankCellMemory
  cases xg <;> cases xm <;> cases hw : sy0.worker <;>
    simp [bankMemoryRootKeep, hp, hb1, hb2, hw, apply_ite Id.run]

end L3.RenewalReferenceClock

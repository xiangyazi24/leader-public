import Leader.L3.Bank.InheritedCellRows
import Leader.L3.Bank.MemoryNonroot

/-!
# `bankCellMemory` on a nonroot source

`bankCellMemory` (BankInheritedCellRows.lean) is the record transcription of the BANK ghost
memory `renewalBankPairMemory`. As for `bankPair_nonroot` (BankPairNonroot.lean) and
`renewalBankPairMemory_nonroot` (BankMemoryNonroot.lean): on a nonroot source its root rows never
run, the source controller ends empty, the responder controller is `bankMemoryCtlY`, and the two
workers are `bankMemoryNRW`. Lemmas about a nonroot step rewrite with `bankCellMemory_nonroot` and
unfold only the worker rows.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false

/-- The two workers of `bankCellMemory` on a nonroot source are `bankMemoryNRW`. -/
theorem bankCellMemory_nonroot_workers {n : Nat} (b : Nat)
    (sx0 sy0 : RenewalBankSite n) (service : Nat) (e dest : Fin n) (bx cy : BankCell)
    (hx : bx.role ≠ 0) :
    (bankCellMemory b sx0 sy0 service e dest bx cy).1.worker =
        (bankMemoryNRW b sx0.worker sy0.worker bx cy).1 ∧
      (bankCellMemory b sx0 sy0 service e dest bx cy).2.worker =
        (bankMemoryNRW b sx0.worker sy0.worker bx cy).2 := by
  have hx' : (bx.role != 0) = true := by simp [hx]
  have hx'' : (bx.role == 0) = false := by simp [hx]
  simp [bankCellMemory, bankMemoryNRW, hx, hx', hx'', apply_ite Id.run, apply_ite Prod.fst,
    apply_ite Prod.snd, apply_ite RenewalBankSite.worker, apply_ite RenewalBankSite.controller,
    ite_self]

/-- On a nonroot source the source controller ends empty and the responder controller is
`bankMemoryCtlY`. -/
theorem bankCellMemory_nonroot_controllers {n : Nat} (b : Nat)
    (sx0 sy0 : RenewalBankSite n) (service : Nat) (e dest : Fin n) (bx cy : BankCell)
    (hx : bx.role ≠ 0) :
    (bankCellMemory b sx0 sy0 service e dest bx cy).1.controller = .empty ∧
      (bankCellMemory b sx0 sy0 service e dest bx cy).2.controller =
        bankMemoryCtlY b sy0.controller bx cy := by
  have hx' : (bx.role != 0) = true := by simp [hx]
  have hx'' : (bx.role == 0) = false := by simp [hx]
  simp [bankCellMemory, bankMemoryCtlY, hx, hx', hx'', apply_ite Id.run, apply_ite Prod.fst,
    apply_ite Prod.snd, apply_ite RenewalBankSite.worker, apply_ite RenewalBankSite.controller,
    ite_self] <;>
    by_cases h1 : packNext bx.role cy.role b = cy.role <;>
    by_cases h2 : packNext bx.role cy.role b = 0 <;> simp_all

/-- **`bankCellMemory` on a nonroot source.** -/
theorem bankCellMemory_nonroot {n : Nat} (b : Nat)
    (sx0 sy0 : RenewalBankSite n) (service : Nat) (e dest : Fin n) (bx cy : BankCell)
    (hx : bx.role ≠ 0) :
    bankCellMemory b sx0 sy0 service e dest bx cy =
      (⟨(bankMemoryNRW b sx0.worker sy0.worker bx cy).1, .empty⟩,
       ⟨(bankMemoryNRW b sx0.worker sy0.worker bx cy).2,
        bankMemoryCtlY b sy0.controller bx cy⟩) := by
  have hW := bankCellMemory_nonroot_workers b sx0 sy0 service e dest bx cy hx
  have hC := bankCellMemory_nonroot_controllers b sx0 sy0 service e dest bx cy hx
  generalize bankCellMemory b sx0 sy0 service e dest bx cy = M at hW hC ⊢
  rcases M with ⟨⟨w1, c1⟩, ⟨w2, c2⟩⟩
  simp only at hW hC
  rw [hW.1, hW.2, hC.1, hC.2]

end L3.RenewalReferenceClock

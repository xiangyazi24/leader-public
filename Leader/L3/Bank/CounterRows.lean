import Leader.L3.Bank.HeadThreshold

/-!
Local comparator-row diagnosis for the genuine BANK reference.

The finite countermodel of this diagnosis
is a BANK pair/observer row, NOT a proved reachable word
of renewalBankStart. Consequently no theorem asserting the full
BankReferenceCounterRows or R11 is introduced here.

The predicate below removes the old threshold-like cut clause
from its DEFINITION and records genuine origin-indexed comparator
tokens and their already-read digit bits. Its preservation would
still require the missing origin/phase exclusion invariant.
-/

namespace L3.BankCounterRows

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankHeadThreshold

set_option autoImplicit false
set_option Elab.async false

/-- Prefix digit equality at the current physical snapshot.
A CR1 carrier at role j should certify all indices below j. -/
def bankComparatorPrefixMatched {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (o : RenewalBankOrigin n) (last : Nat) : Prop :=
  ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    j.val + 1 ≤ last →
    (r.1 (Counter.site ring o.root (j.val + 1))).bit =
      (compileAdvice (ceilLogTwo n)).theta j.val

/-- No in-flight increment is permitted among the scanned
digits while a comparator value is claimed to be frozen. -/
def bankComparatorPrefixIRFree {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (o : RenewalBankOrigin n) (last : Nat) : Prop :=
  ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    j.val + 1 ≤ last →
    (r.1 (Counter.site ring o.root (j.val + 1))).tok ≠ .IR

/-- Candidate strengthening, deliberately without the almost
identical-to-R11 old cut clause of BankOriginCounterValueInv.

The first component is the origin-specific physical carry ledger.
The second records CR1/CL1 checked bits and no IR in those digits,
for a comparator token carrying the SAME completed origin.
This is a DIAGNOSTIC Prop, not a claimed inductive invariant.
In particular, it does not assert origin-exclusive root ownership
or exclude a foreign ARMED service during a comparator flight. -/
def BankReferenceComparatorInv {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) : Prop :=
  (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
    ((r.2.sites i).worker = .payload p ∨
      (r.2.sites i).controller = .active p) →
    p.origin = some o →
    bankOriginCarryValue ring r.1 o ≤ p.heads) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
    (r.2.sites i).worker = .payload p →
    p.origin = some o →
    (((r.1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring r o
        (r.1 i).pack.val ∧
      bankComparatorPrefixIRFree ring r o
        (r.1 i).pack.val) ∧
     ((r.1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring r o
        (compileAdvice (ceilLogTwo n)).b ∧
      bankComparatorPrefixIRFree ring r o
        (compileAdvice (ceilLogTwo n)).b)))

/-- The noncircular numerical component of the diagnostic Prop. -/
theorem bankReferenceComparatorInvLedger {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (h : BankReferenceComparatorInv ring r)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hc : (r.2.sites i).worker = .payload p ∨
      (r.2.sites i).controller = .active p)
    (ho : p.origin = some o) :
    bankOriginCarryValue ring r.1 o ≤ p.heads :=
  h.1 o i p hc ho

/-- Literal source bank cell for the failed finite local row. -/
private def bankCounterForeignArmedSource : BankCell :=
  { role := 0, mode := .ARMED, bit := false,
    tok := .E, lease := 0, grant := false }

/-- Literal first digit before the unmatched ARMED head. -/
private def bankCounterForeignFirstDigit : BankCell :=
  { role := 1, mode := .RESET, bit := false,
    tok := .E, lease := 0, grant := false }

/-- The selected raw BANK edge writes a 1 to the first digit.
The distant CR1 worker is framed by renewalBankMemoryNext. -/
theorem bankCounterForeignArmedBit :
    (bankPair bankCounterForeignArmedSource
      bankCounterForeignFirstDigit 1 13
      (fun _ => false)).2.bit = true := by
  rfl

/-- The old ARMED controller proceeds to CSTART on that edge. -/
theorem bankCounterForeignArmedMode :
    (bankPair bankCounterForeignArmedSource
      bankCounterForeignFirstDigit 1 13
      (fun _ => false)).1.mode = .CSTART := by
  rfl

/-- The finite row gains one unit of physical digit credit while
the origin's distant payload can retain heads = 6. This is
local raw arithmetic, not a reachable-reference counterexample. -/
theorem bankCounterForeignUnpaidUnit :
    6 <
      (if (bankPair bankCounterForeignArmedSource
        bankCounterForeignFirstDigit 1 13
        (fun _ => false)).2.bit then 1 else 0) + 2 + 4 := by
  change 6 < 1 + 2 + 4
  omega

end L3.BankCounterRows

#print axioms L3.BankCounterRows.bankReferenceComparatorInvLedger
#print axioms L3.BankCounterRows.bankCounterForeignArmedBit
#print axioms L3.BankCounterRows.bankCounterForeignArmedMode
#print axioms L3.BankCounterRows.bankCounterForeignUnpaidUnit

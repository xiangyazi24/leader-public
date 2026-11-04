import Leader.L3.Base

/-!
# The BANK pair on a root source with an unchanged first digit

`bankPair` (Base.lean) is one `Id.run do` block whose first statements are role guards. On a root
source (PACK 0) whose responder has PACK 1 and keeps it, with `2 ≤ b`, every role guard is
decided: the source token is cleared, the responder's mode and lease are reset, and only the root
rows run. `bankPairRootKeep` is those root rows, in the original order, with the guards removed.
`bankPair_rootKeep` states this once, at variables; consumers rewrite with it and split only the
mode and token selectors their statement reads. The ghost memory has the same form
(`renewalBankPairMemory_rootKeep`, BankMemoryRoot.lean).
-/

namespace L3

set_option autoImplicit false

/-- The root rows of `bankPair` on a root source and a responder of PACK 1 that keeps it, with
`2 ≤ b`: the text of `bankPair` after its role guards. Consumer: `bankPair_rootKeep`. -/
def bankPairRootKeep (x0 y0 : BankCell) (b : Nat) (theta : Nat → Bool) : BankCell × BankCell :=
  let L := 13 * (b + 2)
  let x : BankCell := { x0 with tok := .E }
  let y : BankCell := { y0 with role := 1, mode := .RESET, lease := 0 }
  let wait : BankCell → BankCell := fun z =>
    if isWaitMode z.mode then
      (if z.lease > 1 then { z with lease := z.lease - 1 }
       else { z with mode := .RESET, lease := 0 })
    else z
  if x.grant then ({ x with mode := .RESET, lease := 0 }, { y with tok := .E })
  else if x.mode == .RESET then
    ({ x with mode := .RWAIT, lease := L }, { y with bit := false, tok := .RR })
  else if isRetTok y.tok then
    if y.tok == .RL && x.mode == .RWAIT then ({ x with mode := .ARMED, lease := 0 }, { y with tok := .E })
    else if y.tok == .AL && x.mode == .IWAIT then
      ({ x with mode := .CSTART, lease := 0 }, { y with tok := .E })
    else if (y.tok == .CL0 || y.tok == .CL1) && x.mode == .CWAIT then
      ({ x with mode := (if y.tok == .CL1 then Mode.RESET else Mode.ARMED), lease := 0 },
        { y with tok := .E })
    else (wait x, { y with tok := .E })
  else if x.mode == .ARMED then
    if y.tok != .E then ({ x with mode := .RESET, lease := 0 }, { y with tok := .E })
    else if y.bit == false then ({ x with mode := .CSTART, lease := 0 }, { y with bit := true })
    else ({ x with mode := .IWAIT, lease := L }, { y with bit := false, tok := .IR })
  else if x.mode == .CSTART then
    if y.tok != .E then ({ x with mode := .RESET, lease := 0 }, { y with tok := .E })
    else ({ x with mode := .CWAIT, lease := L },
      { y with tok := (if y.bit == theta 0 then BTok.CR1 else BTok.CR0) })
  else (wait x, y)

/-- **`bankPair` on a root source and an unchanged responder of PACK 1.** -/
theorem bankPair_rootKeep (x0 y0 : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x0.role = 0) (hy : y0.role = 1) (hb : 2 ≤ b) :
    bankPair x0 y0 1 b theta = bankPairRootKeep x0 y0 b theta := by
  have hb1 : (b == 1) = false := by simp; omega
  have hb2 : 1 ≤ b := by omega
  rcases x0 with ⟨xr, xm, xb, xt, xl, xg⟩
  rcases y0 with ⟨yr, ym, yb, yt, yl, yg⟩
  simp only at hx hy
  subst hx hy
  cases xg <;> cases xm <;>
    simp [bankPair, bankPairRootKeep, hb1, hb2, isWaitMode, apply_ite Id.run]

end L3

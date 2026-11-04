import Leader.L3.Target
import Leader.L3.Top.MarkedLinkQI

/-!
# Q7: the QC rows and the carry ledger are the abstract `carries`

The physical checker carry of `liveTopPair` and the comparison-lane carry ghost
of `digitLaneReplay` evolve by the same launch / advance / abort / retire rows.
The abstract carry class is `off`, `fresh` (ledger `inherited = none`) or
`inh` (any other ledger, or a missing one).

Consumer: `Leader/L3/Top/MarkedLink.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- Carry class of a physical carry and its audit ledger.

Consumer: `link_step`. -/
def absCar {c : Compiled} {n : Nat} (q : QCarry)
    (g : Option (DigitCarryGhost c n)) : Car :=
  match q with
  | .OFF => .off
  | .L _ _ =>
      match g with
      | some l => if l.inherited.isNone then .fresh else .inh
      | none => .inh

/-- The QC block of `liveTopPair`, copied verbatim (root-free branch).

Consumer: `link_step`. -/
def qcPhys (c : Compiled) (ox oy : Agent c) : QCarry × QCarry × Bool :=
  let a := c.topA
  let qTerminal := topTerminal ox oy
  let qc2Live := ox.qCarry.isL && !qTerminal
  let qc2Success := qc2Live && oy.qCarry.isOff && oy.qIn.isS
  let qc3 := topBorder ox && ox.qCarry.isOff && ox.qIn.isS && !oy.l
  if ox.qCarry.isL then
    if qTerminal then (.OFF, oy.qCarry, qcE ox.qCarry)
    else if qc2Success then
      let v := (inV c oy.qIn).val
      let cc := qcC ox.qCarry
      let e := qcE ox.qCarry
      let c1 := cc && v + 1 == a
      let e1 := e || (oy.d.val != mod (v + (if cc then 1 else 0)) a)
      (.OFF, QC c1 e1, false)
    else (.OFF, oy.qCarry, false)
  else if qc3 then
    let v := (inV c ox.qIn).val
    (QC (v + 1 == a) (ox.d.val != mod (v + 1) a), oy.qCarry, false)
  else (ox.qCarry, oy.qCarry, false)

/-- The checker carry outputs of `liveTopPair` are the copied QC block.

Consumer: `link_step`. -/
theorem liveTopPair_qCarry (c : Compiled) (x y : Agent c) (rb1 rb2 : Bool)
    (hxl : x.l = false) (hyl : y.l = false) :
    (liveTopPair c x y rb1 rb2).x.qCarry = (qcPhys c x y).1 ∧
    (liveTopPair c x y rb1 rb2).y.qCarry = (qcPhys c x y).2.1 := by
  simp [liveTopPair, qcPhys, hxl, hyl]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8192 in
/-- Physical and ghost carry agree with the abstract `carries` row.

Consumer: `link_step`. -/
theorem carry_link {c : Compiled} {n : Nat} (time : Nat) (src dst : Fin n)
    (x y : Agent c) (hxl : x.l = false) (hyl : y.l = false)
    (gx gy : DigitLaneGhost c n) (xc yc : Cell)
    (hxi : xc.i.isS = x.qIn.isS) (hyi : yc.i.isS = y.qIn.isS)
    (hxc : xc.c = absCar x.qCarry gx.carry) (hyc : yc.c = absCar y.qCarry gy.carry) :
    absCar (qcPhys c x y).1
      (digitLaneReplay .comparison time src dst
        (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
        (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).x.carry =
      (carries x.beta y.beta xc yc).1 ∧
    absCar (qcPhys c x y).2.1
      (digitLaneReplay .comparison time src dst
        (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
        (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).y.carry =
      (carries x.beta y.beta xc yc).2 := by
  rcases xc with ⟨xi, xk⟩
  rcases yc with ⟨yi, yk⟩
  simp only at hxi hyi hxc hyc
  subst hxc hyc
  rcases hxk : x.qCarry with _ | ⟨xcc, xce⟩ <;>
  rcases hyk : y.qCarry with _ | ⟨ycc, yce⟩ <;>
  rcases gx with ⟨gxo, gxn, _ | ⟨gxi, gxu⟩⟩ <;> rcases gy with ⟨gyo, gyn, _ | ⟨gyi, gyu⟩⟩ <;>
  (try cases gxi) <;> (try cases gyi) <;>
  cases hxb : x.beta <;> cases hyb : y.beta <;>
  cases hxs : x.qIn.isS <;> cases hys : y.qIn.isS <;>
  simp (config := { decide := true })
    [qcPhys, digitLaneReplay, digitLaneView, ProjD.ofAgent, ProjW.ofAgent, absCar,
     carries, hxl, hyl, hxk, hyk, hxb, hyb, hxs, hys, QC,
     topTerminal, topBorder, QCarry.isOff, QCarry.isL,
     Agent.certNative] at hxi hyi ⊢ <;>
  simp_all

end MarkedCells
end L3

#print axioms L3.MarkedCells.carry_link

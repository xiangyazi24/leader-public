import Leader.L3.CertRows
import Leader.L3.Top.MarkedCells

/-!
# Q7: the QI rows of `liveTopPair` are the abstract `inSlots`

Consumer: `Leader/L3/Top/MarkedLink.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- Input class of a physical input token.

Consumer: `link_step`. -/
def absIn {a : Nat} : InTok a → Inp
  | .E => .e
  | .X => .x
  | .P _ t => if t then .pt else .pn
  | .S _ t => if t then .st else .sn

/-- Offness of the abstract carry class matches the physical carry.

Consumer: `link_step`. -/
def OffMatch (q : QCarry) (k : Car) : Prop :=
  (k = .off ↔ q = .OFF)

/-- The non-root QI block of `liveTopPair`, copied verbatim.

Consumer: `link_step`. -/
def qiPhys (c : Compiled) (ox oy : Agent c) : InSt c.topA × Bool :=
  let qTerminal := topTerminal ox oy
  let qc2Live := ox.qCarry.isL && !qTerminal
  let qc2Success := qc2Live && oy.qCarry.isOff && oy.qIn.isS
  let qc3 := topBorder ox && ox.qCarry.isOff && ox.qIn.isS && !oy.l
  let qo1 := ox.qOut.isD && oy.beta
  let s : InSt c.topA := { iX := ox.qIn, iY := oy.qIn, fx := false, fy := false }
  let s := if !s.fx && !ox.qCarry.isOff then { s with iX := .E, fx := true } else s
  let s := if !s.fy && !oy.qCarry.isOff then { s with iY := .E, fy := true } else s
  let s := if !s.fx && ox.qIn.isS && inT ox.qIn && !ox.beta then
             { s with iX := .X, fx := true } else s
  let s := if !s.fx && ox.qIn.isX then
             let s := { s with iX := .E, fx := true }
             if !s.fy && topInternal oy && oy.qIn.isS then { s with iY := .X, fy := true } else s
           else s
  let s := if qc2Success && !s.fy then { s with iY := .E, fy := true } else s
  let s := if qc3 && !s.fx then { s with iX := .E, fx := true } else s
  let s := if !s.fx && ox.qIn.isP then
             if qTerminal then
               if !inT ox.qIn then { s with iX := .S (inV c ox.qIn) false, fx := true }
               else if !ox.beta then { s with iX := .E, fx := true }
               else s
             else if topInternal oy && oy.qIn.isE && oy.qCarry.isOff && !s.fy then
               { iX := .E, iY := .P (inV c ox.qIn) (inT ox.qIn), fx := true, fy := true }
             else if oy.qIn.isS && oy.qCarry.isOff then
               { s with iX := .S (inV c ox.qIn) (inT ox.qIn), fx := true }
             else s
           else s
  let acc := !s.fy && qo1 && oy.qIn.isE && oy.qCarry.isOff
  let s := if acc then { s with iY := .P (outV c ox.qOut) (outT ox.qOut), fy := true } else s
  (s, acc)

/-- The checker input outputs of `liveTopPair` are the copied QI block.

Consumer: `link_step`. -/
theorem liveTopPair_qIn (c : Compiled) (x y : Agent c) (rb1 rb2 : Bool)
    (hxl : x.l = false) (hyl : y.l = false) :
    (liveTopPair c x y rb1 rb2).x.qIn = (qiPhys c x y).1.iX ∧
    (liveTopPair c x y rb1 rb2).y.qIn = (qiPhys c x y).1.iY := by
  simp [liveTopPair, qiPhys, hxl, hyl]

/-- Interior responder: the QI block is the abstract `inSlots`.

Consumer: `link_step`. -/
theorem qi_link_interior (c : Compiled) (x y : Agent c)
    (hxl : x.l = false) (hyl : y.l = false) (hyb : y.beta = false)
    (xc yc : Cell)
    (hxi : xc.i = absIn x.qIn) (hyi : yc.i = absIn y.qIn)
    (hxo : OffMatch x.qCarry xc.c) (hyo : OffMatch y.qCarry yc.c) :
    absIn (qiPhys c x y).1.iX = (inSlots x.beta false xc yc).iX ∧
    absIn (qiPhys c x y).1.iY = (inSlots x.beta false xc yc).iY := by
  rcases xc with ⟨xi, xk⟩
  rcases yc with ⟨yi, yk⟩
  simp only at hxi hyi
  subst hxi hyi
  unfold OffMatch at hxo hyo
  simp only at hxo hyo
  rcases hxq : x.qIn with _ | _ | ⟨xv, xt⟩ | ⟨xv, xt⟩ <;>
  rcases hyq : y.qIn with _ | _ | ⟨yv, yt⟩ | ⟨yv, yt⟩ <;>
  rcases hxk : x.qCarry with _ | ⟨xcc, xce⟩ <;>
  rcases hyk : y.qCarry with _ | ⟨ycc, yce⟩ <;>
  cases hxb : x.beta <;>
  (try cases xt) <;> (try cases yt) <;>
  simp (config := { decide := true })
    [qiPhys, hxl, hyl, hxq, hyq, hxk, hyk, hxb, hyb, absIn, inSlots,
     topTerminal, topInternal, topBorder, QCarry.isOff, QCarry.isL,
     InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV, Inp.isS, hxo, hyo]

/-- Terminal responder (a marker): the source row is the abstract `inSlots`, and the
responder keeps its input, is cleaned of a host, or accepts a packet.

Consumer: `link_step`. -/
theorem qi_link_terminal (c : Compiled) (x y : Agent c)
    (hxl : x.l = false) (hyl : y.l = false) (hyb : y.beta = true)
    (xc yc : Cell)
    (hxi : xc.i = absIn x.qIn) (hyi : yc.i = absIn y.qIn)
    (hxo : OffMatch x.qCarry xc.c) (hyo : OffMatch y.qCarry yc.c) :
    absIn (qiPhys c x y).1.iX = (inSlots x.beta true xc yc).iX ∧
    (absIn (qiPhys c x y).1.iY = (portClean yc).i ∨
      ∃ t, absIn (qiPhys c x y).1.iY = (portAccept t yc).i) := by
  rcases xc with ⟨xi, xk⟩
  rcases yc with ⟨yi, yk⟩
  simp only at hxi hyi
  subst hxi hyi
  unfold OffMatch at hxo hyo
  simp only at hxo hyo
  rcases hxq : x.qIn with _ | _ | ⟨xv, xt⟩ | ⟨xv, xt⟩ <;>
  rcases hyq : y.qIn with _ | _ | ⟨yv, yt⟩ | ⟨yv, yt⟩ <;>
  rcases hxk : x.qCarry with _ | ⟨xcc, xce⟩ <;>
  rcases hyk : y.qCarry with _ | ⟨ycc, yce⟩ <;>
  cases hxb : x.beta <;>
  (try cases xt) <;> (try cases yt) <;>
  cases hd : x.qOut.isD <;>
  simp (config := { decide := true })
    [qiPhys, hxl, hyl, hxq, hyq, hxk, hyk, hxb, hyb, hd, absIn, inSlots, portClean, portAccept,
     topTerminal, topInternal, topBorder, QCarry.isOff, QCarry.isL,
     InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV, Inp.isS, hxo, hyo] <;>
  first
    | exact ⟨outT x.qOut, by simp [absIn]⟩
    | skip

end MarkedCells
end L3

#print axioms L3.MarkedCells.qi_link_interior
#print axioms L3.MarkedCells.qi_link_terminal

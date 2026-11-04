import Leader.L3.Top.MarkedLink
import Leader.L3.Top.SettledWorkSourceModel

/-!
# Q7 (P.8): the QO rows of `liveTopPair` are the abstract `srcPair`

The output field `qOut` of the checker on one edge `x -> y` is computed by the QO block of
`liveTopPair`, which reads the markers `x.beta`, `y.beta` and, on a marker responder, the
acceptance flag of the QI block.  This module shows that on agents with `l = false` the
abstract token of the result is `srcPair`, with `acc` the physical acceptance condition (the
responder input is empty and carry-free).

Consumer: `Leader/L3/Top/SettledWorkSource.lean` (the link of the source block to the trace).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The abstract token of a physical output.

Consumer: `srcOf` (TopSettledWorkSource). -/
def absOut {a : Nat} : OutTok a → Tok
  | .E => .e
  | .U => .u
  | .D _ t => if t then .dt else .dn

/-- The non-root QO block of `liveTopPair`, copied verbatim.

Consumer: `liveTopPair_qOut`. -/
def qoPhys (c : Compiled) (ox oy : Agent c) : OutTok c.topA × OutTok c.topA :=
  let acceptQO := (qiPhys c ox oy).2
  let qo1 := ox.qOut.isD && oy.beta
  if qo1 then
    (if acceptQO then ((if outT ox.qOut then .U else .E), oy.qOut) else (ox.qOut, oy.qOut))
  else if ox.qOut.isD && !oy.beta && oy.qOut.isE then
    ((if outT ox.qOut then .U else .E), .D (outV c ox.qOut) (outT ox.qOut))
  else if ox.qOut.isU then (.D ox.d ox.beta, oy.qOut)
  else if ox.beta && ox.qOut.isE then (.U, oy.qOut)
  else (ox.qOut, oy.qOut)

/-- The output fields of `liveTopPair` are the copied QO block.

Consumer: `qo_link_internal`, `qo_link_marker`. -/
theorem liveTopPair_qOut (c : Compiled) (x y : Agent c) (rb1 rb2 : Bool)
    (hxl : x.l = false) (hyl : y.l = false) :
    (liveTopPair c x y rb1 rb2).x.qOut = (qoPhys c x y).1 ∧
    (liveTopPair c x y rb1 rb2).y.qOut = (qoPhys c x y).2 := by
  simp [liveTopPair, qoPhys, qiPhys, hxl, hyl]

/-- The acceptance flag on a marker responder: a sampled output is offered, and the responder
input is empty and carry-free.

Consumer: `qo_link_marker`. -/
theorem qi_acc_marker (c : Compiled) (x y : Agent c)
    (hxl : x.l = false) (hyl : y.l = false) (hyb : y.beta = true) :
    (qiPhys c x y).2 = (x.qOut.isD && y.qIn.isE && y.qCarry.isOff) := by
  rcases hxq : x.qIn with _ | _ | ⟨xv, xt⟩ | ⟨xv, xt⟩ <;>
  rcases hyq : y.qIn with _ | _ | ⟨yv, yt⟩ | ⟨yv, yt⟩ <;>
  rcases hxk : x.qCarry with _ | ⟨xcc, xce⟩ <;>
  rcases hyk : y.qCarry with _ | ⟨ycc, yce⟩ <;>
  cases hxb : x.beta <;>
  (try cases xt) <;> (try cases yt) <;>
  cases hd : x.qOut.isD <;>
  simp (config := { decide := true })
    [qiPhys, hxl, hyl, hxq, hyq, hxk, hyk, hxb, hyb, hd, topTerminal, topInternal, topBorder,
     QCarry.isOff, QCarry.isL, InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV]

/-- Interior responder: the abstract token pair of the QO block.

Consumer: `src_link_edge` (TopSettledWorkSource). -/
theorem qo_link_internal (c : Compiled) (x y : Agent c) (hyb : y.beta = false) :
    absOut (qoPhys c x y).1 = (srcPair x.beta false false (absOut x.qOut) (absOut y.qOut)).1 ∧
    absOut (qoPhys c x y).2 = (srcPair x.beta false false (absOut x.qOut) (absOut y.qOut)).2 := by
  rcases hxo : x.qOut with _ | _ | ⟨xv, xt⟩ <;>
  rcases hyo : y.qOut with _ | _ | ⟨yv, yt⟩ <;>
  cases hxb : x.beta <;> (try cases xt) <;> (try cases yt) <;>
  simp (config := { decide := true })
    [qoPhys, srcPair, absOut, hxo, hyo, hxb, hyb, OutTok.isD, OutTok.isE, OutTok.isU, outT, outV,
     Tok.isD]

/-- Marker responder: the abstract token pair of the QO block, with `acc` the physical
acceptance condition.

Consumer: `src_link_edge`, `src_link_away` (TopSettledWorkSource). -/
theorem qo_link_marker (c : Compiled) (x y : Agent c)
    (hxl : x.l = false) (hyl : y.l = false) (hyb : y.beta = true) :
    absOut (qoPhys c x y).1 =
      (srcPair x.beta true (y.qIn.isE && y.qCarry.isOff) (absOut x.qOut) (absOut y.qOut)).1 ∧
    (qoPhys c x y).2 = y.qOut := by
  have hacc := qi_acc_marker c x y hxl hyl hyb
  rcases hxo : x.qOut with _ | _ | ⟨xv, xt⟩ <;>
  cases hxb : x.beta <;> (try cases xt) <;>
  cases hyi : y.qIn.isE <;> cases hyk : y.qCarry.isOff <;>
  simp (config := { decide := true })
    [qoPhys, srcPair, absOut, hxo, hyb, hacc, hyi, hyk, hxb, OutTok.isD, OutTok.isE, OutTok.isU,
     outT, outV, Tok.isD]

/-- The first token of a marker-responder pair does not read the responder token.

Consumer: `src_link_edge` (TopSettledWorkSource). -/
theorem srcPair_marker_indep (bx acc : Bool) (x y y' : Tok) :
    (srcPair bx true acc x y).1 = (srcPair bx true acc x y').1 := by
  cases x <;> cases bx <;> cases acc <;> simp [srcPair, Tok.isD]

/-- Marker responder, empty and carry-free, offered a sampled token: the responder input is the
pending packet of the offered value and tail flag.

Consumer: `port_accept_link` (TopSettledWorkSource). -/
theorem qi_marker_accept (c : Compiled) (x y : Agent c) (v : Fin c.topA) (t : Bool)
    (hxl : x.l = false) (hyl : y.l = false) (hyb : y.beta = true)
    (hD : x.qOut = .D v t) (hyi : y.qIn.isE = true) (hyk : y.qCarry.isOff = true) :
    (qiPhys c x y).1.iY = .P v t := by
  rcases hxq : x.qIn with _ | _ | ⟨xv, xt⟩ | ⟨xv, xt⟩ <;>
  rcases hyq : y.qIn with _ | _ | ⟨yv, yt⟩ | ⟨yv, yt⟩ <;>
  rcases hxk : x.qCarry with _ | ⟨xcc, xce⟩ <;>
  rcases hyk' : y.qCarry with _ | ⟨ycc, yce⟩ <;>
  cases hxb : x.beta <;>
  (try cases xt) <;> (try cases yt) <;>
  simp (config := { decide := true })
    [qiPhys, hxl, hyl, hxq, hyq, hxk, hyk', hxb, hyb, hD, topTerminal, topInternal, topBorder,
     QCarry.isOff, QCarry.isL, InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV, outT, outV,
     OutTok.isD] at hyi hyk ⊢

end MarkedCells
end L3

#print axioms L3.MarkedCells.liveTopPair_qOut
#print axioms L3.MarkedCells.qi_acc_marker
#print axioms L3.MarkedCells.qo_link_internal
#print axioms L3.MarkedCells.qo_link_marker
#print axioms L3.MarkedCells.qi_marker_accept

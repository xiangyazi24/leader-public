import Leader.L3.CertRows

/-!
# The lane blocks of `liveTopPair`

`liveTopPair` computes all LIVE-TOP fields in one `let` chain. A proof about one field that unfolds
`liveTopPair` makes `simp` carry the whole chain (writer and checker lanes, base, digit, dirty
flags) through every case of its case split. Each block below is the text of one lane of
`liveTopPair`, copied verbatim together with the look flags it reads, and each projection of
`liveTopPair` equals its block by `rfl`. Rewriting with these equations before a case split lets
`simp` unfold only the lane the statement mentions.

No new protocol content: the blocks are definitional copies, checked by `rfl`.
-/

namespace L3

set_option autoImplicit false

/-- The writer-carry rows (`wcr`) of `liveTopPair`, verbatim with their look flags. -/
def liveTopWC (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) : WCarry × WCarry × Option (Fin c.topA) × Option (Fin c.topA) :=
  let a := c.topA
  let wox : Agent c := { ox with beta := betaX }
  let woy : Agent c := { oy with beta := betaY }
  let rootX := ox.l
  let rootY := oy.l
  let wTerminal := topTerminal wox woy
  let qTerminal := topTerminal ox oy
  let wc2Live := ox.wCarry.isW && !wTerminal
  let wc2Success := wc2Live && oy.wCarry.isOff && oy.wIn.isS
  let wc3 := topBorder wox && ox.wCarry.isOff && ox.wIn.isS && !rootY
  let qc2Live := ox.qCarry.isL && !qTerminal
  let qc2Success := qc2Live && oy.qCarry.isOff && oy.qIn.isS
  let qc3 := topBorder ox && ox.qCarry.isOff && ox.qIn.isS && !rootY
  let wo1 := ox.wOut.isD && woy.beta
  let qo1 := ox.qOut.isD && oy.beta
  let wcr : WCarry × WCarry × Option (Fin c.topA) × Option (Fin c.topA) :=
    if rootX || rootY then
      ((if ox.wCarry.isW then .OFF else ox.wCarry), (if oy.wCarry.isW then .OFF else oy.wCarry),
       none, none)
    else if ox.wCarry.isW then
      if !wTerminal && wc2Success then
        let v := (inV c oy.wIn).val
        let cc := wcC ox.wCarry
        (.OFF, WC (cc && v + 1 == a), none, some (c.digitMod (v + (if cc then 1 else 0))))
      else (.OFF, oy.wCarry, none, none)
    else if wc3 then
      let v := (inV c ox.wIn).val
      (WC (v + 1 == a), oy.wCarry, some (c.digitMod (v + 1)), none)
    else (ox.wCarry, oy.wCarry, none, none)
  wcr

/-- The writer-input rows WI0-WI7 (`wi`) of `liveTopPair`, verbatim with their look flags. -/
def liveTopWI (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) : InSt c.topA × Bool :=
  let a := c.topA
  let wox : Agent c := { ox with beta := betaX }
  let woy : Agent c := { oy with beta := betaY }
  let rootX := ox.l
  let rootY := oy.l
  let wTerminal := topTerminal wox woy
  let qTerminal := topTerminal ox oy
  let wc2Live := ox.wCarry.isW && !wTerminal
  let wc2Success := wc2Live && oy.wCarry.isOff && oy.wIn.isS
  let wc3 := topBorder wox && ox.wCarry.isOff && ox.wIn.isS && !rootY
  let qc2Live := ox.qCarry.isL && !qTerminal
  let qc2Success := qc2Live && oy.qCarry.isOff && oy.qIn.isS
  let qc3 := topBorder ox && ox.qCarry.isOff && ox.qIn.isS && !rootY
  let wo1 := ox.wOut.isD && woy.beta
  let qo1 := ox.qOut.isD && oy.beta
  let wi : InSt c.topA × Bool :=
    if rootX || rootY then ({ iX := .E, iY := .E, fx := true, fy := true }, false)
    else
      let s : InSt c.topA := { iX := ox.wIn, iY := oy.wIn, fx := false, fy := false }
      let s := if !s.fx && !ox.wCarry.isOff then { s with iX := .E, fx := true } else s
      let s := if !s.fy && !oy.wCarry.isOff then { s with iY := .E, fy := true } else s
      let s := if !s.fx && ox.wIn.isS && inT ox.wIn && !wox.beta then
                 { s with iX := .X, fx := true } else s
      let s := if !s.fx && ox.wIn.isX then
                 let s := { s with iX := .E, fx := true }
                 if !s.fy && topInternal woy && oy.wIn.isS then { s with iY := .X, fy := true } else s
               else s
      let s := if wc2Success && !s.fy then { s with iY := .E, fy := true } else s
      let s := if wc3 && !s.fx then { s with iX := .E, fx := true } else s
      let s := if !s.fx && ox.wIn.isP then
                 if wTerminal then
                   if !inT ox.wIn then { s with iX := .S (inV c ox.wIn) false, fx := true }
                   else if !wox.beta then { s with iX := .E, fx := true }
                   else s
                 else if topInternal woy && oy.wIn.isE && oy.wCarry.isOff && !s.fy then
                   { iX := .E, iY := .P (inV c ox.wIn) (inT ox.wIn), fx := true, fy := true }
                 else if oy.wIn.isS && oy.wCarry.isOff then
                   { s with iX := .S (inV c ox.wIn) (inT ox.wIn), fx := true }
                 else s
               else s
      let acc := !s.fy && wo1 && oy.wIn.isE && oy.wCarry.isOff
      let s := if acc then { s with iY := .P (outV c ox.wOut) (outT ox.wOut), fy := true } else s
      (s, acc)
  wi

/-- The writer-output rows (`wo`) of `liveTopPair`, verbatim; `acceptWO` read from `liveTopWI`. -/
def liveTopWO (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) : OutTok c.topA × OutTok c.topA :=
  let a := c.topA
  let wox : Agent c := { ox with beta := betaX }
  let woy : Agent c := { oy with beta := betaY }
  let rootX := ox.l
  let rootY := oy.l
  let wTerminal := topTerminal wox woy
  let qTerminal := topTerminal ox oy
  let wc2Live := ox.wCarry.isW && !wTerminal
  let wc2Success := wc2Live && oy.wCarry.isOff && oy.wIn.isS
  let wc3 := topBorder wox && ox.wCarry.isOff && ox.wIn.isS && !rootY
  let qc2Live := ox.qCarry.isL && !qTerminal
  let qc2Success := qc2Live && oy.qCarry.isOff && oy.qIn.isS
  let qc3 := topBorder ox && ox.qCarry.isOff && ox.qIn.isS && !rootY
  let wo1 := ox.wOut.isD && woy.beta
  let qo1 := ox.qOut.isD && oy.beta
  let acceptWO := (liveTopWI c ox oy betaX betaY).2
  let wo : OutTok c.topA × OutTok c.topA :=
    if rootX || rootY then (.E, .E)
    else if wo1 then
      (if acceptWO then ((if outT ox.wOut then .U else .E), oy.wOut) else (ox.wOut, oy.wOut))
    else if ox.wOut.isD && !woy.beta && oy.wOut.isE then
      ((if outT ox.wOut then .U else .E), .D (outV c ox.wOut) (outT ox.wOut))
    else if ox.wOut.isU then (.D ox.d wox.beta, oy.wOut)
    else if wox.beta && ox.wOut.isE && !rootX then (.U, oy.wOut)
    else (ox.wOut, oy.wOut)
  wo

/-- The checker-carry rows (`qcr`) of `liveTopPair`, verbatim with their look flags. -/
def liveTopQC (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) : QCarry × QCarry × Bool :=
  let a := c.topA
  let wox : Agent c := { ox with beta := betaX }
  let woy : Agent c := { oy with beta := betaY }
  let rootX := ox.l
  let rootY := oy.l
  let wTerminal := topTerminal wox woy
  let qTerminal := topTerminal ox oy
  let wc2Live := ox.wCarry.isW && !wTerminal
  let wc2Success := wc2Live && oy.wCarry.isOff && oy.wIn.isS
  let wc3 := topBorder wox && ox.wCarry.isOff && ox.wIn.isS && !rootY
  let qc2Live := ox.qCarry.isL && !qTerminal
  let qc2Success := qc2Live && oy.qCarry.isOff && oy.qIn.isS
  let qc3 := topBorder ox && ox.qCarry.isOff && ox.qIn.isS && !rootY
  let wo1 := ox.wOut.isD && woy.beta
  let qo1 := ox.qOut.isD && oy.beta
  let qcr : QCarry × QCarry × Bool :=
    if rootX || rootY then
      ((if ox.qCarry.isL then .OFF else ox.qCarry), (if oy.qCarry.isL then .OFF else oy.qCarry),
       false)
    else if ox.qCarry.isL then
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
  qcr

/-- The checker-input rows (`qi`) of `liveTopPair`, verbatim with their look flags. -/
def liveTopQI (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) : InSt c.topA × Bool :=
  let a := c.topA
  let wox : Agent c := { ox with beta := betaX }
  let woy : Agent c := { oy with beta := betaY }
  let rootX := ox.l
  let rootY := oy.l
  let wTerminal := topTerminal wox woy
  let qTerminal := topTerminal ox oy
  let wc2Live := ox.wCarry.isW && !wTerminal
  let wc2Success := wc2Live && oy.wCarry.isOff && oy.wIn.isS
  let wc3 := topBorder wox && ox.wCarry.isOff && ox.wIn.isS && !rootY
  let qc2Live := ox.qCarry.isL && !qTerminal
  let qc2Success := qc2Live && oy.qCarry.isOff && oy.qIn.isS
  let qc3 := topBorder ox && ox.qCarry.isOff && ox.qIn.isS && !rootY
  let wo1 := ox.wOut.isD && woy.beta
  let qo1 := ox.qOut.isD && oy.beta
  let qi : InSt c.topA × Bool :=
    if rootX || rootY then ({ iX := .E, iY := .E, fx := true, fy := true }, false)
    else
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
  qi

/-- The checker-output rows (`qo`) of `liveTopPair`, verbatim; `acceptQO` read from `liveTopQI`. -/
def liveTopQO (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) : OutTok c.topA × OutTok c.topA :=
  let a := c.topA
  let wox : Agent c := { ox with beta := betaX }
  let woy : Agent c := { oy with beta := betaY }
  let rootX := ox.l
  let rootY := oy.l
  let wTerminal := topTerminal wox woy
  let qTerminal := topTerminal ox oy
  let wc2Live := ox.wCarry.isW && !wTerminal
  let wc2Success := wc2Live && oy.wCarry.isOff && oy.wIn.isS
  let wc3 := topBorder wox && ox.wCarry.isOff && ox.wIn.isS && !rootY
  let qc2Live := ox.qCarry.isL && !qTerminal
  let qc2Success := qc2Live && oy.qCarry.isOff && oy.qIn.isS
  let qc3 := topBorder ox && ox.qCarry.isOff && ox.qIn.isS && !rootY
  let wo1 := ox.wOut.isD && woy.beta
  let qo1 := ox.qOut.isD && oy.beta
  let acceptQO := (liveTopQI c ox oy betaX betaY).2
  let qo : OutTok c.topA × OutTok c.topA :=
    if rootX || rootY then (.E, .E)
    else if qo1 then
      (if acceptQO then ((if outT ox.qOut then .U else .E), oy.qOut) else (ox.qOut, oy.qOut))
    else if ox.qOut.isD && !oy.beta && oy.qOut.isE then
      ((if outT ox.qOut then .U else .E), .D (outV c ox.qOut) (outT ox.qOut))
    else if ox.qOut.isU then (.D ox.d ox.beta, oy.qOut)
    else if ox.beta && ox.qOut.isE && !rootX then (.U, oy.qOut)
    else (ox.qOut, oy.qOut)
  qo

theorem liveTopPair_x_wCarry (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).x.wCarry = (liveTopWC c ox oy betaX betaY).1 := rfl

theorem liveTopPair_y_wCarry (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).y.wCarry = (liveTopWC c ox oy betaX betaY).2.1 := rfl

theorem liveTopPair_x_wIn (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).x.wIn = (liveTopWI c ox oy betaX betaY).1.iX := rfl

theorem liveTopPair_y_wIn (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).y.wIn = (liveTopWI c ox oy betaX betaY).1.iY := rfl

theorem liveTopPair_x_wOut (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).x.wOut = (liveTopWO c ox oy betaX betaY).1 := rfl

theorem liveTopPair_y_wOut (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).y.wOut = (liveTopWO c ox oy betaX betaY).2 := rfl

theorem liveTopPair_x_qCarry (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).x.qCarry = (liveTopQC c ox oy betaX betaY).1 := rfl

theorem liveTopPair_y_qCarry (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).y.qCarry = (liveTopQC c ox oy betaX betaY).2.1 := rfl

theorem liveTopPair_x_qIn (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).x.qIn = (liveTopQI c ox oy betaX betaY).1.iX := rfl

theorem liveTopPair_y_qIn (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).y.qIn = (liveTopQI c ox oy betaX betaY).1.iY := rfl

theorem liveTopPair_x_qOut (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).x.qOut = (liveTopQO c ox oy betaX betaY).1 := rfl

theorem liveTopPair_y_qOut (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).y.qOut = (liveTopQO c ox oy betaX betaY).2 := rfl


end L3

import Leader.L3.Top.SuffixFinalMobile

/-!
# Q7 (P.8): the source output rows of `liveTopPair`

Only the constructor of a source output token matters for delivery (`E`, `U`, `D`); the digit
and tail bit of a sampled packet are carried along.  This module abstracts a token to its
constructor and proves the row relation of the QO layer of `liveTopPair` on a root-free edge.

Consumer: `Leader/L3/TopPinnedSourceTrace.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The constructor of a source output token.

Consumer: `qo_internal`. -/
inductive SrcTok : Type
  | e | u | d
  deriving DecidableEq

/-- The constructor of an output token.

Consumer: `qo_internal`. -/
def srcTok {a : Nat} : OutTok a → SrcTok
  | .E => .e
  | .U => .u
  | .D _ _ => .d

/-- Token constructor, empty.

Consumer: `qo_internal`. -/
@[simp] theorem srcTok_E {a : Nat} : srcTok (OutTok.E : OutTok a) = .e := rfl

/-- Token constructor, waiting.

Consumer: `qo_internal`. -/
@[simp] theorem srcTok_U {a : Nat} : srcTok (OutTok.U : OutTok a) = .u := rfl

/-- Token constructor, sampled.

Consumer: `qo_internal`. -/
@[simp] theorem srcTok_D {a : Nat} (v : Fin a) (t : Bool) : srcTok (OutTok.D v t) = .d := rfl

/-- What a departing packet leaves behind.

Consumer: `qo_internal`. -/
theorem srcTok_tail {a : Nat} (t : Bool) :
    srcTok (if t = true then (OutTok.U : OutTok a) else .E) = .e ∨
    srcTok (if t = true then (OutTok.U : OutTok a) else .E) = .u := by
  cases t <;> simp

/-- **QO rows on an internal edge** (the responder is not a marker).  A sampled packet moves into
an empty slot and leaves `E` or `U`; a waiting-to-sample slot samples; an empty marker becomes
waiting; every other case is the frame.

Consumer: `Leader/L3/TopPinnedSourceTrace.lean`. -/
theorem qo_internal (c : Compiled) (x y : Agent c) (bx bY : Bool)
    (hxl : x.l = false) (hyl : y.l = false) (hyb : y.beta = false) :
    (srcTok x.qOut = .d → srcTok y.qOut = .e →
      (srcTok (liveTopPair c x y bx bY).x.qOut = .e ∨ srcTok (liveTopPair c x y bx bY).x.qOut = .u) ∧
      srcTok (liveTopPair c x y bx bY).y.qOut = .d) ∧
    (srcTok x.qOut = .u →
      srcTok (liveTopPair c x y bx bY).x.qOut = .d ∧
      srcTok (liveTopPair c x y bx bY).y.qOut = srcTok y.qOut) ∧
    (srcTok x.qOut = .e → x.beta = true →
      srcTok (liveTopPair c x y bx bY).x.qOut = .u ∧
      srcTok (liveTopPair c x y bx bY).y.qOut = srcTok y.qOut) ∧
    (srcTok x.qOut = .d → srcTok y.qOut ≠ .e →
      srcTok (liveTopPair c x y bx bY).x.qOut = .d ∧
      srcTok (liveTopPair c x y bx bY).y.qOut = srcTok y.qOut) ∧
    (srcTok x.qOut = .e → x.beta = false →
      srcTok (liveTopPair c x y bx bY).x.qOut = .e ∧
      srcTok (liveTopPair c x y bx bY).y.qOut = srcTok y.qOut) := by
  rcases hx : x.qOut with _ | _ | ⟨v, t⟩ <;> rcases hy : y.qOut with _ | _ | ⟨w, u⟩ <;>
    cases hb : x.beta <;>
    simp [liveTopPair, hxl, hyl, hyb, hx, hy, hb, srcTok_tail, OutTok.isD, OutTok.isU, OutTok.isE,
      topTerminal, topInternal, topBorder, QCarry.isOff, QCarry.isL, WCarry.isOff, WCarry.isW,
      InTok.isS, InTok.isE, InTok.isX, InTok.isP, outT, outV]

/-- **QO rows on a terminal edge** (the responder is a marker).  The responder's output is
framed; a sampled packet is accepted or kept; a waiting slot samples; an empty marker becomes
waiting.

Consumer: `Leader/L3/TopPinnedSourceTrace.lean`. -/
theorem qo_terminal (c : Compiled) (x y : Agent c) (bx bY : Bool)
    (hxl : x.l = false) (hyl : y.l = false) (hyb : y.beta = true) :
    (liveTopPair c x y bx bY).y.qOut = y.qOut ∧
    (srcTok x.qOut = .u → srcTok (liveTopPair c x y bx bY).x.qOut = .d) ∧
    (srcTok x.qOut = .e → x.beta = true → srcTok (liveTopPair c x y bx bY).x.qOut = .u) ∧
    (srcTok x.qOut = .e → x.beta = false → srcTok (liveTopPair c x y bx bY).x.qOut = .e) := by
  rcases hx : x.qOut with _ | _ | ⟨v, t⟩ <;> cases hb : x.beta <;>
    simp [liveTopPair, hxl, hyl, hyb, hx, hb, OutTok.isD, OutTok.isU, OutTok.isE,
      topTerminal, topInternal, topBorder, QCarry.isOff, QCarry.isL, WCarry.isOff, WCarry.isW,
      InTok.isS, InTok.isE, InTok.isX, InTok.isP, outT, outV]

/-- **A sampled packet offered to an empty carry-free marker input is accepted.**  The source
slot is left `U` after a tail and `E` otherwise, and the responder input becomes the pending
packet.

Consumer: `Leader/L3/TopPinnedSourceTrace.lean`. -/
theorem qo_accept (c : Compiled) (x y : Agent c) (bx bY : Bool)
    (hxl : x.l = false) (hyl : y.l = false) (hyb : y.beta = true)
    (v : Fin c.topA) (t : Bool) (hxo : x.qOut = .D v t)
    (hyi : y.qIn = .E) (hyc : y.qCarry = .OFF) :
    (liveTopPair c x y bx bY).x.qOut = (if t = true then .U else .E) ∧
    (liveTopPair c x y bx bY).y.qIn = .P v t := by
  rcases hxi : x.qIn with _ | _ | ⟨w, u⟩ | ⟨w, u⟩ <;> rcases hxc : x.qCarry with _ | ⟨p, q⟩ <;>
    cases hb : x.beta <;>
    simp [liveTopPair, hb, hxl, hyl, hyb, hxo, hyi, hyc, hxi, hxc, OutTok.isD, OutTok.isU,
      OutTok.isE, topTerminal, topInternal, topBorder, QCarry.isOff, QCarry.isL, WCarry.isOff,
      WCarry.isW, InTok.isS, InTok.isE, InTok.isX, InTok.isP, outT, outV, inT, inV] <;>
    (try (cases u <;> simp_all)) <;> (try (cases t <;> simp_all))

end MarkedCells
end L3

#print axioms L3.MarkedCells.qo_internal
#print axioms L3.MarkedCells.qo_terminal
#print axioms L3.MarkedCells.qo_accept
#print axioms L3.MarkedCells.srcTok_tail

import Leader.Core.Basic
import Leader.L3.Base

/-!
# The L3 protocol

`transition c x y` is `pairFull` (`composed-full.mjs:744-757`): on the selected pair (initiator `x`,
responder `y`) it runs, all from the OLD records,
* the certificate owner `certificateStep` (serializer, SI, LIVE-TOP, raw D1, lease; `711-743`),
* the base owner `baseStep` with the certificate's DCC event (`composed-gpt.mjs:334-397`),
* the anchorless H/K owner `hKStep` (`481-505`),
and assembles the result as `Object.assign({}, base, cert, hk)`.  The three owners write disjoint
namespaces: `certificateStep` writes the `extendAgent` fields (`217-227`) except `h, kH`, which
`hKStep` writes; `baseStep` writes the remaining (native, PACK, BANK, SMALL, token, candidate and
debt) fields.  Each owner copies every field it does not write from the OLD record, so the
assembly below takes each field from its owner.  The transition does not depend on `n`.

`protocol q` is the population protocol of advice `q` with leader output `l`.
-/

namespace L3

set_option autoImplicit false

/-- `Object.assign({}, base, cert, hk)` of `composed-full.mjs:753-754`. -/
def assemble {c : Compiled} (base cert hk : Agent c) : Agent c :=
  { base with
    u := cert.u
    beta := cert.beta
    d := cert.d
    ser := cert.ser
    siLease := cert.siLease
    si := cert.si
    rawKick := cert.rawKick
    rawTok := cert.rawTok
    h := hk.h
    kH := hk.kH
    wBase := cert.wBase
    wOut := cert.wOut
    wIn := cert.wIn
    wCarry := cert.wCarry
    qOut := cert.qOut
    qIn := cert.qIn
    qCarry := cert.qCarry
    topDirty := cert.topDirty }

/-- `pairFull` (`composed-full.mjs:744-757`). -/
def transition (c : Compiled) (x y : Agent c) : Agent c × Agent c :=
  let (cx, cy, ev) := certificateStep c x y
  let (bx, bY) := baseStep c ev x y
  let (hx, hy) := hKStep c x y
  (assemble bx cx hx, assemble bY cy hy)

/-- The L3 protocol for advice `q` (production compile, `composed-full.mjs:172`). -/
def protocol (q : Nat) : PopulationProtocol where
  Q := Agent (compileAdvice q)
  Y := Bool
  transition := transition (compileAdvice q)
  output := fun a => a.l

/-- The selected edge `e` has initiator `e` and responder `e + 1 mod n` (`main.tex:260-262`). -/
theorem rightNeighbor_val {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    (ring.rightNeighbor i).val = (i.val + 1) % n := rfl

end L3

import Leader.L3.Primitive.TapPoly

/-!
# L3 compiled parameters

Transcription of the production compiler of
`research/method-review/l3-machine/composed-full.mjs` (EXEC10, linear BANK lease):
`ceilLog2`/`floorLog2` (lines 47-48), `sourceTOfQ`/`paddedS` (50-51), `kappaDot` (92),
`finiteCertWidth`/`finiteKappa`/`productionKappa` (98-100), the pinned constants
`PRODUCTION_Q_STAR = 79` and `PRODUCTION_K_STAR = 199` (101-102), `compileCore` (111-170) and
`compileAdvice` (172-191), together with the tap table of `recurrence-taps.mjs` (lines 18-24).

Only the data `q, t, s, kappa, taps` is stored; every other compiled quantity is a definition
of these, exactly as `compileCore` computes it.  The compile-time assertions of `compileCore`
(`K < 2^b`, `1 ≤ K ≤ K_*` on the SMALL band, existence of taps) are not built into the type;
they are lemmas to be proved where they are consumed.

The JS rejects `t > 17` (no tap entry).  Here `tapTable t` keeps the literal strings of
`recurrence-taps.mjs` for `t ≤ 17` and, for `t ≥ 18`, the lower `t` bits of the first passing odd
mask found by the finite search `tapSearchFuel` of `TapPoly` (main.tex rem:primitive-taps,
R-TAPS); `TapTablePrimitive.tapTablePrimitive` proves the companion map primitive at every
width `t ≥ 2`.
-/

namespace L3

set_option autoImplicit false

/-- `ceil(log2 m)` for `m ≥ 1` (`composed-full.mjs:47`); `0` at `m = 0`, where the JS asserts. -/
def ceilLogTwo (m : Nat) : Nat :=
  if m ≤ 1 then 0 else Nat.log2 (m - 1) + 1

/-- `floor(log2 m)` (`composed-full.mjs:48`). -/
def floorLogTwo (m : Nat) : Nat := Nat.log2 m

/-- Source width `psi = ceil(log2 q)` (`composed-full.mjs:50`). -/
def sourceTOfQ (q : Nat) : Nat := ceilLogTwo q

/-- Padded width `s = max 2 t` (`composed-full.mjs:51`). -/
def paddedS (t : Nat) : Nat := max 2 t

/-- EXEC10 threshold above the finite band (`composed-full.mjs:92`):
`kappa(s) = ceil(log2 (A_s + 1))` with `A_s = 557 s + 119981` for `s ≥ 7`. -/
def kappaDot (s : Nat) : Nat :=
  if s = 2 then 14
  else if s = 3 then 15
  else if s = 4 then 15
  else if s = 5 then 14
  else if s ≤ 5 then 29
  else if s = 6 then 18
  else ceilLogTwo (557 * s + 119981 + 1)

/-- EXEC9 certificate width for `3 ≤ q ≤ 32` (`composed-full.mjs:98`). -/
def finiteCertWidth (q : Nat) : Nat :=
  if q ≤ 4 then 2 else if q ≤ 16 then 3 else 5

/-- EXEC9 threshold pin for `2 ≤ q ≤ 32` (`composed-full.mjs:99`). -/
def finiteKappa (q : Nat) : Nat :=
  if q ≤ 4 then 14
  else if q = 5 then 15
  else if q ≤ 11 then 14
  else if q ≤ 16 then 13
  else 14

/-- `composed-full.mjs:100`. -/
def productionKappa (q : Nat) : Nat :=
  if q ≤ 32 then finiteKappa q else kappaDot (paddedS (sourceTOfQ q))

/-- `PRODUCTION_Q_STAR` (`composed-full.mjs:101`). -/
def qStar : Nat := 79

/-- `PRODUCTION_K_STAR`, the physical SMALL carrier capacity (`composed-full.mjs:102`). -/
def kStar : Nat := 199

/-- Primitive tap strings of `recurrence-taps.mjs:18-24` for `t ≤ 17` (character `j` is `b_j`),
and for `t ≥ 18` the bits `b_0, ..., b_{t-1}` of the first passing odd mask of the finite search
`tapSearchFuel` (R-TAPS). -/
def tapTable (t : Nat) : List Bool :=
  if t ≤ 17 then
    let s : String :=
      match t with
      | 2 => "11" | 3 => "110" | 4 => "1100" | 5 => "10100"
      | 6 => "100001" | 7 => "1000001" | 8 => "10001110" | 9 => "100001000"
      | 10 => "1000000100" | 11 => "10000000010" | 12 => "100000101001"
      | 13 => "1000000001101" | 14 => "10000000010101"
      | 15 => "100000000000001" | 16 => "1000000000010110"
      | 17 => "10010000000000000"
      | _ => ""
    s.toList.map (· == '1')
  else
    (List.range t).map (fun j => Nat.testBit (tapSearchFuel t 0 1 (2 ^ t)) j)

/-- The compiled data of one advice value.  `t` is the certificate (source) width, `s` the padded
width, `taps j` the recurrence tap `b_j` for `j < t`. -/
structure Compiled where
  q : Nat
  t : Nat
  s : Nat
  kappa : Nat
  taps : Nat → Bool

namespace Compiled

variable (c : Compiled)

/-- `K = 2q + kappa` (`composed-full.mjs:127`). -/
def K : Nat := 2 * c.q + c.kappa
/-- `b = s + 11` (`composed-full.mjs:129`). -/
def b : Nat := c.s + 11
/-- Binary digits of `K`, `theta_j = floor(K / 2^j) mod 2` for `j < b` (`composed-full.mjs:132`). -/
def theta (j : Nat) : Bool := (c.K / 2 ^ j) % 2 == 1
/-- SMALL band selection `q ≤ q_*` (`composed-full.mjs:145`). -/
def useSmall : Bool := decide (c.q ≤ qStar)
/-- LIVE-TOP radix `a = 2^floor(log2 s)` (`composed-full.mjs:155`). -/
def topA : Nat := 2 ^ floorLogTwo c.s
/-- Serializer lease maximum `8t + 4` (`composed-full.mjs:157`). -/
def siLeaseMax : Nat := 8 * c.t + 4
/-- BANK lease cap `Lambda = 13 (b + 2)` (`composed-full.mjs:166`). -/
def bankLeaseCap : Nat := 13 * (c.b + 2)

theorem topA_pos : 0 < c.topA := Nat.two_pow_pos _

end Compiled

/-- Production compile of advice `q` (`composed-full.mjs:172-191`): width `2` at `q = 2`
(the Q2-SI2 fallback), the EXEC9 finite width for `q ≤ 32`, else `ceil(log2 q)`. -/
def compileAdvice (q : Nat) : Compiled :=
  let t0 := sourceTOfQ q
  let t := if t0 = 1 then 2 else if q ≤ 32 then finiteCertWidth q else t0
  { q := q
    t := t
    s := paddedS t0
    kappa := productionKappa q
    taps := fun j => (tapTable t).getD j false }

end L3

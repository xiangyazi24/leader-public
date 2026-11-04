import Leader.PPL.Transition

/-!
# P_PL v2 predicates

Literal finite predicates used by the frozen P_PL proof architecture.
All definitions follow arXiv:2305.08375v2 and are executable/decidable.
The rooted predicates rotate the paper's WLOG unique leader u_0 to an
explicit `root : Fin n`.
-/

namespace PPL

set_option autoImplicit false

abbrev Config (n psi kappa : Nat) :=
  (protocol psi kappa).Configuration n

/-! ## Cyclic positions and nearest leaders -/

def shiftRight {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) : Fin n :=
  ⟨(i.val + d) % n, Nat.mod_lt _ ring.hn⟩

def shiftLeft {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) : Fin n :=
  ⟨(i.val + n - d % n) % n, Nat.mod_lt _ ring.hn⟩

def cyclicOffset {n : Nat} (ring : DirectedRing n)
    (root i : Fin n) : Nat :=
  (i.val + n - root.val) % n

def scanDistance {n : Nat} (site : Nat → Fin n)
    (hit : Fin n → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, d =>
      if hit (site d) = true then some d
      else scanDistance site hit fuel (d + 1)

def dLLBy {n : Nat} (ring : DirectedRing n)
    (leader : Fin n → Bool) (i : Fin n) : Option Nat :=
  scanDistance (fun d => shiftLeft ring i d) leader n 0

def dRLBy {n : Nat} (ring : DirectedRing n)
    (leader : Fin n → Bool) (i : Fin n) : Option Nat :=
  scanDistance (fun d => shiftRight ring i d) leader n 0

/-- Distance to the nearest leader to the left; `none` is infinity.
Paper `paper.txt:319-321`. -/
def dLL {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) (i : Fin n) : Option Nat :=
  dLLBy ring (fun j => (C j).leader) i

/-- Distance to the nearest leader to the right; `none` is infinity.
Paper `paper.txt:319-321`. -/
def dRL {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) (i : Fin n) : Option Nat :=
  dRLBy ring (fun j => (C j).leader) i

/-! ## Perfect configurations -/

def IsBorder {n psi kappa : Nat}
    (C : Config n psi kappa) (i : Fin n) : Prop :=
  (C i).dist.val = 0 ∨ (C i).dist.val = psi

def isBorderBool {n psi kappa : Nat}
    (C : Config n psi kappa) (i : Fin n) : Bool :=
  (C i).dist.val == 0 || (C i).dist.val == psi

def nextBorderDistance {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (i : Fin n) : Nat :=
  match scanDistance (fun d => shiftRight ring i d)
      (isBorderBool C) n 1 with
  | some d => d
  | none => n

def prevBorderDistance {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (i : Fin n) : Nat :=
  match scanDistance (fun d => shiftLeft ring i d)
      (isBorderBool C) n 1 with
  | some d => d
  | none => n

def segmentIdAux {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (start : Fin n) : Nat → Nat → Nat
  | 0, _ => 0
  | len + 1, j =>
      (if (C (shiftRight ring start j)).id = true then 2 ^ j else 0) +
        segmentIdAux ring C start len (j + 1)

def segmentIdFrom {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (start : Fin n) (len : Nat) : Nat :=
  segmentIdAux ring C start len 0

/-- Literal Perfect: equations (1) and (2), with segment IDs modulo `2^psi`
and distance arithmetic modulo `2*psi`. No other state field occurs.
Paper `paper.txt:393-410`. -/
def Perfect {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  (∀ i : Fin n,
      (C i).dist.val =
        if (C i).leader = true then 0
        else ((C (shiftLeft ring i 1)).dist.val + 1) % (2 * psi)) ∧
    ∀ i : Fin n, IsBorder C i →
      let dn := nextBorderDistance ring C i
      let dp := prevBorderDistance ring C i
      let e := shiftRight ring i dn
      let p := shiftLeft ring i dp
      (C i).leader = true ∨ (C e).leader = true ∨
        segmentIdFrom ring C i dn =
          (segmentIdFrom ring C p dp + 1) % (2 ^ psi)

instance instDecidablePerfect {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa) :
    Decidable (Perfect ring C) := by
  unfold Perfect IsBorder
  infer_instance

/-! ## Peaceful bullets and C_PB -/

def PeacefulCore {n : Nat} (ring : DirectedRing n)
    (leader shield signalB : Fin n → Bool) (i : Fin n) : Prop :=
  match dLLBy ring leader i with
  | none =>
      ∀ j : Fin n, signalB j = false
  | some d =>
      shield (shiftLeft ring i d) = true ∧
        ∀ j : Fin (d + 1), signalB (shiftLeft ring i j.val) = false

instance instDecidablePeacefulCore {n : Nat}
    (ring : DirectedRing n) (leader shield signalB : Fin n → Bool)
    (i : Fin n) :
    Decidable (PeacefulCore ring leader shield signalB i) := by
  unfold PeacefulCore
  cases h : dLLBy ring leader i with
  | none => infer_instance
  | some d => infer_instance

/-- A live bullet at `i` is peaceful when its nearest left leader is
shielded and the whole intervening counterclockwise path has `signalB=0`;
with no leader, this means no `signalB` anywhere.
Paper `paper.txt:966-969`. The predicate itself does not require
`bullet=2`; `CPB` supplies that antecedent. -/
def Peaceful {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) (i : Fin n) : Prop :=
  PeacefulCore ring
    (fun j => (C j).leader)
    (fun j => (C j).shield)
    (fun j => (C j).signalB) i

instance instDecidablePeaceful {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa) (i : Fin n) :
    Decidable (Peaceful ring C i) := by
  unfold Peaceful
  infer_instance

def CPBCore {n : Nat} (ring : DirectedRing n)
    (leader : Fin n → Bool) (bullet : Fin n → Fin 3)
    (shield signalB : Fin n → Bool) : Prop :=
  (∃ i : Fin n, leader i = true) ∧
    ∀ i : Fin n, bullet i = (2 : Fin 3) →
      PeacefulCore ring leader shield signalB i

/-- `C_PB`: at least one leader and every live bullet is peaceful.
Paper `paper.txt:1004`. -/
def CPB {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  CPBCore ring
    (fun i => (C i).leader)
    (fun i => (C i).bullet)
    (fun i => (C i).shield)
    (fun i => (C i).signalB)

instance instDecidableCPB {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa) :
    Decidable (CPB ring C) := by
  unfold CPB CPBCore
  infer_instance

/-! ## Rooted C_DL and rooted paper segments -/

def segmentCount (n psi : Nat) : Nat :=
  (n + psi - 1) / psi

def segmentLength (n psi seg : Nat) : Nat :=
  Nat.min ((seg + 1) * psi) n - seg * psi

def InSegment {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (psi seg : Nat) (i : Fin n) : Prop :=
  let off := cyclicOffset ring root i
  seg * psi ≤ off ∧ off < Nat.min ((seg + 1) * psi) n

instance instDecidableInSegment {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (psi seg : Nat) (i : Fin n) :
    Decidable (InSegment ring root psi seg i) := by
  unfold InSegment
  infer_instance

def rootedSegmentId {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (seg : Nat) : Nat :=
  segmentIdFrom ring C (shiftRight ring root (seg * psi))
    (segmentLength n psi seg)

/-- Rooted `C_DL`: `C_PB`, the unique leader is `root`, and `dist/last`
are the paper's canonical rooted values.
Paper `paper.txt:1027-1031`. -/
def CDLAt {n psi kappa : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa) : Prop :=
  CPB ring C ∧
    (∀ i : Fin n, (C i).leader = true ↔ i = root) ∧
    ∀ i : Fin n,
      let off := cyclicOffset ring root i
      let zeta := segmentCount n psi
      (C i).dist.val = off % (2 * psi) ∧
        ((C i).last = true ↔ psi * (zeta - 1) ≤ off)

instance instDecidableCDLAt {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) :
    Decidable (CDLAt ring root C) := by
  unfold CDLAt
  infer_instance

/-! ## Valid, correct, and risky tokens -/

def tokenAt {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) : Option (TokenData psi) :=
  match kind with
  | .black => q.tokenB
  | .white => q.tokenW

def tokenD' (psi : Nat) : TokenKind → Nat
  | .black => 0
  | .white => psi

def tokenCode {psi : Nat} (t : TokenData psi) :
    Fin (2 * psi - 1) :=
  t.1.1

def tokenBitBool {psi : Nat} (t : TokenData psi) : Bool :=
  t.1.2.val == 1

def tokenCarryBool {psi : Nat} (t : TokenData psi) : Bool :=
  t.2.val == 1

def tokenTargetCoordinate {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : TokenData psi) : Int :=
  (((q.dist.val : Nat) : Int) + decodeOffset psi (tokenCode t) +
      (((tokenD' psi kind : Nat)) : Int)) %
    (((2 * psi : Nat)) : Int)

/-- Literal Definition 3 validity for the selected black/white token at
agent `i`; `none` is not a valid token.
Paper `paper.txt:663-666`. -/
def ValidToken {n psi kappa : Nat} (kind : TokenKind)
    (C : Config n psi kappa) (i : Fin n) : Prop :=
  match tokenAt kind (C i) with
  | none => False
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      let target := tokenTargetCoordinate kind (C i) t
      (0 < c ∧ ((psi : Nat) : Int) ≤ target ∧
          target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
        (c < 0 ∧ 1 ≤ target ∧
          target ≤ (((psi - 1 : Nat)) : Int))

instance instDecidableValidToken {n psi kappa : Nat}
    (kind : TokenKind) (C : Config n psi kappa) (i : Fin n) :
    Decidable (ValidToken kind C i) := by
  unfold ValidToken
  cases h : tokenAt kind (C i) with
  | none => infer_instance
  | some t => dsimp; infer_instance

def tokenTargetSite {n psi : Nat} (ring : DirectedRing n)
    (i : Fin n) (t : TokenData psi) : Fin n :=
  let c := decodeOffset psi (tokenCode t)
  if 0 < c then shiftRight ring i c.toNat
  else shiftLeft ring i c.natAbs

def WorkingFor {n psi kappa : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa)
    (i : Fin n) (kind : TokenKind) (seg : Nat) : Prop :=
  match tokenAt kind (C i) with
  | none => False
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      let target := tokenTargetSite ring i t
      let zeta := segmentCount n psi
      0 < zeta ∧
        ((0 < c ∧
            InSegment ring root psi ((seg + 1) % zeta) target) ∨
          (c < 0 ∧ InSegment ring root psi seg target))

instance instDecidableWorkingFor {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (i : Fin n)
    (kind : TokenKind) (seg : Nat) :
    Decidable (WorkingFor ring root C i kind seg) := by
  unfold WorkingFor
  cases h : tokenAt kind (C i) with
  | none => infer_instance
  | some t => dsimp; infer_instance

def firstZeroAux {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (start : Fin n) : Nat → Nat → Nat
  | 0, j => j
  | fuel + 1, j =>
      if (C (shiftRight ring start j)).id = false then j
      else firstZeroAux ring C start fuel (j + 1)

def firstZeroBit {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (start : Fin n) : Nat :=
  firstZeroAux ring C start psi 0

def payloadCorrect {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (sourceStart : Fin n) (x : Nat) (t : TokenData psi) : Prop :=
  let j := firstZeroBit ring C sourceStart
  let sourceBit := (C (shiftRight ring sourceStart x)).id
  let expectedBit := if x ≤ j then !sourceBit else sourceBit
  let expectedCarry := if x < j then true else false
  tokenBitBool t = expectedBit ∧ tokenCarryBool t = expectedCarry

instance instDecidablePayloadCorrect {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (sourceStart : Fin n) (x : Nat) (t : TokenData psi) :
    Decidable (payloadCorrect ring C sourceStart x t) := by
  unfold payloadCorrect
  infer_instance

/-- Definition 6 correctness for a token at `i` relative to rooted interior
pair `(S_seg,S_(seg+1))`. As in the falsification checker, validity and
"working for" are antecedents supplied by `SPLAt`; this predicate checks the
color/round and payload equations themselves.
Paper `paper.txt:1048-1053`. -/
def CorrectToken {n psi kappa : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa)
    (i : Fin n) (kind : TokenKind) (seg : Nat) : Prop :=
  match tokenAt kind (C i) with
  | none => False
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      let sourceStart := shiftRight ring root (seg * psi)
      let target := tokenTargetSite ring i t
      let rel := cyclicOffset ring sourceStart target
      let parityOK :=
        match kind with
        | .black => seg % 2 = 0
        | .white => seg % 2 = 1
      parityOK ∧
        if 0 < c then
          psi ≤ rel ∧
            let x := rel - psi
            x < psi ∧ payloadCorrect ring C sourceStart x t
        else
          c < 0 ∧ 1 ≤ rel ∧
            let x := rel - 1
            x < psi ∧ payloadCorrect ring C sourceStart x t

instance instDecidableCorrectToken {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (i : Fin n)
    (kind : TokenKind) (seg : Nat) :
    Decidable (CorrectToken ring root C i kind seg) := by
  unfold CorrectToken
  cases kind with
  | black => cases tokenAt TokenKind.black (C i) <;> dsimp <;> infer_instance
  | white => cases tokenAt TokenKind.white (C i) <;> dsimp <;> infer_instance

def tokenRisky {n psi kappa : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa)
    (i : Fin n) (kind : TokenKind) : Prop :=
  match tokenAt kind (C i) with
  | none => False
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      0 < c ∧
        ∀ h : Fin (c.natAbs + 1),
          InSegment ring root psi 0 (shiftRight ring i h.val)

instance instDecidableTokenRisky {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (i : Fin n) (kind : TokenKind) :
    Decidable (tokenRisky ring root C i kind) := by
  unfold tokenRisky
  cases h : tokenAt kind (C i) with
  | none => infer_instance
  | some t => dsimp; infer_instance

/-- Rooted Definition 7: a token at `i` is risky when it moves right and
every site from its host through its target lies in rooted `S_0`.
Validity is deliberately *not* required.
Paper `paper.txt:1072-1075`. -/
def Risky {n psi kappa : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa) (i : Fin n) : Prop :=
  tokenRisky ring root C i .black ∨ tokenRisky ring root C i .white

instance instDecidableRisky {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (i : Fin n) :
    Decidable (Risky ring root C i) := by
  unfold Risky
  infer_instance

/-! ## S_PL -/

/-- Rooted Definition 8: `C_DL`, no risky token, and every interior segment
pair has successor ID with every valid working token correct.
Paper `paper.txt:1077-1081`. -/
def SPLAt {n psi kappa : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa) : Prop :=
  CDLAt ring root C ∧
    (∀ i : Fin n, ¬ Risky ring root C i) ∧
    ∀ seg : Fin (segmentCount n psi - 2),
      rootedSegmentId ring root C (seg.val + 1) =
          (rootedSegmentId ring root C seg.val + 1) % (2 ^ psi) ∧
        ∀ i : Fin n,
          ((ValidToken .black C i ∧
              WorkingFor ring root C i .black seg.val) →
              CorrectToken ring root C i .black seg.val) ∧
          ((ValidToken .white C i ∧
              WorkingFor ring root C i .white seg.val) →
              CorrectToken ring root C i .white seg.val)

instance instDecidableSPLAt {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) :
    Decidable (SPLAt ring root C) := by
  unfold SPLAt
  infer_instance

/-- Rotation-invariant `S_PL`: there is an explicit root witnessing the
paper's WLOG-`u_0` Definition 8.
Paper `paper.txt:1077-1081`; rooted form adopted in R6. -/
def SPL {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  ∃ root : Fin n, SPLAt ring root C

instance instDecidableSPL {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa) :
    Decidable (SPL ring C) := by
  unfold SPL
  infer_instance

/-! ## Literal four-field projection -/

abbrev FourField := Bool × Fin 3 × Bool × Bool
abbrev FourConfig (n : Nat) := Fin n → FourField

/-- Projection to exactly `(leader,bullet,shield,signalB)`, the four fields
used by Peaceful/`C_PB` and literal Algorithm 5.
Paper `paper.txt:956-973,966-1005`. -/
def view4 {psi kappa : Nat} (q : State psi kappa) : FourField :=
  (q.leader, q.bullet, q.shield, q.signalB)

/-- Four-field `PB`: the literal projection of `C_PB`.
Paper `paper.txt:966-1005`. -/
def PB {n : Nat} (ring : DirectedRing n) (D : FourConfig n) : Prop :=
  CPBCore ring
    (fun i => (D i).1)
    (fun i => (D i).2.1)
    (fun i => (D i).2.2.1)
    (fun i => (D i).2.2.2)

instance instDecidablePB {n : Nat}
    (ring : DirectedRing n) (D : FourConfig n) :
    Decidable (PB ring D) := by
  unfold PB CPBCore
  infer_instance

/-- The full-state `C_PB` predicate is definitionally its four-field
projection. This is the deterministic bridge shape frozen in R9/R10.
Paper `paper.txt:966-1005`. -/
theorem cpb_iff_pb_view4 {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa) :
    CPB ring C ↔ PB ring (view4 ∘ C) := by
  rfl

end PPL

#print axioms PPL.cpb_iff_pb_view4

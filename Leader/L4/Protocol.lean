/- Literal ordered pair table of the protocol (an independent transcription). -/
namespace L4

inductive Bullet where
  | none | dummy | live
  deriving Repr, DecidableEq, BEq

inductive Signal where
  | zero | one | two
  deriving Repr, DecidableEq, BEq

def Signal.max : Signal → Signal → Signal
  | .two, _ => .two
  | _, .two => .two
  | .one, _ => .one
  | _, .one => .one
  | .zero, .zero => .zero

inductive Source (Q : Nat) where
  | off | i0 | i1
  | count (k : Fin Q)
  | await (k : Fin Q)
  deriving Repr, DecidableEq, BEq

inductive Rail where
  | e | t | ui | uc | di | dc | x
  deriving Repr, DecidableEq, BEq

structure Site (p c1 : Nat) where
  residue : Fin p
  mark : Bool
  leader : Bool
  bullet : Bullet
  shield : Bool
  signal : Signal
  stock : Bool
  source : Source (2 * c1)
  rail : Rail
  deriving Repr, DecidableEq, BEq

abbrev State := Site

/-- The residue digit supplies a witness that the modulus is positive. -/
def nextResidue {p : Nat} (r : Fin p) : Fin p :=
  ⟨(r.val + 1) % p, Nat.mod_lt _ (Nat.zero_lt_of_lt r.isLt)⟩

def defect {p c1 : Nat} (u v : Site p c1) : Bool :=
  !(v.residue == nextResidue u.residue)

/-- R0, before native bullet impact. -/
def materialize {p c1 : Nat} (u v : Site p c1) : Site p c1 :=
  if v.leader || u.mark || defect u v then { u with mark := true } else u

/-- N0. -/
def fireInitiator {p c1 : Nat} (u : Site p c1) : Site p c1 :=
  if u.leader && !(u.signal == .zero) then
    { u with bullet := .live, shield := true, signal := .zero }
  else u

/-- N1. -/
def fireResponder {p c1 : Nat} (v : Site p c1) : Site p c1 :=
  if v.leader then
    match v.signal with
    | .zero => v
    | .one => { v with bullet := .dummy, shield := false, signal := .zero }
    | .two => { v with bullet := .live, shield := true, signal := .zero }
  else v

/-- N2. -/
def impact {p c1 : Nat} (u v : Site p c1) : Site p c1 × Site p c1 :=
  if !(u.bullet == .none) && v.leader then
    let v' := if u.bullet == .live && !v.shield then { v with leader := false } else v
    ({ u with bullet := .none }, v')
  else (u, v)

def pinned {p c1 : Nat} (u v : Site p c1) : Bool :=
  !v.leader && u.mark

/-- N4, using precisely the post-N2 N3 ghost latch. -/
def followerBullet {p c1 : Nat} (g : Bool) (u v : Site p c1) :
    Site p c1 × Site p c1 :=
  if !(u.bullet == .none) && !v.leader then
    let u' := { u with bullet := .none }
    if g then (u', v)
    else
      let b := if v.bullet == .none then u.bullet else v.bullet
      (u', { v with bullet := b, signal := .zero })
  else (u, v)

/-- Native N0–N5, operating after R0 has materialized the incoming mark. -/
def native {p c1 : Nat} (u v : Site p c1) : Site p c1 × Site p c1 :=
  let (u₂, v₂) := impact (fireInitiator u) (fireResponder v)
  let g := pinned u₂ v₂
  let (u₄, v₄) := followerBullet g u₂ v₂
  let emitted := if v₄.leader then Signal.one else if g then Signal.two else v₄.signal
  ({ u₄ with signal := Signal.max u₄.signal emitted }, v₄)

def payer {p c1 : Nat} (u : Site p c1) : Bool := u.stock || u.leader

/-- P0/P2/P3/P4, simultaneously repairing the incoming residue and moving the mark in P3. -/
def payment {p c1 : Nat} (u v : Site p c1) : Site p c1 × Site p c1 :=
  if v.leader then ({ u with mark := true, stock := false }, v)
  else if !u.mark && !v.stock && payer u then
    ({ u with stock := false }, { v with stock := true })
  else if u.mark && payer u then
    ({ u with mark := false, stock := false },
      { v with residue := nextResidue u.residue, mark := true })
  else (u, v)

def stepPrefix {p c1 : Nat} (u v : Site p c1) : Site p c1 × Site p c1 :=
  let (u', v') := native (materialize u v) v
  payment u' v'

structure Patrol (Q : Nat) where
  source : Source Q
  left : Rail
  right : Rail
  fire : Bool
  deriving Repr, DecidableEq, BEq

def returning : Rail → Bool
  | .di => true
  | .dc => true
  | _ => false

def waiting {Q : Nat} : Source Q → Bool
  | .i1 => true
  | .await _ => true
  | _ => false

/-- For the unused Q=0 completion A1 goes OFF; the stated table has Q≥24. -/
def firstCount (Q : Nat) : Source Q :=
  if h : 0 < Q then .count ⟨0, h⟩ else .off

/-- Group S. -/
def sourceGuard {Q : Nat} (pg : Bool) (a : Patrol Q) : Patrol Q :=
  if !pg then
    { a with source := .off, right := if a.source == .off then a.right else .x }
  else if a.source == .off then { a with source := .i0 }
  else a

/-- Group A, including immediate OFF and the terminal A2 latch. -/
def arrivals {Q : Nat} (root pg leader : Bool) (a : Patrol Q) : Patrol Q :=
  if a.left == .x && pg then { a with source := .i0, left := .e }
  else if a.left == .x && leader then { a with left := .e }
  else if a.source == .i1 && a.left == .di then
    { a with source := firstCount Q, left := .e }
  else
    match a.source, a.left with
    | .await k, .dc =>
      if h : k.val + 1 < Q then { a with source := .count ⟨k.val + 1, h⟩, left := .e }
      else { a with source := .off, left := .e, fire := true }
    | _, _ =>
      if root && returning a.left then { a with left := .e }
      else if waiting a.source && a.left == .e then { a with source := .i0 }
      else a

/-- Group L. -/
def launch {Q : Nat} (a : Patrol Q) : Patrol Q :=
  match a.source with
  | .i0 => { a with source := .i1, left := .ui }
  | .count k => { a with source := .await k, left := .uc }
  | _ => a

/-- Group T. -/
def turn {Q : Nat} (root : Bool) (a : Patrol Q) : Patrol Q :=
  if root then
    match a.right with
    | .ui => { a with right := .di }
    | .uc => { a with right := .dc }
    | .t => { a with right := .e }
    | _ => a
  else a

/-- Group M. -/
def move {Q : Nat} (root : Bool) (a : Patrol Q) : Patrol Q :=
  if root then a
  else
    match a.right with
    | .ui => { a with left := .ui, right := if a.left == .x then .x else .t }
    | .uc =>
      match a.left with
      | .e => { a with left := .uc, right := .t }
      | .t => { a with left := .uc, right := .t }
      | .di => { a with left := .uc, right := .di }
      | .dc => { a with left := .uc, right := .dc }
      | .x => { a with left := .uc, right := .x }
      | .ui => { a with right := .t }
      | .uc => { a with right := .t }
    | _ =>
      if returning a.left || a.left == .x then
        let right :=
          if a.right == .e || a.right == .t || (returning a.right && a.left == .x)
          then a.left else a.right
        { a with left := .e, right := right }
      else if a.left == .e && a.right == .t then { a with right := .e }
      else a

def patrol {Q : Nat} (root pg leader : Bool) (source : Source Q) (left right : Rail) : Patrol Q :=
  let a : Patrol Q := ⟨source, left, right, false⟩
  move root (turn root (launch (arrivals root pg leader (sourceGuard pg a))))

def patrolWrite {p c1 : Nat} (u v : Site p c1) (a : Patrol (2 * c1)) :
    Site p c1 × Site p c1 :=
  ({ u with rail := a.left }, { v with source := a.source, rail := a.right })

/-- Canonical P5, last. Stock is deliberately preserved. -/
def finishBirth {p c1 : Nat} (fire : Bool) (u v : Site p c1) :
    Site p c1 × Site p c1 :=
  if fire && pinned u v then
    (u, { v with leader := true, bullet := .none, shield := true, signal := .zero, source := .off })
  else (u, v)

/-- Literal composition on an ordered selected pair of endpoints. -/
def pairStep {p c1 : Nat} (u v : Site p c1) : Site p c1 × Site p c1 :=
  let (u', v') := stepPrefix u v
  let a := patrol (v'.leader || u'.mark) (pinned u' v') v'.leader v'.source u'.rail v'.rail
  let (u'', v'') := patrolWrite u' v' a
  finishBirth a.fire u'' v''

theorem pairStep_total {p c1 : Nat} (u v : Site p c1) :
    ∃ w : Site p c1 × Site p c1, pairStep u v = w :=
  ⟨pairStep u v, rfl⟩

end L4

import Leader.L4.BStarCustodyCuts

/-! Amended custody interface and closure only. This file does not
establish raw-start reachability. -/
namespace L4.PhysicalCustody
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart
open BStarH6Ordinal BStarCustodyCuts

def sigma : Nat := 2^22 + 14
def radiusTwo (s : Nat) : Nat := (2^s + s - 1) / s
def radWidth (s : Nat) : Nat := 2^s - 1
def streak (k : Nat) : Nat :=
  let l := ell (k+2)
  let x := sigma + 6*l + 100
  sigma + 6*l + 45 + 2*ell x

def rows (s : Nat) :
    LargeRows (production s (radiusTwo s) (ell (radiusTwo s+1))
      (streak s) (streak (radiusTwo s)) (radWidth s) (s+11) 2 12) :=
  bStar s (radiusTwo s) (ell (radiusTwo s+1)) (streak s) (streak (radiusTwo s))
    (radWidth s) (s+11) 2 12 (by decide)

abbrev Raw (s n : Nat) :=
  Fin n → LargeSite (production s (radiusTwo s) (ell (radiusTwo s+1))
    (streak s) (streak (radiusTwo s)) (radWidth s) (s+11) 2 12)

def rawNext (s : Nat) {n : Nat} : Raw s n → Fin n → Raw s n :=
  AllSizeS1Geometry.step (rows s)

def rawRun {s n : Nat} : Raw s n → List (Fin n) → Raw s n :=
  BStarResetSchedule.run (rawNext s)

structure CustodyWitness {s n : Nat} (x : Raw s n) where
  base : Raw s n
  initial : Raw s n
  u : List (Fin n)
  v : List (Fin n)
  past : List (Fin n)
  Q : Raw s n → Prop
  init : Q initial
  closed : ∀ y e, Q y → Q (rawNext s y e)
  fiber : ∀ y, Q y → ∀ i, BStarLongFixedRouting.Layout (rows s) base i = BStarLongFixedRouting.Layout (rows s) y i
  here : rawRun initial ((u++v)++past) = x
  hh : ∃ i, oldH6 (rows s) base i = true
  baseOffset : BStarClearanceOffset.correct (oldH6 (rows s) base) hh 5 base
  offset : BStarClearanceOffset.correct (oldH6 (rows s) base) hh 5 initial
  flags : ∀ i,
    (longGeometry (rows s) (base i)).inside =
      decide (oldOrdinal (rows s) base hh i < radWidth s) ∧
    (longGeometry (rows s) (base i)).last =
      decide (oldOrdinal (rows s) base hh i + 1 = radWidth s)
  notShort : ∀ i, oldH6 (rows s) base (rightNeighbor i) = true →
    radWidth s ≤ oldOrdinal (rows s) base hh i + 1
  heads : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside) = true
  cont : ∀ i, let g := oldPair (rows s) base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true
  packed : total (oldH6 (rows s) base) * radWidth s ≤ n
  upperWidth : ∀ i, oldH6 (rows s) base (rightNeighbor i) = true →
    oldOrdinal (rows s) base hh i + 1 ≤ 1024 * radWidth s
  widthRatio : ∀ e f,
    oldH6 (rows s) base (rightNeighbor e) = true →
    oldH6 (rows s) base (rightNeighbor f) = true →
    4 * (oldOrdinal (rows s) base hh e + 1) <
      81 * (oldOrdinal (rows s) base hh f + 1)
  charts : ∀ o : BStarAcquireLiteralChain.Owners (oldH6 (rows s) base),
    ∃ (S : List (BStarAcquireVisitOrder.Pos n)) (len : Nat)
      (fallback : BStarAcquireVisitOrder.Pos n),
      BStarResetChartTouch.Chart (show 0 < 2 by decide) base hh o S len fallback
  cuts : CutFacts (show 0 < 2 by decide) base initial u v
  coherent : ∀ y, Q y → ∀ i,
    BStarLongGrant.conflict (BStarGrantReaderHistory.ports y i) = false

def Custody {s n : Nat} (x : Raw s n) : Prop := Nonempty (CustodyWitness x)

/-- The historical origin, base, and common recovery cuts are kept.
Only the actual raw letter is appended to the witness's past. -/
theorem custody_closed {s n : Nat} {x : Raw s n} (e : Fin n)
    (H : Custody x) : Custody (rawNext s x e) := by
  obtain ⟨g⟩ := H
  refine ⟨{g with past := g.past++[e], here := ?_}⟩
  unfold rawRun
  rw [←List.append_assoc,BStarResetSchedule.run_append]
  change rawNext s (rawRun g.initial ((g.u++g.v)++g.past)) e=_
  rw [g.here]

end L4.PhysicalCustody


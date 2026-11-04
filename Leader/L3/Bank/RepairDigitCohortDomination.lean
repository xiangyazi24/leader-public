import Leader.L3.Bank.RepairDigitFinalRows
import Leader.L3.Bank.RepairDigitCohortTail

/-!
# T22 task B (T21 step 3): the post-strict cohort dominates the clean grid

One complete pair `[source, target)`, `[target, target + R)` and one lane (writer or comparison;
the shapes are lane generic). Linear cells `q < 2R`: cell `q < R` is the output register of the
source site `source + q`; cell `q ≥ R` is the input register and carry-live bit of the target
site `source + q`. Edge `k` is the literal interaction of the sites of cells `k` and `k + 1`:

* `k + 1 < R`: output motion, `bankRepairDigitPipeStep` (T18, = `liveTopPair`);
* `k + 1 = R`: delivery into the target delimiter, `bankRepairDigitDelStep` (T18);
* `R ≤ k`, `k + 1 < 2R`: input motion, `bankRepairDigitFinStep` (T18);
* `k + 1 = 2R`: the terminal edge into the next delimiter, `cohortTermStep`
  (`cohortWriterTermRow`, `cohortComparisonTermRow` below, = `liveTopPair`);
* every other edge leaves these registers unchanged (T18 `bankRepairDigitEntryRow` for the edge
  into the source delimiter).

Packet `i < R` of the chosen cohort is the sample of source offset `R - 1 - i`; its `R` hops end
at target offset `R - 1 - i`; packet `R - 1` is the tail. A proof-only ghost `lam i` counts the
completed hops; it advances exactly when the literal row moves the packet (the cell ahead is
empty). `CohortPostStrict` is the post-strict class of repair.tex Lemma e-current for this
cohort, after the previous cohort's terminal completion and after the cohort's unread slots have
materialized: the packets sit at `R - 1 - i + lam i`, only empty cells lie between and ahead of
them, no carry is live, a settled operand only sits at its destination. Cells behind the tail
are unconstrained (younger cohorts).

Readiness is the clean grid's `lam i < lam (i - 1)`: no index shift is needed, because packet
`i - 1` starts one cell ahead of packet `i` and every hop is the same one-cell exclusion.
-/

namespace L3.CohortDomination

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortTail
open FiniteUniformStoppingTree
open LeaderCountDyadicTail
open K2ArbitraryElimination.FiniteAccounting

/-! ### The terminal row -/

/-- One lane across the terminal edge from an internal `x` into the next delimiter: new
`(input x, live x)`. -/
def cohortTermStep (ix : BankRepairDigitInSh) (kx : Bool) : BankRepairDigitInSh × Bool :=
  if kx then (.E, false)
  else
    match ix with
    | .E => (.E, false)
    | .X => (.E, false)
    | .S T => ((if T then .X else .S T), false)
    | .P T => ((if T then .E else .S false), false)

-- Both rows read only the input and carry lanes of `x`: rewrite to those lane blocks
-- (`LiveTopBlocks`) before the case split, and do not split the output token, which these lanes
-- do not read (unfolding all of `liveTopPair` in every case took 127 s and 134 s).
theorem cohortWriterTermRow (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hbx : ox.beta = false) (hby : oy.beta = true) :
    (bankRepairDigitInShOf (liveTopPair c ox oy).x.wIn, (liveTopPair c ox oy).x.wCarry.isW) =
      cohortTermStep (bankRepairDigitInShOf ox.wIn) ox.wCarry.isW := by
  rw [liveTopPair_x_wIn, liveTopPair_x_wCarry]
  rcases hi : ox.wIn with _ | _ | ⟨v, _ | _⟩ | ⟨v, _ | _⟩ <;> cases hc : ox.wCarry <;>
    cases hi2 : oy.wIn <;> cases hc2 : oy.wCarry <;>
    simp [liveTopWI, liveTopWC, hl, hly, hby, hbx, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, inV, outT,
      cohortTermStep, bankRepairDigitInShOf, WC, apply_ite InSt.iX, ite_self] <;>
    (repeat' split) <;> simp_all

theorem cohortComparisonTermRow (c : Compiled) (ox oy : Agent c)
    (hl : ox.l = false) (hly : oy.l = false) (hbx : ox.beta = false) (hby : oy.beta = true) :
    (bankRepairDigitInShOf (liveTopPair c ox oy).x.qIn, (liveTopPair c ox oy).x.qCarry.isL) =
      cohortTermStep (bankRepairDigitInShOf ox.qIn) ox.qCarry.isL := by
  rw [liveTopPair_x_qIn, liveTopPair_x_qCarry]
  rcases hi : ox.qIn with _ | _ | ⟨v, _ | _⟩ | ⟨v, _ | _⟩ <;> cases hc : ox.qCarry <;>
    cases hi2 : oy.qIn <;> cases hc2 : oy.qCarry <;>
    simp [liveTopQI, liveTopQC, hl, hly, hby, hbx, hi, hc, hi2, hc2, InTok.isX, InTok.isS,
      InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD,
      OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT, inV, outT,
      cohortTermStep, bankRepairDigitInShOf, QC, apply_ite InSt.iX, ite_self] <;>
    (repeat' split) <;> simp_all

/-! ### The lane of one complete pair -/

/-- Output shapes of the source cells, input shapes and carry-live bits of the target cells,
all indexed by the linear cell. -/
structure CohortLane where
  out : Nat → BankRepairDigitOutSh
  inp : Nat → BankRepairDigitInSh
  live : Nat → Bool

def cohortUpd {α : Type} (f : Nat → α) (a : Nat) (v : α) : Nat → α :=
  fun j => if j = a then v else f j

/-- The literal rows on edge `k`. -/
def cohortEdge (R : Nat) (s : CohortLane) (k : Nat) : CohortLane :=
  if k + 1 < R then
    let p := bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))
    { s with out := cohortUpd (cohortUpd s.out k p.1) (k + 1) p.2 }
  else if k + 1 = R then
    let d := bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))
    { out := cohortUpd s.out k d.1, inp := cohortUpd s.inp (k + 1) d.2.1,
      live := cohortUpd s.live (k + 1) d.2.2 }
  else if k + 1 < 2 * R then
    let f := bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
      (s.live (k + 1))
    { s with inp := cohortUpd (cohortUpd s.inp k f.1) (k + 1) f.2.2.1,
             live := cohortUpd (cohortUpd s.live k f.2.1) (k + 1) f.2.2.2 }
  else if k + 1 = 2 * R then
    let m := cohortTermStep (s.inp k) (s.live k)
    { s with inp := cohortUpd s.inp k m.1, live := cohortUpd s.live k m.2 }
  else s

/-- A scheduler letter acts on edge `k` of the pair, or (`none`) outside it. -/
def cohortLaneStep (R : Nat) (s : CohortLane) : Option Nat → CohortLane
  | none => s
  | some k => cohortEdge R s k

/-! ### Cell tokens -/

inductive CohortTok | empty | pkt (T : Bool) | settled (T : Bool) | other
  deriving DecidableEq

def cohortTokOut : BankRepairDigitOutSh → CohortTok
  | .E => .empty
  | .U => .other
  | .D T => .pkt T

def cohortTokIn (i : BankRepairDigitInSh) (l : Bool) : CohortTok :=
  if l then .other
  else
    match i with
    | .E => .empty
    | .X => .other
    | .P T => .pkt T
    | .S T => .settled T

def cohortTok (R : Nat) (s : CohortLane) (q : Nat) : CohortTok :=
  if q < R then cohortTokOut (s.out q) else cohortTokIn (s.inp q) (s.live q)

theorem cohortTokSrc {R q : Nat} (s : CohortLane) (h : q < R) :
    cohortTok R s q = cohortTokOut (s.out q) := by
  simp [cohortTok, h]

theorem cohortTokTgt {R q : Nat} (s : CohortLane) (h : R ≤ q) :
    cohortTok R s q = cohortTokIn (s.inp q) (s.live q) := by
  simp [cohortTok, Nat.not_lt.mpr h]

theorem cohortTokOutNe (o : BankRepairDigitOutSh) (T : Bool) :
    cohortTokOut o ≠ .settled T := by
  cases o <;> simp [cohortTokOut]

/-! ### Shape facts of the literal rows -/

theorem cohortPipeMove (bx : Bool) (ox oy : BankRepairDigitOutSh) (T : Bool)
    (hx : cohortTokOut ox = .pkt T) (hy : cohortTokOut oy = .empty) :
    cohortTokOut (bankRepairDigitPipeStep bx ox oy).1 = (if T = true then .other else .empty) ∧
      cohortTokOut (bankRepairDigitPipeStep bx ox oy).2 = .pkt T := by
  cases bx <;> cases ox <;> cases oy <;> cases T <;>
    simp_all [cohortTokOut, bankRepairDigitPipeStep]

theorem cohortPipeOcc (bx : Bool) (ox oy : BankRepairDigitOutSh) (T T' : Bool)
    (hx : cohortTokOut ox = .pkt T) (hy : cohortTokOut oy = .pkt T') :
    cohortTokOut (bankRepairDigitPipeStep bx ox oy).1 = .pkt T ∧
      cohortTokOut (bankRepairDigitPipeStep bx ox oy).2 = .pkt T' := by
  cases bx <;> cases ox <;> cases oy <;>
    simp_all [cohortTokOut, bankRepairDigitPipeStep]

theorem cohortPipeEmpty (bx : Bool) (ox oy : BankRepairDigitOutSh)
    (hx : cohortTokOut ox = .empty) (hb : bx = false) :
    cohortTokOut (bankRepairDigitPipeStep bx ox oy).1 = .empty ∧
      cohortTokOut (bankRepairDigitPipeStep bx ox oy).2 = cohortTokOut oy := by
  subst hb
  cases ox <;> cases oy <;> simp_all [cohortTokOut, bankRepairDigitPipeStep]

theorem cohortPipeBehind (bx : Bool) (ox oy : BankRepairDigitOutSh) (T : Bool)
    (hy : cohortTokOut oy = .pkt T) :
    cohortTokOut (bankRepairDigitPipeStep bx ox oy).2 = .pkt T := by
  cases bx <;> cases ox <;> cases oy <;>
    simp_all [cohortTokOut, bankRepairDigitPipeStep]

theorem cohortDelMove (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky T : Bool)
    (hx : cohortTokOut ox = .pkt T) (hy : cohortTokIn iy ky = .empty) :
    cohortTokOut (bankRepairDigitDelStep ox iy ky).1 = (if T = true then .other else .empty) ∧
      cohortTokIn (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 =
        .pkt T := by
  cases ox <;> cases iy <;> cases ky <;> cases T <;>
    simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

theorem cohortDelOcc (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky T T' : Bool)
    (hx : cohortTokOut ox = .pkt T) (hy : cohortTokIn iy ky = .pkt T') :
    cohortTokOut (bankRepairDigitDelStep ox iy ky).1 = .pkt T ∧
      cohortTokIn (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 =
        .pkt T' := by
  cases ox <;> cases iy <;> cases ky <;>
    simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

theorem cohortDelSet (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky T T' : Bool)
    (hx : cohortTokOut ox = .pkt T) (hy : cohortTokIn iy ky = .settled T') :
    cohortTokOut (bankRepairDigitDelStep ox iy ky).1 = .pkt T ∧
      cohortTokIn (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 =
        .settled T' := by
  cases ox <;> cases iy <;> cases ky <;>
    simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

theorem cohortDelEmpty (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (hx : cohortTokOut ox = .empty) :
    cohortTokOut (bankRepairDigitDelStep ox iy ky).1 = .empty ∧
      cohortTokIn (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 =
        cohortTokIn iy ky := by
  cases ox <;> cases iy <;> cases ky <;>
    simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

theorem cohortDelBehindPkt (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky T : Bool)
    (hy : cohortTokIn iy ky = .pkt T) :
    cohortTokIn (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 =
      .pkt T := by
  cases ox <;> cases iy <;> cases ky <;>
    simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

theorem cohortDelBehindSet (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky T : Bool)
    (hy : cohortTokIn iy ky = .settled T) :
    cohortTokIn (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 =
      .settled T := by
  cases ox <;> cases iy <;> cases ky <;>
    simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

theorem cohortFinMove (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky T : Bool)
    (hx : cohortTokIn ix kx = .pkt T) (hy : cohortTokIn iy ky = .empty) :
    cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).1
        (bankRepairDigitFinStep bx ix kx iy ky).2.1 = .empty ∧
      cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = .pkt T := by
  cases bx <;> cases ix <;> cases kx <;> cases iy <;> cases ky <;>
    simp_all [cohortTokIn, bankRepairDigitFinStep]

theorem cohortFinOcc (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky T T' : Bool)
    (hx : cohortTokIn ix kx = .pkt T) (hy : cohortTokIn iy ky = .pkt T') :
    cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).1
        (bankRepairDigitFinStep bx ix kx iy ky).2.1 = .pkt T ∧
      cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = .pkt T' := by
  cases bx <;> cases ix <;> cases kx <;> cases iy <;> cases ky <;>
    simp_all [cohortTokIn, bankRepairDigitFinStep]

theorem cohortFinSet (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky T T' : Bool)
    (hx : cohortTokIn ix kx = .pkt T) (hy : cohortTokIn iy ky = .settled T') :
    cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).1
        (bankRepairDigitFinStep bx ix kx iy ky).2.1 = .settled T ∧
      cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = .settled T' := by
  cases bx <;> cases ix <;> cases kx <;> cases iy <;> cases ky <;>
    simp_all [cohortTokIn, bankRepairDigitFinStep]

theorem cohortFinEmpty (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky : Bool) (hx : cohortTokIn ix kx = .empty) :
    cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).1
        (bankRepairDigitFinStep bx ix kx iy ky).2.1 = .empty ∧
      cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = cohortTokIn iy ky := by
  cases bx <;> cases ix <;> cases kx <;> cases iy <;> cases ky <;>
    simp_all [cohortTokIn, bankRepairDigitFinStep]

theorem cohortFinStay (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky : Bool) (hx : cohortTokIn ix kx = .settled false)
    (hb : bx = false) :
    cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).1
        (bankRepairDigitFinStep bx ix kx iy ky).2.1 = .settled false ∧
      cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = cohortTokIn iy ky := by
  subst hb
  cases ix <;> cases kx <;> cases iy <;> cases ky <;>
    simp_all [cohortTokIn, bankRepairDigitFinStep]

theorem cohortTermSettle (ix : BankRepairDigitInSh) (kx : Bool)
    (hx : cohortTokIn ix kx = .pkt false) :
    cohortTokIn (cohortTermStep ix kx).1 (cohortTermStep ix kx).2 = .settled false := by
  cases ix <;> cases kx <;> simp_all [cohortTokIn, cohortTermStep]

theorem cohortTermEmpty (ix : BankRepairDigitInSh) (kx : Bool)
    (hx : cohortTokIn ix kx = .empty) :
    cohortTokIn (cohortTermStep ix kx).1 (cohortTermStep ix kx).2 = .empty := by
  cases ix <;> cases kx <;> simp_all [cohortTokIn, cohortTermStep]

theorem cohortTermStay (ix : BankRepairDigitInSh) (kx : Bool)
    (hx : cohortTokIn ix kx = .settled false) :
    cohortTokIn (cohortTermStep ix kx).1 (cohortTermStep ix kx).2 = .settled false := by
  cases ix <;> cases kx <;> simp_all [cohortTokIn, cohortTermStep]

/-! ### The edge on the two touched cells -/

theorem cohortTokFrame (R k q : Nat) (s : CohortLane) (hq : q ≠ k) (hq' : q ≠ k + 1) :
    cohortTok R (cohortEdge R s k) q = cohortTok R s q := by
  unfold cohortEdge
  repeat' split
  all_goals simp [cohortTok, cohortUpd, hq, hq']

theorem cohortEdgeFar (R k : Nat) (s : CohortLane) (h : 2 * R ≤ k) : cohortEdge R s k = s := by
  unfold cohortEdge
  rw [if_neg (by omega : ¬ k + 1 < R), if_neg (by omega : ¬ k + 1 = R),
    if_neg (by omega : ¬ k + 1 < 2 * R), if_neg (by omega : ¬ k + 1 = 2 * R)]

theorem cohortTokPipe (R k : Nat) (s : CohortLane) (h : k + 1 < R) :
    cohortTok R (cohortEdge R s k) k =
        cohortTokOut (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).1 ∧
      cohortTok R (cohortEdge R s k) (k + 1) =
        cohortTokOut (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
  have hk : k < R := by omega
  unfold cohortEdge
  rw [if_pos h, cohortTokSrc _ hk, cohortTokSrc _ h]
  simp [cohortUpd]

theorem cohortTokDel (R k : Nat) (s : CohortLane) (h : k + 1 = R) :
    cohortTok R (cohortEdge R s k) k =
        cohortTokOut (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1 ∧
      cohortTok R (cohortEdge R s k) (k + 1) =
        cohortTokIn (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.1
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.2 := by
  have hk : k < R := by omega
  unfold cohortEdge
  rw [if_neg (by omega : ¬ k + 1 < R), if_pos h, cohortTokSrc _ hk,
    cohortTokTgt _ (by omega : R ≤ k + 1)]
  simp [cohortUpd]

theorem cohortTokFin (R k : Nat) (s : CohortLane) (h1 : R ≤ k) (h2 : k + 1 < 2 * R) :
    cohortTok R (cohortEdge R s k) k =
        cohortTokIn (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k)
            (s.inp (k + 1)) (s.live (k + 1))).1
          (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k)
            (s.inp (k + 1)) (s.live (k + 1))).2.1 ∧
      cohortTok R (cohortEdge R s k) (k + 1) =
        cohortTokIn (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k)
            (s.inp (k + 1)) (s.live (k + 1))).2.2.1
          (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k)
            (s.inp (k + 1)) (s.live (k + 1))).2.2.2 := by
  unfold cohortEdge
  rw [if_neg (by omega : ¬ k + 1 < R), if_neg (by omega : ¬ k + 1 = R), if_pos h2,
    cohortTokTgt _ h1, cohortTokTgt _ (by omega : R ≤ k + 1)]
  simp [cohortUpd]

theorem cohortTokTerm (R k : Nat) (s : CohortLane) (h : k + 1 = 2 * R) :
    cohortTok R (cohortEdge R s k) k =
      cohortTokIn (cohortTermStep (s.inp k) (s.live k)).1
        (cohortTermStep (s.inp k) (s.live k)).2 := by
  unfold cohortEdge
  rw [if_neg (by omega : ¬ k + 1 < R), if_neg (by omega : ¬ k + 1 = R),
    if_neg (by omega : ¬ k + 1 < 2 * R), if_pos h, cohortTokTgt _ (by omega : R ≤ k)]
  simp [cohortUpd]

theorem cohortEdgeMove (R k : Nat) (s : CohortLane) (T : Bool) (hk : k + 1 < 2 * R)
    (hx : cohortTok R s k = .pkt T) (hy : cohortTok R s (k + 1) = .empty) :
    cohortTok R (cohortEdge R s k) (k + 1) = .pkt T ∧
      cohortTok R (cohortEdge R s k) k = (if k < R ∧ T = true then .other else .empty) := by
  by_cases h1 : k + 1 < R
  · have hk0 : k < R := by omega
    obtain ⟨e1, e2⟩ := cohortTokPipe R k s h1
    rw [cohortTokSrc s hk0] at hx
    rw [cohortTokSrc s h1] at hy
    obtain ⟨m1, m2⟩ := cohortPipeMove (decide (k = 0)) _ _ T hx hy
    rw [e1, e2, m1, m2]
    simp [hk0]
  · by_cases h2 : k + 1 = R
    · have hk0 : k < R := by omega
      obtain ⟨e1, e2⟩ := cohortTokDel R k s h2
      rw [cohortTokSrc s hk0] at hx
      rw [cohortTokTgt s (by omega : R ≤ k + 1)] at hy
      obtain ⟨m1, m2⟩ := cohortDelMove _ _ _ T hx hy
      rw [e1, e2, m1, m2]
      simp [hk0]
    · have hRk : R ≤ k := by omega
      obtain ⟨e1, e2⟩ := cohortTokFin R k s hRk hk
      rw [cohortTokTgt s hRk] at hx
      rw [cohortTokTgt s (by omega : R ≤ k + 1)] at hy
      obtain ⟨m1, m2⟩ := cohortFinMove (decide (k = R)) _ _ _ _ T hx hy
      rw [e1, e2, m1, m2]
      simp [Nat.not_lt.mpr hRk]

theorem cohortEdgeOcc (R k : Nat) (s : CohortLane) (T T' : Bool) (hk : k + 1 < 2 * R)
    (hx : cohortTok R s k = .pkt T) (hy : cohortTok R s (k + 1) = .pkt T') :
    cohortTok R (cohortEdge R s k) k = .pkt T ∧
      cohortTok R (cohortEdge R s k) (k + 1) = .pkt T' := by
  by_cases h1 : k + 1 < R
  · have hk0 : k < R := by omega
    obtain ⟨e1, e2⟩ := cohortTokPipe R k s h1
    rw [cohortTokSrc s hk0] at hx
    rw [cohortTokSrc s h1] at hy
    obtain ⟨m1, m2⟩ := cohortPipeOcc (decide (k = 0)) _ _ T T' hx hy
    rw [e1, e2, m1, m2]
    exact ⟨rfl, rfl⟩
  · by_cases h2 : k + 1 = R
    · have hk0 : k < R := by omega
      obtain ⟨e1, e2⟩ := cohortTokDel R k s h2
      rw [cohortTokSrc s hk0] at hx
      rw [cohortTokTgt s (by omega : R ≤ k + 1)] at hy
      obtain ⟨m1, m2⟩ := cohortDelOcc _ _ _ T T' hx hy
      rw [e1, e2, m1, m2]
      exact ⟨rfl, rfl⟩
    · have hRk : R ≤ k := by omega
      obtain ⟨e1, e2⟩ := cohortTokFin R k s hRk hk
      rw [cohortTokTgt s hRk] at hx
      rw [cohortTokTgt s (by omega : R ≤ k + 1)] at hy
      obtain ⟨m1, m2⟩ := cohortFinOcc (decide (k = R)) _ _ _ _ T T' hx hy
      rw [e1, e2, m1, m2]
      exact ⟨rfl, rfl⟩

theorem cohortEdgeSet (R k : Nat) (s : CohortLane) (T T' : Bool) (hk : k + 1 < 2 * R)
    (hx : cohortTok R s k = .pkt T) (hy : cohortTok R s (k + 1) = .settled T') :
    (cohortTok R (cohortEdge R s k) k = .pkt T ∨
        cohortTok R (cohortEdge R s k) k = .settled T) ∧
      cohortTok R (cohortEdge R s k) (k + 1) = .settled T' := by
  by_cases h1 : k + 1 < R
  · rw [cohortTokSrc s h1] at hy
    exact absurd hy (cohortTokOutNe _ _)
  · by_cases h2 : k + 1 = R
    · have hk0 : k < R := by omega
      obtain ⟨e1, e2⟩ := cohortTokDel R k s h2
      rw [cohortTokSrc s hk0] at hx
      rw [cohortTokTgt s (by omega : R ≤ k + 1)] at hy
      obtain ⟨m1, m2⟩ := cohortDelSet _ _ _ T T' hx hy
      rw [e1, e2, m1, m2]
      exact ⟨Or.inl rfl, rfl⟩
    · have hRk : R ≤ k := by omega
      obtain ⟨e1, e2⟩ := cohortTokFin R k s hRk hk
      rw [cohortTokTgt s hRk] at hx
      rw [cohortTokTgt s (by omega : R ≤ k + 1)] at hy
      obtain ⟨m1, m2⟩ := cohortFinSet (decide (k = R)) _ _ _ _ T T' hx hy
      rw [e1, e2, m1, m2]
      exact ⟨Or.inr rfl, rfl⟩

theorem cohortEdgeEmpty (R k : Nat) (s : CohortLane) (hk0 : k ≠ 0)
    (hx : cohortTok R s k = .empty) :
    cohortTok R (cohortEdge R s k) k = .empty ∧
      (k + 1 < 2 * R → cohortTok R (cohortEdge R s k) (k + 1) = cohortTok R s (k + 1)) := by
  by_cases h1 : k + 1 < R
  · have hk : k < R := by omega
    obtain ⟨e1, e2⟩ := cohortTokPipe R k s h1
    rw [cohortTokSrc s hk] at hx
    obtain ⟨m1, m2⟩ := cohortPipeEmpty (decide (k = 0)) _ (s.out (k + 1)) hx (by simp [hk0])
    rw [e1, e2, m1, m2, cohortTokSrc s h1]
    exact ⟨rfl, fun _ => rfl⟩
  · by_cases h2 : k + 1 = R
    · have hk : k < R := by omega
      obtain ⟨e1, e2⟩ := cohortTokDel R k s h2
      rw [cohortTokSrc s hk] at hx
      obtain ⟨m1, m2⟩ := cohortDelEmpty _ (s.inp (k + 1)) (s.live (k + 1)) hx
      rw [e1, e2, m1, m2, cohortTokTgt s (by omega : R ≤ k + 1)]
      exact ⟨rfl, fun _ => rfl⟩
    · by_cases h3 : k + 1 < 2 * R
      · have hRk : R ≤ k := by omega
        obtain ⟨e1, e2⟩ := cohortTokFin R k s hRk h3
        rw [cohortTokTgt s hRk] at hx
        obtain ⟨m1, m2⟩ := cohortFinEmpty (decide (k = R)) _ _ (s.inp (k + 1))
          (s.live (k + 1)) hx
        rw [e1, e2, m1, m2, cohortTokTgt s (by omega : R ≤ k + 1)]
        exact ⟨rfl, fun _ => rfl⟩
      · by_cases h4 : k + 1 = 2 * R
        · rw [cohortTokTerm R k s h4]
          rw [cohortTokTgt s (by omega : R ≤ k)] at hx
          exact ⟨cohortTermEmpty _ _ hx, fun h => absurd h (by omega)⟩
        · rw [cohortEdgeFar R k s (by omega)]
          exact ⟨hx, fun _ => rfl⟩

theorem cohortEdgeStay (R k : Nat) (s : CohortLane) (hkR : k ≠ R)
    (hx : cohortTok R s k = .settled false) :
    cohortTok R (cohortEdge R s k) k = .settled false ∧
      (k + 1 < 2 * R → cohortTok R (cohortEdge R s k) (k + 1) = cohortTok R s (k + 1)) := by
  by_cases h0 : k < R
  · rw [cohortTokSrc s h0] at hx
    exact absurd hx (cohortTokOutNe _ _)
  · have hRk : R ≤ k := by omega
    by_cases h3 : k + 1 < 2 * R
    · obtain ⟨e1, e2⟩ := cohortTokFin R k s hRk h3
      rw [cohortTokTgt s hRk] at hx
      obtain ⟨m1, m2⟩ := cohortFinStay (decide (k = R)) _ _ (s.inp (k + 1))
        (s.live (k + 1)) hx (by simp [hkR])
      rw [e1, e2, m1, m2, cohortTokTgt s (by omega : R ≤ k + 1)]
      exact ⟨rfl, fun _ => rfl⟩
    · by_cases h4 : k + 1 = 2 * R
      · rw [cohortTokTerm R k s h4]
        rw [cohortTokTgt s hRk] at hx
        exact ⟨cohortTermStay _ _ hx, fun h => absurd h (by omega)⟩
      · rw [cohortEdgeFar R k s (by omega)]
        exact ⟨hx, fun _ => rfl⟩

theorem cohortEdgeTerm (R k : Nat) (s : CohortLane) (h : k + 1 = 2 * R)
    (hx : cohortTok R s k = .pkt false) :
    cohortTok R (cohortEdge R s k) k = .settled false := by
  rw [cohortTokTerm R k s h]
  rw [cohortTokTgt s (by omega : R ≤ k)] at hx
  exact cohortTermSettle _ _ hx

theorem cohortEdgeBehind (R k : Nat) (s : CohortLane) (T : Bool) (hk : k < R)
    (hy : cohortTok R s (k + 1) = .pkt T ∨ cohortTok R s (k + 1) = .settled T) :
    cohortTok R (cohortEdge R s k) (k + 1) = cohortTok R s (k + 1) := by
  by_cases h1 : k + 1 < R
  · obtain ⟨-, e2⟩ := cohortTokPipe R k s h1
    rw [cohortTokSrc s h1] at hy
    rcases hy with hy | hy
    · rw [e2, cohortPipeBehind _ _ _ T hy, cohortTokSrc s h1, hy]
    · exact absurd hy (cohortTokOutNe _ _)
  · have h2 : k + 1 = R := by omega
    obtain ⟨-, e2⟩ := cohortTokDel R k s h2
    rw [cohortTokTgt s (by omega : R ≤ k + 1)] at hy
    rw [e2, cohortTokTgt s (by omega : R ≤ k + 1)]
    rcases hy with hy | hy
    · rw [cohortDelBehindPkt _ _ _ T hy, hy]
    · rw [cohortDelBehindSet _ _ _ T hy, hy]

/-! ### The post-strict class -/

/-- Cell of packet `i` after `lam i` hops. -/
def cohortPos (R : Nat) (lam : Nat → Nat) (i : Nat) : Nat := R - 1 - i + lam i

/-- The tail bit of packet `i`: the last packet carries the tail. -/
def cohortTail (R i : Nat) : Bool := decide (i + 1 = R)

/-- The post-strict structural class for the chosen cohort (repair.tex Lemma e-current), in the
transport phase: every packet sits at its cell with its tail bit, a settled operand only at its
destination, every other cell from the tail forward is empty (no live carry, no front, no
unread slot, no older operand). -/
structure CohortPostStrict (R : Nat) (s : CohortLane) (lam : Nat → Nat) : Prop where
  two : 2 ≤ R
  le : ∀ i, i < R → lam i ≤ R
  mono : ∀ i, i + 1 < R → lam (i + 1) ≤ lam i
  pkt : ∀ i, i < R →
    cohortTok R s (cohortPos R lam i) = .pkt (cohortTail R i) ∨
      (cohortTok R s (cohortPos R lam i) = .settled (cohortTail R i) ∧ lam i = R)
  gap : ∀ q, q < 2 * R → lam (R - 1) < q → (∀ i, i < R → cohortPos R lam i ≠ q) →
    cohortTok R s q = .empty

/-- The ghost hop counter: packet `i` completes a hop when its own edge is drawn and the cell
ahead of it is empty, which is when the literal row moves it. -/
def cohortGhost (R : Nat) (s : CohortLane) (lam : Nat → Nat) (ke : Option Nat) (i : Nat) :
    Nat :=
  if i < R ∧ lam i < R ∧ ke = some (cohortPos R lam i) ∧
      cohortTok R s (cohortPos R lam i + 1) = .empty then lam i + 1 else lam i

theorem cohortGhostGe (R : Nat) (s : CohortLane) (lam : Nat → Nat) (ke : Option Nat)
    (i : Nat) : lam i ≤ cohortGhost R s lam ke i := by
  unfold cohortGhost
  split <;> omega

section Class

variable {R : Nat} {s : CohortLane} {lam : Nat → Nat}

theorem cohortChain (h : CohortPostStrict R s lam) :
    ∀ a b, a ≤ b → b < R → lam b ≤ lam a := by
  intro a b hab hb
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with he | hlt
    · subst he
      exact Nat.le_refl _
    · exact Nat.le_trans (h.mono b hb) (ih (by omega) (by omega))

theorem cohortPosLt (h : CohortPostStrict R s lam) {a b : Nat} (hab : a < b) (hb : b < R) :
    cohortPos R lam b < cohortPos R lam a := by
  have := cohortChain h a b (Nat.le_of_lt hab) hb
  unfold cohortPos
  omega

theorem cohortPosInj (h : CohortPostStrict R s lam) {a b : Nat} (ha : a < R) (hb : b < R)
    (he : cohortPos R lam a = cohortPos R lam b) : a = b := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have := cohortPosLt h hab hb
    omega
  · exact hab
  · have := cohortPosLt h hab ha
    omega

theorem cohortPosTail (h : CohortPostStrict R s lam) {i : Nat} (hi : i < R) :
    lam (R - 1) ≤ cohortPos R lam i := by
  have := cohortChain h i (R - 1) (by omega) (by omega)
  unfold cohortPos
  omega

theorem cohortPosBound (h : CohortPostStrict R s lam) {i : Nat} (hi : i < R) :
    cohortPos R lam i < 2 * R := by
  have := h.le i hi
  unfold cohortPos
  omega

theorem cohortOcc (h : CohortPostStrict R s lam) {j : Nat} (hj : j < R) :
    cohortTok R s (cohortPos R lam j) ≠ .empty := by
  intro he
  rcases h.pkt j hj with h1 | ⟨h1, -⟩ <;> rw [h1] at he <;> cases he

theorem cohortGhostSame {k : Nat}
    (hno : ∀ j, j < R → lam j < R → cohortPos R lam j = k →
      cohortTok R s (k + 1) = .empty → False) :
    cohortGhost R s lam (some k) = lam := by
  funext j
  unfold cohortGhost
  rw [if_neg]
  rintro ⟨hj, hl, he, hf⟩
  have he' : cohortPos R lam j = k := (Option.some.inj he).symm
  rw [he'] at hf
  exact hno j hj hl he' hf

theorem cohortGhostMove (h : CohortPostStrict R s lam) {i k : Nat} (hi : i < R)
    (hlt : lam i < R) (hpi : cohortPos R lam i = k)
    (hfree : cohortTok R s (k + 1) = .empty) :
    cohortGhost R s lam (some k) = cohortUpd lam i (lam i + 1) := by
  funext j
  unfold cohortGhost cohortUpd
  by_cases hji : j = i
  · subst hji
    rw [if_pos ⟨hi, hlt, by rw [hpi], by rw [hpi]; exact hfree⟩, if_pos rfl]
  · rw [if_neg hji, if_neg]
    rintro ⟨hj, -, he, -⟩
    exact hji (cohortPosInj h hj hi (((Option.some.inj he).symm).trans hpi.symm))

/-- Any change confined to cell `k` and to cells behind the tail that keeps packet `k` (if
any) a packet, and keeps `k` empty if it is a gap cell, stays in the class. -/
theorem cohortRetok {s' : CohortLane} {k : Nat} (h : CohortPostStrict R s lam)
    (hframe : ∀ q, q < 2 * R → lam (R - 1) ≤ q → q ≠ k → cohortTok R s' q = cohortTok R s q)
    (hgapk : (∀ i, i < R → cohortPos R lam i ≠ k) → lam (R - 1) < k → k < 2 * R →
      cohortTok R s' k = .empty)
    (hpk : ∀ i, i < R → cohortPos R lam i = k →
      cohortTok R s' k = .pkt (cohortTail R i) ∨
        (cohortTok R s' k = .settled (cohortTail R i) ∧ lam i = R)) :
    CohortPostStrict R s' lam := by
  refine ⟨h.two, h.le, h.mono, ?_, ?_⟩
  · intro i hi
    by_cases hk : cohortPos R lam i = k
    · rw [hk]
      exact hpk i hi hk
    · rw [hframe _ (cohortPosBound h hi) (cohortPosTail h hi) hk]
      exact h.pkt i hi
  · intro q hq hlq hnq
    by_cases hk : q = k
    · subst hk
      exact hgapk hnq hlq hq
    · rw [hframe q hq (Nat.le_of_lt hlq) hk]
      exact h.gap q hq hlq hnq

/-- Packet `i` hops from its cell into the empty cell ahead. -/
theorem cohortMovePres {s' : CohortLane} {i : Nat} (h : CohortPostStrict R s lam)
    (hi : i < R) (hlt : lam i < R)
    (hfree : cohortTok R s (cohortPos R lam i + 1) = .empty)
    (hframe : ∀ q, q ≠ cohortPos R lam i → q ≠ cohortPos R lam i + 1 →
      cohortTok R s' q = cohortTok R s q)
    (hnew : cohortTok R s' (cohortPos R lam i + 1) = .pkt (cohortTail R i))
    (hold : cohortTok R s' (cohortPos R lam i) =
      if cohortPos R lam i < R ∧ cohortTail R i = true then .other else .empty) :
    CohortPostStrict R s' (cohortUpd lam i (lam i + 1)) := by
  have hR := h.two
  have hupd : ∀ j, j ≠ i → cohortUpd lam i (lam i + 1) j = lam j := fun j hj => by
    simp [cohortUpd, hj]
  have hupdi : cohortUpd lam i (lam i + 1) i = lam i + 1 := by simp [cohortUpd]
  have hposj : ∀ j, j ≠ i →
      cohortPos R (cohortUpd lam i (lam i + 1)) j = cohortPos R lam j := by
    intro j hj
    unfold cohortPos
    rw [hupd j hj]
  have hposi : cohortPos R (cohortUpd lam i (lam i + 1)) i = cohortPos R lam i + 1 := by
    unfold cohortPos
    rw [hupdi]
    omega
  refine ⟨hR, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [hupdi]
      omega
    · rw [hupd j hji]
      exact h.le j hj
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [hupd (j + 1) (by omega), hupdi]
      have := h.mono j hj
      omega
    · by_cases hj1 : j + 1 = i
      · have hfree' : cohortTok R s (cohortPos R lam (j + 1) + 1) = .empty := by
          rw [hj1]; exact hfree
        have hlt' := cohortPosLt h (show j < j + 1 by omega) hj
        have hne : cohortPos R lam j ≠ cohortPos R lam (j + 1) + 1 := by
          intro he
          exact cohortOcc h (show j < R by omega) (by rw [he]; exact hfree')
        rw [hupd j hji, hj1, hupdi, ← hj1]
        unfold cohortPos at hlt' hne
        omega
      · rw [hupd j hji, hupd (j + 1) hj1]
        exact h.mono j hj
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [hposi, hnew]
      exact Or.inl rfl
    · rw [hposj j hji, hupd j hji]
      have hne1 : cohortPos R lam j ≠ cohortPos R lam i := fun he =>
        hji (cohortPosInj h hj hi he)
      have hne2 : cohortPos R lam j ≠ cohortPos R lam i + 1 := fun he =>
        cohortOcc h hj (by rw [he]; exact hfree)
      rw [hframe _ hne1 hne2]
      exact h.pkt j hj
  · intro q hq hlq hnq
    by_cases hq1 : q = cohortPos R lam i
    · subst hq1
      rw [hold]
      have hnt : ¬ (cohortPos R lam i < R ∧ cohortTail R i = true) := by
        rintro ⟨-, ht⟩
        have hiR : i + 1 = R := by simpa [cohortTail] using ht
        have e : R - 1 = i := by omega
        rw [e, hupdi] at hlq
        unfold cohortPos at hlq
        omega
      rw [if_neg hnt]
    · by_cases hq2 : q = cohortPos R lam i + 1
      · exact absurd (hposi.trans hq2.symm) (hnq i hi)
      · rw [hframe q hq1 hq2]
        apply h.gap q hq
        · have hge : lam (R - 1) ≤ cohortUpd lam i (lam i + 1) (R - 1) := by
            by_cases hR1 : R - 1 = i
            · rw [hR1, hupdi]
              omega
            · rw [hupd _ hR1]
              exact Nat.le_refl _
          omega
        · intro j hj he
          by_cases hji : j = i
          · subst hji
            exact hq1 he.symm
          · exact hnq j hj ((hposj j hji).trans he)

/-- The class is preserved by every edge until the grid is complete. -/
theorem cohortPostStrictEdge (h : CohortPostStrict R s lam) (hnd : ¬ gridDone R R lam)
    (k : Nat) : CohortPostStrict R (cohortEdge R s k) (cohortGhost R s lam (some k)) := by
  have hR := h.two
  by_cases hfar : 2 * R ≤ k
  · rw [cohortEdgeFar R k s hfar]
    rw [cohortGhostSame (fun j hj _ hpj _ => by have := cohortPosBound h hj; omega)]
    exact h
  have hk2 : k < 2 * R := by omega
  by_cases hp : ∃ i, i < R ∧ cohortPos R lam i = k
  · obtain ⟨i, hi, hpi⟩ := hp
    have hpk := h.pkt i hi
    rw [hpi] at hpk
    have huniq : ∀ j, j < R → cohortPos R lam j = k → j = i :=
      fun j hj hpj => cohortPosInj h hj hi (hpj.trans hpi.symm)
    rcases hpk with hpkt | ⟨hset, hlamR⟩
    · by_cases hk1 : k + 1 < 2 * R
      · by_cases hfree : cohortTok R s (k + 1) = .empty
        · have hlt : lam i < R := by
            rcases Nat.lt_or_ge (lam i) R with hl | hl
            · exact hl
            · exfalso
              have hli := h.le i hi
              have hi0 : i ≠ 0 := by
                intro he
                subst he
                unfold cohortPos at hpi
                omega
              have hlt2 := cohortPosLt h (show i - 1 < i by omega) hi
              have hle2 := h.le (i - 1) (by omega)
              have he : cohortPos R lam (i - 1) = k + 1 := by
                unfold cohortPos at hlt2 hpi ⊢
                omega
              exact cohortOcc h (show i - 1 < R by omega) (by rw [he]; exact hfree)
          rw [cohortGhostMove h hi hlt hpi hfree]
          obtain ⟨e1, e2⟩ := cohortEdgeMove R k s _ hk1 hpkt hfree
          subst hpi
          exact cohortMovePres h hi hlt hfree
            (fun q h1 h2 => cohortTokFrame R _ q s h1 h2) e1 e2
        · rw [cohortGhostSame (fun _ _ _ _ hf => hfree hf)]
          obtain ⟨j, hj, hpj⟩ : ∃ j, j < R ∧ cohortPos R lam j = k + 1 :=
            Classical.byContradiction fun hne => hfree (h.gap (k + 1) hk1
              (by have := cohortPosTail h hi; omega)
              (fun j hj hpj => hne ⟨j, hj, hpj⟩))
          have hji : j < i := by
            rcases Nat.lt_or_ge j i with hl | hl
            · exact hl
            · exfalso
              rcases Nat.eq_or_lt_of_le hl with he | he
              · rw [he] at hpi
                omega
              · have := cohortPosLt h he hj
                omega
          have hpkj := h.pkt j hj
          rw [hpj] at hpkj
          rcases hpkj with hpj' | ⟨hsj, hlj⟩
          · obtain ⟨e1, e2⟩ := cohortEdgeOcc R k s _ _ hk1 hpkt hpj'
            apply cohortRetok h
            · intro q _ _ hqk
              by_cases hq1 : q = k + 1
              · rw [hq1, e2, hpj']
              · exact cohortTokFrame R k q s hqk hq1
            · intro hno
              exact absurd hpi (hno i hi)
            · intro i' hi' hpi'
              rw [huniq i' hi' hpi']
              exact Or.inl e1
          · obtain ⟨e1, e2⟩ := cohortEdgeSet R k s _ _ hk1 hpkt hsj
            have hlamR : lam i = R := by
              have := h.le i hi
              unfold cohortPos at hpi hpj
              omega
            apply cohortRetok h
            · intro q _ _ hqk
              by_cases hq1 : q = k + 1
              · rw [hq1, e2, hsj]
              · exact cohortTokFrame R k q s hqk hq1
            · intro hno
              exact absurd hpi (hno i hi)
            · intro i' hi' hpi'
              rw [huniq i' hi' hpi']
              rcases e1 with e1 | e1
              · exact Or.inl e1
              · exact Or.inr ⟨e1, hlamR⟩
      · have hk1' : k + 1 = 2 * R := by omega
        have hli := h.le i hi
        have hi0 : i = 0 := by
          unfold cohortPos at hpi
          omega
        have hlam0 : lam i = R := by
          unfold cohortPos at hpi
          omega
        have htail : cohortTail R i = false := by
          simp [cohortTail]
          omega
        rw [htail] at hpkt
        have e1 := cohortEdgeTerm R k s hk1' hpkt
        rw [cohortGhostSame (fun j hj hl hpj _ => by
          have := huniq j hj hpj
          subst this
          omega)]
        apply cohortRetok h
        · intro q hq _ hqk
          exact cohortTokFrame R k q s hqk (by omega)
        · intro hno
          exact absurd hpi (hno i hi)
        · intro i' hi' hpi'
          rw [huniq i' hi' hpi', htail]
          exact Or.inr ⟨e1, hlam0⟩
    · have hiR : i + 1 ≠ R := by
        intro he
        apply hnd
        intro j hj
        have := cohortChain h j i (by omega) hi
        omega
      have htail : cohortTail R i = false := by
        simp [cohortTail]
        exact hiR
      rw [htail] at hset
      have hkR : k ≠ R := by
        unfold cohortPos at hpi
        omega
      obtain ⟨e1, e2⟩ := cohortEdgeStay R k s hkR hset
      rw [cohortGhostSame (fun j hj hl hpj _ => by
        have := huniq j hj hpj
        subst this
        omega)]
      apply cohortRetok h
      · intro q hq _ hqk
        by_cases hq1 : q = k + 1
        · subst hq1
          exact e2 hq
        · exact cohortTokFrame R k q s hqk hq1
      · intro hno
        exact absurd hpi (hno i hi)
      · intro i' hi' hpi'
        rw [huniq i' hi' hpi', htail]
        exact Or.inr ⟨e1, hlamR⟩
  · have hno : ∀ j, j < R → cohortPos R lam j ≠ k := fun j hj hpj => hp ⟨j, hj, hpj⟩
    rw [cohortGhostSame (fun j hj _ hpj _ => hno j hj hpj)]
    have hpT : cohortPos R lam (R - 1) = lam (R - 1) := by
      unfold cohortPos
      omega
    by_cases hbeh : k < lam (R - 1)
    · have hkR : k < R := by
        have := h.le (R - 1) (by omega)
        omega
      apply cohortRetok h
      · intro q _ hlq hqk
        by_cases hq1 : q = k + 1
        · subst hq1
          have he : k + 1 = cohortPos R lam (R - 1) := by omega
          have hpkT := h.pkt (R - 1) (by omega)
          rw [← he] at hpkT
          exact cohortEdgeBehind R k s _ hkR (hpkT.imp id And.left)
        · exact cohortTokFrame R k q s hqk hq1
      · intro _ hlt
        omega
      · intro i' hi' hpi'
        exact absurd hpi' (hno i' hi')
    · have hgt : lam (R - 1) < k := by
        rcases Nat.lt_or_ge (lam (R - 1)) k with hl | hl
        · exact hl
        · exfalso
          exact hno (R - 1) (by omega) (by omega)
      have hemp := h.gap k hk2 hgt hno
      obtain ⟨e1, e2⟩ := cohortEdgeEmpty R k s (by omega) hemp
      apply cohortRetok h
      · intro q hq _ hqk
        by_cases hq1 : q = k + 1
        · subst hq1
          exact e2 hq
        · exact cohortTokFrame R k q s hqk hq1
      · intro _ _ _
        exact e1
      · intro i' hi' hpi'
        exact absurd hpi' (hno i' hi')

theorem cohortPostStrictStep (h : CohortPostStrict R s lam) (hnd : ¬ gridDone R R lam)
    (ke : Option Nat) :
    CohortPostStrict R (cohortLaneStep R s ke) (cohortGhost R s lam ke) := by
  cases ke with
  | none =>
    have : cohortGhost R s lam none = lam := by
      funext j
      simp [cohortGhost]
    rw [this]
    exact h
  | some k => exact cohortPostStrictEdge h hnd k

/-- When the grid is complete, the cohort is packed in the target: packet `i` sits at target
offset `R - 1 - i`, pending or settled. -/
theorem cohortDonePacked (h : CohortPostStrict R s lam) (hd : gridDone R R lam) {i : Nat}
    (hi : i < R) :
    cohortTok R s (2 * R - 1 - i) = .pkt (cohortTail R i) ∨
      cohortTok R s (2 * R - 1 - i) = .settled (cohortTail R i) := by
  have he : cohortPos R lam i = 2 * R - 1 - i := by
    have := h.le i hi
    have := hd i hi
    unfold cohortPos
    omega
  rcases h.pkt i hi with h1 | ⟨h1, -⟩ <;> rw [he] at h1
  · exact Or.inl h1
  · exact Or.inr h1

/-! ### Domination -/

/-- The scheduler letter of hop `j` of packet `i`: the edge of its current cell. -/
def cohortLetter {n : Nat} (R : Nat) (site : Nat → Fin n) : Nat → Nat → Fin n :=
  fun i j => site (R - 1 - i + j)

/-- `hdom` on the class: every ready clean cell whose letter is drawn is completed by the
literal rows. -/
theorem cohortDom {n : Nat} (h : CohortPostStrict R s lam) (site : Nat → Fin n)
    (edgeOf : Fin n → Option Nat) (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k)
    (e : Fin n) :
    rowsLe R (gridStep R (cohortLetter R site) lam e) (cohortGhost R s lam (edgeOf e)) := by
  intro i hi
  by_cases hc : gridReady R lam i ∧ cohortLetter R site i (lam i) = e
  · rw [show gridStep R (cohortLetter R site) lam e i = lam i + 1 from if_pos hc]
    obtain ⟨⟨hlt, hor⟩, hle⟩ := hc
    have hpos : cohortPos R lam i + 1 < 2 * R := by
      unfold cohortPos
      omega
    have hfree : cohortTok R s (cohortPos R lam i + 1) = .empty := by
      apply h.gap _ hpos
      · have := cohortPosTail h hi
        omega
      · intro j hj hpj
        rcases Nat.lt_trichotomy j i with hji | hji | hji
        · rcases hor with h0 | hprev
          · omega
          · have hc1 := cohortChain h j (i - 1) (by omega) (by omega)
            unfold cohortPos at hpj
            omega
        · subst hji
          omega
        · have := cohortPosLt h hji hj
          omega
    have hk : edgeOf e = some (cohortPos R lam i) := by
      rw [← hle]
      exact hedge (cohortPos R lam i) (by omega)
    unfold cohortGhost
    rw [if_pos ⟨hi, hlt, hk, hfree⟩]
    exact Nat.le_refl _
  · rw [show gridStep R (cohortLetter R site) lam e i = lam i from if_neg hc]
    exact cohortGhostGe R s lam (edgeOf e) i

end Class

/-! ### The coupled chain and the charge -/

/-- The literal lane with the ghost hop counter. -/
def cohortNext {n : Nat} (R : Nat) (edgeOf : Fin n → Option Nat)
    (x : CohortLane × (Nat → Nat)) (e : Fin n) : CohortLane × (Nat → Nat) :=
  (cohortLaneStep R x.1 (edgeOf e), cohortGhost R x.1 x.2 (edgeOf e))

/-- The post-strict class, closed: in transport, or the cohort's grid is complete. -/
def CohortClass (R : Nat) (x : CohortLane × (Nat → Nat)) : Prop :=
  CohortPostStrict R x.1 x.2 ∨ gridDone R R x.2

/-- Target: every packet of the cohort has made its `R` hops. -/
def CohortDone (R : Nat) (x : CohortLane × (Nat → Nat)) : Prop := gridDone R R x.2

theorem cohortDoneClosed {n R : Nat} (edgeOf : Fin n → Option Nat) :
    ∀ x e, CohortDone R x → CohortDone R (cohortNext R edgeOf x e) :=
  fun x e hx i hi => Nat.le_trans (hx i hi) (cohortGhostGe R x.1 x.2 (edgeOf e) i)

theorem cohortClassClosed {n R : Nat} (edgeOf : Fin n → Option Nat) :
    ∀ x e, CohortClass R x → CohortClass R (cohortNext R edgeOf x e) := by
  intro x e hx
  by_cases hd : gridDone R R x.2
  · exact Or.inr (cohortDoneClosed edgeOf x e hd)
  · rcases hx with hx | hx
    · exact Or.inl (cohortPostStrictStep hx hd (edgeOf e))
    · exact absurd hx hd

/-- `hdom` of `gridDominationCharge`. -/
theorem cohortHdom {n R : Nat} (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) :
    ∀ x e, CohortClass R x → ¬ CohortDone R x →
      rowsLe R (gridStep R (cohortLetter R site) x.2 e) (cohortNext R edgeOf x e).2 := by
  intro x e hx hnd
  rcases hx with hx | hx
  · exact cohortDom hx site edgeOf hedge e
  · exact absurd hx hnd

/-- `hgood` of `gridDominationCharge`. -/
theorem cohortHgood (R : Nat) :
    ∀ x, CohortClass R x → gridDone R R x.2 → CohortDone R x :=
  fun _ _ h => h

/-- Step 3: from every state of the post-strict class, the chosen cohort's transport completes
at charge `32 n R` (expected `16 n R`), on the literal rows. -/
theorem cohortDominationCharge {n R : Nat} (hR : 0 < R) (site : Nat → Fin n)
    (edgeOf : Fin n → Option Nat) (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) :
    ∀ x, CohortClass R x → ∀ T,
      2 * costNumerator (cohortNext R edgeOf) (CohortDone R) x T ≤ n ^ T * (32 * n * R) :=
  gridDominationCharge (cohortNext R edgeOf) (CohortClass R) (CohortDone R)
    (cohortClassClosed edgeOf) (cohortDoneClosed edgeOf) R hR (cohortLetter R site)
    (fun x => x.2) (cohortHdom site edgeOf hedge) (cohortHgood R)

end L3.CohortDomination

#print axioms L3.CohortDomination.cohortWriterTermRow
#print axioms L3.CohortDomination.cohortComparisonTermRow
#print axioms L3.CohortDomination.cohortTokSrc
#print axioms L3.CohortDomination.cohortTokTgt
#print axioms L3.CohortDomination.cohortTokOutNe
#print axioms L3.CohortDomination.cohortPipeMove
#print axioms L3.CohortDomination.cohortPipeOcc
#print axioms L3.CohortDomination.cohortPipeEmpty
#print axioms L3.CohortDomination.cohortPipeBehind
#print axioms L3.CohortDomination.cohortDelMove
#print axioms L3.CohortDomination.cohortDelOcc
#print axioms L3.CohortDomination.cohortDelSet
#print axioms L3.CohortDomination.cohortDelEmpty
#print axioms L3.CohortDomination.cohortDelBehindPkt
#print axioms L3.CohortDomination.cohortDelBehindSet
#print axioms L3.CohortDomination.cohortFinMove
#print axioms L3.CohortDomination.cohortFinOcc
#print axioms L3.CohortDomination.cohortFinSet
#print axioms L3.CohortDomination.cohortFinEmpty
#print axioms L3.CohortDomination.cohortFinStay
#print axioms L3.CohortDomination.cohortTermSettle
#print axioms L3.CohortDomination.cohortTermEmpty
#print axioms L3.CohortDomination.cohortTermStay
#print axioms L3.CohortDomination.cohortTokFrame
#print axioms L3.CohortDomination.cohortEdgeFar
#print axioms L3.CohortDomination.cohortTokPipe
#print axioms L3.CohortDomination.cohortTokDel
#print axioms L3.CohortDomination.cohortTokFin
#print axioms L3.CohortDomination.cohortTokTerm
#print axioms L3.CohortDomination.cohortEdgeMove
#print axioms L3.CohortDomination.cohortEdgeOcc
#print axioms L3.CohortDomination.cohortEdgeSet
#print axioms L3.CohortDomination.cohortEdgeEmpty
#print axioms L3.CohortDomination.cohortEdgeStay
#print axioms L3.CohortDomination.cohortEdgeTerm
#print axioms L3.CohortDomination.cohortEdgeBehind
#print axioms L3.CohortDomination.cohortGhostGe
#print axioms L3.CohortDomination.cohortChain
#print axioms L3.CohortDomination.cohortPosLt
#print axioms L3.CohortDomination.cohortPosInj
#print axioms L3.CohortDomination.cohortPosTail
#print axioms L3.CohortDomination.cohortPosBound
#print axioms L3.CohortDomination.cohortOcc
#print axioms L3.CohortDomination.cohortGhostSame
#print axioms L3.CohortDomination.cohortGhostMove
#print axioms L3.CohortDomination.cohortRetok
#print axioms L3.CohortDomination.cohortMovePres
#print axioms L3.CohortDomination.cohortPostStrictEdge
#print axioms L3.CohortDomination.cohortPostStrictStep
#print axioms L3.CohortDomination.cohortDonePacked
#print axioms L3.CohortDomination.cohortDom
#print axioms L3.CohortDomination.cohortDoneClosed
#print axioms L3.CohortDomination.cohortClassClosed
#print axioms L3.CohortDomination.cohortHdom
#print axioms L3.CohortDomination.cohortHgood
#print axioms L3.CohortDomination.cohortDominationCharge

import Leader.L3.Bank.RepairDigitPacketMomentU

/-!
# Lemma e-packet: retirement after the settled-empty cut, in moment form

At the settled-empty cut the remaining fronts and carries of the target retire on their next
outgoing contacts. With no settled input, no window edge creates a settled input, a front or
a carry, except a terminal settlement of a pending packet; by the packet barrier a pending
packet reaches the terminal register only when no obstacle stands, i.e. at the packet-only cut.
So the obstacle count `obS` (fronts plus live carries) never rises and the outgoing edge of any
obstacle lowers it (`retMono`, `retDrop`), and `momentOfPotential` gives
`E[z^{T_ret}] ≤ w^{2R}` to the packet-only cut (`retMomentCoupled`); the paper pays `r` hits.
-/

namespace L3.PacketMomentRetire

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open L3.PairMoment
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.DigitPacketRelease
open L3.PacketMomentRelease
open L3.MarkedCells
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentU

/-! ### Weighted sums -/

/-- The sum of `f j` over `j < k`. Consumer: `obS`. -/
def wS (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => wS f k + f k

/-- Sums of agreeing weights agree. Consumer: `wSEditPair`, `wSEditOne`. -/
theorem wS_congr (f g : Nat → Nat) : ∀ k, (∀ j, j < k → g j = f j) → wS g k = wS f k
  | 0 => fun _ => rfl
  | k + 1 => fun h => by
      simp only [wS]
      rw [wS_congr f g k (fun j hj => h j (by omega)), h k (by omega)]

/-- Editing two adjacent weights. Consumer: `moveRet`. -/
theorem wSEditPair (f g : Nat → Nat) (p : Nat) (h : ∀ j, j ≠ p → j ≠ p + 1 → g j = f j) :
    ∀ k, p + 2 ≤ k → wS g k + f p + f (p + 1) = wS f k + g p + g (p + 1) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk
      by_cases hk2 : p + 2 ≤ k
      · have := ih hk2
        simp only [wS]
        rw [h k (by omega) (by omega)]
        omega
      · have hkk : k = p + 1 := by omega
        subst hkk
        have hc := wS_congr f g p (fun j hj => h j (by omega) (by omega))
        simp only [wS]
        rw [hc]
        omega

/-- Editing one weight. Consumer: `moveRet`. -/
theorem wSEditOne (f g : Nat → Nat) (p : Nat) (h : ∀ j, j ≠ p → g j = f j) :
    ∀ k, p + 1 ≤ k → wS g k + f p = wS f k + g p := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk
      by_cases hk2 : p + 1 ≤ k
      · have := ih hk2
        simp only [wS]
        rw [h k (by omega)]
        omega
      · have hkk : k = p := by omega
        subst hkk
        have hc := wS_congr f g k (fun j hj => h j (by omega))
        simp only [wS]
        rw [hc]
        omega

/-- Pointwise smaller weights have a smaller sum. Consumer: `moveRet`. -/
theorem wS_mono (f g : Nat → Nat) : ∀ k, (∀ j, j < k → g j ≤ f j) → wS g k ≤ wS f k
  | 0 => fun _ => Nat.le_refl _
  | k + 1 => fun h => by
      simp only [wS]
      have := wS_mono f g k (fun j hj => h j (by omega))
      have := h k (by omega)
      omega

/-- Weights bounded by `c` have sum at most `c k`. Consumer: `obS_le`. -/
theorem wS_le (f : Nat → Nat) (c : Nat) (h : ∀ j, f j ≤ c) : ∀ k, wS f k ≤ c * k
  | 0 => Nat.zero_le _
  | k + 1 => by
      simp only [wS]
      have := wS_le f c h k
      have := h k
      rw [Nat.mul_succ]
      omega

/-! ### Obstacles -/

/-- Fronts and live carries of one register. Consumer: `obS`. -/
def obW (c : Cell) : Nat := (if c.i = .x then 1 else 0) + (if c.c = .off then 0 else 1)

/-- **The obstacle count** of the window. Consumer: `retMoment`. -/
def obS (r : Nat) (cells : Nat → Cell) : Nat := wS (fun j => obW (cells j)) r

/-- At most two obstacles per register. Consumer: `retMomentCoupled`. -/
theorem obS_le (r : Nat) (cells : Nat → Cell) : obS r cells ≤ 2 * r := by
  apply wS_le
  intro j
  unfold obW
  split <;> split <;> omega

/-- A register with an obstacle is an obstacle of the barrier. Consumer: `moveRet`. -/
theorem obC_of_obW (c : Cell) (h : 0 < obW c) : obC c = true := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> revert h <;> decide

/-- **An internal edge without settled input.** No settled input appears, and the obstacles
do not increase, strictly when the initiator carries one. Consumer: `moveRet`. -/
theorem edgeRet (b : Bool) (x y : Cell) (hx : x.c ≠ .inh) (hy : y.c ≠ .inh)
    (hxs : x.i.isS = false) (hys : y.i.isS = false) :
    (pair b false x y).1.i.isS = false ∧ (pair b false x y).2.i.isS = false ∧
      obW (pair b false x y).1 + obW (pair b false x y).2 + (if 0 < obW x then 1 else 0) ≤
        obW x + obW y := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases b <;> cases xi <;> cases xc <;> cases yi <;> cases yc <;>
    revert hx hy hxs hys <;> decide

/-- **The terminal edge without settled input or pending packet.** Consumer: `moveRet`. -/
theorem termRet (x : Cell) (hx : x.c ≠ .inh) (hxs : x.i.isS = false) (hxp : x.i.isP = false) :
    (pair false true x { i := .e, c := .off }).1.i.isS = false ∧
      obW (pair false true x { i := .e, c := .off }).1 + (if 0 < obW x then 1 else 0) ≤ obW x := by
  rcases x with ⟨xi, xc⟩
  cases xi <;> cases xc <;> revert hx hxs hxp <;> decide

/-- The port cleanup. Consumer: `moveRet`. -/
theorem cleanRet (c : Cell) (hcs : c.i.isS = false) :
    (portClean c).i.isS = false ∧ obW (portClean c) ≤ obW c := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> revert hcs <;> decide

/-- The port acceptance. Consumer: `moveRet`. -/
theorem acceptRet (t : Bool) (c : Cell) (hcs : c.i.isS = false) :
    (portAccept t c).i.isS = false ∧ obW (portAccept t c) ≤ obW c := by
  rcases c with ⟨ci, cc⟩
  cases t <;> cases ci <;> cases cc <;> revert hcs <;> decide

/-- No settled input in the window. Consumer: `retMoment`. -/
def NoS (r : Nat) (cells : Nat → Cell) : Prop := ∀ j, j < r → (cells j).i.isS = false

/-- **One move after the settled-empty cut.** While an obstacle stands, no settled input
appears, and the obstacle count does not rise; the move of an obstacle's outgoing edge lowers
it. Consumer: `retMono`, `retDrop`. -/
theorem moveRet (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (m : WMove) (hm : m.Ok r)
    (hni : NoInh r cells) (hbar : Barrier r cells) (hns : NoS r cells)
    (hob : ∃ q, q < r ∧ 0 < obW (cells q)) :
    NoS r (wApply r cells m) ∧
      obS r (wApply r cells m) + (match m with
        | .edge p => if 0 < obW (cells p) then 1 else 0
        | _ => 0) ≤ obS r cells := by
  cases m with
  | frame => exact ⟨hns, Nat.le_refl _⟩
  | clean =>
      have hc := cleanRet (cells 0) (hns 0 (by omega))
      refine ⟨?_, ?_⟩
      · intro j hj
        show (setOne cells 0 (portClean (cells 0)) j).i.isS = false
        unfold setOne
        by_cases h0 : j = 0
        · rw [if_pos h0]; exact hc.1
        · rw [if_neg h0]; exact hns j hj
      · have he := wSEditOne (fun j => obW (cells j))
          (fun j => obW (setOne cells 0 (portClean (cells 0)) j)) 0
          (fun j hj => by simp [setOne, hj]) r (by omega)
        show obS r (setOne cells 0 (portClean (cells 0))) + 0 ≤ obS r cells
        have h0 : obW (setOne cells 0 (portClean (cells 0)) 0) = obW (portClean (cells 0)) := by simp [setOne]
        unfold obS
        have := hc.2
        omega
  | accept t =>
      have hc := acceptRet t (cells 0) (hns 0 (by omega))
      refine ⟨?_, ?_⟩
      · intro j hj
        show (setOne cells 0 (portAccept t (cells 0)) j).i.isS = false
        unfold setOne
        by_cases h0 : j = 0
        · rw [if_pos h0]; exact hc.1
        · rw [if_neg h0]; exact hns j hj
      · have he := wSEditOne (fun j => obW (cells j))
          (fun j => obW (setOne cells 0 (portAccept t (cells 0)) j)) 0
          (fun j hj => by simp [setOne, hj]) r (by omega)
        show obS r (setOne cells 0 (portAccept t (cells 0))) + 0 ≤ obS r cells
        have h0 : obW (setOne cells 0 (portAccept t (cells 0)) 0) = obW (portAccept t (cells 0)) := by simp [setOne]
        unfold obS
        have := hc.2
        omega
  | edge p =>
      have hp : p < r := hm
      show NoS r (edgeStep r cells p) ∧
        obS r (edgeStep r cells p) + (if 0 < obW (cells p) then 1 else 0) ≤ obS r cells
      by_cases hp1 : p + 1 < r
      · unfold edgeStep; rw [if_pos hp1]
        have hc := edgeRet (decide (p = 0)) (cells p) (cells (p + 1)) (hni p (by omega))
          (hni (p + 1) hp1) (hns p (by omega)) (hns (p + 1) hp1)
        refine ⟨?_, ?_⟩
        · intro j hj
          unfold setTwo
          by_cases h1 : j = p
          · rw [if_pos h1]; exact hc.1
          · rw [if_neg h1]
            by_cases h2 : j = p + 1
            · rw [if_pos h2]; exact hc.2.1
            · rw [if_neg h2]; exact hns j hj
        · have he := wSEditPair (fun j => obW (cells j))
            (fun j => obW (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
              (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2 j)) p
            (fun j h1 h2 => by simp [setTwo, h1, h2]) r (by omega)
          have h0 : obW (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
              (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2 p) =
              obW (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1 := by simp [setTwo]
          have h1 : obW (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
              (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2 (p + 1)) =
              obW (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2 := by simp [setTwo]
          unfold obS
          have := hc.2.2
          omega
      · have hpr : r - 1 = p := by omega
        unfold edgeStep; rw [if_neg hp1, hpr]
        have hxp : (cells p).i.isP = false := by
          apply Classical.byContradiction
          intro hP
          obtain ⟨q, hq, hpos⟩ := hob
          have := hbar p q hp hq (by simpa using hP) (obC_of_obW _ hpos)
          omega
        have hc := termRet (cells p) (hni p hp) (hns p hp) hxp
        refine ⟨?_, ?_⟩
        · intro j hj
          unfold setOne
          by_cases h1 : j = p
          · rw [if_pos h1]; exact hc.1
          · rw [if_neg h1]; exact hns j hj
        · have he := wSEditOne (fun j => obW (cells j))
            (fun j => obW (setOne cells p (pair false true (cells p) { i := .e, c := .off }).1 j)) p
            (fun j hj => by simp [setOne, hj]) r (by omega)
          have h0 : obW (setOne cells p (pair false true (cells p) { i := .e, c := .off }).1 p) =
              obW (pair false true (cells p) { i := .e, c := .off }).1 := by simp [setOne]
          unfold obS
          have := hc.2
          omega

/-! ### The phase on the lane and on the coupled chain -/

/-- The packet-only cut: no settled input, no front, no live carry in the target window.
Consumer: `retMoment`. -/
def PacketOnly (R : Nat) (s : CohortLane) : Prop :=
  ∀ j, j < R → (winOf R s j).i.isS = false ∧ obW (winOf R s j) = 0

/-- The invariant of the phase. Consumer: `retMoment`. -/
def RetInv (R : Nat) (s : CohortLane) : Prop := NoS R (winOf R s) ∧ Barrier R (winOf R s)

/-- Off the packet-only cut an obstacle stands. Consumer: `retMoment`. -/
theorem retObstacle (R : Nat) (s : CohortLane) (h : RetInv R s) (hn : ¬ PacketOnly R s) :
    ∃ q, q < R ∧ 0 < obW (winOf R s q) := by
  apply Classical.byContradiction
  intro hq
  exact hn (fun j hj => ⟨h.1 j hj, by
    apply Classical.byContradiction
    intro h0
    exact hq ⟨j, hj, by omega⟩⟩)

/-- **Retirement on the lane.** From every lane state with no settled input and the packet
barrier, the packet-only cut is reached with `E[z^{T}] ≤ w^{obS}`. Consumer:
`retMomentCoupled`. -/
theorem retMoment {n : Nat} (R : Nat) (hR : 2 ≤ R) (hn : 1 ≤ n) (N : Nat) (hN : n ≤ N)
    (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) (s : CohortLane) (hs : RetInv R s) :
    MomentBoundQ (releaseNext R edgeOf) (PacketOnly R) N (N ^ obS R (winOf R s))
      ((N - n) ^ obS R (winOf R s)) s := by
  let P' : CohortLane → Prop := fun y => PacketOnly R y ∨ ¬ RetInv R y
  have hstep : ∀ y, RetInv R y → ¬ PacketOnly R y → ∀ o : Option Nat,
      RetInv R (cohortLaneStep R y o) ∧
        obS R (winOf R (cohortLaneStep R y o)) ≤ obS R (winOf R y) := by
    intro y hy hn o
    have hob := retObstacle R y hy hn
    have hni : NoInh R (winOf R y) := fun _ _ => liftC_ne_inh _ _
    show (NoS R (winOf R (cohortLaneStep R y o)) ∧ Barrier R (winOf R (cohortLaneStep R y o))) ∧
      obS R (winOf R (cohortLaneStep R y o)) ≤ obS R (winOf R y)
    rw [laneWinOpt]
    have hm := moveRet R hR (winOf R y) _ (laneMoveOptOk R y o) hni hy.2 hy.1 hob
    refine ⟨⟨hm.1, barrier_step R hR _ _ hy.2 hni (moveStep R _ _ (laneMoveOptOk R y o))⟩, ?_⟩
    have := hm.2
    split at this <;> omega
  have hex : ∀ y, ∃ e : Fin n, ¬ P' y →
      obS R (winOf R (releaseNext R edgeOf y e)) + 1 ≤ obS R (winOf R y) := by
    intro y
    by_cases hy : P' y
    · exact ⟨site 0, fun h => absurd hy h⟩
    · have h1 : ¬ PacketOnly R y := fun h => hy (Or.inl h)
      have h2 : RetInv R y := Classical.byContradiction fun h => hy (Or.inr h)
      obtain ⟨q, hq, hpos⟩ := retObstacle R y h2 h1
      refine ⟨site (R + q), fun _ => ?_⟩
      show obS R (winOf R (cohortLaneStep R y (edgeOf (site (R + q))))) + 1 ≤ _
      rw [hedge (R + q) (by omega)]
      show obS R (winOf R (cohortEdge R y (R + q))) + 1 ≤ _
      rw [laneWin, laneMoveEdge R y q hq]
      have hm := moveRet R hR (winOf R y) (.edge q) hq (fun _ _ => liftC_ne_inh _ _) h2.2 h2.1
        ⟨q, hq, hpos⟩
      have := hm.2
      simp only [if_pos hpos] at this
      exact this
  have hP' := momentOfPotential (releaseNext R edgeOf) P' N (fun y => obS R (winOf R y))
    (fun y => Classical.choose (hex y)) hn hN
    (fun y hy => Classical.choose_spec (hex y) hy)
    (fun y hy e => by
      have h1 : ¬ PacketOnly R y := fun h => hy (Or.inl h)
      have h2 : RetInv R y := Classical.byContradiction fun h => hy (Or.inr h)
      exact (hstep y h2 h1 (edgeOf e)).2) s
  exact momentSimQ (releaseNext R edgeOf) (releaseNext R edgeOf)
    (fun a b => a = b ∧ RetInv R a) (PacketOnly R) P' N _ _
    (fun a b e hab hna => by
      obtain ⟨rfl, hi⟩ := hab
      exact ⟨rfl, (hstep a hi hna (edgeOf e)).1⟩)
    (fun a b hab hg => by
      obtain ⟨rfl, hi⟩ := hab
      rcases hg with hg | hg
      · exact hg
      · exact absurd hi hg) s s ⟨rfl, hs⟩ hP'

/-- **Lemma e-packet, retirement, on the coupled chain.** From every layout state whose target
window has no settled input (the settled-empty cut of phase U) and the packet barrier
(`L3.PacketMomentU.winKeepCoupled`), the packet-only cut is reached with
`E[z^{T}] ≤ w^{2R}`, `w = N/(N-n)`, uniformly over source registers and audit.
Consumer: the per-pair moment (`E[z^{T_pair}] < 40`, Lemma e-max), the `+ r` of phase U. -/
theorem retMomentCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : RetInv R (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => PacketOnly R (laneOfState ring hbank root lane src R y)) N
      (N ^ (2 * R)) ((N - n) ^ (2 * R)) x := by
  have hlane := retMoment R hR (by omega) N (Nat.le_of_lt hN)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk)
    (laneOfState ring hbank root lane src R x) hs
  have hco := momentSimQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (releaseNext R (cohortEdgeOf root src R))
    (fun y s => CohortLayout ring hbank root src R y.1 ∧ laneOfState ring hbank root lane src R y = s)
    (fun y => PacketOnly R (laneOfState ring hbank root lane src R y)) (PacketOnly R) N _ _
    (fun y s e hys _ => by
      obtain ⟨hl, hs⟩ := hys
      obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R hR hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs]
      rfl)
    (fun y s hys hg => by rw [hys.2]; exact hg) x _ ⟨hx, rfl⟩ hlane
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ hco
  exact powCross N n _ _ (obS_le R _)

/-- The settled-empty cut of phase U, with the barrier kept from its start
(`L3.PacketMomentU.winKeepCoupled`), starts the retirement. Consumer: the per-pair moment
(composition of `uMomentCoupled` and `retMomentCoupled` by `momentSeq`). -/
theorem retStartOfU (R : Nat) (s : CohortLane) (hs : ¬ WinSettled R s)
    (hbar : Barrier R (winOf R s)) : RetInv R s := by
  refine ⟨fun j hj => ?_, hbar⟩
  cases h : (winOf R s j).i.isS with
  | false => rfl
  | true => exact absurd ⟨j, hj, h⟩ hs

end L3.PacketMomentRetire

#print axioms L3.PacketMomentRetire.edgeRet
#print axioms L3.PacketMomentRetire.moveRet
#print axioms L3.PacketMomentRetire.retMoment
#print axioms L3.PacketMomentRetire.retMomentCoupled
#print axioms L3.PacketMomentRetire.retStartOfU

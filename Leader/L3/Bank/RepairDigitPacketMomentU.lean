import Leader.L3.Bank.RepairDigitPacketMomentSupply
import Leader.L3.Bank.RepairDigitPacketMomentRelease

/-!
# Lemma e-packet, phase U in moment form: the settled-empty cut

The Q7 settled-work potential, read on the e-packet lane (`L3.PacketMomentWindow`,
`L3.PacketMomentSupply`), with the Q7 history colouring as a ghost component:

`uPot = A * uK + uStage`, where `A` is the active charge (paper `A`), and
`uStage = thL` on a front-free window (supply potential `Gv + dist`), otherwise
`2R^2 + R + 3 + M` (`M = 2D + X`, paper `2D + X`).

Off the settled-empty target, with the window invariants (`WinInv`: fresh-carry invariant,
no inherited carry, packet barrier, front cover of the doomed runs), no edge raises `uPot`
(`uMono`) and a nominated edge lowers it (`uDrop`). `momentOfPotential` then gives
`E[z^{T_U}] ≤ w^{uPot} ≤ w^{uBudget R}`, `w = N/(N-n)`, on the lane (`uMoment`) and on the
coupled BANK x audit chain (`uMomentCoupled`), from every layout state whose window has the
fresh-carry invariant and the packet barrier, in particular from every mobile-free cut
(`winStartMobileFree`). `uBudget R = (R^2 + 1)(2R^2 + 4R + 4)`; the paper's
`U = r^2 (2r^2 + 8r + 1) + 5r`.
-/

namespace L3.PacketMomentU

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
open L3.PacketMomentRelease
open L3.MarkedCells
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentSupply

/-! ### The chain with the colouring ghost -/

/-- The window move of a scheduler letter. Consumer: `uNext`. -/
def laneMoveOpt (R : Nat) (s : CohortLane) : Option Nat → WMove
  | none => .frame
  | some k => laneMove R s k

/-- A letter acts on the window by its move. Consumer: `uMono`. -/
theorem laneWinOpt (R : Nat) (s : CohortLane) (o : Option Nat) :
    winOf R (cohortLaneStep R s o) = wApply R (winOf R s) (laneMoveOpt R s o) := by
  cases o with
  | none => rfl
  | some k => exact laneWin R s k

/-- Letter moves are legal. Consumer: `uMono`. -/
theorem laneMoveOptOk (R : Nat) (s : CohortLane) (o : Option Nat) : (laneMoveOpt R s o).Ok R := by
  cases o with
  | none => trivial
  | some k => exact laneMoveOk R s k

/-- The lane with the Q7 history colouring. Consumer: `uMoment`. -/
def uNext {n : Nat} (R : Nat) (edgeOf : Fin n → Option Nat) (x : CohortLane × (Nat → Prop))
    (e : Fin n) : CohortLane × (Nat → Prop) :=
  (cohortLaneStep R x.1 (edgeOf e), moveColour R (winOf R x.1) (laneMoveOpt R x.1 (edgeOf e)) x.2)

/-- A settled input stands in the target window. Consumer: `uMoment`. -/
def WinSettled (R : Nat) (s : CohortLane) : Prop := ∃ j, j < R ∧ (winOf R s j).i.isS = true

/-- No front in the target window. Consumer: `uStage`. -/
def WinFrontFree (R : Nat) (s : CohortLane) : Prop := ∀ p, p < R → (winOf R s p).i ≠ .x

/-- The level width. Consumer: `uPot`. -/
def uK (R : Nat) : Nat := 2 * (R * R) + 4 * R + 4

/-- The stage potential. Consumer: `uPot`. -/
noncomputable def uStage (R : Nat) (x : CohortLane × (Nat → Prop)) : Nat :=
  if WinFrontFree R x.1 then thL R x.1 else (2 * (R * R) + R + 3) + Mn R (winOf R x.1) x.2

/-- **The phase-U potential.** Consumer: `uMoment`. -/
noncomputable def uPot (R : Nat) (x : CohortLane × (Nat → Prop)) : Nat :=
  charge R (act R (winOf R x.1) x.2) * uK R + uStage R x

/-- The budget. Consumer: `uMomentCoupled`. -/
def uBudget (R : Nat) : Nat := (R * R + 1) * uK R

/-- The stage potential is below the level width. Consumer: `uPot_le`, `uMono`, `uDrop`. -/
theorem uStage_lt (R : Nat) (hR : 1 ≤ R) (x : CohortLane × (Nat → Prop)) :
    uStage R x + 1 ≤ uK R := by
  unfold uStage uK
  have h1 := thL_le R hR x.1
  have h2 := Mn_le R (winOf R x.1) x.2
  split <;> omega

/-- The potential is within the budget. Consumer: `uMomentCoupled`. -/
theorem uPot_le (R : Nat) (hR : 1 ≤ R) (x : CohortLane × (Nat → Prop)) :
    uPot R x ≤ uBudget R := by
  have h1 := charge_le (act R (winOf R x.1) x.2) R
  have h2 := uStage_lt R hR x
  have h3 := Nat.mul_le_mul_right (uK R) h1
  unfold uPot uBudget
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Lexicographic comparison. Consumer: `uMono`, `uDrop`. -/
theorem lexLe (K A A' S S' : Nat) (hS' : S' + 1 ≤ K) (hA : A' ≤ A)
    (h : A' < A ∨ S' ≤ S) : A' * K + S' ≤ A * K + S := by
  rcases h with h | h
  · have := Nat.mul_le_mul_right K (show A' + 1 ≤ A by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · have := Nat.mul_le_mul_right K hA
    omega

/-- Strict lexicographic comparison. Consumer: `uDrop`. -/
theorem lexLt (K A A' S S' : Nat) (hS' : S' + 1 ≤ K) (hA : A' ≤ A)
    (h : A' < A ∨ S' + 1 ≤ S) : A' * K + S' + 1 ≤ A * K + S := by
  rcases h with h | h
  · have := Nat.mul_le_mul_right K (show A' + 1 ≤ A by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · have := Nat.mul_le_mul_right K hA
    omega

/-- One letter at zero front debt. Consumer: `uMono`. -/
theorem laneThOpt (R : Nat) (hR : 3 ≤ R) (s : CohortLane) (d : Nat → Prop) (o : Option Nat)
    (h : WinInv R (winOf R s) d) (hex : WinSettled R s) (hM : Mn R (winOf R s) d = 0) :
    charge R (act R (winOf R (cohortLaneStep R s o))
        (moveColour R (winOf R s) (laneMoveOpt R s o) d)) < charge R (act R (winOf R s) d) ∨
    (Mn R (winOf R (cohortLaneStep R s o)) (moveColour R (winOf R s) (laneMoveOpt R s o) d) = 0 ∧
      thL R (cohortLaneStep R s o) ≤ thL R s) := by
  cases o with
  | none =>
      rcases moveGood R hR (winOf R s) d .frame trivial h hex hM with h1 | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, Nat.le_refl _⟩
  | some k =>
      rcases laneTh R hR s d k h hex hM with h1 | ⟨h1, h2, _⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩

/-- **No letter raises the phase-U potential** off the settled-empty target.
Consumer: `uMoment`. -/
theorem uMono {n : Nat} (R : Nat) (hR : 3 ≤ R) (edgeOf : Fin n → Option Nat)
    (x : CohortLane × (Nat → Prop)) (h : WinInv R (winOf R x.1) x.2) (hex : WinSettled R x.1)
    (e : Fin n) : uPot R (uNext R edgeOf x e) ≤ uPot R x := by
  obtain ⟨s, d⟩ := x
  simp only at h hex
  have hW := laneWinOpt R s (edgeOf e)
  have hch := moveCharge R (by omega) (winOf R s) d _ (laneMoveOptOk R s (edgeOf e)) h hex
  have hpot := movePot R (by omega) (winOf R s) d _ (laneMoveOptOk R s (edgeOf e)) h hex
  rw [← hW] at hch hpot
  have hS' := uStage_lt R (by omega) (uNext R edgeOf (s, d) e)
  unfold uPot
  show charge R (act R (winOf R (cohortLaneStep R s (edgeOf e)))
      (moveColour R (winOf R s) (laneMoveOpt R s (edgeOf e)) d)) * uK R +
    uStage R (uNext R edgeOf (s, d) e) ≤ _
  refine lexLe _ _ _ _ _ hS' hch ?_
  by_cases hlt : charge R (act R (winOf R (cohortLaneStep R s (edgeOf e)))
      (moveColour R (winOf R s) (laneMoveOpt R s (edgeOf e)) d)) < charge R (act R (winOf R s) d)
  · exact Or.inl hlt
  right
  have hst' : uStage R (uNext R edgeOf (s, d) e) =
      if WinFrontFree R (cohortLaneStep R s (edgeOf e)) then thL R (cohortLaneStep R s (edgeOf e))
      else (2 * (R * R) + R + 3) + Mn R (winOf R (cohortLaneStep R s (edgeOf e)))
        (moveColour R (winOf R s) (laneMoveOpt R s (edgeOf e)) d) := rfl
  have hst : uStage R (s, d) = if WinFrontFree R s then thL R s
      else (2 * (R * R) + R + 3) + Mn R (winOf R s) d := rfl
  rw [hst', hst]
  have hthl := thL_le R (by omega) (cohortLaneStep R s (edgeOf e))
  by_cases hff : WinFrontFree R s
  · rw [if_pos hff]
    have hM := frontfree_mn_zero R (winOf R s) d h.cov h.lt hff
    rcases laneThOpt R hR s d (edgeOf e) h hex hM with h1 | ⟨hM', hth⟩
    · exact absurd h1 hlt
    · have hff' : WinFrontFree R (cohortLaneStep R s (edgeOf e)) := (mn_zero_facts _ _ _ hM').1
      rw [if_pos hff']; exact hth
  · rw [if_neg hff]
    have heq : charge R (act R (winOf R (cohortLaneStep R s (edgeOf e)))
        (moveColour R (winOf R s) (laneMoveOpt R s (edgeOf e)) d)) =
        charge R (act R (winOf R s) d) := by omega
    unfold Pot at hpot
    rw [heq] at hpot
    split
    · omega
    · omega

/-- A window that is not front-free has a front. Consumer: `uDrop`. -/
theorem frontSite (R : Nat) (s : CohortLane) (h : ¬ WinFrontFree R s) :
    ∃ p, p < R ∧ (winOf R s p).i = .x := by
  apply Classical.byContradiction
  intro hn
  exact h (fun p hp hx => hn ⟨p, hp, hx⟩)

/-- **A nominated letter lowers the phase-U potential** off the settled-empty target.
Consumer: `uMoment`. -/
theorem uDrop {n : Nat} (R : Nat) (hR : 3 ≤ R) (site : Nat → Fin n)
    (edgeOf : Fin n → Option Nat) (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k)
    (x : CohortLane × (Nat → Prop)) (h : WinInv R (winOf R x.1) x.2) (hex : WinSettled R x.1) :
    ∃ e : Fin n, uPot R (uNext R edgeOf x e) + 1 ≤ uPot R x := by
  obtain ⟨s, d⟩ := x
  simp only at h hex
  have key : ∀ k, k < 2 * R →
      (charge R (act R (winOf R (cohortEdge R s k))
          (moveColour R (winOf R s) (laneMove R s k) d)) < charge R (act R (winOf R s) d) ∨
        uStage R (cohortEdge R s k, moveColour R (winOf R s) (laneMove R s k) d) + 1 ≤
          uStage R (s, d)) →
      ∃ e : Fin n, uPot R (uNext R edgeOf (s, d) e) + 1 ≤ uPot R (s, d) := by
    intro k hk hc
    refine ⟨site k, ?_⟩
    have hsk : uNext R edgeOf (s, d) (site k) =
        (cohortEdge R s k, moveColour R (winOf R s) (laneMove R s k) d) := by
      unfold uNext; rw [hedge k hk]; rfl
    rw [hsk]
    have hch := moveCharge R (by omega) (winOf R s) d _ (laneMoveOk R s k) h hex
    rw [← laneWin R s k] at hch
    have hS' := uStage_lt R (by omega) (cohortEdge R s k, moveColour R (winOf R s) (laneMove R s k) d)
    exact lexLt _ _ _ _ _ hS' hch hc
  have hst : uStage R (s, d) = if WinFrontFree R s then thL R s
      else (2 * (R * R) + R + 3) + Mn R (winOf R s) d := rfl
  by_cases hff : WinFrontFree R s
  · have hM := frontfree_mn_zero R (winOf R s) d h.cov h.lt hff
    obtain ⟨k, hk, hc⟩ := laneThStrict R hR s d h hex hM
    refine key k hk ?_
    rcases hc with h1 | ⟨hM', hth⟩
    · exact Or.inl h1
    · right
      have hff' : WinFrontFree R (cohortEdge R s k) := (mn_zero_facts _ _ _ hM').1
      have hst' : uStage R (cohortEdge R s k, moveColour R (winOf R s) (laneMove R s k) d) =
          thL R (cohortEdge R s k) := by
        show (if WinFrontFree R (cohortEdge R s k) then _ else _) = _
        rw [if_pos hff']
      rw [hst', hst, if_pos hff]
      omega
  · obtain ⟨p, hp, hxx⟩ := frontSite R s hff
    have hpot := moveFront R (by omega) (winOf R s) d p hp h hex hxx
    have hch := moveCharge R (by omega) (winOf R s) d (.edge p) hp h hex
    have hmv := laneMoveEdge R s p hp
    have hW : winOf R (cohortEdge R s (R + p)) = wApply R (winOf R s) (.edge p) := by
      rw [laneWin, hmv]
    refine key (R + p) (by omega) ?_
    rw [hmv, hW]
    by_cases hlt : charge R (act R (wApply R (winOf R s) (.edge p))
        (moveColour R (winOf R s) (.edge p) d)) < charge R (act R (winOf R s) d)
    · exact Or.inl hlt
    · right
      have heq : charge R (act R (wApply R (winOf R s) (.edge p))
          (moveColour R (winOf R s) (.edge p) d)) = charge R (act R (winOf R s) d) := by omega
      unfold Pot at hpot
      rw [heq] at hpot
      have hthl := thL_le R (by omega) (cohortEdge R s (R + p))
      have hst' : uStage R (cohortEdge R s (R + p), moveColour R (winOf R s) (.edge p) d) =
          if WinFrontFree R (cohortEdge R s (R + p)) then thL R (cohortEdge R s (R + p))
          else (2 * (R * R) + R + 3) + Mn R (wApply R (winOf R s) (.edge p))
            (moveColour R (winOf R s) (.edge p) d) := by
        show (if WinFrontFree R (cohortEdge R s (R + p)) then _ else _) = _
        rw [hW]
      rw [hst', hst, if_neg hff]
      split <;> omega

/-! ### The moment -/

/-- The window invariants are kept by every letter. Consumer: `uMoment`. -/
theorem uInv {n : Nat} (R : Nat) (hR : 2 ≤ R) (edgeOf : Fin n → Option Nat)
    (x : CohortLane × (Nat → Prop)) (h : WinInv R (winOf R x.1) x.2) (e : Fin n) :
    WinInv R (winOf R (uNext R edgeOf x e).1) (uNext R edgeOf x e).2 := by
  show WinInv R (winOf R (cohortLaneStep R x.1 (edgeOf e)))
    (moveColour R (winOf R x.1) (laneMoveOpt R x.1 (edgeOf e)) x.2)
  rw [laneWinOpt]
  exact moveInv R hR _ _ _ (laneMoveOptOk R x.1 (edgeOf e)) h

/-- **Phase U on the lane.** From every lane state whose window has the invariants, the
settled-empty cut is reached with `E[z^{T_U}] ≤ w^{uPot}`, `w = N/(N-n)`.
Consumer: `uMomentCoupled`. -/
theorem uMoment {n : Nat} (R : Nat) (hR : 3 ≤ R) (hn : 1 ≤ n) (N : Nat) (hN : n ≤ N)
    (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) (x : CohortLane × (Nat → Prop))
    (hx : WinInv R (winOf R x.1) x.2) :
    MomentBoundQ (uNext R edgeOf) (fun y => ¬ WinSettled R y.1) N (N ^ uPot R x)
      ((N - n) ^ uPot R x) x := by
  let P' : CohortLane × (Nat → Prop) → Prop := fun y =>
    ¬ WinSettled R y.1 ∨ ¬ WinInv R (winOf R y.1) y.2
  have hex : ∀ y, ∃ e : Fin n, ¬ P' y → uPot R (uNext R edgeOf y e) + 1 ≤ uPot R y := by
    intro y
    by_cases hy : P' y
    · exact ⟨site 0, fun h => absurd hy h⟩
    · have h1 : WinSettled R y.1 := Classical.byContradiction fun h => hy (Or.inl h)
      have h2 : WinInv R (winOf R y.1) y.2 := Classical.byContradiction fun h => hy (Or.inr h)
      obtain ⟨e, he⟩ := uDrop R hR site edgeOf hedge y h2 h1
      exact ⟨e, fun _ => he⟩
  have hP' := momentOfPotential (uNext R edgeOf) P' N (uPot R)
    (fun y => Classical.choose (hex y)) hn hN
    (fun y hy => Classical.choose_spec (hex y) hy)
    (fun y hy e => by
      have h1 : WinSettled R y.1 := Classical.byContradiction fun h => hy (Or.inl h)
      have h2 : WinInv R (winOf R y.1) y.2 := Classical.byContradiction fun h => hy (Or.inr h)
      exact uMono R hR edgeOf y h2 h1 e) x
  exact momentSimQ (uNext R edgeOf) (uNext R edgeOf)
    (fun a b => a = b ∧ WinInv R (winOf R a.1) a.2) (fun y => ¬ WinSettled R y.1) P' N _ _
    (fun a b e hab _ => by
      obtain ⟨rfl, hi⟩ := hab
      exact ⟨rfl, uInv R (by omega) edgeOf a hi e⟩)
    (fun a b hab hg => by
      obtain ⟨rfl, hi⟩ := hab
      rcases hg with hg | hg
      · exact hg
      · exact absurd hi hg) x x ⟨rfl, hx⟩ hP'

/-- The start of phase U: the fresh-carry invariant and the packet barrier of the window, with
the colouring that marks nothing doomed. Consumer: `uMomentCoupled`. -/
theorem winStart (R : Nat) (s : CohortLane) (hinv : Inv R (winOf R s))
    (hbar : Barrier R (winOf R s)) : WinInv R (winOf R s) (fun _ => False) :=
  { inv := hinv
    ni := fun _ _ => liftC_ne_inh _ _
    bar := hbar
    cov := fun _ hu => absurd hu id
    lt := fun _ hu => absurd hu id }

/-- **A mobile-free cut starts phase U**: no carry and only empty or settled target inputs.
Consumer: `uMomentCoupled` (start at the mobile-free cut of the inherited-work phase). -/
theorem winStartMobileFree (R : Nat) (s : CohortLane)
    (h : ∀ q, R ≤ q → q < 2 * R → s.live q = false ∧ (s.inp q = .E ∨ ∃ T, s.inp q = .S T)) :
    Inv R (winOf R s) ∧ Barrier R (winOf R s) := by
  have hoff : ∀ j, j < R → (winOf R s j).c = .off := by
    intro j hj
    have := (h (R + j) (by omega) (by omega)).1
    simp [winOf, liftC, this]
  refine ⟨⟨fun j hj hf => absurd hf (by rw [hoff j hj]; simp),
    fun j k hj _ hf _ => absurd hf (by rw [hoff j hj]; simp)⟩, ?_⟩
  intro i j hi _ hP _
  exfalso
  rcases (h (R + i) (by omega) (by omega)).2 with hE | ⟨T, hS⟩
  · simp [winOf, liftC, hE, cellIn, Inp.isP] at hP
  · cases T <;> simp [winOf, liftC, hS, cellIn, Inp.isP] at hP

/-- **Lemma e-packet, phase U, on the coupled chain.** From every layout state of the coupled
BANK x audit chain whose target window has the fresh-carry invariant and the packet barrier
(e.g. a mobile-free cut, `winStartMobileFree`), the settled-empty cut of the pair's target is
reached with `E[z^{T_U}] ≤ w^{uBudget R}`, `w = N/(N-n)`, uniformly over source registers and
audit. Consumer: the per-pair moment (`E[z^{T_pair}] < 40`, Lemma e-max), phase U of the
attempt and of the failure return. -/
theorem uMomentCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hinv : Inv R (winOf R (laneOfState ring hbank root lane src R x)))
    (hbar : Barrier R (winOf R (laneOfState ring hbank root lane src R x))) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => ¬ WinSettled R (laneOfState ring hbank root lane src R y)) N
      (N ^ uBudget R) ((N - n) ^ uBudget R) x := by
  have hlane := uMoment R hR (by omega) N (Nat.le_of_lt hN)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk)
    (laneOfState ring hbank root lane src R x, fun _ => False)
    (winStart R _ hinv hbar)
  have hco := momentSimQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (uNext R (cohortEdgeOf root src R))
    (fun y z => CohortLayout ring hbank root src R y.1 ∧
      laneOfState ring hbank root lane src R y = z.1)
    (fun y => ¬ WinSettled R (laneOfState ring hbank root lane src R y))
    (fun z => ¬ WinSettled R z.1) N _ _
    (fun y z e hyz _ => by
      obtain ⟨hl, hs⟩ := hyz
      obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R (by omega) hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs]
      rfl)
    (fun y z hyz hg => by rw [hyz.2]; exact hg) x _ ⟨hx, rfl⟩ hlane
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ hco
  exact powCross N n _ _ (uPot_le R (by omega) _)

/-- **The fresh-carry invariant and the packet barrier are kept by every letter** (they hold
along the whole continuation of a mobile-free cut, in particular at the failure return of the
renewal trial). Consumer: the per-pair moment (failure return to phase U). -/
theorem winKeep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (o : Option Nat)
    (h : Inv R (winOf R s) ∧ Barrier R (winOf R s)) :
    Inv R (winOf R (cohortLaneStep R s o)) ∧ Barrier R (winOf R (cohortLaneStep R s o)) := by
  rw [laneWinOpt]
  have hs := moveStep R (winOf R s) _ (laneMoveOptOk R s o)
  exact ⟨inv_step R hR _ _ h.1 hs,
    barrier_step R hR _ _ h.2 (fun _ _ => liftC_ne_inh _ _) hs⟩

/-- The invariant and the barrier on the coupled chain. Consumer: as `winKeep`. -/
theorem winKeepCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (h : Inv R (winOf R (laneOfState ring hbank root lane src R x)) ∧
      Barrier R (winOf R (laneOfState ring hbank root lane src R x))) (e : Fin n) :
    CohortLayout ring hbank root src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1 ∧
      Inv R (winOf R (laneOfState ring hbank root lane src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e))) ∧
      Barrier R (winOf R (laneOfState ring hbank root lane src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e))) := by
  obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R hR hsrc hend x hx e
  rw [h2]
  exact ⟨h1, winKeep R hR _ _ h⟩

end L3.PacketMomentU

#print axioms L3.PacketMomentU.uMono
#print axioms L3.PacketMomentU.uDrop
#print axioms L3.PacketMomentU.uMoment
#print axioms L3.PacketMomentU.winStartMobileFree
#print axioms L3.PacketMomentU.uMomentCoupled
#print axioms L3.PacketMomentU.winKeep
#print axioms L3.PacketMomentU.winKeepCoupled

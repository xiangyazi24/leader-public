import Leader.L3.Bank.RepairDigitCurrentWin
import Leader.L3.Bank.RepairDigitTailChain

/-!
# The entry fact at a completion terminal: the barrier behind a border tail

Fix one complete pair and lane. A border-tail sample `sigma` (read at the source delimiter) is a
one-way barrier while it travels through the window: as a source packet `D true` at cell `c < R`,
as a pending target input `P true`, as the settled border operand `S true` at `R`, and finally
as the first use of a clean live carry. Everything behind it (cells `q < c`) was rearmed by it
or produced after it. This module proves, on the lane cells of one pair and generic in the
compiled protocol:

* `BarShape`: the shape behind the barrier at `c` is the rearmed (younger) source block while
  `c < R`, and a chosen cohort below `c` with its younger cohort behind it once `c ≥ R`
  (`CohortChosen`, `CohortYounger` of the generated class);
* `BarAt`: the four barrier locations of `sigma`;
* `barAtBack`: one letter moves a barrier location only by a hop of the barrier itself
  (the cell left behind is unread or empty), keeps it in place, or creates it by the border read;
* `BarInv`: at every barrier location, the shape behind it, the clock bound of `sigma` and the
  age of every tracked atom behind it (sampled after `sigma`); `barInvStep` keeps it under every
  letter;
* `termEntry`: at a terminal letter fired by a live last carry whose clean ledger starts with
  `sigma`, the post-terminal lane is in the cycle class (old cohort gone) and the aged window
  `WinAge sigma.time` holds.

Model check: research/lean-l3/ledgers/close-mc.py, clauses `bar_A`, `bar_B`, `bar_B'`, `bar_C`,
`term_cyc`, `term_age` (close-family-notes section 12).
-/

namespace L3.TermEntry

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.CohortEntry
open L3.CohortTail
open L3.PacketClass
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.UseRows
open L3.UseCells
open L3.CurrentWin
open L3.CohortWindow

/-! ### Shapes behind the barrier -/

section Shapes

variable {R : Nat} {s : CohortLane}

/-- The shape behind a barrier at cell `c`: the younger source block while `c < R`, a chosen
cohort below `c` with its younger cohort once `c ≥ R`.  Consumer: `BarInv`, `termEntry`. -/
def BarShape (R : Nat) (s : CohortLane) (c : Nat) : Prop :=
  (c < R → CohortYounger R s c) ∧
  (R ≤ c → ∃ lam : Nat → Nat, CohortChosen R s lam c ∧ CohortYounger R s (lam (R - 1)))

/-- The barrier cell is occupied, and settled only at the target delimiter.  Consumer:
`barShapeStay`. -/
def BarBlock (R : Nat) (s : CohortLane) (c : Nat) : Prop :=
  cohortTok R s c ≠ .empty ∧ ∀ T, cohortTok R s c = .settled T → c ≤ R

/-- A chosen cohort below a cell short of the last target cell has its tail in the source.
Consumer: `barShapeStay`, `barShapeMoveTgt`, `termEntry`. -/
theorem chosenTailLt {lam : Nat → Nat} {c : Nat} (h : CohortChosen R s lam c)
    (hc : c < 2 * R) : lam (R - 1) < R := by
  have hR := h.two
  have hl := h.low 0 (by omega)
  have hch := chosenChain h 0 (R - 1) (by omega) (by omega)
  unfold cohortPos at hl
  omega

/-- **Every letter keeps the shape behind a blocking barrier.**  Consumer: `barInvStep`. -/
theorem barShapeStay (hR : 2 ≤ R) {c : Nat} (h : BarShape R s c) (hc : c < 2 * R)
    (hb : BarBlock R s c) (k : Nat) : BarShape R (cohortEdge R s k) c := by
  refine ⟨fun hcR => youngerEdge hR (h.1 hcR) (Nat.le_of_lt hcR) hb.1 k, fun hRc => ?_⟩
  obtain ⟨lam, hch, hY⟩ := h.2 hRc
  have hpre := chosenTailLt hch hc
  exact ⟨cohortGenGhost R s lam k, (chosenEdge hch hpre (fun _ => hb) k).1,
    youngerGen hch hpre hY k⟩

/-- The same along the lane step of any letter.  Consumer: `barInvStep`. -/
theorem barShapeLane (hR : 2 ≤ R) {c : Nat} (h : BarShape R s c) (hc : c < 2 * R)
    (hb : BarBlock R s c) : ∀ ke : Option Nat, BarShape R (cohortLaneStep R s ke) c
  | none => h
  | some k => barShapeStay hR h hc hb k

/-- The younger block grows by the cell the barrier leaves unread.  Consumer:
`barShapeMoveSrc`. -/
theorem youngerMove (hR : 2 ≤ R) {c : Nat} (hY : CohortYounger R s c) (hcR : c < R)
    (hocc : cohortTok R s c ≠ .empty) (hu : cohortTok R (cohortEdge R s c) c = .other) :
    CohortYounger R (cohortEdge R s c) (c + 1) := by
  have h1 := youngerEdge hR hY (Nat.le_of_lt hcR) hocc c
  intro q hq hqR
  by_cases hqc : q < c
  · exact h1 q hqc hqR
  · have hqe : q = c := by omega
    subst hqe
    exact Or.inl hu

/-- A fully rearmed source block is a chosen cohort that has not moved.  Consumer:
`barShapeMoveSrc`. -/
theorem chosenOfYounger (hR : 2 ≤ R) (hY : CohortYounger R s R) :
    CohortChosen R s (fun _ => 0) R := by
  refine ⟨hR, by omega, fun _ _ => Nat.zero_le _, fun _ _ => Nat.le_refl _, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [cohortPosZero]
    omega
  · intro i hi
    rw [cohortPosZero]
    rcases hY (R - 1 - i) (by omega) (by omega) with h1 | h1
    · exact Or.inr (Or.inr ⟨h1, rfl⟩)
    · left
      rw [h1]
      congr 1
      unfold cohortTail
      by_cases hi0 : R - 1 - i = 0
      · rw [decide_eq_true hi0, decide_eq_true (show i + 1 = R by omega)]
      · rw [decide_eq_false hi0, decide_eq_false (show ¬ (i + 1 = R) by omega)]
  · intro i _ hi hs
    rw [cohortPosZero, cohortTokSrc s (by omega)] at hs
    exact absurd hs (cohortTokOutNe _ _)
  · intro q hq _ hnq
    exfalso
    exact hnq (R - 1 - q) (by omega) (by rw [cohortPosZero]; omega)

/-- **A source barrier hop** (the left cell turns unread).  Consumer: `barInvStep`. -/
theorem barShapeMoveSrc (hR : 2 ≤ R) {c : Nat} (h : BarShape R s c) (hcR : c < R)
    (hocc : cohortTok R s c ≠ .empty) (hu : cohortTok R (cohortEdge R s c) c = .other) :
    BarShape R (cohortEdge R s c) (c + 1) := by
  have hY := youngerMove hR (h.1 hcR) hcR hocc hu
  refine ⟨fun _ => hY, fun hRc => ?_⟩
  have hcR' : c + 1 = R := by omega
  rw [hcR'] at hY ⊢
  exact ⟨fun _ => 0, chosenOfYounger hR hY, cohortRearmInit _ rfl⟩

/-- **A target barrier hop** (the left cell turns empty).  Consumer: `barInvStep`. -/
theorem barShapeMoveTgt (hR : 2 ≤ R) {c : Nat} (h : BarShape R s c) (hRc : R ≤ c)
    (hc : c + 1 < 2 * R) (hb : BarBlock R s c)
    (he : cohortTok R (cohortEdge R s c) c = .empty) :
    BarShape R (cohortEdge R s c) (c + 1) := by
  obtain ⟨lam, hch, hY⟩ := h.2 hRc
  have hpre := chosenTailLt hch (by omega)
  have hch' := (chosenEdge hch hpre (fun _ => hb) c).1
  refine ⟨fun h' => absurd h' (by omega), fun _ =>
    ⟨cohortGenGhost R s lam c, ?_, youngerGen hch hpre hY c⟩⟩
  refine chosenExtend hch' (Nat.le_succ c) (by omega) (fun q h1 h2 => ?_)
  have hqc : q = c := by omega
  subst hqc
  exact he

/-- A settled chosen slot forces the first slot settled.  Consumer: `chosenNoSettled`. -/
theorem chosenSettledFirst {lam : Nat → Nat} {c : Nat} (h : CohortChosen R s lam c) :
    ∀ i, i < R → ∀ T, cohortTok R s (cohortPos R lam i) = .settled T →
      cohortTok R s (cohortPos R lam 0) = .settled (cohortTail R 0) := by
  intro i
  induction i with
  | zero =>
    intro hi T hs
    rcases h.pkt 0 hi with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1] at hs; cases hs
    · exact h1
    · rw [h1] at hs; cases hs
  | succ i ih =>
    intro hi T hs
    have h2 : cohortTok R s (cohortPos R lam (i + 1)) = .settled (cohortTail R (i + 1)) := by
      rcases h.pkt (i + 1) hi with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at hs; cases hs
      · exact h1
      · rw [h1] at hs; cases hs
    have h3 := h.top (i + 1) (by omega) hi h2
    rw [Nat.add_sub_cancel] at h3
    exact ih (by omega) _ h3

/-- Below a cell short of the last target cell no chosen slot is settled.  Consumer:
`barTgt`. -/
theorem chosenNoSettled {lam : Nat → Nat} {c : Nat} (h : CohortChosen R s lam c)
    (hc : c < 2 * R) : ∀ i, i < R → ∀ T, cohortTok R s (cohortPos R lam i) ≠ .settled T := by
  intro i hi T hs
  have hR := h.two
  have h0 := chosenSettledFirst h i hi T hs
  rcases h.pkt 0 (by omega) with h1 | ⟨-, hl⟩ | ⟨h1, -⟩
  · rw [h1] at h0; cases h0
  · have := h.low 0 (by omega)
    unfold cohortPos at this
    omega
  · rw [h1] at h0; cases h0

/-- **The target behind a target barrier** holds only empty cells and pending packets (no live
carry, no settled operand, no tombstone).  Consumer: `barInvStep`, `termEntry`. -/
theorem barTgt {c : Nat} (h : BarShape R s c) (hRc : R ≤ c) (hc : c < 2 * R) (q : Nat)
    (h1 : R ≤ q) (h2 : q < c) :
    s.live q = false ∧ (s.inp q = .E ∨ ∃ T, s.inp q = .P T) := by
  obtain ⟨lam, hch, -⟩ := h.2 hRc
  have hpre := chosenTailLt hch hc
  have hR := hch.two
  have htk : cohortTok R s q = .empty ∨ ∃ T, cohortTok R s q = .pkt T := by
    by_cases hex : ∃ i, i < R ∧ cohortPos R lam i = q
    · obtain ⟨i, hi, hpi⟩ := hex
      rcases hch.pkt i hi with h3 | ⟨h3, -⟩ | ⟨-, hl⟩
      · rw [hpi] at h3
        exact Or.inr ⟨_, h3⟩
      · exact absurd h3 (chosenNoSettled hch hc i hi _)
      · unfold cohortPos at hpi
        omega
    · left
      exact hch.gap q h2 (by omega) (fun i hi he => hex ⟨i, hi, he⟩)
  rw [cohortTokTgt s h1] at htk
  rcases htk with h3 | ⟨T, h3⟩
  · obtain ⟨hE, hl⟩ := tokInEmpty h3
    exact ⟨hl, Or.inl hE⟩
  · obtain ⟨hP, hl⟩ := tokInPkt h3
    exact ⟨hl, Or.inr ⟨T, hP⟩⟩

end Shapes

/-! ### Raw fields of one edge -/

section Edge

/-- Cells off the drawn edge keep all their fields.  Consumer: `barAtBack`. -/
theorem edgeFrameRaw (R k q : Nat) (s : CohortLane) (hq : q ≠ k) (hq' : q ≠ k + 1) :
    (cohortEdge R s k).out q = s.out q ∧ (cohortEdge R s k).inp q = s.inp q ∧
      (cohortEdge R s k).live q = s.live q := by
  unfold cohortEdge
  repeat' split
  all_goals simp [cohortUpd, hq, hq']

theorem edgePipeRaw (R k : Nat) (s : CohortLane) (hk : k + 1 < R) :
    (cohortEdge R s k).out k =
        (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).1 ∧
      (cohortEdge R s k).out (k + 1) =
        (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
  refine ⟨?_, ?_⟩ <;> simp [cohortEdge, hk, cohortUpd]

theorem edgeDelRaw (R k : Nat) (s : CohortLane) (hk : k + 1 = R) :
    (cohortEdge R s k).out k = (bankRepairDigitDelStep (s.out k) (s.inp R) (s.live R)).1 ∧
      (cohortEdge R s k).inp R = (bankRepairDigitDelStep (s.out k) (s.inp R) (s.live R)).2.1 ∧
      (cohortEdge R s k).live R = (bankRepairDigitDelStep (s.out k) (s.inp R) (s.live R)).2.2 := by
  have c1 : ¬ k + 1 < R := by omega
  subst hk
  refine ⟨?_, ?_, ?_⟩ <;> simp [cohortEdge, c1, cohortUpd]

theorem edgeFinRaw (R k : Nat) (s : CohortLane) (h1 : R ≤ k) (h2 : k + 1 < 2 * R) :
    (cohortEdge R s k).inp k = (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k)
        (s.inp (k + 1)) (s.live (k + 1))).1 ∧
      (cohortEdge R s k).live k = (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k)
        (s.inp (k + 1)) (s.live (k + 1))).2.1 ∧
      (cohortEdge R s k).inp (k + 1) = (bankRepairDigitFinStep (decide (k = R)) (s.inp k)
        (s.live k) (s.inp (k + 1)) (s.live (k + 1))).2.2.1 ∧
      (cohortEdge R s k).live (k + 1) = (bankRepairDigitFinStep (decide (k = R)) (s.inp k)
        (s.live k) (s.inp (k + 1)) (s.live (k + 1))).2.2.2 := by
  have c1 : ¬ k + 1 < R := by omega
  have c2 : ¬ k + 1 = R := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cohortEdge, c1, c2, h2, cohortUpd]

theorem edgeTermRaw (R k : Nat) (s : CohortLane) (hk : k + 1 = 2 * R) (hR : 1 ≤ R) :
    (cohortEdge R s k).inp k = (cohortTermStep (s.inp k) (s.live k)).1 ∧
      (cohortEdge R s k).live k = (cohortTermStep (s.inp k) (s.live k)).2 := by
  have c1 : ¬ k + 1 < R := by omega
  have c2 : ¬ k + 1 = R := by omega
  have c3 : ¬ k + 1 < 2 * R := by omega
  unfold cohortEdge
  rw [if_neg c1, if_neg c2, if_neg c3, if_pos hk]
  refine ⟨?_, ?_⟩ <;> simp [cohortUpd]

end Edge

/-! ### Backward rows: where a barrier location came from -/

section Rows

variable {c : Compiled} {n : Nat}

/-- Consumer: `barAtBack`. -/
theorem pipeXBack (stamp : DigitStamp n) (bx : Bool) (ox oy : BankRepairDigitOutSh)
    (gxo gyo : DigitOutGhost n) (a : DigitAtom n)
    (hs : (bankRepairDigitPipeStep bx ox oy).1 = .D true)
    (ha : (ghostPipe stamp bx ox oy gxo gyo).1.atom = some a) :
    (ox = .D true ∧ gxo.atom = some a) ∨ a = .sampled stamp := by
  rcases ox with _ | _ | T <;> rcases oy with _ | _ | T' <;> cases bx <;> (try cases T) <;>
    simp_all [bankRepairDigitPipeStep, ghostPipe, DigitOutGhost.atom]

/-- Consumer: `barAtBack`. -/
theorem pipeYBack (stamp : DigitStamp n) (bx : Bool) (ox oy : BankRepairDigitOutSh)
    (gxo gyo : DigitOutGhost n) (a : DigitAtom n)
    (hs : (bankRepairDigitPipeStep bx ox oy).2 = .D true)
    (ha : (ghostPipe stamp bx ox oy gxo gyo).2.atom = some a) :
    (oy = .D true ∧ gyo.atom = some a) ∨
      (ox = .D true ∧ oy = .E ∧ gxo.atom = some a ∧
        (bankRepairDigitPipeStep bx ox oy).1 = .U) := by
  rcases ox with _ | _ | T <;> rcases oy with _ | _ | T' <;> cases bx <;> (try cases T) <;>
    simp_all [bankRepairDigitPipeStep, ghostPipe, DigitOutGhost.atom]

/-- Consumer: `barAtBack`. -/
theorem delXBack (stamp : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n)) (a : DigitAtom n)
    (hs : (bankRepairDigitDelStep ox iy ky).1 = .D true)
    (ha : (ghostDel stamp ox iy ky gxo gyi).1.atom = some a) :
    ox = .D true ∧ gxo.atom = some a := by
  rcases ox with _ | _ | T <;> rcases iy with _ | _ | T' | T' <;> cases ky <;> (try cases T) <;>
    simp_all [bankRepairDigitDelStep, ghostDel, DigitOutGhost.atom]

/-- Consumer: `barAtBack`. -/
theorem delYBack (stamp : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n)) (a : DigitAtom n)
    (hs : (bankRepairDigitDelStep ox iy ky).2.1 = .P true ∨
      (bankRepairDigitDelStep ox iy ky).2.1 = .S true)
    (ha : (ghostDel stamp ox iy ky gxo gyi).2 = some a) :
    ((bankRepairDigitDelStep ox iy ky).2.1 = iy ∧ (bankRepairDigitDelStep ox iy ky).2.2 = ky ∧
        gyi = some a) ∨
      (ox = .D true ∧ iy = .E ∧ ky = false ∧ gxo.atom = some a ∧
        (bankRepairDigitDelStep ox iy ky).1 = .U ∧
        (bankRepairDigitDelStep ox iy ky).2.1 = .P true ∧
        (bankRepairDigitDelStep ox iy ky).2.2 = false) := by
  rcases ox with _ | _ | T <;> rcases iy with _ | _ | T' | T' <;> cases ky <;> (try cases T) <;>
    (try cases T') <;> simp_all [bankRepairDigitDelStep, ghostDel, DigitOutGhost.atom]

/-- Consumer: `barAtBack`. -/
theorem finXBack (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi : Option (DigitAtom n)) (a : DigitAtom n)
    (hs : ((bankRepairDigitFinStep bx ix kx iy ky).1 = .P true ∧
        (bankRepairDigitFinStep bx ix kx iy ky).2.1 = false) ∨
      (bankRepairDigitFinStep bx ix kx iy ky).1 = .S true)
    (ha : finInX bx ix kx iy ky gxi = some a) :
    ix = .P true ∧ kx = false ∧ gxi = some a := by
  rcases ix with _ | _ | T | T <;> rcases iy with _ | _ | T' | T' <;> cases kx <;> cases ky <;>
    cases bx <;> (try cases T) <;> (try cases T') <;>
    simp_all [bankRepairDigitFinStep, finInX, finXP]

/-- A live left cell after a Fin edge is a launch.  Consumer: `barAtBack`. -/
theorem finXLiveBack (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky : Bool)
    (hl : (bankRepairDigitFinStep bx ix kx iy ky).2.1 = true) :
    bx = true ∧ kx = false ∧ ∃ T, ix = .S T := by
  rcases ix with _ | _ | T | T <;> rcases iy with _ | _ | T' | T' <;> cases kx <;> cases ky <;>
    cases bx <;> (try cases T) <;> simp_all [bankRepairDigitFinStep]

/-- A live left carry always leaves its cell empty.  Consumer: `barAtBack`. -/
theorem finXKx (bx : Bool) (ix : BankRepairDigitInSh) (iy : BankRepairDigitInSh) (ky : Bool) :
    (bankRepairDigitFinStep bx ix true iy ky).1 = .E ∧
      (bankRepairDigitFinStep bx ix true iy ky).2.1 = false := by
  rcases iy with _ | _ | T' | T' <;> cases ky <;> simp [bankRepairDigitFinStep]

/-- Consumer: `barAtBack`. -/
theorem finYBack (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi gyi : Option (DigitAtom n)) (a : DigitAtom n)
    (hs : (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = .P true)
    (hl : (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = false)
    (ha : finInY ix kx iy ky gxi gyi = some a) :
    (iy = .P true ∧ ky = false ∧ gyi = some a) ∨
      (ix = .P true ∧ kx = false ∧ iy = .E ∧ ky = false ∧ gxi = some a ∧
        (bankRepairDigitFinStep bx ix kx iy ky).1 = .E ∧
        (bankRepairDigitFinStep bx ix kx iy ky).2.1 = false) := by
  rcases ix with _ | _ | T | T <;> rcases iy with _ | _ | T' | T' <;> cases kx <;> cases ky <;>
    cases bx <;> (try cases T) <;> (try cases T') <;>
    simp_all [bankRepairDigitFinStep, finInY, finInYFree, finYX, finYP, shS]

/-- A live right cell after a Fin edge was live, or receives the left carry.  Consumer:
`barAtBack`. -/
theorem finYLiveBack (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky : Bool)
    (hl : (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = true) :
    ky = true ∨ kx = true := by
  rcases ix with _ | _ | T | T <;> rcases iy with _ | _ | T' | T' <;> cases kx <;> cases ky <;>
    cases bx <;> (try cases T) <;> simp_all [bankRepairDigitFinStep]

/-- The terminal row leaves no pending tail.  Consumer: `barAtBack`. -/
theorem termNoP (ix : BankRepairDigitInSh) (kx : Bool) : (cohortTermStep ix kx).1 ≠ .P true := by
  rcases ix with _ | _ | T | T <;> cases kx <;> (try cases T) <;> simp [cohortTermStep]

end Rows

/-! ### The barrier on the lane cells -/

section Lane

variable {c : Compiled} {n : Nat} {R : Nat}

/-- **The four barrier locations** of the border-tail sample `sigma` at cell `q`: a source
packet `D true`, a pending target input `P true` (no live carry), the settled border operand
`S true` at `R`, or the first use of a clean live carry.  Consumer: `BarInv`, `barAtBack`. -/
def BarAt (R : Nat) (s : CohortLane) (g : Nat → DigitLaneGhost c n) (sigma : DigitStamp n)
    (q : Nat) : Prop :=
  (q < R ∧ s.out q = .D true ∧ (g q).out.atom = some (.sampled sigma)) ∨
  (R ≤ q ∧ q < 2 * R ∧ s.live q = false ∧ s.inp q = .P true ∧
    (g q).input = some (.sampled sigma)) ∨
  (q = R ∧ s.inp R = .S true ∧ (g R).input = some (.sampled sigma)) ∨
  (R ≤ q ∧ q < 2 * R ∧ s.live q = true ∧ ∃ (L : DigitCarryGhost c n) (u : DigitUse c n),
    (g q).carry = some L ∧ L.inherited = none ∧ L.uses.head? = some u ∧
      u.operand = some (.sampled sigma))

/-- A barrier location blocks its cell.  Consumer: `barInvStep`, `termEntry`. -/
theorem barAtBlock (hR : 2 ≤ R) {s : CohortLane} {g : Nat → DigitLaneGhost c n}
    {sigma : DigitStamp n} {q : Nat} (h : BarAt R s g sigma q) : q < 2 * R ∧ BarBlock R s q := by
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, h3, h4, -⟩ | ⟨rfl, h2, -⟩ | ⟨h1, h2, h3, -⟩
  · refine ⟨by omega, ?_, ?_⟩ <;> rw [cohortTokSrc s h1, h2] <;> simp [cohortTokOut]
  · refine ⟨h2, ?_, ?_⟩ <;> rw [cohortTokTgt s h1, h4, h3] <;> simp [cohortTokIn]
  · refine ⟨by omega, ?_, fun T _ => Nat.le_refl _⟩
    rw [cohortTokTgt s (Nat.le_refl _), h2]
    unfold cohortTokIn
    split <;> simp
  · refine ⟨h2, ?_, ?_⟩ <;> rw [cohortTokTgt s h1, h3] <;> simp [cohortTokIn]

/-- The ghost rows of one letter on the lane cells of the pair (`none`: a letter outside the
pair, which keeps every tracked field).  Supplied on the ring by `laneRowsRing`.  Consumer:
`barAtBack`, `barInvStep`, `termEntry`, `cleanNeStep`. -/
def LaneRows (R : Nat) (stamp : DigitStamp n) (s : CohortLane)
    (g g' : Nat → DigitLaneGhost c n) : Option Nat → Prop
  | none =>
    (∀ q, q < R → (g' q).out = (g q).out) ∧
    (∀ q, R ≤ q → q < 2 * R → (g' q).input = (g q).input ∧ (g' q).carry = (g q).carry)
  | some k =>
    (∀ q, q < R → q ≠ k → q ≠ k + 1 → (g' q).out = (g q).out) ∧
    (∀ q, R ≤ q → q < 2 * R → q ≠ k → q ≠ k + 1 →
      (g' q).input = (g q).input ∧ (g' q).carry = (g q).carry) ∧
    (k + 1 < R → ((g' k).out, (g' (k + 1)).out) =
      ghostPipe stamp (decide (k = 0)) (s.out k) (s.out (k + 1)) (g k).out (g (k + 1)).out) ∧
    (k + 1 = R → ((g' k).out, (g' R).input) =
        ghostDel stamp (s.out k) (s.inp R) (s.live R) (g k).out (g R).input ∧
      (g' R).carry = (g R).carry) ∧
    (R ≤ k → k + 1 < 2 * R →
      ((g' k).input, (g' (k + 1)).input) = ghostFinIn (decide (k = R)) (s.inp k) (s.live k)
        (s.inp (k + 1)) (s.live (k + 1)) (g k).input (g (k + 1)).input ∧
      ((g' k).carry = none ∨ (g' k).carry = (g k).carry ∨
        (k = R ∧ ∃ u : DigitUse c n, u.operand = (g k).input ∧
          (g' k).carry = some (DigitCarryGhost.mk none [u]))) ∧
      ((g' (k + 1)).carry = (g (k + 1)).carry ∨
        ∃ (L : DigitCarryGhost c n) (u : DigitUse c n), (g k).carry = some L ∧
          (g' (k + 1)).carry = some (DigitCarryGhost.mk L.inherited (L.uses ++ [u])))) ∧
    (k + 1 = 2 * R → (g' k).input = ghostTermIn (s.inp k) (s.live k) (g k).input ∧
      ((g' k).carry = none ∨ (g' k).carry = (g k).carry))

/-- Clean target ledgers are nonempty.  Consumer: `barAtBack` (a clean ledger appended keeps its
first use). -/
def CleanNe (R : Nat) (g : Nat → DigitLaneGhost c n) : Prop :=
  ∀ q, R ≤ q → q < 2 * R → ∀ L : DigitCarryGhost c n, (g q).carry = some L →
    L.inherited = none → L.uses ≠ []

/-- **Clean ledgers stay nonempty** under every letter.  Consumer: the run invariant. -/
theorem cleanNeStep {stamp : DigitStamp n} {s : CohortLane} {g g' : Nat → DigitLaneGhost c n}
    (ke : Option Nat) (hrows : LaneRows R stamp s g g' ke) (h : CleanNe R g) : CleanNe R g' := by
  intro q h1 h2 L hL hi
  cases ke with
  | none =>
    rw [(hrows.2 q h1 h2).2] at hL
    exact h q h1 h2 L hL hi
  | some k =>
    obtain ⟨-, hfr, -, hdel, hfin, hterm⟩ := hrows
    by_cases hq1 : q = k
    · subst hq1
      by_cases hk : q + 1 < 2 * R
      · rcases (hfin h1 hk).2.1 with h3 | h3 | ⟨-, u, -, h3⟩
        · rw [h3] at hL; cases hL
        · rw [h3] at hL; exact h q h1 h2 L hL hi
        · rw [h3] at hL; cases hL; simp
      · rcases (hterm (by omega)).2 with h3 | h3
        · rw [h3] at hL; cases hL
        · rw [h3] at hL; exact h q h1 h2 L hL hi
    · by_cases hq2 : q = k + 1
      · by_cases hqR : q = R
        · subst hqR
          rw [(hdel (by omega)).2] at hL
          exact h _ h1 h2 L hL hi
        · rcases (hfin (by omega) (by omega)).2.2 with h3 | ⟨L0, u, -, h3⟩
          · rw [← hq2] at h3
            rw [h3] at hL
            exact h q h1 h2 L hL hi
          · rw [← hq2] at h3
            rw [h3] at hL
            cases hL
            simp
      · rw [(hfr q h1 h2 hq1 hq2).2] at hL
        exact h q h1 h2 L hL hi

/-- **Where a barrier location came from** across one letter: the border read creates it, it
stays in place, or it hops one cell along the drawn edge, leaving an unread source cell or an
empty target cell behind.  Consumer: `barInvStep`. -/
theorem barAtBack (hR : 2 ≤ R) {stamp sigma : DigitStamp n} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} {Ok : Bool → DigitAtom n → Prop} (ke : Option Nat)
    (hrows : LaneRows R stamp s g g' ke) (hcorr : PureCorr R Ok s g)
    (hne : CleanNe R g) (hT : ∀ T, Ok T (.sampled sigma) → T = true) (q : Nat)
    (h : BarAt R (cohortLaneStep R s ke) g' sigma q) :
    (sigma = stamp ∧ ke = some q) ∨ BarAt R s g sigma q ∨
    (0 < q ∧ ke = some (q - 1) ∧ q < 2 * R ∧ BarAt R s g sigma (q - 1) ∧
      (q - 1 < R → cohortTok R (cohortLaneStep R s ke) (q - 1) = .other) ∧
      (R ≤ q - 1 → cohortTok R (cohortLaneStep R s ke) (q - 1) = .empty)) := by
  cases ke with
  | none =>
    right; left
    obtain ⟨ho, hi⟩ := hrows
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3⟩ |
        ⟨h1, h2, h3, L, u, h4, h5, h6, h7⟩
    · exact Or.inl ⟨h1, h2, by rw [← ho q h1]; exact h3⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h3, h4, by rw [← (hi q h1 h2).1]; exact h5⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, by
        rw [← (hi R (Nat.le_refl _) (by omega)).1]; exact h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, L, u, by rw [← (hi q h1 h2).2]; exact h4,
        h5, h6, h7⟩))
  | some k =>
    have hs' : cohortLaneStep R s (some k) = cohortEdge R s k := rfl
    rw [hs'] at h ⊢
    obtain ⟨hfo, hfr, hpipe, hdel, hfin, hterm⟩ := hrows
    by_cases hq1 : q = k
    · -- the drawn edge leaves cell `q`
      subst hq1
      by_cases hp : q + 1 < R
      · obtain ⟨e1, -⟩ := edgePipeRaw R q s hp
        have hg := congrArg Prod.fst (hpipe hp)
        simp only at hg
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [e1] at h2
          rw [hg] at h3
          rcases pipeXBack stamp _ _ _ _ _ _ h2 h3 with ⟨h4, h5⟩ | h4
          · exact Or.inr (Or.inl (Or.inl ⟨h1, h4, h5⟩))
          · left
            simp only [DigitAtom.sampled.injEq] at h4
            exact ⟨h4, rfl⟩
        · omega
        · omega
        · omega
      · by_cases hd : q + 1 = R
        · obtain ⟨e1, -, -⟩ := edgeDelRaw R q s hd
          have hg := congrArg Prod.fst (hdel hd).1
          simp only at hg
          rcases h with ⟨h1, h2, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
          · rw [e1] at h2
            rw [hg] at h3
            obtain ⟨h4, h5⟩ := delXBack stamp _ _ _ _ _ _ h2 h3
            exact Or.inr (Or.inl (Or.inl ⟨h1, h4, h5⟩))
          · omega
          · omega
          · omega
        · by_cases hf : q + 1 < 2 * R
          · have hRq : R ≤ q := by omega
            obtain ⟨e1, e2, -, -⟩ := edgeFinRaw R q s hRq hf
            obtain ⟨hgi, hgx, -⟩ := hfin hRq hf
            have hgi1 := congrArg Prod.fst hgi
            simp only [ghostFinIn] at hgi1
            rcases h with ⟨h1, -⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3⟩ |
                ⟨h1, h2, h3, L, u, h4, h5, h6, h7⟩
            · omega
            · rw [e1] at h4
              rw [e2] at h3
              rw [hgi1] at h5
              obtain ⟨h6, h7, h8⟩ := finXBack _ _ _ _ _ _ _ (Or.inl ⟨h4, h3⟩) h5
              exact Or.inr (Or.inl (Or.inr (Or.inl ⟨h1, h2, h7, h6, h8⟩)))
            · subst h1
              rw [e1] at h2
              rw [hgi1] at h3
              obtain ⟨h6, h7, h8⟩ := finXBack _ _ _ _ _ _ _ (Or.inr h2) h3
              exact Or.inr (Or.inl (Or.inr (Or.inl ⟨Nat.le_refl _, by omega, h7, h6, h8⟩)))
            · rw [e2] at h3
              obtain ⟨hb, hk, T, hS⟩ := finXLiveBack _ _ _ _ _ h3
              have hqR : q = R := of_decide_eq_true hb
              rcases hgx with h8 | h8 | ⟨-, u', hu', h8⟩
              · rw [h8] at h4; cases h4
              · have hl := (hcorr.2 q hRq h2).2
                rw [hk, ← h8, h4] at hl
                simp at hl
              · rw [h8] at h4
                cases h4
                simp at h6
                rw [← h6] at h7
                rw [h7] at hu'
                have hin := (hcorr.2 q hRq h2).1
                rw [hS, ← hu'] at hin
                have hT' := hT T hin
                rw [hT'] at hS
                subst hqR
                exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, hS, hu'.symm⟩))))
          · have ht : q + 1 = 2 * R := by
              rcases h with ⟨h1, -⟩ | ⟨-, h2, -⟩ | ⟨h1, -⟩ | ⟨-, h2, -⟩ <;> omega
            obtain ⟨e1, e2⟩ := edgeTermRaw R q s ht (by omega)
            rcases h with ⟨h1, -⟩ | ⟨-, -, -, h4, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3, -⟩
            · omega
            · rw [e1] at h4
              exact absurd h4 (termNoP _ _)
            · omega
            · rw [e2, termLiveE] at h3
              cases h3
    · by_cases hq2 : q = k + 1
      · -- the drawn edge enters cell `q`
        subst hq2
        simp only [Nat.add_sub_cancel]
        by_cases hp : k + 1 < R
        · obtain ⟨e1, e2⟩ := edgePipeRaw R k s hp
          have hg := congrArg Prod.snd (hpipe hp)
          simp only at hg
          rcases h with ⟨h1, h2, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
          · rw [e2] at h2
            rw [hg] at h3
            rcases pipeYBack stamp _ _ _ _ _ _ h2 h3 with ⟨h4, h5⟩ | ⟨h4, -, h5, h6⟩
            · exact Or.inr (Or.inl (Or.inl ⟨h1, h4, h5⟩))
            · right; right
              refine ⟨by omega, by simp, by omega, Or.inl ⟨by omega, h4, h5⟩, fun _ => ?_,
                fun h' => by omega⟩
              rw [cohortTokSrc _ (by omega), e1, h6]
              rfl
          · omega
          · omega
          · omega
        · by_cases hd : k + 1 = R
          · subst hd
            obtain ⟨e1, e2, e3⟩ := edgeDelRaw (k + 1) k s rfl
            obtain ⟨hg, hgc⟩ := hdel rfl
            have hg2 := congrArg Prod.snd hg
            simp only at hg2
            rcases h with ⟨h1, -⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨-, h2, h3⟩ |
                ⟨h1, h2, h3, L, u, h4, h5, h6, h7⟩
            · omega
            · rw [e2] at h4
              rw [e3] at h3
              rw [hg2] at h5
              rcases delYBack stamp _ _ _ _ _ _ (Or.inl h4) h5 with ⟨h6, h7, h8⟩ |
                  ⟨h6, -, -, h8, h9, -, -⟩
              · right; left; right; left
                exact ⟨Nat.le_refl _, by omega, by rw [← h7]; exact h3,
                  by rw [← h6]; exact h4, h8⟩
              · right; right
                refine ⟨by omega, by simp, by omega, Or.inl ⟨by omega, h6, h8⟩, fun _ => ?_,
                  fun h' => by omega⟩
                rw [cohortTokSrc _ (by omega), e1, h9]
                rfl
            · rw [e2] at h2
              rw [hg2] at h3
              rcases delYBack stamp _ _ _ _ _ _ (Or.inr h2) h3 with ⟨h6, -, h8⟩ |
                  ⟨-, -, -, -, -, h9, -⟩
              · right; left; right; right; left
                exact ⟨rfl, by rw [← h6]; exact h2, h8⟩
              · rw [h9] at h2; cases h2
            · rw [hgc] at h4
              have hl := (hcorr.2 (k + 1) (Nat.le_refl _) (by omega)).2
              simp [h4] at hl
              right; left; right; right; right
              exact ⟨Nat.le_refl _, by omega, hl, L, u, h4, h5, h6, h7⟩
          · by_cases hf : k + 1 < 2 * R
            · have hRk : R ≤ k := by omega
              obtain ⟨e1, e2, e3, e4⟩ := edgeFinRaw R k s hRk hf
              obtain ⟨hgi, -, hgy⟩ := hfin hRk hf
              have hgi2 := congrArg Prod.snd hgi
              simp only [ghostFinIn] at hgi2
              rcases h with ⟨h1, -⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, -⟩ |
                  ⟨h1, h2, h3, L, u, h4, h5, h6, h7⟩
              · omega
              · rw [e3] at h4
                rw [e4] at h3
                rw [hgi2] at h5
                rcases finYBack _ _ _ _ _ _ _ _ h4 h3 h5 with ⟨h6, h7, h8⟩ |
                    ⟨h6, h7, -, -, h8, h9, h10⟩
                · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨h1, h2, h7, h6, h8⟩)))
                · right; right
                  refine ⟨by omega, by simp, h2, Or.inr (Or.inl ⟨hRk, by omega, h7, h6, h8⟩),
                    fun h' => by omega, fun _ => ?_⟩
                  rw [cohortTokTgt _ hRk, e1, e2, h9, h10]
                  rfl
              · omega
              · rcases hgy with h8 | ⟨L0, u0, h8, h9⟩
                · rw [h8] at h4
                  have hl := (hcorr.2 (k + 1) h1 h2).2
                  simp [h4] at hl
                  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr
                    ⟨h1, h2, hl, L, u, h4, h5, h6, h7⟩))))
                · rw [h9] at h4
                  cases h4
                  have hl0 := (hcorr.2 k hRk (by omega)).2
                  simp [h8] at hl0
                  have hne0 := hne k hRk (by omega) L0 h8 h5
                  obtain ⟨u1, t, ht⟩ : ∃ u1 t, L0.uses = u1 :: t := by
                    cases hu : L0.uses with
                    | nil => exact absurd hu hne0
                    | cons u1 t => exact ⟨u1, t, rfl⟩
                  simp [ht] at h6
                  rw [← h6] at h7
                  right; right
                  refine ⟨by omega, by simp, h2, Or.inr (Or.inr (Or.inr
                    ⟨hRk, by omega, hl0, L0, u1, h8, h5, by rw [ht]; rfl, h7⟩)),
                    fun h' => by omega, fun _ => ?_⟩
                  have hx := finXKx (decide (k = R)) (s.inp k) (s.inp (k + 1))
                    (s.live (k + 1))
                  rw [cohortTokTgt _ hRk, e1, e2, hl0, hx.1, hx.2]
                  rfl
            · rcases h with ⟨h1, -⟩ | ⟨-, h2, -⟩ | ⟨h1, -⟩ | ⟨-, h2, -⟩ <;> omega
      · -- the drawn edge misses cell `q`
        right; left
        obtain ⟨f1, f2, f3⟩ := edgeFrameRaw R k q s hq1 hq2
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3⟩ |
            ⟨h1, h2, h3, L, u, h4, h5, h6, h7⟩
        · rw [f1] at h2
          rw [hfo q h1 hq1 hq2] at h3
          exact Or.inl ⟨h1, h2, h3⟩
        · rw [f2] at h4
          rw [f3] at h3
          rw [(hfr q h1 h2 hq1 hq2).1] at h5
          exact Or.inr (Or.inl ⟨h1, h2, h3, h4, h5⟩)
        · rw [h1] at f2 hq1 hq2
          rw [f2] at h2
          rw [(hfr R (Nat.le_refl _) (by omega) hq1 hq2).1] at h3
          exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
        · rw [f3] at h3
          rw [(hfr q h1 h2 hq1 hq2).2] at h4
          exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, L, u, h4, h5, h6, h7⟩))

/-- A source cell whose token is unread, or any empty cell, tracks no atom.  Consumer:
`barInvStep`, `termEntry`. -/
theorem trackedNone {s : CohortLane} {g : Nat → DigitLaneGhost c n}
    {Ok : Bool → DigitAtom n → Prop} (hcorr : PureCorr R Ok s g) (q : Nat) (hq : q < 2 * R)
    (h : (q < R ∧ cohortTok R s q = .other) ∨ cohortTok R s q = .empty) :
    trackedAt R g q = none := by
  unfold trackedAt
  by_cases hqR : q < R
  · rw [if_pos hqR]
    have hc := hcorr.1 q hqR
    rw [cohortTokSrc s hqR] at h
    revert hc h
    cases s.out q with
    | E =>
      intro _ hc
      have hc' : (g q).out = .empty := hc
      simp [hc', DigitOutGhost.atom]
    | U =>
      intro _ hc
      have hc' : (g q).out.obligation.isSome = true := hc
      revert hc'
      cases (g q).out with
      | empty => intro hc; simp [DigitOutGhost.obligation] at hc
      | unread a => intro _; rfl
      | packet a => intro hc; simp [DigitOutGhost.obligation] at hc
    | D T => intro h _; rcases h with ⟨-, h⟩ | h <;> simp [cohortTokOut] at h
  · rw [if_neg hqR, if_pos hq]
    rw [cohortTokTgt s (by omega)] at h
    rcases h with ⟨h, -⟩ | h
    · exact absurd h hqR
    · obtain ⟨hE, -⟩ := tokInEmpty h
      have hc := (hcorr.2 q (by omega) hq).1
      rw [hE] at hc
      exact hc

/-- **The barrier invariant** of `sigma` on the lane cells: at every barrier location `q`, the
shape behind it (`BarShape`), the clock bound of `sigma`, and every tracked atom behind it is a
sample stamped after `sigma`.  Consumer: `barInvStep`, `termEntry`. -/
def BarInv (R : Nat) (s : CohortLane) (g : Nat → DigitLaneGhost c n) (sigma : DigitStamp n)
    (clock : Nat) : Prop :=
  ∀ q, BarAt R s g sigma q → BarShape R s q ∧ sigma.time ≤ clock ∧
    ∀ p (x : DigitAtom n), p < q → trackedAt R g p = some x → AgedAtom sigma.time x

/-- **Every letter keeps the barrier invariant.**  `hback`: a tracked atom after the letter was
tracked at the same cell or one cell to the left, or is the letter's fresh sample (supplied on
the ring by `trackedStep`).  Consumer: the run invariant. -/
theorem barInvStep (hR : 2 ≤ R) {stamp sigma : DigitStamp n} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} {Ok Ok' : Bool → DigitAtom n → Prop} {clock : Nat}
    (ke : Option Nat) (hrows : LaneRows R stamp s g g' ke) (hcorr : PureCorr R Ok s g)
    (hcorr' : PureCorr R Ok' (cohortLaneStep R s ke) g') (hne : CleanNe R g)
    (hT : ∀ T, Ok T (.sampled sigma) → T = true) (hst : stamp.time = clock + 1)
    (hsig : sigma = stamp → ke = some 0)
    (hback : ∀ p (x : DigitAtom n), trackedAt R g' p = some x →
      trackedAt R g p = some x ∨ (0 < p ∧ trackedAt R g (p - 1) = some x) ∨
        x = .sampled stamp)
    (h : BarInv R s g sigma clock) : BarInv R (cohortLaneStep R s ke) g' sigma (clock + 1) := by
  intro q hq
  have hfresh : ∀ x : DigitAtom n, x = .sampled stamp → sigma.time ≤ clock →
      AgedAtom sigma.time x := fun x hx ht => ⟨stamp, hx, by omega⟩
  rcases barAtBack hR ke hrows hcorr hne hT q hq with ⟨hss, hke⟩ | hpre |
      ⟨hq0, hke, hq2, hpre, hsrc, htgt⟩
  · -- created by the border read
    have hq0 : q = 0 := by
      have := hsig hss
      rw [hke] at this
      exact Option.some.inj this
    subst hq0
    refine ⟨⟨fun _ p hp => absurd hp (Nat.not_lt_zero _), fun h0 => absurd h0 (by omega)⟩,
      by rw [hss]; omega, fun p x hp => absurd hp (Nat.not_lt_zero _)⟩
  · -- in place
    obtain ⟨hsh, htime, hage⟩ := h q hpre
    obtain ⟨hq2, hb⟩ := barAtBlock hR hpre
    refine ⟨barShapeLane hR hsh hq2 hb ke, by omega, fun p x hp hx => ?_⟩
    rcases hback p x hx with h1 | ⟨-, h1⟩ | h1
    · exact hage p x hp h1
    · exact hage (p - 1) x (by omega) h1
    · exact hfresh x h1 htime
  · -- a hop from `q - 1`
    obtain ⟨hsh, htime, hage⟩ := h (q - 1) hpre
    obtain ⟨-, hb⟩ := barAtBlock hR hpre
    rw [hke] at hsrc htgt ⊢
    have hstep : cohortLaneStep R s (some (q - 1)) = cohortEdge R s (q - 1) := rfl
    rw [hstep] at hsrc htgt
    have hq1 : q - 1 + 1 = q := by omega
    refine ⟨?_, by omega, fun p x hp hx => ?_⟩
    · rw [hstep]
      by_cases hk : q - 1 < R
      · have := barShapeMoveSrc hR hsh hk hb.1 (hsrc hk)
        rwa [hq1] at this
      · have := barShapeMoveTgt hR hsh (by omega) (by omega) hb (htgt (by omega))
        rwa [hq1] at this
    · by_cases hpk : p = q - 1
      · subst hpk
        have hn : trackedAt R g' (q - 1) = none := by
          rw [hke] at hcorr'
          rw [hstep] at hcorr'
          refine trackedNone hcorr' (q - 1) (by omega) ?_
          by_cases hk : q - 1 < R
          · exact Or.inl ⟨hk, hsrc hk⟩
          · exact Or.inr (htgt (by omega))
        rw [hn] at hx
        cases hx
      · rcases hback p x hx with h1 | ⟨-, h1⟩ | h1
        · exact hage p x (by omega) h1
        · exact hage (p - 1) x (by omega) h1
        · exact hfresh x h1 htime

/-- **The entry at a terminal letter**: a barrier location at the last target cell (a live last
carry whose clean ledger starts with `sigma`, or a pending tail) and the terminal edge.  After
the letter the lane is in the cycle class with the old cohort gone, no target cell is live, no
target ledger is held, and every tracked atom is a sample stamped after `sigma`.  Consumer:
the ring form `termEntryRing`. -/
theorem termEntry (hR : 2 ≤ R) {stamp sigma : DigitStamp n} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} {Ok Ok' : Bool → DigitAtom n → Prop} {clock : Nat}
    (hrows : LaneRows R stamp s g g' (some (2 * R - 1))) (hcorr : PureCorr R Ok s g)
    (hcorr' : PureCorr R Ok' (cohortEdge R s (2 * R - 1)) g') (hst : stamp.time = clock + 1)
    (hback : ∀ p (x : DigitAtom n), trackedAt R g' p = some x →
      trackedAt R g p = some x ∨ (0 < p ∧ trackedAt R g (p - 1) = some x) ∨
        x = .sampled stamp)
    (h : BarInv R s g sigma clock) (hat : BarAt R s g sigma (2 * R - 1)) :
    (∃ (lam : Nat → Nat), CohortCycIn R 0 (cohortEdge R s (2 * R - 1)) (lam, 0) (2 * R + 1)) ∧
    LiveE R (cohortEdge R s (2 * R - 1)) ∧
    (∀ p (x : DigitAtom n), trackedAt R g' p = some x → AgedAtom sigma.time x) ∧
    (∀ q, R ≤ q → q < 2 * R → (g' q).carry = none) := by
  obtain ⟨hsh, htime, hage⟩ := h _ hat
  obtain ⟨-, hb⟩ := barAtBlock hR hat
  obtain ⟨lam, hch, hY⟩ := hsh.2 (by omega)
  have hpre := chosenTailLt hch (by omega)
  have hch' := (chosenEdge hch hpre (fun _ => hb) (2 * R - 1)).1
  have hpre' := chosenTailLt hch' (by omega)
  obtain ⟨e1, e2⟩ := edgeTermRaw R (2 * R - 1) s (by omega) (by omega)
  have hlast : (cohortEdge R s (2 * R - 1)).inp (2 * R - 1) = .E ∧
      (cohortEdge R s (2 * R - 1)).live (2 * R - 1) = false := by
    rw [e1, e2]
    rcases hat with ⟨h1, -⟩ | ⟨-, -, h3, h4, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3, -⟩
    · omega
    · rw [h3, h4]; simp [cohortTermStep]
    · omega
    · rw [h3]; simp [cohortTermStep]
  have hempty : cohortTok R (cohortEdge R s (2 * R - 1)) (2 * R - 1) = .empty := by
    rw [cohortTokTgt _ (by omega), hlast.1, hlast.2]
    rfl
  have hfr : ∀ q, q < 2 * R - 1 → (cohortEdge R s (2 * R - 1)).inp q = s.inp q ∧
      (cohortEdge R s (2 * R - 1)).live q = s.live q := fun q hq =>
    ⟨(edgeFrameRaw R (2 * R - 1) q s (by omega) (by omega)).2.1,
      (edgeFrameRaw R (2 * R - 1) q s (by omega) (by omega)).2.2⟩
  have hdead : ∀ q, R ≤ q → q < 2 * R → (cohortEdge R s (2 * R - 1)).live q = false := by
    intro q h1 h2
    by_cases hq : q = 2 * R - 1
    · rw [hq]; exact hlast.2
    · rw [(hfr q (by omega)).2]
      exact (barTgt hsh (by omega) (by omega) q h1 (by omega)).1
  refine ⟨⟨cohortGenGhost R s lam (2 * R - 1), rfl, ⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [cohortOldDone (R := R) (o := 2 * R + 1) (by omega)]
  · rw [cohortBottomCarry (R := R) (o := 2 * R + 1) (by omega),
      show 2 * R + 1 - 1 = 2 * R by omega]
    refine chosenExtend hch' (by omega) (Nat.le_refl _) (fun q h1 h2 => ?_)
    have hq : q = 2 * R - 1 := by omega
    rw [hq]
    exact hempty
  · exact youngerGen hch hpre hY (2 * R - 1)
  · intro hd
    have := hd (R - 1) (by omega)
    simp only at this
    omega
  · intro q h1 h2 hl
    rw [hdead q h1 h2] at hl
    cases hl
  · intro p x hx
    by_cases hp : p < 2 * R - 1
    · rcases hback p x hx with h1 | ⟨-, h1⟩ | h1
      · exact hage p x hp h1
      · exact hage (p - 1) x (by omega) h1
      · exact ⟨stamp, h1, by omega⟩
    · by_cases hp2 : p = 2 * R - 1
      · rw [hp2, trackedNone hcorr' (2 * R - 1) (by omega) (Or.inr hempty)] at hx
        cases hx
      · unfold trackedAt at hx
        rw [if_neg (by omega), if_neg (by omega)] at hx
        cases hx
  · intro q h1 h2
    have hc := (hcorr'.2 q h1 h2).2
    rw [hdead q h1 h2] at hc
    cases hq : (g' q).carry with
    | none => rfl
    | some L => rw [hq] at hc; cases hc

end Lane

/-! ### The rows on the ring -/

section Ring

variable {c : Compiled} {n : Nat}

/-- A live left carry that does not succeed leaves the right ledger alone.  Consumer:
`carryYLiveKeepD`. -/
theorem replayCarryYLiveKeep (lane : DigitLane) (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) (hlx : x.leader = false)
    (hly : y.leader = false) (hxc : x.carryLive = true) (hmy : y.marker = false)
    (hno : y.carryLive = true ∨ y.input.isS = false) :
    (digitLaneReplay lane time source destination x y gx gy).y.carry = gy.carry := by
  rcases hno with h | h <;> simp [digitLaneReplay, hlx, hly, hxc, hmy, h]

/-- Consumer: `laneRowsRing`. -/
theorem carryYLiveKeepD (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
    (gx gy : DigitGhost c n) (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmy : laneMarkerY lane X Y = false) (hkx : bankRepairDigitLaneLive lane X.top = true)
    (hno : bankRepairDigitLaneLive lane Y.top = true ∨
      shS (bankRepairDigitInShOf (bankRepairDigitLaneIn lane Y.top)) = false) :
    (laneGhost lane (digitService t e d X Y gx gy).y).carry = (laneGhost lane gy).carry := by
  rw [serviceLaneY, serviceLane]
  refine replayCarryYLiveKeep lane t e d _ _ (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewLive]; exact hkx) (by rw [laneViewMarker]; exact hmy) ?_
  rcases hno with h | h
  · left
    rw [laneViewLive]
    exact h
  · right
    rw [laneViewIn]
    revert h
    cases bankRepairDigitLaneIn lane Y.top <;> simp [InTok.isS, bankRepairDigitInShOf, shS]

/-- **The ghost rows of one letter on the ring**, in the form `LaneRows` (projected ring,
layout hypotheses of `cohortProjStep`, the correspondence before the letter).  Consumer:
`barInvRing`, `termEntryRing`. -/
theorem laneRowsRing (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n) (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    {Ok : Bool → DigitAtom n → Prop}
    (hcorr : PureCorr R Ok (cohortProj ring root lane src R S)
      (laneCells ring root lane src A.current)) :
    LaneRows R (DigitStamp.mk (A.clock + 1) (digitSite ring root j) lane)
      (cohortProj ring root lane src R S) (laneCells ring root lane src A.current)
      (laneCells ring root lane src (digitAuditStep ring S A (digitSite ring root j)).current)
      (cohortEdgeOf root src R (digitSite ring root j)) := by
  obtain ⟨cfr, cdel, cfin, cterm⟩ := tgtRows ring hn root S R src hR hsrc hend hroot hbR hb2R
    hbF lane A j hj hbX hbY
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    have hke : cohortEdgeOf root src R (digitSite ring root (src + k)) = some k :=
      cohortEdgeOfSite ring root src R hend k (by omega)
    rw [hke] at cfr cdel cfin cterm ⊢
    have hfr : ∀ q, q ≠ k → q ≠ k + 1 → q < 2 * R →
        laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + k))).current q =
        laneCells ring root lane src A.current q := by
      intro q hq1 hq2 hq
      unfold laneCells
      rw [curFar]
      · intro he
        exact hq1 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        exact hq2 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
    have hx : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current k =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).x := by
      unfold laneCells
      rw [curX]
    have hy : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1) =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).y := by
      unfold laneCells
      rw [show digitSite ring root (src + (k + 1)) =
        ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring hn]
    have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
    refine ⟨fun q hq h1 h2 => by rw [hfr q h1 h2 (by omega)], fun q h1 h2 h3 h4 => ?_,
      fun hp => ?_, fun hd => ?_, fun hRk hk2 => ?_, fun ht => ?_⟩
    · rw [cfr q h1 h2 (fun h => h3 (Option.some.inj h).symm)
        (fun h => h4 (by have := Option.some.inj h; omega))]
      exact ⟨rfl, rfl⟩
    · -- Pipe
      have hbx : (S (digitSite ring root (src + k))).word.beta = decide (k = 0) := by
        by_cases hk0 : k = 0
        · rw [decide_eq_true hk0, hk0]
          exact hb0
        · rw [decide_eq_false hk0]
          exact hbF k (by omega) (by omega) (by omega)
      have hmX : laneMarkerX lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = decide (k = 0) := by
        rw [laneMarkerXBeta lane _ _ hbX]
        exact hbx
      have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = false := by
        rw [laneMarkerYBeta lane _ _ hbY]
        exact hbF (k + 1) (by omega) (by omega) (by omega)
      rw [hx, hy, projOut ring root lane src R S k (by omega),
        projOut ring root lane src R S (k + 1) hp, ← hmX]
      exact rowPipeD lane (A.clock + 1) (digitSite ring root (src + k))
        (ring.rightNeighbor (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
        (A.current (digitSite ring root (src + k)))
        (A.current (digitSite ring root (src + k + 1))) hlx hly hmy
    · -- Del
      have hmx : laneMarkerX lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = false := by
        rw [laneMarkerXBeta lane _ _ hbX]
        exact hbF k (by omega) (by omega) (by omega)
      have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = true := by
        rw [laneMarkerYBeta lane _ _ hbY, show src + k + 1 = src + R by omega]
        exact hbR
      have hrow := rowDelD lane (A.clock + 1) (digitSite ring root (src + k))
        (ring.rightNeighbor (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
        (A.current (digitSite ring root (src + k)))
        (A.current (digitSite ring root (src + k + 1))) hlx hly hmx hmy
      refine ⟨?_, (cdel (by rw [show R - 1 = k by omega])).2⟩
      subst hd
      rw [hx, hy, projOut ring root lane src (k + 1) S k (by omega),
        projIn ring root lane src (k + 1) S (k + 1) (Nat.le_refl _) (by omega),
        projLive ring root lane src (k + 1) S (k + 1) (Nat.le_refl _) (by omega)]
      exact hrow.1
    · -- Fin
      obtain ⟨hin', hxc, hyk, hya⟩ := cfin k rfl hRk hk2
      refine ⟨hin', ?_, ?_⟩
      · rcases hxc with h | h | ⟨hkR, -, u, -, hu1, hu2⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨hkR, u, hu1, hu2⟩)
      · by_cases hlk : (cohortProj ring root lane src R S).live k = true
        · have hcl := (hcorr.2 k hRk (by omega)).2
          rw [hlk] at hcl
          obtain ⟨L, hL⟩ : ∃ L, (laneCells ring root lane src A.current k).carry = some L := by
            cases h0 : (laneCells ring root lane src A.current k).carry with
            | none => rw [h0] at hcl; cases hcl
            | some L => exact ⟨L, rfl⟩
          by_cases hs : (cohortProj ring root lane src R S).live (k + 1) = false ∧
              ∃ T, (cohortProj ring root lane src R S).inp (k + 1) = .S T
          · obtain ⟨hky, T, hT⟩ := hs
            obtain ⟨u, -, -, hu⟩ := hya hlk hky T hT L hL
            exact Or.inr ⟨L, u, hL, hu⟩
          · left
            have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
                (S (digitSite ring root (src + k + 1))) = false := by
              rw [laneMarkerYBeta lane _ _ hbY]
              exact hbF (k + 1) (by omega) (by omega) (by omega)
            rw [projLive ring root lane src R S k hRk (by omega)] at hlk
            rw [hy]
            refine carryYLiveKeepD lane (A.clock + 1) (digitSite ring root (src + k))
              (ring.rightNeighbor (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
              (A.current (digitSite ring root (src + k)))
              (A.current (digitSite ring root (src + k + 1))) hlx hly hmy hlk ?_
            rw [projLive ring root lane src R S (k + 1) (by omega) hk2,
              projIn ring root lane src R S (k + 1) (by omega) hk2] at hs
            cases hl1 : bankRepairDigitLaneLive lane (S (digitSite ring root (src + (k + 1)))).top
            · right
              cases hi : bankRepairDigitInShOf (bankRepairDigitLaneIn lane
                  (S (digitSite ring root (src + k + 1))).top) with
              | S T => exact absurd ⟨hl1, T, hi⟩ hs
              | _ => rfl
            · left
              rfl
        · left
          exact hyk (by simpa using hlk)
    · -- Terminal
      obtain rfl : k = 2 * R - 1 := by omega
      obtain ⟨h1, h2, -⟩ := cterm rfl
      exact ⟨h1, h2⟩
  · have hnone : cohortEdgeOf root src R (digitSite ring root j) = none := by
      unfold cohortEdgeOf
      rw [cohortIdxSite ring root j hj, if_neg hin]
    rw [hnone] at cfr ⊢
    have farNe : ∀ q, q < 2 * R → src + q ≠ j → src + q ≠ j + 1 →
        laneCells ring root lane src (digitAuditStep ring S A (digitSite ring root j)).current q =
        laneCells ring root lane src A.current q := by
      intro q hq n1 n2
      unfold laneCells
      rw [curFar]
      · intro he
        exact n1 (bankRepairDigitSiteInj ring root (by omega) hj he)
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        by_cases hjn : j + 1 < n
        · exact n2 (bankRepairDigitSiteInj ring root (by omega) hjn he)
        · rw [show j + 1 = n by omega, bankRepairDigitSiteN] at he
          have := bankRepairDigitSiteInj ring root (k := src + q) (m := 0) (by omega) (by omega) he
          omega
    refine ⟨fun q hq => ?_, fun q h1 h2 => ?_⟩
    · by_cases h1 : j + 1 = src
      · by_cases hq0 : q = 0
        · subst hq0
          have hlx := bankRepairDigitSiteNonroot ring root S hroot j (by omega) (by omega)
          have hly := bankRepairDigitSiteNonroot ring root S hroot (j + 1) (by omega) (by omega)
          have hmy : laneMarkerY lane (S (digitSite ring root j))
              (S (digitSite ring root (j + 1))) = true := by
            rw [laneMarkerYBeta lane _ _ hbY, h1]
            exact hb0
          show (laneGhost lane ((digitAuditStep ring S A (digitSite ring root j)).current
            (digitSite ring root (src + 0)))).out =
            (laneGhost lane (A.current (digitSite ring root (src + 0)))).out
          rw [show digitSite ring root (src + 0) = ring.rightNeighbor (digitSite ring root j) by
            rw [← h1]; rfl, curY ring hn]
          exact rowEntryD lane (A.clock + 1) (digitSite ring root j)
            (ring.rightNeighbor (digitSite ring root j)) (S (digitSite ring root j))
            (S (digitSite ring root (j + 1))) (A.current (digitSite ring root j))
            (A.current (digitSite ring root (j + 1))) hlx hly hmy
        · rw [farNe q (by omega) (by omega) (by omega)]
      · rw [farNe q (by omega) (by omega) (by omega)]
    · rw [cfr q h1 h2 (by simp) (by simp)]
      exact ⟨rfl, rfl⟩

end Ring

/-! ### The run invariant on the ring -/

section Run

variable {c : Compiled} {n : Nat}

/-- **The barrier run invariant** of one pair and lane: clean ledgers are nonempty, every
recorded border sample of the lane is a tail sample, and every border-tail stamp `sigma` of the
lane has the barrier invariant.  Consumer: `barRunStep`, `termEntryRing`. -/
def BarRun (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  CleanNe R (laneCells ring root lane src A.current) ∧
  (∀ smp : DigitSample c n, DigitRecordedSample A smp → smp.id.site = digitSite ring root src →
    smp.id.lane = lane → smp.tail = true) ∧
  ∀ sigma : DigitStamp n, sigma.site = digitSite ring root src → sigma.lane = lane →
    BarInv R (cohortProj ring root lane src R S) (laneCells ring root lane src A.current) sigma
      A.clock

/-- Ledgers of the audit start are inherited.  Consumer: `barRunInitial`. -/
theorem initialCarryInherited (ring : DirectedRing n) (root : Fin n) (lane : DigitLane)
    (src : Nat) (S : Fin n → ProjD c) (q : Nat) (L : DigitCarryGhost c n)
    (hL : (laneCells ring root lane src (digitAuditInitial S).current q).carry = some L) :
    L.inherited ≠ none := by
  have hL' : (laneGhost lane (digitGhostInitial S (digitSite ring root (src + q)))).carry =
      some L := hL
  rw [laneGhostInitial] at hL'
  unfold DigitLaneGhost.initial at hL'
  by_cases hc : (digitLaneView lane (S (digitSite ring root (src + q)))
      (S (digitSite ring root (src + q))).word.beta).carryLive = true
  · rw [if_pos hc] at hL'
    injection hL' with hL'
    subst hL'
    intro hh
    cases hh
  · rw [if_neg hc] at hL'
    cases hL'

/-- **The barrier run invariant at the audit start** (nothing is sampled, every ledger is
inherited).  Consumer: the width run `L3.CloseTerm.barRunWidth`. -/
theorem barRunInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (hR : 2 ≤ R) (S : Fin n → ProjD c) (Base : Bool → DigitAtom n → Prop)
    (hnb : ∀ T (id : DigitStamp n), ¬ Base T (.sampled id))
    (hgc : GhostCorr ring root lane src R Base S (digitAuditInitial S)) :
    BarRun ring root lane src R S (digitAuditInitial S) := by
  have hnr : ∀ smp : DigitSample c n, ¬ DigitRecordedSample (digitAuditInitial S) smp := by
    intro smp h
    obtain ⟨f, hf, -⟩ := h
    exact absurd hf List.not_mem_nil
  have hns : ∀ T (sigma : DigitStamp n),
      ¬ GhostOk ring root lane src R Base (digitAuditInitial S) T (.sampled sigma) := by
    intro T sigma h
    rcases h with h | ⟨smp, -, hrec, -⟩
    · exact hnb T sigma h
    · exact hnr smp hrec
  refine ⟨fun q _ _ L hL hi => absurd hi (initialCarryInherited ring root lane src S q L hL),
    fun smp h => absurd h (hnr smp), fun sigma _ _ q hq => ?_⟩
  exfalso
  rcases hq with ⟨h1, h2, h3⟩ | ⟨h1, h2, -, h4, h5⟩ | ⟨h1, h2, h3⟩ | ⟨-, -, -, L, u, h4, h5, -⟩
  · have hc := hgc.1 q h1
    rw [h2] at hc
    have hc' : optOk (GhostOk ring root lane src R Base (digitAuditInitial S) true)
        (laneCells ring root lane src (digitAuditInitial S).current q).out.atom := hc
    rw [h3] at hc'
    exact hns true sigma hc'
  · have hc := (hgc.2 q h1 h2).1
    rw [h4, h5] at hc
    exact hns true sigma hc
  · have hc := (hgc.2 R (Nat.le_refl _) (by omega)).1
    rw [h2, h3] at hc
    exact hns true sigma hc
  · exact initialCarryInherited ring root lane src S q L h4 h5

/-- A tracked atom after one letter was tracked at the same cell or one cell to the left, or is
the letter's fresh sample.  Consumer: `barRunStep`, `termEntryRing`. -/
theorem trackedBackRing (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n) (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta) :
    ∀ p (x : DigitAtom n), trackedAt R (laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root j)).current) p = some x →
      trackedAt R (laneCells ring root lane src A.current) p = some x ∨
      (0 < p ∧ trackedAt R (laneCells ring root lane src A.current) (p - 1) = some x) ∨
      x = .sampled (DigitStamp.mk (A.clock + 1) (digitSite ring root j) lane) := by
  obtain ⟨k, hfr, hm⟩ := trackedStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF
    lane A j hj hbX hbY
  intro p x hx
  by_cases h1 : p = k
  · rw [h1] at hx ⊢
    rcases (hm x).1 hx with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Option.some.inj h2).symm)
  · by_cases h2 : p = k + 1
    · rw [h2] at hx ⊢
      rcases (hm x).2 hx with h3 | ⟨h3, -⟩
      · exact Or.inl h3
      · exact Or.inr (Or.inl ⟨by omega, by rw [Nat.add_sub_cancel]; exact h3⟩)
    · rw [hfr p h1 h2] at hx
      exact Or.inl hx

/-- **Every letter keeps the barrier run invariant** (projected ring, layout hypotheses of
`cohortProjStep`, the correspondence before and after the letter with a base holding no
sample).  Consumer: the width run `L3.CloseTerm.barRunWidth`. -/
theorem barRunStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (Base : Bool → DigitAtom n → Prop)
    (hnb : ∀ T (id : DigitStamp n), ¬ Base T (.sampled id)) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    (hgc : GhostCorrDistinct ring root lane src R Base S A)
    (hgc' : GhostCorrDistinct ring root lane src R Base (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)))
    (h : BarRun ring root lane src R S A) :
    BarRun ring root lane src R (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)) := by
  obtain ⟨hne, hbt, hinv⟩ := h
  have hrows := laneRowsRing ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane A j
    hj hbX hbY hgc.1
  have hproj := cohortProjStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane j
    hj hbX hbY
  have hcorr' := hgc'.1
  unfold GhostCorr at hcorr'
  rw [hproj] at hcorr'
  have hback := trackedBackRing ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane A
    j hj hbX hbY
  refine ⟨cleanNeStep _ hrows hne, fun smp hs hsi hl => ?_, fun sigma hsi hl => ?_⟩
  · rcases L3.TailChain.newBorderSample ring root S src R hR hsrc hend hroot hb0 lane A j hj hbX smp hs hsi
      hl with h' | ⟨-, -, -, -, ht⟩
    · exact hbt smp h' hsi hl
    · exact ht
  · rw [hproj]
    refine barInvStep hR _ hrows hgc.1 hcorr' hne ?_ rfl ?_ hback (hinv sigma hsi hl)
    · intro T hok
      rcases hok with hb | ⟨smp, hid, hrec, htail, -⟩
      · exact absurd hb (hnb T sigma)
      · have hsid : smp.id = sigma := by
          simp only [DigitAtom.sampled.injEq] at hid
          exact hid.symm
        rw [← htail]
        exact hbt smp hrec (by rw [hsid]; exact hsi) (by rw [hsid]; exact hl)
    · intro he
      have hjs : j = src := bankRepairDigitSiteInj ring root hj (by omega)
        (by rw [← hsi, he])
      rw [hjs]
      have h0 := cohortEdgeOfSite ring root src R hend 0 (by omega)
      rw [Nat.add_zero] at h0
      exact h0

/-- The aged window is antitone in the cut.  Consumer: the width entry
`L3.CloseTerm.entryCoreOfBarrier`. -/
theorem winAgeMono {ring : DirectedRing n} {root : Fin n} {lane : DigitLane} {src R : Nat}
    {cut cut' : Nat} (hle : cut ≤ cut') {s : CohortLane} {A : DigitAudit c n}
    (h : WinAge ring root lane src R cut' s A) : WinAge ring root lane src R cut s A := by
  refine ⟨h.1, fun q x hx => ?_, fun q h1 h2 L hL => ?_⟩
  · obtain ⟨id, e1, e2⟩ := h.2.1 q x hx
    exact ⟨id, e1, by omega⟩
  · obtain ⟨a1, a2, a3⟩ := h.2.2 q h1 h2 L hL
    refine ⟨a1, a2, fun u hu => ?_⟩
    obtain ⟨b1, id, b2, b3, b4⟩ := a3 u hu
    exact ⟨b1, id, b2, by omega, b4⟩

/-- **The entry at a terminal letter on the ring**: the terminal edge `src + 2R - 1` drawn while
the last target cell holds a live carry whose clean ledger starts with the border-tail stamp
`sigma`.  After the letter the masked lane is in the cycle class with the old cohort gone and
the aged window `WinAge sigma.time` holds.  Consumer: `L3.CloseTerm.entryCoreOfBarrier`. -/
theorem termEntryRing (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (Base : Bool → DigitAtom n → Prop) (A : DigitAudit c n)
    (hbX : (pairW (S (digitSite ring root (src + (2 * R - 1)))).word
      (S (digitSite ring root (src + (2 * R - 1) + 1))).word).1.beta =
        (S (digitSite ring root (src + (2 * R - 1)))).word.beta)
    (hbY : (pairW (S (digitSite ring root (src + (2 * R - 1)))).word
      (S (digitSite ring root (src + (2 * R - 1) + 1))).word).2.beta =
        (S (digitSite ring root (src + (2 * R - 1) + 1))).word.beta)
    (hgc : GhostCorrDistinct ring root lane src R Base S A)
    (hgc' : GhostCorrDistinct ring root lane src R Base
      (phiD ring S (digitSite ring root (src + (2 * R - 1))))
      (digitAuditStep ring S A (digitSite ring root (src + (2 * R - 1)))))
    (h : BarRun ring root lane src R S A) (sigma : DigitStamp n)
    (hsi : sigma.site = digitSite ring root src) (hsl : sigma.lane = lane)
    (hlive : (cohortProj ring root lane src R S).live (2 * R - 1) = true)
    (L : DigitCarryGhost c n) (u : DigitUse c n)
    (hL : (laneCells ring root lane src A.current (2 * R - 1)).carry = some L)
    (hi : L.inherited = none) (hu : L.uses.head? = some u)
    (hop : u.operand = some (.sampled sigma)) :
    (∃ lam : Nat → Nat, CohortCycIn R 0 (cohortProj ring root lane src R
      (phiD ring S (digitSite ring root (src + (2 * R - 1))))) (lam, 0) (2 * R + 1)) ∧
    WinAge ring root lane src R sigma.time (cohortProj ring root lane src R
      (phiD ring S (digitSite ring root (src + (2 * R - 1)))))
      (digitAuditStep ring S A (digitSite ring root (src + (2 * R - 1)))) := by
  have hj : src + (2 * R - 1) < n := by omega
  have hke : cohortEdgeOf root src R (digitSite ring root (src + (2 * R - 1))) =
      some (2 * R - 1) := cohortEdgeOfSite ring root src R hend (2 * R - 1) (by omega)
  have hrows := laneRowsRing ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane A _
    hj hbX hbY hgc.1
  rw [hke] at hrows
  have hproj := cohortProjStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane _
    hj hbX hbY
  rw [hke] at hproj
  have hcorr' := hgc'.1
  unfold GhostCorr at hcorr'
  rw [hproj] at hcorr'
  have hback := trackedBackRing ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane A
    _ hj hbX hbY
  obtain ⟨-, -, hinv⟩ := h
  have hat : BarAt R (cohortProj ring root lane src R S) (laneCells ring root lane src A.current)
      sigma (2 * R - 1) :=
    Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hlive, L, u, hL, hi, hu, hop⟩))
  obtain ⟨hcyc, hlv, hage, hcar⟩ := termEntry hR hrows hgc.1 hcorr' rfl hback
    (hinv sigma hsi hsl) hat
  rw [hproj]
  refine ⟨hcyc, hlv, hage, fun q h1 h2 L' hL' => ?_⟩
  rw [hcar q h1 h2] at hL'
  cases hL'

end Run

end L3.TermEntry

#print axioms L3.TermEntry.barShapeStay
#print axioms L3.TermEntry.barShapeMoveSrc
#print axioms L3.TermEntry.barShapeMoveTgt
#print axioms L3.TermEntry.barTgt
#print axioms L3.TermEntry.pipeXBack
#print axioms L3.TermEntry.pipeYBack
#print axioms L3.TermEntry.delXBack
#print axioms L3.TermEntry.delYBack
#print axioms L3.TermEntry.finXBack
#print axioms L3.TermEntry.finYBack
#print axioms L3.TermEntry.cleanNeStep
#print axioms L3.TermEntry.barAtBack
#print axioms L3.TermEntry.barInvStep
#print axioms L3.TermEntry.termEntry
#print axioms L3.TermEntry.laneRowsRing
#print axioms L3.TermEntry.barRunInitial
#print axioms L3.TermEntry.barRunStep
#print axioms L3.TermEntry.winAgeMono
#print axioms L3.TermEntry.termEntryRing

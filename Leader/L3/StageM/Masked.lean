import Leader.L3.StageM.GhostLane
import Leader.L3.Bank.RepairDigitPacketMomentTrialLabels

/-!
# Stage M (R10c, Lemma e-max): the aligned queue of the post-entrance exports

section 3 (J.queue) and section 5 item 6 on the lane: the aligned labelled queue
(`WinLab`) of the attempt class is kept during Stage M for the packets accepted after the
entrance only, and becomes the aligned queue of the lane at the Stage M stop.

* `maskIn`, `maskL R s G`: the *masked lane*. Every target input that holds an old pending packet
  (ghost flag) or a live carry becomes `X`, every carry is dropped; the source half is unchanged.
  Its pending packets are exactly the packets accepted after the entrance.
* `maskStep`: one lane letter on the lane and its ghost, then masking, has the same source half,
  the same pending tail bits and the same pending labels as one letter on the masked lane
  (row by row: `finMaskCell`, `termMaskCell`, `delMaskCell`; exhaustive case analysis). So the
  masked lane follows the lane dynamics on everything `WinLab` reads.
* `NewBar`: on the ghost, every cell left of a post-entrance pending packet is empty and
  carry-free or another post-entrance pending packet. `newBarStep`: kept by every window move;
  `newBarInit`: holds at the entrance. With it the masked window has the window invariants
  (`maskWin`), so `winLabStep` applies to the masked lane.
* `winLabMaskStep`: `WinLab` of the masked lane is kept by every lane letter (labels `sigStep`
  of the lane). `winLabMaskInit`: at the entrance it follows from `SrcLab` (no post-entrance
  packet yet). `winLabMaskStop`: with no old pending packet and the fresh-carry invariant of the
  lane window, it is `WinLab` of the lane itself.

Exhaustive check before the proof (scratch script, every row and flag pattern; single check):
the masked rows agree with the lane rows on pending tail bits and labels.

Consumer: the Stage M assembly (`WinLab` and `AlignExt` of `WidthLaneCutC` at the stop).
-/

namespace L3.StageMMasked

set_option autoImplicit false

open L3.MarkedCells
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentAlign
open L3.PacketMomentPending
open L3.PacketMomentSites
open L3.PacketMomentQueueLabels
open L3.PacketMomentTrialLabels
open L3.StageMOldRank
open L3.StageMGhostLane

/-! ### The masked lane -/

/-- Mask one target input: a live carry or an old pending packet becomes `X`. Consumer:
`maskL`. -/
def maskIn (i : BankRepairDigitInSh) (k o : Bool) : BankRepairDigitInSh :=
  if k then .X else
    match i with
    | .P T => if o then .X else .P T
    | i => i

/-- **The masked lane** of a lane with its ghost. Consumer: every lemma below. -/
def maskL (R : Nat) (s : CohortLane) (G : Nat → OCell) : CohortLane :=
  { out := s.out,
    inp := fun q => if R ≤ q then maskIn (s.inp q) (s.live q) (G (q - R)).o else s.inp q,
    live := fun q => if R ≤ q then false else s.live q }

/-- A target input of the masked lane. Consumer: `maskStep`. -/
theorem maskInp (R : Nat) (s : CohortLane) (G : Nat → OCell) (j : Nat) :
    (maskL R s G).inp (R + j) = maskIn (s.inp (R + j)) (s.live (R + j)) (G j).o := by
  show (if R ≤ R + j then maskIn (s.inp (R + j)) (s.live (R + j)) (G (R + j - R)).o
    else s.inp (R + j)) = _
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A target carry bit of the masked lane. Consumer: `maskStep`. -/
theorem maskLive (R : Nat) (s : CohortLane) (G : Nat → OCell) (q : Nat) (hq : R ≤ q) :
    (maskL R s G).live q = false := by
  show (if R ≤ q then false else s.live q) = false
  rw [if_pos hq]

/-! ### The rows, cell by cell -/

/-- A pending packet moves on an input-motion edge (the label row `sigFin`). Consumer:
`finMaskCell`. -/
def finMv (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh) (ky : Bool) : Bool :=
  match ix, kx, iy, ky with
  | .P _, false, .E, false => true
  | _, _, _, _ => false

/-- An export is accepted at the border (the label row `sigDel`). Consumer: `delMaskCell`. -/
def delMv (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool) : Bool :=
  match ox, ky, iy with
  | .D _, false, .E => true
  | _, _, _ => false

/-- **The input-motion row, masked.** Consumer: `maskStep`. -/
theorem finMaskCell (bx : Bool) (ix iy : BankRepairDigitInSh) (cx cy : Car) (ox oy : Bool) :
    pwI (maskIn (bankRepairDigitFinStep bx ix (liveOf cx) iy (liveOf cy)).1
        (bankRepairDigitFinStep bx ix (liveOf cx) iy (liveOf cy)).2.1
        (opair bx ⟨cellIn ix, cx, ox⟩ ⟨cellIn iy, cy, oy⟩).1.o) =
      pwI (bankRepairDigitFinStep bx (maskIn ix (liveOf cx) ox) false
        (maskIn iy (liveOf cy) oy) false).1 ∧
    pwI (maskIn (bankRepairDigitFinStep bx ix (liveOf cx) iy (liveOf cy)).2.2.1
        (bankRepairDigitFinStep bx ix (liveOf cx) iy (liveOf cy)).2.2.2
        (opair bx ⟨cellIn ix, cx, ox⟩ ⟨cellIn iy, cy, oy⟩).2.o) =
      pwI (bankRepairDigitFinStep bx (maskIn ix (liveOf cx) ox) false
        (maskIn iy (liveOf cy) oy) false).2.2.1 ∧
    (isPI (maskIn (bankRepairDigitFinStep bx ix (liveOf cx) iy (liveOf cy)).2.2.1
        (bankRepairDigitFinStep bx ix (liveOf cx) iy (liveOf cy)).2.2.2
        (opair bx ⟨cellIn ix, cx, ox⟩ ⟨cellIn iy, cy, oy⟩).2.o) = true →
      finMv ix (liveOf cx) iy (liveOf cy) =
        finMv (maskIn ix (liveOf cx) ox) false (maskIn iy (liveOf cy) oy) false) := by
  cases bx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases cx <;> cases ox <;>
    rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases cy <;> cases oy <;> decide

/-- **The terminal row, masked.** Consumer: `maskStep`. -/
theorem termMaskCell (ix : BankRepairDigitInSh) (cx : Car) (ox : Bool) :
    pwI (maskIn (cohortTermStep ix (liveOf cx)).1 (cohortTermStep ix (liveOf cx)).2
        (oterm ⟨cellIn ix, cx, ox⟩).o) =
      pwI (cohortTermStep (maskIn ix (liveOf cx) ox) false).1 := by
  rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases cx <;> cases ox <;> decide

/-- The ghost of the port edge. Consumer: `delMaskCell`, `maskStep`. -/
def portO (ox : BankRepairDigitOutSh) (c : Cell) (g : OCell) : OCell :=
  if (tokOf ox).isD && decide (c = { i := .e, c := .off }) then oaccept (decide (tokOf ox = .dt)) g
  else oclean g

/-- **The delivery row, masked.** Consumer: `maskStep`. -/
theorem delMaskCell (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (cy : Car) (oy : Bool) :
    (bankRepairDigitDelStep ox iy (liveOf cy)).1 =
      (bankRepairDigitDelStep ox (maskIn iy (liveOf cy) oy) false).1 ∧
    pwI (maskIn (bankRepairDigitDelStep ox iy (liveOf cy)).2.1
        (bankRepairDigitDelStep ox iy (liveOf cy)).2.2
        (portO ox (liftC iy (liveOf cy)) ⟨cellIn iy, cy, oy⟩).o) =
      pwI (bankRepairDigitDelStep ox (maskIn iy (liveOf cy) oy) false).2.1 ∧
    (isPI (maskIn (bankRepairDigitDelStep ox iy (liveOf cy)).2.1
        (bankRepairDigitDelStep ox iy (liveOf cy)).2.2
        (portO ox (liftC iy (liveOf cy)) ⟨cellIn iy, cy, oy⟩).o) = true →
      delMv ox iy (liveOf cy) = delMv ox (maskIn iy (liveOf cy) oy) false) := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases cy <;>
    cases oy <;> decide

/-- The label row `sigFin` at the right cell. Consumer: `maskStep`. -/
theorem sigFinAt (k : Nat) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (σ : Nat → Option Nat) :
    sigFin k ix kx iy ky σ (k + 1) = if finMv ix kx iy ky then σ k else σ (k + 1) := by
  unfold sigFin finMv
  rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases kx <;>
    rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases ky <;> simp [cohortUpd]

/-- The label row `sigDel` at the border. Consumer: `maskStep`. -/
theorem sigDelAt (k : Nat) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (σ : Nat → Option Nat) :
    sigDel k ox iy ky σ (k + 1) = if delMv ox iy ky then σ k else σ (k + 1) := by
  unfold sigDel delMv
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [cohortUpd]

/-- The label row `sigDel` off the border does not read the border. Consumer: `maskStep`. -/
theorem sigDelLow (k : Nat) (ox : BankRepairDigitOutSh) (iy iy' : BankRepairDigitInSh)
    (ky ky' : Bool) (σ : Nat → Option Nat) (q : Nat) (hq : q ≠ k + 1) :
    sigDel k ox iy ky σ q = sigDel k ox iy' ky' σ q := by
  unfold sigDel
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> cases ky' <;>
    rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy' with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [cohortUpd, hq]

/-- Equal pending tail bits and labels. Consumer: `maskStep`. -/
theorem plIEq (a b : BankRepairDigitInSh) (l l' : Option Nat) (h : pwI a = pwI b)
    (hl : isPI a = true → l = l') : plI a l = plI b l' := by
  rcases a with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases b with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [pwI, plI, isPI] at h hl ⊢ <;> exact hl

/-! ### The ghost cells -/

/-- **A ghost cell reads its lane cell.** Consumer: `maskStep`, `maskWin`. -/
theorem ghostCell (R : Nat) (s : CohortLane) (G : Nat → OCell) (h : GhostOf R s G) (j : Nat) :
    G j = { i := cellIn (s.inp (R + j)), c := (G j).c, o := (G j).o } ∧
      liveOf (G j).c = s.live (R + j) := by
  have hj := h j
  unfold StageMGhostLane.fr winOf liftC at hj
  rcases hG : G j with ⟨gi, gc, go⟩
  rw [hG] at hj
  simp only [OCell.cell, Cell.mk.injEq] at hj
  obtain ⟨hi, hc⟩ := hj
  refine ⟨by rw [hi], ?_⟩
  show decide (gc ≠ .off) = s.live (R + j)
  revert hc
  cases s.live (R + j) <;> cases gc <;> simp

/-! ### One letter on the masked lane -/

/-- What `WinLab` reads agrees: the source half, the source labels, and on every target cell the
pending tail bit and label. Consumer: `maskStep`, `winLabCongr`. -/
def MaskSame (R : Nat) (a b : CohortLane) (σa σb : Nat → Option Nat) : Prop :=
  a.out = b.out ∧
    (∀ j, j < R → pwI (a.inp (R + j)) = pwI (b.inp (R + j)) ∧
      plI (a.inp (R + j)) (σa (R + j)) = plI (b.inp (R + j)) (σb (R + j))) ∧
    (∀ q, q < R → σa q = σb q)

/-- One updated cell. Consumer: the row cases of `maskStep`. -/
theorem updOne {α : Type} (f : Nat → α) (k : Nat) (a : α) (q : Nat) :
    cohortUpd f k a q = if q = k then a else f q := rfl

/-- Two updated cells. Consumer: the row cases of `maskStep`. -/
theorem updTwo {α : Type} (f : Nat → α) (k : Nat) (a b : α) (q : Nat) :
    cohortUpd (cohortUpd f k a) (k + 1) b q =
      if q = k + 1 then b else if q = k then a else f q := rfl

/-- The ghost after an edge, cell by cell. Consumer: the row cases of `maskStep`. -/
theorem osetTwoAt (G : Nat → OCell) (p : Nat) (a b : OCell) (j : Nat) :
    osetTwo G p a b j = if j = p then a else if j = p + 1 then b else G j := rfl

/-- The ghost after a one-cell move, cell by cell. Consumer: the row cases of `maskStep`. -/
theorem osetOneAt (G : Nat → OCell) (p : Nat) (a : OCell) (j : Nat) :
    osetOne G p a j = if j = p then a else G j := rfl

/-- The source pipe: the target frames. Consumer: `maskStep`. -/
theorem maskStepPipe (R : Nat) (s : CohortLane) (G : Nat → OCell) (k : Nat) (h1 : k + 1 < R)
    (σ : Nat → Option Nat) :
    MaskSame R (maskL R (cohortEdge R s k) (oApply R G (laneMove R s k)))
      (cohortEdge R (maskL R s G) k) (sigStep R s σ k) (sigStep R (maskL R s G) σ k) := by
  have hm : laneMove R s k = .frame := by unfold laneMove; rw [if_pos h1]
  have es : cohortEdge R s k =
      { s with
        out := (cohortUpd (cohortUpd s.out k
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).1) (k + 1)
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2) } := by
    unfold cohortEdge; rw [if_pos h1]
  have et : cohortEdge R (maskL R s G) k =
      { maskL R s G with
        out := (cohortUpd (cohortUpd s.out k
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).1) (k + 1)
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2) } := by
    unfold cohortEdge; rw [if_pos h1] <;> rfl
  have hσ : sigStep R (maskL R s G) σ k = sigStep R s σ k := by
    unfold sigStep; rw [if_pos h1, if_pos h1]; rfl
  rw [hm, hσ, es, et]
  refine ⟨rfl, fun j _ => ?_, fun q _ => rfl⟩
  rw [maskInp, maskInp]
  exact ⟨rfl, rfl⟩

/-- Edges past the pair: everything frames. Consumer: `maskStep`. -/
theorem maskStepFar (R : Nat) (s : CohortLane) (G : Nat → OCell) (k : Nat) (h3 : 2 * R ≤ k)
    (σ : Nat → Option Nat) :
    MaskSame R (maskL R (cohortEdge R s k) (oApply R G (laneMove R s k)))
      (cohortEdge R (maskL R s G) k) (sigStep R s σ k) (sigStep R (maskL R s G) σ k) := by
  have hm : laneMove R s k = .frame := by
    unfold laneMove; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have es : cohortEdge R s k = s := by
    unfold cohortEdge; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have et : cohortEdge R (maskL R s G) k = maskL R s G := by
    unfold cohortEdge; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hσs : sigStep R s σ k = σ := by
    unfold sigStep; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hσt : sigStep R (maskL R s G) σ k = σ := by
    unfold sigStep; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [hm, hσs, hσt, es, et]
  exact ⟨rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

/-- The delivery edge. Consumer: `maskStep`. -/
theorem maskStepDel (R : Nat) (s : CohortLane) (G : Nat → OCell) (h : GhostOf R s G) (k : Nat)
    (h2 : k + 1 = R) (σ : Nat → Option Nat) :
    MaskSame R (maskL R (cohortEdge R s k) (oApply R G (laneMove R s k)))
      (cohortEdge R (maskL R s G) k) (sigStep R s σ k) (sigStep R (maskL R s G) σ k) := by
  have h1 : ¬ k + 1 < R := by omega
  have hm : laneMove R s k = portMove (winOf R s) (srcLane s k) := by
    unfold laneMove; rw [if_neg h1, if_pos h2]
  have hgo : oApply R G (portMove (winOf R s) (srcLane s k)) =
      osetOne G 0 (portO (s.out k) (winOf R s 0) (G 0)) := by
    unfold portMove portO
    have hs : srcLane s k = tokOf (s.out k) := rfl
    rw [hs]
    split <;> rfl
  have hG0 : G 0 = { i := cellIn (s.inp R), c := (G 0).c, o := (G 0).o } ∧
      liveOf (G 0).c = s.live R := ghostCell R s G h 0
  have hcell := delMaskCell (s.out k) (s.inp R) (G 0).c (G 0).o
  rw [hG0.2, ← hG0.1] at hcell
  have hw0 : winOf R s 0 = liftC (s.inp R) (s.live R) := rfl
  rw [← hw0] at hcell
  have hmi : (maskL R s G).inp R = maskIn (s.inp R) (s.live R) (G 0).o := maskInp R s G 0
  have hml : (maskL R s G).live R = false := maskLive R s G R (Nat.le_refl _)
  have es : cohortEdge R s k =
      { out := cohortUpd s.out k (bankRepairDigitDelStep (s.out k) (s.inp R) (s.live R)).1,
        inp := cohortUpd s.inp R (bankRepairDigitDelStep (s.out k) (s.inp R) (s.live R)).2.1,
        live := cohortUpd s.live R (bankRepairDigitDelStep (s.out k) (s.inp R) (s.live R)).2.2 } := by
    unfold cohortEdge; rw [if_neg h1, if_pos h2, h2]
  have et : cohortEdge R (maskL R s G) k =
      { out := cohortUpd s.out k (bankRepairDigitDelStep (s.out k)
          (maskIn (s.inp R) (s.live R) (G 0).o) false).1,
        inp := cohortUpd (maskL R s G).inp R (bankRepairDigitDelStep (s.out k)
          (maskIn (s.inp R) (s.live R) (G 0).o) false).2.1,
        live := cohortUpd (maskL R s G).live R (bankRepairDigitDelStep (s.out k)
          (maskIn (s.inp R) (s.live R) (G 0).o) false).2.2 } := by
    unfold cohortEdge; rw [if_neg h1, if_pos h2, h2, hmi, hml]; rfl
  have hσs : sigStep R s σ k = sigDel k (s.out k) (s.inp R) (s.live R) σ := by
    unfold sigStep; rw [if_neg h1, if_pos h2, h2]
  have hσt : sigStep R (maskL R s G) σ k =
      sigDel k (s.out k) (maskIn (s.inp R) (s.live R) (G 0).o) false σ := by
    unfold sigStep; rw [if_neg h1, if_pos h2, h2, hmi, hml]; rfl
  have ea := sigDelAt k (s.out k) (s.inp R) (s.live R) σ
  have eb := sigDelAt k (s.out k) (maskIn (s.inp R) (s.live R) (G 0).o) false σ
  rw [h2] at ea eb
  rw [hm, hgo, hσs, hσt, es, et]
  refine ⟨?_, fun j hj => ?_, fun q hq => sigDelLow k _ _ _ _ _ σ q (by omega)⟩
  · show cohortUpd s.out k _ = cohortUpd s.out k _
    rw [hcell.1]
  · rw [maskInp]
    by_cases hj0 : j = 0
    · have c1 : R + j = R := by omega
      have ea' : sigDel k (s.out k) (s.inp R) (s.live R) σ (R + j) =
          if delMv (s.out k) (s.inp R) (s.live R) then σ k else σ R := by rw [c1]; exact ea
      have eb' : sigDel k (s.out k) (maskIn (s.inp R) (s.live R) (G 0).o) false σ (R + j) =
          if delMv (s.out k) (maskIn (s.inp R) (s.live R) (G 0).o) false then σ k else σ R := by
        rw [c1]; exact eb
      simp only [updOne, osetOneAt, if_pos c1, if_pos hj0, ea', eb']
      exact ⟨hcell.2.1, plIEq _ _ _ _ hcell.2.1 (fun hp => by rw [hcell.2.2 hp])⟩
    · have c1 : ¬ (R + j = R) := by omega
      have c2 : R + j ≠ k + 1 := by omega
      refine ⟨?_, ?_⟩ <;>
        simp only [updOne, osetOneAt, if_neg c1, if_neg hj0, maskInp,
          sigDelLow k (s.out k) (s.inp R) (maskIn (s.inp R) (s.live R) (G 0).o) (s.live R) false σ
            (R + j) c2]

/-- The input-motion edges. Consumer: `maskStep`. -/
theorem maskStepFin (R : Nat) (s : CohortLane) (G : Nat → OCell) (h : GhostOf R s G) (p : Nat)
    (hp1 : p + 1 < R) (σ : Nat → Option Nat) :
    MaskSame R (maskL R (cohortEdge R s (R + p)) (oApply R G (laneMove R s (R + p))))
      (cohortEdge R (maskL R s G) (R + p)) (sigStep R s σ (R + p))
      (sigStep R (maskL R s G) σ (R + p)) := by
  have h1 : ¬ R + p + 1 < R := by omega
  have h2 : ¬ R + p + 1 = R := by omega
  have h3 : R + p + 1 < 2 * R := by omega
  have hq : R + p + 1 = R + (p + 1) := by omega
  have hm : laneMove R s (R + p) = .edge p := laneMoveTarget R s p (by omega)
  have hgo : oApply R G (.edge p) =
      osetTwo G p (opair (decide (p = 0)) (G p) (G (p + 1))).1
        (opair (decide (p = 0)) (G p) (G (p + 1))).2 := by
    show oedge R G p = _
    unfold oedge; rw [if_pos hp1]
  have hb : decide (R + p = R) = decide (p = 0) := by
    by_cases hp0 : p = 0
    · subst hp0; simp
    · simp [hp0]
  have hGp := ghostCell R s G h p
  have hGq := ghostCell R s G h (p + 1)
  have hcell := finMaskCell (decide (p = 0)) (s.inp (R + p)) (s.inp (R + (p + 1)))
    (G p).c (G (p + 1)).c (G p).o (G (p + 1)).o
  rw [hGp.2, hGq.2, ← hGp.1, ← hGq.1] at hcell
  have hxN : (maskL R s G).inp (R + p) = maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o :=
    maskInp R s G p
  have hyN : (maskL R s G).inp (R + (p + 1)) =
      maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o := maskInp R s G (p + 1)
  have hlx : (maskL R s G).live (R + p) = false := maskLive R s G _ (by omega)
  have hly : (maskL R s G).live (R + (p + 1)) = false := maskLive R s G _ (by omega)
  have es : cohortEdge R s (R + p) =
      { s with
        inp := cohortUpd (cohortUpd s.inp (R + p) (bankRepairDigitFinStep (decide (p = 0))
          (s.inp (R + p)) (s.live (R + p)) (s.inp (R + (p + 1))) (s.live (R + (p + 1)))).1)
          (R + p + 1) (bankRepairDigitFinStep (decide (p = 0)) (s.inp (R + p))
            (s.live (R + p)) (s.inp (R + (p + 1))) (s.live (R + (p + 1)))).2.2.1,
        live := cohortUpd (cohortUpd s.live (R + p) (bankRepairDigitFinStep (decide (p = 0))
          (s.inp (R + p)) (s.live (R + p)) (s.inp (R + (p + 1))) (s.live (R + (p + 1)))).2.1)
          (R + p + 1) (bankRepairDigitFinStep (decide (p = 0)) (s.inp (R + p))
            (s.live (R + p)) (s.inp (R + (p + 1))) (s.live (R + (p + 1)))).2.2.2 } := by
    unfold cohortEdge
    rw [if_neg h1, if_neg h2, if_pos h3]
    simp only [hb, hq]
  have et : cohortEdge R (maskL R s G) (R + p) =
      { maskL R s G with
        inp := cohortUpd (cohortUpd (maskL R s G).inp (R + p)
          (bankRepairDigitFinStep (decide (p = 0))
            (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false
            (maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o) false).1)
          (R + p + 1) (bankRepairDigitFinStep (decide (p = 0))
            (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false
            (maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o) false).2.2.1,
        live := cohortUpd (cohortUpd (maskL R s G).live (R + p)
          (bankRepairDigitFinStep (decide (p = 0))
            (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false
            (maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o) false).2.1)
          (R + p + 1) (bankRepairDigitFinStep (decide (p = 0))
            (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false
            (maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o) false).2.2.2 } := by
    unfold cohortEdge
    rw [if_neg h1, if_neg h2, if_pos h3]
    simp only [hb, hq, hxN, hyN, hlx, hly]
  have hσs : sigStep R s σ (R + p) = sigFin (R + p) (s.inp (R + p)) (s.live (R + p))
      (s.inp (R + (p + 1))) (s.live (R + (p + 1))) σ := by
    unfold sigStep; rw [if_neg h1, if_neg h2, if_pos h3, hq]
  have hσt : sigStep R (maskL R s G) σ (R + p) = sigFin (R + p)
      (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false
      (maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o) false σ := by
    unfold sigStep; rw [if_neg h1, if_neg h2, if_pos h3, hq, hxN, hyN, hlx, hly]
  have ea := sigFinAt (R + p) (s.inp (R + p)) (s.live (R + p)) (s.inp (R + (p + 1)))
    (s.live (R + (p + 1))) σ
  have eb := sigFinAt (R + p) (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false
    (maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o) false σ
  rw [hq] at ea eb
  rw [hm, hgo, hσs, hσt, es, et]
  refine ⟨rfl, fun j hj => ?_, fun q hq' =>
    by rw [sigFinLow _ _ _ _ _ σ q (by omega), sigFinLow _ _ _ _ _ σ q (by omega)]⟩
  rw [maskInp]
  by_cases hjp : j = p
  · have c1 : ¬ (R + j = R + p + 1) := by omega
    have c2 : R + j = R + p := by omega
    have c3 : R + j ≠ R + p + 1 := c1
    simp only [updOne, osetTwoAt, if_neg c1, if_pos c2, if_pos hjp,
      sigFinLow (R + p) (s.inp (R + p)) (s.live (R + p)) (s.inp (R + (p + 1)))
        (s.live (R + (p + 1))) σ (R + j) c3,
      sigFinLow (R + p) (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false
        (maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o) false σ (R + j) c3]
    exact ⟨hcell.1, plIEq _ _ _ _ hcell.1 (fun _ => rfl)⟩
  · by_cases hjq : j = p + 1
    · have c1 : R + j = R + p + 1 := by omega
      have c4 : R + j = R + (p + 1) := by omega
      have ea' : sigFin (R + p) (s.inp (R + p)) (s.live (R + p)) (s.inp (R + (p + 1)))
          (s.live (R + (p + 1))) σ (R + j) =
          if finMv (s.inp (R + p)) (s.live (R + p)) (s.inp (R + (p + 1))) (s.live (R + (p + 1)))
          then σ (R + p) else σ (R + (p + 1)) := by rw [c4]; exact ea
      have eb' : sigFin (R + p) (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false
          (maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o) false σ (R + j) =
          if finMv (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false
            (maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o) false
          then σ (R + p) else σ (R + (p + 1)) := by rw [c4]; exact eb
      simp only [updOne, osetTwoAt, if_pos c1, if_neg hjp, if_pos hjq, ea', eb']
      exact ⟨hcell.2.1, plIEq _ _ _ _ hcell.2.1 (fun hP => by rw [hcell.2.2 hP])⟩
    · have c1 : ¬ (R + j = R + p + 1) := by omega
      have c2 : ¬ (R + j = R + p) := by omega
      refine ⟨?_, ?_⟩ <;>
        simp only [updOne, osetTwoAt, if_neg c1, if_neg c2, if_neg hjp, if_neg hjq, maskInp,
          sigFinLow (R + p) (s.inp (R + p)) (s.live (R + p)) (s.inp (R + (p + 1)))
            (s.live (R + (p + 1))) σ (R + j) c1,
          sigFinLow (R + p) (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false
            (maskIn (s.inp (R + (p + 1))) (s.live (R + (p + 1))) (G (p + 1)).o) false σ (R + j) c1]

/-- The terminal edge. Consumer: `maskStep`. -/
theorem maskStepTerm (R : Nat) (s : CohortLane) (G : Nat → OCell) (h : GhostOf R s G) (p : Nat)
    (hpR : p + 1 = R) (σ : Nat → Option Nat) :
    MaskSame R (maskL R (cohortEdge R s (R + p)) (oApply R G (laneMove R s (R + p))))
      (cohortEdge R (maskL R s G) (R + p)) (sigStep R s σ (R + p))
      (sigStep R (maskL R s G) σ (R + p)) := by
  have h1 : ¬ R + p + 1 < R := by omega
  have h2 : ¬ R + p + 1 = R := by omega
  have h3 : ¬ R + p + 1 < 2 * R := by omega
  have h4 : R + p + 1 = 2 * R := by omega
  have hm : laneMove R s (R + p) = .edge p := laneMoveTarget R s p (by omega)
  have hgo : oApply R G (.edge p) = osetOne G p (oterm (G p)) := by
    show oedge R G p = _
    unfold oedge; rw [if_neg (by omega), show R - 1 = p by omega]
  have hGp := ghostCell R s G h p
  have hcell := termMaskCell (s.inp (R + p)) (G p).c (G p).o
  rw [hGp.2, ← hGp.1] at hcell
  have es : cohortEdge R s (R + p) =
      { s with
        inp := cohortUpd s.inp (R + p) (cohortTermStep (s.inp (R + p)) (s.live (R + p))).1,
        live := cohortUpd s.live (R + p) (cohortTermStep (s.inp (R + p)) (s.live (R + p))).2 } := by
    unfold cohortEdge; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  have et : cohortEdge R (maskL R s G) (R + p) =
      { maskL R s G with
        inp := cohortUpd (maskL R s G).inp (R + p)
          (cohortTermStep (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false).1,
        live := cohortUpd (maskL R s G).live (R + p)
          (cohortTermStep (maskIn (s.inp (R + p)) (s.live (R + p)) (G p).o) false).2 } := by
    unfold cohortEdge
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, maskInp, maskLive R s G _ (by omega)]
  have hσs : sigStep R s σ (R + p) = σ := by
    unfold sigStep; rw [if_neg h1, if_neg h2, if_neg h3]
  have hσt : sigStep R (maskL R s G) σ (R + p) = σ := by
    unfold sigStep; rw [if_neg h1, if_neg h2, if_neg h3]
  rw [hm, hgo, hσs, hσt, es, et]
  refine ⟨rfl, fun j hj => ?_, fun q _ => rfl⟩
  rw [maskInp]
  by_cases hjp : j = p
  · have c1 : R + j = R + p := by omega
    simp only [updOne, osetOneAt, if_pos c1, if_pos hjp]
    exact ⟨hcell, plIEq _ _ _ _ hcell (fun _ => rfl)⟩
  · have c1 : ¬ (R + j = R + p) := by omega
    refine ⟨?_, ?_⟩ <;> simp only [updOne, osetOneAt, if_neg c1, if_neg hjp, maskInp]

/-- **One lane letter commutes with masking** on everything `WinLab` reads. Consumer:
`winLabMaskStep`. -/
theorem maskStep (R : Nat) (s : CohortLane) (G : Nat → OCell) (h : GhostOf R s G) (k : Nat)
    (σ : Nat → Option Nat) :
    MaskSame R (maskL R (cohortEdge R s k) (oApply R G (laneMove R s k)))
      (cohortEdge R (maskL R s G) k) (sigStep R s σ k) (sigStep R (maskL R s G) σ k) := by
  by_cases h1 : k + 1 < R
  · exact maskStepPipe R s G k h1 σ
  · by_cases h2 : k + 1 = R
    · exact maskStepDel R s G h k h2 σ
    · by_cases h3 : 2 * R ≤ k
      · exact maskStepFar R s G k h3 σ
      · obtain ⟨p, rfl⟩ : ∃ p, k = R + p := ⟨k - R, by omega⟩
        by_cases h4 : p + 1 < R
        · exact maskStepFin R s G h p h4 σ
        · exact maskStepTerm R s G h p (by omega) σ

/-! ### `WinLab` reads only what `MaskSame` compares -/

/-- The source word reads the source half only. Consumer: `winLabCongr`. -/
theorem sFromCongr (R : Nat) (out : Nat → BankRepairDigitOutSh) (σ σ' : Nat → Option Nat) :
    ∀ k, (∀ q, q < k → σ q = σ' q) → sFrom R out σ k = sFrom R out σ' k
  | 0 => fun _ => rfl
  | k + 1 => fun h => by
      show sw R k (out k) (σ k) ++ sFrom R out σ k = sw R k (out k) (σ' k) ++ sFrom R out σ' k
      rw [h k (by omega), sFromCongr R out σ σ' k (fun q hq => h q (by omega))]

/-- **`WinLab` transfers along `MaskSame`.** Consumer: `winLabMaskStep`, `winLabMaskStop`. -/
theorem winLabCongr (R : Nat) (hR : 1 ≤ R) (a b : CohortLane) (σa σb : Nat → Option Nat)
    (h : MaskSame R a b σa σb) (hw : WinLab R a σa) : WinLab R b σb := by
  obtain ⟨ho, hc, hs⟩ := h
  have hpw : pendWord R b = pendWord R a :=
    gFromCongr _ _ R (fun j hj => (hc j hj).1.symm)
  have hpl : pendLab R b σb = pendLab R a σa :=
    lFromCongr _ _ R (fun j hj => (hc j hj).2.symm)
  have hext : extWord R b = extWord R a := by
    unfold extWord; rw [hpw, ho]
  have hlab : labExt R b σb = labExt R a σa := by
    unfold labExt siteWord; rw [hpl, ho, sFromCongr R b.out σb σa R (fun q hq => (hs q hq).symm)]
  have h0 : σb 0 = σa 0 := (hs 0 (by omega)).symm
  obtain ⟨x, ⟨hA1, hA2, b1, hA3⟩, ⟨hL1, hL2, hL3, b2, hL4⟩⟩ := hw
  refine ⟨x, ⟨by rw [← ho]; exact hA1, hA2, b1, by rw [hext]; exact hA3⟩,
    ⟨by rw [← ho]; exact hL1, fun hD => ?_, hL3, b2, by rw [hlab]; exact hL4⟩⟩
  rw [h0]
  exact hL2 (by rw [ho]; exact hD)

/-! ### The post-entrance barrier on the ghost -/

/-- A post-entrance pending packet (carry-free, not old). Consumer: `NewBar`. -/
def newPc (c : OCell) : Bool := c.i.isP && decide (c.c = .off) && !c.o

/-- An empty carry-free register or a post-entrance pending packet. Consumer: `NewBar`. -/
def goodC (c : OCell) : Bool := (decide (c.i = .e) && decide (c.c = .off)) || newPc c

/-- **Left of a post-entrance pending packet only empty carry-free registers or post-entrance
pending packets.** Consumer: `maskWin`. -/
def NewBar (r : Nat) (G : Nat → OCell) : Prop :=
  ∀ i j, j < i → i < r → newPc (G i) = true → goodC (G j) = true

/-- Two good registers stay good across an edge. Consumer: `newBarStep`. -/
theorem goodPair (b : Bool) (x y : OCell) :
    goodC x = true → goodC y = true →
      goodC (opair b x y).1 = true ∧ goodC (opair b x y).2 = true := by
  rcases x with ⟨xi, xc, xo⟩
  rcases y with ⟨yi, yc, yo⟩
  cases b <;> cases xi <;> cases xc <;> cases xo <;> cases yi <;> cases yc <;> cases yo <;>
    decide

/-- A post-entrance packet after an edge comes from one before it. Consumer: `newBarStep`. -/
theorem newPair (b : Bool) (x y : OCell) :
    (newPc (opair b x y).1 = true → newPc x = true) ∧
      (newPc (opair b x y).2 = true → newPc x = true ∨ newPc y = true) ∧
      ((newPc y = true → goodC x = true) → newPc (opair b x y).2 = true →
        goodC (opair b x y).1 = true) := by
  rcases x with ⟨xi, xc, xo⟩
  rcases y with ⟨yi, yc, yo⟩
  cases b <;> cases xi <;> cases xc <;> cases xo <;> cases yi <;> cases yc <;> cases yo <;>
    decide

/-- The terminal, cleanup and acceptance rows. Consumer: `newBarStep`. -/
theorem newOther (t : Bool) (x : OCell) :
    newPc (oterm x) = false ∧ (goodC x = true → goodC (oclean x) = true) ∧
      (goodC x = true → goodC (oaccept t x) = true) := by
  rcases x with ⟨xi, xc, xo⟩
  cases t <;> cases xi <;> cases xc <;> cases xo <;> decide

/-- **The post-entrance barrier is kept by every window move.** Consumer: the Stage M
assembly. -/
theorem newBarStep (r : Nat) (G : Nat → OCell) (m : WMove) (hm : m.Ok r) (h : NewBar r G) :
    NewBar r (oApply r G m) := by
  intro i j hji hi hn
  cases m with
  | frame => exact h i j hji hi hn
  | edge p =>
      have hp : p < r := hm
      show goodC (oedge r G p j) = true
      change newPc (oedge r G p i) = true at hn
      unfold oedge at hn ⊢
      by_cases hp1 : p + 1 < r
      · rw [if_pos hp1] at hn ⊢
        have np := newPair (decide (p = 0)) (G p) (G (p + 1))
        have gp := goodPair (decide (p = 0)) (G p) (G (p + 1))
        simp only [osetTwo] at hn ⊢
        by_cases hip : i = p
        · subst hip
          rw [if_pos rfl] at hn
          rw [if_neg (by omega), if_neg (by omega)]
          exact h i j hji hi (np.1 hn)
        · rw [if_neg hip] at hn
          by_cases hiq : i = p + 1
          · subst hiq
            rw [if_pos rfl] at hn
            by_cases hjp : j = p
            · subst hjp
              rw [if_pos rfl]
              exact np.2.2 (fun hy => h (j + 1) j (by omega) hi hy) hn
            · rw [if_neg hjp, if_neg (by omega)]
              rcases np.2.1 hn with hx | hy
              · exact h p j (by omega) (by omega) hx
              · exact h (p + 1) j hji hi hy
          · rw [if_neg hiq] at hn
            by_cases hjp : j = p
            · subst hjp
              rw [if_pos rfl]
              exact (gp (h i j hji hi hn) (h i (j + 1) (by omega) hi hn)).1
            · rw [if_neg hjp]
              by_cases hjq : j = p + 1
              · subst hjq
                rw [if_pos rfl]
                exact (gp (h i p (by omega) hi hn) (h i (p + 1) hji hi hn)).2
              · rw [if_neg hjq]
                exact h i j hji hi hn
      · rw [if_neg hp1] at hn ⊢
        simp only [osetOne] at hn ⊢
        by_cases hip : i = r - 1
        · rw [if_pos hip, (newOther false (G (r - 1))).1] at hn
          exact absurd hn (by decide)
        · rw [if_neg hip] at hn
          rw [if_neg (by omega)]
          exact h i j hji hi hn
  | clean =>
      change newPc (osetOne G 0 (oclean (G 0)) i) = true at hn
      show goodC (osetOne G 0 (oclean (G 0)) j) = true
      simp only [osetOne] at hn ⊢
      rw [if_neg (show i ≠ 0 by omega)] at hn
      by_cases hj0 : j = 0
      · rw [if_pos hj0]
        subst hj0
        exact (newOther false (G 0)).2.1 (h i 0 hji hi hn)
      · rw [if_neg hj0]
        exact h i j hji hi hn
  | accept t =>
      change newPc (osetOne G 0 (oaccept t (G 0)) i) = true at hn
      show goodC (osetOne G 0 (oaccept t (G 0)) j) = true
      simp only [osetOne] at hn ⊢
      rw [if_neg (show i ≠ 0 by omega)] at hn
      by_cases hj0 : j = 0
      · rw [if_pos hj0]
        subst hj0
        exact (newOther t (G 0)).2.2 (h i 0 hji hi hn)
      · rw [if_neg hj0]
        exact h i j hji hi hn

/-- At the entrance no packet is post-entrance. Consumer: the Stage M assembly. -/
theorem newBarInit (R : Nat) (s : CohortLane) : NewBar R (ghostInit R s) := by
  intro i _ _ _ hn
  exfalso
  revert hn
  show ((cellIn (s.inp (R + i))).isP && decide ((if s.live (R + i) then Car.inh else Car.off) = .off) &&
    !(cellIn (s.inp (R + i))).isP) = true → False
  cases (cellIn (s.inp (R + i))).isP <;> simp

/-! ### The masked window -/

/-- A masked cell: pending only if post-entrance, an obstacle only if not good. Consumer:
`maskWin`. -/
theorem maskCell (i : BankRepairDigitInSh) (c : Car) (o : Bool) :
    ((cellIn (maskIn i (liveOf c) o)).isP = true →
        newPc { i := cellIn i, c := c, o := o } = true) ∧
      (obC (liftC (maskIn i (liveOf c) o) false) = true →
        goodC { i := cellIn i, c := c, o := o } = false) := by
  rcases i with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases c <;> cases o <;> decide

/-- **The masked window has the window invariants** (no carry; every pending packet left of
every obstacle). Consumer: `winLabMaskStep`. -/
theorem maskWin (R : Nat) (s : CohortLane) (G : Nat → OCell) (hg : GhostOf R s G)
    (hn : NewBar R G) : Inv R (winOf R (maskL R s G)) ∧ Barrier R (winOf R (maskL R s G)) := by
  have hw : ∀ j, winOf R (maskL R s G) j =
      liftC (maskIn (s.inp (R + j)) (s.live (R + j)) (G j).o) false := by
    intro j
    show liftC ((maskL R s G).inp (R + j)) ((maskL R s G).live (R + j)) = _
    rw [maskInp, maskLive R s G _ (by omega)]
  have hoff : ∀ j, (winOf R (maskL R s G) j).c = .off := by
    intro j; rw [hw]; rfl
  have hA : InvA R (winOf R (maskL R s G)) := by
    intro j _ hj; rw [hoff] at hj; cases hj
  have hU : InvU R (winOf R (maskL R s G)) := by
    intro j _ _ _ hj; rw [hoff] at hj; cases hj
  refine ⟨⟨hA, hU⟩, ?_⟩
  intro i j hi hj hP hO
  rw [hw] at hP hO
  have ci := ghostCell R s G hg i
  have cj := ghostCell R s G hg j
  rw [← ci.2] at hP
  rw [← cj.2] at hO
  have hni := (maskCell (s.inp (R + i)) (G i).c (G i).o).1 hP
  have hgj := (maskCell (s.inp (R + j)) (G j).c (G j).o).2 hO
  rw [← ci.1] at hni
  rw [← cj.1] at hgj
  by_cases hlt : i < j
  · exact hlt
  · exfalso
    by_cases hij : j = i
    · subst hij
      revert hni hgj
      rcases G j with ⟨a, b, c⟩
      cases a <;> cases b <;> cases c <;> decide
    · have := hn i j (by omega) hi hni
      rw [hgj] at this
      cases this

/-! ### `WinLab` of the masked lane -/

/-- **`WinLab` of the masked lane is kept by every lane letter.** Consumer: the Stage M
assembly. -/
theorem winLabMaskStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (G : Nat → OCell)
    (σ : Nat → Option Nat) (hg : GhostOf R s G) (hn : NewBar R G) (o : Option Nat)
    (h : WinLab R (maskL R s G) σ) :
    WinLab R (maskL R (cohortLaneStep R s o) (gstep R s G o))
      (match o with | none => σ | some k => sigStep R s σ k) := by
  cases o with
  | none => exact h
  | some k =>
      have h1 := winLabStep R hR (maskL R s G) σ k h (maskWin R s G hg hn)
      exact winLabCongr R (by omega) _ _ _ _ (by
        have hs := maskStep R s G hg k σ
        obtain ⟨a, b, c⟩ := hs
        exact ⟨a.symm, fun j hj => ⟨(b j hj).1.symm, (b j hj).2.symm⟩,
          fun q hq => (c q hq).symm⟩) h1

/-- **Start**: at the entrance every pending packet is old, so the labelled aligned source is
the labelled aligned queue of the masked lane. Consumer: the Stage M assembly. -/
theorem winLabMaskInit (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) (h : SrcLab R s σ) :
    WinLab R (maskL R s (ghostInit R s)) σ := by
  obtain ⟨a, hA, hL⟩ := h
  have hnp : ∀ q, R ≤ q → q < 2 * R → isPI ((maskL R s (ghostInit R s)).inp q) = false := by
    intro q h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, q = R + j := ⟨q - R, by omega⟩
    rw [maskInp]
    show isPI (maskIn (s.inp (R + j)) (s.live (R + j)) (cellIn (s.inp (R + j))).isP) = false
    unfold maskIn
    cases s.live (R + j) <;> rcases s.inp (R + j) with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rfl
  exact ⟨a, alignExtOfSrc R a _ hA hnp, labExtOfSite R a _ σ hL hnp⟩

/-- **Stop**: with no old pending packet and the fresh-carry invariant of the lane window, the
masked lane and the lane agree on everything `WinLab` reads. Consumer: the Stage M assembly. -/
theorem winLabMaskStop (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (G : Nat → OCell)
    (σ : Nat → Option Nat) (hg : GhostOf R s G) (hold : ∀ j, j < R → oP (G j) = false)
    (hinv : Inv R (winOf R s)) (h : WinLab R (maskL R s G) σ) : WinLab R s σ := by
  refine winLabCongr R hR (maskL R s G) s σ σ ⟨rfl, fun j hj => ?_, fun _ _ => rfl⟩ h
  rw [maskInp]
  have hc := ghostCell R s G hg j
  have ho := hold j hj
  have hE : s.live (R + j) = true → s.inp (R + j) = .E := by
    intro hl
    have hf : (winOf R s j).c = .fresh := by
      show (liftC (s.inp (R + j)) (s.live (R + j))).c = .fresh
      rw [hl]; rfl
    have := (hinv.1 j hj hf).1
    revert this
    show (cellIn (s.inp (R + j))) = .e → s.inp (R + j) = .E
    rcases s.inp (R + j) with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> simp [cellIn]
  have hoP : ∀ T, s.inp (R + j) = .P T → (G j).o = false := by
    intro T hT
    rw [hc.1] at ho
    revert ho
    show ((G j).o && (cellIn (s.inp (R + j))).isP) = false → (G j).o = false
    rw [hT]
    cases T <;> cases (G j).o <;> simp [cellIn, Inp.isP]
  have key : maskIn (s.inp (R + j)) (s.live (R + j)) (G j).o = s.inp (R + j) ∨
      (s.live (R + j) = true ∧ s.inp (R + j) = .E) := by
    unfold maskIn
    cases hl : s.live (R + j)
    · left
      simp only [Bool.false_eq_true, if_false]
      rcases hi : s.inp (R + j) with _ | _ | ⟨T⟩ | ⟨T⟩
      · rfl
      · rfl
      · rw [hoP T hi]; rfl
      · rfl
    · right; exact ⟨rfl, hE hl⟩
  rcases key with e | ⟨hl, hi⟩
  · rw [e]; exact ⟨rfl, rfl⟩
  · simp only [hl, hi, maskIn, if_true]
    exact ⟨rfl, rfl⟩

end L3.StageMMasked

#print axioms L3.StageMMasked.finMaskCell
#print axioms L3.StageMMasked.delMaskCell
#print axioms L3.StageMMasked.maskStep
#print axioms L3.StageMMasked.winLabCongr
#print axioms L3.StageMMasked.newBarStep
#print axioms L3.StageMMasked.maskWin
#print axioms L3.StageMMasked.winLabMaskStep
#print axioms L3.StageMMasked.winLabMaskInit
#print axioms L3.StageMMasked.winLabMaskStop

import Leader.L3.Width.PacketMomentTransport
import Leader.L3.Bank.RepairDigitPacketMomentPrep

/-!
# Lemma e-packet before the first attempt: the distinguished tail, in moment form

The phase "a genuinely generated source tail" of Lemma e-packet (repair.tex 1252-1280): from an
arbitrary lane state the source block of the pair reaches `SrcAligned` (some `Align a`, begun at
the export of the distinguished tail, `preStep`), with every release before it included.

The potential is `tailPot = tailIdx · W + tailG`, `W = 2(R+1)²`:

* `tailIdx` counts the exports still owed before the distinguished tail: the least `m` with
  `Pre R m` when cell `0` owes the next tail (`CZero`), the whole owed word otherwise. It never
  rises, and every export before `SrcAligned` lowers it (`tailIdxStep`).
* `tailG`: while the target border is free, the head potential `headPot` (twice the distance of
  the rightmost occupied source cell to the port, plus one for `U` there); otherwise
  `2R + 1 + releaseWeight`. A free border stays free until an export (`borderKeep`); the release
  weight drops on a nominated edge (`edgeDrop`); the head potential drops on the edge of the
  rightmost occupied source cell, or that edge exports (`headDrop`).

Hence `E[z^T] ≤ w^{tailBudget R}`, `tailBudget R = (R² + 1) · 2(R+1)²`, `w = N/(N-n)`
(`tailMoment` on the lane, `widthTailMoment` at any digit reference, `bankTailMomentCheck` at
the BANK reference). The paper's `F = (2r²+1)B + 8r³` with `B = 3r²+4r+2` bounds the same phase
(releases included); `tailBudget R ≤ F` at `r = R`.

Structural proof from the literal rows (`bankRepairDigitPipeStep`, `bankRepairDigitDelStep`,
`bankRepairDigitFinStep`), uniform over source values and the audit.
-/

namespace L3.WidthPacketMomentTail

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open L3
open L3.PairMoment
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.WidthDigit
open L3.DigitPacketRelease
open L3.PacketMomentRelease
open L3.PacketMomentAlign
open L3.PacketMomentPrep
open L3.WidthPacketMoment

/-! ### A least index -/

/-- The least `m ≤ b` with `P m`, and `b + 1` if there is none. Consumer: `tailIdx`. -/
noncomputable def leastUpTo (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | b + 1 => if ∃ m, m ≤ b ∧ P m then leastUpTo P b else b + 1

/-- The least index is below every witness and is a witness. Consumer: `tailIdxStep`. -/
theorem leastUpToSpec (P : Nat → Prop) : ∀ b m, m ≤ b → P m →
    leastUpTo P b ≤ m ∧ P (leastUpTo P b)
  | 0, m, hm, hp => by
      obtain rfl : m = 0 := by omega
      simp only [leastUpTo]
      exact ⟨Nat.le_refl _, hp⟩
  | b + 1, m, hm, hp => by
      simp only [leastUpTo]
      split
      · next h =>
        obtain ⟨m', hm', hp'⟩ := h
        refine ⟨?_, (leastUpToSpec P b m' hm' hp').2⟩
        rcases Nat.lt_or_ge b m with hbm | hbm
        · exact Nat.le_trans (leastUpToSpec P b m' hm' hp').1 (by omega)
        · exact (leastUpToSpec P b m hbm hp).1
      · next h =>
        have hm' : m = b + 1 := by
          rcases Nat.lt_or_ge m (b + 1) with h1 | h1
          · exact absurd ⟨m, by omega, hp⟩ h
          · omega
        subst hm'
        exact ⟨Nat.le_refl _, hp⟩

/-! ### Lengths of the owed word -/

/-- One cell owes at most `R` exports. Consumer: `wFromLen`. -/
theorem cwLen (R j : Nat) (hR : 1 ≤ R) (x : BankRepairDigitOutSh) : (cw R j x).length ≤ R := by
  rcases x with _ | _ | ⟨_ | _⟩
  · simp [cw]
  · by_cases h : j = 0 <;> simp [cw, blk, h] <;> omega
  · simp [cw] <;> omega
  · by_cases h : j = 0 <;> simp [cw, h] <;> omega

/-- Consumer: `srcWordLen`. -/
theorem wFromLen (R : Nat) (hR : 1 ≤ R) (out : Nat → BankRepairDigitOutSh) :
    ∀ k, (wFrom R out k).length ≤ k * R
  | 0 => by simp [wFrom]
  | k + 1 => by
      simp only [wFrom, List.length_append]
      have h1 := cwLen R k hR (out k)
      have h2 := wFromLen R hR out k
      rw [Nat.succ_mul]
      omega

/-- The source block owes at most `R²` exports. Consumer: `preLe`, `tailIdxLe`. -/
theorem srcWordLen (R : Nat) (hR : 1 ≤ R) (out : Nat → BankRepairDigitOutSh) :
    (srcWord R out).length ≤ R * R :=
  wFromLen R hR out R

/-- Consumer: `tailIdxStep`, `tailIdxLe`. -/
theorem preLe (R m : Nat) (hR : 1 ≤ R) (out : Nat → BankRepairDigitOutSh)
    (h : Pre R m out) : m ≤ R * R := by
  obtain ⟨_, Y, c, hY, hw⟩ := h
  have h1 := congrArg List.length hw
  rw [List.length_append] at h1
  have h2 := srcWordLen R hR out
  omega

/-- `Pre 0` is aligned. Consumer: `tailIdxStep`. -/
theorem preZeroAligned (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (h : Pre R 0 s.out) :
    SrcAligned R s := by
  obtain ⟨hc, Y, c, hY, hw⟩ := h
  have hY0 : Y = [] := List.eq_nil_of_length_eq_zero hY
  exact ⟨0, hc, by omega, c, by rw [hw, hY0]; rfl⟩

/-! ### The export index -/

/-- **Exports owed before the distinguished tail**: the least `Pre` index once cell `0` owes the
next tail, the whole owed word before. Consumer: `tailPot`. -/
noncomputable def tailIdx (R : Nat) (s : CohortLane) : Nat :=
  if CZero s.out then leastUpTo (fun m => Pre R m s.out) (R * R) else (srcWord R s.out).length

/-- Consumer: `tailIdxLe`, `tailIdxStep`. -/
theorem tailIdxSeg (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (hc : CZero s.out) :
    tailIdx R s ≤ (wSeg R s.out 1 (R - 1)).length := by
  have hp := preOfCZero R hR s.out hc
  unfold tailIdx
  rw [if_pos hc]
  exact (leastUpToSpec _ (R * R) _ (preLe R _ hR s.out hp) hp).1

/-- Consumer: `tailIdxStep`, `tailPotLe`. -/
theorem tailIdxLe (R : Nat) (hR : 1 ≤ R) (s : CohortLane) :
    tailIdx R s ≤ (srcWord R s.out).length := by
  by_cases hc : CZero s.out
  · have h1 := tailIdxSeg R hR s hc
    have h2 := congrArg List.length (wordCZero R hR s.out hc)
    rw [List.length_append] at h2
    omega
  · unfold tailIdx
    rw [if_neg hc]
    exact Nat.le_refl _

/-- **An export removes the first owed letter**, from any source block. Consumer:
`tailIdxStep`. -/
theorem exportWord (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (B : Bool)
    (h : Exported R s k B) : srcWord R s.out = B :: srcWord R (cohortEdge R s k).out := by
  obtain ⟨h2, hi, hl, hi', _⟩ := h
  have h1 : ¬ k + 1 < R := by omega
  have hd := portWord R hR (s.out k) (s.inp (k + 1)) (s.live (k + 1))
  have hout : (cohortEdge R s k).out =
      cohortUpd s.out k (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1 := by
    unfold cohortEdge; rw [if_neg h1, if_pos h2]
  have hinp : (cohortEdge R s k).inp R =
      (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.1 := by
    unfold cohortEdge; rw [if_neg h1, if_pos h2]
    show cohortUpd s.inp (k + 1) _ R = _
    simp [cohortUpd, h2]
  have hk : k = R - 1 := by omega
  have hw' := wordPort R (cohortEdge R s k).out (by omega)
  have hw := wordPort R s.out (by omega)
  have hlow : wFrom R (cohortEdge R s k).out (R - 1) = wFrom R s.out (R - 1) :=
    wFromCongr R _ _ _ (fun j hj => by rw [hout]; simp [cohortUpd, show j ≠ k by omega])
  have ek : (cohortEdge R s k).out (R - 1) =
      (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1 := by
    rw [hout, ← hk]; simp [cohortUpd]
  rw [h2] at hd hinp ek
  rw [← hk] at hw hw' hlow ek hd
  rw [hw', hw, hlow, ek]
  rcases hd with ⟨B', _, _, _, hd2, hcw⟩ | ⟨_, hd2⟩
  · have hB : B' = B := by
      rw [hinp, hd2] at hi'
      simpa using hi'
    rw [hcw, hB, List.cons_append]
  · exfalso
    rw [hinp, hd2] at hi'
    simp [hl, hi] at hi'

/-- **Before cell `0` owes the next tail**, a letter that exports nothing keeps the owed word,
or writes `U` into an empty cell `0` and keeps the other cells. Consumer: `tailIdxStep`,
`L3.WidthPacketMomentTailLab.wordAny`. -/
theorem freeWord (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (h : ¬ CZero s.out)
    (hne : ∀ B, ¬ Exported R s k B) :
    srcWord R (cohortEdge R s k).out = srcWord R s.out ∨
      ((cohortEdge R s k).out 0 = .U ∧
        (wSeg R (cohortEdge R s k).out 1 (R - 1)).length ≤ (srcWord R s.out).length) := by
  by_cases h1 : k + 1 < R
  · have hout : (cohortEdge R s k).out =
        cohortUpd (cohortUpd s.out k (bankRepairDigitPipeStep (decide (k = 0)) (s.out k)
          (s.out (k + 1))).1) (k + 1)
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
      unfold cohortEdge; rw [if_pos h1]
    by_cases hk : k = 0
    · subst hk
      rcases hx : s.out 0 with _ | _ | ⟨_ | _⟩
      · right
        have hpt : ∀ j, 1 ≤ j → (cohortEdge R s 0).out j = s.out j := by
          intro j hj
          rw [hout]
          by_cases hj1 : j = 0 + 1
          · subst hj1; simp [cohortUpd, bankRepairDigitPipeStep, hx]
          · simp [cohortUpd, hj1, show j ≠ 0 by omega]
        refine ⟨?_, ?_⟩
        · rw [hout]; simp [cohortUpd, bankRepairDigitPipeStep, hx]
        · rw [wSegCongr R _ _ 1 (R - 1) (fun j hj _ => hpt j hj)]
          have h3 := wFromAdd R s.out 1 (R - 1)
          rw [show 1 + (R - 1) = R by omega] at h3
          unfold srcWord
          rw [h3, List.length_append]
          omega
      · exact absurd (Or.inl hx) h
      · left
        have hsplit' := wordSplit R (cohortEdge R s 0).out 0 (by omega)
        have hsplit := wordSplit R s.out 0 (by omega)
        have hseg : wSeg R (cohortEdge R s 0).out (0 + 2) (R - (0 + 2)) =
            wSeg R s.out (0 + 2) (R - (0 + 2)) :=
          wSegCongr R _ _ _ _ (fun j hj _ => by
            rw [hout]; simp [cohortUpd, show j ≠ 0 by omega, show j ≠ 0 + 1 by omega])
        have ek1 : (cohortEdge R s 0).out (0 + 1) =
            (bankRepairDigitPipeStep (decide (0 = 0)) (s.out 0) (s.out (0 + 1))).2 := by
          rw [hout]; simp [cohortUpd]
        have ek : (cohortEdge R s 0).out 0 =
            (bankRepairDigitPipeStep (decide (0 = 0)) (s.out 0) (s.out (0 + 1))).1 := by
          rw [hout]; simp [cohortUpd]
        rw [hsplit', hsplit, hseg, ek1, ek, hx]
        have hw0 : ∀ out : Nat → BankRepairDigitOutSh, wFrom R out 0 = [] := fun _ => rfl
        rw [hw0, hw0]
        rcases s.out (0 + 1) with _ | _ | ⟨_ | _⟩ <;> simp [bankRepairDigitPipeStep, cw]
      · exact absurd (Or.inr hx) h
    · left
      have hsplit' := wordSplit R (cohortEdge R s k).out k (by omega)
      have hsplit := wordSplit R s.out k (by omega)
      have hseg : wSeg R (cohortEdge R s k).out (k + 2) (R - (k + 2)) =
          wSeg R s.out (k + 2) (R - (k + 2)) :=
        wSegCongr R _ _ _ _ (fun j hj _ => by
          rw [hout]; simp [cohortUpd, show j ≠ k by omega, show j ≠ k + 1 by omega])
      have hlow : wFrom R (cohortEdge R s k).out k = wFrom R s.out k :=
        wFromCongr R _ _ _ (fun j hj => by
          rw [hout]; simp [cohortUpd, show j ≠ k by omega, show j ≠ k + 1 by omega])
      have ek1 : (cohortEdge R s k).out (k + 1) =
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
        rw [hout]; simp [cohortUpd]
      have ek : (cohortEdge R s k).out k =
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).1 := by
        rw [hout]; simp [cohortUpd]
      rw [hsplit', hsplit, hseg, hlow, ek1, ek]
      have e0 : decide (k = 0) = false := by simp [hk]
      rw [e0]
      have hi := pipeWordInner R k (by omega) h1 (s.out k) (s.out (k + 1))
      congr 1
      rw [← List.append_assoc, hi, List.append_assoc]
  · by_cases h2 : k + 1 = R
    · left
      have hd := portWord R hR (s.out k) (s.inp (k + 1)) (s.live (k + 1))
      have hout : (cohortEdge R s k).out =
          cohortUpd s.out k (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1 := by
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
      have hinp : (cohortEdge R s k).inp R =
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.1 := by
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
        show cohortUpd s.inp (k + 1) _ R = _
        simp [cohortUpd, h2]
      have hlive : (cohortEdge R s k).live R =
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.2 := by
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
        show cohortUpd s.live (k + 1) _ R = _
        simp [cohortUpd, h2]
      have hk : k = R - 1 := by omega
      have hw' := wordPort R (cohortEdge R s k).out (by omega)
      have hw := wordPort R s.out (by omega)
      have hlow : wFrom R (cohortEdge R s k).out (R - 1) = wFrom R s.out (R - 1) :=
        wFromCongr R _ _ _ (fun j hj => by rw [hout]; simp [cohortUpd, show j ≠ k by omega])
      have ek : (cohortEdge R s k).out (R - 1) =
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1 := by
        rw [hout, ← hk]; simp [cohortUpd]
      rw [h2] at hd hinp hlive ek
      rw [← hk] at hw hw' hlow ek hd
      rw [hw', hw, hlow, ek]
      rcases hd with ⟨B, _, hky, hiy, hd2, _⟩ | ⟨hcw, _⟩
      · exact absurd ⟨h2, hiy, hky, by rw [hinp, hd2], by rw [hlive, hd2]⟩ (hne B)
      · rw [hcw]
    · left
      have hout : (cohortEdge R s k).out = s.out := by
        unfold cohortEdge; rw [if_neg h1, if_neg h2]
        split
        · rfl
        · split <;> rfl
      rw [hout]

/-- **The export index never rises, and every export before the alignment lowers it.**
Consumer: `tailEdgeMono`, `tailExportDrop`. -/
theorem tailIdxStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat)
    (hna : ¬ SrcAligned R s) :
    ((∀ B, ¬ Exported R s k B) → tailIdx R (cohortEdge R s k) ≤ tailIdx R s) ∧
      (∀ B, Exported R s k B → tailIdx R (cohortEdge R s k) + 1 ≤ tailIdx R s) := by
  have hle' := tailIdxLe R (by omega) (cohortEdge R s k)
  by_cases hc : CZero s.out
  · have hc' := c0Step R hR s k hc
    have hp0 := preOfCZero R (by omega) s.out hc
    have hspec := leastUpToSpec (fun m => Pre R m s.out) (R * R) _ (preLe R _ (by omega) s.out hp0)
      hp0
    generalize hm : leastUpTo (fun m => Pre R m s.out) (R * R) = m at hspec
    have ht : tailIdx R s = m := by unfold tailIdx; rw [if_pos hc, hm]
    have hP : Pre R m s.out := hspec.2
    have hm0 : m ≠ 0 := fun h0 => hna (preZeroAligned R (by omega) s (h0 ▸ hP))
    have ht' : ∀ m', Pre R m' (cohortEdge R s k).out → tailIdx R (cohortEdge R s k) ≤ m' := by
      intro m' hm'
      unfold tailIdx
      rw [if_pos hc']
      exact (leastUpToSpec _ (R * R) m' (preLe R m' (by omega) _ hm') hm').1
    rcases preStep R m hR s k hP with ⟨hP', hno⟩ | ⟨B, _, _, _, hlt⟩
    · exact ⟨fun _ => by rw [ht]; exact ht' m hP',
        fun B hB => absurd ⟨hB, exportWord R hR s k B hB⟩ (hno B)⟩
    · have h3 := ht' _ (hlt (Nat.pos_of_ne_zero hm0))
      exact ⟨fun _ => by rw [ht]; omega, fun _ _ => by rw [ht]; omega⟩
  · have ht : tailIdx R s = (srcWord R s.out).length := by unfold tailIdx; rw [if_neg hc]
    refine ⟨fun hne => ?_, fun B hB => ?_⟩
    · rcases freeWord R hR s k hc hne with hw | ⟨hc', hlen⟩
      · rw [ht, ← hw]; exact hle'
      · have := tailIdxSeg R (by omega) _ (Or.inl hc')
        rw [ht]; omega
    · have hw := congrArg List.length (exportWord R hR s k B hB)
      simp only [List.length_cons] at hw
      rw [ht]; omega

/-! ### The head of the source block -/

/-- Weight of source cell `j` as the head: empty `2R`, `U` odd, `D` even, decreasing towards
the port. Consumer: `headMin`. -/
def headW (R j : Nat) : BankRepairDigitOutSh → Nat
  | .E => 2 * R
  | .U => 2 * (R - 1 - j) + 1
  | .D _ => 2 * (R - 1 - j)

/-- The least head weight of cells `k - 1, ..., 0`. Consumer: `headPot`. -/
def headMin (R : Nat) (out : Nat → BankRepairDigitOutSh) : Nat → Nat
  | 0 => 2 * R
  | k + 1 => min (headW R k (out k)) (headMin R out k)

/-- **The head potential** of the source block: the weight of its rightmost occupied cell
(`2R` if it is empty). Consumer: `tailG`. -/
def headPot (R : Nat) (s : CohortLane) : Nat := headMin R s.out R

/-- Consumer: `headStep`, `headDrop`. -/
theorem headMinLe (R : Nat) (out : Nat → BankRepairDigitOutSh) :
    ∀ k j, j < k → headMin R out k ≤ headW R j (out j)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, j, h => by
      simp only [headMin]
      by_cases hj : j = k
      · subst hj; exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _) (headMinLe R out k j (by omega))

/-- Consumer: `headStep`, `headDrop`. -/
theorem headMinAtt (R : Nat) (out : Nat → BankRepairDigitOutSh) :
    ∀ k, headMin R out k = 2 * R ∨ ∃ j, j < k ∧ headMin R out k = headW R j (out j)
  | 0 => Or.inl rfl
  | k + 1 => by
      simp only [headMin]
      rw [Nat.min_def]
      split
      · exact Or.inr ⟨k, by omega, rfl⟩
      · rcases headMinAtt R out k with h | ⟨j, hj, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, h⟩

/-- Consumer: `tailGLe`, `headStep`. -/
theorem headMinLeTwiceR (R : Nat) (out : Nat → BankRepairDigitOutSh) : ∀ k, headMin R out k ≤ 2 * R
  | 0 => Nat.le_refl _
  | k + 1 => Nat.le_trans (Nat.min_le_right _ _) (headMinLeTwiceR R out k)

/-- **Every letter that exports nothing leaves some source cell whose head weight is at most
that of the old head.** Consumer: `headStep`. -/
theorem headCell (R : Nat) (_hR : 2 ≤ R) (s : CohortLane) (k j0 : Nat) (hj0 : j0 < R)
    (hne : ∀ B, ¬ Exported R s k B) :
    ∃ j, j < R ∧ headW R j ((cohortEdge R s k).out j) ≤ headW R j0 (s.out j0) := by
  by_cases h1 : k + 1 < R
  · have hout : (cohortEdge R s k).out =
        cohortUpd (cohortUpd s.out k (bankRepairDigitPipeStep (decide (k = 0)) (s.out k)
          (s.out (k + 1))).1) (k + 1)
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
      unfold cohortEdge; rw [if_pos h1]
    have ek : (cohortEdge R s k).out k =
        (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).1 := by
      rw [hout]; simp [cohortUpd]
    have ek1 : (cohortEdge R s k).out (k + 1) =
        (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
      rw [hout]; simp [cohortUpd]
    by_cases hjk : j0 = k
    · subst hjk
      rcases hx : s.out j0 with _ | _ | ⟨T⟩
      · refine ⟨j0, hj0, ?_⟩
        rw [ek, hx]
        cases decide (j0 = 0) <;> simp [bankRepairDigitPipeStep, headW] <;> omega
      · refine ⟨j0, hj0, ?_⟩
        rw [ek, hx]
        simp [bankRepairDigitPipeStep, headW] <;> omega
      · rcases hy : s.out (j0 + 1) with _ | _ | ⟨T'⟩
        · refine ⟨j0 + 1, h1, ?_⟩
          rw [ek1, hx, hy]
          simp [bankRepairDigitPipeStep, headW]
          omega
        all_goals
          refine ⟨j0, hj0, ?_⟩
          rw [ek, hx, hy]
          simp [bankRepairDigitPipeStep, headW]
    · by_cases hjk1 : j0 = k + 1
      · subst hjk1
        refine ⟨k + 1, hj0, ?_⟩
        rw [ek1]
        rcases hx : s.out k with _ | _ | ⟨T⟩ <;> rcases hy : s.out (k + 1) with _ | _ | ⟨T'⟩ <;>
          cases decide (k = 0) <;> simp [bankRepairDigitPipeStep, headW] <;> omega
      · refine ⟨j0, hj0, ?_⟩
        rw [hout]
        simp [cohortUpd, hjk, hjk1]
  · by_cases h2 : k + 1 = R
    · have hout : (cohortEdge R s k).out =
          cohortUpd s.out k (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1 := by
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
      by_cases hjk : j0 = k
      · subst hjk
        refine ⟨j0, hj0, ?_⟩
        rw [hout]
        simp only [cohortUpd]
        rw [if_pos trivial]
        rcases hx : s.out j0 with _ | _ | ⟨T⟩
        · simp [bankRepairDigitDelStep]
        · simp [bankRepairDigitDelStep, headW] <;> omega
        · rcases hl : s.live (j0 + 1) with _ | _
          · rcases hi : s.inp (j0 + 1) with _ | _ | _ | _
            · exfalso
              refine hne T ⟨h2, ?_, ?_, ?_, ?_⟩
              · rw [← h2]; exact hi
              · rw [← h2]; exact hl
              · unfold cohortEdge; rw [if_neg h1, if_pos h2]
                show cohortUpd s.inp (j0 + 1) _ R = _
                simp [cohortUpd, hx, hi, hl, h2.symm, bankRepairDigitDelStep]
              · unfold cohortEdge; rw [if_neg h1, if_pos h2]
                show cohortUpd s.live (j0 + 1) _ R = _
                simp [cohortUpd, hx, hi, hl, h2.symm, bankRepairDigitDelStep]
            all_goals simp [bankRepairDigitDelStep]
          · simp [bankRepairDigitDelStep]
      · refine ⟨j0, hj0, ?_⟩
        rw [hout]
        simp [cohortUpd, hjk]
    · have hout : (cohortEdge R s k).out = s.out := by
        unfold cohortEdge; rw [if_neg h1, if_neg h2]
        split
        · rfl
        · split <;> rfl
      exact ⟨j0, hj0, by rw [hout]; exact Nat.le_refl _⟩

/-- **The head potential never rises on a letter that exports nothing.** Consumer:
`tailGStep`. -/
theorem headStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat)
    (hne : ∀ B, ¬ Exported R s k B) : headPot R (cohortEdge R s k) ≤ headPot R s := by
  unfold headPot
  rcases headMinAtt R s.out R with h | ⟨j0, hj0, h⟩
  · rw [h]; exact headMinLeTwiceR R _ R
  · obtain ⟨j, hj, hw⟩ := headCell R hR s k j0 hj0 hne
    rw [h]
    exact Nat.le_trans (headMinLe R _ R j hj) hw

/-- **The head potential drops on the edge of the rightmost occupied source cell, or that edge
exports.** Consumer: `tailEdgeDrop`. -/
theorem headDrop (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (hb : BorderFree R s) :
    ∃ k, k < R ∧ ((∃ B, Exported R s k B) ∨
      headPot R (cohortEdge R s k) + 1 ≤ headPot R s) := by
  obtain ⟨hbi, hbl⟩ := hb
  unfold headPot
  have hcase : headMin R s.out R = 2 * R ∨
      ∃ j0, j0 < R ∧ s.out j0 ≠ .E ∧ headMin R s.out R = headW R j0 (s.out j0) := by
    rcases headMinAtt R s.out R with h | ⟨j0, hj0, h⟩
    · exact Or.inl h
    · by_cases hE : s.out j0 = .E
      · left; rw [h, hE]; rfl
      · exact Or.inr ⟨j0, hj0, hE, h⟩
  rcases hcase with h | ⟨j0, hj0, hE, h⟩
  · -- an empty block: cell `0` opens
    refine ⟨0, by omega, Or.inr ?_⟩
    have h0 : s.out 0 = .E := by
      have hle := headMinLe R s.out R 0 (by omega)
      rw [h] at hle
      rcases hx : s.out 0 with _ | _ | ⟨T⟩
      · rfl
      · rw [hx] at hle; simp [headW] at hle <;> omega
      · rw [hx] at hle; simp [headW] at hle <;> omega
    have hc : (cohortEdge R s 0).out 0 = .U := by
      unfold cohortEdge; rw [if_pos (by omega)]
      simp [cohortUpd, bankRepairDigitPipeStep, h0]
    have hle := headMinLe R (cohortEdge R s 0).out R 0 (by omega)
    rw [hc] at hle
    rw [h]
    simp [headW] at hle
    omega
  · have hfree : ∀ j, j0 < j → j < R → s.out j = .E := by
      intro j hj hjR
      have hle := headMinLe R s.out R j hjR
      rw [h] at hle
      rcases hx : s.out j with _ | _ | ⟨T⟩
      · rfl
      all_goals
        rw [hx] at hle
        rcases hx0 : s.out j0 with _ | _ | ⟨T0⟩
        · exact absurd hx0 hE
        all_goals (rw [hx0] at hle; simp [headW] at hle <;> omega)
    refine ⟨j0, hj0, ?_⟩
    rw [h]
    by_cases h1 : j0 + 1 < R
    · right
      have hout : (cohortEdge R s j0).out =
          cohortUpd (cohortUpd s.out j0 (bankRepairDigitPipeStep (decide (j0 = 0)) (s.out j0)
            (s.out (j0 + 1))).1) (j0 + 1)
            (bankRepairDigitPipeStep (decide (j0 = 0)) (s.out j0) (s.out (j0 + 1))).2 := by
        unfold cohortEdge; rw [if_pos h1]
      have hy := hfree (j0 + 1) (by omega) h1
      rcases hx : s.out j0 with _ | _ | ⟨T⟩
      · exact absurd hx hE
      · have hle := headMinLe R (cohortEdge R s j0).out R j0 hj0
        have ek : (cohortEdge R s j0).out j0 = .D (decide (j0 = 0)) := by
          rw [hout]; simp [cohortUpd, bankRepairDigitPipeStep, hx]
        rw [ek] at hle
        simp [headW] at hle ⊢
        omega
      · have hle := headMinLe R (cohortEdge R s j0).out R (j0 + 1) h1
        have ek : (cohortEdge R s j0).out (j0 + 1) = .D T := by
          rw [hout]; simp [cohortUpd, bankRepairDigitPipeStep, hx, hy]
        rw [ek] at hle
        simp [headW] at hle ⊢
        omega
    · have h2 : j0 + 1 = R := by omega
      have hout : (cohortEdge R s j0).out =
          cohortUpd s.out j0 (bankRepairDigitDelStep (s.out j0) (s.inp (j0 + 1))
            (s.live (j0 + 1))).1 := by
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
      rcases hx : s.out j0 with _ | _ | ⟨T⟩
      · exact absurd hx hE
      · right
        have hle := headMinLe R (cohortEdge R s j0).out R j0 hj0
        have ek : (cohortEdge R s j0).out j0 = .D false := by
          rw [hout]; simp [cohortUpd, bankRepairDigitDelStep, hx]
        rw [ek] at hle
        simp [headW] at hle ⊢
        omega
      · left
        refine ⟨T, h2, hbi, hbl, ?_, ?_⟩
        · unfold cohortEdge; rw [if_neg h1, if_pos h2]
          show cohortUpd s.inp (j0 + 1) _ R = _
          rw [h2]
          simp [cohortUpd, hx, hbi, hbl, bankRepairDigitDelStep]
        · unfold cohortEdge; rw [if_neg h1, if_pos h2]
          show cohortUpd s.live (j0 + 1) _ R = _
          rw [h2]
          simp [cohortUpd, hx, hbi, hbl, bankRepairDigitDelStep]

/-! ### The free border -/

/-- An export needs a free border. Consumer: `tailEdgeMono`, `tailEdgeDrop`. -/
theorem exportedBorder (R : Nat) (s : CohortLane) (k : Nat) (B : Bool)
    (h : Exported R s k B) : BorderFree R s :=
  ⟨h.2.1, h.2.2.1⟩

/-- **A free border stays free until an export.** Consumer: `tailGStep`. -/
theorem borderKeep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (h : BorderFree R s)
    (hne : ∀ B, ¬ Exported R s k B) : BorderFree R (cohortEdge R s k) := by
  obtain ⟨hi, hl⟩ := h
  by_cases h1 : k + 1 < R
  · have hi' : (cohortEdge R s k).inp = s.inp := by unfold cohortEdge; simp [h1]
    have hl' : (cohortEdge R s k).live = s.live := by unfold cohortEdge; simp [h1]
    exact ⟨by rw [hi']; exact hi, by rw [hl']; exact hl⟩
  · by_cases h2 : k + 1 = R
    · have hinp : (cohortEdge R s k).inp R =
          (bankRepairDigitDelStep (s.out k) (s.inp R) (s.live R)).2.1 := by
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
        show cohortUpd s.inp (k + 1) _ R = _
        simp [cohortUpd, h2]
      have hlive : (cohortEdge R s k).live R =
          (bankRepairDigitDelStep (s.out k) (s.inp R) (s.live R)).2.2 := by
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
        show cohortUpd s.live (k + 1) _ R = _
        simp [cohortUpd, h2]
      rcases hx : s.out k with _ | _ | ⟨T⟩
      · exact ⟨by simp [hinp, hx, hi, hl, bankRepairDigitDelStep],
          by simp [hlive, hx, hi, hl, bankRepairDigitDelStep]⟩
      · exact ⟨by simp [hinp, hx, hi, hl, bankRepairDigitDelStep],
          by simp [hlive, hx, hi, hl, bankRepairDigitDelStep]⟩
      · exfalso
        exact hne T ⟨h2, hi, hl, by simp [hinp, hx, hi, hl, bankRepairDigitDelStep],
          by simp [hlive, hx, hi, hl, bankRepairDigitDelStep]⟩
    · by_cases h3 : k + 1 < 2 * R
      · unfold cohortEdge
        rw [if_neg h1, if_neg h2, if_pos h3]
        by_cases hk : k = R
        · subst hk
          refine ⟨?_, ?_⟩
          · show cohortUpd (cohortUpd s.inp k _) (k + 1) _ k = _
            cases hk1 : s.live (k + 1) <;> simp [cohortUpd, hi, hl, hk1, bankRepairDigitFinStep]
          · show cohortUpd (cohortUpd s.live k _) (k + 1) _ k = _
            cases hk1 : s.live (k + 1) <;> simp [cohortUpd, hi, hl, hk1, bankRepairDigitFinStep]
        · refine ⟨?_, ?_⟩
          · show cohortUpd (cohortUpd s.inp k _) (k + 1) _ R = _
            simp [cohortUpd, show R ≠ k + 1 by omega, show R ≠ k by omega, hi]
          · show cohortUpd (cohortUpd s.live k _) (k + 1) _ R = _
            simp [cohortUpd, show R ≠ k + 1 by omega, show R ≠ k by omega, hl]
      · by_cases h4 : k + 1 = 2 * R
        · unfold cohortEdge
          rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          refine ⟨?_, ?_⟩
          · show cohortUpd s.inp k _ R = _
            simp [cohortUpd, show R ≠ k by omega, hi]
          · show cohortUpd s.live k _ R = _
            simp [cohortUpd, show R ≠ k by omega, hl]
        · unfold cohortEdge
          rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          exact ⟨hi, hl⟩

/-! ### The potential -/

/-- The weight of one owed export. Consumer: `tailPot`. -/
def tailW (R : Nat) : Nat := 2 * (R * R) + 4 * R + 2

/-- The within-export part: the head potential at a free border, the release weight above
`2R + 1` otherwise. Consumer: `tailPot`. -/
noncomputable def tailG (R : Nat) (s : CohortLane) : Nat :=
  if BorderFree R s then headPot R s else 2 * R + 1 + releaseWeight R s

/-- **The distinguished-tail potential.** Consumer: `tailMoment`. -/
noncomputable def tailPot (R : Nat) (s : CohortLane) : Nat := tailIdx R s * tailW R + tailG R s

/-- **The budget of the distinguished-tail phase**, `(R² + 1) · 2(R+1)²`. Consumer:
`widthTailMoment`, the per-pair moment before the first attempt. -/
def tailBudget (R : Nat) : Nat := (R * R + 1) * tailW R

/-- **The distinguished-tail budget is within one pair clock**: `tailBudget R ≤ C_R`, leaving
`2 C_R` of the allowance `3 C_R` for the stages after the distinguished export. Consumer: the
pre-attempt stage obligation (`BankPairStageW`). -/
theorem tailBudgetLe (R : Nat) : tailBudget R ≤ bankRepairDigitPairClock R := by
  have h4 : R ^ 4 = R * R * (R * R) := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]
  have h3 : R ^ 3 = R * R * R := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  have h2 : R ^ 2 = R * R := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  unfold tailBudget tailW bankRepairDigitPairClock
  rw [h4, h3, h2]
  have hlin : (R * R + 1) * (2 * (R * R) + 4 * R + 2) =
      2 * (R * R * (R * R)) + 4 * (R * R * R) + 4 * (R * R) + 4 * R + 2 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm (R * R) 2 (R * R),
      Nat.mul_left_comm (R * R) 4 R]
    omega
  rw [hlin]
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0; simp
  · have hc : R * R ≤ R * R * R := Nat.le_mul_of_pos_right (R * R) hpos
    omega

/-- Consumer: `tailExportDrop`, `tailPotLe`. -/
theorem tailGLe (R : Nat) (s : CohortLane) : tailG R s + 1 ≤ tailW R := by
  have hq : R * (2 * R + 2) = 2 * (R * R) + 2 * R := by
    rw [Nat.mul_add, Nat.mul_left_comm R 2 R]; omega
  have h1 := releaseWeightLe R s
  have h2 := headMinLeTwiceR R s.out R
  unfold tailG tailW headPot
  split <;> omega

/-- Consumer: `tailMoment`, `widthTailMoment`. -/
theorem tailPotLe (R : Nat) (hR : 1 ≤ R) (s : CohortLane) : tailPot R s ≤ tailBudget R := by
  have h1 : tailIdx R s * tailW R ≤ R * R * tailW R :=
    Nat.mul_le_mul_right _ (Nat.le_trans (tailIdxLe R hR s) (srcWordLen R hR s.out))
  have h2 : (R * R + 1) * tailW R = R * R * tailW R + tailW R := Nat.succ_mul _ _
  have h3 := tailGLe R s
  unfold tailPot tailBudget
  omega

/-- **The within-export part never rises on a letter that exports nothing.** Consumer:
`tailEdgeMono`. -/
theorem tailGStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat)
    (hne : ∀ B, ¬ Exported R s k B) : tailG R (cohortEdge R s k) ≤ tailG R s := by
  unfold tailG
  by_cases hb : BorderFree R s
  · rw [if_pos (borderKeep R hR s k hb hne), if_pos hb]
    exact headStep R hR s k hne
  · rw [if_neg hb]
    by_cases hb' : BorderFree R (cohortEdge R s k)
    · rw [if_pos hb']
      have := headMinLeTwiceR R (cohortEdge R s k).out R
      unfold headPot
      omega
    · rw [if_neg hb']
      have := edgeMono R k s hR hb
      omega

/-- **An export before the alignment lowers the potential.** Consumer: `tailEdgeMono`,
`tailEdgeDrop`. -/
theorem tailExportDrop (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (B : Bool)
    (hna : ¬ SrcAligned R s) (hB : Exported R s k B) :
    tailPot R (cohortEdge R s k) + 1 ≤ tailPot R s := by
  have h1 := (tailIdxStep R hR s k hna).2 B hB
  have h2 : (tailIdx R (cohortEdge R s k) + 1) * tailW R ≤ tailIdx R s * tailW R :=
    Nat.mul_le_mul_right _ h1
  have h3 : (tailIdx R (cohortEdge R s k) + 1) * tailW R =
      tailIdx R (cohortEdge R s k) * tailW R + tailW R := Nat.succ_mul _ _
  have h4 := tailGLe R (cohortEdge R s k)
  unfold tailPot
  omega

/-- **No letter raises the potential before the alignment.** Consumer: `tailMoment`. -/
theorem tailEdgeMono (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (hna : ¬ SrcAligned R s)
    (k : Nat) : tailPot R (cohortEdge R s k) ≤ tailPot R s := by
  by_cases hex : ∃ B, Exported R s k B
  · obtain ⟨B, hB⟩ := hex
    have := tailExportDrop R hR s k B hna hB
    omega
  · have hne : ∀ B, ¬ Exported R s k B := fun B hB => hex ⟨B, hB⟩
    have h1 := Nat.mul_le_mul_right (tailW R) ((tailIdxStep R hR s k hna).1 hne)
    have h2 := tailGStep R hR s k hne
    unfold tailPot
    omega

/-- **A nominated edge lowers the potential before the alignment**: the release edge
(`edgeDrop`) while the border is occupied, the head edge (`headDrop`) while it is free.
Consumer: `tailMoment`. -/
theorem tailEdgeDrop (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (hna : ¬ SrcAligned R s) :
    ∃ k, k < 2 * R ∧ tailPot R (cohortEdge R s k) + 1 ≤ tailPot R s := by
  by_cases hb : BorderFree R s
  · obtain ⟨k, hk, hd⟩ := headDrop R hR s hb
    refine ⟨k, by omega, ?_⟩
    by_cases hex : ∃ B, Exported R s k B
    · obtain ⟨B, hB⟩ := hex
      exact tailExportDrop R hR s k B hna hB
    · have hne : ∀ B, ¬ Exported R s k B := fun B hB => hex ⟨B, hB⟩
      rcases hd with ⟨B, hB⟩ | hd
      · exact absurd hB (hne B)
      · have h1 := Nat.mul_le_mul_right (tailW R) ((tailIdxStep R hR s k hna).1 hne)
        have hb' := borderKeep R hR s k hb hne
        unfold tailPot tailG
        rw [if_pos hb, if_pos hb']
        omega
  · obtain ⟨k, hk, hd⟩ := edgeDrop R s hR hb
    refine ⟨k, hk, ?_⟩
    have hne : ∀ B, ¬ Exported R s k B := fun B hB => hb (exportedBorder R s k B hB)
    have h1 := Nat.mul_le_mul_right (tailW R) ((tailIdxStep R hR s k hna).1 hne)
    have h2 : tailG R (cohortEdge R s k) ≤ 2 * R + 1 + releaseWeight R (cohortEdge R s k) := by
      unfold tailG
      split
      · have := headMinLeTwiceR R (cohortEdge R s k).out R
        unfold headPot
        omega
      · exact Nat.le_refl _
    have h3 : tailG R s = 2 * R + 1 + releaseWeight R s := by
      unfold tailG; rw [if_neg hb]
    unfold tailPot
    omega

/-! ### The moment bounds -/

/-- **The distinguished-tail phase in moment form, on the lane.** From every lane state the
source block is aligned with `E[z^T] ≤ w^{tailPot}`. Consumer: `widthTailMoment`. -/
theorem tailMoment {n : Nat} (R : Nat) (hR : 2 ≤ R) (hn : 1 ≤ n) (N : Nat) (hN : n ≤ N)
    (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) (s : CohortLane) :
    MomentBoundQ (releaseNext R edgeOf) (SrcAligned R) N (N ^ tailPot R s)
      ((N - n) ^ tailPot R s) s := by
  have hex : ∀ s : CohortLane, ∃ e : Fin n, ¬ SrcAligned R s →
      tailPot R (releaseNext R edgeOf s e) + 1 ≤ tailPot R s := by
    intro s
    by_cases ha : SrcAligned R s
    · exact ⟨site 0, fun h => absurd ha h⟩
    · obtain ⟨k, hk, hd⟩ := tailEdgeDrop R hR s ha
      refine ⟨site k, fun _ => ?_⟩
      show tailPot R (cohortLaneStep R s (edgeOf (site k))) + 1 ≤ tailPot R s
      rw [hedge k hk]
      exact hd
  exact momentOfPotential (releaseNext R edgeOf) (SrcAligned R) N (tailPot R)
    (fun s => Classical.choose (hex s)) hn hN
    (fun s hs => Classical.choose_spec (hex s) hs)
    (fun s hs e => by
      show tailPot R (cohortLaneStep R s (edgeOf e)) ≤ tailPot R s
      cases edgeOf e with
      | none => exact Nat.le_refl _
      | some k => exact tailEdgeMono R hR s hs k) s

section Coupled

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
    WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (N : Nat) (hN : n < N)

include hfix hn hsrc hend hN

/-- **The distinguished-tail phase at a digit reference.** From every layout state of the
coupled reference x audit chain the source block of the pair is aligned (`SrcAligned`, begun at
the distinguished export) with `E[z^T] ≤ w^{tailBudget R}`, `w = N/(N-n)`, uniformly over source
values and the audit; all releases before the distinguished export are included. Consumer: the
per-pair moment before the first attempt (`WidthStrictPairMoment`, BANK and SMALL). -/
theorem widthTailMoment (hR : 2 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => SrcAligned R (widthLaneOfState ref root lane src R y)) N
      (N ^ tailBudget R) ((N - n) ^ tailBudget R) x :=
  widthLaneMoment ref hfix hn root lane src R hR hsrc hend (SrcAligned R) N _ _ hN
    (tailPotLe R (by omega) _) x hx
    (tailMoment R hR (by omega) N (Nat.le_of_lt hN) (fun k => digitSite ring root (src + k))
      (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk) _)

end Coupled

/-- **Port check**: the BANK instance of `widthTailMoment` on the BANK lane projection.
Consumer: none in the chain; it checks the port. -/
theorem bankTailMomentCheck {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => SrcAligned R (L3.DigitPacketTransport.laneOfState ring hbank root lane src R y))
      N (N ^ tailBudget R) ((N - n) ^ tailBudget R) x :=
  widthTailMoment (bankWidthDigitReference ring hn hbank) (fun _ _ h => h.2) hn root lane src R
    hsrc hend N hN hR x hx

end L3.WidthPacketMomentTail

#print axioms L3.WidthPacketMomentTail.tailIdxStep
#print axioms L3.WidthPacketMomentTail.headDrop
#print axioms L3.WidthPacketMomentTail.borderKeep
#print axioms L3.WidthPacketMomentTail.tailBudgetLe
#print axioms L3.WidthPacketMomentTail.tailMoment
#print axioms L3.WidthPacketMomentTail.widthTailMoment
#print axioms L3.WidthPacketMomentTail.bankTailMomentCheck

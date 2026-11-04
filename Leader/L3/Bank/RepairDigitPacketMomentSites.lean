import Leader.L3.Bank.RepairDigitPacketMomentAlign

/-!
# Lemma e-packet, I1: the sampling positions of the source exports

repair.tex, Lemma e-packet: "After this tail exports, exclusion and its rearms force each
subsequent group's export origins to be `r-1, …, 0`."

The position version of `L3.PacketMomentAlign.Align`. A position label `σ j` rides with each data
packet of the source (the source cell where its operand was sampled): a read of `U` at cell `j`
labels the new packet `j`; a hop carries the label; the delivery hands the label of cell `R - 1`
to the border cell `R` (`sigStep`, the label rows of the ghost rows `ghostPipe` / `ghostDel`).
Labels are `Option Nat`: `none` marks a packet whose sampling position is not known (an inherited
packet present before the first read of the window); `SitePre` and `SiteAlign` only constrain the
labels the word lists, all of which are `some` once the source has read.

The **position word** (`siteWord`, oldest export first) lists the labels the source still owes:
a packet owes its own label and, if it is a tail at cell `j`, the rearms it leaves at cells
`R - 1, …, max j 1` (`dn R (max j 1)`); an unread `U` at cell `j ≥ 1` owes `j`, at cell `0` a tail
and its rearms `0, R - 1, …, 1` (`sb R`). Every lane letter keeps the word, appends one group
`sb R` (a tail leaving cell `0`), or exports its first label into the border (`siteStep`).

`SiteAlign a`: the word is `a, a - 1, …, 1` followed by whole groups `0, R - 1, …, 1`. It is kept
by every letter, and **every export carries the label `a`**, after which the index is
`a - 1` (or `R - 1` after the tail `a = 0`) (`siteAlignStep`). `SitePre`: any word ending in a
group (every state with `CZero` and a labelled tail on cell `0`); `sitePreStep`: the prefix
shrinks, and the export at the empty prefix carries label `0` and leaves `SiteAlign (R - 1)`.
-/

namespace L3.PacketMomentSites

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.PacketMomentAlign

/-! ### Descending runs -/

/-- `m - 1, m - 2, …, j`. Consumer: `sw`. -/
def dn (m j : Nat) : List Nat := (List.range (m - j)).map (fun i => m - 1 - i)

/-- Consumer: `pipeSiteInner`. -/
theorem dnSucc (m j : Nat) (h : j < m) : dn m j = dn m (j + 1) ++ [j] := by
  unfold dn
  rw [show m - j = (m - (j + 1)) + 1 by omega, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  congr 2
  omega

/-- Consumer: `siteAlignStep`. -/
theorem dnHead (a : Nat) (h : 1 ≤ a) : dn (a + 1) 1 = a :: dn a 1 := by
  unfold dn
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  rw [show c + 1 + 1 - 1 = c + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.cons.injEq]
  refine ⟨by omega, ?_⟩
  rw [show c + 1 - 1 = c by omega]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  omega

/-- Consumer: `siteAlignStep`. -/
theorem dnOne : dn 1 1 = [] := rfl

/-- The labels of a descending run are at least its bottom. Consumer: `zeroNotDn`. -/
theorem dnGe (m j x : Nat) (h : x ∈ dn m j) : j ≤ x ∧ x < m := by
  unfold dn at h
  simp only [List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  omega

/-- Consumer: `siteAlignStep`. -/
theorem zeroNotDnSome (m : Nat) : some 0 ∉ (dn m 1).map some := by
  intro h
  simp only [List.mem_map, Option.some.injEq] at h
  obtain ⟨x, hx, rfl⟩ := h
  have := dnGe m 1 0 hx
  omega

/-! ### The position word -/

/-- One group of export labels: the tail sampled at cell `0`, then the rearms `R - 1, …, 1`.
Consumer: `sgrp`. -/
def sb (R : Nat) : List (Option Nat) := some 0 :: (dn R 1).map some

/-- The labels owed by one source cell with label `v`. Consumer: `sFrom`. -/
def sw (R j : Nat) : BankRepairDigitOutSh → Option Nat → List (Option Nat)
  | .E, _ => []
  | .U, _ => if j = 0 then sb R else [some j]
  | .D false, v => [v]
  | .D true, v => v :: (dn R (if j = 0 then 1 else j)).map some

/-- The labels owed by cells `k - 1, …, 0`. Consumer: `siteWord`. -/
def sFrom (R : Nat) (out : Nat → BankRepairDigitOutSh) (σ : Nat → Option Nat) : Nat → List (Option Nat)
  | 0 => []
  | k + 1 => sw R k (out k) (σ k) ++ sFrom R out σ k

/-- The labels owed by cells `lo + m - 1, …, lo`. Consumer: `siteSplit`. -/
def sSeg (R : Nat) (out : Nat → BankRepairDigitOutSh) (σ : Nat → Option Nat) (lo : Nat) :
    Nat → List (Option Nat)
  | 0 => []
  | m + 1 => sw R (lo + m) (out (lo + m)) (σ (lo + m)) ++ sSeg R out σ lo m

/-- **The position word of the source block**, oldest export first. Consumer: `siteStep`. -/
def siteWord (R : Nat) (out : Nat → BankRepairDigitOutSh) (σ : Nat → Option Nat) : List (Option Nat) :=
  sFrom R out σ R

theorem sFromAdd (R : Nat) (out : Nat → BankRepairDigitOutSh) (σ : Nat → Option Nat) (lo : Nat) :
    ∀ m, sFrom R out σ (lo + m) = sSeg R out σ lo m ++ sFrom R out σ lo
  | 0 => by simp [sSeg]
  | m + 1 => by
      show sw R (lo + m) (out (lo + m)) (σ (lo + m)) ++ sFrom R out σ (lo + m) = _
      rw [sFromAdd R out σ lo m]
      simp [sSeg, List.append_assoc]

theorem sFromCongr (R : Nat) (out out' : Nat → BankRepairDigitOutSh) (σ σ' : Nat → Option Nat) :
    ∀ k, (∀ j, j < k → out' j = out j ∧ σ' j = σ j) → sFrom R out' σ' k = sFrom R out σ k
  | 0 => fun _ => rfl
  | k + 1 => fun h => by
      simp only [sFrom]
      rw [(h k (by omega)).1, (h k (by omega)).2,
        sFromCongr R out out' σ σ' k (fun j hj => h j (by omega))]

theorem sSegCongr (R : Nat) (out out' : Nat → BankRepairDigitOutSh) (σ σ' : Nat → Option Nat)
    (lo : Nat) : ∀ m, (∀ j, lo ≤ j → j < lo + m → out' j = out j ∧ σ' j = σ j) →
      sSeg R out' σ' lo m = sSeg R out σ lo m
  | 0 => fun _ => rfl
  | m + 1 => fun h => by
      simp only [sSeg]
      rw [(h (lo + m) (by omega) (by omega)).1, (h (lo + m) (by omega) (by omega)).2,
        sSegCongr R out out' σ σ' lo m (fun j h1 h2 => h j h1 (by omega))]

theorem siteSplit (R : Nat) (out : Nat → BankRepairDigitOutSh) (σ : Nat → Option Nat) (k : Nat)
    (hk : k + 2 ≤ R) :
    siteWord R out σ = sSeg R out σ (k + 2) (R - (k + 2)) ++
      (sw R (k + 1) (out (k + 1)) (σ (k + 1)) ++ (sw R k (out k) (σ k) ++ sFrom R out σ k)) := by
  have h := sFromAdd R out σ (k + 2) (R - (k + 2))
  rw [show k + 2 + (R - (k + 2)) = R by omega] at h
  unfold siteWord
  rw [h]
  rfl

theorem sitePort (R : Nat) (out : Nat → BankRepairDigitOutSh) (σ : Nat → Option Nat) (hR : 1 ≤ R) :
    siteWord R out σ = sw R (R - 1) (out (R - 1)) (σ (R - 1)) ++ sFrom R out σ (R - 1) := by
  unfold siteWord
  obtain ⟨m, rfl⟩ : ∃ m, R = m + 1 := ⟨R - 1, by omega⟩
  rfl

/-! ### The label rows -/

/-- Labels across a Pipe edge: a read labels the new packet with its cell, a hop carries the
label (the ghost row `ghostPipe`). Consumer: `sigStep`. -/
def sigPipe (k : Nat) (x y : BankRepairDigitOutSh) (σ : Nat → Option Nat) : Nat → Option Nat :=
  match x, y with
  | .D _, .E => cohortUpd σ (k + 1) (σ k)
  | .U, _ => cohortUpd σ k (some k)
  | _, _ => σ

/-- Labels across the delivery edge: a read labels the new packet; an accepted export hands the
label to the border (the ghost row `ghostDel`). Consumer: `sigStep`. -/
def sigDel (k : Nat) (x : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (σ : Nat → Option Nat) : Nat → Option Nat :=
  match x, ky, iy with
  | .U, _, _ => cohortUpd σ k (some k)
  | .D _, false, .E => cohortUpd σ (k + 1) (σ k)
  | _, _, _ => σ

/-- Labels across an input-motion edge: a moving packet carries its label into an empty cell.
Consumer: `sigStep`. -/
def sigFin (k : Nat) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh) (ky : Bool)
    (σ : Nat → Option Nat) : Nat → Option Nat :=
  match ix, kx, iy, ky with
  | .P _, false, .E, false => cohortUpd σ (k + 1) (σ k)
  | _, _, _, _ => σ

/-- **The label step of one lane letter.** Consumer: `siteStep`, the pending join. -/
def sigStep (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat) : Nat → Option Nat :=
  if k + 1 < R then sigPipe k (s.out k) (s.out (k + 1)) σ
  else if k + 1 = R then sigDel k (s.out k) (s.inp (k + 1)) (s.live (k + 1)) σ
  else if k + 1 < 2 * R then sigFin k (s.inp k) (s.live k) (s.inp (k + 1)) (s.live (k + 1)) σ
  else σ

theorem sigPipeOther (k : Nat) (x y : BankRepairDigitOutSh) (σ : Nat → Option Nat) (j : Nat)
    (h1 : j ≠ k) (h2 : j ≠ k + 1) : sigPipe k x y σ j = σ j := by
  unfold sigPipe
  rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> simp [cohortUpd, h1, h2]

theorem sigDelOther (k : Nat) (x : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (σ : Nat → Option Nat) (j : Nat) (h1 : j ≠ k) (h2 : j ≠ k + 1) : sigDel k x iy ky σ j = σ j := by
  unfold sigDel
  rcases x with _ | _ | _ <;> cases ky <;> rcases iy with _ | _ | _ | _ <;>
    simp [cohortUpd, h1, h2]

theorem sigFinLow (k : Nat) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (σ : Nat → Option Nat) (j : Nat) (h : j ≠ k + 1) : sigFin k ix kx iy ky σ j = σ j := by
  unfold sigFin
  rcases ix with _ | _ | _ | _ <;> cases kx <;> rcases iy with _ | _ | _ | _ <;> cases ky <;>
    simp [cohortUpd, h]

/-- An internal edge away from cell `0` keeps the labels owed by its two cells. Consumer:
`siteStep`. -/
theorem pipeSiteInner (R k : Nat) (hk : 1 ≤ k) (hk1 : k + 1 < R) (x y : BankRepairDigitOutSh)
    (σ : Nat → Option Nat) :
    sw R (k + 1) (bankRepairDigitPipeStep false x y).2 (sigPipe k x y σ (k + 1)) ++
        sw R k (bankRepairDigitPipeStep false x y).1 (sigPipe k x y σ k) =
      sw R (k + 1) y (σ (k + 1)) ++ sw R k x (σ k) := by
  have h0 : k ≠ 0 := by omega
  have h1 : k + 1 ≠ 0 := by omega
  have hd := dnSucc R k (by omega)
  rcases x with _ | _ | ⟨_ | _⟩ <;> rcases y with _ | _ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitPipeStep, sw, sigPipe, cohortUpd, h0, h1, hd]

/-- The edge at cell `0`: a tail leaving cell `0` appends one group. Consumer: `siteStep`. -/
theorem pipeSiteZero (R : Nat) (x y : BankRepairDigitOutSh) (σ : Nat → Option Nat)
    (hx : x = .U ∨ x = .D true) :
    sw R 1 (bankRepairDigitPipeStep true x y).2 (sigPipe 0 x y σ 1) ++
        sw R 0 (bankRepairDigitPipeStep true x y).1 (sigPipe 0 x y σ 0) =
      sw R 1 y (σ 1) ++ sw R 0 x (σ 0) ++ (if x = .D true ∧ y = .E then sb R else []) := by
  rcases hx with rfl | rfl
  · simp [bankRepairDigitPipeStep, sw, sigPipe, cohortUpd, sb]
  · rcases y with _ | _ | ⟨_ | _⟩ <;> simp [bankRepairDigitPipeStep, sw, sigPipe, cohortUpd, sb]

/-- The delivery edge: an export removes the first owed label and hands it to the border.
Consumer: `siteStep`. -/
theorem portSite (R : Nat) (hR : 2 ≤ R) (x : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) (σ : Nat → Option Nat) :
    (∃ B, x = .D B ∧ ky = false ∧ iy = .E ∧
        sigDel (R - 1) x iy ky σ R = σ (R - 1) ∧
        sw R (R - 1) x (σ (R - 1)) = σ (R - 1) ::
          sw R (R - 1) (bankRepairDigitDelStep x iy ky).1 (sigDel (R - 1) x iy ky σ (R - 1))) ∨
      sw R (R - 1) (bankRepairDigitDelStep x iy ky).1 (sigDel (R - 1) x iy ky σ (R - 1)) =
        sw R (R - 1) x (σ (R - 1)) ∧ (x = .D false ∨ x = .D true → ky = true ∨ iy ≠ .E) := by
  have h0 : R - 1 ≠ 0 := by omega
  have hR1 : R - 1 + 1 = R := by omega
  have hdn : dn R (R - 1) = [R - 1] := by
    unfold dn; rw [show R - (R - 1) = 1 by omega]; rfl
  rcases x with _ | _ | ⟨_ | _⟩
  · right; cases ky <;> simp [bankRepairDigitDelStep, sw, sigDel]
  · right; cases ky <;> rcases iy with _ | _ | _ | _ <;>
      simp [bankRepairDigitDelStep, sw, sigDel, cohortUpd, h0]
  · cases ky
    · cases iy
      · left
        exact ⟨false, rfl, rfl, rfl, by simp [sigDel, cohortUpd, hR1],
          by simp [bankRepairDigitDelStep, sw, sigDel, cohortUpd]⟩
      all_goals (right; simp [bankRepairDigitDelStep, sw, sigDel])
    · right; simp [bankRepairDigitDelStep, sw, sigDel]
  · cases ky
    · cases iy
      · left
        exact ⟨true, rfl, rfl, rfl, by simp [sigDel, cohortUpd, hR1],
          by simp [bankRepairDigitDelStep, sw, sigDel, cohortUpd, h0, hdn]⟩
      all_goals (right; simp [bankRepairDigitDelStep, sw, sigDel])
    · right; simp [bankRepairDigitDelStep, sw, sigDel]

/-! ### One lane letter -/

/-- **One lane letter on the position word.** From a `CZero` state the word is unchanged, or
one group is appended (a tail leaving cell `0`), or the first label is exported and handed to the
border cell. Consumer: `siteAlignStep`, `sitePreStep`. -/
theorem siteStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (h : CZero s.out) :
    (siteWord R (cohortEdge R s k).out (sigStep R s σ k) = siteWord R s.out σ ∧
        ∀ B, ¬ Exported R s k B) ∨
      (k = 0 ∧ siteWord R (cohortEdge R s k).out (sigStep R s σ k) =
        siteWord R s.out σ ++ sb R ∧ ∀ B, ¬ Exported R s k B) ∨
      (∃ B, Exported R s k B ∧
        siteWord R s.out σ = σ (R - 1) :: siteWord R (cohortEdge R s k).out (sigStep R s σ k) ∧
        sigStep R s σ k R = σ (R - 1)) := by
  by_cases h1 : k + 1 < R
  · have hsig : sigStep R s σ k = sigPipe k (s.out k) (s.out (k + 1)) σ := by
      unfold sigStep; rw [if_pos h1]
    have hout : (cohortEdge R s k).out =
        cohortUpd (cohortUpd s.out k (bankRepairDigitPipeStep (decide (k = 0)) (s.out k)
          (s.out (k + 1))).1) (k + 1)
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
      unfold cohortEdge; rw [if_pos h1]
    rw [hsig]
    have hsplit' := siteSplit R (cohortEdge R s k).out (sigPipe k (s.out k) (s.out (k + 1)) σ) k
      (by omega)
    have hsplit := siteSplit R s.out σ k (by omega)
    have hseg : sSeg R (cohortEdge R s k).out (sigPipe k (s.out k) (s.out (k + 1)) σ) (k + 2)
        (R - (k + 2)) = sSeg R s.out σ (k + 2) (R - (k + 2)) :=
      sSegCongr R _ _ _ _ _ _ (fun j hj _ => ⟨by
        rw [hout]; simp [cohortUpd, show j ≠ k by omega, show j ≠ k + 1 by omega],
        sigPipeOther k _ _ σ j (by omega) (by omega)⟩)
    have hlow : sFrom R (cohortEdge R s k).out (sigPipe k (s.out k) (s.out (k + 1)) σ) k =
        sFrom R s.out σ k :=
      sFromCongr R _ _ _ _ _ (fun j hj => ⟨by
        rw [hout]; simp [cohortUpd, show j ≠ k by omega, show j ≠ k + 1 by omega],
        sigPipeOther k _ _ σ j (by omega) (by omega)⟩)
    have ek1 : (cohortEdge R s k).out (k + 1) =
        (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
      rw [hout]; simp [cohortUpd]
    have ek : (cohortEdge R s k).out k =
        (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).1 := by
      rw [hout]; simp [cohortUpd]
    rw [hsplit', hsplit, hseg, hlow, ek1, ek]
    by_cases hk : k = 0
    · subst hk
      have hz := pipeSiteZero R (s.out 0) (s.out 1) σ h
      have e0 : decide ((0 : Nat) = 0) = true := rfl
      rw [e0]
      have hw0 : sFrom R s.out σ 0 = [] := rfl
      have hw0' : sFrom R (cohortEdge R s 0).out (sigPipe 0 (s.out 0) (s.out (0 + 1)) σ) 0 = [] :=
        rfl
      rw [hw0]
      by_cases hc : s.out 0 = .D true ∧ s.out (0 + 1) = .E
      · right; left
        refine ⟨rfl, ?_, fun B hB => by have := hB.1; omega⟩
        simp only [List.append_nil] at hz ⊢
        rw [show (0 : Nat) + 1 = 1 from rfl, hz, if_pos hc]
        simp [List.append_assoc]
      · left
        refine ⟨?_, fun B hB => by have := hB.1; omega⟩
        simp only [List.append_nil] at hz ⊢
        rw [show (0 : Nat) + 1 = 1 from rfl, hz, if_neg hc]
        simp [List.append_assoc]
    · left
      refine ⟨?_, fun B hB => by have := hB.1; omega⟩
      have e0 : decide (k = 0) = false := by simp [hk]
      rw [e0]
      have hi := pipeSiteInner R k (by omega) h1 (s.out k) (s.out (k + 1)) σ
      congr 1
      rw [← List.append_assoc, hi, List.append_assoc]
  · by_cases h2 : k + 1 = R
    · have hk : k = R - 1 := by omega
      have hsig : sigStep R s σ k = sigDel k (s.out k) (s.inp (k + 1)) (s.live (k + 1)) σ := by
        unfold sigStep; rw [if_neg h1, if_pos h2]
      have hd := portSite R hR (s.out k) (s.inp (k + 1)) (s.live (k + 1)) σ
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
      rw [hsig]
      have hw' := sitePort R (cohortEdge R s k).out
        (sigDel k (s.out k) (s.inp (k + 1)) (s.live (k + 1)) σ) (by omega)
      have hw := sitePort R s.out σ (by omega)
      have hlow : sFrom R (cohortEdge R s k).out
          (sigDel k (s.out k) (s.inp (k + 1)) (s.live (k + 1)) σ) (R - 1) = sFrom R s.out σ (R - 1) :=
        sFromCongr R _ _ _ _ _ (fun j hj => ⟨by rw [hout]; simp [cohortUpd, show j ≠ k by omega],
          sigDelOther k _ _ _ σ j (by omega) (by omega)⟩)
      have ek : (cohortEdge R s k).out (R - 1) =
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1 := by
        rw [hout, ← hk]; simp [cohortUpd]
      rw [hw', hw, hlow, ek]
      rw [h2] at hd hinp hlive
      rw [← hk] at hd
      rw [h2, ← hk]
      rcases hd with ⟨B, hx, hky, hiy, hlab, hcw⟩ | ⟨hcw, hnot⟩
      · right; right
        refine ⟨B, ⟨h2, hiy, hky, ?_, ?_⟩, ?_, hlab⟩
        · rw [hinp, hx, hky, hiy]; simp [bankRepairDigitDelStep]
        · rw [hlive, hx, hky, hiy]; simp [bankRepairDigitDelStep]
        · rw [hcw]; rfl
      · left
        refine ⟨by rw [hcw], fun B ⟨_, hiE, hlF, hP, _⟩ => ?_⟩
        rw [hinp] at hP
        revert hP hnot
        rw [hiE, hlF]
        rcases s.out k with _ | _ | ⟨_ | _⟩ <;> simp [bankRepairDigitDelStep]
    · left
      refine ⟨?_, fun B hB => by have := hB.1; omega⟩
      have hout : (cohortEdge R s k).out = s.out := by
        unfold cohortEdge; rw [if_neg h1, if_neg h2]
        split
        · rfl
        · split <;> rfl
      have hlow : siteWord R s.out (sigStep R s σ k) = siteWord R s.out σ := by
        unfold siteWord
        refine sFromCongr R _ _ _ _ _ (fun j hj => ⟨rfl, ?_⟩)
        unfold sigStep
        rw [if_neg h1, if_neg h2]
        split
        · exact sigFinLow k _ _ _ _ σ j (by omega)
        · rfl
      rw [hout, hlow]

/-! ### The alignment of the labels -/

/-- `b` groups of labels. Consumer: `SiteAlign`. -/
def sgrp (R : Nat) : Nat → List (Option Nat)
  | 0 => []
  | b + 1 => sgrp R b ++ sb R

theorem sgrpCons (R : Nat) : ∀ b, sgrp R (b + 1) = sb R ++ sgrp R b
  | 0 => by simp [sgrp]
  | b + 1 => by
      show sgrp R (b + 1) ++ sb R = sb R ++ (sgrp R b ++ sb R)
      rw [sgrpCons R b, List.append_assoc]

/-- The tail on cell `0` was sampled at cell `0`. Consumer: `siteCZero`. -/
def SigZero (s : CohortLane) (σ : Nat → Option Nat) : Prop := s.out 0 = .D true → σ 0 = some 0

/-- Kept by every letter. Consumer: `siteAlignStep`, `sitePreStep`. -/
theorem sigZeroStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (h : SigZero s σ) : SigZero (cohortEdge R s k) (sigStep R s σ k) := by
  intro h0
  by_cases h1 : k + 1 < R
  · have hsig : sigStep R s σ k = sigPipe k (s.out k) (s.out (k + 1)) σ := by
      unfold sigStep; rw [if_pos h1]
    rw [hsig]
    have hout : (cohortEdge R s k).out =
        cohortUpd (cohortUpd s.out k (bankRepairDigitPipeStep (decide (k = 0)) (s.out k)
          (s.out (k + 1))).1) (k + 1)
          (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 := by
      unfold cohortEdge; rw [if_pos h1]
    rw [hout] at h0
    by_cases hk : k = 0
    · subst hk
      simp only [cohortUpd, show (0 : Nat) ≠ 0 + 1 by omega, if_false, if_true] at h0
      revert h0 h
      unfold SigZero
      rcases s.out 0 with _ | _ | ⟨_ | _⟩ <;> rcases s.out (0 + 1) with _ | _ | ⟨_ | _⟩ <;>
        simp [bankRepairDigitPipeStep, sigPipe, cohortUpd]
    · simp only [cohortUpd, show (0 : Nat) ≠ k + 1 by omega, show (0 : Nat) ≠ k by omega,
        if_false] at h0
      rw [sigPipeOther k _ _ σ 0 (by omega) (by omega)]
      exact h h0
  · have hout0 : (cohortEdge R s k).out 0 = s.out 0 := by
      unfold cohortEdge; rw [if_neg h1]
      split
      · show cohortUpd s.out k _ 0 = _; simp [cohortUpd, show (0 : Nat) ≠ k by omega]
      · split
        · rfl
        · split <;> rfl
    rw [hout0] at h0
    have hs0 : sigStep R s σ k 0 = σ 0 := by
      unfold sigStep; rw [if_neg h1]
      split
      · exact sigDelOther k _ _ _ σ 0 (by omega) (by omega)
      · split
        · exact sigFinLow k _ _ _ _ σ 0 (by omega)
        · rfl
    rw [hs0]
    exact h h0

/-- A `CZero` word with a labelled tail on cell `0` ends with a group. Consumer:
`siteAlignStep`, `sitePreOf`. -/
theorem siteCZero (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (h : CZero s.out)
    (hz : SigZero s σ) : siteWord R s.out σ = sSeg R s.out σ 1 (R - 1) ++ sb R := by
  have h1 := sFromAdd R s.out σ 1 (R - 1)
  rw [show 1 + (R - 1) = R by omega] at h1
  unfold siteWord
  rw [h1]
  show _ ++ (sw R 0 (s.out 0) (σ 0) ++ []) = _
  rcases h with h | h
  · rw [h]; simp [sw]
  · rw [h, hz h]; simp [sw, sb]

/-- **The aligned labels**: `a, a - 1, …, 1`, then whole groups `0, R - 1, …, 1`; the next
export carries label `a`. Consumer: `siteAlignStep`; the pending join (I2). -/
def SiteAlign (R a : Nat) (s : CohortLane) (σ : Nat → Option Nat) : Prop :=
  CZero s.out ∧ SigZero s σ ∧ a + 1 ≤ R ∧
    ∃ b, siteWord R s.out σ = (dn (a + 1) 1).map some ++ sgrp R (b + 1)

/-- **I1: the alignment of the labels is kept, and every export carries the label `a`.**
Consumer: the pending join (I2) and the completion of the aligned group (`DigitCompletion`:
samples at `src + j`). -/
theorem siteAlignStep (R a : Nat) (hR : 2 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (h : SiteAlign R a s σ) :
    (SiteAlign R a (cohortEdge R s k) (sigStep R s σ k) ∧ ∀ B, ¬ Exported R s k B) ∨
      (∃ B, Exported R s k B ∧ σ (R - 1) = some a ∧ sigStep R s σ k R = some a ∧
        SiteAlign R (if a = 0 then R - 1 else a - 1) (cohortEdge R s k) (sigStep R s σ k)) := by
  obtain ⟨hc, hz, ha, b, hw⟩ := h
  have hc' := c0Step R hR s k hc
  have hz' := sigZeroStep R hR s σ k hz
  rcases siteStep R hR s σ k hc with ⟨he, hne⟩ | ⟨_, he, hne⟩ | ⟨B, hex, he, hlab⟩
  · left
    exact ⟨⟨hc', hz', ha, b, by rw [he, hw]⟩, hne⟩
  · left
    exact ⟨⟨hc', hz', ha, b + 1, by rw [he, hw, List.append_assoc]; rfl⟩, hne⟩
  · right
    rw [hw] at he
    obtain ⟨Y, hY⟩ : ∃ Y, siteWord R (cohortEdge R s k).out (sigStep R s σ k) = Y ++ sb R :=
      ⟨_, siteCZero R (by omega) _ _ hc' hz'⟩
    by_cases h0 : a = 0
    · subst h0
      rw [dnOne, List.map_nil, List.nil_append, sgrpCons] at he
      simp only [sb, List.cons_append, List.cons.injEq] at he
      obtain ⟨hB, hrest⟩ := he
      refine ⟨B, hex, hB.symm, by rw [hlab, ← hB], ?_⟩
      rw [if_pos rfl]
      refine ⟨hc', hz', by omega, ?_⟩
      cases b with
      | zero =>
          exfalso
          simp only [sgrp, List.append_nil] at hrest
          rw [hY] at hrest
          have hm : some 0 ∈ (dn R 1).map some := by rw [hrest]; simp [sb]
          exact zeroNotDnSome R hm
      | succ b =>
          refine ⟨b, ?_⟩
          rw [← hrest, show R - 1 + 1 = R by omega]
    · rw [dnHead a (by omega), List.map_cons] at he
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨hB, hrest⟩ := he
      refine ⟨B, hex, hB.symm, by rw [hlab, ← hB], ?_⟩
      rw [if_neg h0]
      exact ⟨hc', hz', by omega, b, by rw [← hrest, show a - 1 + 1 = a by omega]⟩

/-- **The labels before the distinguished group.** Consumer: `sitePreStep`. -/
def SitePre (R m : Nat) (s : CohortLane) (σ : Nat → Option Nat) : Prop :=
  CZero s.out ∧ SigZero s σ ∧ ∃ (Y : List (Option Nat)) (c : Nat), Y.length = m ∧
    siteWord R s.out σ = Y ++ sgrp R (c + 1)

/-- **Every `CZero` state with a labelled tail on cell `0` is `SitePre`** (e.g. as soon as cell
`0` holds `U`). Consumer: the distinguished-tail phase. -/
theorem sitePreOf (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (h : CZero s.out)
    (hz : SigZero s σ) : SitePre R (sSeg R s.out σ 1 (R - 1)).length s σ :=
  ⟨h, hz, _, 0, rfl, by rw [siteCZero R hR s σ h hz]; simp [sgrp]⟩

/-- **The prefix shrinks with each export; the export at the empty prefix is the distinguished
tail, with label `0`, after which the labels are aligned.** Consumer: the distinguished-tail
phase (start of `SiteAlign`). -/
theorem sitePreStep (R m : Nat) (hR : 2 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (h : SitePre R m s σ) :
    (SitePre R m (cohortEdge R s k) (sigStep R s σ k) ∧ ∀ B, ¬ Exported R s k B) ∨
      (∃ B, Exported R s k B ∧
        (m = 0 → σ (R - 1) = some 0 ∧ SiteAlign R (R - 1) (cohortEdge R s k) (sigStep R s σ k)) ∧
        (0 < m → SitePre R (m - 1) (cohortEdge R s k) (sigStep R s σ k))) := by
  obtain ⟨hc, hz, Y, c, hY, hw⟩ := h
  have hc' := c0Step R hR s k hc
  have hz' := sigZeroStep R hR s σ k hz
  rcases siteStep R hR s σ k hc with ⟨he, hne⟩ | ⟨_, he, hne⟩ | ⟨B, hex, he, _⟩
  · left
    exact ⟨⟨hc', hz', Y, c, hY, by rw [he, hw]⟩, hne⟩
  · left
    exact ⟨⟨hc', hz', Y, c + 1, hY, by rw [he, hw, List.append_assoc]; rfl⟩, hne⟩
  · right
    refine ⟨B, hex, fun hm => ?_, fun hm => ?_⟩
    · subst hm
      have hY0 : Y = [] := List.length_eq_zero_iff.mp hY
      subst hY0
      rw [hw, List.nil_append, sgrpCons] at he
      simp only [sb, List.cons_append, List.cons.injEq] at he
      obtain ⟨hB, hrest⟩ := he
      refine ⟨hB.symm, hc', hz', by omega, ?_⟩
      obtain ⟨Y', hY'⟩ : ∃ Y', siteWord R (cohortEdge R s k).out (sigStep R s σ k) = Y' ++ sb R :=
        ⟨_, siteCZero R (by omega) _ _ hc' hz'⟩
      cases c with
      | zero =>
          exfalso
          simp only [sgrp, List.append_nil] at hrest
          rw [hY'] at hrest
          have hm : some 0 ∈ (dn R 1).map some := by rw [hrest]; simp [sb]
          exact zeroNotDnSome R hm
      | succ c =>
          refine ⟨c, ?_⟩
          rw [← hrest, show R - 1 + 1 = R by omega]
    · obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
        cases Y with
        | nil => simp at hY; omega
        | cons y Y' => exact ⟨y, Y', rfl⟩
      rw [hw] at he
      simp only [List.cons_append, List.cons.injEq] at he
      exact ⟨hc', hz', Y', c, by simp at hY; omega, by rw [← he.2]⟩

end L3.PacketMomentSites

#print axioms L3.PacketMomentSites.siteStep
#print axioms L3.PacketMomentSites.siteAlignStep
#print axioms L3.PacketMomentSites.sitePreStep
#print axioms L3.PacketMomentSites.sigZeroStep

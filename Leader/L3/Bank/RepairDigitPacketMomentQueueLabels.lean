import Leader.L3.Bank.RepairDigitPacketMomentSites
import Leader.L3.Bank.RepairDigitPacketMomentVSerial

/-!
# Lemma e-packet, I2: the position labels of the pending queue

The label version of `L3.PacketMomentPending`. The pending packets of the target window carry
their position labels (`L3.PacketMomentSites`): the **label queue** `labExt R s σ` lists the
labels of the pending packets, oldest (rightmost) first, followed by the position word of the
source (`pendLab ++ siteWord`). Under the window invariants (`HostE`, `BarS`), every lane letter
leaves it unchanged, appends one group `sb R`, or removes its first label, which is the label of
the oldest pending packet (cell `k`, which then settles or retires) (`labExtStep`).

`LabExtAlign a`: the label queue is `a, …, 1` followed by whole groups `0, R - 1, …, 1`; it is
kept, and every removal removes the label `a` (`labAlignStep`). It starts from the source
alignment at a cut without pending packets (`labExtOfSite`).

The label queue has the length of the tail-bit queue `extWord` (`labLen`), and the source
position word that of `srcWord` (`siteLen`); so the label index of an aligned queue is its
tail-bit index (`extIdx`, `srcIdx`).
-/

namespace L3.PacketMomentQueueLabels

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.MarkedCells
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentAlign
open L3.PacketMomentPending
open L3.PacketMomentV
open L3.PacketMomentSites

/-! ### Words over cells -/

/-- The words `f (k-1), ..., f 0`. Consumer: `pendLab`. -/
def lFrom {α : Type} (f : Nat → List α) : Nat → List α
  | 0 => []
  | k + 1 => f k ++ lFrom f k

/-- The words `f (lo+m-1), ..., f lo`. Consumer: `lSplit`. -/
def lSeg {α : Type} (f : Nat → List α) (lo : Nat) : Nat → List α
  | 0 => []
  | m + 1 => f (lo + m) ++ lSeg f lo m

theorem lFromAdd {α : Type} (f : Nat → List α) (lo : Nat) :
    ∀ m, lFrom f (lo + m) = lSeg f lo m ++ lFrom f lo
  | 0 => by simp [lSeg]
  | m + 1 => by
      show f (lo + m) ++ lFrom f (lo + m) = _
      rw [lFromAdd f lo m]
      simp [lSeg, List.append_assoc]

theorem lFromCongr {α : Type} (f g : Nat → List α) :
    ∀ k, (∀ j, j < k → g j = f j) → lFrom g k = lFrom f k
  | 0 => fun _ => rfl
  | k + 1 => fun h => by
      simp only [lFrom]
      rw [h k (by omega), lFromCongr f g k (fun j hj => h j (by omega))]

theorem lSegCongr {α : Type} (f g : Nat → List α) (lo : Nat) :
    ∀ m, (∀ j, lo ≤ j → j < lo + m → g j = f j) → lSeg g lo m = lSeg f lo m
  | 0 => fun _ => rfl
  | m + 1 => fun h => by
      simp only [lSeg]
      rw [h (lo + m) (by omega) (by omega), lSegCongr f g lo m (fun j h1 h2 => h j h1 (by omega))]

theorem lSegNil {α : Type} (f : Nat → List α) (lo : Nat) :
    ∀ m, (∀ j, lo ≤ j → j < lo + m → f j = []) → lSeg f lo m = []
  | 0 => fun _ => rfl
  | m + 1 => fun h => by
      simp only [lSeg]
      rw [h (lo + m) (by omega) (by omega), lSegNil f lo m (fun j h1 h2 => h j h1 (by omega))]
      rfl

theorem lFromNil {α : Type} (f : Nat → List α) :
    ∀ k, (∀ j, j < k → f j = []) → lFrom f k = []
  | 0 => fun _ => rfl
  | k + 1 => fun h => by
      simp only [lFrom]
      rw [h k (by omega), lFromNil f k (fun j hj => h j (by omega))]
      rfl

theorem lSplit {α : Type} (f : Nat → List α) (n p : Nat) (hp : p + 2 ≤ n) :
    lFrom f n = lSeg f (p + 2) (n - (p + 2)) ++ (f (p + 1) ++ (f p ++ lFrom f p)) := by
  have h := lFromAdd f (p + 2) (n - (p + 2))
  rw [show p + 2 + (n - (p + 2)) = n by omega] at h
  rw [h]
  rfl

theorem lTop {α : Type} (f : Nat → List α) (n : Nat) (hn : 1 ≤ n) :
    lFrom f n = f (n - 1) ++ lFrom f (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem lBot {α : Type} (f : Nat → List α) (n : Nat) (hn : 1 ≤ n) :
    lFrom f n = lSeg f 1 (n - 1) ++ f 0 := by
  have h := lFromAdd f 1 (n - 1)
  rw [show 1 + (n - 1) = n by omega] at h
  rw [h]
  simp [lFrom]

/-- Lengths of cell words. Consumer: `pendLen`. -/
theorem lFromLen {α : Type} (f : Nat → List α) (g : Nat → List Bool)
    (h : ∀ j, (f j).length = (g j).length) : ∀ k, (lFrom f k).length = (gFrom g k).length
  | 0 => rfl
  | k + 1 => by
      show (f k ++ lFrom f k).length = (g k ++ gFrom g k).length
      rw [List.length_append, List.length_append, h k, lFromLen f g h k]

/-! ### The label queue -/

/-- The label of a pending input. Consumer: `pendLab`. -/
def plI : BankRepairDigitInSh → Option Nat → List (Option Nat)
  | .P _, l => [l]
  | _, _ => []

/-- **The labels of the pending packets**, oldest (rightmost) first. Consumer: `labExt`. -/
def pendLab (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) : List (Option Nat) :=
  lFrom (fun j => plI (s.inp (R + j)) (σ (R + j))) R

/-- **The label queue**: pending labels, then the labels the source owes. Consumer:
`labAlignStep`. -/
def labExt (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) : List (Option Nat) :=
  pendLab R s σ ++ siteWord R s.out σ

/-- The delivery row on the border label. Consumer: `labExtStep`. -/
theorem delPend (k : Nat) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (σ : Nat → Option Nat) (hy : ky = true → iy = .E) :
    plI (bankRepairDigitDelStep ox iy ky).2.1 (sigDel k ox iy ky σ (k + 1)) = plI iy (σ (k + 1)) ∨
      (∃ T, ox = .D T ∧ ky = false ∧ iy = .E ∧ (bankRepairDigitDelStep ox iy ky).2.1 = .P T ∧
        (bankRepairDigitDelStep ox iy ky).2.2 = false) := by
  have hk1 : k + 1 ≠ k := by omega
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitDelStep, sigDel, plI, cohortUpd, hk1] at hy ⊢

/-- The input-motion row on the pending labels. Consumer: `labExtStep`. -/
theorem finLabPend (k : Nat) (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky : Bool) (σ : Nat → Option Nat) (hx : kx = true → ix = .E)
    (hy : ky = true → iy = .E) :
    plI (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 (sigFin k ix kx iy ky σ (k + 1)) ++
        plI (bankRepairDigitFinStep bx ix kx iy ky).1 (sigFin k ix kx iy ky σ k) =
      plI iy (σ (k + 1)) ++ plI ix (σ k) ∨
    (isPI ix = true ∧ isSI iy = true ∧
      plI (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 (sigFin k ix kx iy ky σ (k + 1)) ++
        plI (bankRepairDigitFinStep bx ix kx iy ky).1 (sigFin k ix kx iy ky σ k) = []) := by
  have hk1 : k ≠ k + 1 := by omega
  rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases kx <;>
    rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases ky <;> cases bx <;>
    simp [bankRepairDigitFinStep, sigFin, plI, cohortUpd, isPI, isSI, hk1] at hx hy ⊢

/-- The terminal row on the pending labels. Consumer: `labExtStep`. -/
theorem termLabPend (ix : BankRepairDigitInSh) (kx : Bool) (l : Option Nat)
    (hx : kx = true → ix = .E) :
    plI (cohortTermStep ix kx).1 l = plI ix l ∨
      (isPI ix = true ∧ plI (cohortTermStep ix kx).1 l = []) := by
  cases kx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [cohortTermStep, plI, isPI] at hx ⊢

/-- **One lane letter on the label queue.** Unchanged, one group appended, or the first label
removed: it is the label of the oldest pending packet, on cell `k`. Consumer: `labAlignStep`. -/
theorem labExtStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (hc : CZero s.out) (hh : HostE R s) (hb : BarS R s) :
    labExt R (cohortEdge R s k) (sigStep R s σ k) = labExt R s σ ∨
      (k = 0 ∧ labExt R (cohortEdge R s k) (sigStep R s σ k) = labExt R s σ ++ sb R) ∨
      (R ≤ k ∧ k < 2 * R ∧ isPI (s.inp k) = true ∧
        labExt R s σ = σ k :: labExt R (cohortEdge R s k) (sigStep R s σ k)) := by
  have hsite := siteStep R hR s σ k hc
  unfold labExt pendLab
  by_cases h1 : k + 1 < R
  · have hinp : (cohortEdge R s k).inp = s.inp := by unfold cohortEdge; rw [if_pos h1]
    have hsig : sigStep R s σ k = sigPipe k (s.out k) (s.out (k + 1)) σ := by
      unfold sigStep; rw [if_pos h1]
    have hp : lFrom (fun j => plI ((cohortEdge R s k).inp (R + j)) (sigStep R s σ k (R + j))) R =
        lFrom (fun j => plI (s.inp (R + j)) (σ (R + j))) R :=
      lFromCongr _ _ _ (fun j _ => by
        rw [hinp, hsig, sigPipeOther _ _ _ _ _ (by omega) (by omega)])
    rw [hp]
    rcases hsite with ⟨he, _⟩ | ⟨hk0, he, _⟩ | ⟨B, hex, _⟩
    · left; rw [he]
    · right; left; exact ⟨hk0, by rw [he, List.append_assoc]⟩
    · exact absurd hex.1 (by omega)
  · by_cases h2 : k + 1 = R
    · obtain rfl : R = k + 1 := h2.symm
      have hoth : ∀ j, j ≠ k + 1 → (cohortEdge (k + 1) s k).inp j = s.inp j := by
        intro j hj
        unfold cohortEdge; rw [if_neg h1, if_pos rfl]
        show cohortUpd s.inp (k + 1) _ j = _
        simp [cohortUpd, hj]
      have hsig : sigStep (k + 1) s σ k = sigDel k (s.out k) (s.inp (k + 1)) (s.live (k + 1)) σ := by
        unfold sigStep; rw [if_neg h1, if_pos rfl]
      have hb1 := lBot (fun j => plI ((cohortEdge (k + 1) s k).inp (k + 1 + j))
        (sigStep (k + 1) s σ k (k + 1 + j))) (k + 1) (by omega)
      have hb0 := lBot (fun j => plI (s.inp (k + 1 + j)) (σ (k + 1 + j))) (k + 1) (by omega)
      have hseg : lSeg (fun j => plI ((cohortEdge (k + 1) s k).inp (k + 1 + j))
            (sigStep (k + 1) s σ k (k + 1 + j))) 1 (k + 1 - 1) =
          lSeg (fun j => plI (s.inp (k + 1 + j)) (σ (k + 1 + j))) 1 (k + 1 - 1) :=
        lSegCongr _ _ _ _ (fun j hj _ => by
          rw [hoth (k + 1 + j) (by omega), hsig, sigDelOther _ _ _ _ _ _ (by omega) (by omega)])
      rw [hb1, hb0, hseg]
      simp only [Nat.add_zero]
      have hi1 : (cohortEdge (k + 1) s k).inp (k + 1) =
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.1 := by
        unfold cohortEdge; rw [if_neg h1, if_pos rfl]
        show cohortUpd s.inp (k + 1) _ (k + 1) = _
        simp [cohortUpd]
      rcases hsite with ⟨he, hne⟩ | ⟨hk0, _, _⟩ | ⟨B, hex, he, hlab⟩
      · left
        rw [he, hi1, hsig]
        rcases delPend k (s.out k) (s.inp (k + 1)) (s.live (k + 1)) σ
            (hh (k + 1) (by omega) (by omega)) with hq | ⟨T, _, hky, hiy, hP, hlv⟩
        · rw [hq]
        · exfalso
          refine hne T ⟨rfl, hiy, hky, ?_, ?_⟩
          · rw [hi1, hP]
          · unfold cohortEdge; rw [if_neg h1, if_pos rfl]
            show cohortUpd s.live (k + 1) _ (k + 1) = _
            simp [cohortUpd, hlv]
      · omega
      · left
        obtain ⟨_, hE, _, hP, _⟩ := hex
        rw [he, hlab]
        have hP' : (cohortEdge (k + 1) s k).inp (k + 1) = .P B := hP
        rw [hP', hE]
        simp [plI, List.append_assoc]
    · have hsrc' : (cohortEdge R s k).out = s.out := by
        unfold cohortEdge; rw [if_neg h1, if_neg h2]
        split
        · rfl
        · split <;> rfl
      have hsw : siteWord R (cohortEdge R s k).out (sigStep R s σ k) = siteWord R s.out σ := by
        rw [hsrc']
        unfold siteWord
        refine sFromCongr R _ _ _ _ R (fun j hj => ⟨rfl, ?_⟩)
        unfold sigStep; rw [if_neg h1, if_neg h2]
        split
        · exact sigFinLow _ _ _ _ _ _ _ (by omega)
        · rfl
      rw [hsw]
      by_cases h3 : k + 1 < 2 * R
      · have hk : R ≤ k := by omega
        have hinp : (cohortEdge R s k).inp = cohortUpd (cohortUpd s.inp k
            (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
              (s.live (k + 1))).1) (k + 1)
            (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
              (s.live (k + 1))).2.2.1 := by
          unfold cohortEdge; rw [if_neg h1, if_neg h2, if_pos h3]
        have hsig : sigStep R s σ k = sigFin k (s.inp k) (s.live k) (s.inp (k + 1))
            (s.live (k + 1)) σ := by
          unfold sigStep; rw [if_neg h1, if_neg h2, if_pos h3]
        have hp := lSplit (fun j => plI ((cohortEdge R s k).inp (R + j))
          (sigStep R s σ k (R + j))) R (k - R) (by omega)
        have hp0 := lSplit (fun j => plI (s.inp (R + j)) (σ (R + j))) R (k - R) (by omega)
        have hseg : lSeg (fun j => plI ((cohortEdge R s k).inp (R + j)) (sigStep R s σ k (R + j)))
            (k - R + 2) (R - (k - R + 2)) =
            lSeg (fun j => plI (s.inp (R + j)) (σ (R + j))) (k - R + 2) (R - (k - R + 2)) :=
          lSegCongr _ _ _ _ (fun j hj _ => by
            rw [hinp, hsig, sigFinLow _ _ _ _ _ _ _ (by omega)]
            simp [cohortUpd, show R + j ≠ k by omega, show R + j ≠ k + 1 by omega])
        have hlow : lFrom (fun j => plI ((cohortEdge R s k).inp (R + j))
            (sigStep R s σ k (R + j))) (k - R) =
            lFrom (fun j => plI (s.inp (R + j)) (σ (R + j))) (k - R) :=
          lFromCongr _ _ _ (fun j hj => by
            rw [hinp, hsig, sigFinLow _ _ _ _ _ _ _ (by omega)]
            simp [cohortUpd, show R + j ≠ k by omega, show R + j ≠ k + 1 by omega])
        have e1 : R + (k - R + 1) = k + 1 := by omega
        have e0 : R + (k - R) = k := by omega
        rw [hp, hp0, hseg, hlow]
        simp only [e1, e0]
        have ik1 : (cohortEdge R s k).inp (k + 1) =
            (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
              (s.live (k + 1))).2.2.1 := by rw [hinp]; simp [cohortUpd]
        have ik : (cohortEdge R s k).inp k =
            (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
              (s.live (k + 1))).1 := by rw [hinp]; simp [cohortUpd]
        rw [ik1, ik, hsig]
        rcases finLabPend k (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1)) (s.live (k + 1)) σ
            (hh k hk (by omega)) (hh (k + 1) (by omega) h3) with hq | ⟨hP, hS, hnil⟩
        · left
          have key : ∀ L : List (Option Nat),
              plI (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
                (s.live (k + 1))).2.2.1 (sigFin k (s.inp k) (s.live k) (s.inp (k + 1))
                  (s.live (k + 1)) σ (k + 1)) ++
              (plI (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
                (s.live (k + 1))).1 (sigFin k (s.inp k) (s.live k) (s.inp (k + 1))
                  (s.live (k + 1)) σ k) ++ L) =
              plI (s.inp (k + 1)) (σ (k + 1)) ++ (plI (s.inp k) (σ k) ++ L) := fun L => by
            rw [← List.append_assoc, hq, List.append_assoc]
          rw [key]
        · right; right
          refine ⟨hk, by omega, hP, ?_⟩
          have hup : lSeg (fun j => plI (s.inp (R + j)) (σ (R + j))) (k - R + 2)
              (R - (k - R + 2)) = [] :=
            lSegNil _ _ _ (fun j h1' h2' => by
              cases hq : s.inp (R + j) with
              | P T =>
                  exfalso
                  have := hb (R + j) (k + 1) (by omega) (by omega) (by omega) h3
                    (by rw [hq]; rfl) hS
                  omega
              | _ => rfl)
          have key : ∀ L : List (Option Nat),
              plI (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
                (s.live (k + 1))).2.2.1 (sigFin k (s.inp k) (s.live k) (s.inp (k + 1))
                  (s.live (k + 1)) σ (k + 1)) ++
              (plI (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
                (s.live (k + 1))).1 (sigFin k (s.inp k) (s.live k) (s.inp (k + 1))
                  (s.live (k + 1)) σ k) ++ L) = L := fun L => by
            rw [← List.append_assoc, hnil, List.nil_append]
          rw [key, hup]
          have hSn : plI (s.inp (k + 1)) (σ (k + 1)) = [] := by
            revert hS; cases s.inp (k + 1) with
            | S T => intro _; rfl
            | _ => intro h; cases h
          have hPn : plI (s.inp k) (σ k) = [σ k] := by
            revert hP; cases s.inp k with
            | P T => intro _; rfl
            | _ => intro h; cases h
          rw [hSn, hPn]
          simp
      · by_cases h4 : k + 1 = 2 * R
        · have hinp : (cohortEdge R s k).inp = cohortUpd s.inp k
              (cohortTermStep (s.inp k) (s.live k)).1 := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          have hsig : sigStep R s σ k = σ := by
            unfold sigStep; rw [if_neg h1, if_neg h2, if_neg h3]
          rw [hsig]
          have ht := lTop (fun j => plI ((cohortEdge R s k).inp (R + j)) (σ (R + j))) R (by omega)
          have ht0 := lTop (fun j => plI (s.inp (R + j)) (σ (R + j))) R (by omega)
          have hlow : lFrom (fun j => plI ((cohortEdge R s k).inp (R + j)) (σ (R + j))) (R - 1) =
              lFrom (fun j => plI (s.inp (R + j)) (σ (R + j))) (R - 1) :=
            lFromCongr _ _ _ (fun j hj => by
              rw [hinp]; simp [cohortUpd, show R + j ≠ k by omega])
          have e0 : R + (R - 1) = k := by omega
          rw [ht, ht0, hlow]
          simp only [e0]
          have ik : (cohortEdge R s k).inp k = (cohortTermStep (s.inp k) (s.live k)).1 := by
            rw [hinp]; simp [cohortUpd]
          rw [ik]
          rcases termLabPend (s.inp k) (s.live k) (σ k) (hh k (by omega) (by omega)) with
            hq | ⟨hP, hnil⟩
          · left; rw [hq]
          · right; right
            refine ⟨by omega, by omega, hP, ?_⟩
            have hPn : plI (s.inp k) (σ k) = [σ k] := by
              revert hP; cases s.inp k with
              | P T => intro _; rfl
              | _ => intro h; cases h
            rw [hnil, hPn]
            simp
        · left
          rw [edgeFar R s k (by omega)]
          have hsig : sigStep R s σ k = σ := by
            unfold sigStep; rw [if_neg h1, if_neg h2, if_neg h3]
          rw [hsig]

/-! ### Lengths -/

theorem dnLen (m j : Nat) : (dn m j).length = m - j := by
  simp [dn]

theorem swLen (R j : Nat) (o : BankRepairDigitOutSh) (v : Option Nat) :
    (sw R j o v).length = (cw R j o).length := by
  rcases o with _ | _ | ⟨_ | _⟩
  · rfl
  · by_cases h : j = 0 <;> simp [sw, cw, h, sb, blk, dnLen]
  · rfl
  · by_cases h : j = 0 <;> simp [sw, cw, h, dnLen]

theorem sFromLen (R : Nat) (out : Nat → BankRepairDigitOutSh) (σ : Nat → Option Nat) :
    ∀ k, (sFrom R out σ k).length = (wFrom R out k).length
  | 0 => rfl
  | k + 1 => by
      show (sw R k (out k) (σ k) ++ sFrom R out σ k).length = (cw R k (out k) ++ wFrom R out k).length
      rw [List.length_append, List.length_append, swLen, sFromLen R out σ k]

/-- **The position word has the length of the tail-bit word.** Consumer: `srcIdx`. -/
theorem siteLen (R : Nat) (out : Nat → BankRepairDigitOutSh) (σ : Nat → Option Nat) :
    (siteWord R out σ).length = (srcWord R out).length :=
  sFromLen R out σ R

/-- **The label queue has the length of the tail-bit queue.** Consumer: `extIdx`. -/
theorem labLen (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) :
    (labExt R s σ).length = (extWord R s).length := by
  unfold labExt extWord pendLab pendWord
  rw [List.length_append, List.length_append, siteLen]
  congr 1
  exact lFromLen _ _ (fun j => by
    cases s.inp (R + j) with
    | P T => rfl
    | _ => rfl) R

theorem grpLen (R : Nat) (hR : 1 ≤ R) : ∀ b, (grp R b).length = b * R
  | 0 => by simp [grp]
  | b + 1 => by
      show (grp R b ++ blk R).length = _
      rw [List.length_append, grpLen R hR b, Nat.succ_mul]
      simp [blk]
      omega

theorem sgrpLen (R : Nat) (hR : 1 ≤ R) : ∀ b, (sgrp R b).length = b * R
  | 0 => by simp [sgrp]
  | b + 1 => by
      show (sgrp R b ++ sb R).length = _
      rw [List.length_append, sgrpLen R hR b, Nat.succ_mul]
      simp [sb, dnLen]
      omega

/-- Two aligned forms of equal length have equal index. Consumer: `extIdx`, `srcIdx`. -/
theorem idxOfLen (R a a' b b' : Nat) (ha : a < R) (ha' : a' < R)
    (h : a + (b + 1) * R = a' + (b' + 1) * R) : a = a' := by
  have h1 : (a + (b + 1) * R) % R = a := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h2 : (a' + (b' + 1) * R) % R = a' := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha']
  rw [← h1, ← h2, h]

/-! ### The aligned label queue -/

/-- **The aligned label queue**: `a, …, 1`, then whole groups `0, R - 1, …, 1`. Consumer: the
label version of the renewal trial. -/
def LabExtAlign (R a : Nat) (s : CohortLane) (σ : Nat → Option Nat) : Prop :=
  CZero s.out ∧ SigZero s σ ∧ a + 1 ≤ R ∧
    ∃ b, labExt R s σ = (dn (a + 1) 1).map some ++ sgrp R (b + 1)

/-- **The label index of an aligned queue is its tail-bit index.** Consumer: the label version of
the renewal trial. -/
theorem extIdx (R a a' : Nat) (s : CohortLane) (σ : Nat → Option Nat) (hA : AlignExt R a s)
    (hL : LabExtAlign R a' s σ) : a = a' := by
  obtain ⟨_, ha, b, hb⟩ := hA
  obtain ⟨_, _, ha', b', hb'⟩ := hL
  have hl := labLen R s σ
  rw [hb, hb'] at hl
  simp only [List.length_append, List.length_map, List.length_replicate, dnLen,
    sgrpLen R (by omega), grpLen R (by omega)] at hl
  exact idxOfLen R a a' b b' (by omega) (by omega) (by omega)

/-- **The label index of an aligned source is its tail-bit index.** Consumer: the label version
of the distinguished-tail and inherited-work phases. -/
theorem srcIdx (R a a' : Nat) (s : CohortLane) (σ : Nat → Option Nat) (hA : Align R a s.out)
    (hL : SiteAlign R a' s σ) : a = a' := by
  obtain ⟨_, ha, b, hb⟩ := hA
  obtain ⟨_, _, ha', b', hb'⟩ := hL
  have hl := siteLen R s.out σ
  rw [hb, hb'] at hl
  simp only [List.length_append, List.length_map, List.length_replicate, dnLen,
    sgrpLen R (by omega), grpLen R (by omega)] at hl
  exact idxOfLen R a a' b b' (by omega) (by omega) (by omega)

/-- **The aligned label queue is kept, and every removal removes the label `a`.** Consumer: the
label version of the renewal trial. -/
theorem labAlignStep (R a : Nat) (hR : 2 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (h : LabExtAlign R a s σ) (hh : HostE R s) (hb : BarS R s) :
    (LabExtAlign R a (cohortEdge R s k) (sigStep R s σ k) ∧
        (labExt R s σ).length ≤ (labExt R (cohortEdge R s k) (sigStep R s σ k)).length) ∨
      (R ≤ k ∧ k < 2 * R ∧ isPI (s.inp k) = true ∧ σ k = some a ∧
        labExt R s σ = σ k :: labExt R (cohortEdge R s k) (sigStep R s σ k) ∧
        LabExtAlign R (if a = 0 then R - 1 else a - 1) (cohortEdge R s k) (sigStep R s σ k)) := by
  obtain ⟨hc, hz, ha, b, hw⟩ := h
  have hc' := c0Step R hR s k hc
  have hz' := sigZeroStep R hR s σ k hz
  rcases labExtStep R hR s σ k hc hh hb with he | ⟨_, he⟩ | ⟨hk, hk2, hP, he⟩
  · left
    exact ⟨⟨hc', hz', ha, b, by rw [he, hw]⟩, by rw [he]; exact Nat.le_refl _⟩
  · left
    refine ⟨⟨hc', hz', ha, b + 1, by rw [he, hw, List.append_assoc]; rfl⟩, ?_⟩
    rw [he, List.length_append]
    omega
  · right
    obtain ⟨Y, hY⟩ : ∃ Y, labExt R (cohortEdge R s k) (sigStep R s σ k) = Y ++ sb R := by
      refine ⟨pendLab R (cohortEdge R s k) (sigStep R s σ k) ++
        sSeg R (cohortEdge R s k).out (sigStep R s σ k) 1 (R - 1), ?_⟩
      unfold labExt
      rw [siteCZero R (by omega) _ _ hc' hz', List.append_assoc]
    rw [hw] at he
    by_cases h0 : a = 0
    · subst h0
      rw [dnOne, List.map_nil, List.nil_append, sgrpCons] at he
      simp only [sb, List.cons_append, List.cons.injEq] at he
      obtain ⟨hB, hrest⟩ := he
      refine ⟨hk, hk2, hP, hB.symm, ?_, ?_⟩
      · rw [hw, dnOne, List.map_nil, List.nil_append, sgrpCons, ← hB]
        simp only [sb, List.cons_append]
        rw [hrest]
      · rw [if_pos rfl]
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
      refine ⟨hk, hk2, hP, hB.symm, ?_, ?_⟩
      · rw [hw, dnHead a (by omega), List.map_cons, ← hB]
        simp only [List.cons_append]
        rw [hrest]
      · rw [if_neg h0]
        exact ⟨hc', hz', by omega, b, by rw [← hrest, show a - 1 + 1 = a by omega]⟩

/-- **A cut without pending packets inherits the source label alignment.** Consumer: the start
of the label queue at the mobile-free cut. -/
theorem labExtOfSite (R a : Nat) (s : CohortLane) (σ : Nat → Option Nat) (h : SiteAlign R a s σ)
    (hnp : ∀ q, R ≤ q → q < 2 * R → isPI (s.inp q) = false) : LabExtAlign R a s σ := by
  obtain ⟨hc, hz, ha, b, hw⟩ := h
  refine ⟨hc, hz, ha, b, ?_⟩
  have hp : pendLab R s σ = [] :=
    lFromNil _ _ (fun j hj => by
      have := hnp (R + j) (by omega) (by omega)
      revert this
      cases s.inp (R + j) with
      | P T => intro h; cases h
      | _ => intro _; rfl)
  unfold labExt
  rw [hp, List.nil_append, hw]

end L3.PacketMomentQueueLabels

#print axioms L3.PacketMomentQueueLabels.labExtStep
#print axioms L3.PacketMomentQueueLabels.labLen
#print axioms L3.PacketMomentQueueLabels.extIdx
#print axioms L3.PacketMomentQueueLabels.srcIdx
#print axioms L3.PacketMomentQueueLabels.labAlignStep
#print axioms L3.PacketMomentQueueLabels.labExtOfSite

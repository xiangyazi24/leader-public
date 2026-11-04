import Leader.L3.Bank.RepairDigitPacketMomentAlign
import Leader.L3.Bank.RepairDigitPacketMomentU

/-!
# Lemma e-packet: the pending word joined to the export word

The pending packets of the target window, oldest (rightmost) first, followed by the owed
exports of the source block, form the word `extWord R s` (`pendWord ++ srcWord`). With the
fresh-carry invariant and the packet barrier of the window (`Inv`, `Barrier`, kept by every
letter: `L3.PacketMomentU.winKeep`), every lane letter leaves `extWord` unchanged (an export
moves the first owed letter to the youngest pending packet), appends one group (a tail
leaving source cell `0`), or removes its first letter, and then exactly the oldest pending
packet settles beside a settled input (internal edge) or is retired at the terminal
(`extStep`). The removed bit is the packet's tail bit.

So the queue rank of a pending packet fixes its tail bit: `alignExtStep` keeps the form
`F^a (T F^(R-1))^(b+1)` of `extWord`, and the next removal is a tail iff `a = 0`. A
packet-only cut (no pending packet) inherits the form from the source alignment
(`alignExtOfSrc`, `L3.PacketMomentAlign.Align`). The ranks agree with the export-time order
of `L3.DigitPacketQueue.QueueAt` (clause 2: right of means older), so this is the pending
queue of `PacketQueue` with tail bits attached.
-/

namespace L3.PacketMomentPending

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.MarkedCells
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentAlign

/-! ### Generic words over cells -/

/-- The words `f (k-1), ..., f 0`. Consumer: `pendWord`. -/
def gFrom (f : Nat → List Bool) : Nat → List Bool
  | 0 => []
  | k + 1 => f k ++ gFrom f k

/-- The words `f (lo+m-1), ..., f lo`. Consumer: `gSplit`. -/
def gSeg (f : Nat → List Bool) (lo : Nat) : Nat → List Bool
  | 0 => []
  | m + 1 => f (lo + m) ++ gSeg f lo m

/-- Splitting. Consumer: `gSplit`. -/
theorem gFromAdd (f : Nat → List Bool) (lo : Nat) :
    ∀ m, gFrom f (lo + m) = gSeg f lo m ++ gFrom f lo
  | 0 => by simp [gSeg]
  | m + 1 => by
      show f (lo + m) ++ gFrom f (lo + m) = _
      rw [gFromAdd f lo m]
      simp [gSeg, List.append_assoc]

/-- Agreement below `k`. Consumer: `extStep`. -/
theorem gFromCongr (f g : Nat → List Bool) :
    ∀ k, (∀ j, j < k → g j = f j) → gFrom g k = gFrom f k
  | 0 => fun _ => rfl
  | k + 1 => fun h => by
      simp only [gFrom]
      rw [h k (by omega), gFromCongr f g k (fun j hj => h j (by omega))]

/-- Agreement on a segment. Consumer: `extStep`. -/
theorem gSegCongr (f g : Nat → List Bool) (lo : Nat) :
    ∀ m, (∀ j, lo ≤ j → j < lo + m → g j = f j) → gSeg g lo m = gSeg f lo m
  | 0 => fun _ => rfl
  | m + 1 => fun h => by
      simp only [gSeg]
      rw [h (lo + m) (by omega) (by omega), gSegCongr f g lo m (fun j h1 h2 => h j h1 (by omega))]

/-- An empty segment. Consumer: `extStep`. -/
theorem gSegNil (f : Nat → List Bool) (lo : Nat) :
    ∀ m, (∀ j, lo ≤ j → j < lo + m → f j = []) → gSeg f lo m = []
  | 0 => fun _ => rfl
  | m + 1 => fun h => by
      simp only [gSeg]
      rw [h (lo + m) (by omega) (by omega), gSegNil f lo m (fun j h1 h2 => h j h1 (by omega))]
      rfl

/-- The word around cells `p`, `p+1`. Consumer: `extStep`. -/
theorem gSplit (f : Nat → List Bool) (n p : Nat) (hp : p + 2 ≤ n) :
    gFrom f n = gSeg f (p + 2) (n - (p + 2)) ++ (f (p + 1) ++ (f p ++ gFrom f p)) := by
  have h := gFromAdd f (p + 2) (n - (p + 2))
  rw [show p + 2 + (n - (p + 2)) = n by omega] at h
  rw [h]
  rfl

/-- The word at the top cell. Consumer: `extStep`. -/
theorem gTop (f : Nat → List Bool) (n : Nat) (hn : 1 ≤ n) :
    gFrom f n = f (n - 1) ++ gFrom f (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- The word at the bottom cell. Consumer: `extStep`. -/
theorem gBot (f : Nat → List Bool) (n : Nat) (hn : 1 ≤ n) :
    gFrom f n = gSeg f 1 (n - 1) ++ f 0 := by
  have h := gFromAdd f 1 (n - 1)
  rw [show 1 + (n - 1) = n by omega] at h
  rw [h]
  simp [gFrom]

/-! ### The pending word -/

/-- The tail bit of a pending input. Consumer: `pendWord`. -/
def pwI : BankRepairDigitInSh → List Bool
  | .P T => [T]
  | _ => []

/-- Pending input test. Consumer: `finPend`. -/
def isPI : BankRepairDigitInSh → Bool
  | .P _ => true
  | _ => false

/-- Settled input test. Consumer: `finPend`. -/
def isSI : BankRepairDigitInSh → Bool
  | .S _ => true
  | _ => false

/-- The settled input of a pending one. Consumer: `finPend`. -/
def settleOf : BankRepairDigitInSh → BankRepairDigitInSh
  | .P T => .S T
  | i => i

/-- **The pending word** of the target window, oldest (rightmost) first. Consumer: `extWord`. -/
def pendWord (R : Nat) (s : CohortLane) : List Bool := gFrom (fun j => pwI (s.inp (R + j))) R

/-- **Pending queue then owed exports.** Consumer: `alignExtStep`, the renewal preparation `V`. -/
def extWord (R : Nat) (s : CohortLane) : List Bool := pendWord R s ++ srcWord R s.out

/-- **The Fin row on the pending word**: unchanged, or the initiator is a pending packet that
settles beside a settled responder. Consumer: `extStep`. -/
theorem finPend (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (hx : kx = true → ix = .E) (hy : ky = true → iy = .E) :
    pwI (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 ++ pwI (bankRepairDigitFinStep bx ix kx iy ky).1
        = pwI iy ++ pwI ix ∨
      (isPI ix = true ∧ isSI iy = true ∧ (bankRepairDigitFinStep bx ix kx iy ky).1 = settleOf ix ∧
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = iy ∧
        pwI (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 ++
          pwI (bankRepairDigitFinStep bx ix kx iy ky).1 = []) := by
  cases bx <;> cases kx <;> cases ky <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    revert hx hy <;> decide

/-- The retired input of a pending packet at the terminal. Consumer: `termPend`. -/
def retireOf : BankRepairDigitInSh → BankRepairDigitInSh
  | .P true => .E
  | .P false => .S false
  | i => i

/-- **The terminal row on the pending word.** Consumer: `extStep`. -/
theorem termPend (ix : BankRepairDigitInSh) (kx : Bool) (hx : kx = true → ix = .E) :
    pwI (cohortTermStep ix kx).1 = pwI ix ∨
      (isPI ix = true ∧ (cohortTermStep ix kx).1 = retireOf ix ∧ pwI (cohortTermStep ix kx).1 = []) := by
  cases kx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> revert hx <;> decide

/-! ### Lane forms of the window invariants -/

/-- Live carries sit on empty hosts. Consumer: `extStep`. -/
def HostE (R : Nat) (s : CohortLane) : Prop :=
  ∀ q, R ≤ q → q < 2 * R → s.live q = true → s.inp q = .E

/-- Pending inputs lie left of every settled input. Consumer: `extStep`. -/
def BarS (R : Nat) (s : CohortLane) : Prop :=
  ∀ i j, R ≤ i → i < 2 * R → R ≤ j → j < 2 * R → isPI (s.inp i) = true →
    isSI (s.inp j) = true → i < j

/-- The fresh-carry invariant gives empty hosts. Consumer: `extStepOfWin`. -/
theorem hostOfInv (R : Nat) (s : CohortLane) (h : Inv R (winOf R s)) : HostE R s := by
  intro q h1 h2 hl
  have := (h.1 (q - R) (by omega) (by simp [winOf, liftC, show R + (q - R) = q by omega, hl])).1
  simp only [winOf, liftC, show R + (q - R) = q by omega] at this
  revert this
  cases s.inp q with
  | E => intro _; rfl
  | X => intro h; cases h
  | P T => cases T <;> (intro h; cases h)
  | S T => cases T <;> (intro h; cases h)

/-- The packet barrier gives `BarS`. Consumer: `extStepOfWin`. -/
theorem barOfBarrier (R : Nat) (s : CohortLane) (h : Barrier R (winOf R s)) : BarS R s := by
  intro i j h1 h2 h3 h4 hP hS
  have hP' : (winOf R s (i - R)).i.isP = true := by
    simp only [winOf, liftC, show R + (i - R) = i by omega]
    revert hP; cases s.inp i with
    | P T => cases T <;> (intro _; rfl)
    | _ => intro h; cases h
  have hS' : obC (winOf R s (j - R)) = true := by
    simp only [winOf, liftC, show R + (j - R) = j by omega, obC]
    revert hS; cases s.inp j with
    | S T => cases T <;> intro _ <;> simp [cellIn, Inp.isS]
    | _ => intro h; cases h
  have := h (i - R) (j - R) (by omega) (by omega) hP' hS'
  omega

/-! ### One lane letter on the joined word -/

/-- On a window edge the two cells keep their pending letters (no settlement, no
retirement). Consumer: `extStep`, the renewal preparation `V`. -/
def LocalSame (R : Nat) (s : CohortLane) (k : Nat) : Prop :=
  (R ≤ k → k + 1 < 2 * R → pwI ((cohortEdge R s k).inp (k + 1)) ++ pwI ((cohortEdge R s k).inp k) =
    pwI (s.inp (k + 1)) ++ pwI (s.inp k)) ∧
  (k + 1 = 2 * R → pwI ((cohortEdge R s k).inp k) = pwI (s.inp k))

/-- **One lane letter on the pending-then-owed word.** Unchanged, one group appended, or the
first letter removed: then the oldest pending packet (cell `k`) settles beside a settled input,
or is retired at the terminal. Consumer: `alignExtStep`, the renewal preparation `V`. -/
theorem extStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (hc : CZero s.out)
    (hh : HostE R s) (hb : BarS R s) :
    (extWord R (cohortEdge R s k) = extWord R s ∧ LocalSame R s k) ∨
      (k = 0 ∧ extWord R (cohortEdge R s k) = extWord R s ++ blk R) ∨
      (∃ B, extWord R s = B :: extWord R (cohortEdge R s k) ∧ R ≤ k ∧ k < 2 * R ∧
        s.inp k = .P B ∧
        (k + 1 < 2 * R → isSI (s.inp (k + 1)) = true ∧ (cohortEdge R s k).inp k = .S B) ∧
        (k + 1 = 2 * R → (cohortEdge R s k).inp k = retireOf (.P B))) := by
  have hsrc := srcStep R hR s k hc
  unfold extWord pendWord
  by_cases h1 : k + 1 < R
  · have hinp : (cohortEdge R s k).inp = s.inp := by unfold cohortEdge; rw [if_pos h1]
    rw [hinp]
    rcases hsrc with ⟨he, _⟩ | ⟨hk0, he⟩ | ⟨B, ⟨hk, _⟩, _⟩
    · left; exact ⟨by rw [he], fun h _ => by omega, fun h => by omega⟩
    · right; left; exact ⟨hk0, by rw [he, List.append_assoc]⟩
    · omega
  · by_cases h2 : k + 1 = R
    · have hoth : ∀ j, j ≠ R → (cohortEdge R s k).inp j = s.inp j := by
        intro j hj
        unfold cohortEdge; rw [if_neg h1, if_pos h2]
        show cohortUpd s.inp (k + 1) _ j = _
        simp [cohortUpd, show j ≠ k + 1 by omega]
      have hb1 := gBot (fun j => pwI ((cohortEdge R s k).inp (R + j))) R (by omega)
      have hb0 := gBot (fun j => pwI (s.inp (R + j))) R (by omega)
      have hseg : gSeg (fun j => pwI ((cohortEdge R s k).inp (R + j))) 1 (R - 1) =
          gSeg (fun j => pwI (s.inp (R + j))) 1 (R - 1) :=
        gSegCongr _ _ _ _ (fun j hj _ => by rw [hoth (R + j) (by omega)])
      rw [hb1, hb0, hseg]
      simp only [Nat.add_zero]
      rcases hsrc with ⟨he, hw⟩ | ⟨hk, _⟩ | ⟨B, ⟨_, hE, _, hP, _⟩, he⟩
      · left
        refine ⟨?_, fun h _ => by omega, fun h => by omega⟩
        obtain ⟨hi, hl⟩ := hw h2
        rw [he, hi]
        by_cases hlv : s.live R = true
        · rw [if_pos hlv, hh R (by omega) (by omega) hlv]
        · rw [if_neg hlv]
      · omega
      · left
        refine ⟨?_, fun h _ => by omega, fun h => by omega⟩
        rw [hP, hE, he]
        simp [pwI, List.append_assoc]
    · have hsrc' : (cohortEdge R s k).out = s.out := by
        unfold cohortEdge; rw [if_neg h1, if_neg h2]
        split
        · rfl
        · split <;> rfl
      rw [hsrc']
      by_cases h3 : k + 1 < 2 * R
      · -- an internal window edge
        have hk : R ≤ k := by omega
        have hinp : (cohortEdge R s k).inp = cohortUpd (cohortUpd s.inp k
            (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
              (s.live (k + 1))).1) (k + 1)
            (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
              (s.live (k + 1))).2.2.1 := by
          unfold cohortEdge; rw [if_neg h1, if_neg h2, if_pos h3]
        have hp := gSplit (fun j => pwI ((cohortEdge R s k).inp (R + j))) R (k - R) (by omega)
        have hp0 := gSplit (fun j => pwI (s.inp (R + j))) R (k - R) (by omega)
        have hseg : gSeg (fun j => pwI ((cohortEdge R s k).inp (R + j))) (k - R + 2)
            (R - (k - R + 2)) = gSeg (fun j => pwI (s.inp (R + j))) (k - R + 2) (R - (k - R + 2)) :=
          gSegCongr _ _ _ _ (fun j hj _ => by
            rw [hinp]; simp [cohortUpd, show R + j ≠ k by omega,
              show R + j ≠ k + 1 by omega])
        have hlow : gFrom (fun j => pwI ((cohortEdge R s k).inp (R + j))) (k - R) =
            gFrom (fun j => pwI (s.inp (R + j))) (k - R) :=
          gFromCongr _ _ _ (fun j hj => by
            rw [hinp]; simp [cohortUpd, show R + j ≠ k by omega,
              show R + j ≠ k + 1 by omega])
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
        rw [ik1, ik]
        rcases finPend (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1)) (s.live (k + 1))
            (hh k hk (by omega)) (hh (k + 1) (by omega) h3) with hq | ⟨hP, hS, hx', _, hnil⟩
        · left
          have key : ∀ L : List Bool,
              pwI (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
                (s.live (k + 1))).2.2.1 ++ (pwI (bankRepairDigitFinStep (decide (k = R)) (s.inp k)
                (s.live k) (s.inp (k + 1)) (s.live (k + 1))).1 ++ L) =
              pwI (s.inp (k + 1)) ++ (pwI (s.inp k) ++ L) := fun L => by
            rw [← List.append_assoc, hq, List.append_assoc]
          refine ⟨by rw [key], fun _ _ => by rw [ik1, ik]; exact hq, fun h => by omega⟩
        · right; right
          obtain ⟨B, hB⟩ : ∃ B, s.inp k = .P B := by
            revert hP; cases s.inp k with
            | P T => intro _; exact ⟨T, rfl⟩
            | _ => intro h; cases h
          have hup : gSeg (fun j => pwI (s.inp (R + j))) (k - R + 2) (R - (k - R + 2)) = [] :=
            gSegNil _ _ _ (fun j h1' h2' => by
              cases hq : s.inp (R + j) with
              | P T =>
                  exfalso
                  have := hb (R + j) (k + 1) (by omega) (by omega) (by omega) h3
                    (by rw [hq]; rfl) hS
                  omega
              | _ => rfl)
          refine ⟨B, ?_, hk, by omega, hB, fun _ => ⟨hS, by rw [hx', hB]; rfl⟩,
            fun h' => by omega⟩
          have key : ∀ L : List Bool,
              pwI (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
                (s.live (k + 1))).2.2.1 ++ (pwI (bankRepairDigitFinStep (decide (k = R)) (s.inp k)
                (s.live k) (s.inp (k + 1)) (s.live (k + 1))).1 ++ L) = L := fun L => by
            rw [← List.append_assoc, hnil, List.nil_append]
          rw [hup, key, hB]
          have hSn : pwI (s.inp (k + 1)) = [] := by
            revert hS; cases s.inp (k + 1) with
            | S T => intro _; rfl
            | _ => intro h; cases h
          rw [hSn]
          simp [pwI]
      · by_cases h4 : k + 1 = 2 * R
        · have hinp : (cohortEdge R s k).inp = cohortUpd s.inp k
              (cohortTermStep (s.inp k) (s.live k)).1 := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          have ht := gTop (fun j => pwI ((cohortEdge R s k).inp (R + j))) R (by omega)
          have ht0 := gTop (fun j => pwI (s.inp (R + j))) R (by omega)
          have hlow : gFrom (fun j => pwI ((cohortEdge R s k).inp (R + j))) (R - 1) =
              gFrom (fun j => pwI (s.inp (R + j))) (R - 1) :=
            gFromCongr _ _ _ (fun j hj => by
              rw [hinp]; simp [cohortUpd, show R + j ≠ k by omega])
          have e0 : R + (R - 1) = k := by omega
          rw [ht, ht0, hlow]
          simp only [e0]
          have ik : (cohortEdge R s k).inp k = (cohortTermStep (s.inp k) (s.live k)).1 := by
            rw [hinp]; simp [cohortUpd]
          rw [ik]
          rcases termPend (s.inp k) (s.live k) (hh k (by omega) (by omega)) with
            hq | ⟨hP, hx', hnil⟩
          · left; exact ⟨by rw [hq], fun _ h => by omega, fun _ => by rw [ik]; exact hq⟩
          · right; right
            obtain ⟨B, hB⟩ : ∃ B, s.inp k = .P B := by
              revert hP; cases s.inp k with
              | P T => intro _; exact ⟨T, rfl⟩
              | _ => intro h; cases h
            refine ⟨B, ?_, by omega, by omega, hB, fun h' => by omega,
              fun _ => by rw [hx', hB]⟩
            rw [hnil, hB]
            simp [pwI]
        · left
          have hinp : (cohortEdge R s k).inp = s.inp := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          exact ⟨by rw [hinp], fun _ h => by omega, fun h => by omega⟩

/-- `extStep` from the window invariants. Consumer: the renewal preparation `V`. -/
theorem extStepOfWin (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (hc : CZero s.out)
    (h : Inv R (winOf R s) ∧ Barrier R (winOf R s)) :
    (extWord R (cohortEdge R s k) = extWord R s ∧ LocalSame R s k) ∨
      (k = 0 ∧ extWord R (cohortEdge R s k) = extWord R s ++ blk R) ∨
      (∃ B, extWord R s = B :: extWord R (cohortEdge R s k) ∧ R ≤ k ∧ k < 2 * R ∧
        s.inp k = .P B ∧
        (k + 1 < 2 * R → isSI (s.inp (k + 1)) = true ∧ (cohortEdge R s k).inp k = .S B) ∧
        (k + 1 = 2 * R → (cohortEdge R s k).inp k = retireOf (.P B))) :=
  extStep R hR s k hc (hostOfInv R s h.1) (barOfBarrier R s h.2)

/-! ### The alignment of the pending queue -/

/-- **The aligned pending queue**: `extWord = F^a (T F^(R-1))^(b+1)`, `a ≤ R - 1`; the next
removal (settlement or terminal retirement of the oldest pending packet) is a tail iff
`a = 0`. Consumer: the renewal preparation `V`. -/
def AlignExt (R a : Nat) (s : CohortLane) : Prop :=
  CZero s.out ∧ a + 1 ≤ R ∧ ∃ b, extWord R s = List.replicate a false ++ grp R (b + 1)

/-- A word ending in a group. Consumer: `alignExtStep`. -/
theorem extEndsBlk (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (hc : CZero s.out) :
    ∃ Y, extWord R s = Y ++ blk R :=
  ⟨pendWord R s ++ wSeg R s.out 1 (R - 1), by
    unfold extWord; rw [wordCZero R hR s.out hc, List.append_assoc]⟩

/-- **The queue alignment is kept by every letter, and fixes the tail bit of every removal.**
Consumer: the renewal preparation `V`. -/
theorem alignExtStep (R a : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (h : AlignExt R a s)
    (hw : Inv R (winOf R s) ∧ Barrier R (winOf R s)) :
    (AlignExt R a (cohortEdge R s k) ∧
        (∀ B, extWord R s ≠ B :: extWord R (cohortEdge R s k)) ∧ LocalSame R s k) ∨
      (∃ B, extWord R s = B :: extWord R (cohortEdge R s k) ∧ B = decide (a = 0) ∧
        AlignExt R (if a = 0 then R - 1 else a - 1) (cohortEdge R s k) ∧ R ≤ k ∧ k < 2 * R ∧
        s.inp k = .P B ∧
        (k + 1 < 2 * R → isSI (s.inp (k + 1)) = true ∧ (cohortEdge R s k).inp k = .S B) ∧
        (k + 1 = 2 * R → (cohortEdge R s k).inp k = retireOf (.P B))) := by
  obtain ⟨hc, ha, b, hwd⟩ := h
  have hc' := c0Step R hR s k hc
  rcases extStepOfWin R hR s k hc hw with ⟨he, hls⟩ | ⟨hk0, he⟩ | ⟨B, he, hrest⟩
  · left
    refine ⟨⟨hc', ha, b, by rw [he, hwd]⟩, fun B hB => ?_, hls⟩
    rw [he] at hB
    have := congrArg List.length hB
    simp at this
  · left
    refine ⟨⟨hc', ha, b + 1, by rw [he, hwd, List.append_assoc]; rfl⟩, fun B hB => ?_,
      fun h _ => by omega, fun h => by omega⟩
    rw [he] at hB
    have := congrArg List.length hB
    simp [blk] at this
    omega
  · right
    refine ⟨B, he, ?_⟩
    rw [hwd] at he
    obtain ⟨Y, hY⟩ := extEndsBlk R (by omega) (cohortEdge R s k) hc'
    by_cases h0 : a = 0
    · subst h0
      rw [grpCons] at he
      simp only [List.replicate_zero, List.nil_append, blk, List.cons_append,
        List.cons.injEq] at he
      obtain ⟨hB, hr⟩ := he
      refine ⟨by rw [← hB]; rfl, ?_, hrest⟩
      rw [if_pos rfl]
      refine ⟨hc', by omega, ?_⟩
      cases b with
      | zero =>
          exfalso
          simp [grp] at hr
          exact noTailRep R (R - 1) Y (by rw [hr, hY])
      | succ b => exact ⟨b, by rw [← hr]⟩
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at he
      obtain ⟨hB, hr⟩ := he
      refine ⟨by rw [← hB]; simp, ?_, hrest⟩
      rw [if_neg (by omega)]
      exact ⟨hc', by omega, b, by rw [← hr]; rfl⟩

/-- **A cut without pending packets inherits the source alignment.** Consumer: the renewal
preparation `V` (start at the packet-only cut). -/
theorem alignExtOfSrc (R a : Nat) (s : CohortLane) (h : Align R a s.out)
    (hnp : ∀ q, R ≤ q → q < 2 * R → isPI (s.inp q) = false) : AlignExt R a s := by
  obtain ⟨hc, ha, b, hw⟩ := h
  have hp : pendWord R s = [] := by
    unfold pendWord
    have : ∀ m, m ≤ R → gFrom (fun j => pwI (s.inp (R + j))) m = [] := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
          intro hm
          simp only [gFrom]
          rw [ih (by omega)]
          have := hnp (R + m) (by omega) (by omega)
          revert this
          cases s.inp (R + m) with
          | P T => intro h; cases h
          | _ => intro _; rfl
    exact this R (Nat.le_refl _)
  exact ⟨hc, ha, b, by unfold extWord; rw [hp, hw]; rfl⟩

end L3.PacketMomentPending

#print axioms L3.PacketMomentPending.finPend
#print axioms L3.PacketMomentPending.extStep
#print axioms L3.PacketMomentPending.alignExtStep
#print axioms L3.PacketMomentPending.alignExtOfSrc

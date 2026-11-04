import Leader.L3.Bank.RepairDigitPacketQueueExport
import Leader.L3.Bank.RepairDigitPacketMomentTrialEnd
import Leader.L3.Bank.RepairDigitPacketMomentGroupLabels

/-!
# Lemma e-packet, I2b: the export map over the settled run of the renewal trial

repair.tex 1306-1307: the pending queue is a consecutive suffix of the accepted serial stream.
`L3.DigitPacketQueue.QueueAt` states it for the moving packets (`P` cells) of the target block.
Here the clause is extended to the **held** cells, moving or settled (`P` or `S`), during the
renewal trial (`L3.PacketMomentV.VShape`: no carry, a settled non-tail suffix, empty or moving
cells to its left), and read at the aligned group:

* `HeldQ R s G Ex χ`: every held target cell `q` holds the operand of the recorded delimiter
  export `χ q`; a held cell further left was exported later; no gap (every recorded delimiter
  export at or after the export of a held cell is the export of a held cell).
* Lane rows under the trial shape: `heldFin` (keep, or a move into an empty cell; a settlement
  keeps both cells held with their atoms), `heldTerm` (the last cell keeps its atom or drops out,
  and it is the oldest), `heldDel` (an accepted export, stamped `clock + 1`, becomes the leftmost
  held cell).
* `heldStep`: every coupled letter from a layout state in the trial shape with ordered audit
  frames carries `HeldAt` (with a new witness).
* `heldTrialMoment`: the renewal trial from `VIAt R m` reaches `VTA R m` with `HeldAt`, with the
  bound of `L3.PacketMomentTrialEnd.vAlignAtCoupled`.
* `heldOfPacketQueue`: at a trial state without settled cells (`VShape R 0`: the packet-only cut,
  the cleared window after the front) `HeldAt` is `QueueAt` of the reached-state invariant
  `PacketQueue`.
* `heldGroup`: **at the aligned group, `χ (R + j)` is a recorded delimiter export carrying the
  input atom of target cell `R + j`, the exports are stamped in decreasing order of `j`, and every
  recorded delimiter export stamped at or after `χ (2R - 1)` is one of them.**
-/

namespace L3.PacketMomentHeldQueue

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.DigitPacketRelease
open L3.DigitPacketOrder
open L3.DigitPacketQueue
open L3.DigitPacketQueueStep
open L3.DigitPacketQueueRows
open L3.DigitPacketQueueExport
open L3.PacketMomentRelease
open L3.PacketMomentU
open L3.PacketMomentPending
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentFinish
open L3.PacketMomentCells
open L3.PacketMomentGroupLabels
open L3.PacketMomentTrialEnd

section Lane

variable {c : Compiled} {n : Nat}

/-! ### The clause on the held cells of the masked lane -/

/-- A held target input: a moving or a settled packet. Consumer: `HeldQ`. -/
def held : BankRepairDigitInSh → Bool
  | .P _ => true
  | .S _ => true
  | _ => false

/-- **The fourth clause on the held cells.** `G q` is the lane input ghost of target cell `q`,
`Ex` the set of recorded delimiter exports. Consumer: `HeldAt` and every row lemma. -/
def HeldQ (R : Nat) (s : CohortLane) (G : Nat → Option (DigitAtom n))
    (Ex : DigitExport c n → Prop) (χ : Nat → DigitExport c n) : Prop :=
  (∀ q, R ≤ q → q < 2 * R → held (s.inp q) = true → Ex (χ q) ∧ G q = (χ q).operand) ∧
    (∀ q q', R ≤ q → q < q' → q' < 2 * R → held (s.inp q) = true → held (s.inp q') = true →
      (χ q').time < (χ q).time) ∧
    (∀ q y, R ≤ q → q < 2 * R → held (s.inp q) = true → Ex y → (χ q).time ≤ y.time →
      ∃ q', R ≤ q' ∧ q' < 2 * R ∧ held (s.inp q') = true ∧ y = χ q')

/-- **Relabelling** (`L3.DigitPacketQueueRows.queueTransfer` on the held cells). Consumer:
`heldSame`, `heldFin`, `heldTerm`. -/
theorem heldTransfer (R : Nat) (s s' : CohortLane) (G G' : Nat → Option (DigitAtom n))
    (Ex Ex' : DigitExport c n → Prop) (χ : Nat → DigitExport c n) (σ : Nat → Nat)
    (h1 : ∀ q, R ≤ q → q < 2 * R → held (s'.inp q) = true →
      R ≤ σ q ∧ σ q < 2 * R ∧ held (s.inp (σ q)) = true ∧ G' q = G (σ q))
    (h2 : ∀ q q', R ≤ q → q < q' → q' < 2 * R → held (s'.inp q) = true →
      held (s'.inp q') = true → σ q < σ q')
    (h3 : ∀ p, R ≤ p → p < 2 * R → held (s.inp p) = true →
      (∃ q, R ≤ q ∧ q < 2 * R ∧ held (s'.inp q) = true ∧ σ q = p) ∨
      (∀ q, R ≤ q → q < 2 * R → held (s'.inp q) = true → σ q < p))
    (hex : ∀ y, Ex' y ↔ Ex y) (h : HeldQ R s G Ex χ) :
    HeldQ R s' G' Ex' (fun q => χ (σ q)) := by
  obtain ⟨c1, c2, c3⟩ := h
  refine ⟨fun q hq1 hq2 hp => ?_, fun q q' hq hlt hq' hp hp' => ?_,
    fun q y hq1 hq2 hp hy ht => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h1 q hq1 hq2 hp
    obtain ⟨b1, b2⟩ := c1 (σ q) a1 a2 a3
    exact ⟨(hex _).2 b1, by rw [a4]; exact b2⟩
  · obtain ⟨a1, -, a3, -⟩ := h1 q hq (by omega) hp
    obtain ⟨-, b2, b3, -⟩ := h1 q' (by omega) hq' hp'
    exact c2 (σ q) (σ q') a1 (h2 q q' hq hlt hq' hp hp') b2 a3 b3
  · obtain ⟨a1, a2, a3, -⟩ := h1 q hq1 hq2 hp
    obtain ⟨p, p1, p2, p3, hyp⟩ := c3 (σ q) y a1 a2 a3 ((hex y).1 hy) ht
    have ht0 : (χ (σ q)).time ≤ (χ p).time := by rw [← hyp]; exact ht
    rcases h3 p p1 p2 p3 with ⟨q', e1, e2, e3, e4⟩ | hr
    · exact ⟨q', e1, e2, e3, by show y = χ (σ q'); rw [hyp, e4]⟩
    · have hlt := hr q hq1 hq2 hp
      have := c2 (σ q) p a1 hlt p2 a3 p3
      omega

/-- **Same labels.** Consumer: the far, pipe and keep rows. -/
theorem heldSame (R : Nat) (s s' : CohortLane) (G G' : Nat → Option (DigitAtom n))
    (Ex Ex' : DigitExport c n → Prop) (χ : Nat → DigitExport c n)
    (hp : ∀ q, R ≤ q → q < 2 * R → held (s'.inp q) = held (s.inp q))
    (hg : ∀ q, R ≤ q → q < 2 * R → held (s.inp q) = true → G' q = G q)
    (hex : ∀ y, Ex' y ↔ Ex y) (h : HeldQ R s G Ex χ) : HeldQ R s' G' Ex' χ :=
  heldTransfer R s s' G G' Ex Ex' χ id
    (fun q h1 h2 hq => ⟨h1, h2, by show held (s.inp q) = true; rw [← hp q h1 h2]; exact hq,
      hg q h1 h2 (by rw [← hp q h1 h2]; exact hq)⟩)
    (fun _ _ _ hlt _ _ _ => hlt)
    (fun p h1 h2 hq => Or.inl ⟨p, h1, h2, by rw [hp p h1 h2]; exact hq, rfl⟩) hex h

/-- With no settled target cell the held clause is the moving-packet clause. Consumer:
`heldOfPacketQueue`. -/
theorem heldOfPk (R : Nat) (s : CohortLane) (G : Nat → Option (DigitAtom n))
    (Ex : DigitExport c n → Prop) (χ : Nat → DigitExport c n)
    (hq : ∀ q, R ≤ q → q < 2 * R → held (s.inp q) = pk (s.inp q))
    (h : QueueLane R s G Ex χ) : HeldQ R s G Ex χ := by
  obtain ⟨c1, c2, c3⟩ := h
  refine ⟨fun q h1 h2 hp => c1 q h1 h2 (by rw [← hq q h1 h2]; exact hp),
    fun q q' h1 hlt h2 hp hp' => c2 q q' h1 hlt h2 (by rw [← hq q h1 (by omega)]; exact hp)
      (by rw [← hq q' (by omega) h2]; exact hp'),
    fun q y h1 h2 hp hy ht => ?_⟩
  obtain ⟨q', p1, p2, p3, p4⟩ := c3 q y h1 h2 (by rw [← hq q h1 h2]; exact hp) hy ht
  exact ⟨q', p1, p2, by rw [hq q' p1 p2]; exact p3, p4⟩

/-! ### The literal cells under the trial shape -/

/-- **One input-motion edge on two carry-free cells of the trial shape**: both cells keep their
held status and atoms (a settlement keeps the packet in place with its atom), or a moving packet
moves into an empty cell with its atom. Consumer: `heldFin`. -/
theorem heldFinCell (bx : Bool) (ix iy : BankRepairDigitInSh) (gxi gyi : Option (DigitAtom n))
    (hx1 : ix ≠ .X) (hx2 : ix ≠ .S true) (hy : iy ≠ .X)
    (hs : shS ix = true → bx = false ∧ shS iy = true) :
    (held (bankRepairDigitFinStep bx ix false iy false).1 = held ix ∧
      (held ix = true → (ghostFinIn bx ix false iy false gxi gyi).1 = gxi) ∧
      held (bankRepairDigitFinStep bx ix false iy false).2.2.1 = held iy ∧
      (held iy = true → (ghostFinIn bx ix false iy false gxi gyi).2 = gyi)) ∨
    (held ix = true ∧ held iy = false ∧ held (bankRepairDigitFinStep bx ix false iy false).1 = false ∧
      held (bankRepairDigitFinStep bx ix false iy false).2.2.1 = true ∧
      (ghostFinIn bx ix false iy false gxi gyi).2 = gxi) := by
  cases bx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitFinStep, ghostFinIn, finInX, finInY, finInYFree, finXP, finYX, finYP,
      shS, held] at hx1 hx2 hy hs ⊢

/-- **The terminal row on the last cell**: it keeps its held status and atom, or it is no longer
held. Consumer: `heldTerm`. -/
theorem heldTermCell (ix : BankRepairDigitInSh) (gxi : Option (DigitAtom n)) :
    (held (cohortTermStep ix false).1 = held ix ∧
      (held ix = true → ghostTermIn ix false gxi = gxi)) ∨
    held (cohortTermStep ix false).1 = false := by
  rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> simp [cohortTermStep, ghostTermIn, held]

/-- **The delivery row on a carry-free border**: no acceptance leaves the border input alone;
acceptance takes an empty border to a held one. Consumer: `heldDel`. -/
theorem heldDelCell (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) :
    (delAccept ox iy false = false ∧ (bankRepairDigitDelStep ox iy false).2.1 = iy) ∨
      (delAccept ox iy false = true ∧ iy = .E ∧
        held (bankRepairDigitDelStep ox iy false).2.1 = true) := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitDelStep, delAccept, held]

/-- Without acceptance a carry-free border keeps its input atom. Consumer: `heldExport`. -/
theorem ghostDelKeep (st : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n)) (hd : delAccept ox iy false = false) :
    (ghostDel st ox iy false gxo gyi).2 = gyi := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [ghostDel, delAccept] at hd ⊢

/-- The cell forms of the trial shape. Consumer: `heldFin`. -/
theorem shapeForm (i : BankRepairDigitInSh) (h : i = .E ∨ isPI i = true ∨ i = .S false) :
    i ≠ .X ∧ i ≠ .S true := by
  revert h
  cases i <;> simp [isPI]

/-- Consumer: `heldFin`. -/
theorem shapeCell (R i : Nat) (s : CohortLane) (hS : VShape R i s) (q : Nat) (h1 : R ≤ q)
    (h2 : q < 2 * R) : s.inp q = .E ∨ isPI (s.inp q) = true ∨ s.inp q = .S false := by
  by_cases hq : 2 * R - i ≤ q
  · exact Or.inr (Or.inr ((hS.2 q h1 h2).2.1 hq))
  · rcases (hS.2 q h1 h2).2.2 (by omega) with he | hp
    · exact Or.inl he
    · exact Or.inr (Or.inl hp)

/-! ### The rows on the masked lane -/

/-- **The Fin rows on the held cells** of a trial-shape lane. Consumer: `heldFinC`. -/
theorem heldFin (R k : Nat) (s : CohortLane) (hk1 : R ≤ k) (hk2 : k + 1 < 2 * R) (i : Nat)
    (hS : VShape R i s) (G G' : Nat → Option (DigitAtom n)) (Ex Ex' : DigitExport c n → Prop)
    (χ : Nat → DigitExport c n)
    (hGk : G' k = (ghostFinIn (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
      (s.live (k + 1)) (G k) (G (k + 1))).1)
    (hGk1 : G' (k + 1) = (ghostFinIn (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
      (s.live (k + 1)) (G k) (G (k + 1))).2)
    (hG : ∀ q, q < 2 * R → q ≠ k → q ≠ k + 1 → G' q = G q)
    (hex : ∀ y, Ex' y ↔ Ex y) (h : HeldQ R s G Ex χ) :
    ∃ χ' : Nat → DigitExport c n, HeldQ R (cohortEdge R s k) G' Ex' χ' := by
  obtain ⟨⟨ik, -⟩, ⟨ik1, -⟩, ifar⟩ := finCells R k s hk1 hk2
  have hf : finOf R s k = bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k)
      (s.inp (k + 1)) (s.live (k + 1)) := rfl
  rw [hf] at ik ik1
  have l0 := (hS.2 k hk1 (by omega)).1
  have l1 := (hS.2 (k + 1) (by omega) hk2).1
  rw [l0, l1] at ik ik1 hGk hGk1
  have fx := shapeForm _ (shapeCell R i s hS k hk1 (by omega))
  have fy := shapeForm _ (shapeCell R i s hS (k + 1) (by omega) hk2)
  have hsx : shS (s.inp k) = true → decide (k = R) = false ∧ shS (s.inp (k + 1)) = true := by
    intro hsk
    by_cases hq : 2 * R - i ≤ k
    · have hi := hS.1
      refine ⟨decide_eq_false (by omega), ?_⟩
      rw [(hS.2 (k + 1) (by omega) hk2).2.1 (by omega)]
      rfl
    · exfalso
      rcases (hS.2 k hk1 (by omega)).2.2 (by omega) with he | hp
      · rw [he] at hsk; cases hsk
      · revert hsk hp; cases s.inp k <;> simp [isPI, shS]
  have hfar : ∀ q, q ≠ k → q ≠ k + 1 → (cohortEdge R s k).inp q = s.inp q :=
    fun q e1 e2 => (ifar q (fun hh => hh.elim e1 e2)).1
  rcases heldFinCell (decide (k = R)) (s.inp k) (s.inp (k + 1)) (G k) (G (k + 1)) fx.1 fx.2
      fy.1 hsx with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4, a5⟩
  · -- keep
    refine ⟨χ, heldSame R s _ G G' Ex Ex' χ ?_ ?_ hex h⟩
    · intro q _ _
      by_cases e1 : q = k
      · rw [e1, ik]; exact a1
      · by_cases e2 : q = k + 1
        · rw [e2, ik1]; exact a3
        · rw [hfar q e1 e2]
    · intro q _ hq2 hp
      by_cases e1 : q = k
      · rw [e1, hGk]; rw [e1] at hp; exact a2 hp
      · by_cases e2 : q = k + 1
        · rw [e2, hGk1]; rw [e2] at hp; exact a4 hp
        · exact hG q hq2 e1 e2
  · -- move: the packet at `k` enters the empty cell `k + 1` with its atom
    have nk : ∀ r, held ((cohortEdge R s k).inp r) = true → r ≠ k := by
      intro r hr e
      rw [e, ik, a3] at hr
      exact absurd hr (by decide)
    refine ⟨_, heldTransfer R s _ G G' Ex Ex' χ (fun q => if q = k + 1 then k else q)
      ?_ ?_ ?_ hex h⟩
    · intro q hq1 hq2 hp
      show R ≤ (if q = k + 1 then k else q) ∧ (if q = k + 1 then k else q) < 2 * R ∧
        held (s.inp (if q = k + 1 then k else q)) = true ∧
          G' q = G (if q = k + 1 then k else q)
      by_cases e1 : q = k + 1
      · rw [if_pos e1]
        refine ⟨hk1, by omega, a1, ?_⟩
        rw [e1, hGk1]
        exact a5
      · rw [if_neg e1]
        have e2 := nk q hp
        rw [hfar q e2 e1] at hp
        exact ⟨hq1, hq2, hp, hG q hq2 e2 e1⟩
    · intro q q' _ hlt _ hp hp'
      have e1 := nk q hp
      have e2 := nk q' hp'
      show (if q = k + 1 then k else q) < (if q' = k + 1 then k else q')
      split <;> split <;> omega
    · intro p hp1 hp2 hp
      by_cases e1 : p = k
      · refine Or.inl ⟨k + 1, by omega, hk2, by rw [ik1]; exact a4, ?_⟩
        show (if k + 1 = k + 1 then k else k + 1) = p
        rw [if_pos rfl, e1]
      · by_cases e2 : p = k + 1
        · rw [e2, a2] at hp
          exact absurd hp (by decide)
        · refine Or.inl ⟨p, hp1, hp2, by rw [hfar p e1 e2]; exact hp, ?_⟩
          show (if p = k + 1 then k else p) = p
          rw [if_neg e2]

/-- **The terminal row on the held cells**: the last cell keeps its atom or drops out; it is the
rightmost, hence the oldest, held cell. Consumer: `heldTermC`. -/
theorem heldTerm (R k : Nat) (hk : k + 1 = 2 * R) (s : CohortLane) (hlv : s.live k = false)
    (G G' : Nat → Option (DigitAtom n)) (Ex Ex' : DigitExport c n → Prop)
    (χ : Nat → DigitExport c n) (hGk : G' k = ghostTermIn (s.inp k) (s.live k) (G k))
    (hG : ∀ q, q < k → G' q = G q) (hex : ∀ y, Ex' y ↔ Ex y) (h : HeldQ R s G Ex χ) :
    ∃ χ' : Nat → DigitExport c n, HeldQ R (cohortEdge R s k) G' Ex' χ' := by
  obtain ⟨hi, -⟩ := L3.DigitPacketRelease.edgeTerm R k s hk
  have ik : (cohortEdge R s k).inp k = (cohortTermStep (s.inp k) (s.live k)).1 := by
    rw [hi]; simp [cohortUpd]
  have hfar : ∀ q, q ≠ k → (cohortEdge R s k).inp q = s.inp q := by
    intro q e; rw [hi]; simp [cohortUpd, e]
  rw [hlv] at ik hGk
  refine ⟨_, heldTransfer R s _ G G' Ex Ex' χ id ?_ ?_ ?_ hex h⟩
  · intro q hq1 hq2 hp
    show R ≤ q ∧ q < 2 * R ∧ held (s.inp q) = true ∧ G' q = G q
    by_cases e : q = k
    · rw [e] at hp ⊢
      rcases heldTermCell (s.inp k) (G k) with ⟨b1, b2⟩ | b1
      · rw [ik, b1] at hp
        exact ⟨by omega, by omega, hp, by rw [hGk]; exact b2 hp⟩
      · rw [ik, b1] at hp
        exact absurd hp (by decide)
    · rw [hfar q e] at hp
      exact ⟨hq1, hq2, hp, hG q (by omega)⟩
  · intro _ _ _ hlt _ _ _
    exact hlt
  · intro p hp1 hp2 hp
    by_cases e : p = k
    · rcases heldTermCell (s.inp k) (G k) with ⟨b1, -⟩ | b1
      · refine Or.inl ⟨k, by omega, by omega, ?_, by show k = p; exact e.symm⟩
        rw [ik, b1, ← e]
        exact hp
      · refine Or.inr (fun q _ hq2 hq => ?_)
        have hqk : q ≠ k := by
          intro ee
          rw [ee, ik, b1] at hq
          exact absurd hq (by decide)
        show q < p
        omega
    · exact Or.inl ⟨p, hp1, hp2, by rw [hfar p e]; exact hp, rfl⟩

/-- **The export row on the held cells.** On the delivery edge `k = R - 1` with a carry-free
border: without acceptance the clause is carried with the same witness; with acceptance of a new
export `ex`, newer than every recorded one, whose operand is the new border ghost, the clause
holds with `χ' R = ex`. Consumer: `heldExport`. -/
theorem heldDel (R k : Nat) (hk : k + 1 = R) (s : CohortLane) (hlv : s.live R = false)
    (G G' : Nat → Option (DigitAtom n)) (Ex Ex' : DigitExport c n → Prop)
    (χ : Nat → DigitExport c n) (t : Nat)
    (hG : ∀ q, R < q → q < 2 * R → G' q = G q)
    (hold : ∀ y, Ex y → y.time < t)
    (hrej : delAccept (s.out k) (s.inp R) (s.live R) = false →
      G' R = G R ∧ ∀ y, Ex' y ↔ Ex y)
    (hacc : delAccept (s.out k) (s.inp R) (s.live R) = true →
      ∃ ex : DigitExport c n, ex.time = t ∧ G' R = ex.operand ∧ ∀ y, Ex' y ↔ Ex y ∨ y = ex)
    (h : HeldQ R s G Ex χ) :
    ∃ χ' : Nat → DigitExport c n, HeldQ R (cohortEdge R s k) G' Ex' χ' := by
  subst hk
  obtain ⟨hi, -⟩ := L3.DigitPacketRelease.edgeDel (k + 1) k s rfl
  have iR : (cohortEdge (k + 1) s k).inp (k + 1) =
      (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.1 := by
    rw [hi]; simp [cohortUpd]
  have hfar : ∀ q, q ≠ k + 1 → (cohortEdge (k + 1) s k).inp q = s.inp q := by
    intro q e; rw [hi]; simp [cohortUpd, e]
  rw [hlv] at iR hrej hacc
  rcases heldDelCell (s.out k) (s.inp (k + 1)) with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩
  · obtain ⟨g1, g2⟩ := hrej a1
    refine ⟨χ, heldSame (k + 1) s _ G G' Ex Ex' χ ?_ ?_ g2 h⟩
    · intro q _ _
      by_cases e : q = k + 1
      · rw [e, iR, a2]
      · rw [hfar q e]
    · intro q hq1 hq2 _
      by_cases e : q = k + 1
      · rw [e]; exact g1
      · exact hG q (by omega) hq2
  · obtain ⟨ex, ht, hGR, hEx⟩ := hacc a1
    obtain ⟨c1, c2, c3⟩ := h
    have old0 : held (s.inp (k + 1)) = false := by rw [a2]; rfl
    refine ⟨fun q => if q = k + 1 then ex else χ q, ?_, ?_, ?_⟩
    · intro q hq1 hq2 hp
      show Ex' (if q = k + 1 then ex else χ q) ∧ G' q = (if q = k + 1 then ex else χ q).operand
      by_cases e : q = k + 1
      · rw [if_pos e, e]
        exact ⟨(hEx ex).2 (Or.inr rfl), hGR⟩
      · rw [if_neg e]
        rw [hfar q e] at hp
        obtain ⟨b1, b2⟩ := c1 q hq1 hq2 hp
        exact ⟨(hEx _).2 (Or.inl b1), by rw [hG q (by omega) hq2]; exact b2⟩
    · intro q q' hq hlt hq' hp hp'
      show (if q' = k + 1 then ex else χ q').time < (if q = k + 1 then ex else χ q).time
      have e' : q' ≠ k + 1 := by omega
      rw [if_neg e']
      rw [hfar q' e'] at hp'
      by_cases e : q = k + 1
      · rw [if_pos e, ht]
        exact hold _ (c1 q' (by omega) hq' hp').1
      · rw [if_neg e]
        rw [hfar q e] at hp
        exact c2 q q' hq hlt hq' hp hp'
    · intro q y hq1 hq2 hp hy hty
      have hty' : (if q = k + 1 then ex else χ q).time ≤ y.time := hty
      rcases (hEx y).1 hy with hy0 | hy1
      · by_cases e : q = k + 1
        · rw [if_pos e, ht] at hty'
          have := hold y hy0
          omega
        · rw [if_neg e] at hty'
          rw [hfar q e] at hp
          obtain ⟨q', p1, p2, p3, p4⟩ := c3 q y hq1 hq2 hp hy0 hty'
          have e' : q' ≠ k + 1 := by
            intro ee
            rw [ee, old0] at p3
            exact absurd p3 (by decide)
          refine ⟨q', p1, p2, by rw [hfar q' e']; exact p3, ?_⟩
          show y = (if q' = k + 1 then ex else χ q')
          rw [if_neg e']
          exact p4
      · refine ⟨k + 1, Nat.le_refl _, by omega, by rw [iR]; exact a3, ?_⟩
        show y = (if k + 1 = k + 1 then ex else χ (k + 1))
        rw [if_pos rfl]
        exact hy1

/-! ### The trial on the lane -/

/-- **One letter of the trial**: the outcome `VTA R m`, or the trial at the same index (the step
of `L3.PacketMomentTrialEnd.vAlignAt`). Consumer: `heldTrialStep`. -/
theorem trialNext (R m : Nat) (hR : 3 ≤ R) (s : CohortLane) (o : Option Nat) (h : VIAt R m s) :
    VTA R m (cohortLaneStep R s o) ∨ VIAt R m (cohortLaneStep R s o) := by
  obtain ⟨a', i', hai', hA', hS', hm'⟩ := h
  cases o with
  | none => exact Or.inr ⟨a', i', hai', hA', hS', hm'⟩
  | some k =>
    rcases vStepIdx R hR s k a' i' hai' hA' hS' with ⟨ha0, hi1, ht⟩ | hv
    · left
      subst ha0
      have hidx : vIdx R 0 i' = i' := by
        unfold vIdx; rw [if_neg (by omega)]; omega
      have hw := winKeep R (by omega) s (some k) (shapeWin R i' s hS')
      refine ⟨?_, vtAtAlign R i' (by omega) s k hA' hS' hi1 ht, hw⟩
      show VTAt R m (cohortEdge R s k)
      rw [← hm', hidx]
      exact ht
    · right; rw [← hm']; exact hv

end Lane

/-! ### On the coupled chain -/

section Coupled

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-- **The held clause of a coupled state** with witness `χ`. Consumer: `heldStep`,
`heldTrialMoment`, `heldGroup`. -/
def HeldAt (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  HeldQ R (laneOfState ring hbank root lane src R x)
    (fun q => (laneCells ring root lane src x.2.current q).input)
    (DelExport ring root lane src R x.2) χ

/-- **The export row on the coupled chain** (the coupling of
`L3.DigitPacketQueueExport.queueExport`). Consumer: `heldStep`. -/
theorem heldExport (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (hk : k + 1 = R)
    (hlv : (laneOfState ring hbank root lane src R x).live R = false)
    (hfo : AuditFrameOrder x.2) (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : HeldAt ring hbank root lane src R x χ) :
    ∃ χ' : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      HeldAt ring hbank root lane src R (nxt ring hn hbank x (digitSite ring root (src + k))) χ' := by
  subst hk
  have hl := (laneStep ring hn hbank root lane src (k + 1) hR hsrc hend x hx
    (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src (k + 1) hend k (by omega)] at hl
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hx
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root x.1 hL
    (digitSite ring root (src + k))
  have hbX' : (pairW (piD x.1.val.1 (digitSite ring root (src + k))).word
      (piD x.1.val.1 (digitSite ring root (src + (k + 1)))).word).1.beta =
      (piD x.1.val.1 (digitSite ring root (src + k))).word.beta := hbX
  have hbY' : (pairW (piD x.1.val.1 (digitSite ring root (src + k))).word
      (piD x.1.val.1 (digitSite ring root (src + (k + 1)))).word).2.beta =
      (piD x.1.val.1 (digitSite ring root (src + (k + 1)))).word.beta := hbY
  have hlx := bankRepairDigitSiteNonroot ring root (piD x.1.val.1) hroot (src + k) (by omega)
    (by omega)
  have hly := bankRepairDigitSiteNonroot ring root (piD x.1.val.1) hroot (src + (k + 1))
    (by omega) (by omega)
  have hmx : laneMarkerX lane (piD x.1.val.1 (digitSite ring root (src + k)))
      (piD x.1.val.1 (digitSite ring root (src + (k + 1)))) = false := by
    rw [laneMarkerXBeta lane _ _ hbX']
    exact hbF k (by omega) (by omega) (by omega)
  have hmy : laneMarkerY lane (piD x.1.val.1 (digitSite ring root (src + k)))
      (piD x.1.val.1 (digitSite ring root (src + (k + 1)))) = true := by
    rw [laneMarkerYBeta lane _ _ hbY']
    exact hbR
  obtain ⟨hrow, -⟩ := rowDelD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD x.1.val.1 (digitSite ring root (src + k)))
    (piD x.1.val.1 (digitSite ring root (src + (k + 1))))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + (k + 1)))) hlx hly hmx hmy
  have hexp := delExportedD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD x.1.val.1 (digitSite ring root (src + k)))
    (piD x.1.val.1 (digitSite ring root (src + (k + 1))))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + (k + 1)))) hlx hly hmx hmy
  have pO := projOut ring root lane src (k + 1) (piD x.1.val.1) k (by omega)
  have pI := projIn ring root lane src (k + 1) (piD x.1.val.1) (k + 1) (Nat.le_refl _) (by omega)
  have pL := projLive ring root lane src (k + 1) (piD x.1.val.1) (k + 1) (Nat.le_refl _)
    (by omega)
  rw [← pO, ← pI, ← pL] at hrow hexp
  have hlv' : (cohortProj ring root lane src (k + 1) (piD x.1.val.1)).live (k + 1) = false := hlv
  have he : digitSite ring root (src + k) = digitSite ring root (src + (k + 1 - 1)) := by
    rw [Nat.add_sub_cancel]
  unfold HeldAt
  rw [hl]
  refine heldDel (k + 1) k rfl (cohortProj ring root lane src (k + 1) (piD x.1.val.1)) hlv'
    (fun q => (laneCells ring root lane src x.2.current q).input) _
    (DelExport ring root lane src (k + 1) x.2) _ χ (x.2.clock + 1) ?_ ?_ ?_ ?_ h
  · intro q hq1 hq2
    show (laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
      (digitSite ring root (src + k))).current (digitSite ring root (src + q)))).input =
      (laneGhost lane (x.2.current (digitSite ring root (src + q)))).input
    rw [curFar ring (piD x.1.val.1) x.2 _ _
      (siteNe ring root _ _ (by omega) (by omega) (by omega))
      (siteNe ring root (src + q) (src + k + 1) (by omega) (by omega) (by omega))]
  · intro y hy
    have := delExportClock ring root lane src (k + 1) x.2 hfo y hy
    omega
  · intro hd
    refine ⟨?_, fun y => ?_⟩
    · show (laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
        (digitSite ring root (src + k))).current
          (ring.rightNeighbor (digitSite ring root (src + k))))).input =
        (laneGhost lane (x.2.current (digitSite ring root (src + (k + 1))))).input
      rw [curY ring (by omega)]
      rw [hlv'] at hd hrow
      exact (congrArg Prod.snd hrow).trans (ghostDelKeep _ _ _ _ _ hd)
    · refine (delExportStep ring root lane src (k + 1) (piD x.1.val.1) x.2 _ he y).trans ?_
      refine ⟨fun hy => hy.elim id (fun hN => ?_), Or.inl⟩
      have hexp' : (digitReceiptLane lane (svcAt ring (piD x.1.val.1) x.2
          (digitSite ring root (src + k)))).exported.isSome =
          delAccept ((cohortProj ring root lane src (k + 1) (piD x.1.val.1)).out k)
            ((cohortProj ring root lane src (k + 1) (piD x.1.val.1)).inp (k + 1))
            ((cohortProj ring root lane src (k + 1) (piD x.1.val.1)).live (k + 1)) := hexp
      rw [hN.2.2.1, hd] at hexp'
      exact absurd hexp' (by simp)
  · intro hd
    obtain ⟨T, hD, hiy, hky'⟩ := delAcceptCases _ _ _ hd
    rw [pO] at hD
    rw [pI] at hiy
    rw [pL] at hky'
    obtain ⟨ex, e1, e2, e3, e4, e5, e6, -, e8⟩ := recordDeliveryD lane (x.2.clock + 1)
      (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
      (piD x.1.val.1 (digitSite ring root (src + k)))
      (piD x.1.val.1 (digitSite ring root (src + (k + 1))))
      (x.2.current (digitSite ring root (src + k)))
      (x.2.current (digitSite ring root (src + (k + 1)))) hlx hly hmy hD hiy hky'
    have e1' : (digitReceiptLane lane (svcAt ring (piD x.1.val.1) x.2
        (digitSite ring root (src + k)))).exported = some ex := e1
    refine ⟨ex, e3, ?_, fun y => ?_⟩
    · show (laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
        (digitSite ring root (src + k))).current
          (ring.rightNeighbor (digitSite ring root (src + k))))).input = ex.operand
      rw [curY ring (by omega)]
      exact e8.trans e2.symm
    · refine (delExportStep ring root lane src (k + 1) (piD x.1.val.1) x.2 _ he y).trans ?_
      refine or_congr Iff.rfl ⟨fun hN => Option.some.inj (hN.2.2.1.symm.trans e1'), ?_⟩
      intro hy
      rw [hy]
      exact ⟨e3, e5, e1', e4, e6⟩

/-- **The Fin rows on the coupled chain.** Consumer: `heldStep`. -/
theorem heldFinC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (hk1 : R ≤ k) (hk2 : k + 1 < 2 * R)
    (i : Nat) (hS : VShape R i (laneOfState ring hbank root lane src R x))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : HeldAt ring hbank root lane src R x χ) :
    ∃ χ' : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      HeldAt ring hbank root lane src R (nxt ring hn hbank x (digitSite ring root (src + k))) χ' := by
  have hl := (laneStep ring hn hbank root lane src R hR hsrc hend x hx
    (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hl
  have hc := cellsFin ring hn hbank root lane src R hR hsrc hend x hx k hk1 hk2
  unfold HeldAt
  rw [hl]
  exact heldFin R k _ hk1 hk2 i hS
    (fun q => (laneCells ring root lane src x.2.current q).input)
    (fun q => (laneCells ring root lane src
      (nxt ring hn hbank x (digitSite ring root (src + k))).2.current q).input)
    (DelExport ring root lane src R x.2) _ χ (congrArg Prod.fst hc) (congrArg Prod.snd hc)
    (fun q hq e1 e2 => congrArg DigitLaneGhost.input
      (cellsFar ring hn hbank root lane src R hend x k (by omega) q hq e1 e2))
    (fun y => delExportOff ring root lane src R (piD x.1.val.1) x.2
      (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega)) y) h

/-- **The terminal row on the coupled chain.** Consumer: `heldStep`. -/
theorem heldTermC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (hk : k + 1 = 2 * R)
    (hlv : (laneOfState ring hbank root lane src R x).live k = false)
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : HeldAt ring hbank root lane src R x χ) :
    ∃ χ' : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      HeldAt ring hbank root lane src R (nxt ring hn hbank x (digitSite ring root (src + k))) χ' := by
  have hl := (laneStep ring hn hbank root lane src R hR hsrc hend x hx
    (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hl
  have hc := cellsTerm ring hn hbank root lane src R hR hsrc hend x hx k hk
  unfold HeldAt
  rw [hl]
  exact heldTerm R k hk _ hlv
    (fun q => (laneCells ring root lane src x.2.current q).input)
    (fun q => (laneCells ring root lane src
      (nxt ring hn hbank x (digitSite ring root (src + k))).2.current q).input)
    (DelExport ring root lane src R x.2) _ χ hc
    (fun q hq => congrArg DigitLaneGhost.input
      (cellsFar ring hn hbank root lane src R hend x k (by omega) q (by omega) (by omega)
        (by omega)))
    (fun y => delExportOff ring root lane src R (piD x.1.val.1) x.2
      (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega)) y) h

/-- **The step of the held clause.** Every coupled letter, from a layout state in the trial
shape with ordered audit frames, carries `HeldAt` (with a new witness). Consumer:
`heldTrialStep`. -/
theorem heldStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (hfo : AuditFrameOrder x.2) (i : Nat)
    (hS : VShape R i (laneOfState ring hbank root lane src R x))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : HeldAt ring hbank root lane src R x χ) (e : Fin n) :
    ∃ χ' : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      HeldAt ring hbank root lane src R (nxt ring hn hbank x e) χ' := by
  have hl := (laneStep ring hn hbank root lane src R hR hsrc hend x hx e).2
  rcases hE : cohortEdgeOf root src R e with _ | k
  · -- off the pair
    rw [hE] at hl
    have hne : e ≠ digitSite ring root (src + (R - 1)) := by
      intro he
      rw [he, cohortEdgeOfSite ring root src R hend (R - 1) (by omega)] at hE
      cases hE
    refine ⟨χ, ?_⟩
    unfold HeldAt
    rw [hl]
    exact heldSame R (laneOfState ring hbank root lane src R x)
      (cohortLaneStep R (laneOfState ring hbank root lane src R x) none)
      (fun q => (laneCells ring root lane src x.2.current q).input)
      (fun q => (laneCells ring root lane src (nxt ring hn hbank x e).2.current q).input)
      (DelExport ring root lane src R x.2) (DelExport ring root lane src R (nxt ring hn hbank x e).2)
      χ (fun q _ _ => by rfl)
      (fun q hq1 hq2 _ => congrArg DigitLaneGhost.input
        ((cellsOff ring hn hbank root lane src R hR hsrc hend x hx e hE q hq2).2 (by omega)))
      (fun y => delExportOff ring root lane src R (piD x.1.val.1) x.2 e hne y) h
  · obtain ⟨hk, rfl⟩ := L3.PacketMomentLabels.edgeOfSome ring root src R e k hE
    by_cases h1 : k + 1 < R
    · -- a source pipe edge
      rw [hE] at hl
      refine ⟨χ, ?_⟩
      unfold HeldAt
      rw [hl]
      have hp := (L3.DigitPacketRelease.edgePipe R k (laneOfState ring hbank root lane src R x) h1).1
      exact heldSame R (laneOfState ring hbank root lane src R x)
        (cohortLaneStep R (laneOfState ring hbank root lane src R x) (some k))
        (fun q => (laneCells ring root lane src x.2.current q).input)
        (fun q => (laneCells ring root lane src
          (nxt ring hn hbank x (digitSite ring root (src + k))).2.current q).input)
        (DelExport ring root lane src R x.2)
        (DelExport ring root lane src R (nxt ring hn hbank x (digitSite ring root (src + k))).2)
        χ (fun q _ _ => by
          show held ((cohortEdge R (laneOfState ring hbank root lane src R x) k).inp q) = _
          rw [hp])
        (fun q hq1 hq2 _ => congrArg DigitLaneGhost.input
          (cellsFar ring hn hbank root lane src R hend x k hk q hq2 (by omega) (by omega)))
        (fun y => delExportOff ring root lane src R (piD x.1.val.1) x.2
          (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega))
          y) h
    · by_cases h2 : k + 1 = R
      · exact heldExport ring hn hbank root lane src R hR hsrc hend x hx k h2
          ((hS.2 R (Nat.le_refl _) (by omega)).1) hfo χ h
      · by_cases h3 : k + 1 = 2 * R
        · exact heldTermC ring hn hbank root lane src R hR hsrc hend x hx k h3
            ((hS.2 k (by omega) (by omega)).1) χ h
        · exact heldFinC ring hn hbank root lane src R hR hsrc hend x hx k (by omega) (by omega)
            i hS χ h

/-! ### The renewal trial with the held clause -/

/-- The trial at index `m` (or its outcome) with ordered frames and the held clause. Consumer:
`heldTrialMoment`. -/
def HeldTrial (m : Nat)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  CohortLayout ring hbank root src R y.1 ∧ AuditFrameOrder y.2 ∧
    (VIAt R m (laneOfState ring hbank root lane src R y) ∨
      VTA R m (laneOfState ring hbank root lane src R y)) ∧
    ∃ χ, HeldAt ring hbank root lane src R y χ

/-- **The held trial is kept off its outcome.** Consumer: `heldTrialMoment`. -/
theorem heldTrialStep (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : HeldTrial ring hbank root lane src R m y)
    (hnt : ¬ VTA R m (laneOfState ring hbank root lane src R y)) :
    HeldTrial ring hbank root lane src R m (nxt ring hn hbank y e) := by
  obtain ⟨hy, hfo, ht, χ, hq⟩ := h
  have hvi : VIAt R m (laneOfState ring hbank root lane src R y) := by
    rcases ht with ht | ht
    · exact ht
    · exact absurd ht hnt
  have hnext := trialNext R m hR _ (cohortEdgeOf root src R e) hvi
  obtain ⟨_, i, _, _, hS, _⟩ := hvi
  obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R (by omega) hsrc hend y hy e
  obtain ⟨χ', hq'⟩ := heldStep ring hn hbank root lane src R (by omega) hsrc hend y hy hfo i hS
    χ hq e
  refine ⟨h1, auditFrameOrderStep ring (piD y.1.val.1) y.2 e hfo, ?_, χ', hq'⟩
  rw [h2]
  rcases hnext with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **The renewal trial carries the held clause to its outcome.** From a layout state with
ordered frames, whose lane is a trial state of index `m` and which satisfies the held clause, the
outcome `VTA R m` is reached with the held clause, `E[z^T] ≤ w^{(R+2)(2R+2)}` (the bound of
`vAlignAtCoupled`). Consumer: the aligned completion (`heldGroup` at `m = R - 1`), the race
class. -/
theorem heldTrialMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (hfo : AuditFrameOrder x.2)
    (hs : VIAt R m (laneOfState ring hbank root lane src R x))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hq : HeldAt ring hbank root lane src R x χ) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => VTA R m (laneOfState ring hbank root lane src R y) ∧
        HeldTrial ring hbank root lane src R m y) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x :=
  momentKeepUntil _ _ _ N _ _
    (fun y e h hnt => heldTrialStep ring hn hbank root lane src R hR hsrc hend m y e h hnt) x
    ⟨hx, hfo, Or.inl hs, χ, hq⟩
    (vAlignAtCoupled ring hn hbank root lane src R hR hsrc hend N hN m x hx hs)

/-! ### Entry and the aligned group -/

/-- **Entry**: at a trial state without settled target cells (the packet-only cut, the cleared
window after the front), the held clause is the moving-packet clause of the reached-state
invariant `PacketQueue`. Consumer: the composition of the trial with
`L3.DigitPacketQueueExport.packetQueueWord`. -/
theorem heldOfPacketQueue
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hS : VShape R 0 (laneOfState ring hbank root lane src R x))
    (hq : PacketQueue ring root lane src R (piD x.1.val.1) x.2) :
    ∃ χ, HeldAt ring hbank root lane src R x χ := by
  obtain ⟨-, χ, h⟩ := hq
  rw [queueAtIff] at h
  refine ⟨χ, heldOfPk R _ _ _ χ (fun q h1 h2 => ?_) h⟩
  have hc : (laneOfState ring hbank root lane src R x).inp q = .E ∨
      isPI ((laneOfState ring hbank root lane src R x).inp q) = true :=
    (hS.2 q h1 h2).2.2 (by omega)
  revert hc
  cases (laneOfState ring hbank root lane src R x).inp q <;> simp [isPI, held, pk]

/-- **The aligned group holds a consecutive run of the delimiter stream.** At the aligned group
with the held clause: `χ (R + j)` (`j < R`) is a recorded delimiter export whose operand is the
input atom of target cell `R + j`; the exports are stamped in decreasing order of `j`; and every
recorded delimiter export stamped at or after `χ (2R - 1)` is one of them. Consumer: the aligned
completion (the export clauses of `DigitCompletion`). -/
theorem heldGroup (hR : 1 ≤ R)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hg : AGroup R (laneOfState ring hbank root lane src R y))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : HeldAt ring hbank root lane src R y χ) :
    (∀ j, j < R → DelExport ring root lane src R y.2 (χ (R + j)) ∧
      (laneCells ring root lane src y.2.current (R + j)).input = (χ (R + j)).operand) ∧
    (∀ j j', j < j' → j' < R → (χ (R + j')).time < (χ (R + j)).time) ∧
    (∀ ex, DelExport ring root lane src R y.2 ex → (χ (2 * R - 1)).time ≤ ex.time →
      ∃ j, j < R ∧ ex = χ (R + j)) := by
  have hall : ∀ q, R ≤ q → q < 2 * R →
      held ((laneOfState ring hbank root lane src R y).inp q) = true := by
    intro q h1 h2
    obtain ⟨-, hc⟩ := hg
    by_cases hq : q = R
    · rw [(hc q h1 h2).2.1 (by omega)]; rfl
    · rw [(hc q h1 h2).2.2.1 (by omega)]; rfl
  obtain ⟨c1, c2, c3⟩ := h
  refine ⟨fun j hj => c1 (R + j) (by omega) (by omega) (hall _ (by omega) (by omega)),
    fun j j' hjj hj' => c2 (R + j) (R + j') (by omega) (by omega) (by omega)
      (hall _ (by omega) (by omega)) (hall _ (by omega) (by omega)),
    fun ex hex ht => ?_⟩
  obtain ⟨q', p1, p2, -, p4⟩ := c3 (2 * R - 1) ex (by omega) (by omega)
    (hall _ (by omega) (by omega)) hex ht
  refine ⟨q' - R, by omega, ?_⟩
  rw [p4, show R + (q' - R) = q' by omega]

end Coupled

end L3.PacketMomentHeldQueue

#print axioms L3.PacketMomentHeldQueue.heldTransfer
#print axioms L3.PacketMomentHeldQueue.heldSame
#print axioms L3.PacketMomentHeldQueue.heldOfPk
#print axioms L3.PacketMomentHeldQueue.heldFinCell
#print axioms L3.PacketMomentHeldQueue.heldTermCell
#print axioms L3.PacketMomentHeldQueue.heldDelCell
#print axioms L3.PacketMomentHeldQueue.ghostDelKeep
#print axioms L3.PacketMomentHeldQueue.heldFin
#print axioms L3.PacketMomentHeldQueue.heldTerm
#print axioms L3.PacketMomentHeldQueue.heldDel
#print axioms L3.PacketMomentHeldQueue.trialNext
#print axioms L3.PacketMomentHeldQueue.heldExport
#print axioms L3.PacketMomentHeldQueue.heldFinC
#print axioms L3.PacketMomentHeldQueue.heldTermC
#print axioms L3.PacketMomentHeldQueue.heldStep
#print axioms L3.PacketMomentHeldQueue.heldTrialStep
#print axioms L3.PacketMomentHeldQueue.heldTrialMoment
#print axioms L3.PacketMomentHeldQueue.heldOfPacketQueue
#print axioms L3.PacketMomentHeldQueue.heldGroup

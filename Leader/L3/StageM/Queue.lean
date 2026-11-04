import Leader.L3.StageM.Masked
import Leader.L3.Bank.RepairDigitPacketQueueExport

/-!
# Stage M (R10c, Lemma e-max): the queue clause of the post-entrance exports, on the lane

The fourth clause `QueueLane` (`L3.DigitPacketQueueRows`) is run on the masked lane
`maskL R s G` (`L3.StageMMasked`): old pending packets and carry cells are masked to `X`, so the
pending packets of the masked lane are exactly the exports accepted after the entrance, and the
masked lane is in the packet-order class (`maskOrder`, from `maskWin`). The lane rows
`queueLaneFin`, `queueLaneTerm`, `queueLaneDel` then apply to the masked lane, and `maskStep` moves
the result to the masked lane after the letter.

* `orderOfWin`: the window invariants `Inv ∧ Barrier` of a lane give `PacketOrder` (cut at the
  first obstacle). Used on the masked lane here and on the lane at the Stage M stop.
* `finAtomMask`, `delAcceptMask`, `pkMask`: on a cell that is pending in the masked lane after the
  letter, the lane ghost atom of the real row equals the masked one; acceptance is the same.
* `queueMaskFin`, `queueMaskTerm`, `queueMaskDel`, `queueMaskFrame`: the lane rows of the clause on
  the masked lane, with the hypotheses in the shape the coupled rows provide for the real lane.
* `queueMaskInit` (no masked packet at the entrance) and `queueMaskStop` (no old pending packet and
  the fresh-carry invariant: the masked clause is the clause of the lane).

Consumer: `L3.StageMQueueCoupled` (the coupled step) and the Stage M assembly.
-/

namespace L3.StageMQueue

set_option autoImplicit false

open L3
open L3.MarkedCells
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.GhostBridge
open L3.DigitPacketRelease
open L3.DigitPacketOrder
open L3.DigitPacketQueue
open L3.DigitPacketQueueRows
open L3.DigitPacketQueueExport
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentPending
open L3.StageMOldRank
open L3.StageMGhostLane
open L3.StageMMasked

variable {c : Compiled} {n : Nat}

/-! ### Packet order from the window invariants -/

/-- The first obstacle of a window, or `r`. Consumer: `orderOfWin`. -/
theorem firstObEx (w : Nat → Cell) :
    ∀ r : Nat, ∃ f, f ≤ r ∧ (∀ j, j < f → obC (w j) = false) ∧ (f < r → obC (w f) = true)
  | 0 => ⟨0, Nat.le_refl _, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun h => absurd h (Nat.lt_irrefl _)⟩
  | r + 1 => by
      obtain ⟨f, h1, h2, h3⟩ := firstObEx w r
      by_cases hf : f < r
      · exact ⟨f, by omega, h2, fun _ => h3 hf⟩
      · have hfr : f = r := by omega
        subst hfr
        cases hb : obC (w f) with
        | true => exact ⟨f, by omega, h2, fun _ => hb⟩
        | false =>
            refine ⟨f + 1, Nat.le_refl _, fun j hj => ?_, fun h => absurd h (Nat.lt_irrefl _)⟩
            by_cases hjf : j = f
            · rw [hjf]; exact hb
            · exact h2 j (by omega)

/-- A lane cell that is not an obstacle is clean. Consumer: `orderOfWin`. -/
theorem cleanOfOb (i : BankRepairDigitInSh) (l : Bool) (h : obC (liftC i l) = false) :
    CleanT i l := by
  cases l <;> rcases i with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    first
    | exact ⟨rfl, Or.inl rfl⟩
    | exact ⟨rfl, Or.inr ⟨_, rfl⟩⟩
    | exact absurd h (by decide)

/-- A pending lane cell. Consumer: `orderOfWin`. -/
theorem pendOfP (i : BankRepairDigitInSh) (l : Bool) (T : Bool) (h : i = .P T) :
    (liftC i l).i.isP = true := by
  subst h; cases T <;> rfl

/-- A live lane cell carries a fresh carry. Consumer: `orderOfWin`. -/
theorem freshOfLive (i : BankRepairDigitInSh) (l : Bool) (h : l = true) :
    (liftC i l).c = .fresh := by
  subst h; rfl

/-- An obstacle that is empty or pending carries a fresh carry. Consumer: `orderOfWin`. -/
theorem freshOfObEP (i : BankRepairDigitInSh) (l : Bool) (h : obC (liftC i l) = true)
    (he : EP (liftC i l)) : (liftC i l).c = .fresh := by
  cases l <;> rcases i with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    first
    | rfl
    | exact absurd h (by decide)
    | (exfalso; rcases he with he | he <;> exact absurd he (by decide))

/-- An empty host is the empty input. Consumer: `orderOfWin`. -/
theorem emptyOfE (i : BankRepairDigitInSh) (l : Bool) (h : (liftC i l).i = .e) : i = .E := by
  cases l <;> rcases i with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> first | rfl | exact absurd h (by decide)

/-- **The window invariants give packet order**, cut at the first obstacle: every pending input is
left of every obstacle (`Barrier`), and a live carry is the unique fresh one with an empty host and
only empty or pending inputs on its left (`Inv`). Consumer: `maskOrder` and the Stage M stop
(`PacketOrder` of `WidthLaneCutC`). -/
theorem orderOfWin (R : Nat) (s : CohortLane) (hI : Inv R (winOf R s))
    (hB : Barrier R (winOf R s)) : ∃ m, OrderAt R s m := by
  obtain ⟨f, hfR, hlow, hat⟩ := firstObEx (winOf R s) R
  refine ⟨R + f, by omega, by omega, fun q h1 h2 => ?_, fun q h1 h2 => ?_,
    fun q h1 h2 => ?_, fun h1 hl => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, q = R + j := ⟨q - R, by omega⟩
    exact cleanOfOb _ _ (hlow j (by omega))
  · obtain ⟨j, rfl⟩ : ∃ j, q = R + j := ⟨q - R, by omega⟩
    intro T hT
    have hP : (winOf R s j).i.isP = true := pendOfP _ _ T hT
    have := hB j f (by omega) (by omega) hP (hat (by omega))
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, q = R + j := ⟨q - R, by omega⟩
    cases hl : s.live (R + j) with
    | false => rfl
    | true =>
        exfalso
        have hfj : (winOf R s j).c = .fresh := freshOfLive _ _ hl
        have hep := (hI.1 j (by omega) hfj).2 f (by omega)
        have hff : (winOf R s f).c = .fresh := freshOfObEP _ _ (hat (by omega)) hep
        have := hI.2 f j (by omega) (by omega) hff hfj
        omega
  · have hff : (winOf R s f).c = .fresh := freshOfLive _ _ hl
    exact emptyOfE _ _ (hI.1 f (by omega) hff).1

/-- **The masked lane is in the packet-order class.** Consumer: `queueMaskFin`,
`queueMaskDel`. -/
theorem maskOrder (R : Nat) (s : CohortLane) (G : Nat → OCell) (hg : GhostOf R s G)
    (hn : NewBar R G) : ∃ m, OrderAt R (maskL R s G) m :=
  orderOfWin R _ (maskWin R s G hg hn).1 (maskWin R s G hg hn).2

/-! ### The masked rows, atom by atom -/

/-- Equal pending tail bits give equal pending tests. Consumer: `maskPk`. -/
theorem pkOfPw (a b : BankRepairDigitInSh) (h : pwI a = pwI b) : pk a = pk b := by
  cases a <;> cases b <;> first | rfl | (simp [pwI] at h)

/-- A masked pending input is an unmasked carry-free pending input. Consumer: `queueMaskDel`. -/
theorem pkMask (i : BankRepairDigitInSh) (k o : Bool) (h : pk (maskIn i k o) = true) :
    k = false ∧ pk i = true := by
  cases k <;> cases o <;> rcases i with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

/-- Masking does not change acceptance at the border. Consumer: `queueMaskDel`. -/
theorem delAcceptMask (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky oy : Bool) :
    delAccept ox (maskIn iy ky oy) false = delAccept ox iy ky := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> cases oy <;>
    rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rfl

/-- **The Fin row atoms, masked.** On a cell pending in the masked lane after an input-motion
edge, the lane ghost atom of the real row equals that of the masked row. Consumer:
`queueMaskFin`. -/
theorem finAtomMask (bx : Bool) (ix iy : BankRepairDigitInSh) (kx ky ox oy : Bool)
    (gx gy : Option (DigitAtom n)) :
    (pk (bankRepairDigitFinStep bx (maskIn ix kx ox) false (maskIn iy ky oy) false).1 = true →
      (ghostFinIn bx ix kx iy ky gx gy).1 =
        (ghostFinIn bx (maskIn ix kx ox) false (maskIn iy ky oy) false gx gy).1) ∧
    (pk (bankRepairDigitFinStep bx (maskIn ix kx ox) false (maskIn iy ky oy) false).2.2.1 =
        true →
      (ghostFinIn bx ix kx iy ky gx gy).2 =
        (ghostFinIn bx (maskIn ix kx ox) false (maskIn iy ky oy) false gx gy).2) := by
  cases bx <;> cases kx <;> cases ky <;> cases ox <;> cases oy <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [maskIn, bankRepairDigitFinStep, pk, ghostFinIn, finInX, finInY, finInYFree, finXP,
      finYX, finYP, shS]

/-- The masked lane after a letter has the pending cells of the letter on the masked lane.
Consumer: the rows below. -/
theorem maskPk (R : Nat) (s : CohortLane) (G : Nat → OCell) (hg : GhostOf R s G) (k q : Nat)
    (h1 : R ≤ q) (h2 : q < 2 * R) :
    pk ((maskL R (cohortEdge R s k) (oApply R G (laneMove R s k))).inp q) =
      pk ((cohortEdge R (maskL R s G) k).inp q) := by
  obtain ⟨j, rfl⟩ : ∃ j, q = R + j := ⟨q - R, by omega⟩
  exact pkOfPw _ _ ((maskStep R s G hg k (fun _ => none)).2.1 j (by omega)).1

/-- A target input of the masked lane at `R + p + 1`. Consumer: `queueMaskFin`. -/
theorem maskInpSucc (R : Nat) (s : CohortLane) (G : Nat → OCell) (p : Nat) :
    (maskL R s G).inp (R + p + 1) =
      maskIn (s.inp (R + p + 1)) (s.live (R + p + 1)) (G (p + 1)).o := by
  have h := maskInp R s G (p + 1)
  rw [← Nat.add_assoc] at h
  exact h

/-- Replace two adjacent atoms. Consumer: `queueMaskFin`. -/
def updPair {α : Type} (A : Nat → α) (k : Nat) (a b : α) : Nat → α :=
  fun q => if q = k then a else if q = k + 1 then b else A q

/-- The Fin row atoms of a lane at edge `k`. Consumer: `queueMaskFin`. -/
def finAtoms (R : Nat) (s0 : CohortLane) (A : Nat → Option (DigitAtom n)) (k : Nat) :
    Option (DigitAtom n) × Option (DigitAtom n) :=
  ghostFinIn (decide (k = R)) (s0.inp k) (s0.live k) (s0.inp (k + 1)) (s0.live (k + 1)) (A k)
    (A (k + 1))

/-! ### The rows on the masked lane -/

/-- **The Fin rows on the masked lane.** The hypotheses are those of `queueLaneFin` for the real
lane; the conclusion is the clause on the masked lane after the letter. Consumer:
`L3.StageMQueueCoupled.maskQueueFin`. -/
theorem queueMaskFin (R k : Nat) (s : CohortLane) (G : Nat → OCell) (hg : GhostOf R s G)
    (hn : NewBar R G) (hk1 : R ≤ k) (hk2 : k + 1 < 2 * R)
    (A A' : Nat → Option (DigitAtom n)) (Ex Ex' : DigitExport c n → Prop)
    (χ : Nat → DigitExport c n)
    (hGk : A' k = (ghostFinIn (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
      (s.live (k + 1)) (A k) (A (k + 1))).1)
    (hGk1 : A' (k + 1) = (ghostFinIn (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
      (s.live (k + 1)) (A k) (A (k + 1))).2)
    (hG : ∀ q, q < 2 * R → q ≠ k → q ≠ k + 1 → A' q = A q)
    (hex : ∀ y, Ex' y ↔ Ex y) (h : QueueLane R (maskL R s G) A Ex χ) :
    ∃ χ' : Nat → DigitExport c n,
      QueueLane R (maskL R (cohortEdge R s k) (oApply R G (laneMove R s k))) A' Ex' χ' := by
  obtain ⟨m, hm⟩ := maskOrder R s G hg hn
  obtain ⟨p, rfl⟩ : ∃ p, k = R + p := ⟨k - R, by omega⟩
  have hx0 := maskInp R s G p
  have hy0 := maskInpSucc R s G p
  have hlx : (maskL R s G).live (R + p) = false := maskLive R s G _ (by omega)
  have hly : (maskL R s G).live (R + p + 1) = false := maskLive R s G _ (by omega)
  let s0 := maskL R s G
  have u0 : updPair A' (R + p) (finAtoms R s0 A (R + p)).1 (finAtoms R s0 A (R + p)).2 (R + p) =
      (finAtoms R s0 A (R + p)).1 := if_pos rfl
  have u1 : updPair A' (R + p) (finAtoms R s0 A (R + p)).1 (finAtoms R s0 A (R + p)).2
      (R + p + 1) = (finAtoms R s0 A (R + p)).2 := (if_neg (by omega)).trans (if_pos rfl)
  have u2 : ∀ q, q ≠ R + p → q ≠ R + p + 1 →
      updPair A' (R + p) (finAtoms R s0 A (R + p)).1 (finAtoms R s0 A (R + p)).2 q = A' q :=
    fun q e1 e2 => (if_neg e1).trans (if_neg e2)
  obtain ⟨χ', hq⟩ := queueLaneFin R (R + p) m (maskL R s G) hk1 hk2 hm A
    (updPair A' (R + p) (finAtoms R s0 A (R + p)).1 (finAtoms R s0 A (R + p)).2) Ex Ex' χ
    u0 u1 (fun q hq e1 e2 => (u2 q e1 e2).trans (hG q hq e1 e2)) hex h
  obtain ⟨⟨c0, -⟩, ⟨c1, -⟩, coth⟩ := finCells R (R + p) (maskL R s G) hk1 hk2
  refine ⟨χ', queueSame R _ _ _ _ Ex' Ex' χ' (fun q h1 h2 => maskPk R s G hg _ q h1 h2)
    (fun q h1 h2 hp => ?_) (fun _ => Iff.rfl) hq⟩
  by_cases e1 : q = R + p
  · subst e1
    rw [c0] at hp
    unfold finOf at hp
    rw [hx0, hlx, hy0, hly] at hp
    rw [u0, hGk]
    show _ = (ghostFinIn (decide (R + p = R)) ((maskL R s G).inp (R + p))
      ((maskL R s G).live (R + p)) ((maskL R s G).inp (R + p + 1))
      ((maskL R s G).live (R + p + 1)) (A (R + p)) (A (R + p + 1))).1
    rw [hx0, hlx, hy0, hly]
    exact (finAtomMask _ _ _ _ _ _ _ _ _).1 hp
  · by_cases e2 : q = R + p + 1
    · subst e2
      rw [c1] at hp
      unfold finOf at hp
      rw [hx0, hlx, hy0, hly] at hp
      rw [u1, hGk1]
      show _ = (ghostFinIn (decide (R + p = R)) ((maskL R s G).inp (R + p))
        ((maskL R s G).live (R + p)) ((maskL R s G).inp (R + p + 1))
        ((maskL R s G).live (R + p + 1)) (A (R + p)) (A (R + p + 1))).2
      rw [hx0, hlx, hy0, hly]
      exact (finAtomMask _ _ _ _ _ _ _ _ _).2 hp
    · rw [u2 q e1 e2]

/-- **The terminal row on the masked lane.** Consumer:
`L3.StageMQueueCoupled.maskQueueTerm`. -/
theorem queueMaskTerm (R k : Nat) (hk : k + 1 = 2 * R) (s : CohortLane) (G : Nat → OCell)
    (hg : GhostOf R s G) (A A' : Nat → Option (DigitAtom n)) (Ex Ex' : DigitExport c n → Prop)
    (χ : Nat → DigitExport c n) (hG : ∀ q, q < k → A' q = A q)
    (hex : ∀ y, Ex' y ↔ Ex y) (h : QueueLane R (maskL R s G) A Ex χ) :
    ∃ χ' : Nat → DigitExport c n,
      QueueLane R (maskL R (cohortEdge R s k) (oApply R G (laneMove R s k))) A' Ex' χ' := by
  obtain ⟨χ', hq⟩ := queueLaneTerm R k hk (maskL R s G) A A' Ex Ex' χ hG hex h
  exact ⟨χ', queueSame R _ _ _ _ Ex' Ex' χ' (fun q h1 h2 => maskPk R s G hg _ q h1 h2)
    (fun _ _ _ _ => rfl) (fun _ => Iff.rfl) hq⟩

/-- **The export row on the masked lane.** The hypotheses are those of `queueLaneDel` for the
real lane (rejection keeps a carry-free pending border atom); acceptance is the same on the masked
lane. Consumer: `L3.StageMQueueCoupled.maskQueueExport`. -/
theorem queueMaskDel (R k : Nat) (hk : k + 1 = R) (s : CohortLane) (G : Nat → OCell)
    (hg : GhostOf R s G) (hn : NewBar R G) (A A' : Nat → Option (DigitAtom n))
    (Ex Ex' : DigitExport c n → Prop) (χ : Nat → DigitExport c n) (t : Nat)
    (hG : ∀ q, R < q → q < 2 * R → A' q = A q) (hold : ∀ y, Ex y → y.time < t)
    (hrej : delAccept (s.out k) (s.inp R) (s.live R) = false →
      (s.live R = false → pk (s.inp R) = true → A' R = A R) ∧ ∀ y, Ex' y ↔ Ex y)
    (hacc : delAccept (s.out k) (s.inp R) (s.live R) = true →
      ∃ ex : DigitExport c n, ex.time = t ∧ A' R = ex.operand ∧ ∀ y, Ex' y ↔ Ex y ∨ y = ex)
    (h : QueueLane R (maskL R s G) A Ex χ) :
    ∃ χ' : Nat → DigitExport c n,
      QueueLane R (maskL R (cohortEdge R s k) (oApply R G (laneMove R s k))) A' Ex' χ' := by
  obtain ⟨m, hm⟩ := maskOrder R s G hg hn
  have hmi : (maskL R s G).inp R = maskIn (s.inp R) (s.live R) (G 0).o := by
    have := maskInp R s G 0
    rw [Nat.add_zero] at this
    exact this
  have hml : (maskL R s G).live R = false := maskLive R s G R (Nat.le_refl _)
  have hdA : delAccept ((maskL R s G).out k) ((maskL R s G).inp R) ((maskL R s G).live R) =
      delAccept (s.out k) (s.inp R) (s.live R) := by
    rw [hmi, hml]
    exact delAcceptMask (s.out k) (s.inp R) (s.live R) (G 0).o
  obtain ⟨χ', hq⟩ := queueLaneDel R k m hk (maskL R s G) hm A A' Ex Ex' χ t hG hold
    (fun hd => by
      rw [hdA] at hd
      obtain ⟨g1, g2⟩ := hrej hd
      refine ⟨fun hp => ?_, g2⟩
      rw [hmi] at hp
      obtain ⟨hl, hpk⟩ := pkMask _ _ _ hp
      exact g1 hl hpk)
    (fun hd => by
      rw [hdA] at hd
      exact hacc hd)
    h
  exact ⟨χ', queueSame R _ _ _ _ Ex' Ex' χ' (fun q h1 h2 => maskPk R s G hg _ q h1 h2)
    (fun _ _ _ _ => rfl) (fun _ => Iff.rfl) hq⟩

/-- The masked lane of a source-pipe letter is the masked lane before it. Consumer:
`L3.StageMQueueCoupled.maskQueueFar`. -/
theorem maskPipe (R k : Nat) (s : CohortLane) (G : Nat → OCell) (h : k + 1 < R) :
    (maskL R (cohortEdge R s k) (oApply R G (laneMove R s k))).inp = (maskL R s G).inp := by
  have hm : laneMove R s k = .frame := by unfold laneMove; rw [if_pos h]
  rw [hm]
  obtain ⟨h1, h2⟩ := edgePipe R k s h
  funext q
  show (if R ≤ q then maskIn ((cohortEdge R s k).inp q) ((cohortEdge R s k).live q)
    (G (q - R)).o else (cohortEdge R s k).inp q) =
    (if R ≤ q then maskIn (s.inp q) (s.live q) (G (q - R)).o else s.inp q)
  rw [h1, h2]

/-- **Letters that leave the masked target inputs alone.** Consumer:
`L3.StageMQueueCoupled.maskQueueFar`. -/
theorem queueMaskFrame (R : Nat) (s s' : CohortLane) (G G' : Nat → OCell)
    (hinp : ∀ q, R ≤ q → q < 2 * R → (maskL R s' G').inp q = (maskL R s G).inp q)
    (A A' : Nat → Option (DigitAtom n)) (hA : ∀ q, R ≤ q → q < 2 * R → A' q = A q)
    (Ex Ex' : DigitExport c n → Prop) (hex : ∀ y, Ex' y ↔ Ex y) (χ : Nat → DigitExport c n)
    (h : QueueLane R (maskL R s G) A Ex χ) : QueueLane R (maskL R s' G') A' Ex' χ :=
  queueSame R _ _ A A' Ex Ex' χ (fun q h1 h2 => by rw [hinp q h1 h2])
    (fun q h1 h2 _ => hA q h1 h2) hex h

/-! ### Start and stop -/

/-- **Start**: at the entrance every pending packet is old, so the masked lane has no pending
packet and the clause holds for every witness. Consumer: the Stage M assembly. -/
theorem queueMaskInit (R : Nat) (s : CohortLane) (A : Nat → Option (DigitAtom n))
    (Ex : DigitExport c n → Prop) (χ : Nat → DigitExport c n) :
    QueueLane R (maskL R s (ghostInit R s)) A Ex χ := by
  have hnp : ∀ q, R ≤ q → q < 2 * R → pk ((maskL R s (ghostInit R s)).inp q) = false := by
    intro q h1 _
    obtain ⟨j, rfl⟩ : ∃ j, q = R + j := ⟨q - R, by omega⟩
    rw [maskInp]
    show pk (maskIn (s.inp (R + j)) (s.live (R + j)) (cellIn (s.inp (R + j))).isP) = false
    unfold maskIn
    cases s.live (R + j) <;> rcases s.inp (R + j) with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rfl
  refine ⟨fun q h1 h2 hp => ?_, fun q q' h1 h2 h3 hp _ => ?_, fun q _ h1 h2 hp => ?_⟩
  · rw [hnp q h1 h2] at hp; cases hp
  · rw [hnp q h1 (by omega)] at hp; cases hp
  · rw [hnp q h1 h2] at hp; cases hp

/-- **A masked cell at the stop**: with no old pending packet and the fresh-carry invariant, the
masked input is the input, or a live carry over an empty input. Consumer: `queueMaskStop`. -/
theorem maskStopCell (R : Nat) (s : CohortLane) (G : Nat → OCell) (hg : GhostOf R s G)
    (hold : ∀ j, j < R → oP (G j) = false) (hinv : Inv R (winOf R s)) (j : Nat) (hj : j < R) :
    maskIn (s.inp (R + j)) (s.live (R + j)) (G j).o = s.inp (R + j) ∨
      (s.live (R + j) = true ∧ s.inp (R + j) = .E) := by
  have hc := ghostCell R s G hg j
  have ho := hold j hj
  have hE : s.live (R + j) = true → s.inp (R + j) = .E := by
    intro hl
    have hf : (winOf R s j).c = .fresh := by
      show (liftC (s.inp (R + j)) (s.live (R + j))).c = .fresh
      rw [hl]; rfl
    exact emptyOfE _ _ (hinv.1 j hj hf).1
  have hoP : ∀ T, s.inp (R + j) = .P T → (G j).o = false := by
    intro T hT
    rw [hc.1] at ho
    revert ho
    show ((G j).o && (cellIn (s.inp (R + j))).isP) = false → (G j).o = false
    rw [hT]
    cases T <;> cases (G j).o <;> simp [cellIn, Inp.isP]
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

/-- **Stop**: with no old pending packet and the fresh-carry invariant of the lane window, the
masked clause is the clause of the lane. Consumer: the Stage M assembly (`QueueAt` of
`WidthLaneCutC` by `queueAtIff`). -/
theorem queueMaskStop (R : Nat) (s : CohortLane) (G : Nat → OCell) (hg : GhostOf R s G)
    (hold : ∀ j, j < R → oP (G j) = false) (hinv : Inv R (winOf R s))
    (A : Nat → Option (DigitAtom n)) (Ex : DigitExport c n → Prop) (χ : Nat → DigitExport c n)
    (h : QueueLane R (maskL R s G) A Ex χ) : QueueLane R s A Ex χ := by
  refine queueSame R (maskL R s G) s A A Ex Ex χ (fun q h1 h2 => ?_) (fun _ _ _ _ => rfl)
    (fun _ => Iff.rfl) h
  obtain ⟨j, rfl⟩ : ∃ j, q = R + j := ⟨q - R, by omega⟩
  rw [maskInp]
  rcases maskStopCell R s G hg hold hinv j (by omega) with e | ⟨hl, hi⟩
  · rw [e]
  · rw [hl, hi] <;> rfl

end L3.StageMQueue

#print axioms L3.StageMQueue.orderOfWin
#print axioms L3.StageMQueue.finAtomMask
#print axioms L3.StageMQueue.queueMaskFin
#print axioms L3.StageMQueue.queueMaskTerm
#print axioms L3.StageMQueue.queueMaskDel
#print axioms L3.StageMQueue.queueMaskFrame
#print axioms L3.StageMQueue.queueMaskInit
#print axioms L3.StageMQueue.queueMaskStop

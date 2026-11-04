import Leader.L3.Bank.RepairDigitPacketQueueStep

/-!
# Lemma e-packet, fourth clause: the step on the target rows

repair.tex 1306-1307 (the pending queue is a consecutive suffix of the accepted serial stream),
on the target cells `src + q`, `R ≤ q < 2R`, of one lane of a complete pair.

* `QueueLane`: the clause `QueueAt` read on the masked lane, with the lane input ghosts `G` and
  the delimiter exports `Ex` as plain parameters (`queueAtIff`: the two are the same statement).
* `queueTransfer`: the clause moves along a monotone relabelling `σ` of pending cells, provided
  every pending cell that loses its label lies right of every relabelled cell.
* `finCell`: on one input-motion edge (literal rows `bankRepairDigitFinStep`, ghost rows
  `ghostFinIn`), a cell either keeps its packet with its atom, or the packet moves into an empty
  right cell with its atom, or the packet settles against a settled right cell.
* `queueLaneFin`, `queueLaneTerm`: the clause along the Fin rows (`χ` shifted one cell on a move;
  a settled packet is the rightmost pending one by `orderPaper`) and along the terminal row (the
  last cell loses its packet, which is the rightmost pending one).
* `queueTargetFin`, `queueTargetTerm`: the same on the coupled BANK x audit chain, through
  `laneStep`, `curX`/`curY`/`curFar` and the record-field rows `rowFinD`.
-/

namespace L3.DigitPacketQueueRows

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketRelease
open L3.DigitPacketOrder
open L3.DigitPacketTransport
open L3.DigitPacketQueue
open L3.DigitPacketQueueStep

variable {c : Compiled} {n : Nat}

/-! ### The clause on the masked lane -/

/-- The moving-packet test as a Boolean. Consumer: `QueueLane`. -/
def pk : BankRepairDigitInSh → Bool
  | .P _ => true
  | _ => false

/-- Consumer: `queueAtIff`. -/
theorem isPktIff (i : BankRepairDigitInSh) : IsPkt i ↔ pk i = true := by
  cases i <;> simp [IsPkt, pk]

/-- Consumer: `queueLaneFin` (the settle case reads `orderPaper`). -/
theorem pkSome (i : BankRepairDigitInSh) (h : pk i = true) : ∃ T, i = .P T := by
  cases i <;> simp [pk] at h ⊢

/-- Consumer: `queueLaneFin`. -/
theorem shSSome (i : BankRepairDigitInSh) (h : shS i = true) : ∃ T, i = .S T := by
  cases i <;> simp [shS] at h ⊢

/-- Consumer: `queueLaneFin`. -/
theorem shSNotPk (i : BankRepairDigitInSh) (h : shS i = true) : pk i = false := by
  cases i <;> simp [shS, pk] at h ⊢

/-- **The fourth clause on the masked lane.** `G q` is the lane input ghost of target cell `q`,
`Ex` the set of recorded delimiter exports. Consumer: `queueAtIff` and every row lemma. -/
def QueueLane (R : Nat) (s : CohortLane) (G : Nat → Option (DigitAtom n))
    (Ex : DigitExport c n → Prop) (χ : Nat → DigitExport c n) : Prop :=
  (∀ q, R ≤ q → q < 2 * R → pk (s.inp q) = true → Ex (χ q) ∧ G q = (χ q).operand) ∧
    (∀ q q', R ≤ q → q < q' → q' < 2 * R → pk (s.inp q) = true → pk (s.inp q') = true →
      (χ q').time < (χ q).time) ∧
    (∀ q y, R ≤ q → q < 2 * R → pk (s.inp q) = true → Ex y → (χ q).time ≤ y.time →
      ∃ q', R ≤ q' ∧ q' < 2 * R ∧ pk (s.inp q') = true ∧ y = χ q')

/-- `QueueAt` is `QueueLane` on the projection, the lane ghosts and the delimiter exports.
Consumer: `queueTargetFin`, `queueTargetTerm`, the export row. -/
theorem queueAtIff (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (χ : Nat → DigitExport c n) :
    QueueAt ring root lane src R S A χ ↔
      QueueLane R (cohortProj ring root lane src R S)
        (fun q => (laneCells ring root lane src A.current q).input)
        (DelExport ring root lane src R A) χ := by
  unfold QueueAt QueueLane
  simp only [isPktIff]

/-- **Relabelling.** The clause moves along a monotone map `σ` from new pending cells to old
pending cells carrying the atoms, when every old pending cell outside the image lies right of the
image. Consumer: `queueSame`, `queueLaneFin`, `queueLaneTerm`. -/
theorem queueTransfer (R : Nat) (s s' : CohortLane) (G G' : Nat → Option (DigitAtom n))
    (Ex Ex' : DigitExport c n → Prop) (χ : Nat → DigitExport c n) (σ : Nat → Nat)
    (h1 : ∀ q, R ≤ q → q < 2 * R → pk (s'.inp q) = true →
      R ≤ σ q ∧ σ q < 2 * R ∧ pk (s.inp (σ q)) = true ∧ G' q = G (σ q))
    (h2 : ∀ q q', R ≤ q → q < q' → q' < 2 * R → pk (s'.inp q) = true →
      pk (s'.inp q') = true → σ q < σ q')
    (h3 : ∀ p, R ≤ p → p < 2 * R → pk (s.inp p) = true →
      (∃ q, R ≤ q ∧ q < 2 * R ∧ pk (s'.inp q) = true ∧ σ q = p) ∨
      (∀ q, R ≤ q → q < 2 * R → pk (s'.inp q) = true → σ q < p))
    (hex : ∀ y, Ex' y ↔ Ex y) (h : QueueLane R s G Ex χ) :
    QueueLane R s' G' Ex' (fun q => χ (σ q)) := by
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

/-- **Same labels.** Unchanged pending cells with unchanged atoms carry the clause with the same
witness. Consumer: `queueLaneFin` (the keep case) and the export row (no acceptance). -/
theorem queueSame (R : Nat) (s s' : CohortLane) (G G' : Nat → Option (DigitAtom n))
    (Ex Ex' : DigitExport c n → Prop) (χ : Nat → DigitExport c n)
    (hp : ∀ q, R ≤ q → q < 2 * R → pk (s'.inp q) = pk (s.inp q))
    (hg : ∀ q, R ≤ q → q < 2 * R → pk (s.inp q) = true → G' q = G q)
    (hex : ∀ y, Ex' y ↔ Ex y) (h : QueueLane R s G Ex χ) : QueueLane R s' G' Ex' χ :=
  queueTransfer R s s' G G' Ex Ex' χ id
    (fun q h1 h2 hq => ⟨h1, h2, by show pk (s.inp q) = true; rw [← hp q h1 h2]; exact hq,
      hg q h1 h2 (by rw [← hp q h1 h2]; exact hq)⟩)
    (fun _ _ _ hlt _ _ _ => hlt)
    (fun p h1 h2 hq => Or.inl ⟨p, h1, h2, by rw [hp p h1 h2]; exact hq, rfl⟩) hex h

/-! ### The literal cells -/

/-- **One input-motion edge on two cells**, shapes with ghosts, given the carry clause of the
order invariant (a live carry has an empty input): keep, move into an empty cell with the atom,
or settle against a settled cell. Consumer: `queueLaneFin`. -/
theorem finCell (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi gyi : Option (DigitAtom n)) (hkx : kx = true → ix = .E)
    (hky : ky = true → iy = .E) :
    (pk (bankRepairDigitFinStep bx ix kx iy ky).1 = pk ix ∧
      (pk ix = true → (ghostFinIn bx ix kx iy ky gxi gyi).1 = gxi) ∧
      pk (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = pk iy ∧
      (pk iy = true → (ghostFinIn bx ix kx iy ky gxi gyi).2 = gyi)) ∨
    (pk ix = true ∧ iy = .E ∧ pk (bankRepairDigitFinStep bx ix kx iy ky).1 = false ∧
      pk (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = true ∧
      (ghostFinIn bx ix kx iy ky gxi gyi).2 = gxi) ∨
    (pk ix = true ∧ shS iy = true ∧ pk (bankRepairDigitFinStep bx ix kx iy ky).1 = false ∧
      pk (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = false) := by
  cases bx <;> cases kx <;> cases ky <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitFinStep, ghostFinIn, finInX, finInY, finInYFree, finXP, finYX, finYP,
      shS, pk] at hkx hky ⊢

/-- The terminal row leaves no moving packet in the last cell. Consumer: `queueLaneTerm`. -/
theorem termCell (ix : BankRepairDigitInSh) (kx : Bool) : pk (cohortTermStep ix kx).1 = false := by
  cases kx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> simp [cohortTermStep, pk]

/-! ### The rows on the masked lane -/

/-- **The Fin rows.** On an input-motion edge `k` (`R ≤ k`, `k + 1 < 2R`) of a lane in the
packet-order class, the clause holds after the edge for the lane ghosts given by `ghostFinIn` on
the two cells (others unchanged) and unchanged delimiter exports. Consumer: `queueTargetFin`. -/
theorem queueLaneFin (R k m : Nat) (s : CohortLane) (hk1 : R ≤ k) (hk2 : k + 1 < 2 * R)
    (ho : OrderAt R s m) (G G' : Nat → Option (DigitAtom n)) (Ex Ex' : DigitExport c n → Prop)
    (χ : Nat → DigitExport c n)
    (hGk : G' k = (ghostFinIn (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
      (s.live (k + 1)) (G k) (G (k + 1))).1)
    (hGk1 : G' (k + 1) = (ghostFinIn (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
      (s.live (k + 1)) (G k) (G (k + 1))).2)
    (hG : ∀ q, q < 2 * R → q ≠ k → q ≠ k + 1 → G' q = G q)
    (hex : ∀ y, Ex' y ↔ Ex y) (h : QueueLane R s G Ex χ) :
    ∃ χ' : Nat → DigitExport c n, QueueLane R (cohortEdge R s k) G' Ex' χ' := by
  obtain ⟨⟨ik, -⟩, ⟨ik1, -⟩, ifar⟩ := finCells R k s hk1 hk2
  have hf : finOf R s k = bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k)
      (s.inp (k + 1)) (s.live (k + 1)) := rfl
  rw [hf] at ik ik1
  have hlvE : ∀ q, R ≤ q → q < 2 * R → s.live q = true → s.inp q = .E :=
    fun q h1 h2 hl => ((orderPaper R m s ho).2 q h1 h2 hl).1
  have hfar : ∀ q, q ≠ k → q ≠ k + 1 → (cohortEdge R s k).inp q = s.inp q :=
    fun q e1 e2 => (ifar q (fun hh => hh.elim e1 e2)).1
  rcases finCell (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1)) (s.live (k + 1))
      (G k) (G (k + 1)) (hlvE k hk1 (by omega)) (hlvE (k + 1) (by omega) hk2) with
    ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4, a5⟩ | ⟨a1, a2, a3, a4⟩
  · -- keep
    refine ⟨χ, queueSame R s _ G G' Ex Ex' χ ?_ ?_ hex h⟩
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
    have nk : ∀ r, pk ((cohortEdge R s k).inp r) = true → r ≠ k := by
      intro r hr e
      rw [e, ik, a3] at hr
      exact absurd hr (by decide)
    refine ⟨_, queueTransfer R s _ G G' Ex Ex' χ (fun q => if q = k + 1 then k else q)
      ?_ ?_ ?_ hex h⟩
    · intro q hq1 hq2 hp
      show R ≤ (if q = k + 1 then k else q) ∧ (if q = k + 1 then k else q) < 2 * R ∧
        pk (s.inp (if q = k + 1 then k else q)) = true ∧ G' q = G (if q = k + 1 then k else q)
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
  · -- settle: the packet at `k` is the rightmost pending one
    have nk : ∀ r, pk ((cohortEdge R s k).inp r) = true → r ≠ k ∧ r ≠ k + 1 := by
      intro r hr
      refine ⟨fun e => ?_, fun e => ?_⟩
      · rw [e, ik, a3] at hr
        exact absurd hr (by decide)
      · rw [e, ik1, a4] at hr
        exact absurd hr (by decide)
    refine ⟨_, queueTransfer R s _ G G' Ex Ex' χ id ?_ ?_ ?_ hex h⟩
    · intro q hq1 hq2 hp
      obtain ⟨e1, e2⟩ := nk q hp
      rw [hfar q e1 e2] at hp
      exact ⟨hq1, hq2, hp, hG q hq2 e1 e2⟩
    · intro _ _ _ hlt _ _ _
      exact hlt
    · intro p hp1 hp2 hp
      by_cases e1 : p = k
      · refine Or.inr (fun q hq1 hq2 hq => ?_)
        obtain ⟨n1, n2⟩ := nk q hq
        rw [hfar q n1 n2] at hq
        show q < p
        rw [e1]
        by_cases hlt : q < k
        · exact hlt
        · have hgt : k + 1 < q := by omega
          obtain ⟨T, hT⟩ := shSSome _ a2
          exact absurd hT (((orderPaper R m s ho).1 q (k + 1) (by omega) hgt hq2
            (pkSome _ hq)).2.2 T)
      · by_cases e2 : p = k + 1
        · rw [e2, shSNotPk _ a2] at hp
          exact absurd hp (by decide)
        · exact Or.inl ⟨p, hp1, hp2, by rw [hfar p e1 e2]; exact hp, rfl⟩

/-- **The terminal row.** On the terminal edge `k = 2R - 1` the last cell loses any moving
packet; it is the rightmost pending one, so the clause survives with the same witness, for lane
ghosts unchanged left of the last cell and unchanged delimiter exports. Consumer:
`queueTargetTerm`. -/
theorem queueLaneTerm (R k : Nat) (hk : k + 1 = 2 * R) (s : CohortLane)
    (G G' : Nat → Option (DigitAtom n)) (Ex Ex' : DigitExport c n → Prop)
    (χ : Nat → DigitExport c n) (hG : ∀ q, q < k → G' q = G q)
    (hex : ∀ y, Ex' y ↔ Ex y) (h : QueueLane R s G Ex χ) :
    ∃ χ' : Nat → DigitExport c n, QueueLane R (cohortEdge R s k) G' Ex' χ' := by
  obtain ⟨hi, -⟩ := edgeTerm R k s hk
  have ik : (cohortEdge R s k).inp k = (cohortTermStep (s.inp k) (s.live k)).1 := by
    rw [hi]; simp [cohortUpd]
  have hfar : ∀ q, q ≠ k → (cohortEdge R s k).inp q = s.inp q := by
    intro q e; rw [hi]; simp [cohortUpd, e]
  have nk : ∀ r, pk ((cohortEdge R s k).inp r) = true → r ≠ k := by
    intro r hr e
    rw [e, ik, termCell] at hr
    exact absurd hr (by decide)
  refine ⟨_, queueTransfer R s _ G G' Ex Ex' χ id ?_ ?_ ?_ hex h⟩
  · intro q hq1 hq2 hp
    have e1 := nk q hp
    rw [hfar q e1] at hp
    exact ⟨hq1, hq2, hp, hG q (by omega)⟩
  · intro _ _ _ hlt _ _ _
    exact hlt
  · intro p hp1 hp2 hp
    by_cases e1 : p = k
    · refine Or.inr (fun q _ hq2 hq => ?_)
      have := nk q hq
      show q < p
      omega
    · exact Or.inl ⟨p, hp1, hp2, by rw [hfar p e1]; exact hp, rfl⟩

/-! ### The rows on the coupled chain -/

/-- **The Fin rows on the coupled chain.** A letter at offset `src + k`, `R ≤ k`, `k + 1 < 2R`,
from a layout state in the packet-order class, carries the clause (with a shifted witness).
Consumer: `L3.DigitPacketQueueExport.queueStep`. -/
theorem queueTargetFin (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (hk1 : R ≤ k) (hk2 : k + 1 < 2 * R)
    (ho : PacketOrder R (laneOfState ring hbank root lane src R x)) (χ : Nat → DigitExport _ n)
    (h : QueueAt ring root lane src R (piD x.1.val.1) x.2 χ) :
    ∃ χ' : Nat → DigitExport _ n, QueueAt ring root lane src R
      (piD (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (digitSite ring root (src + k))).1.val.1)
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (digitSite ring root (src + k))).2 χ' := by
  obtain ⟨m, hm⟩ := ho
  have hl := (laneStep ring hn hbank root lane src R hR hsrc hend x hx
    (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hl
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hx
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root x.1 hL
    (digitSite ring root (src + k))
  have hbX' : (pairW (piD x.1.val.1 (digitSite ring root (src + k))).word
      (piD x.1.val.1 (digitSite ring root (src + k + 1))).word).1.beta =
      (piD x.1.val.1 (digitSite ring root (src + k))).word.beta := hbX
  have hbY' : (pairW (piD x.1.val.1 (digitSite ring root (src + k))).word
      (piD x.1.val.1 (digitSite ring root (src + k + 1))).word).2.beta =
      (piD x.1.val.1 (digitSite ring root (src + k + 1))).word.beta := hbY
  have hlx := bankRepairDigitSiteNonroot ring root (piD x.1.val.1) hroot (src + k) (by omega)
    (by omega)
  have hly := bankRepairDigitSiteNonroot ring root (piD x.1.val.1) hroot (src + k + 1) (by omega)
    (by omega)
  have hbx : (piD x.1.val.1 (digitSite ring root (src + k))).word.beta = decide (k = R) := by
    by_cases hkR : k = R
    · rw [decide_eq_true hkR, hkR]
      exact hbR
    · rw [decide_eq_false hkR]
      exact hbF k (by omega) (by omega) hkR
  have hmX : laneMarkerX lane (piD x.1.val.1 (digitSite ring root (src + k)))
      (piD x.1.val.1 (digitSite ring root (src + k + 1))) = decide (k = R) := by
    rw [laneMarkerXBeta lane _ _ hbX']
    exact hbx
  have hmy : laneMarkerY lane (piD x.1.val.1 (digitSite ring root (src + k)))
      (piD x.1.val.1 (digitSite ring root (src + k + 1))) = false := by
    rw [laneMarkerYBeta lane _ _ hbY']
    exact hbF (k + 1) (by omega) (by omega) (by omega)
  obtain ⟨hI, -, -⟩ := rowFinD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD x.1.val.1 (digitSite ring root (src + k)))
    (piD x.1.val.1 (digitSite ring root (src + k + 1)))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + k + 1))) hlx hly hmy
  rw [queueAtIff] at h
  refine (exists_congr fun χ' => queueAtIff ring root lane src R _ _ χ').2 ?_
  have hlane : cohortProj ring root lane src R
      (piD (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (digitSite ring root (src + k))).1.val.1) =
      cohortEdge R (cohortProj ring root lane src R (piD x.1.val.1)) k := hl
  rw [hlane]
  refine queueLaneFin R k m _ hk1 hk2 hm _ _ _ _ χ ?_ ?_ ?_ ?_ h
  · show (laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
      (digitSite ring root (src + k))).current (digitSite ring root (src + k)))).input = _
    rw [curX, show laneOfState ring hbank root lane src R x =
      cohortProj ring root lane src R (piD x.1.val.1) from rfl,
      projIn ring root lane src R _ k hk1 (by omega),
      projLive ring root lane src R _ k hk1 (by omega),
      projIn ring root lane src R _ (k + 1) (by omega) hk2,
      projLive ring root lane src R _ (k + 1) (by omega) hk2, ← hmX]
    exact congrArg Prod.fst hI
  · show (laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
      (digitSite ring root (src + k))).current
        (ring.rightNeighbor (digitSite ring root (src + k))))).input = _
    rw [curY ring (by omega), show laneOfState ring hbank root lane src R x =
      cohortProj ring root lane src R (piD x.1.val.1) from rfl,
      projIn ring root lane src R _ k hk1 (by omega),
      projLive ring root lane src R _ k hk1 (by omega),
      projIn ring root lane src R _ (k + 1) (by omega) hk2,
      projLive ring root lane src R _ (k + 1) (by omega) hk2, ← hmX]
    exact congrArg Prod.snd hI
  · intro q hq e1 e2
    show (laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
      (digitSite ring root (src + k))).current (digitSite ring root (src + q)))).input =
      (laneGhost lane (x.2.current (digitSite ring root (src + q)))).input
    rw [curFar ring (piD x.1.val.1) x.2 _ _
      (siteNe ring root _ _ (by omega) (by omega) (by omega))
      (siteNe ring root (src + q) (src + k + 1) (by omega) (by omega) (by omega))]
  · exact fun y => delExportOff ring root lane src R (piD x.1.val.1) x.2
      (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega)) y

/-- **The terminal row on the coupled chain.** A letter at offset `src + 2R - 1` carries the
clause with the same witness. Consumer: `L3.DigitPacketQueueExport.queueStep`. -/
theorem queueTargetTerm (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (hk : k + 1 = 2 * R)
    (χ : Nat → DigitExport _ n) (h : QueueAt ring root lane src R (piD x.1.val.1) x.2 χ) :
    ∃ χ' : Nat → DigitExport _ n, QueueAt ring root lane src R
      (piD (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (digitSite ring root (src + k))).1.val.1)
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (digitSite ring root (src + k))).2 χ' := by
  have hl := (laneStep ring hn hbank root lane src R hR hsrc hend x hx
    (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hl
  rw [queueAtIff] at h
  refine (exists_congr fun χ' => queueAtIff ring root lane src R _ _ χ').2 ?_
  have hlane : cohortProj ring root lane src R
      (piD (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (digitSite ring root (src + k))).1.val.1) =
      cohortEdge R (cohortProj ring root lane src R (piD x.1.val.1)) k := hl
  rw [hlane]
  refine queueLaneTerm R k hk _ _ _ _ _ χ ?_ ?_ h
  · intro q hq
    show (laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
      (digitSite ring root (src + k))).current (digitSite ring root (src + q)))).input =
      (laneGhost lane (x.2.current (digitSite ring root (src + q)))).input
    rw [curFar ring (piD x.1.val.1) x.2 _ _
      (siteNe ring root _ _ (by omega) (by omega) (by omega))
      (siteNe ring root (src + q) (src + k + 1) (by omega) (by omega) (by omega))]
  · exact fun y => delExportOff ring root lane src R (piD x.1.val.1) x.2
      (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega)) y

end L3.DigitPacketQueueRows

#print axioms L3.DigitPacketQueueRows.isPktIff
#print axioms L3.DigitPacketQueueRows.queueAtIff
#print axioms L3.DigitPacketQueueRows.queueTransfer
#print axioms L3.DigitPacketQueueRows.queueSame
#print axioms L3.DigitPacketQueueRows.finCell
#print axioms L3.DigitPacketQueueRows.termCell
#print axioms L3.DigitPacketQueueRows.queueLaneFin
#print axioms L3.DigitPacketQueueRows.queueLaneTerm
#print axioms L3.DigitPacketQueueRows.queueTargetFin
#print axioms L3.DigitPacketQueueRows.queueTargetTerm

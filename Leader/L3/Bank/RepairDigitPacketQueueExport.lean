import Leader.L3.Bank.RepairDigitPacketQueueRows

/-!
# Lemma e-packet, fourth clause: the export row and the clause along every coupled word

repair.tex 1306-1307 and 1310: "Export inserts at free offset zero"; the pending queue stays a
consecutive suffix of the accepted serial stream.

* `delCellShape`, `delGhostKeep`, `delAcceptCases`: the literal delivery row on the border cell
  (no acceptance keeps a pending packet with its atom; acceptance needs an empty, carry-free
  border and leaves a moving packet there).
* `delExportedD`: the lane receipt exports exactly on acceptance (record fields).
* `delExportStep`, `delExportClock`: the delimiter exports after a delimiter letter are the old
  ones and the new frame's export (stamped `clock + 1`); under `AuditFrameOrder` every old one is
  stamped at most `clock`.
* `queueLaneDel`, `queueExport`: the export row on the lane and on the coupled chain. The new
  export is the newest, sits at the border, the leftmost cell, and becomes the leftmost pending
  packet (`χ' R = ex`).
* `queueStep`, `packetQueueStep`, `packetQueueWord`: every coupled letter, then every coupled word
  from a layout state with ordered frames, carries `PacketQueue` (shape invariant by
  `orderCoupled`, ghost clause by the rows).
-/

namespace L3.DigitPacketQueueExport

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
open L3.DigitPacketQueueRows

variable {c : Compiled} {n : Nat}

/-! ### The literal border cell -/

/-- **The delivery row on the border**, given the carry clause of the order invariant: without
acceptance the border keeps its packet status; acceptance needs an empty border and leaves a
moving packet. Consumer: `queueLaneDel`. -/
theorem delCellShape (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (hky : ky = true → iy = .E) :
    (delAccept ox iy ky = false ∧ pk (bankRepairDigitDelStep ox iy ky).2.1 = pk iy) ∨
      (delAccept ox iy ky = true ∧ iy = .E ∧ pk (bankRepairDigitDelStep ox iy ky).2.1 = true) := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitDelStep, delAccept, pk] at hky ⊢

/-- Without acceptance a pending border packet keeps its atom. Consumer: `queueExport`. -/
theorem delGhostKeep (st : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n))
    (hky : ky = true → iy = .E) (hd : delAccept ox iy ky = false) (hp : pk iy = true) :
    (ghostDel st ox iy ky gxo gyi).2 = gyi := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [ghostDel, delAccept, pk] at hky hd hp ⊢

/-- Acceptance is a data packet into an empty carry-free border. Consumer: `queueExport`. -/
theorem delAcceptCases (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (h : delAccept ox iy ky = true) : ∃ T, ox = .D T ∧ iy = .E ∧ ky = false := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [delAccept] at h ⊢

/-- The lane receipt of a delivery letter exports exactly on acceptance (record fields).
Consumer: `queueExport`. -/
theorem delExportedD (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
    (gx gy : DigitGhost c n) (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmx : laneMarkerX lane X Y = false) (hmy : laneMarkerY lane X Y = true) :
    (digitReceiptLane lane (digitService t e d X Y gx gy)).exported.isSome =
      delAccept (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane X.top))
        (bankRepairDigitInShOf (bankRepairDigitLaneIn lane Y.top))
        (bankRepairDigitLaneLive lane Y.top) := by
  obtain ⟨-, -, h3⟩ := replayDel lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmx) (by rw [laneViewMarker]; exact hmy)
  rw [laneViewOutSh, laneViewInSh, laneViewLive] at h3
  rw [serviceLane]
  exact h3

/-! ### Delimiter exports along one letter -/

/-- **Delimiter-export bookkeeping on the delimiter letter.** Consumer: `queueExport`. -/
theorem delExportStep (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n)
    (he : e = digitSite ring root (src + (R - 1))) (y : DigitExport c n) :
    DelExport ring root lane src R (digitAuditStep ring S A e) y ↔
      DelExport ring root lane src R A y ∨
        (y.time = A.clock + 1 ∧ y.source = e ∧
          (digitReceiptLane lane (svcAt ring S A e)).exported = some y ∧ y.lane = lane ∧
          y.destination = digitSite ring root (src + R)) := by
  unfold DelExport
  rw [recordedExportStep]
  constructor
  · rintro ⟨h | ⟨h1, h2, h3⟩, h4, h5, h6⟩
    · exact Or.inl ⟨h, h4, h5, h6⟩
    · exact Or.inr ⟨h1, h2, by rw [← h4]; exact h3, h4, h6⟩
  · rintro (⟨h, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h6⟩)
    · exact ⟨Or.inl h, h4, h5, h6⟩
    · exact ⟨Or.inr ⟨h1, h2, by rw [h4]; exact h3⟩, h4, by rw [h2, he], h6⟩

/-- Every recorded delimiter export is stamped at most the clock. Consumer: `queueExport`. -/
theorem delExportClock (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) (hA : AuditFrameOrder A) (y : DigitExport c n)
    (hy : DelExport ring root lane src R A y) : y.time ≤ A.clock := by
  obtain ⟨⟨f, hf, ht, -, -⟩, -⟩ := hy
  have := (hA.2.1 f hf).2
  omega

/-! ### The export row on the masked lane -/

/-- **The export row.** On the delivery edge `k = R - 1` of a lane in the packet-order class:
without acceptance the clause is carried with the same witness; with acceptance of a new export
`ex`, newer than every recorded one, whose operand is the new border ghost, the clause holds with
`χ' R = ex`. Consumer: `queueExport`. -/
theorem queueLaneDel (R k m : Nat) (hk : k + 1 = R) (s : CohortLane) (ho : OrderAt R s m)
    (G G' : Nat → Option (DigitAtom n)) (Ex Ex' : DigitExport c n → Prop)
    (χ : Nat → DigitExport c n) (t : Nat)
    (hG : ∀ q, R < q → q < 2 * R → G' q = G q)
    (hold : ∀ y, Ex y → y.time < t)
    (hrej : delAccept (s.out k) (s.inp R) (s.live R) = false →
      (pk (s.inp R) = true → G' R = G R) ∧ ∀ y, Ex' y ↔ Ex y)
    (hacc : delAccept (s.out k) (s.inp R) (s.live R) = true →
      ∃ ex : DigitExport c n, ex.time = t ∧ G' R = ex.operand ∧ ∀ y, Ex' y ↔ Ex y ∨ y = ex)
    (h : QueueLane R s G Ex χ) :
    ∃ χ' : Nat → DigitExport c n, QueueLane R (cohortEdge R s k) G' Ex' χ' := by
  subst hk
  obtain ⟨hi, -⟩ := edgeDel (k + 1) k s rfl
  have iR : (cohortEdge (k + 1) s k).inp (k + 1) =
      (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.1 := by
    rw [hi]; simp [cohortUpd]
  have hfar : ∀ q, q ≠ k + 1 → (cohortEdge (k + 1) s k).inp q = s.inp q := by
    intro q e; rw [hi]; simp [cohortUpd, e]
  have hky : s.live (k + 1) = true → s.inp (k + 1) = .E := fun hl =>
    ((orderPaper (k + 1) m s ho).2 (k + 1) (Nat.le_refl _) (by omega) hl).1
  rcases delCellShape (s.out k) (s.inp (k + 1)) (s.live (k + 1)) hky with
    ⟨a1, a2⟩ | ⟨a1, a2, a3⟩
  · obtain ⟨g1, g2⟩ := hrej a1
    refine ⟨χ, queueSame (k + 1) s _ G G' Ex Ex' χ ?_ ?_ g2 h⟩
    · intro q _ _
      by_cases e : q = k + 1
      · rw [e, iR]; exact a2
      · rw [hfar q e]
    · intro q hq1 hq2 hp
      by_cases e : q = k + 1
      · rw [e]; rw [e] at hp; exact g1 hp
      · exact hG q (by omega) hq2
  · obtain ⟨ex, ht, hGR, hEx⟩ := hacc a1
    obtain ⟨c1, c2, c3⟩ := h
    have old0 : pk (s.inp (k + 1)) = false := by rw [a2]; rfl
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

/-! ### The export row on the coupled chain -/

/-- **The export row on the coupled chain.** The delimiter letter at offset `src + R - 1`, from a
layout state in the packet-order class with ordered audit frames, carries the clause; an accepted
export, stamped `clock + 1`, becomes the leftmost pending packet. Consumer: `queueStep`. -/
theorem queueExport (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (hk : k + 1 = R)
    (ho : PacketOrder R (laneOfState ring hbank root lane src R x)) (hfo : AuditFrameOrder x.2)
    (χ : Nat → DigitExport _ n) (h : QueueAt ring root lane src R (piD x.1.val.1) x.2 χ) :
    ∃ χ' : Nat → DigitExport _ n, QueueAt ring root lane src R
      (piD (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (digitSite ring root (src + k))).1.val.1)
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (digitSite ring root (src + k))).2 χ' := by
  subst hk
  obtain ⟨m, hm0⟩ := ho
  have hm : OrderAt (k + 1) (cohortProj ring root lane src (k + 1) (piD x.1.val.1)) m := hm0
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
  have hky : (cohortProj ring root lane src (k + 1) (piD x.1.val.1)).live (k + 1) = true →
      (cohortProj ring root lane src (k + 1) (piD x.1.val.1)).inp (k + 1) = .E := fun hl' =>
    ((orderPaper (k + 1) m _ hm).2 (k + 1) (Nat.le_refl _) (by omega) hl').1
  have he : digitSite ring root (src + k) = digitSite ring root (src + (k + 1 - 1)) := by
    rw [Nat.add_sub_cancel]
  rw [queueAtIff] at h
  refine (exists_congr fun χ' => queueAtIff ring root lane src (k + 1) _ _ χ').2 ?_
  have hlane : cohortProj ring root lane src (k + 1)
      (piD (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (digitSite ring root (src + k))).1.val.1) =
      cohortEdge (k + 1) (cohortProj ring root lane src (k + 1) (piD x.1.val.1)) k := hl
  rw [hlane]
  refine queueLaneDel (k + 1) k m rfl _ hm _ _ _ _ χ (x.2.clock + 1) ?_ ?_ ?_ ?_ h
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
    refine ⟨fun hp => ?_, fun y => ?_⟩
    · show (laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
        (digitSite ring root (src + k))).current
          (ring.rightNeighbor (digitSite ring root (src + k))))).input =
        (laneGhost lane (x.2.current (digitSite ring root (src + (k + 1))))).input
      rw [curY ring (by omega)]
      exact (congrArg Prod.snd hrow).trans (delGhostKeep _ _ _ _ _ _ hky hd hp)
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

/-! ### Every coupled letter, every coupled word -/

/-- **The step of the fourth clause.** Every coupled letter, from a layout state in the
packet-order class with ordered audit frames, carries `QueueAt` (with a new witness).
Consumer: `packetQueueStep`. -/
theorem queueStep (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (hfo : AuditFrameOrder x.2)
    (ho : PacketOrder R (laneOfState ring hbank root lane src R x))
    (χ : Nat → DigitExport _ n) (h : QueueAt ring root lane src R (piD x.1.val.1) x.2 χ)
    (e : Fin n) :
    ∃ χ' : Nat → DigitExport _ n, QueueAt ring root lane src R
      (piD (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1.val.1)
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).2 χ' := by
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  by_cases hfar : j + 1 < src + R ∨ src + 2 * R ≤ j
  · exact ⟨χ, queueFar ring hn hbank root lane src R hR hsrc hend x hx j hj hfar χ h⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    by_cases h1 : k + 1 = R
    · exact queueExport ring hn hbank root lane src R hR hsrc hend x hx k h1 ho hfo χ h
    · by_cases h2 : k + 1 = 2 * R
      · exact queueTargetTerm ring hn hbank root lane src R hR hsrc hend x hx k h2 χ h
      · exact queueTargetFin ring hn hbank root lane src R hR hsrc hend x hx k (by omega)
          (by omega) ho χ h

/-- **The reached-state invariant with its ghost clause along one coupled letter**, with the
layout and the frame order. Consumer: `packetQueueWord`. -/
theorem packetQueueStep (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (hfo : AuditFrameOrder x.2)
    (hq : PacketQueue ring root lane src R (piD x.1.val.1) x.2) (e : Fin n) :
    CohortLayout ring hbank root src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1 ∧
      AuditFrameOrder (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).2 ∧
      PacketQueue ring root lane src R
        (piD (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1.val.1)
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).2 := by
  obtain ⟨ho, χ, h⟩ := hq
  obtain ⟨h1, h2⟩ := orderCoupled ring hn hbank root lane src R hR hsrc hend x hx ho e
  obtain ⟨χ', h'⟩ := queueStep ring hn hbank root lane src R hR hsrc hend x hx hfo ho χ h e
  exact ⟨h1, auditFrameOrderStep ring (piD x.1.val.1) x.2 e hfo, h2, χ', h'⟩

/-- **The reached-state invariant with its ghost clause along every coupled word** (repair.tex
1300-1326, all four clauses): from a layout state with ordered audit frames where `PacketQueue`
holds (for instance a mobile-free cut, `packetQueueMobileFree`), it holds after every word.
Consumer: the settled-empty (`U`) and renewal-trial (`V`) phases of Lemma e-packet. -/
theorem packetQueueWord (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) :
    ∀ (w : List (Fin n))
      (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      CohortLayout ring hbank root src R x.1 → AuditFrameOrder x.2 →
      PacketQueue ring root lane src R (piD x.1.val.1) x.2 →
      CohortLayout ring hbank root src R
          (w.foldl (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x).1 ∧
        AuditFrameOrder
          (w.foldl (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x).2 ∧
        PacketQueue ring root lane src R
          (piD (w.foldl (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x).1.val.1)
          (w.foldl (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x).2 := by
  intro w
  induction w with
  | nil => intro x hx hfo hq; exact ⟨hx, hfo, hq⟩
  | cons e w ih =>
    intro x hx hfo hq
    obtain ⟨h1, h2, h3⟩ := packetQueueStep ring hn hbank root lane src R hR hsrc hend x hx hfo hq e
    exact ih _ h1 h2 h3

end L3.DigitPacketQueueExport

#print axioms L3.DigitPacketQueueExport.delCellShape
#print axioms L3.DigitPacketQueueExport.delGhostKeep
#print axioms L3.DigitPacketQueueExport.delAcceptCases
#print axioms L3.DigitPacketQueueExport.delExportedD
#print axioms L3.DigitPacketQueueExport.delExportStep
#print axioms L3.DigitPacketQueueExport.delExportClock
#print axioms L3.DigitPacketQueueExport.queueLaneDel
#print axioms L3.DigitPacketQueueExport.queueExport
#print axioms L3.DigitPacketQueueExport.queueStep
#print axioms L3.DigitPacketQueueExport.packetQueueStep
#print axioms L3.DigitPacketQueueExport.packetQueueWord

import Leader.L3.Bank.RepairDigitValueCorr
import Leader.L3.Bank.RepairDigitFiveReach

/-!
# T32 item 1 (continued): values of exports and uses, and the value invariant on the chain

* `ExportVal`: every recorded export on the delimiter edge whose operand is a sampled atom
  `.sampled id` has a recorded sample with stamp `id` carrying the export's value and tail
  (`exportValStep`: the export of a letter reads the physical `D v T` of the delimiter source
  cell, and `ValCorr` pairs it with the cell's ghost atom).
* `UseVal`: the same for every use of a ledger on a target cell and of a recorded terminal on the
  terminal edge (`useValStep`: a use reads the settled input `S v T` of its target cell).
* `sampleUnique`: under ordered frames a recorded sample is determined by its stamp, so two
  value records of one sampled atom agree (`sampValAgree`, `useMatchesExport`).
* `ValInv` (`ValCorr ∧ ExportVal ∧ UseVal ∧ LedgerOk`) holds at the audit start and along every
  coupled word in the layout class (`valInvRun`, `valInvFromStart`); `ValReach` adds exact
  frames and is carried by every `windowNext` letter (`valReachStep`).
* `chiSampledOf`, `closeUsesOf`, `receiptOfPins`: `ChiSampled` and the use clause of
  `receiptOfCore` from the operand facts `SitePin` (items 2 and 4) and `UseTrack` (item 3).
-/

namespace L3.ValueLedger

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortSites
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortLedger
open L3.CohortWindow
open L3.CohortClose
open L3.HClose
open L3.CloseReceipt
open L3.FiveReach
open L3.ValueCorr

/-! ### Uses of one replay -/

section Replay

variable {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (source destination : Fin n)
  (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)

/-- Left ledger of the replay: retired, kept, or launched with one use reading the settled
left input. -/
theorem replayCarryXUse (hlx : x.leader = false) (hly : y.leader = false) :
    (digitLaneReplay lane time source destination x y gx gy).x.carry = none ∨
    (digitLaneReplay lane time source destination x y gx gy).x.carry = gx.carry ∨
    ∃ u : DigitUse c n,
      (digitLaneReplay lane time source destination x y gx gy).x.carry =
        some (DigitCarryGhost.mk none [u]) ∧
      u.operand = gx.input ∧ u.value = inV c x.input ∧ u.tail = inT x.input ∧
      x.input.isS = true := by
  cases hxc : x.carryLive <;> cases hxm : x.marker <;>
    simp [digitLaneReplay, hlx, hly, hxc, hxm] <;> (repeat' split) <;> simp_all

/-- Right ledger of the replay off a marker: kept, or the left ledger with one use appended
reading the settled right input. -/
theorem replayCarryYUse (hlx : x.leader = false) (hly : y.leader = false)
    (hmy : y.marker = false) :
    (digitLaneReplay lane time source destination x y gx gy).y.carry = gy.carry ∨
    ∃ u : DigitUse c n,
      (digitLaneReplay lane time source destination x y gx gy).y.carry =
        some (DigitCarryGhost.mk
          (gx.carry.getD (DigitCarryGhost.mk
            (some (.missing (DigitStamp.mk time source lane) .carry)) [])).inherited
          ((gx.carry.getD (DigitCarryGhost.mk
            (some (.missing (DigitStamp.mk time source lane) .carry)) [])).uses ++ [u])) ∧
      u.operand = gy.input ∧ u.value = inV c y.input ∧ u.tail = inT y.input ∧
      y.input.isS = true := by
  cases hxc : x.carryLive <;>
    simp [digitLaneReplay, hlx, hly, hmy, hxc] <;> (repeat' split) <;> simp_all

end Replay

/-! ### Value records -/

section Records

variable {c : Compiled} {n : Nat}

/-- Every use of a ledger records the value and tail of its sampled operand. -/
def UsesVal (A : DigitAudit c n) (L : DigitCarryGhost c n) : Prop :=
  ∀ u, u ∈ L.uses → AtomSV A u.operand u.value u.tail

theorem usesValStep (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) {L : DigitCarryGhost c n} (h : UsesVal A L) :
    UsesVal (digitAuditStep ring S A e) L :=
  fun u hu => atomSVStep ring S A e (h u hu)

theorem isSCases {A : Nat} (t : InTok A) (h : t.isS = true) : ∃ v T, t = .S v T := by
  cases t <;> simp_all [InTok.isS]

theorem outDCases (o : OutTok c.topA) (T : Bool) (h : bankRepairDigitOutShOf o = .D T) :
    ∃ v, o = .D v T := by
  cases o <;> simp_all [bankRepairDigitOutShOf]

/-- A use reading a settled input records the input's value and tail on the input's atom. -/
theorem useAtomSV (A : DigitAudit c n) (i : InTok c.topA) (a : Option (DigitAtom n))
    (hv : InVal A i a) (hS : i.isS = true) (u : DigitUse c n) (h1 : u.operand = a)
    (h2 : u.value = inV c i) (h3 : u.tail = inT i) : AtomSV A u.operand u.value u.tail := by
  obtain ⟨v, T, rfl⟩ := isSCases i hS
  rw [h1, h2, h3]
  exact hv

/-- The delimiter-edge export of one service records the source token's value and tail on the
source ghost's atom. -/
theorem delExportVal (A : DigitAudit c n) (lane : DigitLane) (t : Nat) (e d : Fin n)
    (X Y : ProjD c) (gx gy : DigitGhost c n) (hlx : X.word.native.l = false)
    (hly : Y.word.native.l = false) (hmx : laneMarkerX lane X Y = false)
    (hmy : laneMarkerY lane X Y = true)
    (hov : OutVal A (bankRepairDigitLaneOut lane X.top) (laneGhost lane gx).out)
    (x : DigitExport c n)
    (hx : (digitReceiptLane lane (digitService t e d X Y gx gy)).exported = some x) :
    AtomSV A x.operand x.value x.tail := by
  rw [serviceLane] at hx
  obtain ⟨-, -, -, -, f1, f2, f3⟩ := replayExportFields lane t e d _ _ _ _ x hx
  have hd := (replayDel lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmx) (by rw [laneViewMarker]; exact hmy)).2.2
  rw [hx, Option.isSome_some] at hd
  obtain ⟨T, hD, -, -⟩ := delAcceptTrue _ _ _ hd.symm
  rw [laneViewOut] at hD f2 f3
  obtain ⟨v, hvD⟩ := outDCases _ T hD
  rw [hvD] at hov f2 f3
  rw [f1, f2, f3]
  exact hov

theorem frameUnique : ∀ (l : List (DigitFrame c n)), l.Pairwise (fun f g => g.time < f.time) →
    ∀ f g, f ∈ l → g ∈ l → f.time = g.time → f = g
  | [], _, _, _, hf, _, _ => absurd hf List.not_mem_nil
  | a :: l, hp, f, g, hf, hg, ht => by
      rw [List.pairwise_cons] at hp
      rcases List.mem_cons.mp hf with h1 | h1 <;> rcases List.mem_cons.mp hg with h2 | h2
      · rw [h1, h2]
      · have := hp.1 g h2
        rw [h1] at ht
        omega
      · have := hp.1 f h1
        rw [h2] at ht
        omega
      · exact frameUnique l hp.2 f g h1 h2 ht

/-- **Sample uniqueness**: under ordered frames a recorded sample is determined by its stamp. -/
theorem sampleUnique (A : DigitAudit c n) (hfo : AuditFrameOrder A) (s s' : DigitSample c n)
    (hs : DigitRecordedSample A s) (hs' : DigitRecordedSample A s') (hid : s.id = s'.id) :
    s = s' := by
  obtain ⟨f, hf, h1, -, h3, -⟩ := hs
  obtain ⟨f', hf', h1', -, h3', -⟩ := hs'
  have hff : f = f' := frameUnique A.frames hfo.1 f f' hf hf' (by rw [h1, h1', hid])
  subst hff
  rw [hid] at h3
  exact Option.some.inj (h3.symm.trans h3')

theorem sampValAgree (A : DigitAudit c n) (hfo : AuditFrameOrder A) {id : DigitStamp n}
    {v v' : Fin c.topA} {T T' : Bool} (h : SampVal A id v T) (h' : SampVal A id v' T') :
    v = v' ∧ T = T' := by
  obtain ⟨s, hs, hid, hv, hT⟩ := h
  obtain ⟨s', hs', hid', hv', hT'⟩ := h'
  have := sampleUnique A hfo s s' hs hs' (hid.trans hid'.symm)
  subst this
  exact ⟨hv.symm.trans hv', hT.symm.trans hT'⟩

end Records

/-! ### The export and use invariants on the ring -/

section Ring

variable {c : Compiled} {n : Nat}

/-- **Export values**: every delimiter-edge export records the value and tail of its sampled
operand. -/
def ExportVal (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) : Prop :=
  ∀ x : DigitExport c n, DigitRecordedExport A x → OnEdge ring root lane src R x →
    AtomSV A x.operand x.value x.tail

/-- **Use values**: every use of a target-cell ledger and of a terminal-edge receipt records the
value and tail of its sampled operand. -/
def UseVal (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) : Prop :=
  (∀ q, R ≤ q → q < 2 * R → ∀ L : DigitCarryGhost c n,
    (laneCells ring root lane src A.current q).carry = some L → UsesVal A L) ∧
  (∀ T : DigitTerminal c n, DigitRecordedTerminal A T → T.lane = lane →
    T.source = digitSite ring root (src + (2 * R - 1)) → ∀ L : DigitCarryGhost c n,
    T.ledger = some L → UsesVal A L)

theorem exportValStep (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n) (e : Fin n)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta)
    (hv : ValCorr ring root lane src R S A) (h : ExportVal ring root lane src R A) :
    ExportVal ring root lane src R (digitAuditStep ring S A e) := by
  intro x hx hon
  rcases recordedExportStepCases ring S A e x hx with hx' | ⟨-, hxs, hxe⟩
  · exact atomSVStep ring S A e (h x hx' hon)
  · obtain ⟨hl, hs⟩ := hon
    have he : e = digitSite ring root (src + (R - 1)) := hxs.symm.trans hs
    subst he
    rw [hl] at hxe
    have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + (R - 1)) (by omega)
      (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (src + (R - 1) + 1) (by omega)
      (by omega)
    have hmx : laneMarkerX lane (S (digitSite ring root (src + (R - 1))))
        (S (ring.rightNeighbor (digitSite ring root (src + (R - 1))))) = false := by
      rw [laneMarkerXBeta lane _ _ hbX]
      exact hbF (R - 1) (by omega) (by omega) (by omega)
    have hmy : laneMarkerY lane (S (digitSite ring root (src + (R - 1))))
        (S (ring.rightNeighbor (digitSite ring root (src + (R - 1))))) = true := by
      rw [laneMarkerYBeta lane _ _ hbY]
      show (S (digitSite ring root (src + (R - 1) + 1))).word.beta = true
      rw [show src + (R - 1) + 1 = src + R by omega]
      exact hbR
    exact atomSVStep ring S A _ (delExportVal A lane (A.clock + 1)
      (digitSite ring root (src + (R - 1))) (ring.rightNeighbor (digitSite ring root (src + (R - 1))))
      (S (digitSite ring root (src + (R - 1))))
      (S (ring.rightNeighbor (digitSite ring root (src + (R - 1)))))
      (A.current (digitSite ring root (src + (R - 1))))
      (A.current (ring.rightNeighbor (digitSite ring root (src + (R - 1)))))
      hlx hly hmx hmy (hv.1 (R - 1) (by omega)) x hxe)

/-- **Every letter preserves the use values** (layout hypotheses of `ledgerOkStep`). -/
theorem useValStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    (hv : ValCorr ring root lane src R S A) (h : UseVal ring root lane src R A) :
    UseVal ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) := by
  obtain ⟨hC, hT⟩ := h
  refine ⟨?_, ?_⟩
  · intro q hq1 hq2 L hL
    have far : src + q ≠ j → src + q ≠ j + 1 →
        UsesVal (digitAuditStep ring S A (digitSite ring root j)) L := by
      intro n1 n2
      rw [cellFar ring root S A lane src j q hj (by omega) (by omega) n1 n2] at hL
      exact usesValStep ring S A _ (hC q hq1 hq2 L hL)
    by_cases hin : src ≤ j ∧ j < src + 2 * R
    · obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
      have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
      have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega)
        (by omega)
      have vlx : (digitLaneView lane (S (digitSite ring root (src + k)))
          (laneMarkerX lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))))).leader = false := by
        rw [laneViewLeader]; exact hlx
      have vly : (digitLaneView lane (S (digitSite ring root (src + k + 1)))
          (laneMarkerY lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))))).leader = false := by
        rw [laneViewLeader]; exact hly
      have vmx : (digitLaneView lane (S (digitSite ring root (src + k)))
          (laneMarkerX lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))))).marker =
            (S (digitSite ring root (src + k))).word.beta := by
        rw [laneViewMarker, laneMarkerXBeta lane _ _ hbX]
      have vmy : (digitLaneView lane (S (digitSite ring root (src + k + 1)))
          (laneMarkerY lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))))).marker =
            (S (digitSite ring root (src + k + 1))).word.beta := by
        rw [laneViewMarker, laneMarkerYBeta lane _ _ hbY]
      by_cases hqk : q = k
      · subst hqk
        rw [cellX] at hL
        rcases replayCarryXUse lane _ _ _ _ _ _ _ vlx vly with h1 | h1 |
          ⟨u, h1, u1, u2, u3, u4⟩
        · rw [h1] at hL
          cases hL
        · rw [h1] at hL
          exact usesValStep ring S A _ (hC q hq1 hq2 L hL)
        · rw [h1] at hL
          injection hL with hL
          subst hL
          intro w hw
          have hw' : w = u := List.mem_singleton.mp hw
          subst hw'
          apply atomSVStep ring S A _
          rw [laneViewIn] at u2 u3 u4
          exact useAtomSV A _ _ (hv.2 q hq1 hq2) u4 w u1 u2 u3
      · by_cases hqk1 : q = k + 1
        · subst hqk1
          rw [cellY ring hn] at hL
          by_cases hkR : k + 1 = R
          · have hmx' : (digitLaneView lane (S (digitSite ring root (src + k)))
                (laneMarkerX lane (S (digitSite ring root (src + k)))
                  (S (digitSite ring root (src + k + 1))))).marker = false := by
              rw [vmx]; exact hbF k (by omega) (by omega) (by omega)
            have hmy' : (digitLaneView lane (S (digitSite ring root (src + k + 1)))
                (laneMarkerY lane (S (digitSite ring root (src + k)))
                  (S (digitSite ring root (src + k + 1))))).marker = true := by
              rw [vmy, show src + k + 1 = src + R by omega]; exact hbR
            rw [(replayDel lane _ _ _ _ _ _ _ vlx vly hmx' hmy').2.1] at hL
            exact usesValStep ring S A _ (hC (k + 1) hq1 hq2 L hL)
          · have hmy' : (digitLaneView lane (S (digitSite ring root (src + k + 1)))
                (laneMarkerY lane (S (digitSite ring root (src + k)))
                  (S (digitSite ring root (src + k + 1))))).marker = false := by
              rw [vmy]; exact hbF (k + 1) (by omega) (by omega) hkR
            have hkR' : R ≤ k := by omega
            rcases replayCarryYUse lane _ _ _ _ _ _ _ vlx vly hmy' with h1 |
              ⟨u, h1, u1, u2, u3, u4⟩
            · rw [h1] at hL
              exact usesValStep ring S A _ (hC (k + 1) hq1 hq2 L hL)
            · rw [h1] at hL
              injection hL with hL
              subst hL
              intro w hw
              apply atomSVStep ring S A _
              rcases List.mem_append.mp hw with hw | hw
              · cases hgx : (laneCells ring root lane src A.current k).carry with
                | none =>
                  rw [hgx] at hw
                  simp at hw
                | some L0 =>
                  rw [hgx] at hw
                  exact hC k hkR' (by omega) L0 hgx w hw
              · have hw' : w = u := List.mem_singleton.mp hw
                subst hw'
                rw [laneViewIn] at u2 u3 u4
                exact useAtomSV A _ _ (hv.2 (k + 1) hq1 hq2) u4 w u1 u2 u3
        · exact far (by omega) (by omega)
    · exact far (by omega) (by omega)
  · intro T hTr hTl hTs L hL
    obtain ⟨f, hf, h1, h2, h3⟩ := hTr
    rcases auditFrameMemStepCases ring S A _ f hf with hf' | hf'
    · exact usesValStep ring S A _ (hT T ⟨f, hf', h1, h2, h3⟩ hTl hTs L hL)
    · subst hf'
      have hje : j = src + (2 * R - 1) :=
        bankRepairDigitSiteInj ring root hj (by omega) (h2.trans hTs)
      subst hje
      rw [hTl] at h3
      have h3' : (digitReceiptLane lane (svcAt ring S A
          (digitSite ring root (src + (2 * R - 1))))).terminal = some T := h3
      unfold svcAt at h3'
      rw [serviceLane] at h3'
      obtain ⟨e1, -, -⟩ := replayTerminal lane _ _ _ _ _ _ _ T h3'
      rw [hL] at e1
      exact usesValStep ring S A _ (hC (2 * R - 1) (by omega) (by omega) L e1.symm)

/-- A use of a terminal-edge receipt and a delimiter-edge export with the same sampled operand
record the same value and tail. -/
theorem useMatchesExport (ring : DirectedRing n) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (A : DigitAudit c n) (hfo : AuditFrameOrder A)
    (hxv : ExportVal ring root lane src R A) (huv : UseVal ring root lane src R A)
    (x : DigitExport c n) (hxr : DigitRecordedExport A x) (hon : OnEdge ring root lane src R x)
    (T : DigitTerminal c n) (hT : DigitRecordedTerminal A T) (hTl : T.lane = lane)
    (hTs : T.source = digitSite ring root (src + (2 * R - 1))) (L : DigitCarryGhost c n)
    (hL : T.ledger = some L) (u : DigitUse c n) (hmem : u ∈ L.uses) (id : DigitStamp n)
    (hxo : x.operand = some (.sampled id)) (huo : u.operand = x.operand) :
    u.value = x.value ∧ u.tail = x.tail :=
  sampValAgree A hfo (huv.2 T hT hTl hTs L hL u hmem id (huo.trans hxo))
    (hxv x hxr hon id hxo)

/-! ### The audit start -/

theorem initialOutVal (A : DigitAudit c n) (lane : DigitLane) (i : Fin n) (v : DigitLaneView c) :
    OutVal A v.out (DigitLaneGhost.initial lane i v).out := by
  cases h : v.out <;> simp [DigitLaneGhost.initial, h, OutVal, AtomSV, DigitOutGhost.atom]

theorem initialInVal (A : DigitAudit c n) (lane : DigitLane) (i : Fin n) (v : DigitLaneView c) :
    InVal A v.input (DigitLaneGhost.initial lane i v).input := by
  cases h : v.input <;> simp [DigitLaneGhost.initial, h, InVal, AtomSV]

theorem valCorrInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) : ValCorr ring root lane src R S (digitAuditInitial S) := by
  refine ⟨fun q _ => ?_, fun q _ _ => ?_⟩
  · show OutVal _ _ (laneGhost lane (digitGhostInitial S (digitSite ring root (src + q)))).out
    rw [laneGhostInitial, ← laneViewOut lane (S (digitSite ring root (src + q)))
      (S (digitSite ring root (src + q))).word.beta]
    exact initialOutVal _ lane _ _
  · show InVal _ _ (laneGhost lane (digitGhostInitial S (digitSite ring root (src + q)))).input
    rw [laneGhostInitial, ← laneViewIn lane (S (digitSite ring root (src + q)))
      (S (digitSite ring root (src + q))).word.beta]
    exact initialInVal _ lane _ _

theorem exportValInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (S : Fin n → ProjD c) :
    ExportVal ring root lane src R (digitAuditInitial S) := by
  intro x hx
  obtain ⟨f, hf, -⟩ := hx
  exact absurd hf List.not_mem_nil

theorem useValInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) : UseVal ring root lane src R (digitAuditInitial S) := by
  refine ⟨fun q _ _ L hL => ?_, fun T hT => ?_⟩
  · have hL' : (laneGhost lane (digitGhostInitial S (digitSite ring root (src + q)))).carry =
        some L := hL
    rw [laneGhostInitial] at hL'
    unfold DigitLaneGhost.initial at hL'
    by_cases hc : (digitLaneView lane (S (digitSite ring root (src + q)))
        (S (digitSite ring root (src + q))).word.beta).carryLive = true
    · rw [if_pos hc] at hL'
      injection hL' with hL'
      subst hL'
      intro u hu
      simp at hu
    · rw [if_neg hc] at hL'
      cases hL'
  · obtain ⟨f, hf, -⟩ := hT
    exact absurd hf List.not_mem_nil

end Ring

/-! ### Along the coupled chain -/

section Run

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- **The value invariant** of a coupled state. -/
def ValInv (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  ValCorr ring root lane src R (piD z.1.val.1) z.2 ∧ ExportVal ring root lane src R z.2 ∧
    UseVal ring root lane src R z.2 ∧ LedgerOk ring root lane src R z.2

include hn hR hsrc hend in
theorem valInvBankStep
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1)
    (hc : ValInv ring hbank root lane src R z) (e : Fin n) :
    ValInv ring hbank root lane src R (bankRepairDigitBoundaryAuditNext ring hbank z e) := by
  have hlo := (ledgerOkBankStep ring hn hbank root lane src R hR hsrc hend z hz hc.2.2.2 e).2
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨heq, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  obtain ⟨hv, hx, hu, -⟩ := hc
  show ValCorr ring root lane src R (piD (bankRepairNext ring hbank z.1 e).val.1)
      (digitAuditStep ring (piD z.1.val.1) z.2 e) ∧
    ExportVal ring root lane src R (digitAuditStep ring (piD z.1.val.1) z.2 e) ∧
    UseVal ring root lane src R (digitAuditStep ring (piD z.1.val.1) z.2 e) ∧
    LedgerOk ring root lane src R (digitAuditStep ring (piD z.1.val.1) z.2 e)
  rw [heq]
  refine ⟨?_, exportValStep ring root (piD z.1.val.1) R src hR hend hroot hbR hbF lane z.2 e
    hbX hbY hv hx, ?_, hlo⟩
  · obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    exact valCorrStep ring (by omega) root (piD z.1.val.1) R src hR hsrc hend hroot hb0 hbR
      hb2R hbF lane z.2 j hj hbX hbY hv
  · obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    exact useValStep ring (by omega) root (piD z.1.val.1) R src hR hsrc hend hroot hbR hbF
      lane z.2 j hj hbX hbY hv hu

include hn hR hsrc hend in
/-- **Run level**: along every coupled word in the layout class the value invariant persists. -/
theorem valInvRun (word : List (Fin n)) :
    ∀ z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      CohortLayout ring hbank root src R z.1 → ValInv ring hbank root lane src R z →
      CohortLayout ring hbank root src R
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).1 ∧
      ValInv ring hbank root lane src R
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z) := by
  induction word with
  | nil => intro z h1 h2; exact ⟨h1, h2⟩
  | cons e rest ih =>
      intro z h1 h2
      exact ih _ (cohortBankStep ring hn hbank root lane src R hR hsrc hend z.1 h1 e).1
        (valInvBankStep ring hn hbank root lane src R hR hsrc hend z h1 h2 e)

include hn hR hsrc hend in
/-- The value invariant along every coupled word from the audit start. -/
theorem valInvFromStart (z : BankReferenceState ring hbank)
    (hz : CohortLayout ring hbank root src R z) (word : List (Fin n)) :
    ValInv ring hbank root lane src R
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (z, digitAuditInitial (piD z.val.1))) :=
  (valInvRun ring hn hbank root lane src R hR hsrc hend word _ hz
    ⟨valCorrInitial ring root lane src R _, exportValInitial ring root lane src R _,
      useValInitial ring root lane src R _, ledgerOkInitial ring root lane src R _⟩).2

/-- **Value reach**: exact frames and the value invariant. -/
def ValReach
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  FramesExact ring w.1.2 ∧ ValInv ring hbank root lane src R w.1

include hn hR hsrc hend in
/-- Every `windowNext` letter from a state with the window invariant keeps the value reach. -/
theorem valReachStep
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (h : ValReach ring hbank root lane src R w) :
    ValReach ring hbank root lane src R (windowNext ring hbank root lane src R w e) :=
  ⟨framesExactStep ring (piD w.1.1.val.1) w.1.2 e h.1,
    valInvBankStep ring hn hbank root lane src R hR hsrc hend w.1 hw.1 h.2 e⟩

/-- Value reach implies exact reach. -/
theorem exactOfValReach
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (h : ValReach ring hbank root lane src R w) :
    ExactReach ring hbank w := h.1

end Run

/-! ### The receipt from the operand facts -/

section Receipt

variable {n : Nat} (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)

/-- **Items 2 and 4 (open)**: crossing `chi i` carries a sampled atom (no base atom) whose
recorded sample was read on this lane at source cell `src + (R - 1 - i)`, with the tail set
exactly at the last cell. -/
def SitePin (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ i, i < R → ∃ s : DigitSample (compileAdvice (ceilLogTwo n)) n,
    (chi i).operand = some (.sampled s.id) ∧ DigitRecordedSample A s ∧ s.id.lane = lane ∧
    s.id.site = digitSite ring root (src + (R - 1 - i)) ∧ s.tail = decide (R - 1 - i = 0)

/-- **Item 3 (open)**: the terminal's ledger is launched clean, and its `j`-th use, made after
`t0`, reads the operand of `chi (R - 1 - j)`. -/
def UseTrack (t0 : Nat) (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n,
    U.ledger = some L ∧ L.inherited = none ∧
    ∀ j (u : DigitUse (compileAdvice (ceilLogTwo n)) n), L.uses[j]? = some u →
      u.operand = (chi (R - 1 - j)).operand ∧ t0 < u.time

/-- **`ChiSampled` from the site pin**: values and tails from `ExportVal` and sample
uniqueness, sample times from the frame order and the distinct correspondence. -/
theorem chiSampledOf (hR : 2 ≤ R) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hfo : AuditFrameOrder A) (hxv : ExportVal ring root lane src R A)
    (htime : ∀ (x : DigitExport (compileAdvice (ceilLogTwo n)) n) (id : DigitStamp n),
      DigitRecordedExport A x → OnEdge ring root lane src R x →
      x.operand = some (.sampled id) → id.time < x.time ∧ x.time ≤ A.clock)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hchi : ∀ i, i < R → DigitRecordedExport A (chi i) ∧ OnEdge ring root lane src R (chi i))
    (hpin : SitePin ring root lane src R A chi) :
    ChiSampled ring root lane src R A chi := by
  have hpin' : ∀ i, ∃ s : DigitSample (compileAdvice (ceilLogTwo n)) n, i < R →
      (chi i).operand = some (.sampled s.id) ∧ DigitRecordedSample A s ∧ s.id.lane = lane ∧
      s.id.site = digitSite ring root (src + (R - 1 - i)) ∧ s.tail = decide (R - 1 - i = 0) := by
    intro i
    by_cases hi : i < R
    · obtain ⟨s, hs⟩ := hpin i hi
      exact ⟨s, fun _ => hs⟩
    · obtain ⟨s, -⟩ := hpin 0 (by omega)
      exact ⟨s, fun h => absurd h hi⟩
  refine ⟨fun i => Classical.choose (hpin' i), fun i hi => ?_⟩
  obtain ⟨ho, hrec, hl, hsite, htl⟩ := Classical.choose_spec (hpin' i) hi
  try dsimp only
  generalize Classical.choose (hpin' i) = s at ho hrec hl hsite htl ⊢
  obtain ⟨hcr, hon⟩ := hchi i hi
  have hpos : 0 < s.id.time := by
    obtain ⟨f, hf, h1, -⟩ := hrec
    rw [← h1]
    exact (hfo.2.1 f hf).1
  obtain ⟨s', hs', hid', hv', ht'⟩ := hxv (chi i) hcr hon s.id ho
  have hss := sampleUnique A hfo s' s hs' hrec hid'
  subst hss
  exact ⟨hrec, ho, hl, hsite, hpos, (htime (chi i) _ hcr hon ho).1, hv'.symm, ht'.symm, htl⟩

theorem lengthOfGet {α : Type} (l : List α) (j : Nat) (a : α) (h : l[j]? = some a) :
    j < l.length := by
  rcases Nat.lt_or_ge j l.length with h1 | h1
  · exact h1
  · rw [List.getElem?_eq_none h1] at h
    cases h

/-- **The use clause of `receiptOfCore` from the operand tracking**: lengths and order from the
clean ledger (`LedgerOk`), values and tails from `UseVal`, `ExportVal` and sample uniqueness. -/
theorem closeUsesOf (hR : 2 ≤ R) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hfo : AuditFrameOrder A) (hxv : ExportVal ring root lane src R A)
    (huv : UseVal ring root lane src R A) (hlo : LedgerOk ring root lane src R A)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hchi : ∀ i, i < R → DigitRecordedExport A (chi i) ∧ OnEdge ring root lane src R (chi i) ∧
      ∃ id, (chi i).operand = some (.sampled id))
    (t0 : Nat) (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hU : DigitRecordedTerminal A U) (hUl : U.lane = lane)
    (hUs : U.source = digitSite ring root (src + (2 * R - 1)))
    (hop : UseTrack R t0 U chi) :
    ∃ L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n,
      U.ledger = some L ∧ L.inherited = none ∧ L.uses.length = R ∧
      UsesOk ring root src R U.time L.uses ∧
      ∀ j (u : DigitUse (compileAdvice (ceilLogTwo n)) n), L.uses[j]? = some u →
        u.operand = (chi (R - 1 - j)).operand ∧ u.value = (chi (R - 1 - j)).value ∧
        u.tail = (chi (R - 1 - j)).tail ∧ t0 < u.time := by
  obtain ⟨L, hL, hcl, hops⟩ := hop
  obtain ⟨hlen, hok⟩ := terminalCleanUses ring root lane src R hR A hlo U hU hUl hUs L hL hcl
  refine ⟨L, hL, hcl, hlen, hok, fun j u hj => ?_⟩
  obtain ⟨ho, ht⟩ := hops j u hj
  have hjR : j < R := by
    have := lengthOfGet L.uses j u hj
    omega
  obtain ⟨hr, hon, id, hid⟩ := hchi (R - 1 - j) (by omega)
  have hmem : u ∈ L.uses := List.mem_of_getElem? hj
  obtain ⟨hv, htl⟩ := useMatchesExport ring root lane src R A hfo hxv huv _ hr hon U hU hUl hUs
    L hL u hmem id hid ho
  exact ⟨ho, hv, htl, ht⟩

end Receipt

section Assembly

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

include hR in
/-- **The receipt from the operand facts**: at a cycle start `wc` with exact frames, ordered
frames and the delimiter-time clause of the distinct correspondence, a core window `chi` with the
site pin, and a terminal `U` recorded later with the value invariant there and the operand
tracking, `U` has its receipt. -/
theorem receiptOfPins
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hfe : FramesExact ring wc.1.2) (hfo : AuditFrameOrder wc.1.2)
    (hxv0 : ExportVal ring root lane src R wc.1.2)
    (htime : ∀ (x : DigitExport (compileAdvice (ceilLogTwo n)) n) (id : DigitStamp n),
      DigitRecordedExport wc.1.2 x → OnEdge ring root lane src R x →
      x.operand = some (.sampled id) → id.time < x.time ∧ x.time ≤ wc.1.2.clock)
    (hval : ValInv ring hbank root lane src R
      (word.foldl (windowNext ring hbank root lane src R) wc).1)
    (hU : DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U)
    (hUl : U.lane = lane) (hUs : U.source = digitSite ring root (src + (2 * R - 1)))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hcore : ChiCore ring hbank root lane src R wc chi)
    (hpin : SitePin ring root lane src R wc.1.2 chi)
    (hop : UseTrack R wc.1.2.clock U chi) :
    CloseReceipt ring hbank root lane src R wc U := by
  have hfoF : AuditFrameOrder (word.foldl (windowNext ring hbank root lane src R) wc).1.2 :=
    auditFold ring hbank root lane src R AuditFrameOrder
      (fun S A e hA => auditFrameOrderStep ring S A e hA) word wc hfo
  have hsamp := chiSampledOf ring root lane src R hR wc.1.2 hfo hxv0 htime chi
    (fun i hi => (hcore.1 i hi)) hpin
  have hchiF : ∀ i, i < R →
      DigitRecordedExport (word.foldl (windowNext ring hbank root lane src R) wc).1.2 (chi i) ∧
      OnEdge ring root lane src R (chi i) ∧ ∃ id, (chi i).operand = some (.sampled id) := by
    intro i hi
    obtain ⟨s, hs, -⟩ := hpin i hi
    exact ⟨auditFold ring hbank root lane src R (fun A => DigitRecordedExport A (chi i))
      (fun S A e hA => recordedExportStep ring S A e _ hA) word wc (hcore.1 i hi).1,
      (hcore.1 i hi).2, s.id, hs⟩
  obtain ⟨-, hxvF, huvF, hloF⟩ := hval
  exact receiptOfCore ring hbank root lane src R hR wc word U hfe hU hUs chi hcore hsamp
    (closeUsesOf ring root lane src R hR _ hfoF hxvF huvF hloF chi hchiF wc.1.2.clock U hU hUl
      hUs hop)

end Assembly

end L3.ValueLedger

#print axioms L3.ValueLedger.replayCarryXUse
#print axioms L3.ValueLedger.replayCarryYUse
#print axioms L3.ValueLedger.sampleUnique
#print axioms L3.ValueLedger.exportValStep
#print axioms L3.ValueLedger.useValStep
#print axioms L3.ValueLedger.valInvRun
#print axioms L3.ValueLedger.valInvFromStart
#print axioms L3.ValueLedger.valReachStep
#print axioms L3.ValueLedger.chiSampledOf
#print axioms L3.ValueLedger.closeUsesOf
#print axioms L3.ValueLedger.receiptOfPins

import Leader.L3.Bank.RepairDigitValueRows

/-!
# T32 item 1: the value correspondence on the pair

`ValCorr`: on one lane of the pair `[src, src + R)`, `[src + R, src + 2R)`, every sampled ghost
atom sitting on a physical token with a value records that value: a source output `D v T` whose
ghost atom is `.sampled id`, and a target input `P v T` / `S v T` whose ghost atom is
`.sampled id`, have a recorded sample with stamp `id`, value `v` and tail `T` (`SampVal`).

Every letter of the projected ring keeps it (`valCorrStep`), with the layout hypotheses of
`ghostCorrStep`. The local rows `pipeVal`, `delVal`, `finVal`, `termVal` pair T32's valued rows
(`L3.ValueRows`) with T25's ghost rows; a freshly read slot is the letter's recorded sample with
the cell's digit (`freshVal`).
-/

namespace L3.ValueCorr

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortSites
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.ValueRows

/-! ### Cells -/

section Cells

variable {c : Compiled} {n : Nat}

/-- A recorded sample with stamp `id`, value `v` and tail `T`. -/
def SampVal (A : DigitAudit c n) (id : DigitStamp n) (v : Fin c.topA) (T : Bool) : Prop :=
  ∃ s : DigitSample c n, DigitRecordedSample A s ∧ s.id = id ∧ s.value = v ∧ s.tail = T

/-- A sampled atom carries value `v` and tail `T`. -/
def AtomSV (A : DigitAudit c n) (a : Option (DigitAtom n)) (v : Fin c.topA) (T : Bool) : Prop :=
  ∀ id, a = some (.sampled id) → SampVal A id v T

/-- Output cell: a data packet's sampled atom carries the packet's value and tail. -/
def OutVal (A : DigitAudit c n) : OutTok c.topA → DigitOutGhost n → Prop
  | .D v T, g => AtomSV A g.atom v T
  | _, _ => True

/-- Input cell: a pending or settled input's sampled atom carries its value and tail. -/
def InVal (A : DigitAudit c n) : InTok c.topA → Option (DigitAtom n) → Prop
  | .P v T, a => AtomSV A a v T
  | .S v T, a => AtomSV A a v T
  | _, _ => True

theorem atomSVFresh {A : DigitAudit c n} {id : DigitStamp n} {v : Fin c.topA} {T : Bool}
    (h : SampVal A id v T) : AtomSV A (some (.sampled id)) v T := by
  intro id' he
  simp only [Option.some.injEq, DigitAtom.sampled.injEq] at he
  subst he
  exact h

theorem pipeVal (A : DigitAudit c n) (stamp : DigitStamp n) (bx : Bool) (d : Fin c.topA)
    (ox oy : OutTok c.topA) (gxo gyo : DigitOutGhost n)
    (hx : OutVal A ox gxo) (hy : OutVal A oy gyo) (hnew : ox = .U → SampVal A stamp d bx) :
    OutVal A (vPipe bx d ox oy).1
      (ghostPipe stamp bx (bankRepairDigitOutShOf ox) (bankRepairDigitOutShOf oy) gxo gyo).1 ∧
    OutVal A (vPipe bx d ox oy).2
      (ghostPipe stamp bx (bankRepairDigitOutShOf ox) (bankRepairDigitOutShOf oy) gxo gyo).2 := by
  rcases ox with _ | _ | ⟨v, T⟩ <;> rcases oy with _ | _ | ⟨v', T'⟩ <;> cases bx <;>
    (try cases T) <;>
    simp [vPipe, ghostPipe, bankRepairDigitOutShOf, OutVal, DigitOutGhost.atom] at hx hy ⊢ <;>
    (repeat' constructor) <;>
    first | assumption | exact atomSVFresh (hnew rfl) | (intro id hid; simp at hid)

theorem delVal (A : DigitAudit c n) (stamp : DigitStamp n) (d : Fin c.topA)
    (ox : OutTok c.topA) (iy : InTok c.topA) (ky : Bool)
    (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n))
    (hx : OutVal A ox gxo) (hy : InVal A iy gyi) (hnew : ox = .U → SampVal A stamp d false) :
    OutVal A (vDel d ox iy ky).1
      (ghostDel stamp (bankRepairDigitOutShOf ox) (bankRepairDigitInShOf iy) ky gxo gyi).1 ∧
    InVal A (vDel d ox iy ky).2.1
      (ghostDel stamp (bankRepairDigitOutShOf ox) (bankRepairDigitInShOf iy) ky gxo gyi).2 := by
  rcases ox with _ | _ | ⟨v, T⟩ <;> rcases iy with _ | _ | ⟨v', T'⟩ | ⟨v', T'⟩ <;> cases ky <;>
    (try cases T) <;>
    simp [vDel, ghostDel, bankRepairDigitOutShOf, bankRepairDigitInShOf, OutVal, InVal,
      DigitOutGhost.atom] at hx hy ⊢ <;>
    (repeat' constructor) <;>
    first | assumption | exact atomSVFresh (hnew rfl) | (intro id hid; simp at hid)

theorem finVal (A : DigitAudit c n) (bx : Bool) (ix : InTok c.topA) (kx : Bool)
    (iy : InTok c.topA) (ky : Bool) (gxi gyi : Option (DigitAtom n))
    (hx : InVal A ix gxi) (hy : InVal A iy gyi) :
    InVal A (vFin bx ix kx iy ky).1
      (finInX bx (bankRepairDigitInShOf ix) kx (bankRepairDigitInShOf iy) ky gxi) ∧
    InVal A (vFin bx ix kx iy ky).2.2.1
      (finInY (bankRepairDigitInShOf ix) kx (bankRepairDigitInShOf iy) ky gxi gyi) := by
  rcases ix with _ | _ | ⟨v, T⟩ | ⟨v, T⟩ <;> rcases iy with _ | _ | ⟨v', T'⟩ | ⟨v', T'⟩ <;>
    cases kx <;> cases ky <;> cases bx <;> (try cases T) <;>
    simp [vFin, finInX, finInY, finInYFree, finXP, finYX, finYP, shS, bankRepairDigitInShOf,
      InVal] at hx hy ⊢ <;>
    (repeat' constructor) <;>
    first | assumption | (intro id hid; simp at hid)

theorem termVal (A : DigitAudit c n) (ix : InTok c.topA) (kx : Bool)
    (gxi : Option (DigitAtom n)) (hx : InVal A ix gxi) :
    InVal A (vTerm ix kx).1 (ghostTermIn (bankRepairDigitInShOf ix) kx gxi) := by
  rcases ix with _ | _ | ⟨v, T⟩ | ⟨v, T⟩ <;> cases kx <;> (try cases T) <;>
    simp [vTerm, ghostTermIn, bankRepairDigitInShOf, InVal] at hx ⊢ <;>
    first | assumption | trivial | (intro id hid; simp at hid)

end Cells

/-! ### Monotonicity and the fresh sample -/

section Mono

variable {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
  (A : DigitAudit c n) (e : Fin n)

theorem sampValStep {id : DigitStamp n} {v : Fin c.topA} {T : Bool} (h : SampVal A id v T) :
    SampVal (digitAuditStep ring S A e) id v T := by
  obtain ⟨s, h1, h2⟩ := h
  exact ⟨s, recordedSampleStep ring S A e s h1, h2⟩

theorem atomSVStep {a : Option (DigitAtom n)} {v : Fin c.topA} {T : Bool}
    (h : AtomSV A a v T) : AtomSV (digitAuditStep ring S A e) a v T :=
  fun id hid => sampValStep ring S A e (h id hid)

theorem outValStep {o : OutTok c.topA} {g : DigitOutGhost n} (h : OutVal A o g) :
    OutVal (digitAuditStep ring S A e) o g := by
  cases o with
  | D v T => exact atomSVStep ring S A e h
  | _ => trivial

theorem inValStep {i : InTok c.topA} {a : Option (DigitAtom n)} (h : InVal A i a) :
    InVal (digitAuditStep ring S A e) i a := by
  cases i with
  | P v T => exact atomSVStep ring S A e h
  | S v T => exact atomSVStep ring S A e h
  | _ => trivial

/-- A freshly read slot is the letter's recorded sample, with the cell's digit and the left
marker as tail. -/
theorem freshVal (lane : DigitLane) (b : Bool) (hlx : (S e).word.native.l = false)
    (hly : (S (ring.rightNeighbor e)).word.native.l = false)
    (hU : bankRepairDigitLaneOut lane (S e).top = .U)
    (hm : laneMarkerX lane (S e) (S (ring.rightNeighbor e)) = b) :
    SampVal (digitAuditStep ring S A e) (DigitStamp.mk (A.clock + 1) e lane) (S e).top.d b := by
  obtain ⟨s, h1, h2, h3, h4, -⟩ := recordUnreadReadD lane (A.clock + 1) e (ring.rightNeighbor e)
    (S e) (S (ring.rightNeighbor e)) (A.current e) (A.current (ring.rightNeighbor e)) hlx hly
    (by rw [hU]; rfl)
  refine ⟨s, ⟨DigitFrame.mk (A.clock + 1) e S A.current (svcAt ring S A e),
    List.mem_cons.mpr (Or.inl rfl), ?_, ?_, ?_, ?_⟩, h2, h4, h3.trans hm⟩
  · rw [h2]
  · rw [h2]
  · rw [h2]
    exact h1
  · rw [h4]

end Mono

/-! ### The correspondence on the ring -/

section Ring

variable {c : Compiled} {n : Nat}

/-- **The value correspondence** of one lane on the pair. -/
def ValCorr (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  (∀ q, q < R → OutVal A (bankRepairDigitLaneOut lane (S (digitSite ring root (src + q))).top)
      (laneCells ring root lane src A.current q).out) ∧
  (∀ q, R ≤ q → q < 2 * R →
    InVal A (bankRepairDigitLaneIn lane (S (digitSite ring root (src + q))).top)
      (laneCells ring root lane src A.current q).input)

theorem siteNe (ring : DirectedRing n) (root : Fin n) (src j q : Nat) (hj : j < n)
    (hq : src + q < n) (hpos : 0 < src + q) (n1 : src + q ≠ j) (n2 : src + q ≠ j + 1) :
    digitSite ring root (src + q) ≠ digitSite ring root j ∧
      digitSite ring root (src + q) ≠ ring.rightNeighbor (digitSite ring root j) := by
  constructor
  · intro he
    exact n1 (bankRepairDigitSiteInj ring root hq hj he)
  · intro he
    rw [← bankRepairDigitSiteSucc] at he
    by_cases hjn : j + 1 < n
    · exact n2 (bankRepairDigitSiteInj ring root hq hjn he)
    · rw [show j + 1 = n by omega, bankRepairDigitSiteN] at he
      have := bankRepairDigitSiteInj ring root (k := src + q) (m := 0) hq (by omega) he
      omega

/-- **Every letter preserves the value correspondence** (projected ring, layout hypotheses of
`ghostCorrStep`). -/
theorem valCorrStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    (h : ValCorr ring root lane src R S A) :
    ValCorr ring root lane src R (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)) := by
  obtain ⟨pX, pY, pFar, -⟩ := bankRepairDigitPhiDAt ring hn S (digitSite ring root j) hbX hbY
  have ho : ∀ q, q < R → OutVal (digitAuditStep ring S A (digitSite ring root j))
      (bankRepairDigitLaneOut lane (S (digitSite ring root (src + q))).top)
      (laneCells ring root lane src A.current q).out :=
    fun q hq => outValStep ring S A _ (h.1 q hq)
  have hi : ∀ q, R ≤ q → q < 2 * R → InVal (digitAuditStep ring S A (digitSite ring root j))
      (bankRepairDigitLaneIn lane (S (digitSite ring root (src + q))).top)
      (laneCells ring root lane src A.current q).input :=
    fun q h1 h2 => inValStep ring S A _ (h.2 q h1 h2)
  have frame : ∀ q, q < 2 * R → src + q ≠ j → src + q ≠ j + 1 →
      phiD ring S (digitSite ring root j) (digitSite ring root (src + q)) =
        S (digitSite ring root (src + q)) ∧
      laneCells ring root lane src (digitAuditStep ring S A (digitSite ring root j)).current q =
        laneCells ring root lane src A.current q := by
    intro q hq n1 n2
    have hne := siteNe ring root src j q hj (by omega) (by omega) n1 n2
    refine ⟨pFar _ hne.1 hne.2, ?_⟩
    unfold laneCells
    rw [curFar ring S A _ _ hne.1 hne.2]
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
    have cX : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current k =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).x := by
      unfold laneCells
      rw [curX]
    have cY : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1) =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).y := by
      unfold laneCells
      rw [show digitSite ring root (src + (k + 1)) =
        ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring hn]
    have tX : (phiD ring S (digitSite ring root (src + k)) (digitSite ring root (src + k))).top =
        (bankRepairDigitTopPairOf c (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1)))).x := pX
    have tY : (phiD ring S (digitSite ring root (src + k))
        (digitSite ring root (src + (k + 1)))).top =
        (bankRepairDigitTopPairOf c (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1)))).y := pY
    by_cases h1 : k + 1 < R
    · -- Pipe
      have hbx : (S (digitSite ring root (src + k))).word.beta = decide (k = 0) := by
        by_cases hk0 : k = 0
        · rw [decide_eq_true hk0, hk0]
          exact hb0
        · rw [decide_eq_false hk0]
          exact hbF k (by omega) (by omega) (by omega)
      have hby : (S (digitSite ring root (src + k + 1))).word.beta = false :=
        hbF (k + 1) (by omega) (by omega) (by omega)
      have hmX : laneMarkerX lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = (S (digitSite ring root (src + k))).word.beta :=
        laneMarkerXBeta lane _ _ hbX
      have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = false := by
        rw [laneMarkerYBeta lane _ _ hbY]
        exact hby
      have hrow := rowPipeD lane (A.clock + 1) (digitSite ring root (src + k))
        (ring.rightNeighbor (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
        (A.current (digitSite ring root (src + k)))
        (A.current (digitSite ring root (src + k + 1))) hlx hly hmy
      rw [hmX] at hrow
      have hval := pipeValD c lane (S (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k + 1))) hlx hly hby
      have pv := pipeVal (digitAuditStep ring S A (digitSite ring root (src + k)))
        (DigitStamp.mk (A.clock + 1) (digitSite ring root (src + k)) lane)
        (S (digitSite ring root (src + k))).word.beta (S (digitSite ring root (src + k))).top.d
        (bankRepairDigitLaneOut lane (S (digitSite ring root (src + k))).top)
        (bankRepairDigitLaneOut lane (S (digitSite ring root (src + k + 1))).top)
        (laneCells ring root lane src A.current k).out
        (laneCells ring root lane src A.current (k + 1)).out
        (ho k (by omega)) (ho (k + 1) h1)
        (fun hU => freshVal ring S A _ lane _ hlx hly hU hmX)
      refine ⟨fun q hq => ?_, fun q hq1 hq2 => ?_⟩
      · by_cases hqk : q = k
        · rw [hqk, tX, cX]
          have v1 := congrArg Prod.fst hval
          dsimp only at v1
          rw [v1]
          exact (congrArg (OutVal _ _) (congrArg Prod.fst hrow)).mpr pv.1
        · by_cases hqk1 : q = k + 1
          · rw [hqk1, tY, cY]
            have v2 := congrArg Prod.snd hval
            dsimp only at v2
            rw [v2]
            exact (congrArg (OutVal _ _) (congrArg Prod.snd hrow)).mpr pv.2
          · rw [(frame q (by omega) (by omega) (by omega)).1,
              (frame q (by omega) (by omega) (by omega)).2]
            exact ho q hq
      · rw [(frame q hq2 (by omega) (by omega)).1, (frame q hq2 (by omega) (by omega)).2]
        exact hi q hq1 hq2
    · by_cases h2 : k + 1 = R
      · -- Del
        have hbx : (S (digitSite ring root (src + k))).word.beta = false :=
          hbF k (by omega) (by omega) (by omega)
        have hby : (S (digitSite ring root (src + k + 1))).word.beta = true := by
          rw [show src + k + 1 = src + R by omega]
          exact hbR
        have hmx : laneMarkerX lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))) = false := by
          rw [laneMarkerXBeta lane _ _ hbX]
          exact hbx
        have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))) = true := by
          rw [laneMarkerYBeta lane _ _ hbY]
          exact hby
        have hrow := (rowDelD lane (A.clock + 1) (digitSite ring root (src + k))
          (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly hmx hmy).1
        have hval := delValD c lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) hlx hly hbx hby
        have dv := delVal (digitAuditStep ring S A (digitSite ring root (src + k)))
          (DigitStamp.mk (A.clock + 1) (digitSite ring root (src + k)) lane)
          (S (digitSite ring root (src + k))).top.d
          (bankRepairDigitLaneOut lane (S (digitSite ring root (src + k))).top)
          (bankRepairDigitLaneIn lane (S (digitSite ring root (src + k + 1))).top)
          (bankRepairDigitLaneLive lane (S (digitSite ring root (src + k + 1))).top)
          (laneCells ring root lane src A.current k).out
          (laneCells ring root lane src A.current (k + 1)).input
          (ho k (by omega)) (hi (k + 1) (by omega) (by omega))
          (fun hU => freshVal ring S A _ lane _ hlx hly hU hmx)
        refine ⟨fun q hq => ?_, fun q hq1 hq2 => ?_⟩
        · by_cases hqk : q = k
          · rw [hqk, tX, cX]
            have v1 := congrArg Prod.fst hval
            dsimp only at v1
            rw [v1]
            exact (congrArg (OutVal _ _) (congrArg Prod.fst hrow)).mpr dv.1
          · rw [(frame q (by omega) (by omega) (by omega)).1,
              (frame q (by omega) (by omega) (by omega)).2]
            exact ho q hq
        · by_cases hqk1 : q = k + 1
          · rw [hqk1, tY, cY]
            have v2 := congrArg (fun p => p.2.1) hval
            dsimp only at v2
            rw [v2]
            exact (congrArg (InVal _ _) (congrArg Prod.snd hrow)).mpr dv.2
          · rw [(frame q hq2 (by omega) (by omega)).1, (frame q hq2 (by omega) (by omega)).2]
            exact hi q hq1 hq2
      · by_cases h3 : k + 1 < 2 * R
        · -- Fin
          have hby : (S (digitSite ring root (src + k + 1))).word.beta = false :=
            hbF (k + 1) (by omega) (by omega) (by omega)
          have hmX : laneMarkerX lane (S (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k + 1))) =
              (S (digitSite ring root (src + k))).word.beta :=
            laneMarkerXBeta lane _ _ hbX
          have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k + 1))) = false := by
            rw [laneMarkerYBeta lane _ _ hbY]
            exact hby
          have hrow := (rowFinD lane (A.clock + 1) (digitSite ring root (src + k))
            (ring.rightNeighbor (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
            (A.current (digitSite ring root (src + k)))
            (A.current (digitSite ring root (src + k + 1))) hlx hly hmy).1
          rw [hmX] at hrow
          have hval := finValD c lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))) hlx hly hby
          have fv := finVal (digitAuditStep ring S A (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k))).word.beta
            (bankRepairDigitLaneIn lane (S (digitSite ring root (src + k))).top)
            (bankRepairDigitLaneLive lane (S (digitSite ring root (src + k))).top)
            (bankRepairDigitLaneIn lane (S (digitSite ring root (src + k + 1))).top)
            (bankRepairDigitLaneLive lane (S (digitSite ring root (src + k + 1))).top)
            (laneCells ring root lane src A.current k).input
            (laneCells ring root lane src A.current (k + 1)).input
            (hi k (by omega) (by omega)) (hi (k + 1) (by omega) h3)
          refine ⟨fun q hq => ?_, fun q hq1 hq2 => ?_⟩
          · rw [(frame q (by omega) (by omega) (by omega)).1,
              (frame q (by omega) (by omega) (by omega)).2]
            exact ho q hq
          · by_cases hqk : q = k
            · rw [hqk, tX, cX]
              have v1 := congrArg Prod.fst hval
              dsimp only at v1
              rw [v1]
              exact (congrArg (InVal _ _) (congrArg Prod.fst hrow)).mpr fv.1
            · by_cases hqk1 : q = k + 1
              · rw [hqk1, tY, cY]
                have v2 := congrArg (fun p => p.2.2.1) hval
                dsimp only at v2
                rw [v2]
                exact (congrArg (InVal _ _) (congrArg Prod.snd hrow)).mpr fv.2
              · rw [(frame q hq2 (by omega) (by omega)).1,
                  (frame q hq2 (by omega) (by omega)).2]
                exact hi q hq1 hq2
        · -- Term
          have hbx : (S (digitSite ring root (src + k))).word.beta = false :=
            hbF k (by omega) (by omega) (by omega)
          have hby : (S (digitSite ring root (src + k + 1))).word.beta = true := by
            rw [show src + k + 1 = src + 2 * R by omega]
            exact hb2R
          have hmx : laneMarkerX lane (S (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k + 1))) = false := by
            rw [laneMarkerXBeta lane _ _ hbX]
            exact hbx
          have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k + 1))) = true := by
            rw [laneMarkerYBeta lane _ _ hbY]
            exact hby
          have hrow := (rowTermD lane (A.clock + 1) (digitSite ring root (src + k))
            (ring.rightNeighbor (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
            (A.current (digitSite ring root (src + k)))
            (A.current (digitSite ring root (src + k + 1))) hlx hly hmx hmy).1
          have hval := termValD c lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))) hlx hly hbx hby
          have tv := termVal (digitAuditStep ring S A (digitSite ring root (src + k)))
            (bankRepairDigitLaneIn lane (S (digitSite ring root (src + k))).top)
            (bankRepairDigitLaneLive lane (S (digitSite ring root (src + k))).top)
            (laneCells ring root lane src A.current k).input (hi k (by omega) (by omega))
          refine ⟨fun q hq => ?_, fun q hq1 hq2 => ?_⟩
          · rw [(frame q (by omega) (by omega) (by omega)).1,
              (frame q (by omega) (by omega) (by omega)).2]
            exact ho q hq
          · by_cases hqk : q = k
            · rw [hqk, tX, cX]
              have v1 := congrArg Prod.fst hval
              dsimp only at v1
              rw [v1]
              exact (congrArg (InVal _ _) hrow).mpr tv
            · rw [(frame q hq2 (by omega) (by omega)).1, (frame q hq2 (by omega) (by omega)).2]
              exact hi q hq1 hq2
  · by_cases h1 : j + 1 = src
    · -- Entry
      have hlx := bankRepairDigitSiteNonroot ring root S hroot j (by omega) (by omega)
      have hly := bankRepairDigitSiteNonroot ring root S hroot (j + 1) (by omega) (by omega)
      have hby : (S (digitSite ring root (j + 1))).word.beta = true := by
        rw [h1]
        exact hb0
      have hmy : laneMarkerY lane (S (digitSite ring root j))
          (S (digitSite ring root (j + 1))) = true := by
        rw [laneMarkerYBeta lane _ _ hbY]
        exact hby
      have hs : digitSite ring root (src + 0) = ring.rightNeighbor (digitSite ring root j) := by
        rw [← h1]
        rfl
      refine ⟨fun q hq => ?_, fun q hq1 hq2 => ?_⟩
      · by_cases hq0 : q = 0
        · rw [hq0]
          show OutVal _ (bankRepairDigitLaneOut lane
              (phiD ring S (digitSite ring root j) (digitSite ring root (src + 0))).top)
            (laneGhost lane ((digitAuditStep ring S A (digitSite ring root j)).current
              (digitSite ring root (src + 0)))).out
          have hy := ho 0 (by omega)
          unfold laneCells at hy
          rw [hs] at hy
          have e1 : bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c
              (S (digitSite ring root j)) (S (ring.rightNeighbor (digitSite ring root j)))).y =
              bankRepairDigitLaneOut lane (S (ring.rightNeighbor (digitSite ring root j))).top :=
            bankRepairDigitEntryRowD c lane _ _ hlx hly hby
          have e2 : (laneGhost lane (svcAt ring S A (digitSite ring root j)).y).out =
              (laneGhost lane (A.current (ring.rightNeighbor (digitSite ring root j)))).out :=
            rowEntryD lane (A.clock + 1) (digitSite ring root j)
              (ring.rightNeighbor (digitSite ring root j)) (S (digitSite ring root j))
              (S (digitSite ring root (j + 1))) (A.current (digitSite ring root j))
              (A.current (digitSite ring root (j + 1))) hlx hly hmy
          rw [hs, pY, curY ring hn, e1, e2]
          exact hy
        · rw [(frame q (by omega) (by omega) (by omega)).1,
            (frame q (by omega) (by omega) (by omega)).2]
          exact ho q hq
      · rw [(frame q hq2 (by omega) (by omega)).1, (frame q hq2 (by omega) (by omega)).2]
        exact hi q hq1 hq2
    · -- Far
      refine ⟨fun q hq => ?_, fun q hq1 hq2 => ?_⟩
      · rw [(frame q (by omega) (by omega) (by omega)).1,
          (frame q (by omega) (by omega) (by omega)).2]
        exact ho q hq
      · rw [(frame q hq2 (by omega) (by omega)).1, (frame q hq2 (by omega) (by omega)).2]
        exact hi q hq1 hq2

end Ring

end L3.ValueCorr

#print axioms L3.ValueCorr.pipeVal
#print axioms L3.ValueCorr.delVal
#print axioms L3.ValueCorr.finVal
#print axioms L3.ValueCorr.termVal
#print axioms L3.ValueCorr.valCorrStep

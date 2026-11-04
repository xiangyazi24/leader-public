import Leader.L3.Bank.RepairDigitCohortWindow

/-!
# T28 item 1: the distinct correspondence inside the window, and the atoms of the crossings

`WinInvD` is T27's window invariant `WinInv` with T27's distinct correspondence
`GhostCorrDistinct` inside it, and with the crossing map `chi` matched to the slots
(`ChiAtoms`): the export `chi i` of every crossed slot `i` carries the atom slot `i` held on the
delimiter cell when it crossed, an atom of slot `i`'s provenance class (a base atom or a recorded
sample of the lane read at a source cell) with slot `i`'s tail bit `cohortTail R i`.

At a closing letter (`windowClosingD`) the closed window has, besides T27's facts, pairwise
distinct sampled operands (a sample is exported at most once on the delimiter edge) and each
sampled operand stamped before its export.
-/

namespace L3.CohortClose

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow

/-! ### The atoms of the crossings -/

section Atoms

variable {c : Compiled} {n : Nat}

/-- Every crossed slot's export carries an atom of the slot's provenance class with the slot's
tail bit. -/
def ChiAtoms (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (A : DigitAudit c n) (lam : Nat → Nat)
    (chi : Nat → DigitExport c n) : Prop :=
  ∀ i, i < R → R ≤ cohortPos R lam i →
    ∃ a, (chi i).operand = some a ∧ GhostOk ring root lane src R Base A (cohortTail R i) a

theorem chiAtomsStart (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (A : DigitAudit c n) (chi : Nat → DigitExport c n) :
    ChiAtoms ring root lane src R Base A (fun _ => 0) chi := by
  intro i hi hc
  have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
  omega

/-- The delimiter-edge export carries the atom of the delimiter cell's output ghost. -/
theorem delOperand (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n)
    (hbX : (pairW (S (digitSite ring root (src + (R - 1)))).word
      (S (digitSite ring root (src + (R - 1) + 1))).word).1.beta =
        (S (digitSite ring root (src + (R - 1)))).word.beta)
    (hbY : (pairW (S (digitSite ring root (src + (R - 1)))).word
      (S (digitSite ring root (src + (R - 1) + 1))).word).2.beta =
        (S (digitSite ring root (src + (R - 1) + 1))).word.beta) :
    ∀ x : DigitExport c n,
      (digitReceiptLane lane (svcAt ring S A (digitSite ring root (src + (R - 1))))).exported =
        some x →
      x.operand = (laneCells ring root lane src A.current (R - 1)).out.atom := by
  have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + (R - 1)) (by omega) (by omega)
  have hly := bankRepairDigitSiteNonroot ring root S hroot (src + (R - 1) + 1) (by omega)
    (by omega)
  have hmx : laneMarkerX lane (S (digitSite ring root (src + (R - 1))))
      (S (digitSite ring root (src + (R - 1) + 1))) = false := by
    rw [laneMarkerXBeta lane _ _ hbX]
    exact hbF (R - 1) (by omega) (by omega) (by omega)
  have hmy : laneMarkerY lane (S (digitSite ring root (src + (R - 1))))
      (S (digitSite ring root (src + (R - 1) + 1))) = true := by
    rw [laneMarkerYBeta lane _ _ hbY, show src + (R - 1) + 1 = src + R by omega]
    exact hbR
  intro x hx
  exact (delExportD lane (A.clock + 1) (digitSite ring root (src + (R - 1)))
    (ring.rightNeighbor (digitSite ring root (src + (R - 1))))
    (S (digitSite ring root (src + (R - 1)))) (S (digitSite ring root (src + (R - 1) + 1)))
    (A.current (digitSite ring root (src + (R - 1))))
    (A.current (digitSite ring root (src + (R - 1) + 1))) hlx hly hmx hmy x hx).1

/-- **Atom step**: in a cycle, the slot crossing at the letter takes the delimiter cell's atom,
which carries the slot's provenance class with its tail bit; older crossings keep theirs. -/
theorem chiAtomsStep (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n)
    (ke : Option Nat)
    (hedge : ke = some (R - 1) → e = digitSite ring root (src + (R - 1)))
    (hdel : e = digitSite ring root (src + (R - 1)) →
      DelFacts ring lane S A e (cohortProj ring root lane src R S) R)
    (hop : e = digitSite ring root (src + (R - 1)) → ∀ x : DigitExport c n,
      (digitReceiptLane lane (svcAt ring S A e)).exported = some x →
      x.operand = (laneCells ring root lane src A.current (R - 1)).out.atom)
    (hcorr : GhostCorr ring root lane src R Base S A)
    {jj o : Nat} {g : (Nat → Nat) × Nat}
    (hcyc : CohortCycIn R jj (cohortProj ring root lane src R S) g o)
    (chi : Nat → DigitExport c n) (ha : ChiAtoms ring root lane src R Base A g.1 chi) :
    ChiAtoms ring root lane src R Base (digitAuditStep ring S A e)
      (cohortGenStep R (cohortProj ring root lane src R S) g.1 ke)
      (chiNext ring root lane src R S A e g.1 chi) := by
  obtain ⟨-, hg, -, -⟩ := hcyc
  have hch := hg.2
  have hR := hch.two
  unfold GhostCorr at hcorr
  intro i hi hc'
  by_cases hc : R ≤ cohortPos R g.1 i
  · have hn : chiNext ring root lane src R S A e g.1 chi i = chi i := by
      unfold chiNext
      exact if_neg (fun hh => by have := hh.1; omega)
    rw [hn]
    obtain ⟨a, h1, h2⟩ := ha i hi hc
    exact ⟨a, h1, ghostOkStep ring root lane src R Base S A e _ a h2⟩
  · rcases genStepCases (R := R) (s := cohortProj ring root lane src R S) (lam := g.1) ke i with
      h | ⟨hk, -, -, ht1, ht2, h⟩
    · unfold cohortPos at hc hc'
      rw [h] at hc'
      exact absurd hc' hc
    · have hpi : cohortPos R g.1 i = R - 1 := by
        unfold cohortPos at hc hc' ⊢
        rw [h] at hc'
        omega
      rw [hpi] at hk ht1 ht2
      have he := hedge hk
      have hD : (cohortProj ring root lane src R S).out (R - 1) = .D (cohortTail R i) := by
        rcases hch.pkt i hi with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [hpi, cohortTokSrc _ (by omega : R - 1 < R)] at h1
          exact tokOutPkt h1
        · rw [hpi, cohortTokSrc _ (by omega : R - 1 < R)] at h1
          exact absurd h1 (cohortTokOutNe _ _)
        · rw [hpi] at h1
          exact absurd h1 ht1
      rw [show R - 1 + 1 = R by omega, cohortTokTgt _ (Nat.le_refl R)] at ht2
      obtain ⟨hE, hL⟩ := tokInEmpty ht2
      obtain ⟨x, hx, -, -, -⟩ := (hdel he).2 _ hD hE hL
      have hchi : chiNext ring root lane src R S A e g.1 chi i = x := by
        unfold chiNext
        rw [if_pos ⟨hpi, he⟩, hx]
        rfl
      rw [hchi, hop he x hx]
      have hoc := hcorr.1 (R - 1) (by omega)
      rw [hD] at hoc
      have hoc' : optOk (GhostOk ring root lane src R Base A (cohortTail R i))
          (laneCells ring root lane src A.current (R - 1)).out.atom := hoc
      cases hat : (laneCells ring root lane src A.current (R - 1)).out.atom with
      | none =>
        rw [hat] at hoc'
        exact hoc'.elim
      | some a =>
        rw [hat] at hoc'
        exact ⟨a, rfl, ghostOkStep ring root lane src R Base S A e _ a hoc'⟩

end Atoms

/-! ### The strengthened window invariant on the coupled chain -/

section WindowRunD

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- **The window invariant with M1 inside**: layout, ordered frames, the distinct
correspondence, the cycle class with the cycle ghost, and a window whose crossings carry the
slots' atoms. -/
def WinInvD (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) : Prop :=
  CohortLayout ring hbank root src R z.1 ∧ AuditFrameOrder z.2 ∧
  GhostCorrDistinct ring root lane src R Base (piD z.1.val.1) z.2 ∧
  (∃ o, CohortCycIn R g.2 (cohortProj ring root lane src R (piD z.1.val.1)) g o) ∧
  ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
    CycWin ring root lane src R z.2 g.1 chi t0 ∧ ChiAtoms ring root lane src R Base z.2 g.1 chi

theorem winInvOfD
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (h : WinInvD ring hbank root lane src R Base z g) :
    WinInv ring hbank root lane src R z g := by
  obtain ⟨h1, h2, -, h4, chi, t0, h5, -⟩ := h
  exact ⟨h1, h2, h4, chi, t0, h5⟩

include hn hR hsrc hend in
/-- **Step of the strengthened window invariant**: every letter keeps `WinInvD`; the arrival
counter stays, or advances by one with a closed window whose crossings carry the atoms. -/
theorem winInvDStep
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (h : WinInvD ring hbank root lane src R Base z g) (e : Fin n) :
    WinInvD ring hbank root lane src R Base (bankRepairDigitBoundaryAuditNext ring hbank z e)
      (windowGhost ring hbank root lane src R z g e) ∧
    ((windowGhost ring hbank root lane src R z g e).2 = g.2 ∨
      ((windowGhost ring hbank root lane src R z g e).2 = g.2 + 1 ∧
        ∃ (lam : Nat → Nat) (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
          (t0 : Nat), gridDone R R lam ∧
          CycWin ring root lane src R (bankRepairDigitBoundaryAuditNext ring hbank z e).2 lam
            chi t0 ∧
          ChiAtoms ring root lane src R Base (bankRepairDigitBoundaryAuditNext ring hbank z e).2
            lam chi)) := by
  obtain ⟨hlay, hfo, hgd, ⟨o, hcyc⟩, chi, t0, hw, ha⟩ := h
  have hgd' := (ghostCorrDistinctBankStep ring hn hbank root lane src R hR hsrc hend Base z hlay
    hgd e).2
  obtain ⟨hlay', hproj⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend z.1 hlay e
  have hfo' : AuditFrameOrder (bankRepairDigitBoundaryAuditNext ring hbank z e).2 :=
    auditFrameOrderStep ring (piD z.1.val.1) z.2 e hfo
  have hcs := cohortCycStep hcyc (cohortEdgeOf root src R e)
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hedge : cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) →
      digitSite ring root jx = digitSite ring root (src + (R - 1)) := fun hk => by
    rw [edgeOfSome ring root src R jx (R - 1) hj hk]
  have hkeDel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) := fun he => by
    rw [he]
    exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
  have hdel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      DelFacts ring lane (piD z.1.val.1) z.2 (digitSite ring root jx)
        (cohortProj ring root lane src R (piD z.1.val.1)) R := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delEdgeFacts ring root (piD z.1.val.1) R src hR hend hroot hbR hbF lane z.2 hbX hbY
  have hop : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
        (digitReceiptLane lane (svcAt ring (piD z.1.val.1) z.2 (digitSite ring root jx))).exported =
          some x →
        x.operand = (laneCells ring root lane src z.2.current (R - 1)).out.atom := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delOperand ring root (piD z.1.val.1) R src hR hend hroot hbR hbF lane z.2 hbX hbY
  have hw' := cycWinStep ring root lane src R (piD z.1.val.1) z.2 hfo (digitSite ring root jx)
    (cohortProj ring root lane src R (piD z.1.val.1))
    (cohortEdgeOf root src R (digitSite ring root jx)) hedge hkeDel hdel hcyc chi t0 hw
  have ha' := chiAtomsStep ring root lane src R Base (piD z.1.val.1) z.2 (digitSite ring root jx)
    (cohortEdgeOf root src R (digitSite ring root jx)) hedge hdel hop hgd.1 hcyc chi ha
  have hcyc' : ∃ o', CohortCycIn R (windowGhost ring hbank root lane src R z g
      (digitSite ring root jx)).2
      (cohortProj ring root lane src R
        (piD (bankRepairDigitBoundaryAuditNext ring hbank z (digitSite ring root jx)).1.val.1))
      (windowGhost ring hbank root lane src R z g (digitSite ring root jx)) o' := by
    show ∃ o', CohortCycIn R _ (cohortProj ring root lane src R
      (piD (bankRepairNext ring hbank z.1 (digitSite ring root jx)).val.1)) _ o'
    rw [hproj]
    rcases hcs with ⟨o', -, hin, -⟩ | hst
    · refine ⟨o', ?_⟩
      unfold windowGhost
      rw [hin.1]
      exact hin
    · refine ⟨0, ?_⟩
      unfold windowGhost
      rw [hst.1]
      exact hst
  unfold windowGhost cohortCycleGhost at hcyc' ⊢
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD z.1.val.1))
      g.1 (cohortEdgeOf root src R (digitSite ring root jx)))
  · rw [if_pos hd] at hcyc' ⊢
    exact ⟨⟨hlay', hfo', hgd', hcyc', chi, _,
      cycWinStart ring root lane src R _ hfo' chi, chiAtomsStart ring root lane src R Base _ chi⟩,
      Or.inr ⟨rfl, _, _, t0, hd, hw', ha'⟩⟩
  · rw [if_neg hd] at hcyc' ⊢
    exact ⟨⟨hlay', hfo', hgd', hcyc', _, t0, hw', ha'⟩, Or.inl rfl⟩

include hn hR hsrc hend in
/-- The strengthened window invariant along every coupled word. -/
theorem winInvDRun (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      WinInvD ring hbank root lane src R Base w.1 w.2 →
      WinInvD ring hbank root lane src R Base
        (word.foldl (windowNext ring hbank root lane src R) w).1
        (word.foldl (windowNext ring hbank root lane src R) w).2 := by
  induction word with
  | nil => intro w h; exact h
  | cons e rest ih =>
      intro w h
      exact ih _ (winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 h e).1

include hR in
/-- The strengthened window invariant at the T24 cycle entry (cycle `0`, nothing crossed). -/
theorem winInvDEntry
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1) (hfo : AuditFrameOrder z.2)
    (hgd : GhostCorrDistinct ring root lane src R Base (piD z.1.val.1) z.2)
    (hset : CohortSettling R 0 (cohortProj ring root lane src R (piD z.1.val.1)))
    (hyng : ∀ q, q < R →
      cohortTok R (cohortProj ring root lane src R (piD z.1.val.1)) q = .other ∨
      cohortTok R (cohortProj ring root lane src R (piD z.1.val.1)) q = .pkt (decide (q = 0)))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) :
    WinInvD ring hbank root lane src R Base z ((fun _ => 0), 0) :=
  ⟨hz, hfo, hgd, ⟨0, cohortCycEntry hR hset hyng⟩, chi, _,
    cycWinStart ring root lane src R z.2 hfo chi, chiAtomsStart ring root lane src R Base _ chi⟩

include hn hR hsrc hend in
/-- **hclose part A at a closing letter**: when a letter completes an arrival, the closed window
`chi` has every slot crossed, recorded on the delimiter edge with increasing times; the crossing
of slot `i` carries an atom of slot `i`'s provenance class with tail bit `cohortTail R i`; the
sampled operands of distinct slots are distinct and stamped before their exports; and along every
continuation the delimiter-edge exports between `chi 0` and `chi (R - 1)` are crossings. -/
theorem windowClosingD
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (h : WinInvD ring hbank root lane src R Base w.1 w.2) (e : Fin n)
    (hcl : (windowNext ring hbank root lane src R w e).2.2 = w.2.2 + 1) :
    ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
      (∀ i, i < R →
        DigitRecordedExport (windowNext ring hbank root lane src R w e).1.2 (chi i) ∧
        OnEdge ring root lane src R (chi i) ∧ t0 < (chi i).time ∧
        ∃ a, (chi i).operand = some a ∧
          GhostOk ring root lane src R Base (windowNext ring hbank root lane src R w e).1.2
            (cohortTail R i) a) ∧
      (∀ a b, a < b → b < R → (chi a).time < (chi b).time) ∧
      (∀ a b (id : DigitStamp n), a < R → b < R → (chi a).operand = some (.sampled id) →
        (chi b).operand = some (.sampled id) → a = b) ∧
      (∀ i (id : DigitStamp n), i < R → (chi i).operand = some (.sampled id) →
        id.time < (chi i).time) ∧
      ∀ (word : List (Fin n)) (x : DigitExport (compileAdvice (ceilLogTwo n)) n),
        DigitRecordedExport
          (word.foldl (windowNext ring hbank root lane src R)
            (windowNext ring hbank root lane src R w e)).1.2 x →
        OnEdge ring root lane src R x → (chi 0).time ≤ x.time →
        x.time ≤ (chi (R - 1)).time → ∃ i, i < R ∧ x = chi i := by
  have hfo' : AuditFrameOrder (windowNext ring hbank root lane src R w e).1.2 :=
    auditFrameOrderStep ring (piD w.1.1.val.1) w.1.2 e h.2.1
  obtain ⟨hnext, hs⟩ := winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 h e
  have hgd' := hnext.2.2.1
  rcases hs with hs | hs
  · have : (windowNext ring hbank root lane src R w e).2.2 = w.2.2 := hs
    omega
  · obtain ⟨-, lam, chi, t0, hd, hw, ha⟩ := hs
    have hc : ∀ i, i < R → R ≤ cohortPos R lam i := by
      intro i hi
      have := hd i hi
      unfold cohortPos
      omega
    have hmono : ∀ a b, a < b → b < R → (chi a).time < (chi b).time :=
      fun a b hab hb => hw.2.2.2 a b hab hb (hc b hb)
    refine ⟨chi, t0, fun i hi => ?_, hmono, ?_, ?_, fun word x hx ho h1 h2 => ?_⟩
    · obtain ⟨r1, r2, r3⟩ := hw.2.2.1 i hi (hc i hi)
      exact ⟨r1, r2, r3, ha i hi (hc i hi)⟩
    · intro a b id ha' hb' hopa hopb
      have heq := hgd'.2.2.2.2.2 (chi a) (chi b) id (hw.2.2.1 a ha' (hc a ha')).1
        (hw.2.2.1 b hb' (hc b hb')).1 (hw.2.2.1 a ha' (hc a ha')).2.1
        (hw.2.2.1 b hb' (hc b hb')).2.1 hopa hopb
      rcases Nat.lt_trichotomy a b with hab | hab | hab
      · have := hmono a b hab hb'
        rw [heq] at this
        omega
      · exact hab
      · have := hmono b a hab ha'
        rw [heq] at this
        omega
    · intro i id hi hop
      exact (hgd'.2.2.2.1 (chi i) id (hw.2.2.1 i hi (hc i hi)).1
        (hw.2.2.1 i hi (hc i hi)).2.1 hop).1
    · exact noExtraExport ring root lane src R hR _ _ hfo'
        (exportsBackRun ring hbank root lane src R word _) lam chi t0 hw hd x hx ho h1 h2

end WindowRunD

end L3.CohortClose

#print axioms L3.CohortClose.chiAtomsStep
#print axioms L3.CohortClose.winInvDStep
#print axioms L3.CohortClose.winInvDRun
#print axioms L3.CohortClose.windowClosingD

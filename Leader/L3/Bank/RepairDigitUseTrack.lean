import Leader.L3.Bank.RepairDigitUseCells

/-!
# T33: target-cell operand tracking and the restricted receipt without the premise

T32 proved the per-block clock from the premise `SitePin.UseFact`. That premise is stated on
`PinReach` states, and `PinReach` says nothing about *which* atom sits in a target cell: it pins
the crossings' sample sites (`SitePin`), not the identity of the target-cell atoms, and a source
cell is read many times (stamps carry the time). So the identity has to be carried as an
invariant. This module carries it and proves the receipt on the strengthened reach class.

* `IdState` (items 1 and 2): the current window `chi` with T32's window clauses, every crossed
  chosen slot's target cell holding exactly `(chi i).operand` (`CurIdA`), and after the first
  arrival the last closed window `chiOld` (with T32's `LastClose`) whose operand is held by every
  target cell that is not a chosen slot position, until it is consumed (`OldIdA`). Carried by
  every letter (`idStateStep`): the cell rows move an atom only by a hop into an empty cell or by
  the delimiter acceptance, and no tombstone `X` is ever off a live target cell, so the Fin row in
  which an `X` input overwrites a settled cell never fires on the pair (`UseCells.tgtNoX`).
* `UseReach := PinReach ∧ IdState`, carried by every letter (`useReachStep`), holding at every
  `PinReach` cycle start of the entrance cycle (`useReachOfStart`).
* `RunInv` (items 2 and 3): from a block entrance `wc` on, every ledger on a target cell `q` is
  clean (`inherited = none`), has `q + 1 - R` uses whose `m`-th reads `(chiOld (R-1-m)).operand`
  and is made after `wc`; every terminal on the terminal edge recorded after `wc` carries such a
  ledger with `R` uses (`runInvRun`).
* **Item 4**: `useFactReach` (the operand tracking at every reachable block entrance, for the
  window closed there) and `useFactOn` (T32's `UseFact` with `UseReach` in place of `PinReach`,
  for every latest core window `chi`: two latest core windows agree, `windowUnique`); then
  `hCloseOnPinReach`, `oldCompletionPinReach`, `pinCoupledBlockReach` with no premise.
  `useFactOfOn` reads T32's `UseFact` as `UseFactOn PinReach`; that instance is not claimed:
  `PinReach` alone does not determine the target-cell atoms (the closing state of `JustClosed`
  comes from an arbitrary `WinInvD` state, whose target ghosts are only classed, not identified).
* **Item 5, the upstream obligation**: `pinCoupledBlockReach` takes, as its hypothesis `hA`,
  coupled start states satisfying `FiveInvOn … UseReach … ∧ w.2.2 = 0`. The final theorem
  `pinCoupledBlockStart` states the obligation in exact form as its hypothesis `hStart`: every
  start state lifts to a coupled state with `WinInvD` and `PinReach` **at a cycle start**
  (chosen ghost `lam = 0`) **in the entrance cycle** (arrival counter `0`), anchored after
  `after`. Then every block entrance comes at least one closing after the window chain starts,
  and the old cohort of each entrance crossed entirely inside the chain (`useReachOfStart`).
-/

namespace L3.UseTrack

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
open L3.CohortStages
open L3.CohortTransfer
open L3.CohortLedger
open L3.FiveTransfer
open L3.Projection
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
open L3.CohortClose
open L3.CohortOrder
open L3.BlockStart
open L3.FiveClose
open L3.HClose
open L3.CloseReceipt
open L3.FiveReach
open L3.ValueCorr
open L3.ValueLedger
open L3.SitePin
open L3.UseRows
open L3.UseCells

/-! ### Target cells of an audit -/

section Cells

variable {c : Compiled} {n : Nat}

/-- The input atoms of the cells `src + q`. -/
def inA (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src : Nat)
    (A : DigitAudit c n) : Nat → Option (DigitAtom n) :=
  fun q => (laneCells ring root lane src A.current q).input

/-- The carry ledgers of the cells `src + q`. -/
def caA (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src : Nat)
    (A : DigitAudit c n) : Nat → Option (DigitCarryGhost c n) :=
  fun q => (laneCells ring root lane src A.current q).carry

theorem recordedTerminalStepCases (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (U : DigitTerminal c n)
    (h : DigitRecordedTerminal (digitAuditStep ring S A e) U) :
    DigitRecordedTerminal A U ∨
      (U.time = A.clock + 1 ∧ U.source = e ∧
        (digitReceiptLane U.lane (svcAt ring S A e)).terminal = some U) := by
  obtain ⟨f, hf, h1, h2, h3⟩ := h
  rcases auditFrameMemStepCases ring S A e f hf with hf' | hf'
  · exact Or.inl ⟨f, hf', h1, h2, h3⟩
  · subst hf'
    exact Or.inr ⟨h1.symm, h2.symm, h3⟩

/-- At a cycle start no target cell is live. -/
theorem noLiveStart {R j : Nat} {s : CohortLane} {g : (Nat → Nat) × Nat}
    (h : CohortCycIn R j s g 0) (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) : s.live q = false := by
  cases hl : s.live q
  · rfl
  · exfalso
    have ht : cohortTok R s q = .other := by rw [cohortTokTgt s h1, hl]; exact tokInLive _
    rcases tgtRegion h q h1 h2 with ⟨i, hi, hp⟩ | ⟨-, he⟩ | ⟨-, -, ⟨T, hT⟩ | ⟨T, hT⟩⟩ |
        ⟨ho, -⟩ | ⟨ho, -⟩
    · subst hp
      exact chosenOtherLow h.2.1.2 hi h1 ht
    · rw [ht] at he; cases he
    · rw [ht] at hT; cases hT
    · rw [ht] at hT; cases hT
    · omega
    · omega

/-- **Two windows with the same last crossing agree**: if `chi` is interval-complete (every
recorded export of class `P` between its first and last crossing is one of its crossings),
`chi'` is a strictly increasing run of recorded `P`-exports no later than `chi`'s last crossing
and starting no earlier than `chi`'s first, then `chi' = chi` on `[0, R)`. -/
theorem windowUnique (A : DigitAudit c n) (P : DigitExport c n → Prop) (R : Nat) (hR : 1 ≤ R)
    (chi chi' : Nat → DigitExport c n)
    (h1' : ∀ i, i < R → DigitRecordedExport A (chi' i) ∧ P (chi' i))
    (h2 : ∀ a b, a < b → b < R → (chi a).time < (chi b).time)
    (h2' : ∀ a b, a < b → b < R → (chi' a).time < (chi' b).time)
    (h3 : ∀ x, DigitRecordedExport A x → P x → (chi 0).time ≤ x.time →
      x.time ≤ (chi (R - 1)).time → ∃ i, i < R ∧ x = chi i)
    (htop : (chi' (R - 1)).time ≤ (chi (R - 1)).time)
    (hbot : (chi 0).time ≤ (chi' 0).time) : ∀ j, j < R → chi' j = chi j := by
  have hex : ∀ j, ∃ i, j < R → i < R ∧ chi' j = chi i := by
    intro j
    by_cases hj : j < R
    · have hlo : (chi 0).time ≤ (chi' j).time := by
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0
          exact hbot
        · have := h2' 0 j hpos hj
          omega
      have hhi : (chi' j).time ≤ (chi (R - 1)).time := by
        rcases Nat.lt_or_ge j (R - 1) with hlt | hge
        · have := h2' j (R - 1) hlt (by omega)
          omega
        · have hj' : j = R - 1 := by omega
          subst hj'
          exact htop
      obtain ⟨i, hi, he⟩ := h3 (chi' j) (h1' j hj).1 (h1' j hj).2 hlo hhi
      exact ⟨i, fun _ => ⟨hi, he⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  have hσ : ∀ j, j < R → Classical.choose (hex j) < R ∧ chi' j = chi (Classical.choose (hex j)) :=
    fun j hj => Classical.choose_spec (hex j) hj
  have hmono : ∀ a b, a < b → b < R → Classical.choose (hex a) < Classical.choose (hex b) := by
    intro a b hab hb
    obtain ⟨ha1, ha2⟩ := hσ a (by omega)
    obtain ⟨hb1, hb2⟩ := hσ b hb
    have ht := h2' a b hab hb
    rw [ha2, hb2] at ht
    rcases Nat.lt_or_ge (Classical.choose (hex a)) (Classical.choose (hex b)) with h | h
    · exact h
    · exfalso
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · rw [h'] at ht
        omega
      · have := h2 _ _ h' ha1
        omega
  have hlow : ∀ j, j < R → j ≤ Classical.choose (hex j) := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have := hmono k (k + 1) (by omega) hk
      have := ih (by omega)
      omega
  have hup : ∀ k, k < R → Classical.choose (hex (R - 1 - k)) ≤ R - 1 - k := by
    intro k
    induction k with
    | zero =>
      intro _
      have := (hσ (R - 1) (by omega)).1
      omega
    | succ k ih =>
      intro hk
      have := hmono (R - 1 - (k + 1)) (R - 1 - k) (by omega) (by omega)
      have := ih (by omega)
      omega
  intro j hj
  have h4 := hup (R - 1 - j) (by omega)
  rw [show R - 1 - (R - 1 - j) = j by omega] at h4
  have h5 := hlow j hj
  rw [(hσ j hj).2, show Classical.choose (hex j) = j by omega]

end Cells

/-! ### One coupled letter on the target cells -/

section Window

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

include hn hR hsrc hend in
/-- **The target facts of one coupled letter**: the cycle class before, the chosen class after,
the correspondence before and after, the input and ledger rows (`MoveH`, `CarryH`), the
crossing map, the delimiter export, and the terminal receipt. -/
theorem letterRows
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (e : Fin n) :
    ∃ (o c' : Nat) (stamp : DigitStamp n) (gxo : DigitOutGhost n)
      (Ok Ok' : Bool → DigitAtom n → Prop),
      CohortCycIn R w.2.2 (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2 o ∧
      CohortChosen R (cohortLaneStep R (cohortProj ring root lane src R (piD w.1.1.val.1))
          (cohortEdgeOf root src R e))
        (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2.1
          (cohortEdgeOf root src R e)) c' ∧
      (∀ q, R ≤ q → q < 2 * R →
        InCorr Ok ((cohortProj ring root lane src R (piD w.1.1.val.1)).inp q)
          (inA ring root lane src w.1.2 q) ∧
        (cohortProj ring root lane src R (piD w.1.1.val.1)).live q =
          (caA ring root lane src w.1.2 q).isSome) ∧
      (∀ q, R ≤ q → q < 2 * R →
        InCorr Ok' ((cohortLaneStep R (cohortProj ring root lane src R (piD w.1.1.val.1))
          (cohortEdgeOf root src R e)).inp q)
          (inA ring root lane src (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e) q)) ∧
      MoveH R (cohortProj ring root lane src R (piD w.1.1.val.1)) (cohortEdgeOf root src R e)
        (inA ring root lane src w.1.2)
        (inA ring root lane src (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e)) stamp gxo ∧
      CarryH R (cohortProj ring root lane src R (piD w.1.1.val.1)) (cohortEdgeOf root src R e)
        (inA ring root lane src w.1.2) (caA ring root lane src w.1.2)
        (caA ring root lane src (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e))
        (w.1.2.clock + 1) ∧
      (∀ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (i : Nat),
        chiNext ring root lane src R (piD w.1.1.val.1) w.1.2 e w.2.1 chi i =
          if cohortPos R w.2.1 i = R - 1 ∧ cohortEdgeOf root src R e = some (R - 1) then
            ((digitReceiptLane lane (svcAt ring (piD w.1.1.val.1) w.1.2 e)).exported).getD
              (chi i)
          else chi i) ∧
      (cohortEdgeOf root src R e = some (R - 1) → ∀ T,
        (cohortProj ring root lane src R (piD w.1.1.val.1)).out (R - 1) = .D T →
        cohortTok R (cohortProj ring root lane src R (piD w.1.1.val.1)) R = .empty →
        ∃ x, (digitReceiptLane lane (svcAt ring (piD w.1.1.val.1) w.1.2 e)).exported = some x ∧
          x.operand = gxo.atom) ∧
      (∀ U : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
        (digitReceiptLane lane (svcAt ring (piD w.1.1.val.1) w.1.2 e)).terminal = some U →
        cohortEdgeOf root src R e = some (2 * R - 1) →
        (cohortProj ring root lane src R (piD w.1.1.val.1)).live (2 * R - 1) = true ∧
          U.ledger = caA ring root lane src w.1.2 (2 * R - 1)) := by
  obtain ⟨hlay, -, hgd, ⟨o, hcyc⟩, -⟩ := hw
  have hgd' := (ghostCorrDistinctBankStep ring hn hbank root lane src R hR hsrc hend Base w.1 hlay
    hgd e).2
  have hproj := (cohortBankStep ring hn hbank root lane src R hR hsrc hend w.1.1 hlay e).2
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root w.1.1 hL e
  obtain ⟨o', -, hgen', -, -⟩ :=
    cohortGenStepClosed hcyc.2.1 hcyc.2.2.1 hcyc.2.2.2 (cohortEdgeOf root src R e)
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hrows := tgtRows ring (by omega) root (piD w.1.1.val.1) R src hR hsrc hend hroot hbR hb2R
    hbF lane w.1.2 jx hj hbX hbY
  have hedge : cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) →
      digitSite ring root jx = digitSite ring root (src + (R - 1)) := fun hk => by
    rw [edgeOfSome ring root src R jx (R - 1) hj hk]
  have hkeDel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) := fun he => by
    rw [he]
    exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
  have hdel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      DelFacts ring lane (piD w.1.1.val.1) w.1.2 (digitSite ring root jx)
        (cohortProj ring root lane src R (piD w.1.1.val.1)) R := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delEdgeFacts ring root (piD w.1.1.val.1) R src hR hend hroot hbR hbF lane w.1.2 hbX hbY
  have hop : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
        (digitReceiptLane lane (svcAt ring (piD w.1.1.val.1) w.1.2
          (digitSite ring root jx))).exported = some x →
        x.operand = (laneCells ring root lane src w.1.2.current (R - 1)).out.atom := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delOperand ring root (piD w.1.1.val.1) R src hR hend hroot hbR hbF lane w.1.2 hbX hbY
  refine ⟨o, cohortBottom R o', DigitStamp.mk (w.1.2.clock + 1) (digitSite ring root jx) lane,
    (laneCells ring root lane src w.1.2.current (R - 1)).out, GhostOk ring root lane src R Base w.1.2,
    GhostOk ring root lane src R Base
      (digitAuditStep ring (piD w.1.1.val.1) w.1.2 (digitSite ring root jx)),
    hcyc, hgen'.2, fun q h1 h2 => hgd.1.2 q h1 h2, fun q h1 h2 => ?_,
    ⟨fun q h1 h2 h3 h4 => congrArg DigitLaneGhost.input (hrows.1 q h1 h2 h3 h4),
      fun hk => (hrows.2.1 hk).1, fun k hk h1 h2 => (hrows.2.2.1 k hk h1 h2).1,
      fun hk => (hrows.2.2.2 hk).1⟩,
    ⟨fun q h1 h2 h3 h4 => congrArg DigitLaneGhost.carry (hrows.1 q h1 h2 h3 h4),
      fun hk => (hrows.2.1 hk).2, fun k hk h1 h2 => (hrows.2.2.1 k hk h1 h2).2,
      fun hk => (hrows.2.2.2 hk).2.1⟩, fun chi i => ?_, ?_, fun U hU hk => ?_⟩
  · have hc := (hgd'.1.2 q h1 h2).1
    change InCorr _ ((cohortProj ring root lane src R
      (piD (bankRepairNext ring hbank w.1.1 (digitSite ring root jx)).val.1)).inp q)
      ((laneCells ring root lane src
        (digitAuditStep ring (piD w.1.1.val.1) w.1.2 (digitSite ring root jx)).current q).input)
      at hc
    rw [hproj] at hc
    exact hc
  · unfold chiNext
    by_cases hc : cohortPos R w.2.1 i = R - 1 ∧
        digitSite ring root jx = digitSite ring root (src + (R - 1))
    · rw [if_pos hc, if_pos ⟨hc.1, hkeDel hc.2⟩]
    · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, hedge h.2⟩)]
  · intro hk T hD hemp
    have he := hedge hk
    rw [cohortTokTgt _ (Nat.le_refl R)] at hemp
    obtain ⟨hE, hLv⟩ := inEmptyOf hemp
    obtain ⟨x, hx, -, -, -⟩ := (hdel he).2 T hD hE hLv
    exact ⟨x, hx, hop he x hx⟩
  · exact (hrows.2.2.2 hk).2.2 U hU

/-! ### Items 1 and 2: the identity state -/

/-- **The identity state**: the current window with T32's clauses and the target identity of its
crossed slots; after the first arrival, the last closed window with T32's `LastClose` and the
identity of the old target cells. -/
def IdState
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
    CycWin ring root lane src R w.1.2 w.2.1 chi t0 ∧
    ChiInv R (SPin ring root lane src w.1.2) chi w.2.1 ∧
    CurIdA R w.2.1 (inA ring root lane src w.1.2) chi ∧
    (1 ≤ w.2.2 → ∃ chiOld, LastClose ring hbank root lane src R w chiOld t0 ∧
      OldIdA R w.2.1 (inA ring root lane src w.1.2) chiOld)

include hn hR hsrc hend in
/-- **`IdState` is carried by every letter**; a closing letter turns the crossed slots' identity
into the old cells' identity for the window it closes. -/
theorem idStateStep
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (hp : PinState ring hbank root lane src R w)
    (h : IdState ring hbank root lane src R w) (e : Fin n) :
    IdState ring hbank root lane src R (windowNext ring hbank root lane src R w e) := by
  obtain ⟨-, -, hWs, hXs⟩ :=
    windowPinFacts ring hn hbank root lane src R hR hsrc hend Base w hw e
  have hfo' : AuditFrameOrder (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e) :=
    auditFrameOrderStep ring (piD w.1.1.val.1) w.1.2 e hw.2.1
  obtain ⟨o, c', stamp, gxo, Ok, Ok', hcyc, hch', hcorr, hcorr', hm, -, hchi, hxe, -⟩ :=
    letterRows ring hn hbank root lane src R hR hsrc hend Base w hw e
  obtain ⟨chi, t0, hcw, hci, hcur, hlast⟩ := h
  have hw' := hWs chi t0 hcw
  have hci' := hXs chi hp.1 hci
  have hcur' := curIdStep hcyc hch' (fun q h1 h2 => (hcorr q h1 h2).1) hcorr' hm chi _ _
    (hchi chi) hxe hcur
  have hA : (windowNext ring hbank root lane src R w e).1.2 =
      digitAuditStep ring (piD w.1.1.val.1) w.1.2 e := rfl
  have hg : (windowNext ring hbank root lane src R w e).2 =
      cohortCycleGhost R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2
        (cohortEdgeOf root src R e) := rfl
  unfold IdState LastClose
  rw [hA, hg]
  unfold cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1))
      w.2.1 (cohortEdgeOf root src R e))
  · rw [if_pos hd]
    dsimp only
    have hall : ∀ i, i < R → R ≤ cohortPos R (cohortGenStep R
        (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2.1 (cohortEdgeOf root src R e)) i := by
      intro i hi
      have := hd i hi
      unfold cohortPos
      omega
    refine ⟨chi, _, cycWinStart ring root lane src R _ hfo' chi, ?_, ?_, fun _ =>
        ⟨chiNext ring root lane src R (piD w.1.1.val.1) w.1.2 e w.2.1 chi, ⟨?_, ?_, ?_⟩,
          oldOfCur hch' hd _ hcur'⟩⟩
    · intro i hi hc
      have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
      omega
    · intro i hi hc
      have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
      omega
    · refine ⟨fun i hi => ⟨(hw'.2.2.1 i hi (hall i hi)).1, (hw'.2.2.1 i hi (hall i hi)).2.1⟩,
        fun a b hab hb => hw'.2.2.2 a b hab hb (hall b hb), fun word x hx ho h1 h2 => ?_⟩
      exact noExtraExport ring root lane src R hR _ _ hfo'
        (exportsBackRun ring hbank root lane src R word _) _ _ t0 hw' hd x hx ho h1 h2
    · intro i hi
      obtain ⟨a, ha, s, h1, h2, h3, h4, h5⟩ := hci' i hi (hall i hi)
      exact ⟨s, by rw [ha, h1], h2, h3, h4, h5⟩
    · intro x hx ho _
      by_cases hxt : t0 < x.time
      · obtain ⟨i, hi, -, rfl⟩ := hw'.2.1 x hx ho hxt
        rcases Nat.lt_or_ge i (R - 1) with hlt | hge
        · exact Nat.le_of_lt (hw'.2.2.2 i (R - 1) hlt (by omega) (hall _ (by omega)))
        · have hiR : i = R - 1 := by omega
          subst hiR
          exact Nat.le_refl _
      · have := (hw'.2.2.1 (R - 1) (by omega) (hall _ (by omega))).2.2
        omega
  · rw [if_neg hd]
    dsimp only
    refine ⟨_, t0, hw', hci', hcur', fun h1 => ?_⟩
    obtain ⟨chiOld, ⟨hcore, hpin, hlat⟩, hold⟩ := hlast h1
    refine ⟨chiOld, ⟨chiCoreStep ring hbank root lane src R w e chiOld hcore,
      sitePinStep ring root lane src R _ _ _ chiOld hpin, fun x hx ho ht => ?_⟩,
      oldIdStep hcyc hm chiOld hold⟩
    rcases recordedExportStepCases ring (piD w.1.1.val.1) w.1.2 _ x hx with hx' | ⟨hxt, -, -⟩
    · exact hlat x hx' ho ht
    · have := hcw.1
      omega

/-- **The strengthened reach class**: T32's `PinReach` and the identity state. -/
def UseReach
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  PinReach ring hbank root lane src R w ∧ IdState ring hbank root lane src R w

include hn hR hsrc hend in
theorem useReachStep
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (h : UseReach ring hbank root lane src R w) :
    UseReach ring hbank root lane src R (windowNext ring hbank root lane src R w e) :=
  ⟨pinReachStep ring hn hbank root lane src R hR hsrc hend Base w e hw h.1,
    idStateStep ring hn hbank root lane src R hR hsrc hend Base w hw h.1.2 h.2 e⟩

include hn hR hsrc hend in
theorem useReachRun (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      WinInvD ring hbank root lane src R Base w.1 w.2 → UseReach ring hbank root lane src R w →
      UseReach ring hbank root lane src R (word.foldl (windowNext ring hbank root lane src R) w) := by
  induction word with
  | nil => intro w _ h; exact h
  | cons e rest ih =>
      intro w hw h
      exact ih _ (winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 hw e).1
        (useReachStep ring hn hbank root lane src R hR hsrc hend Base w e hw h)

/-- **Entrance into the strengthened class**: a `PinReach` state at a cycle start (ghost
`lam = 0`) in the entrance cycle (no arrival yet) satisfies `UseReach`. -/
theorem useReachOfStart
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (h : PinReach ring hbank root lane src R w) (hfo : AuditFrameOrder w.1.2)
    (h0 : w.2.1 = fun _ => 0) (hc : w.2.2 = 0) :
    UseReach ring hbank root lane src R w := by
  refine ⟨h, ?_⟩
  obtain ⟨-, -, chi, -⟩ := h.2
  refine ⟨chi, w.1.2.clock, ?_, fun i hi hc' => ?_, fun i hi hc' => ?_, fun h1 => by omega⟩
  · rw [h0]
    exact cycWinStart ring root lane src R _ hfo chi
  · rw [h0] at hc'
    have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
    omega
  · rw [h0] at hc'
    have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
    omega

/-! ### Items 2 and 3: the run from a block entrance -/

/-- **The run invariant** from a block entrance stamped `t0` with closed window `chiOld`: the old
target cells' identity, clean ledgers reading the old operands after `t0`, and every terminal on
the terminal edge recorded after `t0` with the operand tracking. -/
def RunInv (t0 : Nat) (chiOld : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  t0 ≤ w.1.2.clock ∧ OldIdA R w.2.1 (inA ring root lane src w.1.2) chiOld ∧
  LedgerA R t0 chiOld (caA ring root lane src w.1.2) ∧
  ∀ U : DigitTerminal (compileAdvice (ceilLogTwo n)) n, DigitRecordedTerminal w.1.2 U →
    U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) → t0 < U.time →
    UseTrack R t0 U chiOld

theorem countStep
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n) :
    (windowNext ring hbank root lane src R w e).2.2 = w.2.2 ∨
      (windowNext ring hbank root lane src R w e).2.2 = w.2.2 + 1 := by
  show (cohortCycleGhost R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2
    (cohortEdgeOf root src R e)).2 = w.2.2 ∨
    (cohortCycleGhost R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2
    (cohortEdgeOf root src R e)).2 = w.2.2 + 1
  unfold cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1))
      w.2.1 (cohortEdgeOf root src R e))
  · rw [if_pos hd]
    exact Or.inr rfl
  · rw [if_neg hd]
    exact Or.inl rfl

theorem countRun (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      w.2.2 ≤ (word.foldl (windowNext ring hbank root lane src R) w).2.2 := by
  induction word with
  | nil => intro w; exact Nat.le_refl _
  | cons e rest ih =>
      intro w
      have h1 := ih (windowNext ring hbank root lane src R w e)
      rcases countStep ring hbank root lane src R w e with h2 | h2
      · show w.2.2 ≤ (rest.foldl (windowNext ring hbank root lane src R)
          (windowNext ring hbank root lane src R w e)).2.2
        omega
      · show w.2.2 ≤ (rest.foldl (windowNext ring hbank root lane src R)
          (windowNext ring hbank root lane src R w e)).2.2
        omega

include hn hR hsrc hend in
/-- **One non-closing letter keeps the run invariant**: launch, consumption and terminal. -/
theorem runInvStep (t0 : Nat) (chiOld : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (hc : (windowNext ring hbank root lane src R w e).2.2 = w.2.2)
    (h : RunInv ring hbank root lane src R t0 chiOld w) :
    RunInv ring hbank root lane src R t0 chiOld (windowNext ring hbank root lane src R w e) := by
  obtain ⟨o, c', stamp, gxo, Ok, Ok', hcyc, -, hcorr, -, hm, hcar, -, -, hterm⟩ :=
    letterRows ring hn hbank root lane src R hR hsrc hend Base w hw e
  obtain ⟨ht0, hold, hled, htm⟩ := h
  have hA : (windowNext ring hbank root lane src R w e).1.2 =
      digitAuditStep ring (piD w.1.1.val.1) w.1.2 e := rfl
  have hg : (windowNext ring hbank root lane src R w e).2 =
      cohortCycleGhost R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2
        (cohortEdgeOf root src R e) := rfl
  have hnd : ¬ gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1))
      w.2.1 (cohortEdgeOf root src R e)) := by
    intro hd
    rw [hg] at hc
    unfold cohortCycleGhost at hc
    rw [if_pos hd] at hc
    dsimp only at hc
    omega
  have hlam : (windowNext ring hbank root lane src R w e).2.1 =
      cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2.1
        (cohortEdgeOf root src R e) := by
    rw [hg]
    unfold cohortCycleGhost
    rw [if_neg hnd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA]
    show t0 ≤ w.1.2.clock + 1
    omega
  · rw [hlam, hA]
    exact oldIdStep hcyc hm chiOld hold
  · rw [hA]
    exact ledgerStep hcyc (fun q h1 h2 => (hcorr q h1 h2).1) (fun q h1 h2 => (hcorr q h1 h2).2)
      chiOld hold hcar (by omega) hled
  · rw [hA]
    intro U hU hUl hUs hUt
    rcases recordedTerminalStepCases ring (piD w.1.1.val.1) w.1.2 e U hU with hU' |
        ⟨-, hUe, hUr⟩
    · exact htm U hU' hUl hUs hUt
    · have he : e = digitSite ring root (src + (2 * R - 1)) := by rw [← hUe, hUs]
      have hk : cohortEdgeOf root src R e = some (2 * R - 1) := by
        rw [he]
        exact cohortEdgeOfSite ring root src R hend (2 * R - 1) (by omega)
      rw [hUl] at hUr
      obtain ⟨hlv, hled'⟩ := hterm U hUr hk
      obtain ⟨L, hL⟩ : ∃ L, caA ring root lane src w.1.2 (2 * R - 1) = some L := by
        have h3 := (hcorr (2 * R - 1) (by omega) (by omega)).2
        rw [hlv] at h3
        cases h0 : caA ring root lane src w.1.2 (2 * R - 1) with
        | none => rw [h0] at h3; cases h3
        | some L => exact ⟨L, rfl⟩
      obtain ⟨hi0, -, hops⟩ := hled (2 * R - 1) (by omega) (by omega) L hL
      exact ⟨L, by rw [hled', hL], hi0, fun j u hj => hops j u hj⟩

include hn hR hsrc hend in
theorem runInvRun (t0 : Nat) (chiOld : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      WinInvD ring hbank root lane src R Base w.1 w.2 →
      (word.foldl (windowNext ring hbank root lane src R) w).2.2 = w.2.2 →
      RunInv ring hbank root lane src R t0 chiOld w →
      RunInv ring hbank root lane src R t0 chiOld
        (word.foldl (windowNext ring hbank root lane src R) w) := by
  induction word with
  | nil => intro w _ _ h; exact h
  | cons e rest ih =>
      intro w hw hc h
      have hc' : (rest.foldl (windowNext ring hbank root lane src R)
          (windowNext ring hbank root lane src R w e)).2.2 = w.2.2 := hc
      have h1 := countRun ring hbank root lane src R rest (windowNext ring hbank root lane src R w e)
      have h2 := countStep ring hbank root lane src R w e
      have hce : (windowNext ring hbank root lane src R w e).2.2 = w.2.2 := by omega
      exact ih _ (winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 hw e).1
        (by rw [hce]; exact hc')
        (runInvStep ring hn hbank root lane src R hR hsrc hend Base t0 chiOld w e hw hce h)

include hn hR hsrc hend in
/-- At a block entrance the run invariant starts with the entrance clock: no target cell is live
and no terminal is recorded after the clock. -/
theorem runInvStart
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hjc : JustClosed ring hbank root lane src R Base wc)
    (chiOld : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hold : OldIdA R wc.2.1 (inA ring root lane src wc.1.2) chiOld) :
    RunInv ring hbank root lane src R wc.1.2.clock chiOld wc := by
  obtain ⟨hwd, hst⟩ := justClosedStart ring hn hbank root lane src R hR hsrc hend Base wc hjc
  refine ⟨Nat.le_refl _, hold, fun q h1 h2 L hL => ?_, fun U hU _ _ hUt => ?_⟩
  · exfalso
    have h3 := (hwd.2.2.1.1.2 q h1 h2).2
    rw [noLiveStart hst q h1 h2] at h3
    have h4 : caA ring root lane src wc.1.2 q = some L := hL
    unfold caA at h4
    rw [h4] at h3
    cases h3
  · exfalso
    obtain ⟨f, hf, ht, -⟩ := hU
    have := (hwd.2.1.2.1 f hf).2
    omega

/-! ### Item 4: the operand tracking and the receipt -/

include hn hR hsrc hend in
/-- **Item 4 (operand tracking) at every reachable block entrance**: the window closed there
satisfies T32's core clauses, site pin and latest-window clause, and every later terminal of the
old cohort on the terminal edge has a clean ledger whose `j`-th use, made after the entrance,
reads the operand of `chi (R - 1 - j)`. -/
theorem useFactReach
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (hre : UseReach ring hbank root lane src R wc)
    (hjc : JustClosed ring hbank root lane src R Base wc)
    (hcnt : (word.foldl (windowNext ring hbank root lane src R) wc).2.2 = wc.2.2) :
    ∃ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      ChiCore ring hbank root lane src R wc chi ∧ SitePin ring root lane src R wc.1.2 chi ∧
      (∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport wc.1.2 x →
        OnEdge ring root lane src R x → x.time ≤ (chi (R - 1)).time) ∧
      ∀ U : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
        DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U →
        U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) →
        wc.1.2.clock < U.time → UseTrack R wc.1.2.clock U chi := by
  obtain ⟨hwd, -⟩ := justClosedStart ring hn hbank root lane src R hR hsrc hend Base wc hjc
  obtain ⟨hlam, h1⟩ := justClosedLam ring hbank root lane src R Base wc hjc
  obtain ⟨-, chi', t0, hcw, -, -, hlast⟩ := hre
  obtain ⟨chi, ⟨hcore, hpin, hlat⟩, hold⟩ := hlast h1
  have hrun := runInvRun ring hn hbank root lane src R hR hsrc hend Base wc.1.2.clock chi word
    wc hwd hcnt (runInvStart ring hn hbank root lane src R hR hsrc hend Base wc hjc chi hold)
  refine ⟨chi, hcore, hpin, fun x hx ho => hlat x hx ho ?_, fun U hU hUl hUs hUt =>
    hrun.2.2.2 U hU hUl hUs hUt⟩
  rcases Nat.lt_or_ge t0 x.time with hlt | hge
  · exfalso
    obtain ⟨i, hi, hc, -⟩ := hcw.2.1 x hx ho hlt
    rw [hlam] at hc
    have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
    omega
  · exact hge

/-- T32's `UseFact` with the reach predicate as a parameter (`UseFact` is the case
`Reach := PinReach`). -/
def UseFactOn
    (Reach : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat) : Prop :=
  ∀ (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
    Reach wc → JustClosed ring hbank root lane src R Base wc →
    AnchorIn ring root lane src R after wc.1.2 → after ≤ wc.1.2.clock →
    (word.foldl (windowNext ring hbank root lane src R) wc).2.2 = wc.2.2 →
    OrderInv ring hbank root lane src R (word.foldl (windowNext ring hbank root lane src R) wc).1
      (word.foldl (windowNext ring hbank root lane src R) wc).2 wc.1.2.clock →
    DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U →
    U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) →
    wc.1.2.clock < U.time →
    ∀ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      ChiCore ring hbank root lane src R wc chi → SitePin ring root lane src R wc.1.2 chi →
      (∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport wc.1.2 x →
        OnEdge ring root lane src R x → x.time ≤ (chi (R - 1)).time) →
      UseTrack R wc.1.2.clock U chi

theorem useFactOfOn (after : Nat)
    (h : UseFactOn ring hbank root lane src R Base (PinReach ring hbank root lane src R) after) :
    UseFact ring hbank root lane src R Base after := h

include hn hR hsrc hend in
/-- **Item 4: `UseFact` on `UseReach` states**, for every latest core window `chi` (any two latest
core windows at the entrance agree, `windowUnique`). -/
theorem useFactOn (after : Nat) :
    UseFactOn ring hbank root lane src R Base (UseReach ring hbank root lane src R) after := by
  intro wc word U hre hjc _ _ hcnt _ hU hUl hUs hUt chi hcore _ hlat
  obtain ⟨hwd, -⟩ := justClosedStart ring hn hbank root lane src R hR hsrc hend Base wc hjc
  obtain ⟨chiO, hcoreO, -, hlatO, huse⟩ :=
    useFactReach ring hn hbank root lane src R hR hsrc hend Base wc word hre hjc hcnt
  have hfo := hwd.2.1
  have ht1 := hlat (chiO (R - 1)) (hcoreO.1 (R - 1) (by omega)).1 (hcoreO.1 (R - 1) (by omega)).2
  have ht2 := hlatO (chi (R - 1)) (hcore.1 (R - 1) (by omega)).1 (hcore.1 (R - 1) (by omega)).2
  have heq : ∀ j, j < R → chi j = chiO j := by
    rcases Nat.le_total (chi 0).time (chiO 0).time with hb | hb
    · intro j hj
      exact (windowUnique wc.1.2 (OnEdge ring root lane src R) R (by omega) chi chiO hcoreO.1
        hcore.2.1 hcoreO.2.1 (fun x hx ho h1 h2 => hcore.2.2 [] x hx ho h1 h2) ht1 hb j hj).symm
    · intro j hj
      exact windowUnique wc.1.2 (OnEdge ring root lane src R) R (by omega) chiO chi hcore.1
        hcoreO.2.1 hcore.2.1 (fun x hx ho h1 h2 => hcoreO.2.2 [] x hx ho h1 h2) ht2 hb j hj
  obtain ⟨L, hL, hcl, hops⟩ := huse U hU hUl hUs hUt
  refine ⟨L, hL, hcl, fun j u hj => ?_⟩
  rw [heq (R - 1 - j) (by omega)]
  exact hops j u hj

include hn hR hsrc hend in
/-- **The restricted receipt `HCloseOn` on `UseReach` states, with no premise.** -/
theorem hCloseOnPinReach (after : Nat) :
    HCloseOn ring hbank root lane src R Base (UseReach ring hbank root lane src R) after := by
  intro wc word U hre hjc hanc haft hcnt hord hU hUl hUs hUt
  obtain ⟨hwd, -⟩ := justClosedStart ring hn hbank root lane src R hR hsrc hend Base wc hjc
  obtain ⟨chi, hcore, hpin, -, huse⟩ :=
    useFactReach ring hn hbank root lane src R hR hsrc hend Base wc word hre hjc hcnt
  have hreF := pinReachRun ring hn hbank root lane src R hR hsrc hend Base word wc hwd hre.1
  exact receiptOfPins ring hbank root lane src R hR wc word U hre.1.1.1 hwd.2.1 hre.1.1.2.2.1
    hwd.2.2.1.2.2.2.1 hreF.1.2 hU hUl hUs chi hcore hpin (huse U hU hUl hUs hUt)

include hn hR hsrc hend in
/-- The completion obligation of the five-cohort transfer on `UseReach` states. -/
theorem oldCompletionPinReach (after : Nat) :
    OldCompletionOn ring hbank root lane src R Base (UseReach ring hbank root lane src R) after :=
  oldCompletionOn ring hn hbank root lane src R hR hsrc hend Base _ after
    (hCloseOnPinReach ring hn hbank root lane src R hR hsrc hend Base after)

include hn hR hsrc hend in
/-- **The per-block clock on `UseReach` states, with no premise** (T31's `fiveReachCoupledBlock`
with `Reach := UseReach`). The hypothesis `hA` is the upstream obligation: the start states are
coupled states in the entrance cycle carrying `FiveInvOn` for `UseReach` (by `useReachOfStart`,
any `PinReach` state at a cycle start in the entrance cycle carries `UseReach`). -/
theorem pinCoupledBlockReach (after : Nat)
    (P Q : BankReferenceState ring hbank → Prop)
    (hA : ∀ z, P z → ∃ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ (WinInvD ring hbank root lane src R Base w.1 w.2 ∧
        FiveInvOn ring hbank root lane src R Base (UseReach ring hbank root lane src R) after w ∧
        w.2.2 = 0))
    (hB : ∀ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      FwdChain ring w.1.2 root src (src + R) lane 5 after → Q w.1.1) :
    CoupledBlock ring hbank P Q (200 * n * R) :=
  fiveReachCoupledBlock ring hn hbank root lane src R hR hsrc hend Base
    (UseReach ring hbank root lane src R) after
    (fun w e hw h => useReachStep ring hn hbank root lane src R hR hsrc hend Base w e hw h)
    (oldCompletionPinReach ring hn hbank root lane src R hR hsrc hend Base after) P Q hA hB

include hn hR hsrc hend in
/-- **Item 5, the per-block clock from the upstream obligation**: `pinCoupledBlockReach` with the
start hypothesis `hStart` = T32 item 4's obligation in exact form: every start state lifts to a
coupled state with the window invariant and `PinReach` **at a cycle start** (chosen ghost
`lam = 0`, so the old cohort of every later block entrance had its whole crossing phase inside
the chain) **in the entrance cycle** (arrival counter `0`, so every block entrance comes at least
one closing after the chain starts), anchored after `after`. -/
theorem pinCoupledBlockStart (after : Nat)
    (P Q : BankReferenceState ring hbank → Prop)
    (hStart : ∀ z, P z → ∃ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ WinInvD ring hbank root lane src R Base w.1 w.2 ∧
        PinReach ring hbank root lane src R w ∧ w.2.1 = (fun _ => 0) ∧ w.2.2 = 0 ∧
        after ≤ w.1.2.clock ∧ AnchorIn ring root lane src R after w.1.2)
    (hB : ∀ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      FwdChain ring w.1.2 root src (src + R) lane 5 after → Q w.1.1) :
    CoupledBlock ring hbank P Q (200 * n * R) := by
  refine pinCoupledBlockReach ring hn hbank root lane src R hR hsrc hend Base after P Q
    (fun z hz => ?_) hB
  obtain ⟨w, hz, hw, hpr, h0, hc, haft, hanc⟩ := hStart z hz
  exact ⟨w, hz, hw, ⟨useReachOfStart ring hbank root lane src R w hpr hw.2.1 h0 hc,
    Or.inl ⟨hc, haft, hanc⟩⟩, hc⟩

end Window

end L3.UseTrack

#print axioms L3.UseTrack.letterRows
#print axioms L3.UseTrack.idStateStep
#print axioms L3.UseTrack.useReachRun
#print axioms L3.UseTrack.useReachOfStart
#print axioms L3.UseTrack.runInvRun
#print axioms L3.UseTrack.useFactReach
#print axioms L3.UseTrack.windowUnique
#print axioms L3.UseTrack.useFactOn
#print axioms L3.UseTrack.hCloseOnPinReach
#print axioms L3.UseTrack.oldCompletionPinReach
#print axioms L3.UseTrack.pinCoupledBlockReach
#print axioms L3.UseTrack.pinCoupledBlockStart

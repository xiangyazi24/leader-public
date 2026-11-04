import Leader.L3.Bank.RepairDigitGhostBridge

/-!
# T26 items 3-5: the BANK ghost correspondence

The BANK analogue of `CheckerPacketCorrespondence` (`GhostCorr`): on one interior pair, each
tracked cell of the masked lane (`cohortProj`) corresponds to the audit ghost at its site.

* source cells (`q < R`): output `E` ↔ ghost `.empty`, `U` ↔ an unread obligation, `D T` ↔ a
  packet whose atom is present and satisfies the provenance `GhostOk … T`;
* target cells (`R ≤ q < 2R`): input `E` ↔ no atom, `P T` / `S T` ↔ an atom with provenance
  `GhostOk … T`, and carry-live ↔ a ledger is present.

`GhostOk Base A T a`: `a` is a base atom (`Base T a`; at the audit start the inherited atoms,
`InheritedOk`) or a recorded sample of this lane (`DigitRecordedSample A`), read at a source cell
of the pair, with tail bit `T`.

Proved: the pure edge rows (`pipeCorr` … `termCorr`, `pureCorrPipe` … `pureCorrTerm`), the F1 rows
on record fields (`rowPipeD` … `rowEntryD`), preservation by every letter (`ghostCorrStep` on the
projected ring, `ghostCorrBankStep` on the coupled BANK x audit chain), the run lemma
(`ghostCorrRun`), the audit start (`ghostCorrInitial`, `ghostCorrFromStart`), the cycle entry
(`ghostCorrCycEntry`), and F4 (`nextCompletionExists`, `firstStrictCompletionExists`).
-/

namespace L3.Correspondence

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.CohortEntry
open L3.Rearm
open L3.Recording
open L3.GhostBridge

section Cells

variable {c : Compiled} {n : Nat}

def optOk (P : DigitAtom n → Prop) : Option (DigitAtom n) → Prop
  | none => False
  | some b => P b

/-- Output cell: kind for kind, and the packet's atom carries the provenance `Ok T`. -/
def OutCorr (Ok : Bool → DigitAtom n → Prop) : BankRepairDigitOutSh → DigitOutGhost n → Prop
  | .E, g => g = .empty
  | .U, g => g.obligation.isSome = true
  | .D T, g => optOk (Ok T) g.atom

/-- Input cell: empty ↔ no atom; pending and settled inputs carry the provenance `Ok T`; a
tombstone `X` carries no obligation. -/
def InCorr (Ok : Bool → DigitAtom n → Prop) : BankRepairDigitInSh → Option (DigitAtom n) → Prop
  | .E, a => a = none
  | .X, _ => True
  | .P T, a => optOk (Ok T) a
  | .S T, a => optOk (Ok T) a

theorem optOkMono {P Q : DigitAtom n → Prop} (h : ∀ a, P a → Q a) :
    ∀ o, optOk P o → optOk Q o
  | none, hp => hp
  | some a, hp => h a hp

theorem outCorrMono {Ok Ok' : Bool → DigitAtom n → Prop} (h : ∀ T a, Ok T a → Ok' T a)
    (o : BankRepairDigitOutSh) (g : DigitOutGhost n) (hc : OutCorr Ok o g) : OutCorr Ok' o g := by
  cases o with
  | E => exact hc
  | U => exact hc
  | D T => exact optOkMono (h T) _ hc

theorem inCorrMono {Ok Ok' : Bool → DigitAtom n → Prop} (h : ∀ T a, Ok T a → Ok' T a)
    (i : BankRepairDigitInSh) (a : Option (DigitAtom n)) (hc : InCorr Ok i a) : InCorr Ok' i a := by
  cases i with
  | E => exact hc
  | X => exact hc
  | P T => exact optOkMono (h T) _ hc
  | S T => exact optOkMono (h T) _ hc

/-! ### Pure row preservation (with F1's ghost rows) -/

theorem pipeCorr (Ok : Bool → DigitAtom n → Prop) (stamp : DigitStamp n) (bx : Bool)
    (ox oy : BankRepairDigitOutSh) (gxo gyo : DigitOutGhost n)
    (hx : OutCorr Ok ox gxo) (hy : OutCorr Ok oy gyo)
    (hnew : ox = .U → Ok bx (.sampled stamp)) :
    OutCorr Ok (bankRepairDigitPipeStep bx ox oy).1 (ghostPipe stamp bx ox oy gxo gyo).1 ∧
    OutCorr Ok (bankRepairDigitPipeStep bx ox oy).2 (ghostPipe stamp bx ox oy gxo gyo).2 := by
  rcases ox with _ | _ | T <;> rcases oy with _ | _ | T' <;> cases bx <;> (try cases T) <;>
    simp_all [OutCorr, ghostPipe, bankRepairDigitPipeStep, optOk, DigitOutGhost.atom,
      DigitOutGhost.obligation]

theorem delCorr (Ok : Bool → DigitAtom n → Prop) (stamp : DigitStamp n)
    (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n))
    (hx : OutCorr Ok ox gxo) (hy : InCorr Ok iy gyi)
    (hnew : ox = .U → Ok false (.sampled stamp)) :
    OutCorr Ok (bankRepairDigitDelStep ox iy ky).1 (ghostDel stamp ox iy ky gxo gyi).1 ∧
    InCorr Ok (bankRepairDigitDelStep ox iy ky).2.1 (ghostDel stamp ox iy ky gxo gyi).2 ∧
    (bankRepairDigitDelStep ox iy ky).2.2 = ky := by
  rcases ox with _ | _ | T <;> rcases iy with _ | _ | T' | T' <;> cases ky <;> (try cases T) <;>
    simp_all [OutCorr, InCorr, ghostDel, bankRepairDigitDelStep, optOk, DigitOutGhost.atom,
      DigitOutGhost.obligation]

theorem finCorr {c : Compiled} (Ok : Bool → DigitAtom n → Prop) (bx : Bool)
    (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh) (ky : Bool)
    (gxi gyi : Option (DigitAtom n)) (gxc gyc : Option (DigitCarryGhost c n))
    (hx : InCorr Ok ix gxi) (hy : InCorr Ok iy gyi)
    (hkx : kx = gxc.isSome) (hky : ky = gyc.isSome) :
    InCorr Ok (bankRepairDigitFinStep bx ix kx iy ky).1 (finInX bx ix kx iy ky gxi) ∧
    (bankRepairDigitFinStep bx ix kx iy ky).2.1 =
      (!kx && ((bx && shS ix) || gxc.isSome)) ∧
    InCorr Ok (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 (finInY ix kx iy ky gxi gyi) ∧
    (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 =
      ((kx && !ky && shS iy) || gyc.isSome) := by
  rw [← hkx, ← hky]
  rcases ix with _ | _ | T | T <;> rcases iy with _ | _ | T' | T' <;> cases kx <;> cases ky <;>
    cases bx <;> (try cases T) <;>
    simp_all [InCorr, bankRepairDigitFinStep, finInX, finInY, finInYFree, finXP, finYX, finYP,
      shS, optOk]

theorem termCorr {c : Compiled} (Ok : Bool → DigitAtom n → Prop) (ix : BankRepairDigitInSh)
    (kx : Bool) (gxi : Option (DigitAtom n)) (gxc : Option (DigitCarryGhost c n))
    (hx : InCorr Ok ix gxi) (hkx : kx = gxc.isSome) :
    InCorr Ok (cohortTermStep ix kx).1 (ghostTermIn ix kx gxi) ∧
    (cohortTermStep ix kx).2 = (!kx && gxc.isSome) := by
  rw [← hkx]
  rcases ix with _ | _ | T | T <;> cases kx <;> (try cases T) <;>
    simp_all [InCorr, cohortTermStep, ghostTermIn, optOk]

/-! ### The correspondence on one lane, cell by cell -/

/-- Source cells `q < R` carry output correspondence; target cells `R ≤ q < 2R` carry input
correspondence and carry-live ↔ ledger present. -/
def PureCorr (R : Nat) (Ok : Bool → DigitAtom n → Prop) (s : CohortLane)
    (g : Nat → DigitLaneGhost c n) : Prop :=
  (∀ q, q < R → OutCorr Ok (s.out q) (g q).out) ∧
  (∀ q, R ≤ q → q < 2 * R → InCorr Ok (s.inp q) (g q).input ∧ s.live q = (g q).carry.isSome)

theorem pureCorrMono {R : Nat} {Ok Ok' : Bool → DigitAtom n → Prop}
    (h : ∀ T a, Ok T a → Ok' T a) {s : CohortLane} {g : Nat → DigitLaneGhost c n}
    (hc : PureCorr R Ok s g) : PureCorr R Ok' s g :=
  ⟨fun q hq => outCorrMono h _ _ (hc.1 q hq),
    fun q h1 h2 => ⟨inCorrMono h _ _ (hc.2 q h1 h2).1, (hc.2 q h1 h2).2⟩⟩

theorem pureCorrSame {R : Nat} {Ok : Bool → DigitAtom n → Prop} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} (hc : PureCorr R Ok s g)
    (ho : ∀ q, q < R → (g' q).out = (g q).out)
    (hi : ∀ q, R ≤ q → q < 2 * R → (g' q).input = (g q).input ∧ (g' q).carry = (g q).carry) :
    PureCorr R Ok s g' := by
  refine ⟨fun q hq => ?_, fun q h1 h2 => ?_⟩
  · rw [ho q hq]
    exact hc.1 q hq
  · rw [(hi q h1 h2).1, (hi q h1 h2).2]
    exact hc.2 q h1 h2

theorem pureCorrEq {R : Nat} {Ok : Bool → DigitAtom n → Prop} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} (hc : PureCorr R Ok s g)
    (hg : ∀ q, q < 2 * R → g' q = g q) : PureCorr R Ok s g' :=
  pureCorrSame hc (fun q hq => by rw [hg q (by omega)])
    (fun q _ h2 => by rw [hg q h2]; exact ⟨rfl, rfl⟩)

theorem pureCorrPipe {R : Nat} {Ok : Bool → DigitAtom n → Prop} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} (k : Nat) (hk : k + 1 < R) (stamp : DigitStamp n)
    (hc : PureCorr R Ok s g)
    (hfr : ∀ q, q ≠ k → q ≠ k + 1 → q < 2 * R → g' q = g q)
    (hrow : ((g' k).out, (g' (k + 1)).out) =
      ghostPipe stamp (decide (k = 0)) (s.out k) (s.out (k + 1)) (g k).out (g (k + 1)).out)
    (hnew : s.out k = .U → Ok (decide (k = 0)) (.sampled stamp)) :
    PureCorr R Ok (cohortEdge R s k) g' := by
  obtain ⟨ho, hi⟩ := hc
  obtain ⟨p1, p2⟩ := pipeCorr Ok stamp (decide (k = 0)) (s.out k) (s.out (k + 1)) (g k).out
    (g (k + 1)).out (ho k (by omega)) (ho (k + 1) hk) hnew
  have e1 : (g' k).out = _ := congrArg Prod.fst hrow
  have e2 : (g' (k + 1)).out = _ := congrArg Prod.snd hrow
  rw [← e1] at p1
  rw [← e2] at p2
  refine ⟨fun q hq => ?_, fun q h1 h2 => ?_⟩
  · simp only [cohortEdge, if_pos hk, cohortUpd]
    by_cases hq1 : q = k + 1
    · rw [if_pos hq1, hq1]
      exact p2
    · rw [if_neg hq1]
      by_cases hq2 : q = k
      · rw [if_pos hq2, hq2]
        exact p1
      · rw [if_neg hq2, hfr q hq2 hq1 (by omega)]
        exact ho q hq
  · simp only [cohortEdge, if_pos hk]
    rw [hfr q (by omega) (by omega) h2]
    exact hi q h1 h2

theorem pureCorrDel {R : Nat} {Ok : Bool → DigitAtom n → Prop} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} (k : Nat) (hk : k + 1 = R) (stamp : DigitStamp n)
    (hc : PureCorr R Ok s g)
    (hfr : ∀ q, q ≠ k → q ≠ k + 1 → q < 2 * R → g' q = g q)
    (hrow : ((g' k).out, (g' (k + 1)).input) =
      ghostDel stamp (s.out k) (s.inp (k + 1)) (s.live (k + 1)) (g k).out (g (k + 1)).input)
    (hcar : (g' (k + 1)).carry = (g (k + 1)).carry)
    (hnew : s.out k = .U → Ok false (.sampled stamp)) :
    PureCorr R Ok (cohortEdge R s k) g' := by
  obtain ⟨ho, hi⟩ := hc
  obtain ⟨d1, d2, d3⟩ := delCorr Ok stamp (s.out k) (s.inp (k + 1)) (s.live (k + 1)) (g k).out
    (g (k + 1)).input (ho k (by omega)) (hi (k + 1) (by omega) (by omega)).1 hnew
  have e1 : (g' k).out = _ := congrArg Prod.fst hrow
  have e2 : (g' (k + 1)).input = _ := congrArg Prod.snd hrow
  rw [← e1] at d1
  rw [← e2] at d2
  have c1 : ¬ k + 1 < R := by omega
  refine ⟨fun q hq => ?_, fun q h1 h2 => ?_⟩
  · simp only [cohortEdge, if_neg c1, if_pos hk, cohortUpd]
    by_cases hq2 : q = k
    · rw [if_pos hq2, hq2]
      exact d1
    · rw [if_neg hq2, hfr q hq2 (by omega) (by omega)]
      exact ho q hq
  · simp only [cohortEdge, if_neg c1, if_pos hk, cohortUpd]
    by_cases hq1 : q = k + 1
    · rw [if_pos hq1, if_pos hq1, hq1, d3, hcar]
      exact ⟨d2, (hi (k + 1) (by omega) (by omega)).2⟩
    · rw [if_neg hq1, if_neg hq1, hfr q (by omega) hq1 h2]
      exact hi q h1 h2

theorem pureCorrFin {R : Nat} {Ok : Bool → DigitAtom n → Prop} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} (k : Nat) (hk1 : R ≤ k) (hk2 : k + 1 < 2 * R)
    (hc : PureCorr R Ok s g)
    (hfr : ∀ q, q ≠ k → q ≠ k + 1 → q < 2 * R → g' q = g q)
    (hrx : (g' k).input = finInX (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
      (s.live (k + 1)) (g k).input)
    (hry : (g' (k + 1)).input = finInY (s.inp k) (s.live k) (s.inp (k + 1)) (s.live (k + 1))
      (g k).input (g (k + 1)).input)
    (hcx : (g' k).carry.isSome =
      (!s.live k && ((decide (k = R) && shS (s.inp k)) || (g k).carry.isSome)))
    (hcy : (g' (k + 1)).carry.isSome =
      ((s.live k && !s.live (k + 1) && shS (s.inp (k + 1))) || (g (k + 1)).carry.isSome)) :
    PureCorr R Ok (cohortEdge R s k) g' := by
  obtain ⟨ho, hi⟩ := hc
  obtain ⟨f1, f2, f3, f4⟩ := finCorr Ok (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
    (s.live (k + 1)) (g k).input (g (k + 1)).input (g k).carry (g (k + 1)).carry
    (hi k hk1 (by omega)).1 (hi (k + 1) (by omega) hk2).1 (hi k hk1 (by omega)).2
    (hi (k + 1) (by omega) hk2).2
  rw [← hrx] at f1
  rw [← hry] at f3
  rw [← hcx] at f2
  rw [← hcy] at f4
  have c1 : ¬ k + 1 < R := by omega
  have c2 : ¬ k + 1 = R := by omega
  refine ⟨fun q hq => ?_, fun q h1 h2 => ?_⟩
  · simp only [cohortEdge, if_neg c1, if_neg c2, if_pos hk2]
    rw [hfr q (by omega) (by omega) (by omega)]
    exact ho q hq
  · simp only [cohortEdge, if_neg c1, if_neg c2, if_pos hk2, cohortUpd]
    by_cases hq1 : q = k + 1
    · rw [if_pos hq1, if_pos hq1, hq1]
      exact ⟨f3, f4⟩
    · rw [if_neg hq1, if_neg hq1]
      by_cases hq2 : q = k
      · rw [if_pos hq2, if_pos hq2, hq2]
        exact ⟨f1, f2⟩
      · rw [if_neg hq2, if_neg hq2, hfr q hq2 hq1 h2]
        exact hi q h1 h2

theorem pureCorrTerm {R : Nat} {Ok : Bool → DigitAtom n → Prop} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} (k : Nat) (hk : k + 1 = 2 * R)
    (hc : PureCorr R Ok s g)
    (hfr : ∀ q, q ≠ k → q < 2 * R → g' q = g q)
    (hrow : (g' k).input = ghostTermIn (s.inp k) (s.live k) (g k).input)
    (hcar : (g' k).carry.isSome = (!s.live k && (g k).carry.isSome)) :
    PureCorr R Ok (cohortEdge R s k) g' := by
  obtain ⟨ho, hi⟩ := hc
  obtain ⟨t1, t2⟩ := termCorr Ok (s.inp k) (s.live k) (g k).input (g k).carry
    (hi k (by omega) (by omega)).1 (hi k (by omega) (by omega)).2
  rw [← hrow] at t1
  rw [← hcar] at t2
  have c1 : ¬ k + 1 < R := by omega
  have c2 : ¬ k + 1 = R := by omega
  have c3 : ¬ k + 1 < 2 * R := by omega
  refine ⟨fun q hq => ?_, fun q h1 h2 => ?_⟩
  · simp only [cohortEdge, if_neg c1, if_neg c2, if_neg c3, if_pos hk]
    rw [hfr q (by omega) (by omega)]
    exact ho q hq
  · simp only [cohortEdge, if_neg c1, if_neg c2, if_neg c3, if_pos hk, cohortUpd]
    by_cases hq2 : q = k
    · rw [if_pos hq2, if_pos hq2, hq2]
      exact ⟨t1, t2⟩
    · rw [if_neg hq2, if_neg hq2, hfr q hq2 h2]
      exact hi q h1 h2

end Cells

/-! ### The F1 rows on the record fields -/

section RowsD

variable {c : Compiled} {n : Nat} (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
  (gx gy : DigitGhost c n)

theorem rowPipeD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmy : laneMarkerY lane X Y = false) :
    ((laneGhost lane (digitService t e d X Y gx gy).x).out,
      (laneGhost lane (digitService t e d X Y gx gy).y).out) =
    ghostPipe (DigitStamp.mk t e lane) (laneMarkerX lane X Y)
      (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane X.top))
      (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane Y.top))
      (laneGhost lane gx).out (laneGhost lane gy).out := by
  have h := replayPipe lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmy)
  rw [laneViewMarker, laneViewOutSh, laneViewOutSh] at h
  rw [serviceLaneX, serviceLaneY, serviceLane]
  exact h

theorem rowDelD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmx : laneMarkerX lane X Y = false) (hmy : laneMarkerY lane X Y = true) :
    ((laneGhost lane (digitService t e d X Y gx gy).x).out,
      (laneGhost lane (digitService t e d X Y gx gy).y).input) =
      ghostDel (DigitStamp.mk t e lane) (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane X.top))
        (bankRepairDigitInShOf (bankRepairDigitLaneIn lane Y.top))
        (bankRepairDigitLaneLive lane Y.top) (laneGhost lane gx).out (laneGhost lane gy).input ∧
    (laneGhost lane (digitService t e d X Y gx gy).y).carry = (laneGhost lane gy).carry := by
  obtain ⟨h1, h2, -⟩ := replayDel lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmx) (by rw [laneViewMarker]; exact hmy)
  rw [laneViewOutSh, laneViewInSh, laneViewLive] at h1
  rw [serviceLaneX, serviceLaneY, serviceLane]
  exact ⟨h1, h2⟩

theorem rowFinD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmy : laneMarkerY lane X Y = false) :
    ((laneGhost lane (digitService t e d X Y gx gy).x).input,
      (laneGhost lane (digitService t e d X Y gx gy).y).input) =
      ghostFinIn (laneMarkerX lane X Y) (bankRepairDigitInShOf (bankRepairDigitLaneIn lane X.top))
        (bankRepairDigitLaneLive lane X.top)
        (bankRepairDigitInShOf (bankRepairDigitLaneIn lane Y.top))
        (bankRepairDigitLaneLive lane Y.top) (laneGhost lane gx).input (laneGhost lane gy).input ∧
    (laneGhost lane (digitService t e d X Y gx gy).x).carry.isSome =
      (!bankRepairDigitLaneLive lane X.top && ((laneMarkerX lane X Y &&
        shS (bankRepairDigitInShOf (bankRepairDigitLaneIn lane X.top))) ||
        (laneGhost lane gx).carry.isSome)) ∧
    (laneGhost lane (digitService t e d X Y gx gy).y).carry.isSome =
      ((bankRepairDigitLaneLive lane X.top && !bankRepairDigitLaneLive lane Y.top &&
        shS (bankRepairDigitInShOf (bankRepairDigitLaneIn lane Y.top))) ||
        (laneGhost lane gy).carry.isSome) := by
  have h := replayFin lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmy)
  rw [laneViewMarker, laneViewInSh, laneViewInSh, laneViewLive, laneViewLive] at h
  rw [serviceLaneX, serviceLaneY, serviceLane]
  exact h

theorem rowTermD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmx : laneMarkerX lane X Y = false) (hmy : laneMarkerY lane X Y = true) :
    (laneGhost lane (digitService t e d X Y gx gy).x).input =
      ghostTermIn (bankRepairDigitInShOf (bankRepairDigitLaneIn lane X.top))
        (bankRepairDigitLaneLive lane X.top) (laneGhost lane gx).input ∧
    (laneGhost lane (digitService t e d X Y gx gy).x).carry.isSome =
      (!bankRepairDigitLaneLive lane X.top && (laneGhost lane gx).carry.isSome) := by
  obtain ⟨h1, h2, -⟩ := replayTerm lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmx) (by rw [laneViewMarker]; exact hmy)
  rw [laneViewInSh, laneViewLive] at h1
  rw [laneViewLive] at h2
  rw [serviceLaneX, serviceLane]
  exact ⟨h1, h2⟩

theorem rowEntryD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmy : laneMarkerY lane X Y = true) :
    (laneGhost lane (digitService t e d X Y gx gy).y).out = (laneGhost lane gy).out := by
  rw [serviceLaneY, serviceLane]
  exact replayEntry lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmy)

end RowsD

/-! ### The correspondence on the ring -/

section Ring

variable {c : Compiled} {n : Nat}

/-- Provenance of a tracked atom: a recorded sample of this lane, read at a source cell of the
pair, with tail bit `T`. -/
def SampleOk (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) (T : Bool) (a : DigitAtom n) : Prop :=
  ∃ s : DigitSample c n, a = .sampled s.id ∧ DigitRecordedSample A s ∧ s.tail = T ∧
    s.id.lane = lane ∧ ∃ q, q < R ∧ s.id.site = digitSite ring root (src + q)

/-- Provenance: either a base atom (present when the tracking began) or a recorded sample. -/
def GhostOk (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (A : DigitAudit c n) (T : Bool) (a : DigitAtom n) :
    Prop :=
  Base T a ∨ SampleOk ring root lane src R A T a

/-- The lane ghosts at the cells `src + q`. -/
def laneCells (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src : Nat)
    (G : Fin n → DigitGhost c n) : Nat → DigitLaneGhost c n :=
  fun q => laneGhost lane (G (digitSite ring root (src + q)))

/-- **The BANK ghost correspondence** on the pair `[src, src + R)`, `[src + R, src + 2R)` of one
lane: every tracked cell of the masked lane corresponds to the current audit ghost at its site,
and every tracked atom is a base atom or a recorded sample of this lane read at a source cell
with the cell's tail bit. -/
def GhostCorr (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  PureCorr R (GhostOk ring root lane src R Base A) (cohortProj ring root lane src R S)
    (laneCells ring root lane src A.current)

theorem recordedSampleStep (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (s : DigitSample c n) (h : DigitRecordedSample A s) :
    DigitRecordedSample (digitAuditStep ring S A e) s := by
  obtain ⟨f, hf, h1, h2, h3, h4⟩ := h
  exact ⟨f, auditFrameMemStep ring S A e f hf, h1, h2, h3, h4⟩

theorem ghostOkStep (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) :
    ∀ T a, GhostOk ring root lane src R Base A T a →
      GhostOk ring root lane src R Base (digitAuditStep ring S A e) T a := by
  intro T a h
  rcases h with h | ⟨s, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, h1, recordedSampleStep ring S A e s h2, h3⟩

/-- The service receipt of one audit letter. -/
def svcAt (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) :
    DigitService c n :=
  digitService (A.clock + 1) e (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
    (A.current e) (A.current (ring.rightNeighbor e))

theorem curX (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) :
    (digitAuditStep ring S A e).current e = (svcAt ring S A e).x := by
  simp [digitAuditStep, digitGhostStep, svcAt]

theorem curY (ring : DirectedRing n) (hn : 2 ≤ n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) :
    (digitAuditStep ring S A e).current (ring.rightNeighbor e) = (svcAt ring S A e).y := by
  simp [digitAuditStep, digitGhostStep, svcAt, bankRepairDigitRightNe ring hn e]

theorem curFar (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n) (e i : Fin n)
    (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) :
    (digitAuditStep ring S A e).current i = A.current i := by
  simp [digitAuditStep, digitGhostStep, h1, h2]

/-- A freshly read unread slot is a recorded sample of the new frame. -/
theorem freshSample (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (lane : DigitLane) (hlx : (S e).word.native.l = false)
    (hly : (S (ring.rightNeighbor e)).word.native.l = false)
    (hU : bankRepairDigitOutShOf (bankRepairDigitLaneOut lane (S e).top) = .U) :
    ∃ s : DigitSample c n, s.id = DigitStamp.mk (A.clock + 1) e lane ∧
      s.tail = laneMarkerX lane (S e) (S (ring.rightNeighbor e)) ∧
      DigitRecordedSample (digitAuditStep ring S A e) s := by
  obtain ⟨s, h1, h2, h3, h4, -⟩ := recordUnreadReadD lane (A.clock + 1) e (ring.rightNeighbor e)
    (S e) (S (ring.rightNeighbor e)) (A.current e) (A.current (ring.rightNeighbor e)) hlx hly hU
  refine ⟨s, h2, h3, DigitFrame.mk (A.clock + 1) e S A.current (svcAt ring S A e),
    List.mem_cons.mpr (Or.inl rfl), ?_, ?_, ?_, h4⟩
  · rw [h2]
  · rw [h2]
  · rw [h2]
    exact h1

theorem projOut (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (q : Nat) (hq : q < R) :
    (cohortProj ring root lane src R S).out q =
      bankRepairDigitOutShOf (bankRepairDigitLaneOut lane (S (digitSite ring root (src + q))).top) := by
  show (if q < R then bankRepairDigitOutL ring root lane S src q else .E) = _
  rw [if_pos hq]
  rfl

theorem projIn (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) :
    (cohortProj ring root lane src R S).inp q =
      bankRepairDigitInShOf (bankRepairDigitLaneIn lane (S (digitSite ring root (src + q))).top) := by
  show (if R ≤ q ∧ q < 2 * R then bankRepairDigitInL ring root lane S src q else .E) = _
  rw [if_pos ⟨h1, h2⟩]
  rfl

theorem projLive (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) :
    (cohortProj ring root lane src R S).live q =
      bankRepairDigitLaneLive lane (S (digitSite ring root (src + q))).top := by
  show (if R ≤ q ∧ q < 2 * R then bankRepairDigitLvL ring root lane S src q else false) = _
  rw [if_pos ⟨h1, h2⟩]
  rfl

/-- **Every letter preserves the correspondence** (projected ring, layout hypotheses of
`cohortProjStep`). -/
theorem ghostCorrStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (Base : Bool → DigitAtom n → Prop) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    (h : GhostCorr ring root lane src R Base S A) :
    GhostCorr ring root lane src R Base (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)) := by
  have hm : PureCorr R (GhostOk ring root lane src R Base
      (digitAuditStep ring S A (digitSite ring root j))) (cohortProj ring root lane src R S)
      (laneCells ring root lane src A.current) :=
    pureCorrMono (ghostOkStep ring root lane src R Base S A (digitSite ring root j)) h
  unfold GhostCorr
  rw [cohortProjStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane j hj hbX hbY]
  unfold cohortEdgeOf
  rw [cohortIdxSite ring root j hj]
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · rw [if_pos hin]
    obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    rw [Nat.add_sub_cancel_left]
    show PureCorr R _ (cohortEdge R _ k) _
    have hfr : ∀ q, q ≠ k → q ≠ k + 1 → q < 2 * R →
        laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + k))).current q =
        laneCells ring root lane src A.current q := by
      intro q hq1 hq2 hq
      unfold laneCells
      rw [curFar]
      · intro he
        exact hq1 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        exact hq2 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
    have hx : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current k =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).x := by
      unfold laneCells
      rw [curX]
    have hy : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1) =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).y := by
      unfold laneCells
      rw [show digitSite ring root (src + (k + 1)) =
        ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring hn]
    have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
    by_cases h1 : k + 1 < R
    · -- Pipe
      have hbx : (S (digitSite ring root (src + k))).word.beta = decide (k = 0) := by
        by_cases hk0 : k = 0
        · rw [decide_eq_true hk0, hk0]
          exact hb0
        · rw [decide_eq_false hk0]
          exact hbF k (by omega) (by omega) (by omega)
      have hmX : laneMarkerX lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = decide (k = 0) := by
        rw [laneMarkerXBeta lane _ _ hbX]
        exact hbx
      have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = false := by
        rw [laneMarkerYBeta lane _ _ hbY]
        exact hbF (k + 1) (by omega) (by omega) (by omega)
      apply pureCorrPipe k h1 (DigitStamp.mk (A.clock + 1) (digitSite ring root (src + k)) lane)
        hm hfr
      · rw [hx, hy, projOut ring root lane src R S k (by omega),
          projOut ring root lane src R S (k + 1) h1, ← hmX]
        exact rowPipeD lane (A.clock + 1) (digitSite ring root (src + k))
          (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly hmy
      · intro hU
        rw [projOut ring root lane src R S k (by omega)] at hU
        obtain ⟨smp, hid, htl, hrec⟩ :=
          freshSample ring S A (digitSite ring root (src + k)) lane hlx hly hU
        refine Or.inr ⟨smp, by rw [hid], hrec, ?_, by rw [hid], k, by omega, by rw [hid]⟩
        rw [htl]
        exact hmX
    · by_cases h2 : k + 1 = R
      · -- Del
        have hmx : laneMarkerX lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))) = false := by
          rw [laneMarkerXBeta lane _ _ hbX]
          exact hbF k (by omega) (by omega) (by omega)
        have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))) = true := by
          rw [laneMarkerYBeta lane _ _ hbY, show src + k + 1 = src + R by omega]
          exact hbR
        have hrow := rowDelD lane (A.clock + 1) (digitSite ring root (src + k))
          (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly hmx hmy
        apply pureCorrDel k h2 (DigitStamp.mk (A.clock + 1) (digitSite ring root (src + k)) lane)
          hm hfr
        · rw [hx, hy, projOut ring root lane src R S k (by omega),
            projIn ring root lane src R S (k + 1) (by omega) (by omega),
            projLive ring root lane src R S (k + 1) (by omega) (by omega)]
          exact hrow.1
        · rw [hy]
          exact hrow.2
        · intro hU
          rw [projOut ring root lane src R S k (by omega)] at hU
          obtain ⟨smp, hid, htl, hrec⟩ :=
            freshSample ring S A (digitSite ring root (src + k)) lane hlx hly hU
          refine Or.inr ⟨smp, by rw [hid], hrec, ?_, by rw [hid], k, by omega, by rw [hid]⟩
          rw [htl]
          exact hmx
      · by_cases h3 : k + 1 < 2 * R
        · -- Fin
          have hbx : (S (digitSite ring root (src + k))).word.beta = decide (k = R) := by
            by_cases hkR : k = R
            · rw [decide_eq_true hkR, hkR]
              exact hbR
            · rw [decide_eq_false hkR]
              exact hbF k (by omega) (by omega) hkR
          have hmX : laneMarkerX lane (S (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k + 1))) = decide (k = R) := by
            rw [laneMarkerXBeta lane _ _ hbX]
            exact hbx
          have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k + 1))) = false := by
            rw [laneMarkerYBeta lane _ _ hbY]
            exact hbF (k + 1) (by omega) (by omega) (by omega)
          obtain ⟨hI, hcx, hcy⟩ := rowFinD lane (A.clock + 1) (digitSite ring root (src + k))
            (ring.rightNeighbor (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
            (A.current (digitSite ring root (src + k)))
            (A.current (digitSite ring root (src + k + 1))) hlx hly hmy
          apply pureCorrFin k (by omega) h3 hm hfr
          · rw [hx, projIn ring root lane src R S k (by omega) (by omega),
              projLive ring root lane src R S k (by omega) (by omega),
              projIn ring root lane src R S (k + 1) (by omega) (by omega),
              projLive ring root lane src R S (k + 1) (by omega) (by omega), ← hmX]
            exact congrArg Prod.fst hI
          · rw [hy, projIn ring root lane src R S k (by omega) (by omega),
              projLive ring root lane src R S k (by omega) (by omega),
              projIn ring root lane src R S (k + 1) (by omega) (by omega),
              projLive ring root lane src R S (k + 1) (by omega) (by omega)]
            exact congrArg Prod.snd hI
          · rw [hx, projIn ring root lane src R S k (by omega) (by omega),
              projLive ring root lane src R S k (by omega) (by omega), ← hmX]
            exact hcx
          · rw [hy, projIn ring root lane src R S (k + 1) (by omega) (by omega),
              projLive ring root lane src R S k (by omega) (by omega),
              projLive ring root lane src R S (k + 1) (by omega) (by omega)]
            exact hcy
        · -- Term
          have h4 : k + 1 = 2 * R := by omega
          have hmx : laneMarkerX lane (S (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k + 1))) = false := by
            rw [laneMarkerXBeta lane _ _ hbX]
            exact hbF k (by omega) (by omega) (by omega)
          have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k + 1))) = true := by
            rw [laneMarkerYBeta lane _ _ hbY, show src + k + 1 = src + 2 * R by omega]
            exact hb2R
          obtain ⟨t1, t2⟩ := rowTermD lane (A.clock + 1) (digitSite ring root (src + k))
            (ring.rightNeighbor (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
            (A.current (digitSite ring root (src + k)))
            (A.current (digitSite ring root (src + k + 1))) hlx hly hmx hmy
          apply pureCorrTerm k h4 hm (fun q hq1 hq => hfr q hq1 (by omega) hq)
          · rw [hx, projIn ring root lane src R S k (by omega) (by omega),
              projLive ring root lane src R S k (by omega) (by omega)]
            exact t1
          · rw [hx, projLive ring root lane src R S k (by omega) (by omega)]
            exact t2
  · rw [if_neg hin]
    show PureCorr R _ (cohortProj ring root lane src R S) _
    have farNe : ∀ q, q < 2 * R → src + q ≠ j → src + q ≠ j + 1 →
        laneCells ring root lane src (digitAuditStep ring S A (digitSite ring root j)).current q =
        laneCells ring root lane src A.current q := by
      intro q hq n1 n2
      unfold laneCells
      rw [curFar]
      · intro he
        exact n1 (bankRepairDigitSiteInj ring root (by omega) hj he)
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        by_cases hjn : j + 1 < n
        · exact n2 (bankRepairDigitSiteInj ring root (by omega) hjn he)
        · rw [show j + 1 = n by omega, bankRepairDigitSiteN] at he
          have := bankRepairDigitSiteInj ring root (k := src + q) (m := 0) (by omega) (by omega) he
          omega
    by_cases h1 : j + 1 = src
    · -- Entry
      have hlx := bankRepairDigitSiteNonroot ring root S hroot j (by omega) (by omega)
      have hly := bankRepairDigitSiteNonroot ring root S hroot (j + 1) (by omega) (by omega)
      have hmy : laneMarkerY lane (S (digitSite ring root j))
          (S (digitSite ring root (j + 1))) = true := by
        rw [laneMarkerYBeta lane _ _ hbY, h1]
        exact hb0
      apply pureCorrSame hm
      · intro q hq
        by_cases hq0 : q = 0
        · rw [hq0]
          unfold laneCells
          rw [show digitSite ring root (src + 0) = ring.rightNeighbor (digitSite ring root j) by
            rw [← h1]; rfl, curY ring hn]
          exact rowEntryD lane (A.clock + 1) (digitSite ring root j)
            (ring.rightNeighbor (digitSite ring root j)) (S (digitSite ring root j))
            (S (digitSite ring root (j + 1))) (A.current (digitSite ring root j))
            (A.current (digitSite ring root (j + 1))) hlx hly hmy
        · rw [farNe q (by omega) (by omega) (by omega)]
      · intro q hq1 hq2
        rw [farNe q hq2 (by omega) (by omega)]
        exact ⟨rfl, rfl⟩
    · -- Far
      exact pureCorrEq hm (fun q hq => farNe q hq (by omega) (by omega))

end Ring

/-! ### Along the coupled BANK x audit run -/

section Run

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

include hn hR hsrc hend in
/-- One coupled letter keeps the layout and the correspondence. -/
theorem ghostCorrBankStep
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1)
    (hc : GhostCorr ring root lane src R Base (piD z.1.val.1) z.2) (e : Fin n) :
    CohortLayout ring hbank root src R (bankRepairDigitBoundaryAuditNext ring hbank z e).1 ∧
    GhostCorr ring root lane src R Base
      (piD (bankRepairDigitBoundaryAuditNext ring hbank z e).1.val.1)
      (bankRepairDigitBoundaryAuditNext ring hbank z e).2 := by
  refine ⟨(cohortBankStep ring hn hbank root lane src R hR hsrc hend z.1 hz e).1, ?_⟩
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨heq, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  show GhostCorr ring root lane src R Base (piD (bankRepairNext ring hbank z.1 e).val.1)
    (digitAuditStep ring (piD z.1.val.1) z.2 e)
  rw [heq]
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  exact ghostCorrStep ring (by omega) root (piD z.1.val.1) R src hR hsrc hend hroot hb0 hbR hb2R
    hbF lane Base z.2 j hj hbX hbY hc

include hn hR hsrc hend in
/-- **Run level**: along every coupled word, from any layout state where the correspondence
holds, the layout and the correspondence persist. -/
theorem ghostCorrRun (word : List (Fin n)) :
    ∀ z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      CohortLayout ring hbank root src R z.1 →
      GhostCorr ring root lane src R Base (piD z.1.val.1) z.2 →
      CohortLayout ring hbank root src R
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).1 ∧
      GhostCorr ring root lane src R Base
        (piD (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).1.val.1)
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).2 := by
  induction word with
  | nil => intro z h1 h2; exact ⟨h1, h2⟩
  | cons e rest ih =>
      intro z h1 h2
      obtain ⟨a, b⟩ := ghostCorrBankStep ring hn hbank root lane src R hR hsrc hend Base z h1 h2 e
      exact ih _ a b

include hn hR hsrc hend in
/-- **From the cycle entry**: at a coupled layout state with the correspondence whose masked
lane is at the T24 entry (`CohortSettling R 0` with the younger source cells), the first cycle
starts (`cohortCycEntry`) and the correspondence holds along every continuation. -/
theorem ghostCorrCycEntry
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1)
    (hc : GhostCorr ring root lane src R Base (piD z.1.val.1) z.2)
    (hset : CohortSettling R 0 (cohortProj ring root lane src R (piD z.1.val.1)))
    (hyng : ∀ q, q < R →
      cohortTok R (cohortProj ring root lane src R (piD z.1.val.1)) q = .other ∨
      cohortTok R (cohortProj ring root lane src R (piD z.1.val.1)) q = .pkt (decide (q = 0))) :
    CohortCycStart R 0 (cohortProj ring root lane src R (piD z.1.val.1)) ((fun _ => 0), 0) ∧
    ∀ word : List (Fin n),
      CohortLayout ring hbank root src R
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).1 ∧
      GhostCorr ring root lane src R Base
        (piD (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).1.val.1)
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).2 :=
  ⟨cohortCycEntry hR hset hyng,
    fun word => ghostCorrRun ring hn hbank root lane src R hR hsrc hend Base word z hz hc⟩

end Run

/-! ### The correspondence at the audit start -/

section Initial

variable {c : Compiled} {n : Nat}

/-- Base atoms at the audit start: the inherited atoms of this lane. -/
def InheritedOk (lane : DigitLane) (_T : Bool) (a : DigitAtom n) : Prop :=
  ∃ site slot, a = DigitAtom.inherited lane site slot

theorem laneGhostInitial (lane : DigitLane) (S : Fin n → ProjD c) (i : Fin n) :
    laneGhost lane (digitGhostInitial S i) =
      DigitLaneGhost.initial lane i (digitLaneView lane (S i) (S i).word.beta) := by
  cases lane <;> rfl

theorem initialOut (lane : DigitLane) (Ok : Bool → DigitAtom n → Prop)
    (hOk : ∀ T i slot, Ok T (DigitAtom.inherited lane i slot)) (i : Fin n) (v : DigitLaneView c) :
    OutCorr Ok (bankRepairDigitOutShOf v.out) (DigitLaneGhost.initial lane i v).out := by
  cases h : v.out <;>
    simp [DigitLaneGhost.initial, h, bankRepairDigitOutShOf, OutCorr, optOk,
      DigitOutGhost.obligation, DigitOutGhost.atom, hOk]

theorem initialIn (lane : DigitLane) (Ok : Bool → DigitAtom n → Prop)
    (hOk : ∀ T i slot, Ok T (DigitAtom.inherited lane i slot)) (i : Fin n) (v : DigitLaneView c) :
    InCorr Ok (bankRepairDigitInShOf v.input) (DigitLaneGhost.initial lane i v).input := by
  cases h : v.input <;>
    simp [DigitLaneGhost.initial, h, bankRepairDigitInShOf, InCorr, optOk, hOk]

theorem initialLive (lane : DigitLane) (i : Fin n) (v : DigitLaneView c) :
    v.carryLive = (DigitLaneGhost.initial (c := c) lane i v).carry.isSome := by
  cases h : v.carryLive <;> simp [DigitLaneGhost.initial, h]

/-- At the audit start the correspondence holds with the inherited atoms as base. -/
theorem ghostCorrInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) :
    GhostCorr ring root lane src R (InheritedOk lane) S (digitAuditInitial S) := by
  have hOk : ∀ T i slot, GhostOk ring root lane src R (InheritedOk lane) (digitAuditInitial S) T
      (DigitAtom.inherited lane i slot) := fun _ i slot => Or.inl ⟨i, slot, rfl⟩
  refine ⟨fun q hq => ?_, fun q h1 h2 => ?_⟩
  · rw [projOut ring root lane src R S q hq]
    show OutCorr _ _ (laneGhost lane (digitGhostInitial S (digitSite ring root (src + q)))).out
    rw [laneGhostInitial, ← laneViewOut lane (S (digitSite ring root (src + q)))
      (S (digitSite ring root (src + q))).word.beta]
    exact initialOut lane _ hOk _ _
  · rw [projIn ring root lane src R S q h1 h2, projLive ring root lane src R S q h1 h2]
    show InCorr _ _ (laneGhost lane (digitGhostInitial S (digitSite ring root (src + q)))).input ∧
      _ = (laneGhost lane (digitGhostInitial S (digitSite ring root (src + q)))).carry.isSome
    rw [laneGhostInitial, ← laneViewIn lane (S (digitSite ring root (src + q)))
      (S (digitSite ring root (src + q))).word.beta, ← laneViewLive lane
      (S (digitSite ring root (src + q))) (S (digitSite ring root (src + q))).word.beta]
    exact ⟨initialIn lane _ hOk _ _, initialLive lane _ _⟩

/-- From the audit start in the layout class, the correspondence (inherited base) holds along
every coupled word. -/
theorem ghostCorrFromStart {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (z : BankReferenceState ring hbank) (hz : CohortLayout ring hbank root src R z)
    (word : List (Fin n)) :
    let w := word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (z, digitAuditInitial (piD z.val.1))
    CohortLayout ring hbank root src R w.1 ∧
      GhostCorr ring root lane src R (InheritedOk lane) (piD w.1.val.1) w.2 :=
  ghostCorrRun ring hn hbank root lane src R hR hsrc hend (InheritedOk lane) word
    (z, digitAuditInitial (piD z.val.1)) hz (ghostCorrInitial ring root lane src R _)

end Initial

/-! ### F4: finite minimum -/

section Min

theorem natMinWitness {α : Type} (P : α → Prop) (f : α → Nat) :
    ∀ N x, P x → f x ≤ N → ∃ y, P y ∧ ∀ z, P z → f y ≤ f z := by
  intro N
  induction N with
  | zero =>
      intro x hx hle
      exact ⟨x, hx, fun z _ => by omega⟩
  | succ N ih =>
      intro x hx hle
      rcases Classical.em (∃ z, P z ∧ f z ≤ N) with ⟨z, hz, hzN⟩ | hno
      · exact ih z hz hzN
      · refine ⟨x, hx, fun z hz => ?_⟩
        rcases Nat.lt_or_ge N (f z) with hl | hl
        · omega
        · exact absurd ⟨z, hz, hl⟩ hno

variable {c : Compiled} {n : Nat}

/-- **F4**: any completion after `after` yields a next completion (`DigitNextCompletion`). -/
theorem nextCompletionExists (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (after : Nat) (t : DigitTerminal c n)
    (ht : DigitCompletion ring A root source target lane 0 t) (ha : after < t.time) :
    ∃ t', DigitNextCompletion ring A root source target lane after t' := by
  obtain ⟨y, ⟨hy1, hy2⟩, hmin⟩ := natMinWitness
    (fun u : DigitTerminal c n => DigitCompletion ring A root source target lane 0 u ∧
      after < u.time) (fun u => u.time) t.time t ⟨ht, ha⟩ (Nat.le_refl _)
  exact ⟨y, hy1, hy2, fun other ho hao => hmin other ⟨ho, hao⟩⟩

/-- The same finite minimum for `DigitFirstStrictCompletion`. -/
theorem firstStrictCompletionExists (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (cut : Nat) (t : DigitTerminal c n)
    (ht : DigitCompletion ring A root source target lane cut t) :
    ∃ t', DigitFirstStrictCompletion ring A root source target lane cut t' := by
  obtain ⟨y, hy, hmin⟩ := natMinWitness
    (fun u : DigitTerminal c n => DigitCompletion ring A root source target lane cut u)
    (fun u => u.time) t.time t ht (Nat.le_refl _)
  exact ⟨y, hy, hmin⟩

end Min

end L3.Correspondence

#print axioms L3.Correspondence.ghostCorrStep
#print axioms L3.Correspondence.ghostCorrRun
#print axioms L3.Correspondence.ghostCorrFromStart
#print axioms L3.Correspondence.ghostCorrCycEntry
#print axioms L3.Correspondence.natMinWitness
#print axioms L3.Correspondence.nextCompletionExists
#print axioms L3.Correspondence.firstStrictCompletionExists

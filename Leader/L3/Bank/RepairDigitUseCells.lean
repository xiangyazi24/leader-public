import Leader.L3.Bank.RepairDigitUseRows

/-!
# T33, cells: atom identity and clean ledgers on the target cells

Abstract (lane-level) bookkeeping on the target cells `R ≤ q < 2R` of the pair.

* `tgtRegion`: in a cycle every target cell is a chosen slot position, an empty cell below the
  old region, or an old cell (pending or settled in settlement; the live carry cell, or settled
  `false` above it, in the carry phase). Hence no tombstone `X` is ever off a live cell
  (`tgtNoX`): the Fin row in which an `X` input replaces a settled right cell never fires on the
  pair, a pending packet ahead of an empty cell is a chosen slot (`tgtPktSlot`), and a live cell
  is the carry cell with settled `false` operands above it and every chosen slot below it
  (`tgtLive`).
* `tgtMove`: one letter moves a target atom only by a hop of a pending packet into an empty cell
  or by the delimiter acceptance.
* **Item 1** (`curIdStep`, `oldIdStep`, `oldOfCur`): a crossed chosen slot's target cell holds
  exactly the operand of its crossing; a target cell that is not a chosen slot position holds
  nothing or the operand of the last closed window's crossing for that cell; at a closing letter
  the first clause becomes the second.
* **Items 2 and 3** (`ledgerStep`): every ledger on a target cell `q` is clean, has `q + 1 - R`
  uses, and its `m`-th use reads the operand of `chiOld (R - 1 - m)` after `t0`.
-/

namespace L3.UseCells

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.CohortEntry
open L3.CohortTail
open L3.PacketClass
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortWindow
open L3.SitePin

/-! ### Token shapes -/

section Toks

theorem tokInPkt {i : BankRepairDigitInSh} {l T : Bool} (h : cohortTokIn i l = .pkt T) :
    i = .P T ∧ l = false := by
  cases l <;> cases i <;> simp_all [cohortTokIn]

theorem tokInSettled {i : BankRepairDigitInSh} {l T : Bool} (h : cohortTokIn i l = .settled T) :
    i = .S T ∧ l = false := by
  cases l <;> cases i <;> simp_all [cohortTokIn]

theorem tokInLive (i : BankRepairDigitInSh) : cohortTokIn i true = .other := by
  simp [cohortTokIn]

theorem tokInX : cohortTokIn .X false = .other := by
  simp [cohortTokIn]

theorem tokInP (T : Bool) : cohortTokIn (.P T) false = .pkt T := by
  simp [cohortTokIn]

theorem tokInE : cohortTokIn .E false = .empty := by
  simp [cohortTokIn]

theorem optSome {n : Nat} {P : DigitAtom n → Prop} {o : Option (DigitAtom n)} (h : optOk P o) :
    ∃ b, o = some b := by
  cases o with
  | none => exact h.elim
  | some b => exact ⟨b, rfl⟩

theorem singletonGet {α : Type} (u u' : α) (m : Nat) (h : [u][m]? = some u') :
    m = 0 ∧ u = u' := by
  cases m with
  | zero =>
    simp at h
    exact ⟨rfl, h⟩
  | succ m => simp at h

end Toks

/-! ### Target cells in a cycle -/

section Region

variable {R : Nat} {s : CohortLane}

/-- **The target region of a cycle**: a chosen slot position, an empty cell below the old region,
or an old cell. -/
theorem tgtRegion {j o : Nat} {g : (Nat → Nat) × Nat} (h : CohortCycIn R j s g o)
    (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) :
    (∃ i, i < R ∧ cohortPos R g.1 i = q) ∨
    (q < cohortBottom R o ∧ cohortTok R s q = .empty) ∨
    (cohortBottom R o ≤ q ∧ o ≤ R ∧
      ((∃ T, cohortTok R s q = .pkt T) ∨ ∃ T, cohortTok R s q = .settled T)) ∨
    (R < o ∧ o ≤ 2 * R ∧ q = o - 1 ∧ s.live q = true) ∨
    (R < o ∧ o ≤ 2 * R ∧ o - 1 < q ∧ cohortTok R s q = .settled false) := by
  obtain ⟨-, ⟨hold, hch⟩, -, -⟩ := h
  by_cases hb : cohortBottom R o ≤ q
  · by_cases ho1 : o ≤ R
    · rw [cohortOldSettle ho1] at hold
      have h3 := hold.1 (2 * R - 1 - q) (by omega)
      rw [show 2 * R - 1 - (2 * R - 1 - q) = q by omega] at h3
      right; right; left
      refine ⟨hb, ho1, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inl ⟨_, h3⟩
      · exact Or.inr ⟨_, h3⟩
    · by_cases ho2 : o ≤ 2 * R
      · rw [cohortOldCarry (by omega) ho2, cohortCarryMid (by omega) (by omega)] at hold
        rw [cohortBottomCarry (by omega)] at hb
        by_cases hq : q = o - 1
        · right; right; right; left
          refine ⟨by omega, ho2, hq, ?_⟩
          rw [hq, show o - 1 = R + (o - R) - 1 by omega]
          exact hold.1
        · right; right; right; right
          exact ⟨by omega, ho2, by omega, hold.2 q (by omega) h2⟩
      · rw [cohortBottomCarry (by omega)] at hb
        rw [cohortOldDone (by omega)] at hold
        omega
  · by_cases hex : ∃ i, i < R ∧ cohortPos R g.1 i = q
    · exact Or.inl hex
    · right; left
      refine ⟨by omega, ?_⟩
      have hR := hch.two
      have htl := hch.le (R - 1) (by omega)
      have hp : cohortPos R g.1 (R - 1) = g.1 (R - 1) := by unfold cohortPos; omega
      refine hch.gap q (by omega) ?_ (fun i hi he => hex ⟨i, hi, he⟩)
      rcases Nat.lt_or_ge (g.1 (R - 1)) q with hlt | hge
      · exact hlt
      · exact (hex ⟨R - 1, by omega, by rw [hp]; omega⟩).elim

theorem chosenOtherLow {lam : Nat → Nat} {c : Nat} (hch : CohortChosen R s lam c) {i : Nat}
    (hi : i < R) (hp : R ≤ cohortPos R lam i) (ht : cohortTok R s (cohortPos R lam i) = .other) :
    False := by
  rcases hch.pkt i hi with h3 | ⟨h3, -⟩ | ⟨-, h4⟩
  · rw [ht] at h3; cases h3
  · rw [ht] at h3; cases h3
  · unfold cohortPos at hp; omega

/-- **No tombstone off a live cell** on the target cells of a cycle. -/
theorem tgtNoX {j o : Nat} {g : (Nat → Nat) × Nat} (h : CohortCycIn R j s g o)
    (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) (hl : s.live q = false) : s.inp q ≠ .X := by
  intro hx
  have ht : cohortTok R s q = .other := by rw [cohortTokTgt s h1, hx, hl]; exact tokInX
  rcases tgtRegion h q h1 h2 with ⟨i, hi, hp⟩ | ⟨-, he⟩ | ⟨-, -, ⟨T, hT⟩ | ⟨T, hT⟩⟩ |
      ⟨-, -, -, hlv⟩ | ⟨-, -, -, hT⟩
  · subst hp
    exact chosenOtherLow h.2.1.2 hi h1 ht
  · rw [ht] at he; cases he
  · rw [ht] at hT; cases hT
  · rw [ht] at hT; cases hT
  · rw [hl] at hlv; cases hlv
  · rw [ht] at hT; cases hT

/-- A pending packet ahead of an empty target cell is a chosen slot. -/
theorem tgtPktSlot {j o : Nat} {g : (Nat → Nat) × Nat} (h : CohortCycIn R j s g o)
    (q : Nat) (h1 : R ≤ q) (h2 : q + 1 < 2 * R) {T : Bool} (hp : cohortTok R s q = .pkt T)
    (he : cohortTok R s (q + 1) = .empty) : ∃ i, i < R ∧ cohortPos R g.1 i = q := by
  rcases tgtRegion h q h1 (by omega) with hs | ⟨-, he'⟩ | ⟨hb, -, -⟩ | ⟨-, -, -, hlv⟩ |
      ⟨-, -, -, hT⟩
  · exact hs
  · rw [hp] at he'; cases he'
  · rcases tgtRegion h (q + 1) (by omega) h2 with ⟨i, hi, hpi⟩ | ⟨hb', -⟩ |
        ⟨-, -, ⟨T', hT'⟩ | ⟨T', hT'⟩⟩ | ⟨ho1, -, hq, -⟩ | ⟨-, -, -, hT'⟩
    · have := h.2.1.2.low i hi
      omega
    · omega
    · rw [he] at hT'; cases hT'
    · rw [he] at hT'; cases hT'
    · rw [cohortBottomCarry ho1] at hb
      omega
    · rw [he] at hT'; cases hT'
  · rw [cohortTokTgt s h1, hlv, tokInLive] at hp; cases hp
  · rw [hp] at hT; cases hT

/-- A live target cell is the carry cell: every chosen slot is below it and every cell above it
is settled `false`. -/
theorem tgtLive {j o : Nat} {g : (Nat → Nat) × Nat} (h : CohortCycIn R j s g o)
    (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) (hl : s.live q = true) :
    (∀ i, i < R → cohortPos R g.1 i < q) ∧
      ∀ q', q < q' → q' < 2 * R → cohortTok R s q' = .settled false := by
  have ht : cohortTok R s q = .other := by rw [cohortTokTgt s h1, hl]; exact tokInLive _
  rcases tgtRegion h q h1 h2 with ⟨i, hi, hp⟩ | ⟨-, he⟩ | ⟨-, -, ⟨T, hT⟩ | ⟨T, hT⟩⟩ |
      ⟨ho1, ho2, hq, -⟩ | ⟨-, -, -, hT⟩
  · subst hp
    exact (chosenOtherLow h.2.1.2 hi h1 ht).elim
  · rw [ht] at he; cases he
  · rw [ht] at hT; cases hT
  · rw [ht] at hT; cases hT
  · refine ⟨fun i hi => ?_, fun q' h3 h4 => ?_⟩
    · have := h.2.1.2.low i hi
      rw [cohortBottomCarry ho1] at this
      omega
    · have hold := h.2.1.1
      rw [cohortOldCarry ho1 ho2, cohortCarryMid (by omega) (by omega)] at hold
      exact hold.2 q' (by omega) h4
  · rw [ht] at hT; cases hT

/-- The chosen tail never settles at cell `R` inside a cycle. -/
theorem tgtSettledR {j o : Nat} {g : (Nat → Nat) × Nat} (h : CohortCycIn R j s g o)
    (i : Nat) (hi : i < R) (hp : cohortPos R g.1 i = R) (T : Bool) :
    cohortTok R s R ≠ .settled T := by
  intro hT
  have hch := h.2.1.2
  rcases hch.pkt i hi with h3 | ⟨-, h4⟩ | ⟨h3, -⟩
  · rw [hp, hT] at h3; cases h3
  · have hi' : i = R - 1 := by unfold cohortPos at hp; omega
    subst hi'
    have := tailLt hch h.2.2.2
    omega
  · rw [hp, hT] at h3; cases h3

end Region

/-! ### Ghost input rows -/

section RowsA

variable {n : Nat}

theorem finInXSome (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi : Option (DigitAtom n)) (b : DigitAtom n)
    (h : finInX bx ix kx iy ky gxi = some b) : gxi = some b := by
  rcases ix with _ | _ | T | T <;> rcases iy with _ | _ | T' | T' <;> cases kx <;> cases ky <;>
    cases bx <;> simp_all [finInX, finXP]

theorem finInYSome (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi gyi : Option (DigitAtom n)) (b : DigitAtom n)
    (h : finInY ix kx iy ky gxi gyi = some b) :
    gyi = some b ∨ (ix = .X ∧ kx = false) ∨
      (∃ T, ix = .P T ∧ kx = false ∧ iy = .E ∧ ky = false ∧ gxi = some b) := by
  rcases ix with _ | _ | T | T <;> rcases iy with _ | _ | T' | T' <;> cases kx <;> cases ky <;>
    simp_all [finInY, finInYFree, finYX, finYP, shS]

theorem termInSome (ix : BankRepairDigitInSh) (kx : Bool) (gxi : Option (DigitAtom n))
    (b : DigitAtom n) (h : ghostTermIn ix kx gxi = some b) : gxi = some b := by
  rcases ix with _ | _ | T | T <;> cases kx <;> (try cases T) <;> simp_all [ghostTermIn]

theorem delInSome (stamp : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n)) (b : DigitAtom n)
    (h : (ghostDel stamp ox iy ky gxo gyi).2 = some b) :
    gyi = some b ∨ (iy = .E ∧ ky = false ∧ (∃ T, ox = .D T) ∧ gxo.atom = some b) := by
  rcases ox with _ | _ | T <;> rcases iy with _ | _ | T' | T' <;> cases ky <;>
    simp_all [ghostDel]

end RowsA

/-! ### One letter on the target inputs -/

section Move

variable {c : Compiled} {n : Nat}

/-- The target-input rows of one letter on the drawn pair edge `ke`. -/
def MoveH (R : Nat) (s : CohortLane) (ke : Option Nat) (a a' : Nat → Option (DigitAtom n))
    (stamp : DigitStamp n) (gxo : DigitOutGhost n) : Prop :=
  (∀ q, R ≤ q → q < 2 * R → ke ≠ some q → ke ≠ some (q - 1) → a' q = a q) ∧
  (ke = some (R - 1) →
    a' R = (ghostDel stamp (s.out (R - 1)) (s.inp R) (s.live R) gxo (a R)).2) ∧
  (∀ k, ke = some k → R ≤ k → k + 1 < 2 * R →
    (a' k, a' (k + 1)) = ghostFinIn (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
      (s.live (k + 1)) (a k) (a (k + 1))) ∧
  (ke = some (2 * R - 1) →
    a' (2 * R - 1) = ghostTermIn (s.inp (2 * R - 1)) (s.live (2 * R - 1)) (a (2 * R - 1)))

variable {R : Nat} {s : CohortLane} {ke : Option Nat} {a a' : Nat → Option (DigitAtom n)}
  {stamp : DigitStamp n} {gxo : DigitOutGhost n}

/-- **One letter moves a target atom** only by a hop of a pending packet into an empty cell, or
by the delimiter acceptance (no tombstone off a live cell). -/
theorem tgtMove (hm : MoveH R s ke a a' stamp gxo)
    (hnoX : ∀ q, R ≤ q → q < 2 * R → s.live q = false → s.inp q ≠ .X)
    (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) (b : DigitAtom n) (hb : a' q = some b) :
    a q = some b ∨
    (ke = some (q - 1) ∧ R ≤ q - 1 ∧ (∃ T, cohortTok R s (q - 1) = .pkt T) ∧
      cohortTok R s q = .empty ∧ a (q - 1) = some b) ∨
    (q = R ∧ ke = some (R - 1) ∧ cohortTok R s R = .empty ∧ (∃ T, s.out (R - 1) = .D T) ∧
      gxo.atom = some b) := by
  obtain ⟨hfr, hdel, hfin, hterm⟩ := hm
  by_cases hk1 : ke = some q
  · left
    by_cases hq : q + 1 < 2 * R
    · have h3 := congrArg Prod.fst (hfin q hk1 h1 hq)
      simp only [ghostFinIn] at h3
      rw [hb] at h3
      exact finInXSome _ _ _ _ _ _ _ h3.symm
    · have hq' : q = 2 * R - 1 := by omega
      subst hq'
      rw [hterm hk1] at hb
      exact termInSome _ _ _ _ hb
  · by_cases hk2 : ke = some (q - 1)
    · by_cases hqR : q = R
      · subst hqR
        rw [hdel hk2] at hb
        rcases delInSome _ _ _ _ _ _ _ hb with h3 | ⟨hiE, hkE, hD, hat⟩
        · exact Or.inl h3
        · right; right
          refine ⟨rfl, hk2, ?_, hD, hat⟩
          rw [cohortTokTgt s (Nat.le_refl _), hiE, hkE]
          exact tokInE
      · have h3 := congrArg Prod.snd (hfin (q - 1) hk2 (by omega) (by omega))
        simp only [ghostFinIn] at h3
        rw [show q - 1 + 1 = q by omega] at h3
        rw [hb] at h3
        rcases finInYSome _ _ _ _ _ _ _ h3.symm with h4 | ⟨hX, hkx⟩ |
            ⟨T, hP, hkx, hiE, hky, hat⟩
        · exact Or.inl h4
        · exact absurd hX (hnoX (q - 1) (by omega) (by omega) hkx)
        · right; left
          refine ⟨hk2, by omega, ⟨T, ?_⟩, ?_, hat⟩
          · rw [cohortTokTgt s (by omega), hP, hkx]
            exact tokInP T
          · rw [cohortTokTgt s h1, hiE, hky]
            exact tokInE
    · exact Or.inl (by rw [← hfr q h1 h2 hk1 hk2]; exact hb)

/-- A hopping pending packet leaves no atom behind. -/
theorem tgtVacate (hm : MoveH R s ke a a' stamp gxo) (k : Nat) (hk : ke = some k)
    (h1 : R ≤ k) (h2 : k + 1 < 2 * R) {T : Bool} (hp : cohortTok R s k = .pkt T)
    (he : cohortTok R s (k + 1) = .empty) : a' k = none := by
  have h3 := congrArg Prod.fst (hm.2.2.1 k hk h1 h2)
  rw [cohortTokTgt s h1] at hp
  rw [cohortTokTgt s (by omega)] at he
  obtain ⟨hP, hl⟩ := tokInPkt hp
  obtain ⟨hE, hl'⟩ := inEmptyOf he
  simp only [ghostFinIn] at h3
  rw [h3, hP, hl, hE, hl']
  simp [finInX, finXP]

end Move

/-! ### Item 1: atom identity on the target cells -/

section Identity

variable {c : Compiled} {n : Nat}

/-- A crossed chosen slot's target cell holds the operand of its crossing. -/
def CurIdA (R : Nat) (lam : Nat → Nat) (a : Nat → Option (DigitAtom n))
    (chi : Nat → DigitExport c n) : Prop :=
  ∀ i, i < R → R ≤ cohortPos R lam i → a (cohortPos R lam i) = (chi i).operand

/-- A target cell off the chosen slots holds nothing, or the operand of the last closed window's
crossing for that cell. -/
def OldIdA (R : Nat) (lam : Nat → Nat) (a : Nat → Option (DigitAtom n))
    (chiOld : Nat → DigitExport c n) : Prop :=
  ∀ q, R ≤ q → q < 2 * R → (∀ i, i < R → cohortPos R lam i ≠ q) →
    ∀ b, a q = some b → some b = (chiOld (2 * R - 1 - q)).operand

variable {R jj o : Nat} {s : CohortLane} {g : (Nat → Nat) × Nat} {ke : Option Nat}
  {a a' : Nat → Option (DigitAtom n)} {stamp : DigitStamp n} {gxo : DigitOutGhost n}
  {Ok Ok' : Bool → DigitAtom n → Prop} {c' : Nat}

/-- **Crossed slots keep their crossing operands** through every letter. -/
theorem curIdStep (hcyc : CohortCycIn R jj s g o)
    (hch' : CohortChosen R (cohortLaneStep R s ke) (cohortGenStep R s g.1 ke) c')
    (hcorr : ∀ q, R ≤ q → q < 2 * R → InCorr Ok (s.inp q) (a q))
    (hcorr' : ∀ q, R ≤ q → q < 2 * R → InCorr Ok' ((cohortLaneStep R s ke).inp q) (a' q))
    (hm : MoveH R s ke a a' stamp gxo)
    (chi chi' : Nat → DigitExport c n) (xe : Option (DigitExport c n))
    (hchi : ∀ i, chi' i =
      if cohortPos R g.1 i = R - 1 ∧ ke = some (R - 1) then xe.getD (chi i) else chi i)
    (hxe : ke = some (R - 1) → ∀ T, s.out (R - 1) = .D T → cohortTok R s R = .empty →
      ∃ x, xe = some x ∧ x.operand = gxo.atom)
    (hcur : CurIdA R g.1 a chi) : CurIdA R (cohortGenStep R s g.1 ke) a' chi' := by
  intro i hi hpos
  have hch := hcyc.2.1.2
  have hle := hch'.le i hi
  have hq2 : cohortPos R (cohortGenStep R s g.1 ke) i < 2 * R := by unfold cohortPos; omega
  obtain ⟨b, hb⟩ : ∃ b, a' (cohortPos R (cohortGenStep R s g.1 ke) i) = some b := by
    have hc := hcorr' _ hpos hq2
    rcases hch'.pkt i hi with h3 | ⟨h3, -⟩ | ⟨-, h4⟩
    · rw [cohortTokTgt _ hpos] at h3
      obtain ⟨hP, -⟩ := tokInPkt h3
      rw [hP] at hc
      exact optSome hc
    · rw [cohortTokTgt _ hpos] at h3
      obtain ⟨hS, -⟩ := tokInSettled h3
      rw [hS] at hc
      exact optSome hc
    · unfold cohortPos at hpos; omega
  rw [hb]
  have hnoX := fun q h1 h2 hl => tgtNoX hcyc q h1 h2 hl
  rcases genStepCases (R := R) (s := s) (lam := g.1) ke i with hst |
      ⟨hke, -, hlt, -, hemp, hhop⟩
  · have hpe : cohortPos R (cohortGenStep R s g.1 ke) i = cohortPos R g.1 i := by
      unfold cohortPos; rw [hst]
    rw [hpe] at hb hpos
    have hc : chi' i = chi i := by rw [hchi i, if_neg (by omega)]
    rw [hc, ← hcur i hi hpos]
    rcases tgtMove hm hnoX _ hpos (by omega) b hb with h3 | ⟨-, -, -, he, -⟩ |
        ⟨hq, -, he, -⟩
    · exact h3.symm
    · exact (chosenNe hch hi he).elim
    · exact (chosenNe hch hi (by rw [hq]; exact he)).elim
  · have hpe : cohortPos R (cohortGenStep R s g.1 ke) i = cohortPos R g.1 i + 1 := by
      unfold cohortPos; rw [hhop]; omega
    rw [hpe] at hb hpos
    have hnone : a (cohortPos R g.1 i + 1) = none := by
      have hc := hcorr _ hpos (by omega)
      rw [cohortTokTgt s hpos] at hemp
      obtain ⟨hE, -⟩ := inEmptyOf hemp
      rw [hE] at hc
      exact hc
    rcases tgtMove hm hnoX _ hpos (by omega) b hb with h3 | ⟨-, hR1, -, -, hat⟩ |
        ⟨hq, hk2, he, ⟨T, hD⟩, hat⟩
    · rw [hnone] at h3; cases h3
    · rw [show cohortPos R g.1 i + 1 - 1 = cohortPos R g.1 i by omega] at hR1 hat
      have hc : chi' i = chi i := by rw [hchi i, if_neg (by omega)]
      rw [hc, ← hcur i hi hR1, hat]
    · have hp : cohortPos R g.1 i = R - 1 := by omega
      obtain ⟨x, hx, hxo⟩ := hxe hk2 T hD he
      rw [hchi i, if_pos ⟨hp, hk2⟩, hx]
      show some b = x.operand
      rw [hxo, hat]

/-- **Old cells keep their operands** through every letter until consumed. -/
theorem oldIdStep (hcyc : CohortCycIn R jj s g o)
    (hm : MoveH R s ke a a' stamp gxo) (chiOld : Nat → DigitExport c n)
    (hold : OldIdA R g.1 a chiOld) : OldIdA R (cohortGenStep R s g.1 ke) a' chiOld := by
  intro q h1 h2 hnot b hb
  have hch := hcyc.2.1.2
  have hnoX := fun q h1 h2 hl => tgtNoX hcyc q h1 h2 hl
  rcases tgtMove hm hnoX q h1 h2 b hb with h3 | ⟨hk2, hR1, ⟨T, hpk⟩, hemp, -⟩ |
      ⟨hq, hk2, hemp, ⟨T, hD⟩, -⟩
  · refine hold q h1 h2 (fun i hi hpi => ?_) b h3
    rcases genStepCases (R := R) (s := s) (lam := g.1) ke i with hst |
        ⟨hke, -, hlt, hno, hemp', -⟩
    · apply hnot i hi
      unfold cohortPos at hpi ⊢
      rw [hst]
      exact hpi
    · have hq1 : q + 1 < 2 * R := by unfold cohortPos at hpi; omega
      have hpk : cohortTok R s q = .pkt (cohortTail R i) := by
        rcases hch.pkt i hi with h4 | ⟨-, h5⟩ | ⟨h4, -⟩
        · rw [hpi] at h4; exact h4
        · omega
        · exact absurd h4 hno
      rw [hpi] at hke hemp'
      rw [tgtVacate hm q hke h1 hq1 hpk hemp'] at hb
      cases hb
  · obtain ⟨i, hi, hpi⟩ := tgtPktSlot hcyc (q - 1) hR1 (by omega) hpk
      (by rw [show q - 1 + 1 = q by omega]; exact hemp)
    have hlt : g.1 i < R := by
      rcases Nat.lt_or_ge (g.1 i) R with hlt | hge
      · exact hlt
      exfalso
      have hl := hch.le i hi
      have hi0 : 0 < i := by unfold cohortPos at hpi; omega
      have hlt' := chosenPosLt hch (show i - 1 < i by omega) hi
      have hle' := hch.le (i - 1) (by omega)
      have hq' : cohortPos R g.1 (i - 1) = q := by unfold cohortPos at hpi hlt' ⊢; omega
      exact chosenNe hch (show i - 1 < R by omega) (by rw [hq']; exact hemp)
    have hhop := genStepHop (R := R) (s := s) (lam := g.1) hi hlt hpi
      (by rw [hpk]; intro h; cases h) (by rw [show q - 1 + 1 = q by omega]; exact hemp)
    exfalso
    apply hnot i hi
    rw [hk2]
    unfold cohortPos at hpi ⊢
    rw [hhop]
    omega
  · subst q
    have hocc : cohortTok R s (R - 1) ≠ .empty := by
      rw [cohortTokSrc s (by omega), hD]; intro h; cases h
    obtain ⟨i, hi, hpi⟩ := delSlot hch (bottomGe R o) hcyc.2.2.2 hocc
    have hhop := genStepHop (R := R) (s := s) (lam := g.1) hi
      (by unfold cohortPos at hpi; omega) hpi
      (by rw [cohortTokSrc s (by omega), hD]; intro h; cases h)
      (by rw [show R - 1 + 1 = R by omega]; exact hemp)
    exfalso
    apply hnot i hi
    rw [hk2]
    unfold cohortPos at hpi ⊢
    rw [hhop]
    omega

/-- **At a closing letter** the crossed slots become the old cells of the next cycle. -/
theorem oldOfCur {lam : Nat → Nat} (hch' : CohortChosen R s lam c') (hd : gridDone R R lam)
    (chi : Nat → DigitExport c n) (hcur : CurIdA R lam a chi) :
    OldIdA R (fun _ => 0) a chi := by
  intro q h1 h2 _ b hb
  have hi : 2 * R - 1 - q < R := by omega
  have hl := hd _ hi
  have hl2 := hch'.le _ hi
  have hp : cohortPos R lam (2 * R - 1 - q) = q := by unfold cohortPos; omega
  have h3 := hcur _ hi (by rw [hp]; exact h1)
  rw [hp, hb] at h3
  exact h3

end Identity

/-! ### Items 2 and 3: clean ledgers on the target cells -/

section Ledger

variable {c : Compiled} {n : Nat}

/-- Every ledger on a target cell `q` is clean, has `q + 1 - R` uses, and its `m`-th use reads
the operand of `chiOld (R - 1 - m)` after `t0`. -/
def LedgerA (R t0 : Nat) (chiOld : Nat → DigitExport c n)
    (cc : Nat → Option (DigitCarryGhost c n)) : Prop :=
  ∀ q, R ≤ q → q < 2 * R → ∀ L, cc q = some L →
    L.inherited = none ∧ L.uses.length = q + 1 - R ∧
    ∀ m (u : DigitUse c n), L.uses[m]? = some u →
      u.operand = (chiOld (R - 1 - m)).operand ∧ t0 < u.time

/-- The target-ledger rows of one letter on the drawn pair edge `ke`, stamped `tn`. -/
def CarryH (R : Nat) (s : CohortLane) (ke : Option Nat) (a : Nat → Option (DigitAtom n))
    (cc cc' : Nat → Option (DigitCarryGhost c n)) (tn : Nat) : Prop :=
  (∀ q, R ≤ q → q < 2 * R → ke ≠ some q → ke ≠ some (q - 1) → cc' q = cc q) ∧
  (ke = some (R - 1) → cc' R = cc R) ∧
  (∀ k, ke = some k → R ≤ k → k + 1 < 2 * R →
    (cc' k = none ∨ cc' k = cc k ∨
      (k = R ∧ shS (s.inp k) = true ∧ ∃ u : DigitUse c n, u.time = tn ∧ u.operand = a k ∧
        cc' k = some (DigitCarryGhost.mk none [u]))) ∧
    (s.live k = false → cc' (k + 1) = cc (k + 1)) ∧
    (s.live k = true → s.live (k + 1) = false → ∀ T, s.inp (k + 1) = .S T →
      ∀ L, cc k = some L → ∃ u : DigitUse c n, u.time = tn ∧ u.operand = a (k + 1) ∧
        cc' (k + 1) = some (DigitCarryGhost.mk L.inherited (L.uses ++ [u])))) ∧
  (ke = some (2 * R - 1) → cc' (2 * R - 1) = none ∨ cc' (2 * R - 1) = cc (2 * R - 1))

variable {R jj o t0 tn : Nat} {s : CohortLane} {g : (Nat → Nat) × Nat} {ke : Option Nat}
  {a : Nat → Option (DigitAtom n)} {cc cc' : Nat → Option (DigitCarryGhost c n)}
  {Ok : Bool → DigitAtom n → Prop}

theorem inSome {i : BankRepairDigitInSh} {T : Bool} (hi : i = .S T) {b : Option (DigitAtom n)}
    (h : InCorr Ok i b) : ∃ x, b = some x := by
  subst hi
  exact optSome h

/-- **Launch, consumption and terminal ledgers**: every letter keeps `LedgerA`. A launch (at
`R`) reads the settled old operand of cell `R`; a carry moving onto `q` reads the settled old
operand of `q`; both are stamped after `t0`. -/
theorem ledgerStep (hcyc : CohortCycIn R jj s g o)
    (hcorr : ∀ q, R ≤ q → q < 2 * R → InCorr Ok (s.inp q) (a q))
    (hlive : ∀ q, R ≤ q → q < 2 * R → s.live q = (cc q).isSome)
    (chiOld : Nat → DigitExport c n) (hold : OldIdA R g.1 a chiOld)
    (hc : CarryH R s ke a cc cc' tn) (ht : t0 < tn)
    (hL : LedgerA R t0 chiOld cc) : LedgerA R t0 chiOld cc' := by
  obtain ⟨cfr, cdel, cfin, cterm⟩ := hc
  intro q h1 h2 L hLq
  by_cases hk1 : ke = some q
  · by_cases hq : q + 1 < 2 * R
    · rcases (cfin q hk1 h1 hq).1 with h3 | h3 | ⟨hqR, hS, u, hut, huo, hu⟩
      · rw [h3] at hLq; cases hLq
      · rw [h3] at hLq; exact hL q h1 h2 L hLq
      · rw [hu] at hLq
        cases hLq
        subst q
        refine ⟨rfl, by simp, fun m u' hm => ?_⟩
        obtain ⟨rfl, rfl⟩ := singletonGet u u' m hm
        obtain ⟨T, hT⟩ : ∃ T, s.inp R = .S T := by
          revert hS
          cases s.inp R <;> simp [shS]
        obtain ⟨b, hb⟩ := inSome hT (hcorr R h1 h2)
        have hnc : ∀ i, i < R → cohortPos R g.1 i ≠ R := by
          intro i hi hpi
          by_cases hlv : s.live R = true
          · have := (tgtLive hcyc R h1 h2 hlv).1 i hi
            omega
          · have hlv' : s.live R = false := by simpa using hlv
            refine tgtSettledR hcyc i hi hpi T ?_
            rw [cohortTokTgt s h1, hT, hlv']
            simp [cohortTokIn]
        have hid := hold R h1 h2 hnc b hb
        refine ⟨?_, by omega⟩
        rw [huo, hb, hid, show 2 * R - 1 - R = R - 1 - 0 by omega]
    · have hq' : q = 2 * R - 1 := by omega
      subst hq'
      rcases cterm hk1 with h3 | h3
      · rw [h3] at hLq; cases hLq
      · rw [h3] at hLq; exact hL _ h1 h2 L hLq
  · by_cases hk2 : ke = some (q - 1)
    · by_cases hqR : q = R
      · subst q
        rw [cdel hk2] at hLq
        exact hL _ h1 h2 L hLq
      · have hf := cfin (q - 1) hk2 (by omega) (by omega)
        rw [show q - 1 + 1 = q by omega] at hf
        by_cases hlk : s.live (q - 1) = true
        · obtain ⟨hpos, hset⟩ := tgtLive hcyc (q - 1) (by omega) (by omega) hlk
          have hsq := hset q (by omega) h2
          rw [cohortTokTgt s h1] at hsq
          obtain ⟨hS, hlq⟩ := tokInSettled hsq
          obtain ⟨L0, hL0⟩ : ∃ L0, cc (q - 1) = some L0 := by
            have := hlive (q - 1) (by omega) (by omega)
            rw [hlk] at this
            cases h0 : cc (q - 1) with
            | none => rw [h0] at this; cases this
            | some L0 => exact ⟨L0, rfl⟩
          obtain ⟨u, hut, huo, hu⟩ := hf.2.2 hlk hlq false hS L0 hL0
          rw [hu] at hLq
          cases hLq
          obtain ⟨hi0, hlen0, hops0⟩ := hL (q - 1) (by omega) (by omega) L0 hL0
          refine ⟨hi0, by simp [hlen0]; omega, fun m u' hm => ?_⟩
          by_cases hm1 : m < L0.uses.length
          · rw [List.getElem?_append_left hm1] at hm
            exact hops0 m u' hm
          · rw [List.getElem?_append_right (by omega)] at hm
            obtain ⟨hm2, rfl⟩ := singletonGet u u' _ hm
            obtain ⟨b, hb⟩ := inSome hS (hcorr q h1 h2)
            have hnc : ∀ i, i < R → cohortPos R g.1 i ≠ q := by
              intro i hi hpi
              have := hpos i hi
              omega
            have hid := hold q h1 h2 hnc b hb
            refine ⟨?_, by omega⟩
            rw [huo, hb, hid, show 2 * R - 1 - q = R - 1 - m by omega]
        · have hlk' : s.live (q - 1) = false := by simpa using hlk
          rw [hf.2.1 hlk'] at hLq
          exact hL q h1 h2 L hLq
    · rw [cfr q h1 h2 hk1 hk2] at hLq
      exact hL q h1 h2 L hLq

end Ledger

end L3.UseCells

#print axioms L3.UseCells.tgtMove
#print axioms L3.UseCells.curIdStep
#print axioms L3.UseCells.oldIdStep
#print axioms L3.UseCells.oldOfCur
#print axioms L3.UseCells.ledgerStep

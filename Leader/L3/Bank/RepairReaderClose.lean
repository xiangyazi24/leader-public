import Leader.L3.Bank.RepairReader

/-!
R10b, R stage of the BANK repair: the resident-retirement clock
(paper lem:e-readers, repair.tex 1096-1107: each of at most n marked
resident readers needs at most t outgoing hits, conditional mean t n²).

Scope.  The installed `BankRepairResidentRetirementClock` quantifies
over every reference state with `BankRepairWAccepted`
(native ∧ candidate ∧ word factors).  That class carries no
grant-freeness, so the OLD no-FIRE premise of the reader projection
(`bankRepairReaderPhiStepOfNoFire`) is not available on it, and without
it the actual masked word need not be a phiR reader run.  The paper's R
stage runs inside the grant-free repair phase (repair.tex 91: no birth
is possible during repair).  This module proves the clock for starts in
`BankPostInheritedGrantDrain` (closed under `bankRepairNext`,
grant-free hence birth-free), which is the class the repair runs in.

Proof: a tag invariant (inherited tags sit on occupied raw slots, the
H bits are exactly the inherited tags, done means no inherited tag)
along the coupled physical/reader trace; the inherited-debt potential
of E.G19 never increases on any edge and drops by one on the outgoing
edge of any inherited reader; a final ticket pays the last edge.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ## Finite sums over the ring -/

/-- Exchanging one coordinate of a finite sum.
Consumer: `bankRepairCloseSumTwoCells`, `bankRepairCloseSumIndicator`. -/
theorem bankRepairCloseSumExchange {m : Nat} (f g : Fin m → Nat)
    (a : Fin m) (h : ∀ i, i ≠ a → f i = g i) :
    (List.ofFn f).sum + g a = (List.ofFn g).sum + f a := by
  induction m with
  | zero => exact a.elim0
  | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.sum_cons, List.sum_cons]
      cases a using Fin.cases with
      | zero =>
          have htail : (List.ofFn fun i : Fin m => f i.succ) =
              List.ofFn fun i : Fin m => g i.succ := by
            congr 1
            funext i
            exact h i.succ (Fin.succ_ne_zero i)
          rw [htail]
          omega
      | succ k =>
          have h0 : f 0 = g 0 := h 0 (fun hk => Fin.succ_ne_zero k hk.symm)
          have htail := ih (fun i => f i.succ) (fun i => g i.succ) k
            (fun i hi => h i.succ (fun he => hi (Fin.succ_inj.mp he)))
          rw [h0]
          omega

/-- Two changed coordinates of a finite sum.
Consumer: `bankRepairCloseTotalStep`. -/
theorem bankRepairCloseSumTwoCells {m : Nat} (f g : Fin m → Nat)
    (e j : Fin m) (hje : j ≠ e)
    (h : ∀ i, i ≠ e → i ≠ j → g i = f i) :
    (List.ofFn g).sum + (f e + f j) =
      (List.ofFn f).sum + (g e + g j) := by
  have h1 := bankRepairCloseSumExchange
    (fun i => if i = e then g e else f i) f e
    (fun i hi => by simp [hi])
  have h2 := bankRepairCloseSumExchange g
    (fun i => if i = e then g e else f i) j
    (fun i hi => by
      by_cases hie : i = e
      · subst hie
        simp
      · simp [hie, h i hie hi])
  rw [if_pos (rfl : e = e)] at h1
  rw [if_neg hje] at h2
  omega

/-- A one-point indicator sums to one.
Consumer: `bankRepairCloseDrift`. -/
theorem bankRepairCloseSumIndicator {m : Nat} (a : Fin m) :
    (List.ofFn (fun i : Fin m => if i = a then 1 else 0)).sum = 1 := by
  have h := bankRepairCloseSumExchange
    (fun i : Fin m => if i = a then 1 else 0) (fun _ => 0) a
    (fun i hi => by simp [hi])
  rw [ofFn_sum_const] at h
  simp at h
  omega

/-! ## Raw-reader rows and the reader control on one edge -/

/-- The six exhaustive OLD raw-reader rows with their physical
token outputs.  Consumer: the tag and debt step lemmas below. -/
theorem bankRepairCloseRowCases {c : Compiled} (x y : ProjR c) :
    (∃ src ty, x.rawTok = some src ∧ y.rawTok = some ty ∧
      BlockA.readerCase x y = .collision ∧
      (pairR x y).1.rawTok = none ∧ (pairR x y).2.rawTok = some ty) ∨
    (∃ src nxt, x.rawTok = some src ∧ y.rawTok = none ∧ src.j < c.t ∧
      BlockA.readerCase x y = .move ∧
      (pairR x y).1.rawTok = none ∧ (pairR x y).2.rawTok = some nxt ∧
      nxt.jm1.val = src.j) ∨
    (∃ src, x.rawTok = some src ∧ y.rawTok = none ∧ ¬ src.j < c.t ∧
      BlockA.readerCase x y = .terminal ∧
      (pairR x y).1.rawTok = none ∧ (pairR x y).2.rawTok = none) ∨
    (∃ ty, x.rawTok = none ∧ y.rawTok = some ty ∧
      BlockA.readerCase x y = .resident ∧
      (pairR x y).1.rawTok = none ∧ (pairR x y).2.rawTok = some ty) ∨
    (x.rawTok = none ∧ y.rawTok = none ∧
      BlockA.readerCase x y = .kickArm ∧
      (pairR x y).1.rawTok = none ∧ (pairR x y).2.rawTok = none) ∨
    (x.rawTok = none ∧ y.rawTok = none ∧
      BlockA.readerCase x y = .kickLaunch ∧
      (pairR x y).1.rawTok = none) := by
  cases hx : x.rawTok with
  | some src =>
      cases hy : y.rawTok with
      | some ty =>
          obtain ⟨h1, h2, h3⟩ := Closure.readerCollisionRow x y src ty hx hy
          exact Or.inl ⟨src, ty, rfl, rfl, h3, h1, h2⟩
      | none =>
          by_cases hm : src.j < c.t
          · obtain ⟨h1, _, h3⟩ := Closure.readerMoveRow x y src hx hy hm
            have hcursor : (pairR x y).2.rawTok.map
                (fun raw => raw.jm1.val) = some src.j := by
              simp [pairR, rawR, rawD1Step, ProjR.lift, hx, hy, hm]
            cases hnext : (pairR x y).2.rawTok with
            | none =>
                rw [hnext] at hcursor
                cases hcursor
            | some nxt =>
                rw [hnext] at hcursor
                simp at hcursor
                exact Or.inr (Or.inl
                  ⟨src, nxt, rfl, rfl, hm, h3, h1, rfl, hcursor⟩)
          · obtain ⟨h1, h2, h3⟩ := Closure.readerTerminalRow x y src hx hy hm
            exact Or.inr (Or.inr (Or.inl ⟨src, rfl, rfl, hm, h3, h1, h2⟩))
  | none =>
      cases hy : y.rawTok with
      | some ty =>
          obtain ⟨h1, h2, h3⟩ := Closure.readerResidentRow x y ty hx hy
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ty, rfl, rfl, h3, h1, h2⟩)))
      | none =>
          cases hk : y.rawKick with
          | false =>
              obtain ⟨h1, h2, h3⟩ := Closure.readerKickArmRow x y hx hy hk
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨rfl, rfl, h3, h1, h2⟩))))
          | true =>
              have h3 : BlockA.readerCase x y = .kickLaunch := by
                simp [rawR, rawD1Step, BlockA.readerCase,
                  ProjR.lift, hx, hy, hk]
              have h1 : (pairR x y).1.rawTok = none := by
                simp [pairR, rawR, rawD1Step, ProjR.lift, hx, hy, hk]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨rfl, rfl, h3, h1⟩))))

/-- No tag of this kind is inherited.
Consumer: the tag invariant `BankRepairCloseReaderTagged`. -/
def bankRepairCloseNotInherited {n t : Nat} (tag : BlockA.RawTag n t) : Prop :=
  ∀ name : Fin n, tag ≠ .inherited name

/-- An empty raw slot carries no resident debt. Consumer: `bankRepairClosePairDebt`, `bankRepairCloseTotalStep`. -/
theorem bankRepairCloseDebtNone {n t : Nat} (tag : BlockA.RawTag n t) :
    bankRepairReaderResidentSiteDebt tag none = 0 := by
  cases tag <;> rfl

/-- A tag that is not inherited carries no resident debt.
Consumer: `bankRepairClosePairDebt`. -/
theorem bankRepairCloseDebtNotInherited {n t : Nat}
    (tag : BlockA.RawTag n t) (h : bankRepairCloseNotInherited tag)
    (tok : Option (RawTok t)) :
    bankRepairReaderResidentSiteDebt tag tok = 0 := by
  cases tag with
  | empty => cases tok <;> rfl
  | inherited name => exact absurd rfl (h name)
  | fresh name index samples => cases tok <;> rfl

/-- Tags off the selected pair are unchanged. Consumer: `bankRepairCloseTotalStep`, `bankRepairCloseTaggedStep`. -/
theorem bankRepairCloseTagsOther {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (BlockA.readerControlNext ring h p e p').tags i = h.tags i := by
  simp [BlockA.readerControlNext, hi, hj]

/-- R0a/R0b/R0c erase the initiator tag. Consumer: `bankRepairCloseSourceNotInherited`. -/
theorem bankRepairCloseTagsSourceErased {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hcase : BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .collision ∨
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .move ∨
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .terminal) :
    (BlockA.readerControlNext ring h p e p').tags e = .empty := by
  rcases hcase with hc | hc | hc <;>
    simp [BlockA.readerControlNext, hc]

/-- Resident and kick rows keep the initiator tag. Consumer: `bankRepairCloseSourceNotInherited`. -/
theorem bankRepairCloseTagsSourceKept {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hcase : BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .resident ∨
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .kickArm ∨
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .kickLaunch) :
    (BlockA.readerControlNext ring h p e p').tags e = h.tags e := by
  rcases hcase with hc | hc | hc <;>
    simp [BlockA.readerControlNext, hc]

/-- Collision, resident and kick-arm rows keep the responder tag. Consumer: `bankRepairClosePairDebt`, `bankRepairCloseTaggedStep`. -/
theorem bankRepairCloseTagsTargetKept {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hcase : BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .collision ∨
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .resident ∨
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .kickArm) :
    (BlockA.readerControlNext ring h p e p').tags (ring.rightNeighbor e) =
      h.tags (ring.rightNeighbor e) := by
  rcases hcase with hc | hc | hc <;>
    simp [BlockA.readerControlNext, hc, hne]

/-- A move transfers the initiator tag to the responder. Consumer: `bankRepairClosePairDebt`, `bankRepairCloseTaggedStep`. -/
theorem bankRepairCloseTagsTargetMove {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hc : BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .move) :
    (BlockA.readerControlNext ring h p e p').tags (ring.rightNeighbor e) =
      BlockA.readerTransfer (h.tags e)
        (BlockA.readerSelectedSample (ring.rightNeighbor e)
          (p e) (p (ring.rightNeighbor e))) := by
  simp [BlockA.readerControlNext, hc, hne]

/-- A terminal row empties the responder tag. Consumer: `bankRepairCloseTaggedStep`, `bankRepairCloseDrift`. -/
theorem bankRepairCloseTagsTargetTerminal {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hc : BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .terminal) :
    (BlockA.readerControlNext ring h p e p').tags (ring.rightNeighbor e) =
      .empty := by
  simp [BlockA.readerControlNext, hc, hne]

/-- A kick launch never writes an inherited responder tag. Consumer: `bankRepairClosePairDebt`, `bankRepairCloseTaggedStep`. -/
theorem bankRepairCloseTagsTargetLaunch {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hc : BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .kickLaunch) :
    bankRepairCloseNotInherited
      ((BlockA.readerControlNext ring h p e p').tags (ring.rightNeighbor e)) := by
  intro name
  simp [BlockA.readerControlNext, hc, hne]
  split
  · simp
  · split <;> simp

/-- Transfer of a non-inherited tag is not inherited. Consumer: `bankRepairCloseTaggedStep`, `bankRepairCloseDrift`. -/
theorem bankRepairCloseTransferNotInherited {n : Nat} {c : Compiled}
    (tag : BlockA.RawTag n c.t) (h : bankRepairCloseNotInherited tag)
    (read : BlockA.ReaderSample n) :
    bankRepairCloseNotInherited (BlockA.readerTransfer tag read) := by
  cases tag with
  | empty => intro name; simp [BlockA.readerTransfer]
  | inherited m => exact absurd rfl (h m)
  | fresh m index samples => intro name; simp [BlockA.readerTransfer]

/-- phiR initiator coordinate. Consumer: `bankRepairCloseTotalStep`. -/
theorem bankRepairClosePhiSource {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjR c) (e : Fin n) :
    (phiR ring p e) e = (pairR (p e) (p (ring.rightNeighbor e))).1 := by
  simp [phiR, projectedEdge]

/-- phiR responder coordinate. Consumer: `bankRepairCloseTotalStep`, `bankRepairCloseTaggedStep`. -/
theorem bankRepairClosePhiTarget {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjR c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (phiR ring p e) (ring.rightNeighbor e) =
      (pairR (p e) (p (ring.rightNeighbor e))).2 := by
  simp [phiR, projectedEdge, hne]

/-- phiR leaves other sites unchanged. Consumer: `bankRepairCloseTotalStep`, `bankRepairCloseTaggedStep`. -/
theorem bankRepairClosePhiOther {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjR c) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (phiR ring p e) i = p i := by
  simp [phiR, projectedEdge, hi, hj]

/-! ## The resident debt on one edge -/

/-- E.G19 pair step: the selected pair never gains inherited debt, and
the outgoing edge of an inherited reader pays one ticket (R0a collision,
R0b move, R0c terminal).  Consumer: `bankRepairCloseTotalStep`. -/
theorem bankRepairClosePairDebt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    bankRepairReaderResidentSiteDebt
        ((BlockA.readerControlNext ring h p e p').tags (ring.rightNeighbor e))
        (pairR (p e) (p (ring.rightNeighbor e))).2.rawTok ≤
      bankRepairReaderResidentSiteDebt (h.tags e) (p e).rawTok +
        bankRepairReaderResidentSiteDebt (h.tags (ring.rightNeighbor e))
          (p (ring.rightNeighbor e)).rawTok ∧
    (∀ (name : Fin n) (src : RawTok c.t),
      h.tags e = .inherited name → (p e).rawTok = some src →
      bankRepairReaderResidentSiteDebt
          ((BlockA.readerControlNext ring h p e p').tags (ring.rightNeighbor e))
          (pairR (p e) (p (ring.rightNeighbor e))).2.rawTok + 1 ≤
        bankRepairReaderResidentSiteDebt (h.tags e) (p e).rawTok +
          bankRepairReaderResidentSiteDebt (h.tags (ring.rightNeighbor e))
            (p (ring.rightNeighbor e)).rawTok) := by
  rcases bankRepairCloseRowCases (p e) (p (ring.rightNeighbor e)) with
    ⟨src, ty, hx, hy, hc, _, h2⟩ | ⟨src, nxt, hx, hy, hm, hc, _, h2, hj1⟩ |
    ⟨src, hx, hy, hm, hc, _, h2⟩ | ⟨ty, hx, hy, hc, _, h2⟩ |
    ⟨hx, hy, hc, _, h2⟩ | ⟨hx, hy, hc, _⟩
  · rw [bankRepairCloseTagsTargetKept ring h p p' e hne (Or.inl hc), h2, ← hy]
    refine ⟨Nat.le_add_left _ _, ?_⟩
    intro name src' hinh hsrc
    rw [hinh, hsrc]
    have := bankRepairReaderResidentInheritedPositive name src'
    omega
  · rw [bankRepairCloseTagsTargetMove ring h p p' e hne hc, h2, hy, hx,
      bankRepairCloseDebtNone]
    cases htag : h.tags e with
    | empty =>
        simp [BlockA.readerTransfer, bankRepairReaderResidentSiteDebt]
    | fresh m index samples =>
        simp [BlockA.readerTransfer, bankRepairReaderResidentSiteDebt]
    | inherited m =>
        have hjm := src.jm1.isLt
        have hmv : src.jm1.val + 1 < c.t := hm
        have hval : nxt.jm1.val = src.jm1.val + 1 := hj1
        have hmain : c.t - nxt.jm1.val + 1 = c.t - src.jm1.val := by omega
        constructor
        · change c.t - nxt.jm1.val ≤ c.t - src.jm1.val + 0
          omega
        · intro _ _ _ _
          change c.t - nxt.jm1.val + 1 ≤ c.t - src.jm1.val + 0
          omega
  · rw [h2, bankRepairCloseDebtNone]
    refine ⟨Nat.zero_le _, ?_⟩
    intro name src' hinh hsrc
    rw [hinh, hsrc]
    have := bankRepairReaderResidentInheritedPositive name src'
    omega
  · rw [bankRepairCloseTagsTargetKept ring h p p' e hne (Or.inr (Or.inl hc)),
      h2, ← hy]
    refine ⟨Nat.le_add_left _ _, ?_⟩
    intro _ src' _ hsrc
    rw [hx] at hsrc
    cases hsrc
  · rw [h2, bankRepairCloseDebtNone]
    refine ⟨Nat.zero_le _, ?_⟩
    intro _ src' _ hsrc
    rw [hx] at hsrc
    cases hsrc
  · rw [bankRepairCloseDebtNotInherited _
      (bankRepairCloseTagsTargetLaunch ring h p p' e hne hc)]
    refine ⟨Nat.zero_le _, ?_⟩
    intro _ src' _ hsrc
    rw [hx] at hsrc
    cases hsrc

/-- The total inherited debt never increases on an edge, and drops by
one on the outgoing edge of an inherited reader with its token.
Consumer: `bankRepairCloseDrift`. -/
theorem bankRepairCloseTotalStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    bankRepairReaderResidentTotal (phiR ring p e)
        (BlockA.readerControlNext ring h p e p') ≤
      bankRepairReaderResidentTotal p h ∧
    (∀ (name : Fin n) (src : RawTok c.t),
      h.tags e = .inherited name → (p e).rawTok = some src →
      bankRepairReaderResidentTotal (phiR ring p e)
          (BlockA.readerControlNext ring h p e p') + 1 ≤
        bankRepairReaderResidentTotal p h) := by
  have hpair := bankRepairClosePairDebt ring h p p' e hne
  have hcells := bankRepairCloseSumTwoCells
    (fun i => bankRepairReaderResidentSiteDebt (h.tags i) (p i).rawTok)
    (fun i => bankRepairReaderResidentSiteDebt
      ((BlockA.readerControlNext ring h p e p').tags i)
      ((phiR ring p e) i).rawTok)
    e (ring.rightNeighbor e) hne
    (fun i hi hj => by
      rw [bankRepairCloseTagsOther ring h p p' e i hi hj,
        bankRepairClosePhiOther ring p e i hi hj])
  rw [bankRepairClosePhiSource ring p e,
    bankRepairClosePhiTarget ring p e hne] at hcells
  have hsrcNone : (pairR (p e) (p (ring.rightNeighbor e))).1.rawTok = none := by
    rcases bankRepairCloseRowCases (p e) (p (ring.rightNeighbor e)) with
      ⟨_, _, _, _, _, h1, _⟩ | ⟨_, _, _, _, _, _, h1, _, _⟩ |
      ⟨_, _, _, _, _, h1, _⟩ | ⟨_, _, _, _, h1, _⟩ |
      ⟨_, _, _, h1, _⟩ | ⟨_, _, _, h1⟩ <;> exact h1
  rw [hsrcNone, bankRepairCloseDebtNone] at hcells
  unfold bankRepairReaderResidentTotal
  constructor
  · have := hpair.1
    omega
  · intro name src hinh hsrc
    have := hpair.2 name src hinh hsrc
    omega

/-! ## The reader tag invariant -/

/-- Inherited tags sit on occupied raw slots, the H bits are exactly
the inherited tags, and a done reader has no inherited tag.
Consumer: `bankRepairCloseTraceFacts` and `bankRepairCloseDrift`. -/
def BankRepairCloseReaderTagged {n : Nat} {c : Compiled}
    (p : Fin n → ProjR c) (h : BlockA.ReaderControl n c) : Prop :=
  (∀ (i name : Fin n), h.tags i = .inherited name →
    (p i).rawTok.isSome = true) ∧
  (∀ name : Fin n, h.inheritedNames name = true ↔
    ∃ i : Fin n, h.tags i = .inherited name) ∧
  (h.phase = .done → ∀ (i name : Fin n), h.tags i ≠ .inherited name)

/-- Boolean any over a finite word. Consumer: `bankRepairCloseHasInheritedIff`. -/
theorem bankRepairCloseAnyBoolIff {n : Nat} (f : Fin n → Bool) :
    (List.ofFn f).any (fun b => b) = true ↔ ∃ i : Fin n, f i = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨b, hmem, hb⟩
    rw [List.mem_ofFn] at hmem
    obtain ⟨i, rfl⟩ := hmem
    exact ⟨i, hb⟩
  · rintro ⟨i, hi⟩
    exact ⟨true, List.mem_ofFn.mpr ⟨i, hi⟩, rfl⟩

/-- The next H bits are exactly the next inherited tags. Consumer: `bankRepairCloseTaggedStep`. -/
theorem bankRepairCloseNamesIff {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e name : Fin n) :
    (BlockA.readerControlNext ring h p e p').inheritedNames name = true ↔
      ∃ i : Fin n, (BlockA.readerControlNext ring h p e p').tags i =
        .inherited name := by
  have hx : (BlockA.readerControlNext ring h p e p').inheritedNames name =
      Closure.readerInheritedSet
        (BlockA.readerControlNext ring h p e p').tags name := rfl
  rw [hx]
  exact Closure.readerInheritedSetIff _ name

/-- The still-inherited test is one true H bit. Consumer: `bankRepairCloseTaggedStep`, `bankRepairCloseDrift`. -/
theorem bankRepairCloseHasInheritedIff {n : Nat} {c : Compiled}
    (h : BlockA.ReaderControl n c) :
    Closure.readerHasInherited h = true ↔
      ∃ name : Fin n, h.inheritedNames name = true := by
  unfold Closure.readerHasInherited
  exact bankRepairCloseAnyBoolIff h.inheritedNames

/-- The next phase field. Consumer: `bankRepairClosePhaseDoneIff`. -/
theorem bankRepairClosePhaseNext {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n) :
    (BlockA.readerControlNext ring h p e p').phase =
      if (h.phase == .done ||
          !Closure.readerHasInherited
            (BlockA.readerControlNext ring h p e p')) = true
      then .done else .retire := rfl

/-- The next control is done exactly when the old one was done or no
inherited tag survives.  Consumer: the tag step and the drift. -/
theorem bankRepairClosePhaseDoneIff {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n) :
    (BlockA.readerControlNext ring h p e p').phase = .done ↔
      (h.phase = .done ∨
        Closure.readerHasInherited
          (BlockA.readerControlNext ring h p e p') = false) := by
  rw [bankRepairClosePhaseNext]
  cases hph : h.phase <;>
    cases hhas : Closure.readerHasInherited
      (BlockA.readerControlNext ring h p e p') <;> simp

/-- With the tag invariant, the next source tag is never inherited.
Consumer: `bankRepairCloseTaggedStep`. -/
theorem bankRepairCloseSourceNotInherited {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hI : ∀ (i name : Fin n), h.tags i = .inherited name →
      (p i).rawTok.isSome = true) :
    bankRepairCloseNotInherited
      ((BlockA.readerControlNext ring h p e p').tags e) := by
  rcases bankRepairCloseRowCases (p e) (p (ring.rightNeighbor e)) with
    ⟨_, _, _, _, hc, _, _⟩ | ⟨_, _, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _⟩ | ⟨_, hx, _, hc, _, _⟩ |
    ⟨hx, _, hc, _, _⟩ | ⟨hx, _, hc, _⟩
  · rw [bankRepairCloseTagsSourceErased ring h p p' e (Or.inl hc)]
    intro name hname; cases hname
  · rw [bankRepairCloseTagsSourceErased ring h p p' e (Or.inr (Or.inl hc))]
    intro name hname; cases hname
  · rw [bankRepairCloseTagsSourceErased ring h p p' e (Or.inr (Or.inr hc))]
    intro name hname; cases hname
  all_goals
    first
    | rw [bankRepairCloseTagsSourceKept ring h p p' e (Or.inl hc)]
    | rw [bankRepairCloseTagsSourceKept ring h p p' e (Or.inr (Or.inl hc))]
    | rw [bankRepairCloseTagsSourceKept ring h p p' e (Or.inr (Or.inr hc))]
    intro name hname
    have := hI e name hname
    rw [hx] at this
    cases this

/-- The tag invariant is preserved by every reader edge on the phiR
successor.  Consumer: `bankRepairCloseTraceFacts`. -/
theorem bankRepairCloseTaggedStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (hn2 : 2 ≤ n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hT : BankRepairCloseReaderTagged p h) :
    BankRepairCloseReaderTagged (phiR ring p e)
      (BlockA.readerControlNext ring h p e p') := by
  obtain ⟨hI, hN, hD⟩ := hT
  have hne := clockNeighborDifferent ring hn2 e
  have hsrc := bankRepairCloseSourceNotInherited ring h p p' e hI
  -- the responder tag: inherited only on an occupied successor slot,
  -- and never inherited when no OLD tag was
  have htarget : (∀ name : Fin n,
      (BlockA.readerControlNext ring h p e p').tags (ring.rightNeighbor e) =
        .inherited name →
      ((phiR ring p e) (ring.rightNeighbor e)).rawTok.isSome = true) ∧
      ((∀ (i name : Fin n), h.tags i ≠ .inherited name) →
        bankRepairCloseNotInherited
          ((BlockA.readerControlNext ring h p e p').tags
            (ring.rightNeighbor e))) := by
    rw [bankRepairClosePhiTarget ring p e hne]
    rcases bankRepairCloseRowCases (p e) (p (ring.rightNeighbor e)) with
      ⟨_, ty, _, _, hc, _, h2⟩ | ⟨_, nxt, _, _, _, hc, _, h2, _⟩ |
      ⟨_, _, _, _, hc, _, h2⟩ | ⟨ty, _, _, hc, _, h2⟩ |
      ⟨_, hy, hc, _, h2⟩ | ⟨_, _, hc, _⟩
    · rw [bankRepairCloseTagsTargetKept ring h p p' e hne (Or.inl hc), h2]
      exact ⟨fun _ _ => rfl, fun hall name => hall _ name⟩
    · rw [bankRepairCloseTagsTargetMove ring h p p' e hne hc, h2]
      exact ⟨fun _ _ => rfl, fun hall =>
        bankRepairCloseTransferNotInherited _ (fun name => hall e name) _⟩
    · rw [bankRepairCloseTagsTargetTerminal ring h p p' e hne hc]
      exact ⟨fun name hname => (by cases hname),
        fun _ name hname => (by cases hname)⟩
    · rw [bankRepairCloseTagsTargetKept ring h p p' e hne
        (Or.inr (Or.inl hc)), h2]
      exact ⟨fun _ _ => rfl, fun hall name => hall _ name⟩
    · rw [bankRepairCloseTagsTargetKept ring h p p' e hne
        (Or.inr (Or.inr hc)), h2]
      refine ⟨fun name hname => ?_, fun hall name => hall _ name⟩
      have := hI _ name hname
      rw [hy] at this
      cases this
    · have hl := bankRepairCloseTagsTargetLaunch ring h p p' e hne hc
      exact ⟨fun name hname => absurd hname (hl name), fun _ => hl⟩
  have hnoInh : (∀ (i name : Fin n), h.tags i ≠ .inherited name) →
      ∀ (i name : Fin n),
        (BlockA.readerControlNext ring h p e p').tags i ≠ .inherited name := by
    intro hall i name
    by_cases hie : i = e
    · rw [hie]
      exact hsrc name
    · by_cases hij : i = ring.rightNeighbor e
      · rw [hij]
        exact htarget.2 hall name
      · rw [bankRepairCloseTagsOther ring h p p' e i hie hij]
        exact hall i name
  refine ⟨?_, ?_, ?_⟩
  · intro i name hi
    by_cases hie : i = e
    · rw [hie] at hi
      exact absurd hi (hsrc name)
    · by_cases hij : i = ring.rightNeighbor e
      · rw [hij] at hi ⊢
        exact htarget.1 name hi
      · rw [bankRepairCloseTagsOther ring h p p' e i hie hij] at hi
        rw [bankRepairClosePhiOther ring p e i hie hij]
        exact hI i name hi
  · intro name
    exact bankRepairCloseNamesIff ring h p p' e name
  · intro hdone
    rcases (bankRepairClosePhaseDoneIff ring h p p' e).1 hdone with hold | hnone
    · exact hnoInh (hD hold)
    · intro i name hi
      have hname : (BlockA.readerControlNext ring h p e p').inheritedNames name =
          true := (bankRepairCloseNamesIff ring h p p' e name).2 ⟨i, hi⟩
      have hhas := (bankRepairCloseHasInheritedIff
        (BlockA.readerControlNext ring h p e p')).2 ⟨name, hname⟩
      rw [hnone] at hhas
      cases hhas

/-- The installed initializer at the W endpoint satisfies the tag
invariant.  Consumer: `bankRepairCloseTraceFacts`. -/
theorem bankRepairCloseTaggedInitial {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairCloseReaderTagged (piR z.val.1)
      (bankRepairReaderInitialControl ring hbank z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i name hi
    by_cases hs : (piR z.val.1 i).rawTok.isSome = true
    · exact hs
    · simp [bankRepairReaderInitialControl, hs] at hi
  · intro name
    constructor
    · intro hname
      refine ⟨name, ?_⟩
      have hs : (piR z.val.1 name).rawTok.isSome = true := hname
      simp [bankRepairReaderInitialControl, hs]
    · rintro ⟨i, hi⟩
      by_cases hs : (piR z.val.1 i).rawTok.isSome = true
      · simp [bankRepairReaderInitialControl, hs] at hi
        rw [← hi]
        exact hs
      · simp [bankRepairReaderInitialControl, hs] at hi
  · intro hdone
    cases hdone

/-! ## The coupled trace from a grant-free W endpoint -/

/-- A grant-free reference state disables every OLD FIRE.
Consumer: `bankRepairCloseTraceFacts`. -/
theorem bankRepairCloseNoFireOfDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedGrantDrain ring hbank z) (e : Fin n) :
    oldFire (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) = none := by
  have hg := hz.1.2
  simp [oldFire, fireSelect, hg e, hg (ring.rightNeighbor e)]

/-- Along every word from a grant-free W-accepted endpoint, the coupled
physical/reader trace stays grant-free, satisfies the tag invariant,
and is a genuine BlockA reader run of phiR.
Consumer: `bankRepairResidentRetirementClockOnDrain`. -/
theorem bankRepairCloseTraceFacts {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank start) :
    ∀ word : List (Fin n),
      BankPostInheritedGrantDrain ring hbank
          (bankRepairReaderResidentTrace ring hbank start word).1 ∧
      BankRepairCloseReaderTagged
          (piR (bankRepairReaderResidentTrace ring hbank start word).1.val.1)
          (bankRepairReaderResidentTrace ring hbank start word).2 ∧
      BlockA.Run ring (phiR ring)
        (BlockA.readerControlNext ring)
        (piR start.val.1)
        (.live (piR start.val.1)
          (bankRepairReaderInitialControl ring hbank start))
        word
        (piR (bankRepairReaderResidentTrace ring hbank start word).1.val.1)
        (.live (piR (bankRepairReaderResidentTrace
            ring hbank start word).1.val.1)
          (bankRepairReaderResidentTrace ring hbank start word).2) := by
  have hn2 : 2 ≤ n := by omega
  intro word
  suffices hk : ∀ (k : Nat) (w : List (Fin n)), w.length = k →
      BankPostInheritedGrantDrain ring hbank
          (bankRepairReaderResidentTrace ring hbank start w).1 ∧
      BankRepairCloseReaderTagged
          (piR (bankRepairReaderResidentTrace ring hbank start w).1.val.1)
          (bankRepairReaderResidentTrace ring hbank start w).2 ∧
      BlockA.Run ring (phiR ring)
        (BlockA.readerControlNext ring)
        (piR start.val.1)
        (.live (piR start.val.1)
          (bankRepairReaderInitialControl ring hbank start))
        w
        (piR (bankRepairReaderResidentTrace ring hbank start w).1.val.1)
        (.live (piR (bankRepairReaderResidentTrace
            ring hbank start w).1.val.1)
          (bankRepairReaderResidentTrace ring hbank start w).2) from
    hk word.length word rfl
  intro k
  induction k with
  | zero =>
      intro w hw
      have hnil : w = [] := List.eq_nil_of_length_eq_zero hw
      subst hnil
      exact ⟨hD, bankRepairCloseTaggedInitial ring hbank start, BlockA.Run.empty⟩
  | succ k ih =>
      intro w hw
      rcases List.eq_nil_or_concat w with hnil | ⟨w', b, hcat⟩
      · subst hnil
        simp at hw
      · rw [List.concat_eq_append] at hcat
        subst hcat
        have hlen : w'.length = k := by
          simp at hw
          omega
        obtain ⟨hD', hT, hR⟩ := ih w' hlen
        rw [bankRepairReaderResidentTraceSnoc]
        have hphi := bankRepairReaderPhiStepOfNoFire ring hn2 hbank
          (bankRepairReaderResidentTrace ring hbank start w').1 b
          (bankRepairCloseNoFireOfDrain ring hbank _ hD' b)
        refine ⟨?_, ?_, ?_⟩
        · exact bankPostInheritedGrantDrainClosed ring hn hbank _ hD' b
        · change BankRepairCloseReaderTagged
            (piR (bankRepairNext ring hbank
              (bankRepairReaderResidentTrace ring hbank start w').1 b).val.1)
            (BlockA.readerControlNext ring
              (bankRepairReaderResidentTrace ring hbank start w').2
              (piR (bankRepairReaderResidentTrace ring hbank start w').1.val.1) b
              (piR (bankRepairNext ring hbank
                (bankRepairReaderResidentTrace ring hbank start w').1 b).val.1))
          rw [hphi]
          exact bankRepairCloseTaggedStep ring hn2 _ _ _ b hT
        · change BlockA.Run ring (phiR ring)
            (BlockA.readerControlNext ring)
            (piR start.val.1)
            (.live (piR start.val.1)
              (bankRepairReaderInitialControl ring hbank start))
            (w' ++ [b])
            (piR (bankRepairNext ring hbank
              (bankRepairReaderResidentTrace ring hbank start w').1 b).val.1)
            (.live (piR (bankRepairNext ring hbank
                (bankRepairReaderResidentTrace ring hbank start w').1 b).val.1)
              (BlockA.readerControlNext ring
                (bankRepairReaderResidentTrace ring hbank start w').2
                (piR (bankRepairReaderResidentTrace ring hbank start w').1.val.1) b
                (piR (bankRepairNext ring hbank
                  (bankRepairReaderResidentTrace ring hbank start w').1 b).val.1)))
          rw [hphi]
          have hs := BlockA.Run.next hR b
          simpa [BlockA.update] using hs

/-! ## The one-step Bellman drift of the resident potential -/

/-- On the phiR successor the resident potential (inherited debt, plus
one final ticket when only the done mark is missing) has drift at least
one in the sum over all n edges: no edge raises it, and the outgoing
edge of an inherited reader lowers it.  Consumer:
`bankRepairResidentRetirementClockOnDrain`. -/
theorem bankRepairCloseDrift {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (hn2 : 2 ≤ n)
    (p : Fin n → ProjR c) (h : BlockA.ReaderControl n c)
    (q : Fin n → Fin n → ProjR c)
    (hT : BankRepairCloseReaderTagged p h)
    (hnd : h.phase ≠ .done) :
    1 + (List.ofFn (fun e : Fin n =>
        bankRepairReaderResidentPotential (phiR ring p e)
          (BlockA.readerControlNext ring h p e (q e)))).sum ≤
      n * bankRepairReaderResidentPotential p h := by
  obtain ⟨hI, hN, _⟩ := hT
  have hedge : ∀ e : Fin n,
      bankRepairReaderResidentPotential (phiR ring p e)
          (BlockA.readerControlNext ring h p e (q e)) ≤
        bankRepairReaderResidentTotal (phiR ring p e)
          (BlockA.readerControlNext ring h p e (q e)) := by
    intro e
    unfold bankRepairReaderResidentPotential
    by_cases hd : (BlockA.readerControlNext ring h p e (q e)).phase = .done
    · rw [if_pos hd]
      exact Nat.zero_le _
    · rw [if_neg hd]
      have hhas : Closure.readerHasInherited
          (BlockA.readerControlNext ring h p e (q e)) = true := by
        cases hb : Closure.readerHasInherited
            (BlockA.readerControlNext ring h p e (q e)) with
        | true => rfl
        | false =>
            exact absurd ((bankRepairClosePhaseDoneIff ring h p (q e) e).2
              (Or.inr hb)) hd
      rw [if_pos hhas]
      exact Nat.le_refl _
  unfold bankRepairReaderResidentPotential at ⊢
  rw [if_neg hnd]
  cases hhas : Closure.readerHasInherited h with
  | true =>
      rw [if_pos rfl]
      -- an inherited reader with its token: its outgoing edge pays
      obtain ⟨name, hname⟩ := (bankRepairCloseHasInheritedIff h).1 hhas
      obtain ⟨e0, he0⟩ := (hN name).1 hname
      have hsome := hI e0 name he0
      obtain ⟨src, hsrc⟩ : ∃ src, (p e0).rawTok = some src := by
        cases hp : (p e0).rawTok with
        | none => rw [hp] at hsome; cases hsome
        | some src => exact ⟨src, rfl⟩
      have hF : ∀ e : Fin n,
          (fun e : Fin n =>
            bankRepairReaderResidentPotential (phiR ring p e)
                (BlockA.readerControlNext ring h p e (q e)) +
              (if e = e0 then 1 else 0)) e ≤
            (fun _ : Fin n => bankRepairReaderResidentTotal p h) e := by
        intro e
        dsimp only
        have hstep := bankRepairCloseTotalStep ring h p (q e) e
          (clockNeighborDifferent ring hn2 e)
        have he := hedge e
        by_cases hee : e = e0
        · rw [if_pos hee]
          subst hee
          have := hstep.2 name src he0 hsrc
          omega
        · rw [if_neg hee]
          have := hstep.1
          omega
      have hsum := ofFn_sum_le _ _ hF
      rw [ofFn_sum_add, bankRepairCloseSumIndicator, ofFn_sum_const] at hsum
      have hfold : (List.ofFn (fun e : Fin n =>
          bankRepairReaderResidentPotential (phiR ring p e)
            (BlockA.readerControlNext ring h p e (q e)))).sum + 1 ≤
          n * bankRepairReaderResidentTotal p h := hsum
      unfold bankRepairReaderResidentPotential at hfold
      omega
  | false =>
      rw [if_neg (by decide)]
      -- no inherited tag: every edge marks the reader done
      have hnone : ∀ (i name : Fin n), h.tags i ≠ .inherited name := by
        intro i name hi
        have hname := (hN name).2 ⟨i, hi⟩
        have := (bankRepairCloseHasInheritedIff h).2 ⟨name, hname⟩
        rw [hhas] at this
        cases this
      have hzero : ∀ e : Fin n,
          bankRepairReaderResidentPotential (phiR ring p e)
              (BlockA.readerControlNext ring h p e (q e)) = 0 := by
        intro e
        have hT' := bankRepairCloseTaggedStep ring hn2 h p (q e) e
          ⟨hI, hN, fun hd => absurd hd hnd⟩
        have hnext : Closure.readerHasInherited
            (BlockA.readerControlNext ring h p e (q e)) = false := by
          cases hb : Closure.readerHasInherited
              (BlockA.readerControlNext ring h p e (q e)) with
          | false => rfl
          | true =>
              exfalso
              obtain ⟨name, hname⟩ := (bankRepairCloseHasInheritedIff _).1 hb
              obtain ⟨i, hi⟩ := (hT'.2.1 name).1 hname
              -- the next tags are not inherited when no OLD tag was
              have hne := clockNeighborDifferent ring hn2 e
              have hsrc := bankRepairCloseSourceNotInherited ring h p (q e) e hI
              by_cases hie : i = e
              · rw [hie] at hi
                exact hsrc name hi
              · by_cases hij : i = ring.rightNeighbor e
                · rw [hij] at hi
                  rcases bankRepairCloseRowCases (p e) (p (ring.rightNeighbor e)) with
                    ⟨_, _, _, _, hc, _, _⟩ | ⟨_, _, _, _, _, hc, _, _, _⟩ |
                    ⟨_, _, _, _, hc, _, _⟩ | ⟨_, _, _, hc, _, _⟩ |
                    ⟨_, _, hc, _, _⟩ | ⟨_, _, hc, _⟩
                  · rw [bankRepairCloseTagsTargetKept ring h p (q e) e hne
                      (Or.inl hc)] at hi
                    exact hnone _ name hi
                  · rw [bankRepairCloseTagsTargetMove ring h p (q e) e hne hc] at hi
                    exact bankRepairCloseTransferNotInherited _
                      (fun m => hnone e m) _ name hi
                  · rw [bankRepairCloseTagsTargetTerminal ring h p (q e) e hne hc] at hi
                    cases hi
                  · rw [bankRepairCloseTagsTargetKept ring h p (q e) e hne
                      (Or.inr (Or.inl hc))] at hi
                    exact hnone _ name hi
                  · rw [bankRepairCloseTagsTargetKept ring h p (q e) e hne
                      (Or.inr (Or.inr hc))] at hi
                    exact hnone _ name hi
                  · exact bankRepairCloseTagsTargetLaunch ring h p (q e) e hne hc
                      name hi
                · rw [bankRepairCloseTagsOther ring h p (q e) e i hie hij] at hi
                  exact hnone i name hi
        have hdone := (bankRepairClosePhaseDoneIff ring h p (q e) e).2 (Or.inr hnext)
        unfold bankRepairReaderResidentPotential
        rw [if_pos hdone]
      have hsum : (List.ofFn (fun e : Fin n =>
          bankRepairReaderResidentPotential (phiR ring p e)
            (BlockA.readerControlNext ring h p e (q e)))).sum = 0 := by
        rw [ofFn_sum_eq _ (fun _ => 0) hzero, ofFn_sum_const]
        simp
      unfold bankRepairReaderResidentPotential at hsum
      omega

/-! ## The retirement clock on the grant-free class -/

/-- Word-carrier comparison for the retirement target (copy of the
private comparison in BankRepairReader.lean).  Consumer:
`bankRepairResidentRetirementClockOnDrain`. -/
private theorem bankRepairCloseWordCostLe {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (Q : List (Fin n) → Prop)
    (hQP : ∀ word : List (Fin n), Q word →
      BankRepairReaderRetiredFrom ring hbank start
        (word.foldl (bankRepairNext ring hbank) start))
    (word : List (Fin n)) (T : Nat) :
    costNumerator (bankRepairNext ring hbank)
      (BankRepairReaderRetiredFrom ring hbank start)
      (word.foldl (bankRepairNext ring hbank) start) T ≤
    costNumerator
      (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
      Q word T := by
  classical
  induction T generalizing word with
  | zero =>
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      by_cases hp : BankRepairReaderRetiredFrom
          ring hbank start
          (word.foldl (bankRepairNext ring hbank) start)
      · rw [costNumerator_terminal
          (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          (word.foldl (bankRepairNext ring hbank) start)
          hp (T + 1)]
        exact Nat.zero_le _
      · have hq : ¬ Q word := by
          intro h
          exact hp (hQP word h)
        rw [costNumerator_succ
          (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          (word.foldl (bankRepairNext ring hbank) start)
          hp T]
        rw [costNumerator_succ
          (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
          Q word hq T]
        have hsum := ofFn_sum_le
          (fun e : Fin n =>
            costNumerator (bankRepairNext ring hbank)
              (BankRepairReaderRetiredFrom ring hbank start)
              (bankRepairNext ring hbank
                (word.foldl (bankRepairNext ring hbank) start) e) T)
          (fun e : Fin n =>
            costNumerator
              (fun (w : List (Fin n)) (f : Fin n) => w ++ [f])
              Q (word ++ [e]) T)
          (fun e => by
            have h := ih (word ++ [e])
            simpa only [List.foldl_append, List.foldl_cons,
              List.foldl_nil] using h)
        exact Nat.add_le_add_left hsum (n ^ (T + 1))

/-- A done reader on the coupled trace certifies the retirement target.
Consumer: `bankRepairResidentRetirementClockOnDrain`. -/
theorem bankRepairCloseDoneCertifies {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank start)
    (hW : BankRepairWAccepted ring hbank start)
    (word : List (Fin n))
    (hdone : bankRepairReaderResidentWordDone ring hbank start word) :
    BankRepairReaderRetiredFrom ring hbank start
      (word.foldl (bankRepairNext ring hbank) start) := by
  obtain ⟨_, hT, hrun⟩ := bankRepairCloseTraceFacts ring hn hbank start hD word
  have hphysical := bankRepairReaderResidentTracePhysical
    ring hbank start word
  rw [hphysical] at hrun
  have hd : (bankRepairReaderResidentTrace
      ring hbank start word).2.phase = .done := hdone
  have hnames : ∀ name : Fin n,
      (bankRepairReaderResidentTrace ring hbank start word).2.inheritedNames
        name = false := by
    intro name
    cases hb : (bankRepairReaderResidentTrace ring hbank start word).2.inheritedNames
        name with
    | false => rfl
    | true =>
        obtain ⟨i, hi⟩ := (hT.2.1 name).1 hb
        exact absurd hi (hT.2.2 hd i name)
  exact ⟨word,
    .live (piR start.val.1)
      (bankRepairReaderInitialControl ring hbank start),
    (bankRepairReaderResidentTrace ring hbank start word).2,
    rfl,
    bankRepairReaderInitializesAtW ring hbank start hW,
    hrun, hd, hnames⟩

/-- R10b resident-retirement clock (paper lem:e-readers, E.G19) at its
exact t n² budget, for every W-accepted start in the grant-free
post-inherited class in which the repair runs.  This is the installed
`BankRepairResidentRetirementClock` restricted to that class (the
unrestricted class lacks the no-FIRE premise; see the module header).
Consumer: the R stage of the BANK repair, `bankRepairReaderStage...`
once restated on the grant-free class. -/
theorem bankRepairResidentRetirementClockOnDrain {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ start : BankReferenceState ring hbank,
      BankPostInheritedGrantDrain ring hbank start →
      BankRepairWAccepted ring hbank start →
      ∀ T : Nat,
        2 * costNumerator
          (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          start T ≤
        n ^ T * ((2 * ceilLogTwo (ceilLogTwo n)) * n ^ 2) := by
  intro start hD hW T
  have hn2 : 2 ≤ n := by omega
  have hdrift : ∀ word : List (Fin n),
      ¬ bankRepairReaderResidentWordDone ring hbank start word →
      1 + (List.ofFn (fun e : Fin n =>
        bankRepairReaderResidentWordDebt ring hbank start
          (word ++ [e]))).sum ≤
        n * bankRepairReaderResidentWordDebt ring hbank start word := by
    intro word hnot
    obtain ⟨hDw, hTw, _⟩ := bankRepairCloseTraceFacts ring hn hbank start hD word
    have hsum : (List.ofFn (fun e : Fin n =>
        bankRepairReaderResidentWordDebt ring hbank start (word ++ [e]))) =
        List.ofFn (fun e : Fin n =>
          bankRepairReaderResidentPotential
            (phiR ring (piR (bankRepairReaderResidentTrace
              ring hbank start word).1.val.1) e)
            (BlockA.readerControlNext ring
              (bankRepairReaderResidentTrace ring hbank start word).2
              (piR (bankRepairReaderResidentTrace ring hbank start word).1.val.1) e
              (piR (bankRepairNext ring hbank
                (bankRepairReaderResidentTrace ring hbank start word).1 e).val.1))) := by
      congr 1
      funext e
      unfold bankRepairReaderResidentWordDebt
      rw [bankRepairReaderResidentTraceSnoc]
      have hphi := bankRepairReaderPhiStepOfNoFire ring hn2 hbank
        (bankRepairReaderResidentTrace ring hbank start word).1 e
        (bankRepairCloseNoFireOfDrain ring hbank _ hDw e)
      change bankRepairReaderResidentPotential
          (piR (bankRepairNext ring hbank
            (bankRepairReaderResidentTrace ring hbank start word).1 e).val.1)
          (BlockA.readerControlNext ring
            (bankRepairReaderResidentTrace ring hbank start word).2
            (piR (bankRepairReaderResidentTrace ring hbank start word).1.val.1) e
            (piR (bankRepairNext ring hbank
              (bankRepairReaderResidentTrace ring hbank start word).1 e).val.1)) = _
      rw [hphi]
    rw [hsum]
    exact bankRepairCloseDrift ring hn2 _ _
      (fun e => piR (bankRepairNext ring hbank
        (bankRepairReaderResidentTrace ring hbank start word).1 e).val.1)
      hTw hnot
  have hscaled :
      ∀ word : List (Fin n),
        ¬ bankRepairReaderResidentWordDone
          ring hbank start word →
        n + (List.ofFn (fun e : Fin n =>
          n * bankRepairReaderResidentWordDebt
            ring hbank start (word ++ [e]))).sum ≤
        n * (n * bankRepairReaderResidentWordDebt
          ring hbank start word) := by
    intro word hnot
    have hbase := hdrift word hnot
    have hm := Nat.mul_le_mul_left n hbase
    calc
      n + (List.ofFn (fun e : Fin n =>
          n * bankRepairReaderResidentWordDebt
            ring hbank start (word ++ [e]))).sum =
        n * (1 + (List.ofFn (fun e : Fin n =>
          bankRepairReaderResidentWordDebt
            ring hbank start (word ++ [e]))).sum) := by
          simp only [ofFn_sum_mul_left, Nat.mul_add, Nat.mul_one]
      _ ≤ n * (n * bankRepairReaderResidentWordDebt
          ring hbank start word) := hm
  have hword := Prob.costNumerator_le_of_potential
    (fun (word : List (Fin n)) (e : Fin n) => word ++ [e])
    (bankRepairReaderResidentWordDone ring hbank start)
    (fun word => n * bankRepairReaderResidentWordDebt
      ring hbank start word) hscaled
  have hcap :
      bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        n * ceilLogTwo (ceilLogTwo n) := by
    have hc := bankRepairReaderResidentPotentialCap
      (piR start.val.1)
      (bankRepairReaderInitialControl ring hbank start)
      ring.hn (bankRepairReaderCompiledWidthPos hbank)
    change
      bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        n * (compileAdvice (ceilLogTwo n)).t at hc
    rw [bankRepairReaderCompiledWidth hbank] at hc
    exact hc
  have hbound :
      n * bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        ceilLogTwo (ceilLogTwo n) * n ^ 2 := by
    calc
      n * bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        n * (n * ceilLogTwo (ceilLogTwo n)) :=
          Nat.mul_le_mul_left n hcap
      _ = ceilLogTwo (ceilLogTwo n) * n ^ 2 := by
        rw [Nat.pow_two]
        ac_rfl
  have hphysical := bankRepairCloseWordCostLe
    ring hbank start
    (bankRepairReaderResidentWordDone ring hbank start)
    (fun word hdone =>
      bankRepairCloseDoneCertifies
        ring hn hbank start hD hW word hdone) [] T
  have hcost :
      costNumerator (bankRepairNext ring hbank)
        (BankRepairReaderRetiredFrom ring hbank start)
        start T ≤
      n ^ T * (ceilLogTwo (ceilLogTwo n) * n ^ 2) := by
    calc
      costNumerator (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          start T ≤
        costNumerator
          (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
          (bankRepairReaderResidentWordDone ring hbank start)
          [] T := hphysical
      _ ≤ n ^ T * (n * bankRepairReaderResidentWordDebt
          ring hbank start []) := hword [] T
      _ ≤ n ^ T * (ceilLogTwo (ceilLogTwo n) * n ^ 2) :=
          Nat.mul_le_mul_left (n ^ T) hbound
  have hdouble := Nat.mul_le_mul_left 2 hcost
  calc
    2 * costNumerator (bankRepairNext ring hbank)
        (BankRepairReaderRetiredFrom ring hbank start)
        start T ≤
      2 * (n ^ T * (ceilLogTwo (ceilLogTwo n) * n ^ 2)) :=
        hdouble
    _ = n ^ T *
        ((2 * ceilLogTwo (ceilLogTwo n)) * n ^ 2) := by
      ac_rfl

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairClosePairDebt
#print axioms L3.RenewalReferenceClock.bankRepairCloseTotalStep
#print axioms L3.RenewalReferenceClock.bankRepairCloseTaggedStep
#print axioms L3.RenewalReferenceClock.bankRepairCloseTraceFacts
#print axioms L3.RenewalReferenceClock.bankRepairCloseDrift
#print axioms L3.RenewalReferenceClock.bankRepairCloseDoneCertifies
#print axioms L3.RenewalReferenceClock.bankRepairResidentRetirementClockOnDrain

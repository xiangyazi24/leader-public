import Leader.L3.Width.DigitComparisonValuesChain
import Leader.L3.Width.DigitCuts

/-!
# R10c digit values: every recorded writer terminal carries a carry chain

Along the audit fold `widthDigitAuditNext` from a drained start, every writer carry of the physical
D projection is mirrored by a ghost carry whose ledger (when not inherited) is a `CarryChain`; hence
the ledger of every recorded writer terminal with no inherited carry stores the successor of its
consumed string modulo `topA ^ length`.

This is ledger arithmetic.  It is *not* a statement about the physical digits: whether the stored
digit survives the dirty gate, whether the sampled input was settled, and whether a later edge
overwrites the cell are separate facts (see the notes).

Consumer: the writer-terminal value of `DigitValuesCorrect` at a writer comparison cut.
-/

namespace L3

open L3.WidthDigit

set_option autoImplicit false

section Fold

variable {c : Compiled} {n : Nat}

/-- The initial ghost satisfies the carry invariant (live carries are inherited).

Consumer: `auditCarryInv_initial`. -/
theorem carryAll_initial (S : Fin n → ProjD c) : CarryAll S (digitGhostInitial S) := by
  intro i
  cases hw : (S i).top.wCarry with
  | OFF =>
    simp [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hw,
      WCarry.isW, CarryInv]
  | W cc =>
    simp only [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hw,
      WCarry.isW, CarryInv, if_true]
    exact ⟨_, rfl, fun h => by simp at h⟩

/-- The audit invariant: the current ghost mirrors the physical carry, and every frame was taken at
such a state and holds the exact `digitService` receipt.

Consumer: `auditCarryInv_step`, `writerTerminalChain`. -/
def AuditCarryInv (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  CarryAll S A.current ∧
    ∀ f ∈ A.frames, CarryAll f.old f.oldGhost ∧
      f.receipt = digitService f.time f.edge (ring.rightNeighbor f.edge) (f.old f.edge)
        (f.old (ring.rightNeighbor f.edge)) (f.oldGhost f.edge)
        (f.oldGhost (ring.rightNeighbor f.edge))

/-- Consumer: `auditCarryInv_fold`. -/
theorem auditCarryInv_initial (ring : DirectedRing n) (S : Fin n → ProjD c) :
    AuditCarryInv ring S (digitAuditInitial S) :=
  ⟨carryAll_initial S, fun f hf => by simp [digitAuditInitial] at hf⟩

/-- Consumer: `auditCarryInv_fold`. -/
theorem auditCarryInv_step (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (h : AuditCarryInv ring S A) :
    AuditCarryInv ring (phiD ring S e) (digitAuditStep ring S A e) := by
  refine ⟨carryAll_step ring S A.current (A.clock + 1) e h.1, ?_⟩
  intro f hf
  simp only [digitAuditStep, List.mem_cons] at hf
  rcases hf with hf | hf
  · subst hf
    exact ⟨h.1, rfl⟩
  · exact h.2 f hf

/-- **The invariant holds along the audit fold from a drained start.**

Consumer: `writerLedgerChainOfFold`. -/
theorem auditCarryInv_fold {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (w : List (Fin n)) :
    ∀ p : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ref.drained p.1 → AuditCarryInv ring (piD (ref.phys p.1)) p.2 →
      ref.drained (w.foldl (widthDigitAuditNext ref) p).1 ∧
        AuditCarryInv ring (piD (ref.phys (w.foldl (widthDigitAuditNext ref) p).1))
          (w.foldl (widthDigitAuditNext ref) p).2 := by
  induction w with
  | nil => intro p hd hi; exact ⟨hd, hi⟩
  | cons e w ih =>
    intro p hd hi
    have hnext : widthDigitAuditNext ref p e =
        (ref.next p.1 e, digitAuditStep ring (piD (ref.phys p.1)) p.2 e) := rfl
    simp only [List.foldl_cons]
    apply ih
    · rw [hnext]; exact ref.drainedClosed p.1 hd e
    · rw [hnext]
      show AuditCarryInv ring (piD (ref.phys (ref.next p.1 e))) _
      rw [ref.digitStep p.1 hd e]
      exact auditCarryInv_step ring _ _ e hi

end Fold

section Terminal

variable {c : Compiled} {n : Nat}

/-- A replay terminal is the live carry of the source with its ledger.

Consumer: `writerTerminalChain`. -/
theorem replay_terminal_ledger (lane : DigitLane) (time : Nat) (source dest : Fin n)
    (xv yv : DigitLaneView c) (gx gy : DigitLaneGhost c n) (t : DigitTerminal c n)
    (h : (digitLaneReplay lane time source dest xv yv gx gy).terminal = some t) :
    xv.carryLive = true ∧ t.ledger = gx.carry ∧ t.carryBit = xv.carryBit := by
  simp only [digitLaneReplay] at h
  by_cases hc : (!(xv.leader || yv.leader) && xv.carryLive && (yv.leader || yv.marker)) = true
  · rw [if_pos hc] at h
    have ht := Option.some.inj h
    subst ht
    refine ⟨?_, rfl, rfl⟩
    have hc' : ((xv.leader = false ∧ yv.leader = false) ∧ xv.carryLive = true) ∧
        (yv.leader = true ∨ yv.marker = true) := by simpa using hc
    exact hc'.1.2
  · rw [if_neg hc] at h
    exact absurd h (by simp)

/-- **Every recorded writer terminal without inherited carry carries a carry chain ending in the
terminal carry bit.**

Consumer: `writerTerminalValue`. -/
theorem writerTerminalChain {ring : DirectedRing n} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hinv : AuditCarryInv ring S A) (t : DigitTerminal c n)
    (hrec : DigitRecordedTerminal A t) (hlane : t.lane = .writer)
    (L : DigitCarryGhost c n) (hL : t.ledger = some L) (hinh : L.inherited = none) :
    CarryChain c.topA t.carryBit L.uses := by
  obtain ⟨f, hf, _, _, hterm⟩ := hrec
  obtain ⟨hall, hrcpt⟩ := hinv.2 f hf
  rw [hlane, hrcpt] at hterm
  have hrep := replay_terminal_ledger .writer f.time f.edge (ring.rightNeighbor f.edge) _ _ _ _ t
    hterm
  obtain ⟨hlive, hled, hbit⟩ := hrep
  have hx := hall f.edge
  revert hlive hled hbit
  cases hw : (f.old f.edge).top.wCarry with
  | OFF =>
    intro hlive
    simp [digitLaneView, hw, WCarry.isW] at hlive
  | W cc =>
    intro _ hled hbit
    rw [hw] at hx
    obtain ⟨L', hL', hch⟩ := hx
    have hLL : L' = L := by
      have := hL.symm.trans hled
      rw [hL'] at this
      exact (Option.some.inj this).symm
    subst hLL
    have hcc : t.carryBit = cc := by
      rw [hbit]; simp [digitLaneView, hw, wcC]
    rw [hcc]
    exact hch hinh

/-- **The stored string of a recorded writer terminal is the successor of the consumed string,
modulo `topA ^ length`** (ledger arithmetic only).

Consumer: `WidthDigitComparisonValues` (writer value step). -/
theorem writerTerminalValue {ring : DirectedRing n} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hinv : AuditCarryInv ring S A) (t : DigitTerminal c n)
    (hrec : DigitRecordedTerminal A t) (hlane : t.lane = .writer)
    (L : DigitCarryGhost c n) (hL : t.ledger = some L) (hinh : L.inherited = none) :
    digitsVal c.topA (ledgerOut L.uses) L.uses.length =
      (digitsVal c.topA (ledgerIn L.uses) L.uses.length + 1) % c.topA ^ L.uses.length :=
  carryChain_mod (writerTerminalChain hinv t hrec hlane L hL hinh)

end Terminal

section Reference

variable {n : Nat} {ring : DirectedRing n}

/-- **Along the audit fold from a drained start, every recorded writer terminal without inherited
carry stores the successor of its consumed string.**

Consumer: the writer comparison cut (`WidthWriterComparisonCut.audit`). -/
theorem writerLedgerValueOfFold (ref : WidthDigitReference ring) (start : ref.State)
    (hd : ref.drained start) (w : List (Fin n))
    (t : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hrec : DigitRecordedTerminal
      (w.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2 t)
    (hlane : t.lane = .writer) (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hL : t.ledger = some L) (hinh : L.inherited = none) :
    digitsVal (compileAdvice (ceilLogTwo n)).topA (ledgerOut L.uses) L.uses.length =
      (digitsVal (compileAdvice (ceilLogTwo n)).topA (ledgerIn L.uses) L.uses.length + 1) %
        (compileAdvice (ceilLogTwo n)).topA ^ L.uses.length :=
  writerTerminalValue
    (auditCarryInv_fold ref w (start, digitAuditInitial (piD (ref.phys start))) hd
      (auditCarryInv_initial ring _)).2 t hrec hlane L hL hinh

end Reference

end L3

#print axioms L3.writerLedgerValueOfFold

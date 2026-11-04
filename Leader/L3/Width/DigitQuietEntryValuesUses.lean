import Leader.L3.Width.DigitQuietEntryValuesRows
import Leader.L3.Width.DigitWriterCurrentWrites

/-!
# A writer use leaves its target cell with an empty input

Every use of a writer ledger has a frame at its time whose new state holds an empty writer input at
the target of the use.  The argument is the one of `usesFramed_step` (`usesPair`), with the input
rows `liveTop_advance_in`, `liveTop_launch_in`.

Consumer: `L3.QuietEntryValues.useClean` (WidthDigitQuietEntryValuesStep): from that state on the
dirty invariant holds at the target cell, so the next use of the cell is clean.

Paper: research/lean-l3/ledgers/R10c-qdigit-notes.md section 9.
-/

namespace L3

open L3.DigitQuiet

set_option autoImplicit false

section Writes

variable {c : Compiled} {n : Nat}

/-- **The use has a frame at its time leaving its target with an empty writer input.**  Consumer:
`UsesEmptied`. -/
def UseEmpties (ring : DirectedRing n) (A : DigitAudit c n) (u : DigitUse c n) : Prop :=
  ∃ f ∈ A.frames, f.time = u.time ∧ (∃ (v : Fin c.topA) (T : Bool), (f.old u.target).top.wIn = .S v T) ∧
    (phiD ring f.old f.edge u.target).top.wIn = .E

/-- **Every use of every writer ledger of the current ghost and of the old ghost of every frame has
such a frame.**  Consumer: `usesEmptied_step`, `usesEmptied_fold`. -/
def UsesEmptied (ring : DirectedRing n) (A : DigitAudit c n) : Prop :=
  (∀ i L, (A.current i).writer.carry = some L → ∀ u ∈ L.uses, UseEmpties ring A u) ∧
  (∀ f ∈ A.frames, ∀ i L, (f.oldGhost i).writer.carry = some L → ∀ u ∈ L.uses,
    UseEmpties ring A u)

/-- Consumer: `usesEmptied_step`. -/
theorem useEmpties_mono (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (u : DigitUse c n) (h : UseEmpties ring A u) :
    UseEmpties ring (digitAuditStep ring S A e) u := by
  obtain ⟨f, hf, h1, h2, h3⟩ := h
  exact ⟨f, List.mem_cons_of_mem _ hf, h1, h2, h3⟩

/-- **One audit letter preserves `UsesEmptied`.**

Consumer: `usesEmptied_fold`. -/
theorem usesEmptied_step (ring : DirectedRing n) (hn2 : 2 ≤ n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (h : UsesEmptied ring A) :
    UsesEmptied ring (digitAuditStep ring S A e) := by
  have hne := rightNeighbor_ne ring hn2 e
  obtain ⟨f0, hf0, hf0t, hf0e, hf0o⟩ : ∃ f : DigitFrame c n,
      f ∈ (digitAuditStep ring S A e).frames ∧ f.time = A.clock + 1 ∧ f.edge = e ∧
        f.old = S := ⟨_, List.mem_cons_self .., rfl, rfl, rfl⟩
  have hxP : ∀ L, (A.current e).writer.carry = some L → ∀ u ∈ L.uses,
      UseEmpties ring (digitAuditStep ring S A e) u :=
    fun L hL u hu => useEmpties_mono ring S A e u (h.1 e L hL u hu)
  have hyP : ∀ L, (A.current (ring.rightNeighbor e)).writer.carry = some L → ∀ u ∈ L.uses,
      UseEmpties ring (digitAuditStep ring S A e) u :=
    fun L hL u hu => useEmpties_mono ring S A e u (h.1 _ L hL u hu)
  have key := usesPair DigitLane.writer (A.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
    (digitLaneView .writer (S (ring.rightNeighbor e))
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
    (A.current e).writer (A.current (ring.rightNeighbor e)).writer
    (UseEmpties ring (digitAuditStep ring S A e)) hxP hyP
    (by
      intro h1 h2 h3 h4 h5 h6
      have hxl : (S e).word.native.l = false := h1
      have hyl : (S (ring.rightNeighbor e)).word.native.l = false := h2
      have hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta = false := h4
      have hxc : (S e).top.wCarry.isW = true := h3
      have hyc : (S (ring.rightNeighbor e)).top.wCarry.isW = false := h5
      have his : (S (ring.rightNeighbor e)).top.wIn.isS = true := h6
      obtain ⟨cc, hw⟩ : ∃ cc, (S e).top.wCarry = .W cc := by
        cases hh : (S e).top.wCarry with
        | OFF => rw [hh] at hxc; simp [WCarry.isW] at hxc
        | W cc => exact ⟨cc, rfl⟩
      have hoff : (S (ring.rightNeighbor e)).top.wCarry = .OFF := by
        cases hh : (S (ring.rightNeighbor e)).top.wCarry with
        | OFF => rfl
        | W _ => rw [hh] at hyc; simp [WCarry.isW] at hyc
      obtain ⟨v, T, hs⟩ : ∃ v T, (S (ring.rightNeighbor e)).top.wIn = .S v T := by
        cases hI : (S (ring.rightNeighbor e)).top.wIn with
        | S v T => exact ⟨v, T, rfl⟩
        | E => rw [hI] at his; simp [InTok.isS] at his
        | X => rw [hI] at his; simp [InTok.isS] at his
        | P v T => rw [hI] at his; simp [InTok.isS] at his
      have hv : inV c (S (ring.rightNeighbor e)).top.wIn = v := by rw [hs]; rfl
      have hcb : wcC (S e).top.wCarry = cc := by rw [hw]; rfl
      refine ⟨f0, hf0, hf0t, ⟨v, T, by rw [hf0o]; exact hs⟩, ?_⟩
      show (phiD ring f0.old f0.edge (ring.rightNeighbor e)).top.wIn = .E
      rw [hf0e, hf0o, phiD_at_right ring S e hne]
      exact liveTop_advance_in c _ _ _ _ cc v T hxl hyl hbY hw hoff hs)
    (by
      intro h1 h2 h3 h4 h5
      have hxl : (S e).word.native.l = false := h1
      have hyl : (S (ring.rightNeighbor e)).word.native.l = false := h2
      have hxc : (S e).top.wCarry.isW = false := h3
      have hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = true := h4
      have his : (S e).top.wIn.isS = true := h5
      have hw : (S e).top.wCarry = .OFF := by
        cases hh : (S e).top.wCarry with
        | OFF => rfl
        | W _ => rw [hh] at hxc; simp [WCarry.isW] at hxc
      obtain ⟨v, T, hs⟩ : ∃ v T, (S e).top.wIn = .S v T := by
        cases hI : (S e).top.wIn with
        | S v T => exact ⟨v, T, rfl⟩
        | E => rw [hI] at his; simp [InTok.isS] at his
        | X => rw [hI] at his; simp [InTok.isS] at his
        | P v T => rw [hI] at his; simp [InTok.isS] at his
      have hv : inV c (S e).top.wIn = v := by rw [hs]; rfl
      refine ⟨f0, hf0, hf0t, ⟨v, T, by rw [hf0o]; exact hs⟩, ?_⟩
      show (phiD ring f0.old f0.edge e).top.wIn = .E
      rw [hf0e, hf0o, phiD_at_left]
      exact liveTop_launch_in c _ _ _ _ v T hxl hyl hbX hw hs)
  refine ⟨?_, ?_⟩
  · intro i L hL u hu
    by_cases hie : i = e
    · subst hie
      have hL' : (digitLaneReplay DigitLane.writer (A.clock + 1) i (ring.rightNeighbor i)
          (digitLaneView .writer (S i) (workerW (S i).word (S (ring.rightNeighbor i)).word).betaX)
          (digitLaneView .writer (S (ring.rightNeighbor i))
            (workerW (S i).word (S (ring.rightNeighbor i)).word).betaY)
          (A.current i).writer (A.current (ring.rightNeighbor i)).writer).x.carry = some L := by
        simpa [digitAuditStep, digitGhostStep, digitService] using hL
      exact key.1 L hL' u hu
    · by_cases hij : i = ring.rightNeighbor e
      · subst hij
        have hL' : (digitLaneReplay DigitLane.writer (A.clock + 1) e (ring.rightNeighbor e)
            (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
            (digitLaneView .writer (S (ring.rightNeighbor e))
              (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
            (A.current e).writer (A.current (ring.rightNeighbor e)).writer).y.carry = some L := by
          simpa [digitAuditStep, digitGhostStep, digitService, hie] using hL
        exact key.2 L hL' u hu
      · have hL' : (A.current i).writer.carry = some L := by
          simpa [digitAuditStep, digitGhostStep, hie, hij] using hL
        exact useEmpties_mono ring S A e u (h.1 i L hL' u hu)
  · intro f hf i L hL u hu
    simp only [digitAuditStep, List.mem_cons] at hf
    rcases hf with hf | hf
    · subst hf
      exact useEmpties_mono ring S A e u (h.1 i L hL u hu)
    · exact useEmpties_mono ring S A e u (h.2 f hf i L hL u hu)

/-- Consumer: `usesEmptied_fold`. -/
theorem usesEmptied_initial (ring : DirectedRing n) (S : Fin n → ProjD c) :
    UsesEmptied ring (digitAuditInitial S) := by
  refine ⟨?_, fun f hf => by simp [digitAuditInitial] at hf⟩
  intro i L hL u hu
  by_cases hlive : (S i).top.wCarry.isW = true
  · simp [digitAuditInitial, digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial,
      digitLaneView, hlive] at hL
    rw [← hL] at hu
    simp at hu
  · simp [digitAuditInitial, digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial,
      digitLaneView, hlive] at hL

end Writes

section Fold

open L3.WidthDigit

variable {n : Nat} {ring : DirectedRing n}

/-- **`UsesEmptied` along the audit fold of a drained start.**

Consumer: `terminalUsesEmptied`. -/
theorem usesEmptied_fold (ref : WidthDigitReference ring) (hn2 : 2 ≤ n) (w : List (Fin n)) :
    ∀ p : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ref.drained p.1 → UsesEmptied ring p.2 →
      ref.drained (w.foldl (widthDigitAuditNext ref) p).1 ∧
        UsesEmptied ring (w.foldl (widthDigitAuditNext ref) p).2 := by
  induction w with
  | nil => intro p hd hi; exact ⟨hd, hi⟩
  | cons e w ih =>
    intro p hd hi
    simp only [List.foldl_cons]
    exact ih (widthDigitAuditNext ref p e) (ref.drainedClosed p.1 hd e)
      (usesEmptied_step ring hn2 (piD (ref.phys p.1)) p.2 e hi)

/-- **Every use of the ledger of a recorded writer terminal has a frame leaving its target empty**, on the audit fold of
a drained start.

Consumer: `L3.QuietEntryValues.useClean`. -/
theorem terminalUsesEmptied (ref : WidthDigitReference ring) (hn2 : 2 ≤ n) (start : ref.State)
    (hd : ref.drained start) (w : List (Fin n))
    (t : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hrec : DigitRecordedTerminal
      (w.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2 t)
    (hlane : t.lane = .writer) (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hL : t.ledger = some L) :
    ∀ u ∈ L.uses, UseEmpties ring
      (w.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2 u := by
  have hU := (usesEmptied_fold ref hn2 w (start, digitAuditInitial (piD (ref.phys start))) hd
    (usesEmptied_initial ring _)).2
  obtain ⟨f, hf, -, -, hterm⟩ := hrec
  rw [hlane] at hterm
  have hrcpt := (auditCarryInv_fold ref w (start, digitAuditInitial (piD (ref.phys start))) hd
    (auditCarryInv_initial ring _)).2.2 f hf |>.2
  rw [hrcpt] at hterm
  have hrep := replay_terminal_ledger .writer f.time f.edge (ring.rightNeighbor f.edge) _ _ _ _ t
    hterm
  obtain ⟨-, hled, -⟩ := hrep
  have hg : (f.oldGhost f.edge).writer.carry = some L := by
    rw [← hled]; exact hL
  intro u hu
  exact hU.2 f hf f.edge L hg u hu

end Fold

end L3

#print axioms L3.usesEmptied_step
#print axioms L3.terminalUsesEmptied

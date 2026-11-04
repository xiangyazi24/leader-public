import Leader.L3.Width.DigitWriterCurrentUses
import Leader.L3.Width.DigitComparisonValues

/-!
# Writer currentness: every ledger use is a recorded physical write

`UseFrame ring A u`: the use `u` has a frame of the audit at its time after which the target digit
is `digitMod (value + carryIn)`, unless the target was dirty, or held the base label `ZERO`, before
it (a dirty target keeps its digit, `liveTop_advance_d`; the base label pre-empts a launch write,
`liveTop_launch_d`).  `UsesFramed` asks this for every use of every writer ledger of the current
ghost and of every frame's old ghost, and is carried by the audit.

Consumer: `Leader/L3/Width/DigitWriterCurrentCells.lean` (the target cells of a completion).
-/

namespace L3

set_option autoImplicit false

section Writes

variable {c : Compiled} {n : Nat}

/-- On a ring of at least two sites the right neighbour is another site.

Consumer: `usesFramed_step`. -/
theorem rightNeighbor_ne (ring : DirectedRing n) (hn2 : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have h1 : (e.val + 1) % n = e.val := congrArg Fin.val h
  have h2 := e.isLt
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at h1
    omega
  · have : e.val + 1 = n := by omega
    rw [this, Nat.mod_self] at h1
    omega

/-- **The use has a frame at its time showing the write.**

Consumer: `UsesFramed`. -/
def UseFrame (ring : DirectedRing n) (A : DigitAudit c n) (u : DigitUse c n) : Prop :=
  ∃ f ∈ A.frames, f.time = u.time ∧
    ((phiD ring f.old f.edge u.target).top.d =
        c.digitMod (u.value.val + (if u.carryIn then 1 else 0)) ∨
      (f.old u.target).top.topDirty = true ∨ (f.old u.target).top.wBase = .ZERO)

/-- **Every use of every writer ledger of the current ghost and of the old ghost of every frame has
its frame.**

Consumer: `usesFramed_step`, `usesFramed_fold`. -/
def UsesFramed (ring : DirectedRing n) (A : DigitAudit c n) : Prop :=
  (∀ i L, (A.current i).writer.carry = some L → ∀ u ∈ L.uses, UseFrame ring A u) ∧
  (∀ f ∈ A.frames, ∀ i L, (f.oldGhost i).writer.carry = some L → ∀ u ∈ L.uses,
    UseFrame ring A u)

/-- Consumer: `usesFramed_step`. -/
theorem useFrame_mono (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (u : DigitUse c n) (h : UseFrame ring A u) :
    UseFrame ring (digitAuditStep ring S A e) u := by
  obtain ⟨f, hf, h1, h2⟩ := h
  exact ⟨f, List.mem_cons_of_mem _ hf, h1, h2⟩

/-- Consumer: `usesFramed_step`. -/
theorem advanceDisj (ring : DirectedRing n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (S : Fin n → ProjD c) (cc : Bool) (v : Fin c.topA) (T : Bool)
    (hxl : (S e).word.native.l = false) (hyl : (S (ring.rightNeighbor e)).word.native.l = false)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta = false)
    (hw : (S e).top.wCarry = .W cc) (hoff : (S (ring.rightNeighbor e)).top.wCarry = .OFF)
    (hs : (S (ring.rightNeighbor e)).top.wIn = .S v T) :
    (phiD ring S e (ring.rightNeighbor e)).top.d = c.digitMod (v.val + (if cc then 1 else 0)) ∨
      (S (ring.rightNeighbor e)).top.topDirty = true := by
  have w := writerAdvanceWrite ring S e hne cc v T hxl hyl hbY hw hoff hs
  by_cases hd : (S (ring.rightNeighbor e)).top.topDirty = true
  · exact Or.inr hd
  · rw [if_neg hd] at w
    exact Or.inl w

/-- Consumer: `usesFramed_step`. -/
theorem launchDisj (ring : DirectedRing n) (S : Fin n → ProjD c) (e : Fin n) (v : Fin c.topA)
    (T : Bool)
    (hxl : (S e).word.native.l = false) (hyl : (S (ring.rightNeighbor e)).word.native.l = false)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = true)
    (hw : (S e).top.wCarry = .OFF) (hs : (S e).top.wIn = .S v T) :
    (phiD ring S e e).top.d = c.digitMod (v.val + 1) ∨ (S e).top.topDirty = true ∨
      (S e).top.wBase = .ZERO := by
  by_cases hb : (S e).top.wBase = .ZERO
  · exact Or.inr (Or.inr hb)
  · have w := writerLaunchWrite ring S e v T hxl hyl hbX hb hw hs
    by_cases hd : (S e).top.topDirty = true
    · exact Or.inr (Or.inl hd)
    · rw [if_neg hd] at w
      exact Or.inl w

/-- **One audit letter preserves `UsesFramed`.**

Consumer: `usesFramed_fold`. -/
theorem usesFramed_step (ring : DirectedRing n) (hn2 : 2 ≤ n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (h : UsesFramed ring A) :
    UsesFramed ring (digitAuditStep ring S A e) := by
  have hne := rightNeighbor_ne ring hn2 e
  obtain ⟨f0, hf0, hf0t, hf0e, hf0o⟩ : ∃ f : DigitFrame c n,
      f ∈ (digitAuditStep ring S A e).frames ∧ f.time = A.clock + 1 ∧ f.edge = e ∧
        f.old = S := ⟨_, List.mem_cons_self .., rfl, rfl, rfl⟩
  have hxP : ∀ L, (A.current e).writer.carry = some L → ∀ u ∈ L.uses,
      UseFrame ring (digitAuditStep ring S A e) u :=
    fun L hL u hu => useFrame_mono ring S A e u (h.1 e L hL u hu)
  have hyP : ∀ L, (A.current (ring.rightNeighbor e)).writer.carry = some L → ∀ u ∈ L.uses,
      UseFrame ring (digitAuditStep ring S A e) u :=
    fun L hL u hu => useFrame_mono ring S A e u (h.1 _ L hL u hu)
  have key := usesPair DigitLane.writer (A.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .writer (S e) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaX)
    (digitLaneView .writer (S (ring.rightNeighbor e))
      (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY)
    (A.current e).writer (A.current (ring.rightNeighbor e)).writer
    (UseFrame ring (digitAuditStep ring S A e)) hxP hyP
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
      refine ⟨f0, hf0, hf0t, ?_⟩
      show (phiD ring f0.old f0.edge (ring.rightNeighbor e)).top.d =
          c.digitMod ((inV c (S (ring.rightNeighbor e)).top.wIn).val +
            (if wcC (S e).top.wCarry = true then 1 else 0)) ∨
        (f0.old (ring.rightNeighbor e)).top.topDirty = true ∨
        (f0.old (ring.rightNeighbor e)).top.wBase = .ZERO
      rw [hf0e, hf0o, hv, hcb]
      rcases advanceDisj ring e hne S cc v T hxl hyl hbY hw hoff hs with d | d
      · exact Or.inl d
      · exact Or.inr (Or.inl d))
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
      refine ⟨f0, hf0, hf0t, ?_⟩
      show (phiD ring f0.old f0.edge e).top.d =
          c.digitMod ((inV c (S e).top.wIn).val + (if (true : Bool) = true then 1 else 0)) ∨
        (f0.old e).top.topDirty = true ∨ (f0.old e).top.wBase = .ZERO
      rw [hf0e, hf0o, hv]
      simpa using launchDisj ring S e v T hxl hyl hbX hw hs)
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
        exact useFrame_mono ring S A e u (h.1 i L hL' u hu)
  · intro f hf i L hL u hu
    simp only [digitAuditStep, List.mem_cons] at hf
    rcases hf with hf | hf
    · subst hf
      exact useFrame_mono ring S A e u (h.1 i L hL u hu)
    · exact useFrame_mono ring S A e u (h.2 f hf i L hL u hu)

/-- Consumer: `usesFramed_fold`. -/
theorem usesFramed_initial (ring : DirectedRing n) (S : Fin n → ProjD c) :
    UsesFramed ring (digitAuditInitial S) := by
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

/-- **`UsesFramed` along the audit fold of a drained start.**

Consumer: `terminalUsesFramed`. -/
theorem usesFramed_fold (ref : WidthDigitReference ring) (hn2 : 2 ≤ n) (w : List (Fin n)) :
    ∀ p : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ref.drained p.1 → UsesFramed ring p.2 →
      ref.drained (w.foldl (widthDigitAuditNext ref) p).1 ∧
        UsesFramed ring (w.foldl (widthDigitAuditNext ref) p).2 := by
  induction w with
  | nil => intro p hd hi; exact ⟨hd, hi⟩
  | cons e w ih =>
    intro p hd hi
    simp only [List.foldl_cons]
    exact ih (widthDigitAuditNext ref p e) (ref.drainedClosed p.1 hd e)
      (usesFramed_step ring hn2 (piD (ref.phys p.1)) p.2 e hi)

/-- **Every use of the ledger of a recorded writer terminal has its frame**, on the audit fold of
a drained start.

Consumer: `writerCellsOfCompletion` (WidthDigitWriterCurrentCells). -/
theorem terminalUsesFramed (ref : WidthDigitReference ring) (hn2 : 2 ≤ n) (start : ref.State)
    (hd : ref.drained start) (w : List (Fin n))
    (t : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hrec : DigitRecordedTerminal
      (w.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2 t)
    (hlane : t.lane = .writer) (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hL : t.ledger = some L) :
    ∀ u ∈ L.uses, UseFrame ring
      (w.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2 u := by
  have hU := (usesFramed_fold ref hn2 w (start, digitAuditInitial (piD (ref.phys start))) hd
    (usesFramed_initial ring _)).2
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

#print axioms L3.usesFramed_step
#print axioms L3.terminalUsesFramed

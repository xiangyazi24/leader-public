import Leader.L3.Top.PinnedPrepClasses
import Leader.L3.Top.PinnedFramesInv

/-!
# Q7 (P.12): no earlier strict stop

`topFixedStrictStop` asks for the minimal strict terminal of the whole audit, so a state whose
audit already holds a strict terminal never reaches a strict stop.  This module proves

* the audit-extension relation `PhaseAuditExt A B` (the frames of `B` that are not frames of `A`
  are newer than the clock of `A`) and the restriction lemma: a strict terminal of a longer audit
  whose time lies within a prefix is strict in the prefix audit (`phase_strict_restrict`), and
  conversely a strict terminal persists to every longer audit (`phase_strict_extend`);
* `NoPrefixStop Z`: `Z` is reached and no prefix of its word is a strict stop, together with its
  closure along a letter that does not itself stop (`noPrefixStop_next`);
* `phase_stop_of_terminal`: a strict terminal that appears at the newest service of a state
  without earlier stop is a strict stop, i.e. its first-ness comes for free.

Consumer: `Leader/L3/Top/PinnedPhaseClasses.lean` and the strict-terminal certificate.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The audit `B` extends the audit `A`: same start, `A`'s frames are frames of `B` within the
clock of `A`, and every other frame of `B` is newer than the clock of `A`.

Consumer: `phase_strict_restrict`, `phase_strict_extend`. -/
def PhaseAuditExt {c : Compiled} {n : Nat} (A B : DigitAudit c n) : Prop :=
  A.start = B.start ∧ A.clock ≤ B.clock ∧
  (∀ f ∈ A.frames, f ∈ B.frames ∧ f.time ≤ A.clock) ∧
  (∀ f ∈ B.frames, f ∉ A.frames → A.clock < f.time)

/-- An audit with chronological frames extends itself.

Consumer: `phase_ext_run`. -/
theorem phaseAuditExt_refl {c : Compiled} {n : Nat} (A : DigitAudit c n)
    (h : ∀ f ∈ A.frames, f.time ≤ A.clock) : PhaseAuditExt A A :=
  ⟨rfl, Nat.le_refl _, fun f hf => ⟨hf, h f hf⟩, fun _ hf hn => absurd hf hn⟩

/-- One audit step keeps the extension.

Consumer: `phase_ext_fold`. -/
theorem phaseAuditExt_step {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (S : Fin n → ProjD c) (A B : DigitAudit c n) (e : Fin n) (h : PhaseAuditExt A B) :
    PhaseAuditExt A (digitAuditStep ring S B e) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, ?_, ?_, ?_⟩
  · simp only [digitAuditStep]; omega
  · intro f hf
    exact ⟨by simp only [digitAuditStep, List.mem_cons]; exact Or.inr (h3 f hf).1, (h3 f hf).2⟩
  · intro f hf hn
    simp only [digitAuditStep, List.mem_cons] at hf
    rcases hf with rfl | hf
    · simp only; omega
    · exact h4 f hf hn

/-- A folded word keeps the extension.

Consumer: `phase_ext_run`. -/
theorem phase_ext_fold {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    ∀ (v : List (Fin n)) (Z : TopFixedTraceState n), PhaseAuditExt A Z.1.2 →
      PhaseAuditExt A (v.foldl (topFixedTraceNext ring C) Z).1.2 := by
  intro v
  induction v with
  | nil => intro Z h; exact h
  | cons e v ih =>
      intro Z h
      exact ih _ (phaseAuditExt_step ring (piD Z.1.1) A Z.1.2 e h)

/-- The audit of a run extends the audit of each of its prefixes.

Consumer: `phase_prefix_stop`, `phase_stop_of_terminal`. -/
theorem phase_ext_run {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (a b : List (Fin n)) :
    PhaseAuditExt (topFixedTraceRun ring C a).1.2 (topFixedTraceRun ring C (a ++ b)).1.2 := by
  rw [topFixedTraceRunAppendWord]
  exact phase_ext_fold ring C _ b _
    (phaseAuditExt_refl _ (fun f hf => ((framesInv_run ring C a).1 f hf).2))

/-- The clock of a run is the length of its word.

Consumer: `phase_prefix_stop`. -/
theorem phase_clock_fold {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) :
    ∀ (v : List (Fin n)) (Z : TopFixedTraceState n),
      (v.foldl (topFixedTraceNext ring C) Z).1.2.clock = Z.1.2.clock + v.length := by
  intro v
  induction v with
  | nil => intro Z; simp
  | cons e v ih =>
      intro Z
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [topFixedTraceNext, digitAuditStep]
      omega

/-- The clock of a run is the length of its word.

Consumer: `phase_prefix_stop`. -/
theorem phase_clock_run {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (w : List (Fin n)) : (topFixedTraceRun ring C w).1.2.clock = w.length := by
  unfold topFixedTraceRun
  rw [phase_clock_fold]
  simp [digitAuditInitial]

/-- A frame of the longer audit within the clock of the shorter one is a frame of the shorter.

Consumer: `phase_strict_restrict`. -/
theorem phase_frame_restrict {c : Compiled} {n : Nat} {A B : DigitAudit c n}
    (h : PhaseAuditExt A B) (f : DigitFrame c n) (hf : f ∈ B.frames) (ht : f.time ≤ A.clock) :
    f ∈ A.frames := by
  apply Classical.byContradiction
  intro hn
  have := h.2.2.2 f hf hn
  omega

/-- **Restriction**: a strict cyclic terminal of a longer audit whose time lies within the clock
of a prefix audit is strict in the prefix audit.

Consumer: `phase_prefix_stop`. -/
theorem phase_strict_restrict {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (A B : DigitAudit (compileAdvice (ceilLogTwo n)) n) (h : PhaseAuditExt A B)
    (t : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hs : HeadlineDigit.StrictCyclicTerminal ring C s B t) (ht : t.time ≤ A.clock) :
    HeadlineDigit.StrictCyclicTerminal ring C s A t := by
  unfold HeadlineDigit.StrictCyclicTerminal at hs ⊢
  obtain ⟨hstart, hpair, hrec, hlane, hsrc, hdst, hpos, ledger, samples, exports, uses, hbody⟩ := hs
  dsimp only at hbody ⊢
  obtain ⟨hl1, hl2, hl3, hall, hord, hother⟩ := hbody
  refine ⟨h.1.trans hstart, hpair, ?_, hlane, hsrc, hdst, hpos, ledger, samples, exports, uses,
    hl1, hl2, hl3, ?_, hord, ?_⟩
  · obtain ⟨f, hf, h1, h2, h3⟩ := hrec
    exact ⟨f, phase_frame_restrict h f hf (by omega), h1, h2, h3⟩
  · intro j
    obtain ⟨a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, u1, u2, u3, u4, u5, o1, o2, o3⟩ := hall j
    refine ⟨?_, a2, a3, a4, a5, ?_, b2, b3, b4, b5, b6, b7, u1, u2, u3, u4, u5, o1, o2, o3⟩
    · obtain ⟨f, hf, h1, h2, h3, h4⟩ := a1
      exact ⟨f, phase_frame_restrict h f hf (by omega), h1, h2, h3, h4⟩
    · obtain ⟨f, hf, h1, h2, h3⟩ := b1
      exact ⟨f, phase_frame_restrict h f hf (by omega), h1, h2, h3⟩
  · intro other hother' hl hsrc' hdst' hle hge
    obtain ⟨f, hf, h1, h2, h3⟩ := hother'
    exact hother other ⟨f, (h.2.2.1 f hf).1, h1, h2, h3⟩ hl hsrc' hdst' hle hge

/-- **Persistence**: a strict cyclic terminal of a prefix audit is strict in every longer audit.

Consumer: `phase_prefix_stop`, `phase_stop_of_terminal`. -/
theorem phase_strict_extend {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (A B : DigitAudit (compileAdvice (ceilLogTwo n)) n) (h : PhaseAuditExt A B)
    (t : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hs : HeadlineDigit.StrictCyclicTerminal ring C s A t) :
    HeadlineDigit.StrictCyclicTerminal ring C s B t := by
  have htA : t.time ≤ A.clock := by
    obtain ⟨_, _, ⟨f, hf, h1, _⟩, _⟩ := hs
    rw [← h1]
    exact (h.2.2.1 f hf).2
  unfold HeadlineDigit.StrictCyclicTerminal at hs ⊢
  obtain ⟨hstart, hpair, hrec, hlane, hsrc, hdst, hpos, ledger, samples, exports, uses, hbody⟩ := hs
  dsimp only at hbody ⊢
  obtain ⟨hl1, hl2, hl3, hall, hord, hother⟩ := hbody
  refine ⟨h.1 ▸ hstart, hpair, ?_, hlane, hsrc, hdst, hpos, ledger, samples, exports, uses,
    hl1, hl2, hl3, ?_, hord, ?_⟩
  · obtain ⟨f, hf, h1, h2, h3⟩ := hrec
    exact ⟨f, (h.2.2.1 f hf).1, h1, h2, h3⟩
  · intro j
    obtain ⟨a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, u1, u2, u3, u4, u5, o1, o2, o3⟩ := hall j
    refine ⟨?_, a2, a3, a4, a5, ?_, b2, b3, b4, b5, b6, b7, u1, u2, u3, u4, u5, o1, o2, o3⟩
    · obtain ⟨f, hf, h1, h2, h3, h4⟩ := a1
      exact ⟨f, (h.2.2.1 f hf).1, h1, h2, h3, h4⟩
    · obtain ⟨f, hf, h1, h2, h3⟩ := b1
      exact ⟨f, (h.2.2.1 f hf).1, h1, h2, h3⟩
  · intro other hother' hl hsrc' hdst' hle hge
    obtain ⟨f, hf, h1, h2, h3⟩ := hother'
    have hfirst := hall ⟨0, hpos⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, o1, o2, o3⟩ := hfirst
    have hotime : other.time ≤ A.clock := by omega
    exact hother other ⟨f, phase_frame_restrict h f hf (by omega), h1, h2, h3⟩ hl hsrc' hdst' hle hge

/-- The terminal of a strict cyclic comparison sits on the right neighbour of its source.

Consumer: `phase_prefix_stop`, `phase_stop_of_terminal`. -/
theorem phase_strict_dest {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (t : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hs : HeadlineDigit.StrictCyclicTerminal ring C s A t) :
    t.destination = ring.rightNeighbor t.source := by
  unfold HeadlineDigit.StrictCyclicTerminal at hs
  obtain ⟨_, _, _, _, hsrc, hdst, hpos, _⟩ := hs
  rw [hsrc, hdst, rn_certSite]
  congr 1
  omega

/-- **No earlier strict stop**: the state is reached and no prefix of its word (including the
word itself) is a strict stop.

Consumer: `Leader/L3/Top/PinnedPhaseClasses.lean`. -/
def NoPrefixStop {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop :=
  topClockReached ring C Z ∧
    ∀ m : Nat, m ≤ Z.2.length →
      ¬ topFixedStrictStop ring C s (topFixedTraceRun ring C (Z.2.take m))

/-- The invariant `NoPrefixStop` survives a letter that does not itself stop.

Consumer: `Leader/L3/Top/PinnedPhaseClasses.lean` (closure of the transfer invariant). -/
theorem noPrefixStop_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (h : NoPrefixStop ring C s Z)
    (hn : ¬ topFixedStrictStop ring C s (topFixedTraceNext ring C Z e)) :
    NoPrefixStop ring C s (topFixedTraceNext ring C Z e) := by
  obtain ⟨hreach, hall⟩ := h
  refine ⟨topClockReachedNext ring C Z e hreach, ?_⟩
  intro m hm
  have hsnd : (topFixedTraceNext ring C Z e).2 = Z.2 ++ [e] := rfl
  rw [hsnd] at hm ⊢
  simp only [List.length_append, List.length_singleton] at hm
  by_cases hle : m ≤ Z.2.length
  · rw [List.take_append_of_le_length hle]
    exact hall m hle
  · have hm' : m = Z.2.length + 1 := by omega
    have htake : (Z.2 ++ [e]).take m = Z.2 ++ [e] := by
      apply List.take_of_length_le
      simp only [List.length_append, List.length_singleton]
      omega
    rw [htake]
    have hrun : topFixedTraceRun ring C (Z.2 ++ [e]) = topFixedTraceNext ring C Z e := by
      have hrun0 := topFixedTraceRunAppendWord ring C Z.2 [e]
      rw [hrun0, ← hreach]
      rfl
    rw [hrun]
    exact hn

/-- The initial state has no earlier strict stop.

Consumer: transfer of the fresh-tail phase. -/
theorem noPrefixStop_initial {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) :
    NoPrefixStop ring C s ((C, digitAuditInitial (piD C)), []) := by
  refine ⟨rfl, ?_⟩
  intro m hm
  have hm0 : m = 0 := by simpa using hm
  subst hm0
  rintro ⟨pfx, e, terminal, h1, _⟩
  have h2 : (topFixedTraceRun ring C (([] : List (Fin n)).take 0)).2 = [] := by
    rw [topFixedTraceRun_snd]; rfl
  rw [h2] at h1
  exact absurd h1 (by simp)

/-- A nonempty set of naturals has a least element.

Consumer: `phase_prefix_stop`. -/
theorem phase_nat_min (P : Nat → Prop) (h : ∃ k, P k) :
    ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | _ k ih =>
      by_cases hs : ∃ j, j < k ∧ P j
      · obtain ⟨j, hj, hPj⟩ := hs
        exact ih j hj hPj
      · refine ⟨k, hk, ?_⟩
        intro j hj
        apply Classical.byContradiction
        intro hn
        exact hs ⟨j, by omega, hj⟩

/-- A strict terminal of a reached state yields a strict stop at some prefix.

Consumer: `phase_stop_of_terminal`. -/
theorem phase_prefix_stop {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (w : List (Fin n))
    (o : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (ho : HeadlineDigit.StrictCyclicTerminal ring C s (topFixedTraceRun ring C w).1.2 o) :
    ∃ m : Nat, m ≤ w.length ∧
      topFixedStrictStop ring C s (topFixedTraceRun ring C (w.take m)) := by
  have hex : ∃ k : Nat, ∃ o' : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      HeadlineDigit.StrictCyclicTerminal ring C s (topFixedTraceRun ring C w).1.2 o' ∧
        o'.time = k := ⟨o.time, o, ho, rfl⟩
  obtain ⟨k0, ⟨o0, ho0, hk0⟩, hk0min⟩ := phase_nat_min
    (fun k => ∃ o' : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      HeadlineDigit.StrictCyclicTerminal ring C s (topFixedTraceRun ring C w).1.2 o' ∧
        o'.time = k) hex
  have hmin : ∀ o' : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      HeadlineDigit.StrictCyclicTerminal ring C s (topFixedTraceRun ring C w).1.2 o' →
        k0 ≤ o'.time := fun o' ho' => hk0min o'.time ⟨o', ho', rfl⟩
  have hfw := framesInv_run ring C w
  obtain ⟨f0, hf0, hf0t, hf0e, hf0r⟩ := ho0.2.2.1
  have hk0pos : 1 ≤ k0 := by
    have := (hfw.1 f0 hf0).1
    omega
  have hk0le : k0 ≤ w.length := by
    have := (hfw.1 f0 hf0).2
    rw [phase_clock_run] at this
    omega
  refine ⟨k0, hk0le, ?_⟩
  have hwsplit : w = w.take k0 ++ w.drop k0 := (List.take_append_drop k0 w).symm
  have hext : PhaseAuditExt (topFixedTraceRun ring C (w.take k0)).1.2
      (topFixedTraceRun ring C w).1.2 := by
    conv => rhs; rw [hwsplit]
    exact phase_ext_run ring C _ _
  have hlen : (w.take k0).length = k0 := by
    simp only [List.length_take]; omega
  have hclock : (topFixedTraceRun ring C (w.take k0)).1.2.clock = k0 := by
    rw [phase_clock_run, hlen]
  have hs0 : HeadlineDigit.StrictCyclicTerminal ring C s
      (topFixedTraceRun ring C (w.take k0)).1.2 o0 :=
    phase_strict_restrict ring C s _ _ hext o0 ho0 (by omega)
  have hfirst : HeadlineDigit.FirstStrictCyclicTerminal ring C s
      (topFixedTraceRun ring C (w.take k0)).1.2 o0 := by
    refine ⟨hs0, ?_⟩
    intro other hother
    have := hmin other (phase_strict_extend ring C s _ _ hext other hother)
    omega
  obtain ⟨L, b, hLb⟩ : ∃ (L : List (Fin n)) (b : Fin n), w.take k0 = L ++ [b] := by
    rcases List.eq_nil_or_concat (w.take k0) with h | ⟨L, b, h⟩
    · rw [h] at hlen; simp at hlen; omega
    · exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
  have hLlen : L.length + 1 = k0 := by
    rw [hLb] at hlen; simpa using hlen
  have hrun : topFixedTraceRun ring C (w.take k0) =
      topFixedTraceNext ring C (topFixedTraceRun ring C L) b := by
    rw [hLb, topFixedTraceRunAppendWord]; rfl
  have hsrc : o0.source = b := by
    obtain ⟨g, hg, hgt, hge, hgr⟩ := hs0.2.2.1
    rw [hrun] at hg
    simp only [topFixedTraceNext, digitAuditStep, List.mem_cons] at hg
    have hclockL := phase_clock_run ring C L
    rcases hg with hg | hg
    · rw [← hge, hg]
    · have := ((framesInv_run ring C L).1 g hg).2
      omega
  refine ⟨L, b, o0, ?_, hfirst, ?_, hsrc, ?_⟩
  · rw [topFixedTraceRun_snd, hLb]
  · omega
  · rw [phase_strict_dest ring C s _ o0 hs0, hsrc]

/-- **First-ness is free**: a strict cyclic terminal that appears at the newest service of a
state without earlier strict stop is a strict stop.

Consumer: the strict-terminal certificate along the aligned carry sweep
(`Leader/L3/Top/PinnedPhaseSweep.lean`), and `TopClockPreparationPhase`. -/
theorem phase_stop_of_terminal {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Y : TopFixedTraceState n) (e : Fin n) (hY : NoPrefixStop ring C s Y)
    (t : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hs : HeadlineDigit.StrictCyclicTerminal ring C s (topFixedTraceNext ring C Y e).1.2 t)
    (htime : t.time = Y.2.length + 1) (hsrc : t.source = e) :
    topFixedStrictStop ring C s (topFixedTraceNext ring C Y e) := by
  have hreach := hY.1
  have hrunY : topFixedTraceRun ring C Y.2 = Y := hreach.symm
  have hrunZ : topFixedTraceRun ring C (Y.2 ++ [e]) = topFixedTraceNext ring C Y e := by
    rw [topFixedTraceRunAppendWord, hrunY]; rfl
  refine ⟨Y.2, e, t, rfl, ⟨hs, ?_⟩, htime, hsrc, ?_⟩
  · intro other hother
    apply Classical.byContradiction
    intro hlt
    have hotime : other.time ≤ Y.2.length := by omega
    have hext : PhaseAuditExt (topFixedTraceRun ring C Y.2).1.2
        (topFixedTraceRun ring C (Y.2 ++ [e])).1.2 := phase_ext_run ring C Y.2 [e]
    rw [hrunZ] at hext
    have hrestrict := phase_strict_restrict ring C s _ _ hext other hother
      (by rw [phase_clock_run]; exact hotime)
    obtain ⟨m, hm, hstop⟩ := phase_prefix_stop ring C s Y.2 other hrestrict
    exact hY.2 m hm hstop
  · rw [phase_strict_dest ring C s _ t hs, hsrc]

end MarkedCells
end L3

#print axioms L3.MarkedCells.phase_strict_restrict
#print axioms L3.MarkedCells.phase_strict_extend
#print axioms L3.MarkedCells.noPrefixStop_next
#print axioms L3.MarkedCells.phase_prefix_stop
#print axioms L3.MarkedCells.phase_stop_of_terminal

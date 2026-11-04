import Leader.Wu.Authorization.CheckTerminalReady
import Leader.Wu.Authorization.CheckTerminalConsume
import Leader.Wu.Authorization.GenerationDrain

/-!
# A terminal CHECK-ready word in the original population protocol

The local first-service trichotomy and terminal pending consumer give an
actual word containing one or two services of the same physical edge.
The bound `1 < n` ensures distinct endpoints, including width two. Every
other physical cell is framed exactly, on both target and continuing exits.
The continuing exit uses one service and preserves the first-row interface.

This module consumes the TerminalReady theorem; it makes no assertion of
generator reachability. A source-feasible width-two entrance has `n = 2`,
edge 0, labels 0/1, own paths, depart/CHECK_ready states, empty path2 slots,
common path marks and matching left control, and follower/reset-free cells.
-/

namespace PPLLAuthCheckTerminalMacro

open PPLL PPLLAuthF
open PPLLAuthCheckComponent PPLLAuthCheckComponentFrame PPLLAuthCheckComponentStep
open PPLLAuthCheckTerminalReady PPLLAuthCheckTerminalConsume
open PPLLAuthResetDrain PPLLAuthGenDrain

set_option autoImplicit false

variable {n ψ : Nat}

/-- Some physical cell has no main path. -/
def GlobalHole (D : Fin n → AuthState ψ) : Prop :=
  ∃ i, (D i).core.path = .bot

/-- One service of edge `e`: exact initiator state. -/
theorem authRun_one_left
    (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e : Fin n) :
    (authRun hp κ c ring C [e]) e =
      (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).1 := by
  change bstep hp κ c ring C e e =
    (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).1
  exact bstep_left hp κ c ring C e

/-- One service of edge `e`: exact responder state. -/
theorem authRun_one_right
    (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hn : 1 < n) (C : Fin n → AuthState ψ) (e : Fin n) :
    (authRun hp κ c ring C [e]) (ring.rightNeighbor e) =
      (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).2 := by
  change bstep hp κ c ring C e (ring.rightNeighbor e) =
    (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).2
  exact bstep_right hp κ c ring hn C e

/-- One service of edge `e` fixes every non-endpoint cell. -/
theorem authRun_one_other
    (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e i : Fin n)
    (hie : i ≠ e) (hij : i ≠ ring.rightNeighbor e) :
    (authRun hp κ c ring C [e]) i = C i := by
  change bstep hp κ c ring C e i = C i
  exact bstep_other hp κ c ring C e i hie hij

/-- Two consecutive services of the same physical edge: exact second responder. -/
theorem authRun_two_right
    (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hn : 1 < n) (C : Fin n → AuthState ψ) (e : Fin n) :
    (authRun hp κ c ring C [e, e]) (ring.rightNeighbor e) =
      (PPLLAuthF.pipeline hp κ c
        ((authRun hp κ c ring C [e]) e)
        ((authRun hp κ c ring C [e]) (ring.rightNeighbor e))).2 := by
  change bstep hp κ c ring (authRun hp κ c ring C [e]) e
      (ring.rightNeighbor e) =
    (PPLLAuthF.pipeline hp κ c
      ((authRun hp κ c ring C [e]) e)
      ((authRun hp κ c ring C [e]) (ring.rightNeighbor e))).2
  exact bstep_right hp κ c ring hn (authRun hp κ c ring C [e]) e

/-- Two consecutive services of the same edge still fix every non-endpoint cell. -/
theorem authRun_two_other
    (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e i : Fin n)
    (hie : i ≠ e) (hij : i ≠ ring.rightNeighbor e) :
    (authRun hp κ c ring C [e, e]) i = C i := by
  calc
    (authRun hp κ c ring C [e, e]) i =
        (authRun hp κ c ring C [e]) i := by
      change bstep hp κ c ring (authRun hp κ c ring C [e]) e i =
        (authRun hp κ c ring C [e]) i
      exact bstep_other hp κ c ring (authRun hp κ c ring C [e]) e i hie hij
    _ = C i := authRun_one_other hp κ c ring C e i hie hij

/--
A terminal-ready physical edge admits a word of one or two services.

The first row stops immediately on `Target` or `Continuing`.  Only the
`TerminalPending` branch serves the same edge once more, and the accepted
consumer then gives a responder main-path hole.
-/
theorem terminal_ready_word
    (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AuthState ψ) (e : Fin n) (bl br : Nat)
    (h : TerminalReady (C e) (C (ring.rightNeighbor e)) bl br) :
    ∃ w : List (Fin n),
      (w = [e] ∨ w = [e, e]) ∧
      w.length ≤ 2 ∧
      (∀ i, i ≠ e → i ≠ ring.rightNeighbor e →
        (authRun hp κ cfg ring C w) i = C i) ∧
      (Target
          ((authRun hp κ cfg ring C w) e,
           (authRun hp κ cfg ring C w) (ring.rightNeighbor e)) ∨
        (w = [e] ∧
          Continuing (C e) (C (ring.rightNeighbor e))
            ((authRun hp κ cfg ring C w) e,
             (authRun hp κ cfg ring C w) (ring.rightNeighbor e)))) := by
  let q :=
    PPLLAuthF.pipeline hp κ cfg (C e) (C (ring.rightNeighbor e))
  have hq :
      Target q ∨ Continuing (C e) (C (ring.rightNeighbor e)) q ∨
        TerminalPending q.1 q.2 bl br := by
    simpa [q] using
      (terminal_ready_step hp κ (C e) (C (ring.rightNeighbor e)) bl br h)

  have h1l : (authRun hp κ cfg ring C [e]) e = q.1 := by
    simpa [q] using authRun_one_left hp κ cfg ring C e
  have h1r :
      (authRun hp κ cfg ring C [e]) (ring.rightNeighbor e) = q.2 := by
    simpa [q] using authRun_one_right hp κ cfg ring hn C e

  rcases hq with ht | hq
  · refine ⟨[e], Or.inl rfl, by simp, ?_, ?_⟩
    · intro i hie hij
      exact authRun_one_other hp κ cfg ring C e i hie hij
    · left
      simpa [h1l, h1r] using ht

  rcases hq with hc | hpending
  · refine ⟨[e], Or.inl rfl, by simp, ?_, ?_⟩
    · intro i hie hij
      exact authRun_one_other hp κ cfg ring C e i hie hij
    · right
      refine ⟨rfl, ?_⟩
      simpa [h1l, h1r] using hc

  · have hh :=
      pipeline_terminal_pending_right_hole hp κ q.1 q.2 bl br hpending
    have hhole :
        ((authRun hp κ cfg ring C [e, e]) (ring.rightNeighbor e)).core.path =
          .bot := by
      rw [authRun_two_right hp κ cfg ring hn C e]
      rw [h1l, h1r]
      exact hh
    have ht2 :
        Target
          ((authRun hp κ cfg ring C [e, e]) e,
           (authRun hp κ cfg ring C [e, e]) (ring.rightNeighbor e)) := by
      unfold Target PairHole
      exact Or.inr (Or.inr (Or.inr hhole))
    refine ⟨[e, e], Or.inr rfl, by simp, ?_, Or.inl ht2⟩
    intro i hie hij
    exact authRun_two_other hp κ cfg ring C e i hie hij

/--
The same macro packaged in the accepted `Rch` interface.  `Rch` already
separates a global leader; its residual predicate is a global main-path hole or
the exact first-row `Continuing` frame.
-/
theorem terminal_ready_Rch2
    (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AuthState ψ) (e : Fin n) (bl br : Nat)
    (h : TerminalReady (C e) (C (ring.rightNeighbor e)) bl br) :
    Rch hp κ cfg ring C 2
      (fun D =>
        GlobalHole D ∨
          Continuing (C e) (C (ring.rightNeighbor e))
            (D e, D (ring.rightNeighbor e))) := by
  obtain ⟨w, _, hwlen, _, hout⟩ :=
    terminal_ready_word hp κ ring hn C e bl br h
  refine ⟨w, hwlen, ?_⟩
  rcases hout with ht | hc
  · unfold Target at ht
    rcases ht with hl | hr | hh
    · exact Or.inl ⟨e, hl⟩
    · exact Or.inl ⟨ring.rightNeighbor e, hr⟩
    · unfold PairHole at hh
      rcases hh with hh | hh
      · exact Or.inr (Or.inl ⟨e, hh⟩)
      · exact Or.inr (Or.inl ⟨ring.rightNeighbor e, hh⟩)
  · exact Or.inr (Or.inr hc.2)

#print axioms terminal_ready_word
#print axioms terminal_ready_Rch2

end PPLLAuthCheckTerminalMacro


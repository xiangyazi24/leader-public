import Leader.Wu.Birth.CheckPermitRepairRowLift
import Leader.Wu.Birth.CheckPermitRepairLeaf

set_option autoImplicit false

/-! # The R1 CHECK chain on the ring

A train window starts at cell `s`; its `k`-th cell is `cell ring s k`.  `ReadyCell k u`: `u` is a check-open matching
carrier at label `k` (path `(k, bit)`, no path2, outside depart/equal/larger/less/produce/done/toss/congest/
eliminate_signal), a follower without reset command, with no clean command on path5 (nor on path4 at label 0) and
a positive stall.  `trainRequests ring s psi` is the ordered list of the `psi - 1` internal train edges.  From a
configuration whose train window consists of ready cells (psi at least three, at most n), applying `step1` along the
request list creates a leader on a window cell (`train_requests_leader`). -/

namespace BirthCheckChainR1Ring

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthCheckPermitRepairLeaf

set_option Elab.async false

variable {n ψ κ τ : Nat}

/-- The `k`-th cell of the window starting at `s`. -/
def cell (ring : DirectedRing n) (s : Fin n) (k : Nat) : Fin n :=
  ⟨(s.val + k) % n, Nat.mod_lt _ ring.hn⟩

theorem right_cell (ring : DirectedRing n) (s : Fin n) (k : Nat) :
    ring.rightNeighbor (cell ring s k) = cell ring s (k + 1) := by
  apply Fin.ext
  simp only [DirectedRing.rightNeighbor, cell]
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem mod_two_range (a : Nat) (h : a < 2 * n) : a % n = if a < n then a else a - n := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem cell_ne (ring : DirectedRing n) (s : Fin n) {k j : Nat} (hk : k < n) (hj : j < n) (h : k ≠ j) :
    cell ring s k ≠ cell ring s j := by
  intro he
  have hv := congrArg Fin.val he
  simp only [cell] at hv
  have hs := s.isLt
  rw [mod_two_range _ (by omega), mod_two_range _ (by omega)] at hv
  split at hv <;> split at hv <;> omega

theorem step1_left (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n) :
    step1 hψ h2 ring C e e = (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e))).1 := by
  simp only [step1, PopulationProtocol.step, BirthCheckPermitRepair.protocol, if_true]

theorem step1_right (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    step1 hψ h2 ring C e (ring.rightNeighbor e) =
      (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e))).2 := by
  simp only [step1, PopulationProtocol.step, BirthCheckPermitRepair.protocol, if_neg hne, if_true]

/-- A check-open matching follower carrier at label `k`, ready for the CHECK chain. -/
structure ReadyCell (k : Nat) (u : ExpiringAgentState ψ κ τ) : Prop where
  label : u.core.erase.core.label.val = k
  leader : u.core.erase.core.leader = false
  openMatch : BirthCheckChainR1.CheckOpenMatch u.core.erase.core
  notProduce : u.core.erase.core.state ≠ .produce
  notDone : u.core.erase.core.state ≠ .done
  notToss : u.core.erase.core.state ≠ .toss
  notCongest : u.core.erase.core.state ≠ .congest
  notEliminate : u.core.erase.core.state ≠ .eliminate_signal
  reset : u.core.erase.core.reset_cmd = false
  path4 : k = 0 → ∀ p, u.core.erase.core.path4 = some p → p.1 ≠ -1
  path5 : ∀ p, u.core.erase.core.path5 = some p → p.1 ≠ -1
  stall : u.stall.val ≠ 0

/-- An `equal` chain carrier at label `k`. -/
structure EqualCell (k : Nat) (u : ExpiringAgentState ψ κ τ) : Prop where
  label : u.core.erase.core.label.val = k
  leader : u.core.erase.core.leader = false
  path : ∃ bl, u.core.erase.core.path = .some k bl
  equal : u.core.erase.core.state = .equal
  path2 : u.core.erase.core.path2 = none
  reset : u.core.erase.core.reset_cmd = false

theorem ReadyCell.path_eq {k : Nat} {u : ExpiringAgentState ψ κ τ} (h : ReadyCell k u) :
    u.core.erase.core.path = .some k (if u.core.erase.core.bit then 1 else 0) := by
  rw [h.openMatch.path, h.label]

theorem cons_label (hψ : 0 < ψ) {k : Nat} (hk : k + 1 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (hl : l.core.erase.core.label.val = k) (hr : r.core.erase.core.label.val = k + 1) :
    r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ := by
  apply Fin.ext
  show r.core.erase.core.label.val = (l.core.erase.core.label.val + 1) % ψ
  rw [hr, hl, Nat.mod_eq_of_lt hk]

/-- First chain row on the ring. -/
theorem ring_first_row (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hn : 2 ≤ n) (C : FC n ψ κ τ)
    (s : Fin n) (h0 : ReadyCell 0 (C (cell ring s 0))) (h1 : ReadyCell 1 (C (cell ring s 1))) :
    EqualCell 1 (step1 hψ (by omega) ring C (cell ring s 0) (cell ring s 1)) := by
  have hne : ring.rightNeighbor (cell ring s 0) ≠ cell ring s 0 := by
    rw [right_cell]; exact cell_ne ring s (by omega) (by omega) (by omega)
  have e := step1_right (κ := κ) (τ := τ) hψ (by omega) ring C (cell ring s 0) hne
  rw [right_cell] at e
  rw [e]
  have hr := BirthCheckPermitRepairRowLift.r1_first_row hψ h3 (C (cell ring s 0)) (C (cell ring s 1))
    (cons_label hψ (by omega) _ _ h0.label h1.label) h0.leader h1.leader h0.openMatch h0.label h1.openMatch
    h1.label h0.notProduce h0.notDone h0.notToss h0.notCongest h0.notEliminate h1.notProduce h1.notDone
    h1.notEliminate h1.notToss h1.notCongest h0.reset h1.reset (h0.path4 rfl) h1.path5 h0.stall h1.stall
  obtain ⟨_, _, _, _, s2, p2, q2, l2, r2, d2⟩ := hr
  exact ⟨by rw [l2]; exact h1.label, d2, ⟨_, by rw [p2]; exact h1.path_eq⟩, s2, q2, r2⟩

/-- Intermediate chain row on the ring. -/
theorem ring_chain_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (hψn : ψ ≤ n) (C : FC n ψ κ τ)
    (s : Fin n) (m : Nat) (hm0 : 1 ≤ m) (hm : m + 1 < ψ - 1)
    (hl : EqualCell m (C (cell ring s m))) (hr : ReadyCell (m + 1) (C (cell ring s (m + 1)))) :
    EqualCell (m + 1) (step1 hψ h2 ring C (cell ring s m) (cell ring s (m + 1))) := by
  have hne : ring.rightNeighbor (cell ring s m) ≠ cell ring s m := by
    rw [right_cell]; exact cell_ne ring s (by omega) (by omega) (by omega)
  have e := step1_right (κ := κ) (τ := τ) hψ h2 ring C (cell ring s m) hne
  rw [right_cell] at e
  rw [e]
  obtain ⟨bl, hlp⟩ := hl.path
  have hrow := BirthCheckPermitRepairRowLift.r1_chain_row hψ h2 (C (cell ring s m)) (C (cell ring s (m + 1))) m bl
    (cons_label hψ (by omega) _ _ hl.label hr.label) hl.leader hr.leader hlp hl.label hm hr.openMatch hr.label
    hl.equal hl.path2 hr.notProduce hr.notDone hr.notEliminate hr.notToss hr.notCongest hl.reset hr.reset
    (fun h => absurd h (by omega)) hr.path5 hr.stall
  obtain ⟨s2, p2, q2, l2, r2, d2⟩ := hrow
  exact ⟨by rw [l2]; exact hr.label, d2, ⟨_, by rw [p2]; exact hr.path_eq⟩, s2, q2, r2⟩

/-- Terminal chain row on the ring: an `equal` label-(psi-2) initiator and a ready terminal responder create a
leader on one of the two cells. -/
theorem ring_terminal_row (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n) (C : FC n ψ κ τ)
    (s : Fin n) (hl : EqualCell (ψ - 2) (C (cell ring s (ψ - 2))))
    (hr : ReadyCell (ψ - 2 + 1) (C (cell ring s (ψ - 2 + 1)))) :
    (step1 hψ (by omega) ring C (cell ring s (ψ - 2)) (cell ring s (ψ - 2))).core.core.leader = true ∨
      (step1 hψ (by omega) ring C (cell ring s (ψ - 2)) (cell ring s (ψ - 2 + 1))).core.core.leader = true := by
  have hne : ring.rightNeighbor (cell ring s (ψ - 2)) ≠ cell ring s (ψ - 2) := by
    rw [right_cell]; exact cell_ne ring s (by omega) (by omega) (by omega)
  have eR := step1_right (κ := κ) (τ := τ) hψ (by omega) ring C (cell ring s (ψ - 2)) hne
  have eL := step1_left (κ := κ) (τ := τ) hψ (by omega) ring C (cell ring s (ψ - 2))
  rw [right_cell] at eR eL
  rw [eR, eL]
  obtain ⟨bl, hlp⟩ := hl.path
  exact BirthCheckPermitRepairBirth.r1_terminal_edge_leader hψ (by omega) (C (cell ring s (ψ - 2)))
    (C (cell ring s (ψ - 2 + 1))) (ψ - 2) bl (cons_label hψ (by omega) _ _ hl.label hr.label) hl.leader hr.leader
    hlp hl.label (by omega) hr.openMatch hr.label hl.equal hl.path2 hr.notProduce hr.notDone hr.notEliminate
    hr.notToss hr.notCongest hl.reset hr.reset (fun h => absurd h (by omega)) hr.path5

/-- The ordered internal edges of the train window. -/
def trainRequests (ring : DirectedRing n) (s : Fin n) (ψ : Nat) : List (Fin n) :=
  (List.range' 0 (ψ - 1)).map (cell ring s)

theorem chain_tail (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n) (C0 : FC n ψ κ τ) (s : Fin n)
    (hready : ∀ k, k < ψ → ReadyCell k (C0 (cell ring s k))) :
    ∀ (j m : Nat) (D : FC n ψ κ τ), m + j = ψ - 2 → 1 ≤ m → EqualCell m (D (cell ring s m)) →
      (∀ k, m < k → k < ψ → D (cell ring s k) = C0 (cell ring s k)) →
      ∃ k, k < ψ ∧ (((List.range' m (j + 1)).map (cell ring s)).foldl (step1 hψ (by omega) ring) D
        (cell ring s k)).core.core.leader = true := by
  intro j
  induction j with
  | zero =>
      intro m D hmj _ hD hsame
      have hm' : m = ψ - 2 := by omega
      subst hm'
      rw [List.range'_succ, List.range'_zero, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      have hr : ReadyCell (ψ - 2 + 1) (D (cell ring s (ψ - 2 + 1))) := by
        rw [hsame (ψ - 2 + 1) (by omega) (by omega)]; exact hready _ (by omega)
      rcases ring_terminal_row hψ h3 ring hψn D s hD hr with h | h
      · exact ⟨ψ - 2, by omega, h⟩
      · exact ⟨ψ - 2 + 1, by omega, h⟩
  | succ j ih =>
      intro m D hmj hm1 hD hsame
      rw [List.range'_succ, List.map_cons, List.foldl_cons]
      have hr : ReadyCell (m + 1) (D (cell ring s (m + 1))) := by
        rw [hsame (m + 1) (by omega) (by omega)]; exact hready _ (by omega)
      have hE := ring_chain_row hψ (by omega) ring hψn D s m hm1 (by omega) hD hr
      refine ih (m + 1) _ (by omega) (by omega) hE ?_
      intro k hk hkψ
      have h1 : cell ring s k ≠ cell ring s m := cell_ne ring s (by omega) (by omega) (by omega)
      have h2 : cell ring s k ≠ ring.rightNeighbor (cell ring s m) := by
        rw [right_cell]; exact cell_ne ring s (by omega) (by omega) (by omega)
      rw [step1_other hψ (by omega) ring D _ _ h1 h2]
      exact hsame k (by omega) hkψ

/-- From a window of ready cells (psi at least three, at most n), the ordered train requests create a leader on a
window cell. -/
theorem train_requests_leader (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n) (C : FC n ψ κ τ)
    (s : Fin n) (hready : ∀ k, k < ψ → ReadyCell k (C (cell ring s k))) :
    ∃ k, k < ψ ∧ ((trainRequests ring s ψ).foldl (step1 hψ (by omega) ring) C (cell ring s k)).core.core.leader =
      true := by
  obtain ⟨j, hj⟩ : ∃ j, ψ - 1 = (j + 1) + 1 := ⟨ψ - 3, by omega⟩
  unfold trainRequests
  rw [hj, List.range'_succ, List.map_cons, List.foldl_cons]
  have hE := ring_first_row (κ := κ) (τ := τ) hψ h3 ring (by omega) C s (hready 0 (by omega)) (hready 1 (by omega))
  refine chain_tail hψ h3 ring hψn C s hready j 1 _ (by omega) (Nat.le_refl 1) hE ?_
  intro k hk hkψ
  have h1 : cell ring s k ≠ cell ring s 0 := cell_ne ring s (by omega) (by omega) (by omega)
  have h2 : cell ring s k ≠ ring.rightNeighbor (cell ring s 0) := by
    rw [right_cell]; exact cell_ne ring s (by omega) (by omega) (by omega)
  exact step1_other hψ (by omega) ring C _ _ h1 h2

end BirthCheckChainR1Ring

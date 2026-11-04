import Leader.Wu.ZeroDivisible.EliminationResponder
import Leader.Wu.ZeroDivisible.GroupPreparationWord
import Leader.Wu.ZeroDivisible.TrafficRank

/-! A pending eliminated responder anywhere on a directed ring has a one-edge
actual R5 target word. No physical-label or auxiliary-field premise is used. -/
namespace PPLLAstraR5EliminationWord
open PPLL PPLLAstraR5Repair PPLLAstraR5ResetDrain PPLLAstraR5PrepWord
set_option autoImplicit false

private theorem right_left {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

/-- A globally occupied non-producer/non-done configuration with any E state
has an actual one-edge target word. -/
theorem elimination_target_word {n ψ : Nat} (hp : 0<ψ) (κ : Nat)
    (c : Cfg) (ring : DirectedRing n) (hn : 1<n)
    (C : Fin n → AgentState ψ)
    (hf : ∀ i, (C i).path ≠ .bot)
    (hnp : ∀ i, (C i).state ≠ .produce)
    (hnd : ∀ i, (C i).state ≠ .done)
    (he : ∃ i, (C i).state = .eliminate_signal) :
    ∃ w : List (Fin n), w.length = 1 ∧
      (protocol hp κ c).Reachable ring C (run hp κ c ring C w) ∧
      Target (run hp κ c ring C w) := by
  obtain ⟨i,hi⟩ := he
  let e := ring.leftNeighbor i
  have hr : ring.rightNeighbor e = i := right_left ring i
  have hne : ring.rightNeighbor e ≠ e :=
    PPLLAstraR5GlobalTraffic.rightNeighbor_ne ring hn e
  have hnie : i ≠ e := by simpa only [hr] using hne
  have hx := PPLLAstraR5EliminationResponder.pipeline_elimination_responder_hole
    hp κ c (C e) (C i) (hf e) (hf i) (hnp e) (hnd e) hi
  have ht : Target (run hp κ c ring C [e]) := by
    rcases hx with h | h
    · exact Or.inr ⟨e, by simpa [run, PopulationProtocol.step,
        PPLLAstraR5ResetDrain.protocol, hr] using h⟩
    · exact Or.inr ⟨i, by simpa [run, PopulationProtocol.step,
        PPLLAstraR5ResetDrain.protocol, hr, hne, hnie] using h⟩
  exact ⟨[e], by simp, run_reachable hp κ c ring C [e], ht⟩

#check elimination_target_word
#print axioms elimination_target_word
end PPLLAstraR5EliminationWord

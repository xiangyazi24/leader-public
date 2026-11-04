import Leader.Wu.ZeroDivisible.TrafficRank
import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.ZeroDivisible.TrafficMove
import Leader.Wu.ZeroDivisible.CompareBState
import Leader.Wu.ZeroDivisible.CompareRank
import Leader.Wu.ZeroDivisible.CompareTokenFrame
import Leader.Wu.ZeroDivisible.MiddleCut
import Leader.Wu.ZeroDivisible.ServiceEntry
import Leader.Wu.ZeroDivisible.ResetDrain
import Leader.Wu.ZeroDivisible.OccupiedPathFrame
import Leader.Wu.ZeroDivisible.TerminalDrain

/-! Public one-row discharge of a stored-label terminal elimination state.
Only physical labels and absence of PRODUCE are required. -/
namespace PPLLAstraR5CleanTerminalExit
open PPLL PPLLAstraR5Repair PPLLAstraR5ResetDrain
set_option autoImplicit false

private theorem size_gt_one {q ψ : Nat} (h4 : 4≤ψ)
    (ring : DirectedRing (q*ψ)) : 1<q*ψ := by
  have hq : 1≤q := by
    by_cases hz : q=0
    · have hn := ring.hn; simp [hz] at hn
    · omega
  have hm := Nat.mul_le_mul_right ψ hq
  simp only [Nat.one_mul] at hm
  omega

/-- The incoming physical edge of the stored-label terminal E creates an
actual main-path hole at that terminal. -/
theorem terminal_hole_row {q ψ : Nat} (h4 : 4≤ψ) (hp : 0<ψ)
    (κ : Nat) (c : Cfg) (ring : DirectedRing (q*ψ))
    (C : Fin (q*ψ) → AgentState ψ)
    (hlabels : ∀ x, (C x).label.val=x.val%ψ)
    (hnp : ∀ x, (C x).state≠.produce)
    (i : Fin (q*ψ)) (hit : (C i).label.val+1=ψ)
    (his : (C i).state=.eliminate_signal) :
    (run hp κ c ring C [ring.leftNeighbor i] i).path=.bot := by
  let e := ring.leftNeighbor i
  have hr : ring.rightNeighbor e=i := PPLLAstraR5GlobalTraffic.right_left ring i
  have adj := PPLLAstraR5GlobalTraffic.physical_adj hp ring C hlabels e
  unfold PPLLAstraR5TrafficMove.Adj at adj
  rw [hr] at adj
  have llt := (C e).label.isLt
  have lp : (C e).label.val=ψ-2 := by
    by_cases h : (C e).label.val+1<ψ
    · rw [Nat.mod_eq_of_lt h] at adj
      omega
    · have ht : (C e).label.val+1=ψ := by omega
      rw [ht,Nat.mod_self] at adj
      omega
  have hh := PPLLAstraR5TerminalDrain.terminal_drain hp κ c (C e) (C i)
    h4 lp (by omega) his (hnp e)
  have hne : i≠e := hr ▸ PPLLAstraR5GlobalTraffic.rightNeighbor_ne ring
    (size_gt_one h4 ring) e
  simpa [e,run,PopulationProtocol.step,PPLLAstraR5ResetDrain.protocol,hr,hne] using hh

/-- A single actual physical service is reachable and creates a hole. -/
theorem terminal_exit_word {q ψ : Nat} (h4 : 4≤ψ) (hp : 0<ψ)
    (κ : Nat) (c : Cfg) (ring : DirectedRing (q*ψ))
    (C : Fin (q*ψ) → AgentState ψ)
    (hlabels : ∀ i, (C i).label.val=i.val%ψ)
    (hnp : ∀ i, (C i).state≠.produce)
    (he : ∃ i, (C i).label.val+1=ψ ∧ (C i).state=.eliminate_signal) :
    ∃ e : Fin (q*ψ),
      (protocol hp κ c).Reachable ring C (run hp κ c ring C [e]) ∧
      ∃ i, (run hp κ c ring C [e] i).path=.bot := by
  obtain ⟨i,hit,his⟩ := he
  refine ⟨ring.leftNeighbor i,run_reachable hp κ c ring C _,i,?_⟩
  exact terminal_hole_row h4 hp κ c ring C hlabels hnp i hit his

#check terminal_hole_row
#print axioms terminal_hole_row
#check terminal_exit_word
#print axioms terminal_exit_word
end PPLLAstraR5CleanTerminalExit

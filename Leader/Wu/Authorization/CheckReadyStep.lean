import Leader.Wu.Authorization.CheckReadyCleanFrame

/-!
# A consumer interface for one nonterminal CHECK-ready boundary step

The ready-row frame is combined with the accepted full-pipeline label/reset
facts. A newly created leader is an explicit target, so the continuing case
has the follower, reset and label hypotheses needed by the next physical edge.
This does not yet handle an equal responder or the terminal boundary.
-/
namespace PPLLAuthCheckComponentStep

open PPLL PPLLAuthF PPLLAuthCheckComponent PPLLAuthCheckComponentFrame
set_option autoImplicit false
variable {ψ : Nat}

/-- The local stopping target uses the actual complete row output. -/
def Target (q : AuthState ψ × AuthState ψ) : Prop :=
  q.1.core.leader = true ∨ q.2.core.leader = true ∨ PairHole q

/-- All endpoint facts a subsequent physical-edge induction may consume.
The comparison result includes both original lineage links via `Released`. -/
structure Continuing (l r : AuthState ψ) (q : AuthState ψ × AuthState ψ) : Prop where
  released : Released l r q
  left_label : q.1.core.label = l.core.label
  right_label : q.2.core.label = r.core.label
  left_reset : q.1.core.reset_cmd = false
  right_reset : q.2.core.reset_cmd = false
  left_follower : q.1.core.leader = false
  right_follower : q.2.core.leader = false

/-- One ready-boundary row reaches the ordinary target or supplies the complete
local frame for a subsequent step. Echo, lottery bits and CLEAN records remain
arbitrary. The follower facts come from excluding the leader target, not from
an added input assumption about the row's result. -/
theorem ready_step (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    Target q ∨ Continuing l r q := by
  let q := PPLLAuthF.pipeline hp κ cfg l r
  by_cases hl : q.1.core.leader = true
  · exact Or.inl (Or.inl hl)
  by_cases hr : q.2.core.leader = true
  · exact Or.inl (Or.inr (Or.inl hr))
  have hlf : q.1.core.leader = false := by cases he : q.1.core.leader <;> simp_all
  have hrf : q.2.core.leader = false := by cases he : q.2.core.leader <;> simp_all
  rcases pipeline_ready_or_hole hp κ l r k bl br h with hh | hc
  · exact Or.inl (Or.inr (Or.inr hh))
  · have hn : r.core.label = ⟨(l.core.label.val+1)%ψ,Nat.mod_lt _ hp⟩ := by
      apply Fin.ext
      change r.core.label.val = (l.core.label.val+1)%ψ
      rw [h.rk,h.lk,Nat.mod_eq_of_lt]
      have hi := h.interior
      omega
    have hs := PPLLAuthGenDrain.row_std hp κ cfg l r h.ll h.rl h.lr h.rr hn hrf
    exact Or.inr ⟨hc,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hlf,hrf⟩

#print axioms ready_step
end PPLLAuthCheckComponentStep

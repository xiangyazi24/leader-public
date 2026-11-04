import Leader.Wu.ZeroDivisible.CompareBState
import Leader.Wu.ZeroDivisible.SelectedWaveCut


/-!
# Token frame before stray-reader deletion

This module follows the literal maintain/completeWave/wave prefix. Successor
carried path labels exclude both boundary emitters on internal edges. At the
wrap edge, the B role states and a live token make all three stages inert.
The result does not assume physical/path label agreement, followers, token
field bounds, or auxiliary cleanliness. Rank consumers separately provide
own-path agreement for the reader landers.
-/
namespace PPLLAstraR5CompareTokenFrame


open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2
open PPLLPostElectionGuard PPLLFableDesignR1
open PPLLAstraDesign2 PPLLAstraDesign3
open PPLLAstraR5CompareB
open PPLLAstraR5SelectedWave


set_option autoImplicit false
set_option linter.unusedSimpArgs false


/-- The holder projection needed to transport the shared traffic rank. -/
structure Frame {ψ : Nat} (a b : AgentState ψ) : Prop where
  label : a.label = b.label
  path  : a.path = b.path
  token : a.path2 = b.path2


@[simp] private theorem frame_iff {ψ : Nat} (a b : AgentState ψ) :
    Frame a b ↔ a.label=b.label ∧ a.path=b.path ∧ a.path2=b.path2 := by
  constructor
  · intro h; exact ⟨h.label,h.path,h.token⟩
  · rintro ⟨h1,h2,h3⟩; exact ⟨h1,h2,h3⟩

private theorem Frame.trans {ψ : Nat} {a b c : AgentState ψ}
    (h1 : Frame a b) (h2 : Frame b c) : Frame a c :=
  ⟨h1.label.trans h2.label,
   h1.path.trans h2.path,
   h1.token.trans h2.token⟩


/-- Literal R1 prefix immediately before dropStray. -/
def beforeDrop {ψ : Nat} (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := maintain l r
  let q := completeWave q.1 q.2
  wave q.1 q.2


private def view {ψ : Nat} (u : AgentState ψ) := (u.label,u.path,u.path2)
private theorem frame_view {ψ : Nat} (u v : AgentState ψ) :
    Frame u v ↔ view u = view v := by simp [view,frame_iff]
private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem view_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    view (if p then a else b) = if p then view a else view b := by split <;> rfl

private theorem maintain_frame {ψ : Nat} (l r : AgentState ψ) :
    Frame (maintain l r).1 l ∧
    Frame (maintain l r).2 r := by
  simp only [frame_view]
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [maintain, hl, hr, fst_ite, snd_ite, view_ite]
  all_goals repeat (split <;> simp_all [view])
  all_goals grind

private theorem completeWave_frame {ψ : Nat} (l r : AgentState ψ) :
    Frame (completeWave l r).1 l ∧
    Frame (completeWave l r).2 r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [completeWave, hl, hr, Frame] <;>
    repeat (first | split <;> simp_all [Frame])


private theorem wave_nonboundary_frame
    {ψ j bL bR : Nat} (l r : AgentState ψ)
    (hj : j + 1 < ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some (j + 1) bR) :
    Frame (wave l r).1 l ∧ Frame (wave l r).2 r := by
  have hjlast : j ≠ ψ - 1 := by omega
  have hr0 : j + 1 ≠ 0 := by omega
  simp [wave, hpL, hpR, Frame, hjlast, hr0] <;>
    repeat (first | split <;> simp_all [Frame])


private theorem boundary_prepare_eq
    {ψ bL bR : Nat} (h4 : 4 ≤ ψ)
    (l r : AgentState ψ)
    (hpL : l.path = .some (ψ - 1) bL)
    (hpR : r.path = .some 0 bR)
    (hL : l.state = .compare2)
    (hR : HeadState r.state) :
    let q := maintain l r
    completeWave q.1 q.2 = (l,r) := by
  rcases hR with hR | hR <;>
    simp [maintain, completeWave, hpL, hpR, hL, hR,
      lockedState, lockerState, waveState,
      Nat.mod_eq_of_lt (show ψ - 1 < ψ by omega)] <;> grind


private theorem beforeDrop_boundary_eq
    {ψ bL bR : Nat} (h4 : 4 ≤ ψ)
    (l r : AgentState ψ)
    (hpL : l.path = .some (ψ - 1) bL)
    (hpR : r.path = .some 0 bR)
    (hL : l.state = .compare2)
    (hR : HeadState r.state)
    (ht : HasToken (l,r)) :
    beforeDrop l r = (l,r) := by
  have hp := boundary_prepare_eq h4 l r hpL hpR hL hR
  dsimp [beforeDrop]
  rw [hp]
  exact wave_eq_of_selected_cut (by omega) (l,r)
    ⟨bL, hpL⟩ ⟨bR, hpR⟩ ⟨hL, hR⟩ ht


/-- Exact token/path/label frame in B. Conditional wrap occupancy excludes
re-emission; all internal successor rows require no token restriction. -/
theorem beforeDrop_frame
    {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ)
    (l r : AgentState ψ)
    (hj : j < ψ)
    (hk : k = (j + 1) % ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some k bR)
    (hBL : BState ψ j l.state)
    (hBR : BState ψ k r.state)
    (hboundary : j + 1 = ψ → HasToken (l,r)) :
    let q := beforeDrop l r
    Frame q.1 l ∧ Frame q.2 r := by
  dsimp only
  by_cases ht : j + 1 = ψ
  · have hjlast : j = ψ - 1 := by omega
    have hk0 : k = 0 := by
      rw [hk, ht, Nat.mod_self]
    subst j
    subst k
    have hL : l.state = .compare2 := by
      exact (bState_terminal (by omega) (by omega)).mp hBL
    have hR : HeadState r.state := bState_zero.mp hBR
    have heq := beforeDrop_boundary_eq h4 l r hpL hpR hL hR
      (hboundary (by omega))
    rw [heq]
    exact ⟨⟨rfl,rfl,rfl⟩, ⟨rfl,rfl,rfl⟩⟩
  · have hj1 : j + 1 < ψ := by omega
    have hk' : k = j + 1 := by
      rw [hk, Nat.mod_eq_of_lt hj1]
    subst k
    let m := maintain l r
    let c := completeWave m.1 m.2
    have hm := maintain_frame l r
    have hc := completeWave_frame m.1 m.2
    have hpLm : m.1.path = l.path := hm.1.path
    have hpRm : m.2.path = r.path := hm.2.path
    have hpLc : c.1.path = l.path := hc.1.path.trans hpLm
    have hpRc : c.2.path = r.path := hc.2.path.trans hpRm
    have hw := wave_nonboundary_frame c.1 c.2 hj1
      (by simpa [hpL] using hpLc)
      (by simpa [hpR, Nat.mod_eq_of_lt hj1] using hpRc)
    exact ⟨hw.1.trans (hc.1.trans hm.1),
      hw.2.trans (hc.2.trans hm.2)⟩


end PPLLAstraR5CompareTokenFrame
#print axioms PPLLAstraR5CompareTokenFrame.beforeDrop_frame

import Leader.Wu.ZeroDivisible.PathIndexBreak

/-! An incoming eliminated responder creates an actual one-row path hole. -/
namespace PPLLAstraR5EliminationResponder
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3
open PPLLAstraR5Repair PPLLAstraR5Repair.ServiceEntry
set_option autoImplicit false
set_option linter.unusedSimpArgs false

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by split <;> rfl
private theorem state_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by split <;> rfl
private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl

namespace Prefix
private def view {ψ : Nat} (u : AgentState ψ) := (u.label,u.state)
private theorem view_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    view (if p then a else b) = if p then view a else view b := by split <;> rfl
private theorem path4_view {ψ : Nat} (u : AgentState ψ) : view {u with path4 := none} = view u := rfl
private theorem path5_view {ψ : Nat} (u : AgentState ψ) : view {u with path5 := none} = view u := rfl

private theorem cleanSigGenConnect_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigGenConnect u)) = (view u) := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem cleanSigCleanApply_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigCleanApply u)) = (view u) := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [view_ite, view, label_ite, state_ite]

private theorem clean3_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep3 l r).1) = (view l) ∧
    (view (cleanSigStep3 l r).2) = (view r) := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean4_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep4 l r).1) = (view l) ∧
    (view (cleanSigStep4 l r).2) = (view r) := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean5_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep5 hψ l r).1) = (view l) ∧
    (view (cleanSigStep5 hψ l r).2) = (view r) := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean6_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep6 hψ l r).1) = (view l) ∧
    (view (cleanSigStep6 hψ l r).2) = (view r) := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean_views {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (view (cleanSig hψ l r).1) = (view l) ∧
    (view (cleanSig hψ l r).2) = (view r) := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_view, cleanSigCleanApply_view,
    (clean3_views _ _).1, (clean3_views _ _).2,
    (clean4_views _ _).1, (clean4_views _ _).2,
    (clean5_views _ _ _).1, (clean5_views _ _ _).2,
    (clean6_views _ _ _).1, (clean6_views _ _ _).2, and_self]

private theorem cleanSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (cleanSource hp l r).1 = view l ∧ view (cleanSource hp l r).2 = view r := by
  simp only [cleanSource]
  simp only [fst_ite,snd_ite,view_ite,path4_view,path5_view,cleanSigGenConnect_view,cleanSigCleanApply_view,
    (clean3_views _ _).1,(clean3_views _ _).2,(clean4_views _ _).1,(clean4_views _ _).2,
    (clean5_views _ _ _).1,(clean5_views _ _ _).2,(clean6_views _ _ _).1,(clean6_views _ _ _).2,ite_self,and_self]

end Prefix

private theorem release_E {ψ : Nat} (hp : 0<ψ) (l r : AgentState ψ)
    (he : r.state = .eliminate_signal) :
    (releaseSource hp l r).2.state = .eliminate_signal := by
  simp [releaseSource,he]

private theorem eliminate_right_hole {ψ : Nat} (hp : 0<ψ) (l r : AgentState ψ)
    (he : r.state = .eliminate_signal) :
    (eliminateSig hp l r).2.path = .bot := by
  simp [eliminateSig,he]

private theorem moveEntry_factor {ψ : Nat} (hp : 0<ψ) (κ : Nat)
    (l r : AgentState ψ) :
    moveEntry hp κ l r =
      let p := pPsiProbeWall hp l r
      let g := PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2
      let c := cleanSource hp g.1 g.2
      let d := releaseSource hp c.1 c.2
      eliminateSig hp d.1 d.2 := rfl

private def RightHole {ψ : Nat} (q : AgentState ψ × AgentState ψ) : Prop :=
  q.2.path = .bot
private theorem rightHole_iff {ψ : Nat} (q : AgentState ψ × AgentState ψ) :
    RightHole q ↔ q.2.path = .bot := Iff.rfl
attribute [local irreducible] RightHole
attribute [local irreducible] PPLLAstraR5Repair.ServiceEntry.moveEntry

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem moveEntry_right_hole {ψ : Nat} (hp : 0<ψ) (κ : Nat)
    (l r : AgentState ψ)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hld : l.state ≠ .done)
    (he : r.state = .eliminate_signal) :
    RightHole (moveEntry hp κ l r) := by
  let p := pPsiProbeWall hp l r
  let g := PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2
  let c := cleanSource hp g.1 g.2
  let d := releaseSource hp c.1 c.2
  have hcore := PPLLAstraR5PathIndexBreak.preclean_core hp κ l r
    hlp hrp hls hld (by simp [he])
  have hgs : g.2.state = .eliminate_signal := by
    have h := congrArg Prod.fst hcore.2
    change g.2.state = r.state at h
    exact h.trans he
  have hc := Prefix.cleanSource_views hp g.1 g.2
  change (c.1.label,c.1.state)=(g.1.label,g.1.state) ∧
      (c.2.label,c.2.state)=(g.2.label,g.2.state) at hc
  have hcs : c.2.state = .eliminate_signal := by
    have h := congrArg Prod.snd hc.2
    exact h.trans hgs
  have hds : d.2.state = .eliminate_signal := release_E hp c.1 c.2 hcs
  have hcut : RightHole (eliminateSig hp d.1 d.2) :=
    (rightHole_iff _).2 (eliminate_right_hole hp d.1 d.2 hds)
  rw [moveEntry_factor]
  exact hcut

attribute [local irreducible] PPLLAstraR5Repair.ServiceEntry.afterEntry
  PPLLAstraR5Repair.pipeline

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- An actual R5 row with an occupied pending eliminated responder
creates a main-path hole at any physical label. -/
theorem pipeline_elimination_responder_hole {ψ : Nat} (hp : 0<ψ) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hlp : l.path ≠ .bot) (hrp : r.path ≠ .bot)
    (hls : l.state ≠ .produce) (hld : l.state ≠ .done)
    (he : r.state = .eliminate_signal) :
    (pipeline hp κ c l r).1.path = .bot ∨
    (pipeline hp κ c l r).2.path = .bot := by
  rw [ServiceEntry.pipeline_factor]
  exact ServiceEntry.afterEntry_pairHole hp κ c l r
    (moveEntry hp κ l r).1 (moveEntry hp κ l r).2
    (Or.inr (by
      have hh := moveEntry_right_hole hp κ l r hlp hrp hls hld he
      exact (rightHole_iff _).1 hh))

#check pipeline_elimination_responder_hole
#print axioms pipeline_elimination_responder_hole
end PPLLAstraR5EliminationResponder

import Leader.L4.BStarAcquireGlobalChain

namespace L4.BStarAcquireChainEndpoints
open AllSizeProtocol BStarLongClaims BStarAcquireRailCoverage BStarLongCommand

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

private def checks (g : Pair LongGeometry) (C : CommandClaim) : Bool :=
  match C.destination with
  | some D =>
    active (geometry g C.source.side) C.source.occurrence &&
    active (geometry g D.side) D.occurrence &&
    !(C.source.side == .right && g.2.axes.h6 && C.source.occurrence.val == 10) &&
    !(C.source.side == .left && C.source.occurrence.val == 10 && g.1.axes.h6) &&
    !(D.side == .right && D.occurrence.val == 0 && g.2.axes.h6) &&
    !(D.side == .left && D.occurrence.val == 0 && g.1.axes.h6)
  | none =>
    (C.source.side == .right && g.2.axes.h6) &&
    ((C.kind == .terminal && C.source.occurrence.val == 10) ||
      (C.kind == .door && C.source.occurrence.val == 0))

private theorem checked (g : Pair LongGeometry) (C : CommandClaim)
    (hC : C ∈ orderedCommands g) : checks g C=true := by
  obtain ⟨x,y⟩ := g
  let g := (geo x.axes.h6 x.inside x.last,geo y.axes.h6 y.inside false)
  have F (xh xi xl yh yi : Bool) :
      (commandClaims (geo xh xi xl,geo yh yi false)).all
        (checks (geo xh xi xl,geo yh yi false))=true := by
    cases xh <;> cases xi <;> cases xl <;> cases yh <;> cases yi <;> decide +kernel
  have E : commandClaims (x,y)=commandClaims g := rfl
  have raw := BStarLongFenceTopology.selected_command_raw _ _ hC
  rw [E] at raw
  have h := List.all_eq_true.mp (F x.axes.h6 x.inside x.last y.axes.h6 y.inside) C raw
  change checks g C=true at h
  suffices eq : checks (x,y) C=checks g C by rwa [eq]
  rcases C with ⟨k,⟨s,j⟩,d⟩
  cases s <;> cases d
  all_goals try rfl
  all_goals rename_i v; rcases v with ⟨v,k⟩; cases v <;> rfl

/-- Both ends of every selected literal link are active. A link can
neither leave an H6 K10 nor enter an H6 K0. -/
theorem link_endpoints (g : Pair LongGeometry) (C : CommandClaim) (D : At (Fin 11))
    (hC : C∈orderedCommands g) (hD : C.destination=some D) :
    active (geometry g C.source.side) C.source.occurrence=true ∧
    active (geometry g D.side) D.occurrence=true ∧
    ¬ ((geometry g C.source.side).axes.h6=true ∧ C.source.occurrence.val=10) ∧
    ¬ ((geometry g D.side).axes.h6=true ∧ D.occurrence.val=0) := by
  have H := checked g C hC
  rcases g with ⟨x,y⟩
  cases S : C.source.side <;> cases T : D.side <;>
    simp [checks,hD,geometry,S,T] at H ⊢ <;> grind

/-- The sole non-door selected claim without a destination is
the terminal at old-right H6 K10. -/
theorem terminal (g : Pair LongGeometry) (C : CommandClaim)
    (hC : C∈orderedCommands g) (hD : C.destination=none) (hn : C.kind≠.door) :
    C.kind=.terminal ∧ C.source.side=.right ∧ g.2.axes.h6=true ∧
    C.source.occurrence.val=10 := by
  have H := checked g C hC
  simp [checks,hD,hn] at H
  exact ⟨H.2.1,H.1.1,H.1.2,H.2.2⟩

end L4.BStarAcquireChainEndpoints

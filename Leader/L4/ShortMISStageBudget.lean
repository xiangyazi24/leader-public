import Leader.L4.ShortSheetRankClock
import Leader.L4.ShortInheritedRankParam
import Leader.L4.ShortLayerGeometry
import Leader.L4.ShortSimulLocal

namespace L4.ShortMISStageBudget
open AllSizeProtocol PhysicalCustody PhysicalShortSheet ShortSheetRankClock
open ShortResetChart ShortResetCycle ShortResetWatch ShortPhaseRank
open ShortInheritedRankParam ShortControllerEntrance

theorem rail_cap_formula (D : Nat) :
    railCap D = 2*D^2+1+D*(4*D+2) := by
  simp only [railCap,Nat.pow_two,Nat.mul_assoc]

theorem phase_cap_formula (D : Nat) :
    phaseCap D=16*railCap D+15 := by
  unfold phaseCap
  rw [Nat.mul_add,Nat.mul_one,Nat.succ_mul]
  omega

def resetCost (D : Nat) : Nat := (D+1)^(phaseCap D)+(2*D+1)

def stageCoefficient (D : Nat) : Nat := 3+resetCost D

theorem mis1_constants :
    railCap 9=505 ∧ phaseCap 9=8095 ∧ (2*9+1 : Nat)=19 :=
  ⟨by decide,by decide,by decide⟩

private theorem coeff_as (D q B R : Nat)
    (Q : D+1=q) (E : phaseCap D=B) (W : 2*D+1=R) :
    stageCoefficient D=3+(q^B+R) := by
  unfold stageCoefficient resetCost
  rw [Q,E,W]

theorem h3_coefficient :
    stageCoefficient 27=3+((28 : Nat)^70879+55) :=
  coeff_as 27 28 70879 55 (by decide) (by decide) (by decide)

theorem h4_coefficient :
    stageCoefficient 81=3+((82 : Nat)^632479+163) :=
  coeff_as 81 82 632479 163 (by decide) (by decide) (by decide)

/-- These are the exact local descent obligations on a chosen sheet.
The second case retains the actual controller rank: a lower rail
alone does not suffice if the controller changes. -/
structure RankRows {s n : Nat} (j : Sheet) {h : Fin n → Bool}
    (C : Chart h) (D : Nat) (Q : Raw s n → Prop) : Prop where
  descent : ∀ x, Q x → pc (rootByte C (project j C x))≠8 →
    (∃ e∈watch C, chartDebt C (project j C (rawNext s x e))<chartDebt C (project j C x)) ∨
    (∃ e∈watch C, chartDebt C (project j C (rawNext s x e))=chartDebt C (project j C x) ∧
      rail C D (project j C (rawNext s x e))<rail C D (project j C x))

theorem sheet_issue0_expected {s n D : Nat} (j : Sheet) {h : Fin n → Bool}
    (C : Chart h) (small : C.L≤D) (Q : Raw s n → Prop)
    (closed : ∀ z e, Q z → Q (rawNext s z e))
    (laws : RankRows j C D Q) (x : Raw s n) (X : Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun y => pc (rootByte C (project j C y))=8) x (n*(D+1)^(phaseCap D)) := by
  refine ShortSheetRankClock.chart_expected j C small Q _ closed
    (chartRank C (railCap D) (rail C D)) (fun z _=>chartRank_cap C _ _ _ (rail_cap C D small _))
    ?_ x X
  intro z Z notIssue
  rcases laws.descent z Z notIssue with ⟨e,H,drop⟩|⟨e,H,same,drop⟩
  · exact ⟨e,H,chartRank_phase_drop C _ _ _ _ (rail_cap C D small _) drop⟩
  · exact ⟨e,H,chartRank_rail_drop C _ _ _ _ same drop⟩

/-- A literal MIS1 instance of all the local rank obligations. MIS2
and MIS3 have exactly the same target/rank forms, but need their own
one-step readiness and nominations on their certified lower masks. -/
theorem mis1_rank_rows {s n D : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (small : C.L≤D) (Nom : ShortInheritedRank.ForwardNomination (s:=s) C) :
    RankRows .mis1 C D (fun x : Raw s n => H2Ready x ∧ ∀ i, ShortResetMIS1Ring.header x i=h i) := by
  constructor
  intro x X off
  have H : ShortResetMIS1Ring.header x C.root=true := (X.2 C.root).trans C.rootHeader
  have no : pc (x C.root).mis1≠8 := off
  rcases phase_choice C N x H no with drop|⟨o,_,W,Held⟩
  · exact .inl ⟨_,ShortSimulLocal.door_mem C,drop⟩
  · obtain ⟨e,E,noDoor,drop⟩ := rail_nominate_held C D small N Nom x X.1 X.2 Held
    exact .inr ⟨e,E,debt_nondoor C x e o H W noDoor,drop⟩

theorem mis1_sheet_fiber {s n : Nat} (x0 : Raw s n) (X0 : H2Ready x0)
    (N : 9<n) :
    SheetFiber .mis1 (ShortResetMIS1Ring.header x0)
      (fun x : Raw s n => H2Ready x ∧
        ∀ i, ShortResetMIS1Ring.header x i=ShortResetMIS1Ring.header x0 i) 9 := by
  constructor
  · intro x e X
    exact ⟨h2_ready_closed (by omega) x e X.1,fun i=>
      (H1.raw_h1_selected_frozen (by omega) x e i X.1.1).trans (X.2 i)⟩
  · intro x X
    exact funext X.2
  · intro x X i p
    have Z := h2_ready_gate X.1 i p
    change MISByteCodec.atGate (ShortResetMIS1Ring.header x i) (x i).mis1 p = true ↔
      p.val=1 ∧ ShortResetMIS1Ring.header x i=true at Z
    rw [X.2 i] at Z
    exact Z.trans (and_congr_left fun _ => ⟨fun E=>Fin.ext E,fun E=>congrArg Fin.val E⟩)
  · intro q H
    exact ShortLayerGeometry.mis1_chart x0 X0.1 N q H

/-- The two input means are already for the actual raw process. This
is the arithmetic/stopped-stage composition, not a proof of either
later-sheet protocol premise. -/
theorem conditional_stage_budget {s n : Nat} (D : Nat)
    (A target : Raw s n → Prop) (x : Raw s n)
    (prep : L4.IIDExpectedHittingTimeAtMost (rawNext s) A x (3*n^2))
    (service : ∀ y, A y → L4.IIDExpectedHittingTimeAtMost (rawNext s) target y (resetCost D*n^2)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) target x (stageCoefficient D*n^2) := by
  rw [stageCoefficient,Nat.add_mul]
  exact AllSizeComposition.additive_stage (rawNext s) A target _ _ x prep service

#print axioms rail_cap_formula
#print axioms phase_cap_formula
#print axioms mis1_constants
#print axioms h3_coefficient
#print axioms h4_coefficient
#print axioms sheet_issue0_expected
#print axioms mis1_rank_rows
#print axioms mis1_sheet_fiber
#print axioms conditional_stage_budget
end L4.ShortMISStageBudget

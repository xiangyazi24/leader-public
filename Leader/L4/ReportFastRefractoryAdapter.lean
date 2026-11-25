import Leader.L4.ReportFastRefractory
import Leader.L4.ReportFastItem10Assembly

namespace L4.ReportFastItem10Assembly
open AllSizeProtocol PhysicalCustody Height ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners
open ReportGoodEightBank ReportFastOwnerSupport
open ReportFastRefractory ReportAdaptiveFibre ReportFastKernel ReportGateGeometry

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop} {Y : Type}

noncomputable def decision5 (d : Sheet) (C : Fin 5→Chart h)
    (x : Raw s n) (e : Fin n) : Nat :=
  (List.ofFn (fun j : Fin 5=>(firstDecision d (C j) x e).toNat)).sum

-- The finite multiplicity 2 implies a concrete active OLD gate.
-- This is the only relation needed between the observer's choice
-- count and the physical decisions. No choice need be made at all
-- other race1 gates, so inequality, not equality, is correct.
private theorem choice_at_most_decision (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (C : Fin 5→Chart h)
    (inj : Function.Injective (fun j=>center (C j)))
    (x : Raw s n) (a : Fin n)
    (ban : Fin n→Option (Fin n)) (active desired : Fin 5→Bool)
    (spec : ∀ e b,ban e=some b ↔
      ∃ j,active j=true ∧ e=label (center (C j)) (!desired j) ∧
        b=label (center (C j)) (desired j))
    (Armed : ∀ j,active j=true→
      ReportByteRows.healthyAdmit (params d s)
        (tok d (C j) x ((C j).a+2)) ∧
      (tok d (C j) x ((C j).a+2)).race=1) :
    (if fibre (fun _ : Unit=>mergeSide ban) () a=2 then 1 else 0)≤decision5 d C x a := by
  classical
  have F := pairs_from_centers hh G C inj active desired ban spec
  rw [gate_fibre ban F a]
  by_cases A : ban a=none
  · rw [if_pos A]
    by_cases B : ∃ b,ban b=some a
    · rw [if_pos B]
      obtain ⟨b,B⟩ := B
      obtain ⟨j,J,_,E⟩ := (spec b a).mp B
      have H : firstDecision d (C j) x a=true := by
        apply (decision_iff d (C j) x a).mpr
        refine ⟨(armed_iff d (C j) x).mpr (Armed j J),?_⟩
        rw [(physical_labels (C j)).1,(physical_labels (C j)).2]
        cases V : desired j
        · exact .inl (by simpa [V] using E)
        · exact .inr (by simpa [V] using E)
      have K (k : Fin 5) :
          (if j=k then 1 else 0)≤(firstDecision d (C k) x a).toNat := by
        by_cases L : j=k
        · subst k; simp [H]
        · simp [L]
      have V := sum_ofFn_le _ _ K
      rw [sum_delta j (fun _=>1)] at V
      simpa [decision5] using V
    · simp [B]
  · simp [A]

-- Sum counts along the SAME actual observer word. The generic
-- lemma is useful twice (ownerMark and firstDecision).
private theorem reward_is_raw_sum
    (next : Y→Fin n→Y) (Q : Y→Prop) (project : Y→Raw s n×Bool)
    (closed : ∀ y e,Q y→Q (next y e))
    (raw_step : ∀ y e,Q y→(project (next y e)).1=rawNext s (project y).1 e)
    (m : Fin 5→Raw s n→Fin n→Bool)
    (y : Y) (H : Q y) (u : List (Fin n)) :
    reward next (fun z e=>(List.ofFn (fun j : Fin 5=>
      (m j (project z).1 e).toNat)).sum) y u =
      (List.ofFn (fun j : Fin 5=>rawCount (m j) (project y).1 u)).sum := by
  induction u generalizing y with
  | nil => simp [reward,rawCount]
  | cons e u IH =>
    simp only [reward,rawCount]
    rw [IH (next y e) (closed y e H),raw_step y e H]
    rw [sum_ofFn_add]

private theorem choices_le_raw_decisions (d : Sheet)
    (hh : ∃ i,h i=true) (G : GapInput h) (C : Fin 5→Chart h)
    (inj : Function.Injective (fun j=>center (C j)))
    (next : Y→Fin n→Y) (Q : Y→Prop) (project : Y→Raw s n×Bool)
    (closed : ∀ y e,Q y→Q (next y e))
    (ban : Y→Fin n→Option (Fin n)) (active desired : Y→Fin 5→Bool)
    (spec : ∀ y,Q y→∀ e a,ban y e=some a ↔
      ∃ j,active y j=true ∧ e=label (center (C j)) (!desired y j) ∧
        a=label (center (C j)) (desired y j))
    (Armed : ∀ y,Q y→∀ j,active y j=true→
      ReportByteRows.healthyAdmit (params d s)
        (tok d (C j) (project y).1 ((C j).a+2)) ∧
      (tok d (C j) (project y).1 ((C j).a+2)).race=1)
    (y : Y) (H : Q y) (u : List (Fin n)) :
    choices next (fun z=>mergeSide (ban z)) y u≤
      reward next (fun z e=>decision5 d C (project z).1 e) y u := by
  induction u generalizing y with
  | nil => exact Nat.le_refl _
  | cons e u IH =>
    have A := choice_at_most_decision d hh G C inj (project y).1 e
      (ban y) (active y) (desired y) (spec y H) (Armed y H)
    have B := IH (next y e) (closed y e H)
    -- CHECK: fibre ignores the ambient state type after application
    -- (ReportAdaptiveFibre.lean:15–16). The Unit and Y sums agree by rfl.
    exact Nat.add_le_add A B

-- Stronger than the mapped-word field: all ordinary observer words.
theorem refractory_all_observer_words
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (C : Fin 5→Chart h) (M : ∀ j,C j∈ownerCharts G)
    (inj : Function.Injective (fun j=>center (C j)))
    (w : Nat) (Width : ∀ j,3*w≤(C j).L)
    (next : Y→Fin n→Y) (Q : Y→Prop) (project : Y→Raw s n×Bool)
    (closed : ∀ y e,Q y→Q (next y e))
    (bank : ∀ y,Q y→GoodEightBank d hh P G (project y).1)
    (raw_step : ∀ y e,Q y→(project (next y e)).1=rawNext s (project y).1 e)
    (ban : Y→Fin n→Option (Fin n)) (active desired : Y→Fin 5→Bool)
    (spec : ∀ y,Q y→∀ e a,ban y e=some a ↔
      ∃ j,active y j=true ∧ e=label (center (C j)) (!desired y j) ∧
        a=label (center (C j)) (desired y j))
    (Armed : ∀ y,Q y→∀ j,active y j=true→
      ReportByteRows.healthyAdmit (params d s)
        (tok d (C j) (project y).1 ((C j).a+2)) ∧
      (tok d (C j) (project y).1 ((C j).a+2)).race=1)
    (y : Y) (H : Q y) (u : List (Fin n)) :
    3*(params d s).digits*w*choices next (fun z=>mergeSide (ban z)) y u≤
      3*(params d s).digits*w*5+
        reward next (fun z e=>mark5 d C (project z).1 e) y u := by
  let R := 3*(params d s).digits*w
  let x := (project y).1
  let A := fun j : Fin 5=>rawCount (firstDecision d (C j)) x u
  let B := fun j : Fin 5=>rawCount (ownerMark d (C j)) x u
  have L (j : Fin 5) : R*A j≤R+B j :=
    refractory_from_strong d (C j) N hh G F digit w (Width j)
      x (bank y H).2.1.1.1.1 (serial_from_bank d N hh G F digit x (bank y H) (C j) (M j)) u
  have S := sum_ofFn_le _ _ L
  -- CHECK: these exact sum rewrites are from Height, as used in
  -- ReportAdaptiveProgress.one_reward:30 and ReportGatePairs:108–120.
  rw [sum_ofFn_mul_left,sum_ofFn_add,sum_ofFn_const] at S
  have C0 := choices_le_raw_decisions d hh G C inj next Q project closed
    ban active desired spec Armed y H u
  have C1 := reward_is_raw_sum next Q project closed raw_step
    (fun j=>firstDecision d (C j)) y H u
  have C2 := reward_is_raw_sum next Q project closed raw_step
    (fun j=>ownerMark d (C j)) y H u
  change reward next (fun z e=>decision5 d C (project z).1 e) y u=
      (List.ofFn A).sum at C1
  change reward next (fun z e=>mark5 d C (project z).1 e) y u=
      (List.ofFn B).sum at C2
  rw [C1] at C0
  change R*choices next (fun z=>mergeSide (ban z)) y u≤
    R*5+reward next (fun z e=>mark5 d C (project z).1 e) y u
  rw [C2,Nat.mul_comm R 5]
  exact Nat.le_trans (Nat.mul_le_mul_left R C0) S

-- EXACT PhaseRows.service_program_refractory_raw field.
-- No phase-debt, credit or nominate assumption occurs.
theorem service_program_refractory_raw
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (C : Fin 5→Chart h) (M : ∀ j,C j∈ownerCharts G)
    (inj : Function.Injective (fun j=>center (C j)))
    (w W : Nat) (Width : ∀ j,3*w≤(C j).L)
    (next : Y→Fin n→Y) (Q : Y→Prop) (project : Y→Raw s n×Bool)
    (closed : ∀ y e,Q y→Q (next y e))
    (bank : ∀ y,Q y→GoodEightBank d hh P G (project y).1)
    (raw_step : ∀ y e,Q y→(project (next y e)).1=rawNext s (project y).1 e)
    (ban : Y→Fin n→Option (Fin n)) (active desired : Y→Fin 5→Bool)
    (spec : ∀ y,Q y→∀ e a,ban y e=some a ↔
      ∃ j,active y j=true ∧ e=label (center (C j)) (!desired y j) ∧
        a=label (center (C j)) (desired y j))
    (Armed : ∀ y,Q y→∀ j,active y j=true→
      ReportByteRows.healthyAdmit (params d s)
        (tok d (C j) (project y).1 ((C j).a+2)) ∧
      (tok d (C j) (project y).1 ((C j).a+2)).race=1) :
    ∀ y,Q y→∀ v,v.length=block (params d s).digits W n→
      let u:=mapWord next (fun z=>mergeSide (ban z)) y v
      3*(params d s).digits*w*choices next (fun z=>mergeSide (ban z)) y u≤
        3*(params d s).digits*w*5+
          reward next (fun z e=>mark5 d C (project z).1 e) y u := by
  intro y H v _
  exact refractory_all_observer_words d N hh G F digit C M inj w Width
    next Q project closed bank raw_step ban active desired spec Armed y H
    (mapWord next (fun z=>mergeSide (ban z)) y v)

#print axioms refractory_all_observer_words
#print axioms service_program_refractory_raw
end L4.ReportFastItem10Assembly


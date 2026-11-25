import Leader.L4.ShortSheetProjection
import Leader.L4.ShortLayerStage
import Leader.L4.WatchedUnionIID

namespace L4.ShortSheetRankClock
open AllSizeProtocol PhysicalCustody PhysicalShortSheet
open ShortResetChart ShortResetCycle ShortResetWatch

/-- Static geometry and readiness on one fixed lower fibre. Gate
readiness does not assert that any upper packets are clean. -/
structure SheetFiber {s n : Nat} (j : Sheet) (h : Fin n → Bool)
    (Q : Raw s n → Prop) (D : Nat) : Prop where
  closed : ∀ x e, Q x → Q (rawNext s x e)
  mask : ∀ x, Q x → PhysicalShortSheet.mask j x=h
  acquireGate : ∀ (x : Raw s n), Q x → ∀ i p,
    MISByteCodec.atGate (h i) (bytes j (x i)) p=true ↔ p=1 ∧ h i=true
  chart : ∀ root, h root=true → ∃ C : Chart h, C.root=root ∧ C.L≤D

def project {s n : Nat} {h : Fin n → Bool} (j : Sheet) (C : Chart h)
    (x : Raw s n) : Fin C.L → BitVec 96 :=
  fun i => bytes j (x (nextAt C.root i.val))

theorem outside_project {s n : Nat} {h : Fin n → Bool} (j : Sheet) (C : Chart h)
    (x : Raw s n) (e : Fin n) (N : e ∉ watch C) :
    project j C (rawNext s x e)=project j C x := by
  apply funext
  intro i
  let q := nextAt C.root i.val
  have L : q≠e := fun E=>N ((watch_incident C e).mpr ⟨i.val,i.isLt,.inl E⟩)
  have R : q≠rightNeighbor e := fun E=>N ((watch_incident C e).mpr ⟨i.val,i.isLt,.inr E⟩)
  have A := congrFun (PhysicalShortSheet.exact_raw_step j x e) q
  change project j C (rawNext s x e) i = _
  exact A.trans (by simp only [sliceStep,if_neg L,if_neg R]; rfl)

theorem watch_bound {n : Nat} {h : Fin n → Bool} (C : Chart h) {D : Nat}
    (small : C.L≤D) : (watch C).length≤D+1 := by
  rw [watch_length]
  omega

/-- The cap changes the cardinality used for the clock, not the
physical labels sampled by the joined row. -/
theorem chart_expected {s n D B : Nat} {h : Fin n → Bool} (j : Sheet)
    (C : Chart h) (small : C.L≤D) (Q goal : Raw s n → Prop)
    (closed : ∀ x e, Q x → Q (rawNext s x e))
    (score : (Fin C.L → BitVec 96) → Nat)
    (bounded : ∀ x, Q x → score (project j C x)≤B)
    (nominate : ∀ x, Q x → ¬goal x → ∃ e∈watch C,
      score (project j C (rawNext s x e))<score (project j C x))
    (x : Raw s n) (X : Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) goal x (n*(D+1)^B) := by
  have d : 1<D+1 := by have := C.positive; omega
  let rank := fun (y : Raw s n) => score (project j C y)
  have kit : WatchedUnionIID.Spec (rawNext s) Q goal (watch C) B rank := by
    refine ⟨closed,bounded,?_,nominate,?_⟩
    · intro y Y Z
      by_cases no : goal y
      · exact no
      · obtain ⟨e,_,drop⟩ := nominate y Y no
        change score (project j C y)=0 at Z
        omega
    · intro y e _ _ E
      exact Nat.le_of_eq (congrArg score (outside_project j C y e E))
  exact WatchedUnionIID.expected d kit (watch_bound C small) x X

theorem charts_watch_bound {n D : Nat} {h : Fin n → Bool}
    (cs : List (Chart h)) (small : ∀ C∈cs, C.L≤D) :
    (WatchedUnionIID.chartsWatch cs).length≤(D+1)*cs.length := by
  induction cs with
  | nil => simp [WatchedUnionIID.chartsWatch]
  | cons C cs ih =>
    have H := watch_bound C (small C (by simp))
    have I := ih (fun E m=>small E (List.mem_cons_of_mem _ m))
    simp only [WatchedUnionIID.chartsWatch,List.flatMap_cons,List.length_append,List.length_cons]
    change (watch C).length+(WatchedUnionIID.chartsWatch cs).length≤_
    rw [Nat.mul_succ]
    omega

#print axioms outside_project
#print axioms watch_bound
#print axioms chart_expected
#print axioms charts_watch_bound
end L4.ShortSheetRankClock

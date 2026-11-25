import Leader.L4.ReportGatePairs
import Leader.L4.ReportAdaptiveProgress

namespace L4.ReportFastRawRelift
open ReportAdaptiveFibre

variable {n : Nat} {X Y : Type}

/-- Physical marks always execute the raw step. An excluded mark can only
discard the proof observer and reinitialize it over the actual raw result.
The projection may include the sticky classified-publication latch. -/
def step (real : X→Fin n→X) (observe : Y→Fin n→Y)
    (project : Y→X) (restore : X→Y)
    (ban : Y→Fin n→Option (Fin n)) (y : Y) (e : Fin n) : Y :=
  match ban y e with
  | none => observe y e
  | some _ => restore (real (project y) e)

theorem allowed_after_merge (ban : Fin n→Option (Fin n))
    (D : DisjointPairs ban) (e : Fin n) : ban (mergeSide ban e)=none := by
  cases B : ban e with
  | none => rw [easy_allowed ban e B,B]
  | some a => rw [desired_hit ban e a B,D.allowed_target e a B]

theorem agree_on_driver (real : X→Fin n→X) (observe : Y→Fin n→Y)
    (project : Y→X) (restore : X→Y) (ban : Y→Fin n→Option (Fin n))
    (y : Y) (D : DisjointPairs (ban y)) (e : Fin n) :
    step real observe project restore ban y (mergeSide (ban y) e) =
      observe y (mergeSide (ban y) e) := by
  simp [step,allowed_after_merge (ban y) D e]

theorem raw_all_mark
    (real : X→Fin n→X) (observe : Y→Fin n→Y)
    (project : Y→X) (restore : X→Y) (ban : Y→Fin n→Option (Fin n))
    (Q : Y→Prop) (P : X→Prop)
    (projQ : ∀ y,Q y→P (project y))
    (rawClosed : ∀ x e,P x→P (real x e))
    (restoreQ : ∀ x,P x→Q (restore x))
    (restoreP : ∀ x,P x→project (restore x)=x)
    (localQ : ∀ y e,Q y→ban y e=none→Q (observe y e))
    (localP : ∀ y e,Q y→ban y e=none→project (observe y e)=real (project y) e)
    (y : Y) (e : Fin n) (I : Q y) :
    Q (step real observe project restore ban y e) ∧
    project (step real observe project restore ban y e)=real (project y) e := by
  cases B : ban y e with
  | none => simpa only [step,B] using (show Q (observe y e) ∧ _ from
      ⟨localQ y e I B,localP y e I B⟩)
  | some a =>
    have R := rawClosed (project y) e (projQ y I)
    simpa only [step,B] using (show Q (restore (real (project y) e)) ∧ _ from
      ⟨restoreQ _ R,restoreP _ R⟩)

/-- The driver image is unchanged by re-lifting on excluded ordinary marks.
This is a word-by-word statement, not a new iid draw or a conditioned law. -/
theorem mapWord_agrees
    (real : X→Fin n→X) (observe : Y→Fin n→Y)
    (project : Y→X) (restore : X→Y) (ban : Y→Fin n→Option (Fin n))
    (Q : Y→Prop) (pair : ∀ y,Q y→DisjointPairs (ban y))
    (localQ : ∀ y e,Q y→ban y e=none→Q (observe y e))
    (y : Y) (I : Q y) (w : List (Fin n)) :
    mapWord (step real observe project restore ban) (fun y=>mergeSide (ban y)) y w =
      mapWord observe (fun y=>mergeSide (ban y)) y w := by
  induction w generalizing y with
  | nil => rfl
  | cons e w IH =>
    simp only [mapWord,agree_on_driver real observe project restore ban y (pair y I) e]
    exact congrArg (List.cons (mergeSide (ban y) e))
      (IH _ (localQ y _ I (allowed_after_merge (ban y) (pair y I) e)))

#print axioms allowed_after_merge
#print axioms agree_on_driver
#print axioms raw_all_mark
#print axioms mapWord_agrees

end L4.ReportFastRawRelift

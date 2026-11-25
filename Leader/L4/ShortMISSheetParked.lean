import Leader.L4.ShortMISLift
import Leader.L4.ShortPreReadGrants

namespace L4.ShortMISSheetParked
open AllSizeProtocol PhysicalCustody PhysicalShortSheet ShortMISEngine
open ShortResetChart ShortResetCycle ShortResetMIS1Ring ShortResetForwardH2
open ShortPreReadGrants ShortHelloForward MISByteCodec ShortResetRow
open ShortMISLift

variable {s n : Nat}

/-- Proof-only realization of the same frozen sheet as MIS1.  Only old
MIS1 bytes and old physical selection are read by the local lemmas. -/
def view (P : Params s n) (x : Raw s n) : Raw s n := fun i =>
  {x i with physical := if P.h i then 4 else 0, mis1 := P.byte x i}

theorem view_header (P : Params s n) (x : Raw s n) (i : Fin n) :
    header (view P x) i=P.h i := by
  change (PhysicalMIS.selected (if P.h i then 4 else 0))=P.h i
  cases P.h i <;> rfl

theorem view_next (P : Params s n) (x : Raw s n) (X : Cached P x)
    (e i : Fin n) :
    (rawNext s (view P x) e i).mis1=P.byte (rawNext s x e) i := by
  have L := congrFun (PhysicalShortSheet.exact_raw_step .mis1 (view P x) e) i
  have R := congrFun (PhysicalShortSheet.exact_raw_step P.sheet x e) i
  have M : mask .mis1 (view P x)=P.h := funext (view_header P x)
  rw [M] at L
  rw [P.maskEq x X.1] at R
  exact L.trans R.symm


/-- Both proof-only physical endpoints have idle roles; the single old
pair mark can write roles/caches but does not change selection. We never
iterate this invented physical state. -/
theorem view_step_header (P : Params s n) (x : Raw s n) (e i : Fin n) :
    header (rawNext s (view P x) e) i=P.h i := by
  change PhysicalMIS.selected ((rawNext s (view P x) e i).physical)=P.h i
  unfold rawNext
  rw [AllSizeS1Geometry.exact_physical_projection]
  unfold AllSizeS1Geometry.physicalStep
  dsimp only
  split
  · rename_i H
    subst i
    change PhysicalMIS.selected
      ((PhysicalMIS.next ((if P.h e then 4 else 0),(if P.h (rightNeighbor e) then 4 else 0))).1)=_
    cases P.h e <;> cases P.h (rightNeighbor e) <;> rfl
  · split
    · rename_i H
      subst i
      change PhysicalMIS.selected
        ((PhysicalMIS.next ((if P.h e then 4 else 0),(if P.h (rightNeighbor e) then 4 else 0))).2)=_
      cases P.h e <;> cases P.h (rightNeighbor e) <;> rfl
    · exact view_header P x i

/-- Transfer only all-mark parked safety, with no synthetic-tape or
reachability premise, to the exact original physical mark. -/
theorem parked_nondoor (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (X : Cached P x) (A : Parked P C x) (e : Fin n)
    (E : e≠RearTrace.predecessor C.root) :
    Parked P C (rawNext s x e) := by
  let z := view P x
  have heads : ∀ q,header z q=P.h q := view_header P x
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  have pre : ShortClearLaunch.ClearIssue C z 1 := by
    exact ⟨by decide,A.1.1,A.1.2.1,A.1.2.2⟩
  have ask : NoAsk C.route z := by
    intro j J H
    have V := slot_of_bits C.route z j MISByteCodec.E ShortResetFlow.empty_decode (A.1.1 j J)
    change oldK (header z (nextAt C.root j)) (z (nextAt C.root j)).mis1 (C.route.port j)=_ at V
    change P.h (nextAt C.root j)=true at H
    rw [heads,H] at V
    exact pre_read_no_ask _ _ (.inl V)
  have I := ShortClearLaunch.clear_issue_nondoor C z heads 1 pre e E
  have G := no_ask_keeps_grants_absent C.route z e (edge_sep N e) heads A.2 ask
  have B := view_next P x X e
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro j J
    unfold ShortMISLift.bits
    rw [←B]
    exact I.2.1 j J
  · rw [←B]
    exact I.2.2.1
  · rw [←B]
    exact I.2.2.2
  · intro j J H
    rw [←B]
    exact G j J H

#print axioms view_next
#print axioms view_step_header
#print axioms parked_nondoor
end L4.ShortMISSheetParked

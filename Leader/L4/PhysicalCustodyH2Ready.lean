import Leader.L4.PhysicalCustodyH1Maximal
import Leader.L4.PhysicalCustodyH2ThreeCovers
import Leader.L4.PhysicalShortMISGeometry

namespace L4.PhysicalCustody
open AllSizeProtocol AllSizeS1Geometry BStarH6Ordinal H1

/-- Permanent physical H1 and the actual cold MIS1 cache certificate.
The short controller, grants, banks and all higher fields remain unrestricted. -/
def H2Ready {s n : Nat} (x : Raw s n) : Prop :=
  rawMaximal x ∧ ∃ hh : ∃ i,header (x i)=true,
    ∀ i,off (x i)=min 3 (ordinal (fun j=>header (x j)) hh i) ∧
      successor (x i)=BitVec.ofNat 1 (header (x (rightNeighbor i))).toNat

private theorem distinct {n : Nat} (N : 5≤n) (e : Fin n) : rightNeighbor e≠e := by
  intro H
  have E := congrArg Fin.val H
  change (e.val+1)%n=e.val at E
  by_cases J : e.val+1<n
  · rw [Nat.mod_eq_of_lt J] at E
    omega
  · have J' : e.val+1=n := by have L := e.isLt; omega
    rw [J',Nat.mod_self] at E
    omega

private theorem runword {s n : Nat} (x : Raw s n) (w : List (Fin n)) :
    L4.Height.runWord (rawNext s) x w=rawRun x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (rawNext s x e)

private theorem height_cost {X : Type} {n : Nat} (step : X → Fin n → X)
    (P : X → Prop) (t : Nat) (x : X) :
    L4.iidHitCost step P t x=L4.Height.iidHitCost step P t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases H : P x
    · simp only [L4.iidHitCost,L4.Height.iidHitCost,if_pos H]
    · simp only [L4.iidHitCost,L4.Height.iidHitCost,if_neg H]
      congr 1
      exact FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun e=>ih (step x e))

theorem ready_from_h1_covers {s n : Nat} (N : 5≤n) (x : Raw s n) (M : rawMaximal x)
    (u v w : List (Fin n)) (U : ∀ e,e∈u) (V : ∀ e,e∈v) (W : ∀ e,e∈w) :
    H2Ready (rawRun (rawRun (rawRun x u) v) w) := by
  let h := fun i=>header (x i)
  let root : Fin n := ⟨0,by omega⟩
  have hh : ∃ i,h i=true := by
    rcases M.2 root with A|B|C
    · exact ⟨_,A⟩
    · exact ⟨_,B⟩
    · exact ⟨_,C⟩
  let Q := fun y : Raw s n => rawMaximal y ∧ ∀ i,header (y i)=h i
  have closure (y : Raw s n) (e : Fin n) (C : Q y) : Q (rawNext s y e) :=
    ⟨raw_h1_maximal_closed N y e C.1,fun i=>(raw_h1_selected_frozen N y e i C.1).trans (C.2 i)⟩
  obtain ⟨Z,F⟩ := short_geometry_three_covers h hh (distinct N) Q closure (fun _ C=>C.2)
      x ⟨M,fun _=>rfl⟩ u v w U V W
  let z := rawRun (rawRun (rawRun x u) v) w
  have E : (fun i=>header (z i))=h := funext Z.2
  refine ⟨Z.1,?_⟩
  let cert := fun h' : Fin n→Bool => ∃ hh' : ∃ i,h' i=true,
    ∀ i,off (z i)=min 3 (ordinal h' hh' i) ∧
      successor (z i)=BitVec.ofNat 1 (h' (rightNeighbor i)).toNat
  exact (congrArg cert E).mpr ⟨hh,F⟩

theorem raw_h2_ready_expected {s n : Nat} (N : 5≤n) (x : Raw s n) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) H2Ready x ((5+2*6^9)*n^2) := by
  rw [show (5+2*6^9)*n^2=(2+2*6^9)*n^2+3*n^2 by rw [←Nat.add_mul]]
  apply L4.AllSizeComposition.additive_stage (rawNext s) rawMaximal H2Ready _ _ x
    (raw_h1_maximal_expected N x)
  intro y M
  rw [←Nat.add_zero (3*n^2)]
  apply L4.AllSizeComposition.additive_stage (rawNext s)
    (L4.Height.ThreeCoverClock.ThreeActualCovers (rawNext s) y) H2Ready (3*n^2) 0 y
    (fun t => by rw [height_cost]; exact L4.Height.ThreeCoverClock.three_full_covers_expected _ (by omega) y t)
  intro z H t
  obtain ⟨blocks,L,full,E⟩ := H
  obtain ⟨u,v,w,rfl⟩ : ∃ u v w,blocks=[u,v,w] := by
    cases blocks with
    | nil => cases L
    | cons u blocks =>
      cases blocks with
      | nil => cases L
      | cons v blocks =>
        cases blocks with
        | nil => cases L
        | cons w blocks =>
          cases blocks with
          | nil => exact ⟨u,v,w,rfl⟩
          | cons a blocks => simp at L
  rw [runword] at E
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil,
    BStarResetSchedule.run_append,rawRun] at E
  have ready : H2Ready z := E ▸ ready_from_h1_covers N y M u v w
    (full u (by simp)) (full v (by simp)) (full w (by simp))
  cases t <;> simp [L4.iidHitCost,ready]

theorem h2_ready_closed {s n : Nat} (N : 5≤n) (x : Raw s n) (e : Fin n)
    (P : H2Ready x) : H2Ready (rawNext s x e) := by
  obtain ⟨M,hh,offEq⟩ := P
  let h := fun i=>header (x i)
  let y := rawNext s x e
  let d := fun i=>min 3 (ordinal h hh i)
  have same (i : Fin n) : header (y i)=h i := raw_h1_selected_frozen N x e i M
  have cache := geo_closed_at_fixed_headers (rows s) x e (distinct N e) d
    (fun i=>Nat.min_le_left _ _) same
    (fun i I=>by change min 3 (ordinal h hh i)=0; rw [(ordinal_zero h hh i).mpr I]; rfl)
    (fun i=>by
      change min 3 (ordinal h hh (rightNeighbor i)) =
        if h (rightNeighbor i) then 0 else min 3 (min 3 (ordinal h hh i)+1)
      rw [ordinal_right]
      by_cases q : h (rightNeighbor i)=true
      · simp [q]
      · rw [if_neg q,if_neg q]; omega)
    offEq
  let hc := fun h' : Fin n→Bool => ∃ hh' : ∃ i,h' i=true,
    ∀ i,off (y i)=min 3 (ordinal h' hh' i) ∧
      successor (y i)=BitVec.ofNat 1 (header (y (rightNeighbor i))).toNat
  exact ⟨raw_h1_maximal_closed N x e M,(congrArg hc (funext same)).mpr ⟨hh,cache⟩⟩

theorem h2_ready_gate {s n : Nat} {x : Raw s n} (H : H2Ready x) (i : Fin n) (j : Fin 3) :
    MISByteCodec.atGate (header (x i)) (x i).mis1 j=true ↔ j.val=1 ∧ header (x i)=true := by
  obtain ⟨_,hh,A⟩ := H
  exact short_mis_gate_exact (fun k=>header (x k)) hh x (fun _=>rfl) (fun k=>(A k).1) i j

end L4.PhysicalCustody

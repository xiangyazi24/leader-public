import Leader.L4.ReportStaticSpacing
import Leader.L4.SelectedRingGeometry

namespace L4.ReportCoverMask
open ReportRadiusSpacing ReportStaticSpacing ShortHopSpacing
open PhysicalCustody BStarH6WordChart WidthPackedBridge

variable {I : Type}

def Ball (f g : I → I) (rho : Nat) (c i : I) : Prop :=
  (∃ j ≤ rho, advance f c j = i) ∨ (∃ j ≤ rho, advance g c j = i)

def Sep (f : I → I) (rho : Nat) (Z : I → Bool) : Prop :=
  ∀ q, Z q = true → ∀ j, 0 < j → j ≤ rho → Z (advance f q j) = false

def Dom (f g : I → I) (rho : Nat) (Z : I → Bool) : Prop :=
  ∀ i, ∃ c, Z c = true ∧ Ball f g rho c i

private theorem inverse_run (f g : I → I) (gf : ∀ i, g (f i) = i) (i : I) (j : Nat) :
    advance g (advance f i j) j = i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change advance g (f (advance f i j)) (j+1) = i
    rw [show j+1 = 1+j by omega, advance_add]
    change advance g (g (f (advance f i j))) j = i
    rw [gf, ih]

private theorem least_positive {P : Nat → Prop} (b : Nat)
    (H : ∃ j, 0 < j ∧ j ≤ b ∧ P j) :
    ∃ j, 0 < j ∧ j ≤ b ∧ P j ∧ ∀ i, 0 < i → i < j → ¬ P i := by
  classical
  induction b with
  | zero => obtain ⟨_,_,_,_⟩ := H; omega
  | succ b ih =>
    by_cases K : ∃ j, 0 < j ∧ j ≤ b ∧ P j
    · obtain ⟨j,J,R,Q,A⟩ := ih K
      exact ⟨j,J,by omega,Q,A⟩
    · obtain ⟨j,J,R,Q⟩ := H
      exact ⟨j,J,R,Q,fun i ip ib ipr => K ⟨i,ip,by omega,ipr⟩⟩

theorem first_positive_selected_of_sep_dom (f g : I → I)
    (gf : ∀ i, g (f i) = i) (fg : ∀ i, f (g i) = i)
    (rho : Nat) (Z : I → Bool) (sep : Sep f rho Z) (dom : Dom f g rho Z)
    (q : I) (Q : Z q = true) :
    ∃ d, rho+1 ≤ d ∧ d ≤ 2*rho+1 ∧ Z (advance f q d) = true ∧
      ∀ j, 0 < j → j < d → Z (advance f q j) = false := by
  let m := advance f q (rho+1)
  obtain ⟨c,C,D⟩ := dom m
  have B : ∃ j, 0 < j ∧ j ≤ 2*rho+1 ∧ Z (advance f q j) = true := by
    rcases D with ⟨k,K,A⟩ | ⟨k,K,A⟩
    · have E : advance g m k = c := A ▸ inverse_run f g gf c k
      have S : advance f q (rho+1-k) = c := by
        calc
          advance f q (rho+1-k) =
            advance g (advance f (advance f q (rho+1-k)) k) k :=
              (inverse_run f g gf _ k).symm
          _ = c := by rw [← advance_add, show rho+1-k+k = rho+1 by omega]; exact E
      exact ⟨rho+1-k,by omega,by omega,S ▸ C⟩
    · have E : advance f m k = c := A ▸ inverse_run g f fg c k
      exact ⟨rho+1+k,by omega,by omega,by rw [advance_add]; exact E ▸ C⟩
  obtain ⟨j,J,R,H,A⟩ := least_positive (2*rho+1) B
  have L : rho+1 ≤ j := by
    by_cases K : j ≤ rho
    · exact Bool.noConfusion (H.symm.trans (sep q Q j J K))
    · omega
  refine ⟨j,L,R,H,?_⟩
  intro i ip ib
  cases E : Z (advance f q i)
  · rfl
  · exact (A i ip ib E).elim

variable {n L U rho : Nat} {h out zbyte : Fin n → Bool}

theorem hop_bounds_of_selection (G : GapBounds h L U) (hh : ∃ i, h i = true)
    (Z : Lower h → Bool)
    (sep : Sep (successor G) rho Z)
    (dom : Dom (successor G) (SelectedRingGeometry.predecessor hh) rho Z)
    (mask : ∀ i, out i = (h i && zbyte i))
    (read : ∀ q : Lower h, Z q = zbyte q.val) :
    (∃ i, out i = true) ∧ HopBounds (successorWidth G) out (rho+1) (2*rho+1) ∧
      GapBounds out (L*(rho+1)) (U*(2*rho+1)) := by
  have val (i : Lower h) : out i.val = Z i := by rw [mask, i.property, Bool.true_and, read]
  have sub (i : Fin n) (H : out i = true) : h i = true := by
    rw [mask, Bool.and_eq_true] at H
    exact H.1
  have nonempty : ∃ i, out i = true := by
    obtain ⟨i,H⟩ := hh
    obtain ⟨q,Q,_⟩ := dom ⟨i,H⟩
    exact ⟨q.val, (val q).trans Q⟩
  have hops : HopBounds (successorWidth G) out (rho+1) (2*rho+1) := by
    intro i H
    let q : Lower h := ⟨i,sub i H⟩
    obtain ⟨d,D,R,Q,A⟩ := first_positive_selected_of_sep_dom
      (successor G) (SelectedRingGeometry.predecessor hh)
      (SelectedRingGeometry.predecessor_successor G hh)
      (SelectedRingGeometry.successor_predecessor G hh)
      rho Z sep dom q ((val q).symm.trans H)
    have M (j : Nat) : out (hop (successorWidth G) i j) =
        Z (advance (successor G) q j) := by
      change out (hop (successorWidth G) q.val j) = _
      rw [← advance_val G q j]
      exact val _
    exact ⟨d,D,R,⟨by omega,(M d).trans Q,fun j J K => (M j).trans (A j J K)⟩⟩
  exact ⟨nonempty,hops,spacing_transfer_chosen G sub hops⟩

variable {X : Type}

/-- The adapter produces an all-mark-closed fibre with permanent nonempty
output mask and sharp physical spacing. It consumes only selected Z
preservation at lower roots, not a global publication cut. -/
theorem permanent_mask_of_selection
    (next : X → Fin n → X) (P : X → Prop)
    (step : ∀ x e, P x → P (next x e))
    (outMask data : X → Fin n → Bool)
    (mask : ∀ x, P x → ∀ i, outMask x i = (h i && data x i))
    (stable : ∀ x e, P x → ∀ q : Lower h, data (next x e) q.val = data x q.val)
    (G : GapBounds h L U) (hh : ∃ i, h i = true) (x : X) (A : P x)
    (sep : Sep (successor G) rho (fun q => data x q.val))
    (dom : Dom (successor G) (SelectedRingGeometry.predecessor hh) rho
      (fun q => data x q.val)) :
    (∃ i, outMask x i = true) ∧
    HopBounds (successorWidth G) (outMask x) (rho+1) (2*rho+1) ∧
    ∃ Q : X → Prop, Q x ∧ (∀ y, Q y → P y) ∧
      (∀ y e, Q y → Q (next y e)) ∧
      (∀ y, Q y → outMask y = outMask x ∧
        GapBounds (outMask y) (L*(rho+1)) (U*(2*rho+1))) := by
  obtain ⟨nonempty,hops,gaps⟩ := hop_bounds_of_selection G hh _ sep dom (mask x A) (fun _ => rfl)
  refine ⟨nonempty,hops,fun y => P y ∧ outMask y = outMask x,⟨A,rfl⟩,
    fun _ H => H.1, ?_, ?_⟩
  · intro y e H
    have B := step y e H.1
    refine ⟨B, Eq.trans (funext ?_) H.2⟩
    intro i
    rw [mask _ B, mask _ H.1]
    cases hi : h i with
    | false => rfl
    | true => exact congrArg (fun b => true && b) (stable y e H.1 ⟨i,hi⟩)
  · intro y H
    exact ⟨H.2, H.2.symm ▸ gaps⟩

/-- Report1 feeds the lower mask contract for report2 on actual raw states. -/
theorem permanent_h5_of_selection {s : Nat} (P : Raw s n → Prop)
    (step : ∀ x e, P x → P (rawNext s x e))
    (lower : ∀ x, P x → h4 x = h)
    (stable : ∀ x e, P x → ∀ q : Lower h,
      ReportByteRows.Z (p1 s) ((rawNext s x e) q.val).report1 =
        ReportByteRows.Z (p1 s) (x q.val).report1)
    (G : GapBounds h 16 81) (hh : ∃ i, h i = true) (x : Raw s n) (A : P x)
    (sep : Sep (successor G) s (fun q => ReportByteRows.Z (p1 s) (x q.val).report1))
    (dom : Dom (successor G) (SelectedRingGeometry.predecessor hh) s
      (fun q => ReportByteRows.Z (p1 s) (x q.val).report1)) :
    (∃ i, h5 x i = true) ∧
    HopBounds (successorWidth G) (h5 x) (s+1) (2*s+1) ∧
    ∃ Q : Raw s n → Prop, Q x ∧ (∀ y, Q y → P y) ∧
      (∀ y e, Q y → Q (rawNext s y e)) ∧
      (∀ y, Q y → h5 y = h5 x ∧ GapBounds (h5 y) (16*(s+1)) (81*(2*s+1))) := by
  exact permanent_mask_of_selection (rawNext s) P step h5
    (fun y i => ReportByteRows.Z (p1 s) (y i).report1)
    (fun y Y i => by rw [report1_mask, lower y Y]) stable G hh x A sep dom

/-- Report2 yields exactly the closed H6 mask and CertifiedSpacing
premises consumed by WidthPackJoint and WidthPackTiming. -/
theorem permanent_h6_of_selection {s : Nat} (P : Raw s n → Prop)
    (step : ∀ x e, P x → P (rawNext s x e))
    (lower : ∀ x, P x → h5 x = h)
    (stable : ∀ x e, P x → ∀ q : Lower h,
      ReportByteRows.Z (p2 s) ((rawNext s x e) q.val).report2 =
        ReportByteRows.Z (p2 s) (x q.val).report2)
    (G : GapBounds h (16*(s+1)) (81*(2*s+1))) (hh : ∃ i, h i = true)
    (x : Raw s n) (A : P x)
    (sep : Sep (successor G) (radiusTwo s)
      (fun q => ReportByteRows.Z (p2 s) (x q.val).report2))
    (dom : Dom (successor G) (SelectedRingGeometry.predecessor hh) (radiusTwo s)
      (fun q => ReportByteRows.Z (p2 s) (x q.val).report2)) :
    (∃ i, oldH6 (rows s) x i = true) ∧
    HopBounds (successorWidth G) (oldH6 (rows s) x) (radiusTwo s+1) (2*radiusTwo s+1) ∧
    ∃ Q : Raw s n → Prop, Q x ∧ (∀ y, Q y → P y) ∧
      (∀ y e, Q y → Q (rawNext s y e)) ∧
      (∀ y, Q y → oldH6 (rows s) y = oldH6 (rows s) x ∧ CertifiedSpacing y) := by
  exact permanent_mask_of_selection (rawNext s) P step (oldH6 (rows s))
    (fun y i => ReportByteRows.Z (p2 s) (y i).report2)
    (fun y Y i => by rw [report2_mask, lower y Y]) stable G hh x A sep dom

#print axioms first_positive_selected_of_sep_dom
#print axioms hop_bounds_of_selection
#print axioms permanent_mask_of_selection
#print axioms permanent_h5_of_selection
#print axioms permanent_h6_of_selection
end L4.ReportCoverMask

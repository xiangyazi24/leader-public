import Leader.L4.WidthPackedBridge
import Leader.L4.Height.ProductionCustody

namespace L4.ProductionH6Count
open AllSizeProtocol PhysicalCustody BStarH6WordChart ShortLayerGeometry ShortResetChart

/-- The exact production advice implies the lower limit of its double
exponential ring-size band. -/
theorem advice_lower {s n : Nat} (S : 0<s) (advice : s=ell (ell n)) :
    2^(2^(s-1))<n := by
  have H : (s-1)<ell (ell n) := by omega
  have K : 2^(s-1)<ell n := by
    apply Nat.lt_of_not_ge
    intro P
    exact (Nat.not_le_of_lt H) ((ell_le_iff _ _).mpr P)
  apply Nat.lt_of_not_ge
  intro P
  exact (Nat.not_le_of_lt K) ((ell_le_iff _ _).mpr P)

private theorem power_pad (t : Nat) : t+18≤2^(t+5) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have E : t+1+5=t+5+1 := by omega
    change t+1+18≤2^(t+1+5)
    rw [E,Nat.pow_succ]
    omega

theorem room_of_advice {s n : Nat} (S : 6≤s) (advice : s=ell (ell n)) :
    3*1024*radWidth s<n := by
  have A := advice_lower (by omega) advice
  have B : s+12≤2^(s-1) := by
    have T := power_pad (s-6)
    rw [show s-6+18=s+12 by omega,show s-6+5=s-1 by omega] at T
    exact T
  have C := Nat.pow_le_pow_right (by decide : 0<2) B
  rw [Nat.pow_add] at C
  have R : radWidth s ≤ 2^s := by unfold radWidth; omega
  have D := Nat.mul_le_mul_left 4096 R
  omega

theorem three_gaps_fit {s n : Nat} (S : 6≤s) (advice : s=ell (ell n)) :
    3*(81*(2*s+1)*(2*radiusTwo s+1))<n := by
  have W := (WidthRatioArithmetic.production_bounds S).2
  have R := room_of_advice S advice
  omega

private theorem count_between {n : Nat} {h : Fin n → Bool} {i : Fin n}
    (H : h i=true) : 1≤countPrefix h (i.val+1) ∧ countPrefix h (i.val+1)≤total h := by
  refine ⟨?_,countPrefix_mono h (by have := i.isLt; omega)⟩
  rw [prefix_succ h i,H]
  simp

private theorem count_ne {n : Nat} {h : Fin n → Bool} {i j : Fin n}
    (I : h i=true) (J : h j=true) (D : i≠j) :
    countPrefix h (i.val+1)≠countPrefix h (j.val+1) := by
  have lt {u v : Fin n} (P : u.val<v.val) (V : h v=true) :
      countPrefix h (u.val+1)<countPrefix h (v.val+1) := by
    have E := countPrefix_mono h (show u.val+1≤v.val by omega)
    rw [prefix_succ h v,V]
    simp
    omega
  rcases Nat.lt_trichotomy i.val j.val with A|A|A
  · exact Nat.ne_of_lt (lt A J)
  · exact (D (Fin.ext A)).elim
  · exact (Nat.ne_of_lt (lt A I)).symm

/-- Traverse three positive successor gaps shorter in total than one
turn. The four distinct H6 anchors are counted by the existing total. -/
theorem four_of_gap_law {n B : Nat} (h : Fin n → Bool)
    (hh : ∃ i,h i=true) (room : 3*B<n)
    (step : ∀ r, h r=true → ∃ d≤B, Gap h r d) :
    4≤total h := by
  obtain ⟨r,H⟩ := hh
  obtain ⟨a,A,F⟩ := step r H
  obtain ⟨b,Bb,G⟩ := step _ F.atEnd
  obtain ⟨c,C,I⟩ := step _ G.atEnd
  have ap := F.positive
  have bp := G.positive
  have cp := I.positive
  have G' : h (nextAt r (a+b))=true := by rw [nextAt_add]; exact G.atEnd
  have I' : h (nextAt r (a+b+c))=true := by rw [nextAt_add,nextAt_add]; exact I.atEnd
  have ne (i j : Nat) (A : i≤a+b+c) (B : j≤a+b+c) (D : i≠j) :
      nextAt r i≠nextAt r j := by
    intro Q
    exact D (nextAt_injective_under r _ _ (by omega) (by omega) Q)
  have H' : h (nextAt r 0)=true := H
  have E0 := count_between H'
  have E1 := count_between F.atEnd
  have E2 := count_between G'
  have E3 := count_between I'
  have N01 := count_ne H' F.atEnd (ne 0 a (by omega) (by omega) (by omega))
  have N02 := count_ne H' G' (ne 0 (a+b) (by omega) (by omega) (by omega))
  have N03 := count_ne H' I' (ne 0 (a+b+c) (by omega) (by omega) (by omega))
  have N12 := count_ne F.atEnd G' (ne a (a+b) (by omega) (by omega) (by omega))
  have N13 := count_ne F.atEnd I' (ne a (a+b+c) (by omega) (by omega) (by omega))
  have N23 := count_ne G' I' (ne (a+b) (a+b+c) (by omega) (by omega) (by omega))
  omega

theorem four_h6_of_advice {s n : Nat} (S : 6≤s) (advice : s=ell (ell n))
    (z : Raw s n) (hh : ∃ i,oldH6 (rows s) z i=true)
    (C : WidthPackedBridge.CertifiedSpacing z) :
    4≤total (oldH6 (rows s) z) := by
  apply four_of_gap_law _ hh (three_gaps_fit S advice)
  intro r R
  obtain ⟨d,_,U,G⟩ := C r R
  exact ⟨d,U,G⟩

/-- The service/custody production record follows immediately once the
base spacing is certified; no independent room or owner-count axiom. -/
theorem production_of_spacing {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (S : 6≤s) (advice : s=ell (ell n)) (C : WidthPackedBridge.CertifiedSpacing g.base) :
    Height.ProductionCustody.Production g :=
  ⟨advice,S,room_of_advice S advice,four_h6_of_advice S advice g.base g.hh C⟩

#print axioms advice_lower
#print axioms room_of_advice
#print axioms four_of_gap_law
#print axioms four_h6_of_advice
#print axioms production_of_spacing
end L4.ProductionH6Count

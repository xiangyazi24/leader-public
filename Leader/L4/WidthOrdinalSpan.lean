import Leader.L4.ShortLayerGeometry
import Leader.L4.BStarH6Ordinal

namespace L4.WidthOrdinalSpan
open AllSizeProtocol ShortResetChart ShortLayerGeometry BStarH6Ordinal

theorem back_nextAt_add {n : Nat} (q : Fin n) (a b : Nat) :
    back (nextAt q (a+b)) b=nextAt q a := by
  induction b with
  | zero => exact back_zero _
  | succ b ih => exact (back_right_succ _ _).trans ih

theorem nextAt_back {n : Nat} (q : Fin n) (b : Nat) :
    nextAt (back q b) b=q := by
  induction b generalizing q with
  | zero => exact back_zero _
  | succ b ih =>
    let r := RearTrace.predecessor q
    have Q : rightNeighbor r=q := RearTrace.right_predecessor q
    have B : back q (b+1)=back r b := Q ▸ back_right_succ r b
    rw [B]
    change rightNeighbor (nextAt (back r b) b)=q
    rw [ih,Q]

theorem gap_unique {n : Nat} {h : Fin n → Bool} {r : Fin n} {a b : Nat}
    (F : Gap h r a) (G : Gap h r b) : a=b := by
  rcases Nat.lt_trichotomy a b with H|H|H
  · exact Bool.noConfusion (F.atEnd.symm.trans (G.interior a F.positive H))
  · exact H
  · exact Bool.noConfusion (G.atEnd.symm.trans (F.interior b G.positive H))

/-- The certified forward successor and the actual byte-geometry
ordinal at the last site refer to the same physical word. -/
theorem last_gap {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (q : Fin n) (Q : h (rightNeighbor q)=true) :
    let r := back q (ordinal h hh q)
    h r=true ∧ Gap h r (ordinal h hh q+1) := by
  let d := ordinal h hh q
  let r := back q d
  have H := (ordinal_spec h hh q).2
  have B : nextAt r d=q := nextAt_back q d
  refine ⟨H.1,⟨by omega,?_,?_⟩⟩
  · change h (rightNeighbor (nextAt r d))=true
    rwa [B]
  · intro k P V
    have R := back_nextAt_add r k (d-k)
    rw [show k+(d-k)=d by omega,B] at R
    exact R ▸ H.2 (d-k) (by omega)

/-- Move any certified span bounds, measured on H6 successors,
onto precisely the raw byte-level endpoint width used by the custody interface. -/
theorem end_width_bounds {n A B : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (successor : ∀ r, h r=true → ∃ d, A≤d ∧ d≤B ∧ Gap h r d) :
    ∀ q, h (rightNeighbor q)=true → A≤ordinal h hh q+1 ∧ ordinal h hh q+1≤B := by
  intro q Q
  obtain ⟨root,G⟩ := last_gap h hh q Q
  obtain ⟨d,L,U,F⟩ := successor _ root
  have E := gap_unique F G
  exact ⟨E ▸ L,E ▸ U⟩

end L4.WidthOrdinalSpan

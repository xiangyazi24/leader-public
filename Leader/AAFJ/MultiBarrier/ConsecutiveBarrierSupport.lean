import Leader.AAFJ.OneBarrier.Sanitation

namespace AAFJPK
namespace BarrierAlgebra
namespace ArbitrarySupportGeometry

set_option autoImplicit false

/-- Local copy of the support-order fact, kept here to avoid importing
    `AAFJCenteredBarrierCycle`, whose dependency is stronger than this lemma. -/
private theorem barrierSupport_pairwise_val_lt_local
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (L : Labels n k) :
    (barrierSupport hk ring L).Pairwise (fun a b => a.val < b.val) := by
  unfold barrierSupport
  change (List.finRange n).filter
      (fun e => decide (BarrierAt hk ring L e)) |>.Pairwise
        (fun a b => a.val < b.val)
  exact (List.pairwise_lt_finRange n).filter _

/-- The AAFJ clockwise distance is zero on the diagonal. -/
private theorem aafj_cwDist_self
    {n : Nat} (ring : DirectedRing n) (a : Fin n) :
    SingleBarrierSanitation.cwDist ring a a = 0 := by
  unfold SingleBarrierSanitation.cwDist
  have hsum : a.val + n - a.val = n := by omega
  rw [hsum, Nat.mod_self]

/-- On a non-wrapping ordered pair, clockwise distance is ordinary subtraction. -/
private theorem aafj_cwDist_eq_sub_of_lt
    {n : Nat} (ring : DirectedRing n) {a b : Fin n}
    (hab : a.val < b.val) :
    SingleBarrierSanitation.cwDist ring a b = b.val - a.val := by
  unfold SingleBarrierSanitation.cwDist
  have hsum : b.val + n - a.val = n + (b.val - a.val) := by omega
  have hdiff : b.val - a.val < n := by
    have hb := b.isLt
    omega
  rw [hsum, Nat.add_mod, Nat.mod_self, Nat.zero_add]
  simpa [Nat.mod_mod] using Nat.mod_eq_of_lt hdiff

/-- If more than one charged edge exists, choose a clockwise-consecutive
    charged pair.  "Strictly between" is expressed by canonical clockwise
    distance from q. -/
theorem exists_cw_consecutive_barriers_of_count_gt_one
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (L : Labels n k)
    (hcount : 1 < barrierCount hk ring L) :
    ∃ q r : Fin n,
      q ≠ r ∧
      BarrierAt hk ring L q ∧
      BarrierAt hk ring L r ∧
      0 < SingleBarrierSanitation.cwDist ring q r ∧
      ∀ e : Fin n, BarrierAt hk ring L e →
        ¬ (0 < SingleBarrierSanitation.cwDist ring q e ∧
          SingleBarrierSanitation.cwDist ring q e <
            SingleBarrierSanitation.cwDist ring q r) := by
  generalize hS : barrierSupport hk ring L = S
  have hlen : 1 < S.length := by
    have h := hcount
    change 1 < (barrierSupport hk ring L).length at h
    rw [hS] at h
    exact h
  have hord : S.Pairwise (fun a b => a.val < b.val) := by
    have h := barrierSupport_pairwise_val_lt_local hk ring L
    rw [hS] at h
    exact h
  cases S with
  | nil =>
      simp at hlen
  | cons q tail =>
      cases tail with
      | nil =>
          simp at hlen
      | cons r rest =>
          have hqrVal : q.val < r.val := by
            exact List.rel_of_pairwise_cons hord (by simp)
          have hqr : q ≠ r := by
            intro h
            subst r
            omega
          have hq : BarrierAt hk ring L q := by
            rw [← mem_barrierSupport_iff hk ring L q, hS]
            simp
          have hr : BarrierAt hk ring L r := by
            rw [← mem_barrierSupport_iff hk ring L r, hS]
            simp
          have hdistPos :
              0 < SingleBarrierSanitation.cwDist ring q r := by
            rw [aafj_cwDist_eq_sub_of_lt ring hqrVal]
            omega
          refine ⟨q, r, hqr, hq, hr, hdistPos, ?_⟩
          intro e he hbetween
          have heMem : e ∈ barrierSupport hk ring L :=
            (mem_barrierSupport_iff hk ring L e).2 he
          rw [hS] at heMem
          simp only [List.mem_cons] at heMem
          rcases heMem with heq | heMem
          · subst e
            have hp := hbetween.1
            rw [aafj_cwDist_self ring q] at hp
            omega
          · rcases heMem with heq | heRest
            · subst e
              exact Nat.lt_irrefl _ hbetween.2
            ·
              have hreVal : r.val < e.val :=
                List.rel_of_pairwise_cons hord.tail heRest
              have hqeVal : q.val < e.val :=
                Nat.lt_trans hqrVal hreVal
              rw [aafj_cwDist_eq_sub_of_lt ring hqeVal,
                aafj_cwDist_eq_sub_of_lt ring hqrVal] at hbetween
              omega

end ArbitrarySupportGeometry
end BarrierAlgebra
end AAFJPK

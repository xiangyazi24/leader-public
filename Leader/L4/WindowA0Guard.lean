import Leader.L4.WindowA0Rows
import Leader.L4.FixedResidual

/-! A0 genuine-entry and clean-rail guards. These local lemmas do not
assert arbitrary dirty normalization or a stochastic trial clock. -/
namespace L4.WindowA0Guard

/-- A new worker begins at the source predecessor. It starts on the
top only when the gap is one, rather than in the dirty nonadjacent
payable-top control. -/
theorem launch_already_at_top {I J : Nat} (h : I < J)
    (atTop : J-1 = I) : J=I+1 := by omega

/-- The first adjacency crossing cannot skip from distance at least
two to zero. At most one of the two indicated moves occurs on a mark. -/
theorem first_adjacent_not_top {I U : Nat} (hBefore : I+2 ≤ U)
    (topAdv workerAdv : Bool) (hSeparate : ¬ (topAdv=true ∧ workerAdv=true))
    (hEnter : U-workerAdv.toNat ≤ I+topAdv.toNat+1) :
    U-workerAdv.toNat = I+topAdv.toNat+1 := by
  cases topAdv <;> cases workerAdv <;> simp_all <;> omega

/-- Clockwise top payment is at I−1, whereas the upward worker's
left hop is at U−1. These are different raw labels inside the
nonwrapping lifted interval. -/
theorem separated_incoming {n : Nat} (base : Fin n) {I U : Nat}
    (hne : I ≠ U) (hI : I < n) (hU : U < n) :
    GGStage.incoming base I ≠ GGStage.incoming base U := by
  intro h
  have h' := congrArg rightNeighbor h
  rw [GGStage.incoming_right,GGStage.incoming_right] at h'
  exact hne (liftedSite_inj base hI hU h')

/-- Genuine first contact across any single surviving raw mark. The
two motion flags must identify their actual physical labels. -/
theorem first_adjacent_raw {n : Nat} (base e : Fin n) {I U : Nat}
    (hBefore : I+2 ≤ U) (hU : U < n)
    (topAdv workerAdv : Bool)
    (hTop : topAdv=true → e=GGStage.incoming base I)
    (hWorker : workerAdv=true → e=GGStage.incoming base U)
    (hEnter : U-workerAdv.toNat ≤ I+topAdv.toNat+1) :
    U-workerAdv.toNat = I+topAdv.toNat+1 := by
  apply first_adjacent_not_top hBefore topAdv workerAdv _ hEnter
  rintro ⟨h1,h2⟩
  exact separated_incoming base (by omega : I≠U) (by omega : I<n) hU
    ((hTop h1).symm.trans (hWorker h2))

/-- At an ordinary OFF receiver no break is synthesized in either
selected rail. This excludes the stale-X loss on an already X-free
retained ordinary pair. -/
theorem ordinary_off_no_x {Q : Nat} (a b : Rail)
    (ha : a ≠ .x) (hb : b ≠ .x) :
    (patrol false false false (.off : Source Q) a b).left ≠ .x ∧
    (patrol false false false (.off : Source Q) a b).right ≠ .x := by
  rw [FixedResidual.body_exact]
  cases a <;> cases b <;>
    first
    | exact (ha rfl).elim
    | exact (hb rfl).elim
    | (constructor <;> intro h <;> cases h)

/-- The post-row retained head cannot acquire a break during any
pinned incoming top service, even with arbitrary inherited source
and predecessor rail. A paid outgoing old top is outside this lemma
and outside the retained corridor. -/
theorem pinned_right_no_x {Q : Nat} (s : Source Q) (a b : Rail)
    (hb : b ≠ .x) :
    (patrol true true false s a b).right ≠ .x := by
  rw [FixedResidual.top_exact true false s a b (.inl rfl)]
  cases b <;> first | exact (hb rfl).elim | (intro h; cases h)

/-- The clean worker moves toward the top one site and leaves a T
trail. Unlike X, both E and T accept the return after the pinned turn. -/
theorem clean_ordinary_worker_left {Q : Nat} (a b : Rail)
    (ha : a = .e ∨ a = .t) (hb : b = .ui ∨ b = .uc) :
    (patrol false false false (.off : Source Q) a b).left=b ∧
    (patrol false false false (.off : Source Q) a b).right=.t := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact ⟨rfl,rfl⟩

private theorem sourceGuard_left {Q : Nat} (p : Bool) (a : Patrol Q) :
    (sourceGuard p a).left = a.left := by
  unfold sourceGuard
  split <;> first | rfl | (split <;> rfl)

private theorem arrivals_left_clean {Q : Nat} (r p l : Bool) (a : Patrol Q)
    (h : a.left ≠ .x) :
    (arrivals r p l a).left ≠ .x := by
  unfold arrivals
  split
  · intro hh; cases hh
  · split
    · intro hh; cases hh
    · split
      · intro hh; cases hh
      · split
        · split <;> intro hh <;> cases hh
        · split
          · intro hh; cases hh
          · split <;> exact h

private theorem launch_left_clean {Q : Nat} (a : Patrol Q)
    (h : a.left ≠ .x) : (launch a).left ≠ .x := by
  unfold launch
  split
  · intro hh; cases hh
  · intro hh; cases hh
  · exact h

private theorem turn_left {Q : Nat} (r : Bool) (a : Patrol Q) :
    (turn r a).left = a.left := by
  unfold turn
  split
  · split <;> rfl
  · rfl

/-- At a pinned incoming service both retained rail sockets preserve
X-freedom, including the door's genuine launch on the left. -/
theorem pinned_no_x {Q : Nat} (s : Source Q) (a b : Rail)
    (ha : a ≠ .x) (hb : b ≠ .x) :
    (patrol true true false s a b).left ≠ .x ∧
    (patrol true true false s a b).right ≠ .x := by
  refine ⟨?_,pinned_right_no_x s a b hb⟩
  change (turn true (launch (arrivals true true false
    (sourceGuard true (⟨s,a,b,false⟩ : Patrol Q))))).left ≠ .x
  rw [turn_left]
  apply launch_left_clean
  apply arrivals_left_clean
  rwa [sourceGuard_left]

/-- The final birth row does not overwrite either rail, so the
post-payment patrol mode is the one used in physical guard proofs. -/
theorem pair_rail_projection {p c : Nat} (u v : Site p c) :
    let z := stepPrefix u v
    let m := patrol (z.2.leader || z.1.mark) (pinned z.1 z.2)
      z.2.leader z.2.source z.1.rail z.2.rail
    ((pairStep u v).1.rail,(pairStep u v).2.rail) = (m.left,m.right) := by
  simp only [pairStep]
  unfold finishBirth
  split <;> rfl

/-- A physical selected pair either remains ordinary with OFF receiver
or is pinned. When both post-prefix sockets are X-free this pair cannot
invalidate them. P3 at the old top instead removes that site from the
retained domain, rather than satisfying the ordinary-OFF alternative. -/
theorem pair_no_x_retained {p c : Nat} (u v : Site p c)
    (hl : (stepPrefix u v).2.leader = false)
    (ha : (stepPrefix u v).1.rail ≠ .x) (hb : (stepPrefix u v).2.rail ≠ .x)
    (hcase : (stepPrefix u v).1.mark = true ∨ (stepPrefix u v).2.source = .off) :
    (pairStep u v).1.rail ≠ .x ∧ (pairStep u v).2.rail ≠ .x := by
  have eq := pair_rail_projection u v
  dsimp only at eq
  have h1 := congrArg Prod.fst eq
  have h2 := congrArg Prod.snd eq
  dsimp only at h1 h2
  rw [h1,h2]
  by_cases hm : (stepPrefix u v).1.mark = true
  · simp only [hl,hm,pinned,Bool.false_or,Bool.not_false,Bool.true_and]
    exact pinned_no_x _ _ _ ha hb
  · have hm' := Bool.eq_false_iff.mpr hm
    have hs := hcase.resolve_left hm
    simp only [hl,hm',hs,pinned,Bool.false_or,Bool.not_false,Bool.true_and]
    exact ordinary_off_no_x _ _ ha hb

#print axioms pair_rail_projection
#print axioms pair_no_x_retained
#print axioms pinned_no_x
#print axioms pinned_right_no_x
#print axioms clean_ordinary_worker_left

#print axioms launch_already_at_top
#print axioms first_adjacent_not_top
#print axioms separated_incoming
#print axioms first_adjacent_raw
#print axioms ordinary_off_no_x
end L4.WindowA0Guard

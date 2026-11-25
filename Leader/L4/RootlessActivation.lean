import Leader.L4.DistinctLiteralClock
import Leader.L4.RootlessFIFO
import Leader.L4.TripleRenewal
import Leader.L4.RootedFresh

namespace L4.RootlessActivation
open RankPhysical RankRootless FixedResidual DistinctLiteralClock TaggedTail

private theorem s_mono {n : Nat} {f g : Fin n→Nat} (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))

private theorem s_zero (n : Nat) : sumEdge (fun _ : Fin n => 0)=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons,Nat.zero_add] at *
    exact ih

private theorem s_single {n : Nat} (e : Fin n) :
    sumEdge (fun i => if i=e then 1 else 0)=1 := by
  induction n with
  | zero => exact e.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · simp [sumEdge,List.ofFn_succ,Fin.succ_ne_zero,show (List.ofFn (fun _ : Fin n => 0)).sum=0 from s_zero n]
    · have f (i : Fin n) : (i.succ=e.succ) ↔ i=e := by simp
      rw [show sumEdge (fun i : Fin (n+1) => if i=e.succ then 1 else 0) =
         (if (0:Fin (n+1))=e.succ then 1 else 0)+
           sumEdge (fun i : Fin n => if i.succ=e.succ then 1 else 0) by
        simp [sumEdge,List.ofFn_succ]]
      have hz : (0:Fin (n+1)) ≠ e.succ := Ne.symm (Fin.succ_ne_zero e)
      simp only [hz,if_false,Nat.zero_add,f]
      exact ih e

/-- At rank at least two an upstream mark has another marked bond
strictly before returning to itself. The first such bond supplies the
distinct (nonalias) zero-stock corridor. -/
theorem distinct_ghost_gap {p c n : Nat} (x : Config p c n) (_n0 : 0<n)
    (h : ∃ e : Fin n,(x e).mark=true) (hR : 2≤rank x) (hl : NoLiving x) :
    ∃ up d, d+1<n ∧ FixedLive up (rightNeighbor up) d false x := by
  obtain ⟨up,hup⟩ := h
  have h2 : ∃ e : Fin n, e≠up ∧ (x e).mark=true := by
    by_cases hx : ∃ e : Fin n, e≠up ∧ (x e).mark=true
    · exact hx
    have H : rank x≤1 := by
      unfold rank
      rw [← s_single up]
      apply s_mono
      intro e
      by_cases he : e=up
      · simp [he,hup]
      · have hf : (x e).mark=false := Bool.eq_false_iff.mpr (fun hh => hx ⟨e,he,hh⟩)
        simp [he,hf]
    omega
  obtain ⟨e,he,hE⟩ := h2
  let top := rightNeighbor up
  obtain ⟨j,hj,hJ⟩ := liftedSite_of_site top e
  have hJb : j+1<n := by
    by_cases hh : j+1<n
    · exact hh
    have hN : j+1=n := by omega
    have hEq : liftedSite top j=up := by
      rw [show top=rightNeighbor up from rfl,liftedSite_advance,hN,liftedSite_full]
    exact (he (hJ.symm.trans hEq)).elim
  obtain ⟨d,hD⟩ := firstMark_exists x top ⟨e,hE⟩
  have hd := hD.min_le (hJ.symm ▸ hE)
  exact ⟨up,d,by omega,hup,hl top,hD,hl _⟩

private theorem no_birth_keeps_gap {p c n d : Nat} (hn : 4≤n)
    (x : Config p c n) (up top e : Fin n) (hm : MCOV x)
    (hl : NoLiving x) (hs : NoStock x) (h : FixedLive up top d false x)
    (hl' : NoLiving (step x e)) :
    FixedLive up top d false (step x e) := by
  have hgeom := zero_stock_static hn x e hm hl hs
  refine ⟨(hgeom up).1.trans h.1,hl' top,?_, hl' _⟩
  refine ⟨h.2.2.1.lt,(hgeom _).1.trans h.2.2.1.marked,?_⟩
  intro k hk
  rw [(hgeom _).1]
  exact h.2.2.1.before k hk

theorem birth_earlier_than_geometry_exit {p c n : Nat} (hn : 4≤n)
    (up top : Fin n) (d : Nat) (t : Nat) (x : Config p c n)
    (hm : MCOV x) (hc : COV x) (hl : NoLiving x) (hs : NoStock x)
    (hx : FixedLive up top d false x) :
    iidHitCost step (fun y => ¬NoLiving y) t x ≤
      iidHitCost step (fun y => ¬FixedLive up top d false y) t x := by
  classical
  induction t generalizing x with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    have hb : ¬¬NoLiving x := fun h => h hl
    have hg : ¬¬FixedLive up top d false x := fun h => h hx
    rw [iidHitCost,if_neg hb,iidHitCost,if_neg hg]
    apply Nat.add_le_add_left
    apply s_mono
    intro e
    by_cases he : NoLiving (step x e)
    · obtain ⟨hm',hc'⟩ := EntranceCover.cover_closed hn x e ⟨hm,hc⟩
      exact ih _ hm' hc' he (zero_stock_preserved hn x e hl hs)
        (no_birth_keeps_gap hn x up top e hm hl hs hx he)
    · rw [iidHitCost_of_target step (fun y : Config p c n => ¬NoLiving y) (step x e) he]
      exact Nat.zero_le _

/-- Zero-stock all-ghost activation at rank ≥2, from the literal
distinct timer at coefficient eight. No assumption of a clean rail. -/
theorem zero_stock_birth_mean {p c n : Nat} (hn : 4≤n) (hc : 0<c)
    (x : Config p c n) (hq : QuietEntrance x) (hR : 2≤rank x)
    (hl : NoLiving x) (hs : NoStock x) :
    IIDExpectedHittingTimeAtMost step (fun y => ¬NoLiving y) x (8*(2*c+1)*n^2) := by
  obtain ⟨up,d,hd,hdx⟩ := distinct_ghost_gap x (by omega) hq.2.2.1 hR hl
  obtain ⟨clock,hBudget⟩ := concreteFixedResidualClockEight x up (rightNeighbor up) d false
    hn hc rfl hd hq.1 hq.2.1 hdx
  intro t
  have hBound := birth_earlier_than_geometry_exit hn up (rightNeighbor up) d t x
    hq.1 hq.2.1 hl hs hdx
  refine Nat.le_trans hBound (Nat.le_trans (expected_of_countdown _ _ _ clock t) ?_)
  have ha := Nat.le_trans hBudget (Nat.mul_le_mul_left (8*(2*c+1)) (show d+2≤n by omega))
  apply Nat.mul_le_mul_right
  calc
    _ ≤ n*(8*(2*c+1)*n) := Nat.mul_le_mul_left _ ha
    _ = _ := by rw [Nat.pow_two]; ac_rfl

/-- Both all-ghost entry stages of the stopped attempt, with the
already-checked 17n² drain constant and the sharp fixed timer.
If a retirement occurs during stock drainage, the physical target
is reached already; we need not continue to a birth. -/
theorem rootless_stage_mean {p c n : Nat} (hp : 2≤p) (hc : 12≤c)
    (hn : 4≤n) (x : Config p c n)
    (hq : QuietEntrance x) (hR : 2≤rank x) :
    IIDExpectedHittingTimeAtMost step (fun y => ¬NoLiving y ∨ rank y<rank x) x
      ((17+8*(2*c+1))*n^2) := by
  let obs : TripleRenewal.Stage step x :=
    { State := Config p c n, start := x, next := step, project := id
      ready := RootlessFIFO.DrainTarget, reachable := QuietEntrance
      projInit := rfl, projStep := fun _ _ => rfl, reachStart := hq
      reachStep := fun z e hz => RootedFresh.quiet_step z e hp hc hn hz }
  let goal := fun y : Config p c n => ¬NoLiving y ∨ rank y<rank x
  obtain ⟨e,hE⟩ := hq.2.2.1
  have hDrain := RootlessFIFO.rootless_drain_mean hn x (rightNeighbor e) hq.1
    (by rwa [RearTrace.predecessor_right])
  have ht := TripleRenewal.expected_with_preparation obs goal (17*n^2) (8*(2*c+1)*n^2)
    hDrain (by
      intro y hy hr hg
      change QuietEntrance y at hy
      change RootlessFIFO.DrainTarget y at hr
      change ¬(¬NoLiving y ∨ rank y<rank x) at hg
      have hNo : NoLiving y := Classical.not_not.mp (fun nn => hg (Or.inl nn))
      have hs := hr.resolve_left (fun h => h hNo)
      have hrank : 2≤rank y := by
        have ha : ¬ rank y<rank x := fun hh => hg (Or.inr hh)
        omega
      let finish : TripleRenewal.Stage step y :=
        { State := Config p c n, start := y, next := step, project := id
          ready := fun z => ¬NoLiving z, reachable := fun _ => True
          projInit := rfl, projStep := fun _ _ => rfl, reachStart := trivial
          reachStep := fun _ _ _ => trivial }
      have hz := TripleRenewal.expected_with_preparation finish goal (8*(2*c+1)*n^2) 0
        (zero_stock_birth_mean hn (by omega) y hy hrank hNo hs)
        (by intro z _ hl hh; exact False.elim (hh (Or.inl hl)))
      change IIDExpectedHittingTimeAtMost step goal y (8*(2*c+1)*n^2)
      simpa only [Nat.add_zero] using hz)
  simpa only [goal,Nat.add_mul] using ht

end L4.RootlessActivation


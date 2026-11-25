import Leader.L4.RestartGeometry
import Leader.L4.LiteralSupplier
import Leader.L4.FreshEpochEntry
import Leader.L4.RestartSerial

namespace L4.RestartRouting
open RankPhysical RankSupplier TripleResidual TaggedTail Classical

/-- Preparing consecutive leaders is interrupted by any native kill,
even when that kill is not at the tracked supplier or target. The
rank-loss test precedes the kill test on a completed mark. -/
inductive Exit where
  | active
  | retired
  | killed
  | targetBorn
  deriving DecidableEq, Repr

structure Prep (p c n : Nat) where
  supplier : RankSupplier.Obs p c n
  flag : Exit

def prepInit {p c n : Nat} (x : Config p c n) (d : Nat) : Prep p c n :=
  ⟨RankSupplier.init x d,.active⟩

def prepStep {p c n : Nat} (v : Fin n) (s : Prep p c n) (e : Fin n) : Prep p c n :=
  if s.flag ≠ .active then s else
    let z := RankSupplier.advance v s.supplier e
    if retirement s.supplier.config e then ⟨z,.retired⟩
    else if death s.supplier.config e then ⟨z,.killed⟩
    else if z.stopped then ⟨z,.targetBorn⟩
    else ⟨z,.active⟩

private theorem edge_mono {n : Nat} (f g : Fin n → Nat) (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

theorem active_is_unstopped {p c n : Nat} (v e : Fin n) (s : Prep p c n)
    (h : (prepStep v s e).flag=.active) (_hs : s.flag=.active → s.supplier.stopped=false) :
    (prepStep v s e).supplier.stopped=false := by
  by_cases h₁ : s.flag=.active
  · cases hR : retirement s.supplier.config e <;>
      cases hK : death s.supplier.config e <;>
      cases hB : (RankSupplier.advance v s.supplier e).stopped <;>
      simp [prepStep,h₁,hR,hK,hB] at h ⊢
  · have hEq : prepStep v s e = s := if_pos h₁
    exact False.elim (h₁ (by simpa only [hEq] using h))

/-- The interrupting observer costs no more than the literal fixed
supplier, on exactly the same raw word distribution. -/
theorem prep_cost_le {p c n : Nat} (v : Fin n) (s : Prep p c n)
    (hs : s.flag=.active → s.supplier.stopped=false) (t : Nat) :
    iidHitCost (prepStep v) (fun z => z.flag ≠ .active) t s ≤
    iidHitCost (RankSupplier.advance v) (fun z => z.stopped=true) t s.supplier := by
  induction t generalizing s with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    by_cases h : s.flag=.active
    · have hu : s.supplier.stopped=false := hs h
      rw [iidHitCost,if_neg (by simp [h]),iidHitCost,if_neg (by simp [hu])]
      apply Nat.add_le_add_left
      apply edge_mono
      intro e
      have hp : (prepStep v s e).supplier=RankSupplier.advance v s.supplier e := by
        cases hR : retirement s.supplier.config e <;>
          cases hK : death s.supplier.config e <;>
          cases hB : (RankSupplier.advance v s.supplier e).stopped <;>
          simp [prepStep,h,hR,hK,hB]
      rw [← hp]
      exact ih _ (fun hz => active_is_unstopped v e s hz hs)
    · rw [iidHitCost_of_target (prepStep v) (fun z => z.flag ≠ .active) s h]
      exact Nat.zero_le _

theorem prep_mean {p c n : Nat} (v : Fin n) (x : Config p c n) (d : Nat)
    (hn : 4≤n) (h : Live v (RankSupplier.init x d)) :
    IIDExpectedHittingTimeAtMost (prepStep v) (fun s => s.flag ≠ .active)
      (prepInit x d) (19*n^2) := by
  obtain ⟨L,paths,hL,hp,hcount,hfinish⟩ :=
    QueueDAG.virtual_outlet_paths hn v (virtualInit v (RankSupplier.init x d))
  let C := unpaused_certificate hn v (RankSupplier.init x d) h
    ⟨L,paths,hL,hp,hcount,hfinish⟩
    (literal_fifo_projection hn v (RankSupplier.init x d) h)
  intro t
  exact Nat.le_trans (prep_cost_le v (prepInit x d) (fun _ => rfl) t)
    (fixedSupplier_mean_of_certificate hn v (RankSupplier.init x d) C t)

/-- Any unskipped preparation takes a genuine quiet raw step. -/
theorem prep_step_rows {p c n : Nat} (v e : Fin n) (s : Prep p c n)
    (ha : s.flag=.active) (hs : s.supplier.stopped=false) :
    (prepStep v s e).supplier.config=step s.supplier.config e ∧
    ((prepStep v s e).flag=.retired ↔ retirement s.supplier.config e=true) ∧
    ((prepStep v s e).flag=.killed ↔ retirement s.supplier.config e=false ∧
      death s.supplier.config e=true) ∧
    ((prepStep v s e).flag=.targetBorn ↔ event s.supplier.config e=false ∧
      (RankSupplier.advance v s.supplier e).stopped=true) := by
  have hstep : (RankSupplier.advance v s.supplier e).config=step s.supplier.config e := by
    unfold RankSupplier.advance
    simp only [hs,Bool.false_eq_true,if_false]
    split <;> rfl
  cases hr : retirement s.supplier.config e <;>
    cases hk : death s.supplier.config e <;>
    cases hB : (RankSupplier.advance v s.supplier e).stopped <;>
    simp [prepStep,ha,hr,hk,hB,hstep,event]

/-- A surviving first kill reaches the concrete fresh stage from the
completed pair. The same-mark pay and retirement order is not inferred
from the endpoint leader count alone. -/
theorem transition_after_kill {p c n : Nat} (hn : 4≤n)
    (x : Config p c n) (e : Fin n) (hq : QuietEntrance x)
    (hkill : death x e=true) (hr : retirement x e=false) :
    ∃ v s, s.config=step x e ∧ RankSupplier.Protected v s ∧
      FreshEpochEarly.freshInit s.config v s.donor := by
  have hL := ((death_iff_nativeKill x e).mp hkill).1
  have hne : rightNeighbor e≠e := by
    intro h
    have hEq : liftedSite e 1=liftedSite e 0 := by
      simpa [liftedSite_succ,liftedSite_zero] using h
    have hh := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) hEq
    omega
  have hD := (death_iff_leader_loss x e hne hq.2.1 hL).mp hkill
  exact FreshEpochEntry.kill_starts_fresh_epoch hn x e hq hL hD hr

/-- Three possible nonterminal entries once the rootless observer has
found a surviving leader: one or two fixed-supplier pushes may be
skipped when the relevant successor is already living. -/
inductive NativeEntry {p c n : Nat} (x : Config p c n) : Type where
  | first (v : Fin n) (d : Nat) (h : Live v (RankSupplier.init x d))
  | second (v : Fin n) (a d : Nat) (ha : a+1<n)
      (hv : (x v).leader=true) (hF : FirstMark x v a)
      (h : Live (liftedSite v (a+1)) (RankSupplier.init x d))
  | deletion (v : Fin n) (a b : Nat) (h : TripleResidual.Start x v a b)

/-- Start the second push, or skip it if the next root already lives.
The rank-two case repeats the first endpoint rather than introducing
a third identity. -/
noncomputable def afterFirst {p c n a : Nat} (x : Config p c n) (v : Fin n)
    (hm : MCOV x) (hr : 2≤rank x) (ha : a+1<n)
    (hv : (x v).leader=true) (hF : FirstMark x v a)
    (hV : (x (liftedSite v (a+1))).leader=true) : NativeEntry x := by
  let u := liftedSite v (a+1)
  have ex := RestartGeometry.living_next x u hm hr hV
  let b := Classical.choose ex
  have hb : FirstMark x u b ∧ b+1<n := Classical.choose_spec ex
  exact if hW : (x (liftedSite u (b+1))).leader=true then
    .deletion v a b
      (RestartGeometry.deletion_start_of_successive_births x v hm hv ha hF hb.1 hV hW)
  else .second v a b ha hv hF
    (live_init x u hm hV (Bool.eq_false_iff.mpr hW) hb.1 hb.2)

/-- Select any physical living root predictably at the current cut.
All subsequent routing uses its ambient successors, not a compressed
list of living sites. -/
noncomputable def afterActivation {p c n : Nat} (x : Config p c n)
    (hm : MCOV x) (hr : 2≤rank x) (hl : ¬RankRootless.NoLiving x) :
    NativeEntry x := by
  have ex := RestartGeometry.chosen_living_next x hm hr hl
  let v := Classical.choose ex
  have exA := Classical.choose_spec ex
  let a := Classical.choose exA
  have K := Classical.choose_spec exA
  have hv := K.1
  have hF := K.2.1
  have ha := K.2.2
  exact if hV : (x (liftedSite v (a+1))).leader=true then
    afterFirst x v hm hr ha hv hF hV
  else .first v a (live_init x v hm hv (Bool.eq_false_iff.mpr hV) hF ha)

/-- A continuing second push cannot change the first prepared sector
on an unrelated raw mark, so its original identity and gap persist. -/
theorem second_keep_prefix {p c n a : Nat} (hn : 4≤n) (v e : Fin n)
    (s : RankSupplier.Obs p c n) (h : Live (liftedSite v (a+1)) s)
    (hC : COV s.config) (hv : (s.config v).leader=true)
    (hF : FirstMark s.config v a) (ha : a+1<n) (he : event s.config e=false)
    (hu : (RankSupplier.advance (liftedSite v (a+1)) s e).stopped=false) :
    let z := RankSupplier.advance (liftedSite v (a+1)) s e
    (z.config v).leader=true ∧ FirstMark z.config v a ∧
      Live (liftedSite v (a+1)) z := by
  let u := liftedSite v (a+1)
  have hS := live_step hn u e s h hu
  have hU := no_event_preserves_leader hn s.config e v hC he hv
  have hP := no_event_sector hn s.config e v h.2.1 hC he hv h.2.2.1 hF ha
  have hEq := (RankSupplierPhysical.unstopped_fields u e s h.1 hu).1
  exact ⟨hEq ▸ hU,hEq ▸ hP,hS⟩

/-- Finishing the second push without a kill or retirement provides
the full physical deletion-start invariant. -/
theorem second_success_deletion {p c n a : Nat} (hn : 4≤n) (v e : Fin n)
    (s : RankSupplier.Obs p c n) (h : Live (liftedSite v (a+1)) s)
    (hC : COV s.config) (hv : (s.config v).leader=true)
    (hF : FirstMark s.config v a) (ha : a+1<n) (he : event s.config e=false)
    (hu : (RankSupplier.advance (liftedSite v (a+1)) s e).stopped=true) :
    ∃ b, TripleResidual.Start (step s.config e) v a b := by
  let u := liftedSite v (a+1)
  let pay := geometricPay (s.config e) (s.config (rightNeighbor e))
  let b := s.donor + ((e == liftedSite u s.donor) && pay).toNat
  have K := RestartAudit.second_birth_joins_first_sector hn v e s h hC hv hF ha hu he
  change FirstMark (step s.config e) v a ∧ FirstMark (step s.config e) u b ∧
    b+1<n ∧ ((step s.config e) v).leader=true ∧ ((step s.config e) u).leader=true ∧
    ((step s.config e) (liftedSite u (b+1))).leader=true at K
  exact ⟨b,RestartGeometry.deletion_start_of_successive_births _ v
    (EntranceCover.cover_closed hn s.config e ⟨h.2.1,hC⟩).1
    K.2.2.2.1 ha K.1 K.2.1 K.2.2.2.2.1 K.2.2.2.2.2⟩

end L4.RestartRouting

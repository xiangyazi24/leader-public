import Leader.L4.RankSupplier
import Leader.L4.RearRefillTrack

/-! # Literal predictable pause reserve for the fixed-supplier stage -/

namespace L4.RankSupplier

def payEdge {p c n : Nat} (v : Fin n) (s : Obs p c n) : Fin n :=
  liftedSite v s.donor

private theorem marked_ghost_payment {p c : Nat} (u v : Site p c)
    (hm : u.mark = true) (hL : v.leader = false) (hpay : payer u = true) :
    geometricPay u v = true := by
  have hm0 : materialize u v = u := by
    cases u
    simp_all [materialize]
  have ha : (fireInitiator u).mark = true ∧ payer (fireInitiator u) = true := by
    unfold fireInitiator
    split <;> exact ⟨hm,hpay⟩
  unfold geometricPay native
  rw [hm0]
  have hv : fireResponder v = v := by simp [fireResponder,hL]
  rw [hv]
  have hi (a : Site p c) : impact a v = (a,v) := by simp [impact,hL]
  rw [hi]
  generalize fireInitiator u = a at ha ⊢
  simp only [pinned,ha.1,hL,Bool.not_false,Bool.and_true]
  cases hb : !(a.bullet == .none) <;>
    simp [followerBullet,hb,ha.1,hL,payer] <;> simpa only [payer,Bool.or_eq_true] using ha.2 

theorem payEdge_when_stock {p c n : Nat} (v : Fin n) (s : Obs p c n)
    (h : Live v s) (hs : (s.config (payEdge v s)).stock = true) :
    geometricPay (s.config (payEdge v s)) (s.config (rightNeighbor (payEdge v s))) = true := by
  have hghost : (s.config (rightNeighbor (payEdge v s))).leader = false := by
    unfold payEdge
    rw [← liftedSite_succ]
    exact h.2.2.2.1
  exact marked_ghost_payment _ _ h.2.2.2.2.1.marked hghost (by simp [payer,hs])

theorem liveAdvance_fields {p c n : Nat} (v e : Fin n) (s : Obs p c n)
    (hs : s.stopped = false) (ht : (advance v s e).stopped = false) :
    let t := advance v s e
    t.config = step s.config e ∧
      t.donor = s.donor + ((e == payEdge v s) &&
        geometricPay (s.config e) (s.config (rightNeighbor e))).toNat := by
  unfold advance at ht ⊢
  simp only [hs,Bool.false_eq_true,if_false] at ht ⊢
  split at ht <;> simp_all [payEdge]

private theorem right_ne {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have h' : liftedSite e 1 = liftedSite e 0 := by
    simpa [liftedSite_succ,liftedSite_zero] using h
  have hh := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) h'
  omega

/-- An occupied responder retains its stock on every literal row,
including ordinary blocking, P0, P3 and the final P5. -/
theorem occupied_receiver_stays {p c : Nat} (u v : Site p c)
    (h : v.stock = true) : (pairStep u v).2.stock = true := by
  let l : Option Unit := if u.stock then some () else none
  have hl : l.isSome = u.stock := by cases hh : u.stock <;> simp [l,hh]
  have ht := StockTokenRows.pair_labels u v l (some ()) () hl
    (show (some () : Option Unit).isSome = v.stock by simp [h])
  have hh := congrArg Prod.snd ht
  change (StockTokenRows.update (StockTokenRows.row u v) l (some ()) ()).2.isSome =
    (pairStep u v).2.stock at hh
  rw [GGStockPhysical.incoming_retains_label u v l () () h] at hh
  exact hh.symm

theorem stock_stays_off_outgoing {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (e j : Fin n) (he : j ≠ e) (hj : (x j).stock = true) : (step x e j).stock = true := by
  by_cases hr : j = rightNeighbor e
  · subst j
    simpa [step,right_ne hn e] using occupied_receiver_stays (x e) (x (rightNeighbor e)) hj
  · simpa [step,he,hr] using hj

/-- Pause is remembered only for the resident exposed by a tracked P3.
Ordinary occupancy of the current donor alone does not start a pause. -/
def pauseNext {p c n : Nat} (v : Fin n) (s t : Obs p c n) (pending : Bool) : Bool :=
  if t.stopped then false
  else if s.donor < t.donor then (t.config (payEdge v t)).stock else pending

def pauseOK {p c n : Nat} (v : Fin n) (s : Obs p c n) (pending : Bool) : Prop :=
  pending = true → s.stopped = false → (s.config (payEdge v s)).stock = true

def pauseCredit {p c n : Nat} (s : Obs p c n) : Nat :=
  if s.stopped then 0 else n-s.donor

theorem pauseNext_ok {p c n : Nat} (hn : 4 ≤ n) (v e : Fin n)
    (s : Obs p c n) (pending : Bool) (h : Live v s) (hP : pauseOK v s pending) :
    pauseOK v (advance v s e) (pauseNext v s (advance v s e) pending) := by
  let t := advance v s e
  intro hp hstop
  by_cases hM : s.donor < t.donor
  · simpa [t,pauseNext,hstop,hM] using hp
  · have hi := donor_mono_step v e s
    have heq : t.donor = s.donor := by change s.donor ≤ t.donor at hi; omega
    have hpend : pending = true := by simpa [t,pauseNext,hstop,hM] using hp
    have hstock := hP hpend h.1
    have he : payEdge v s ≠ e := by
      intro heq'
      have hpay := payEdge_when_stock v s h hstock
      have hh := (liveAdvance_fields v (payEdge v s) s h.1 (by rwa [heq'])).2
      have heq'' : (advance v s (payEdge v s)).donor = s.donor := by
        rw [heq']; exact heq
      rw [heq'',hpay] at hh
      simp at hh
    have hc := (liveAdvance_fields v e s h.1 hstop).1
    change (t.config (payEdge v t)).stock = true
    have hPay : payEdge v t = payEdge v s := by unfold payEdge; rw [heq]
    rw [hPay,hc]
    exact stock_stays_off_outgoing hn s.config e _ he hstock

theorem pauseCredit_nonincrease {p c n : Nat} (v e : Fin n) (s : Obs p c n) :
    pauseCredit (advance v s e) ≤ pauseCredit s := by
  by_cases hs : s.stopped = true
  · simp [advance,hs,pauseCredit]
  · by_cases ht : (advance v s e).stopped = true
    · simp [pauseCredit,ht]
    · simp only [pauseCredit,if_neg hs,if_neg ht]
      have h := donor_mono_step v e s
      omega

/-- A pending resident forces credit expenditure on the single premark
nomination; the terminal mark may spend all remaining credit. -/
theorem pauseCredit_hit {p c n : Nat} (v : Fin n) (s : Obs p c n)
    (h : Live v s) (hs : (s.config (payEdge v s)).stock = true) :
    pauseCredit (advance v s (payEdge v s))+1 ≤ pauseCredit s := by
  have hcap := h.2.2.2.2.2
  have hp := payEdge_when_stock v s h hs
  cases ht : (advance v s (payEdge v s)).stopped
  · have hd := (liveAdvance_fields v (payEdge v s) s h.1 ht).2
    simp [hp] at hd
    simp only [pauseCredit,h.1,ht,Bool.false_eq_true,if_false]
    omega
  · simp only [pauseCredit,h.1,ht,if_true,Bool.false_eq_true,if_false]
    omega

end L4.RankSupplier

#print axioms L4.RankSupplier.payEdge_when_stock
#print axioms L4.RankSupplier.occupied_receiver_stays
#print axioms L4.RankSupplier.pauseNext_ok
#print axioms L4.RankSupplier.pauseCredit_nonincrease
#print axioms L4.RankSupplier.pauseCredit_hit

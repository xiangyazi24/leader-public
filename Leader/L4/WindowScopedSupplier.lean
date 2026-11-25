import Leader.L4.WindowLocal
import Leader.L4.FreshSupplierTrack
import Leader.L4.FreshEpochEntry

namespace L4.WindowScopedSupplier
open RankSupplier SevenTagCharge RankPhysical

private theorem right_ne {n : Nat} (hn : 4 ≤ n) (v : Fin n) : rightNeighbor v ≠ v := by
  intro h
  have h' : liftedSite v 1 = liftedSite v 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hb := liftedSite_inj v (by omega : 1<n) (by omega : 0<n) h'
  omega

theorem firstMark_after_local_step {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (v e : Fin n) (hm : MCOV x) (hd : FirstMark x v d)
    (hcap : d+1 < n) (hL0 : (x v).leader = true) (hL : ((step x e) v).leader = true)
    (hret : e=liftedSite v d →
      (geometricPay (x e) (x (rightNeighbor e)) && (x (rightNeighbor e)).mark) = false) :
    let d' := d + ((e == liftedSite v d) && geometricPay (x e) (x (rightNeighbor e))).toNat
    FirstMark (step x e) v d' ∧ d'+1 < n := by
  let pay := geometricPay (x e) (x (rightNeighbor e))

  have hein (hp : pay = true) : rightNeighbor e ≠ v := by
    intro he
    have hf := TaggedTrace.geometricPay_responder_nonleader (x e) (x (rightNeighbor e)) hp
    have hv : (step x e v).leader = false := by
      have hne : v ≠ e := fun he' => right_ne hn e (he.trans he')
      simpa [step,he,hne] using hf
    rw [hL] at hv
    contradiction
  have hpre (k : Nat) (hk : 0 < k) :
      rightNeighbor (liftedSite v (k-1)) = liftedSite v k := by
    rw [← liftedSite_succ,show k-1+1=k by omega]
  have hcovered (k : Nat) (hk : 0 < k) (hk' : k ≤ d)
      (hp : pay = true) : liftedSite v k ≠ rightNeighbor e := by
    intro heq
    have hf := (covered_pair_marks (x e) (x (rightNeighbor e)) (hm e))
    change (if pay then _ else _) at hf
    rw [if_pos hp] at hf
    have hm' : (x (liftedSite v (k-1))).mark = true := by
      have heq' : liftedSite v (k-1) = e := by
        have hr := (hpre k hk).trans heq
        have hh := congrArg RearTrace.predecessor hr
        simpa only [RearTrace.predecessor_right] using hh
      simpa [heq'] using hf.1
    exact hd.before _ (by omega) hm'
  have hnew (k : Nat) (hk : k ≤ d) (hp : pay = true) :
      liftedSite v k ≠ rightNeighbor e := by
    cases k with
    | zero => simpa [liftedSite_zero] using Ne.symm (hein hp)
    | succ k => exact hcovered _ (by omega) hk hp
  dsimp only
  by_cases hpay : pay = true
  · have hg : geometricPay (x e) (x (rightNeighbor e)) = true := hpay
    by_cases he : e = liftedSite v d
    · have hd' : d+2 < n := by
        by_cases h : d+2 < n
        · exact h
        · have hk : liftedSite v (d+2) = v := by
            rw [show d+2=n by omega,liftedSite_full]
          have hm' : (x (liftedSite v (d+1))).mark = true := by
            apply hm
            left
            rw [← liftedSite_succ]
            exact hk.symm ▸ hL0
          have h := hret he
          change (pay && (x (rightNeighbor e)).mark)=false at h
          rw [hpay, Bool.true_and, he, ← liftedSite_succ, hm'] at h
          contradiction
      have hE : (e == liftedSite v d) = true := beq_iff_eq.mpr he
      simp only [hE,hg,Bool.and_self,Bool.toNat_true]
      refine ⟨⟨by omega,?_,?_⟩,by omega⟩
      · rw [covered_step_mark hn x hm]
        rw [if_pos hg]
        have heq : liftedSite v (d+1) = rightNeighbor e := by rw [he,liftedSite_succ]
        simp [heq,right_ne hn e]
      · intro k hk
        rw [covered_step_mark hn x hm]
        have hn' := hnew k (by omega) hpay
        by_cases hke : liftedSite v k = e
        · simp [hg,hke]
        · have hk' : k < d := by
            by_cases hh : k = d
            · subst k; exact False.elim (hke he.symm)
            · omega
          simpa [hg,hke,hn'] using hd.before k hk'
    · have hE : (e == liftedSite v d) = false := Bool.eq_false_iff.mpr
        (fun h => he (beq_iff_eq.mp h))
      simp only [hE,Bool.false_and,Bool.toNat_false,Nat.add_zero]
      refine ⟨⟨hd.lt,?_,?_⟩,hcap⟩
      · rw [covered_step_mark hn x hm]; simp [hg,Ne.symm he,hd.marked]
      · intro k hk
        rw [covered_step_mark hn x hm]
        by_cases hke : liftedSite v k = e
        · simp [hg,hke]
        · simpa [hg,hke,hnew k (by omega) hpay] using hd.before k hk
  · have hg : geometricPay (x e) (x (rightNeighbor e)) = false := Bool.eq_false_iff.mpr hpay
    simp only [hg,Bool.and_false,Bool.toNat_false,Nat.add_zero]
    refine ⟨⟨hd.lt,?_,?_⟩,hcap⟩
    · simpa [covered_step_mark hn x hm,hg] using hd.marked
    · intro k hk
      simpa [covered_step_mark hn x hm,hg] using hd.before k hk

/-- This update records all actual pair effects. Only the calling
window router decides whether the current stage is still live. -/
def follow {p c n : Nat} (v : Fin n) (d : Nat) (x : Config p c n) (e : Fin n) :
    RankSupplier.Obs p c n :=
  RankSupplier.init (step x e)
    (d+((e == liftedSite v d) && geometricPay (x e) (x (rightNeighbor e))).toNat)

theorem tracked_no_retirement_of_group_keep {p c n : Nat} (g : List (Fin n))
    (z : Ledger p c n) (e a : Fin n) (ha : a ∈ g) (hs : z.slots e=some a)
    (h : WindowLocal.selectedGroupLoss g z e=none) :
    retirement z.config e=false := by
  apply Bool.eq_false_iff.mpr
  intro hr
  have hg : WindowLocal.selectedGroupLoss g z e=some a :=
    (WindowLocal.selectedGroupLoss_iff g z e a).mpr ⟨by simp [lostStep,hr,hs],ha⟩
  rw [h] at hg
  cases hg

/-- Exact local successor rule on a protected corridor; a non-target
retirement is not an exit. Absence of birth is tested at the post-P3
target site by the caller. -/
theorem protected_follow {p c n d : Nat} (hn : 4≤n)
    (x : Config p c n) (v e : Fin n) (h : Protected v (RankSupplier.init x d))
    (hc : COV x) (hret : e=liftedSite v d → retirement x e=false)
    (hGhost : ((step x e) (liftedSite v ((follow v d x e).donor+1))).leader=false) :
    Protected v (follow v d x e) := by
  let s := follow v d x e
  have hn' : d≤s.donor := Nat.le_add_right _ _
  have hs := RankFresh.corridor_supplier_step hn x v e h.1.2.1 h.2
  have hD := firstMark_after_local_step hn x v e h.1.2.1 h.2.first h.2.gap
    h.2.leader hs.1 hret
  have hm := (EntranceCover.cover_closed hn x e ⟨h.1.2.1,hc⟩).1
  obtain ⟨j,hj,hF,hClean⟩ := RankFresh.corridor_separator_step hn x v e h.1.2.1 h.2
  exact ⟨⟨rfl,hm,hs.1,hGhost,hD.1,hD.2⟩,
    ⟨hD.1,hD.2,hGhost,hs.1,hs.2.1,⟨j,Nat.le_trans hj hn',hF,hClean⟩⟩⟩

/-- Off the target's incoming bond, its gap remains unchanged and the
ghost cannot be born. In particular all exterior retirements with no
group loss can pass through this fixed-gap protection observer. -/
theorem exterior_continues_protection {p c n d : Nat} (hn : 4≤n)
    (x : Config p c n) (v e : Fin n) (h : Protected v (RankSupplier.init x d))
    (hc : COV x) (he : e≠liftedSite v d) :
    (follow v d x e).donor=d ∧ Protected v (follow v d x e) := by
  have hb : (e == liftedSite v d)=false :=
    Bool.eq_false_iff.mpr (fun h => he (beq_iff_eq.mp h))
  have hD : (follow v d x e).donor=d := by simp [follow,RankSupplier.init,hb]
  refine ⟨hD,protected_follow hn x v e h hc (fun H => (he H).elim) ?_⟩
  rw [hD]
  let u := liftedSite v (d+1)
  have hR : rightNeighbor e≠u := by
    intro h
    have heq : rightNeighbor e=rightNeighbor (liftedSite v d) :=
      h.trans (liftedSite_succ v d)
    have hh := congrArg RearTrace.predecessor heq
    exact he (by simpa only [RearTrace.predecessor_right] using hh)
  have hU : (x u).leader=false := h.2.ghost
  change ((step x e) u).leader=false
  by_cases hEq : u=e
  · rw [hEq] at hU ⊢
    simp [step,(pair_geometric_fields (x e) (x (rightNeighbor e))).2.1,hU]
  · simpa [step,hEq,Ne.symm hR] using hU

theorem followed_exterior_stock {p c n d : Nat} (x : Config p c n)
    (v : Fin n) (l : Fin n) (hG : d+1<n) (hl : d<l.val) :
    let s := RankSupplier.init x d
    let t := follow v d x (liftedSite v l.val)
    t.donor=d ∧ RankSupplierPhysical.realStock v t=RankSupplierPhysical.realStock v s := by
  let e := liftedSite v l.val
  let t := follow v d x e
  let u := RankSupplier.init x d
  have eD : e≠liftedSite v d := by
    intro hh
    have H := liftedSite_inj v l.isLt (show d<n by omega) hh
    omega
  have hb : (e == liftedSite v d)=false := Bool.eq_false_iff.mpr fun h => eD (beq_iff_eq.mp h)
  have hd : t.donor=d := by simp [t,follow,RankSupplier.init,hb]
  refine ⟨hd,funext fun k => ?_⟩
  change RankSupplierPhysical.realStock v t k = RankSupplierPhysical.realStock v u k
  by_cases hk : 0<k ∧ k≤d
  · have he : liftedSite v k≠e := by
      intro h
      have hh := liftedSite_inj v (show k<n by omega) l.isLt h
      omega
    have hr : liftedSite v k≠rightNeighbor e := by
      intro hh
      rw [←liftedSite_succ] at hh
      by_cases hL : l.val+1<n
      · have h := liftedSite_inj v (show k<n by omega) hL hh
        omega
      · rw [show l.val+1=n by have := l.isLt; omega,liftedSite_full] at hh
        have h := liftedSite_inj v (show k<n by omega) (show 0<n by omega)
          (hh.trans (liftedSite_zero v).symm)
        omega
    have hx : t.config=step x e := rfl
    simp [RankSupplierPhysical.realStock,hd,hk,hx,step,he,hr,u,RankSupplier.init]
  · simp [RankSupplierPhysical.realStock,hd,hk,u,RankSupplier.init]

/-- The fixed-line stock comparison continues even on a foreign retirement.
The literal older global observer may stop there, but the measured
stock and payment count both stutter. -/
theorem real_cut_after_local_step {p c n d d0 : Nat} (hn : 4≤n) (v : Fin n)
    (x : Config p c n) (l : Fin n) (h : Live v (RankSupplier.init x d)) (hd0 : d0≤d)
    (hret : liftedSite v l.val=liftedSite v d →
      retirement x (liftedSite v l.val)=false)
    (hLive : Live v (follow v d x (liftedSite v l.val))) :
    let s := RankSupplier.init x d
    let t := follow v d x (liftedSite v l.val)
    FIFOCompare.RealStep (n-1) l.val (RankSupplierPhysical.realStock v s)
      (FIFOCompare.cuts (n-1) (RankSupplierPhysical.realStock v s) (d-d0))
      (FIFOCompare.cuts (n-1) (RankSupplierPhysical.realStock v t) (t.donor-d0)) := by
  let e := liftedSite v l.val
  let s := RankSupplier.init x d
  let t := follow v d x e
  unfold follow at hLive
  by_cases hR : retirement x e=true
  · have hM : (x e).mark=true :=
      RearTrace.paid_was_marked h.2.1 e
        (Bool.and_eq_true_iff.mp hR).1
    have hl : d<l.val := by
      by_cases hL : l.val<d
      · exact (h.2.2.2.2.1.before l.val hL hM).elim
      · by_cases hl' : l.val=d
        · have hN := hret (by rw [hl'])
          change retirement x e=false at hN
          rw [hR] at hN
          cases hN
        · omega
    have gap : d+1<n := h.2.2.2.2.2
    have H := followed_exterior_stock x v l gap hl
    have hS : RankSupplierPhysical.realStock v t=RankSupplierPhysical.realStock v s := H.2
    have hD : t.donor=d := H.1
    change FIFOCompare.RealStep (n-1) l.val (RankSupplierPhysical.realStock v s) _
      (FIFOCompare.cuts (n-1) (RankSupplierPhysical.realStock v t) (t.donor-d0))
    rw [hS,hD]
    refine ⟨fun _ _ _ => Nat.le_refl _,fun hz _ => (by omega : False).elim,?_⟩
    intro _ _ hi _
    have hF := RankSupplierPhysical.realStock_cutoff v s l.val (Or.inl hl)
    rw [hF] at hi
    cases hi
  · have he := Bool.eq_false_iff.mpr hR
    have hN : stop x (step x e) v e t.donor (geometricPay (x e) (x (rightNeighbor e)))=false := by
      have hv : ((step x e) v).leader=true := hLive.2.2.1
      have hh : ((step x e) (liftedSite v (t.donor+1))).leader=false := hLive.2.2.2.1
      change (geometricPay (x e) (x (rightNeighbor e)) && (x (rightNeighbor e)).mark)=false at he
      simp [stop,he,hv,hh]
    have hEq : advance v s e=t := by
      change (if s.stopped then s else
        if stop x (step x e) v e t.donor (geometricPay (x e) (x (rightNeighbor e))) then
          ⟨step x e,d,true⟩ else t)=t
      simp [s,RankSupplier.init,hN]
    have hg : (advance v s e).stopped=false := by rw [hEq]; rfl
    have H := RankSupplierPhysical.literal_real_step hn v s h hd0 l hg
    change FIFOCompare.RealStep (n-1) l.val (RankSupplierPhysical.realStock v s) _
      (FIFOCompare.cuts (n-1) (RankSupplierPhysical.realStock v t) (t.donor-d0))
    rw [←hEq]
    exact H

end L4.WindowScopedSupplier


import Leader.L4.WindowA0Rows
import Leader.L4.RestartGeometry
import Leader.L4.WindowScopedFourHead

namespace L4.WindowA0Drained
open GGStage WindowA0Rows

theorem marked_left_no_injection {p c : Nat} (u v : Site p c)
    (hm : u.mark=true) (hl : u.leader=false) (hs : u.stock=false) :
    (pairStep u v).1.stock=false := by
  have hRight := RearFrontStock.marked_right_stock u v hm
  have hSum := RearFrontStock.pair_stock_le_of_nonleader u v hl
  cases output : (pairStep u v).1.stock
  · rfl
  · simp [RearFrontStock.stockBit,hRight,hs,output] at hSum
    omega

private theorem site_stock_of_left {p c n : Nat} (x : Config p c n) (e : Fin n) :
    (step x e e).stock = (pairStep (x e) (x (rightNeighbor e))).1.stock := by simp [step]

private theorem site_stock_of_right {p c n : Nat} (x : Config p c n) (e : Fin n)
    (he : rightNeighbor e≠e) :
    (step x e (rightNeighbor e)).stock = (pairStep (x e) (x (rightNeighbor e))).2.stock := by
  simp [step,he]

/-- Rebase at I. The retained interval includes I's own stock byte.
All physical marks preserve its emptiness even before dropping a
successful paid top, and J cannot pay from within that interval. -/
theorem drained_step {p c n h : Nat} (hn : 4≤n) (x : Config p c n) (base e : Fin n)
    (hh : 0<h)
    (hmI : (x (incoming base 0)).mark=true) (hmJ : (x (incoming base h)).mark=true)
    (vac : ∀ k, k<h → (x (liftedSite base k)).stock=false)
    (non : ∀ k, k<h → (x (liftedSite base k)).leader=false) :
    moved x base e h=false ∧
    ∀ k, k<h → (step x e (liftedSite base k)).stock=false := by
  have notLoop : rightNeighbor e≠e := by
    intro hEq
    have h := liftedSite_inj e (show 1<n by omega) (show 0<n by omega)
      (show liftedSite e 1=liftedSite e 0 by simpa [liftedSite_zero,liftedSite_succ] using hEq)
    omega
  have pred (i : Nat) (hi : 0<i) : incoming base i=liftedSite base (i-1) := by
    apply FreshSeparation.succ_inj
    rw [incoming_right,←liftedSite_succ,show i-1+1=i by omega]
  refine ⟨?_,?_⟩
  · apply Bool.eq_false_iff.mpr
    intro hp
    obtain ⟨he,hpay⟩ := Bool.and_eq_true_iff.mp hp
    have hE : e=liftedSite base (h-1) := (beq_iff_eq.mp he).trans (pred h hh)
    rw [hE] at hpay
    have hp' := RearTrace.geometricPay_ready _ _ hpay
    have hlt : h-1<h := by omega
    simp [payer,vac _ hlt,non _ hlt] at hp'
  · intro k hk
    by_cases he : liftedSite base k=e
    · rw [he, site_stock_of_left]
      rw [←he,←liftedSite_succ]
      by_cases hk' : k+1<h
      · exact (unstocked_nonleader_pair _ _ (non k hk) (vac k hk) (vac _ hk')).1
      · have hh' : h=k+1 := by omega
        have hEk : liftedSite base k=incoming base h := by
          rw [pred h hh, hh']
          simp
        exact marked_left_no_injection _ _ (hEk.symm ▸ hmJ) (non k hk) (vac k hk)
    · by_cases hr : liftedSite base k=rightNeighbor e
      · rw [hr,site_stock_of_right x e notLoop]
        have hhIn : e=incoming base k := FreshSeparation.succ_inj
          (hr.symm.trans (incoming_right base k).symm)
        by_cases hk0 : k=0
        · have hMarked := (show (x e).mark=true by rwa [hhIn,hk0])
          exact (RearFrontStock.marked_right_stock _ _ hMarked).trans (hr ▸ vac k hk)
        · have eL : e=liftedSite base (k-1) := hhIn.trans (pred k (by omega))
          have hlt : k-1<h := by omega
          rw [eL,show rightNeighbor (liftedSite base (k-1))=liftedSite base k by rw [←eL,hr]]
          exact (unstocked_nonleader_pair _ _ (non _ hlt) (vac _ hlt) (vac _ hk)).2
      · simpa [step,he,hr] using vac k hk

/-- The local stock result survives dropping an overtaken top and
rebasing there. No bound on the scheduling of the upstream feeding
leader is used. -/
theorem drained_after_top_rebase {p c n h : Nat} (hn : 4≤n)
    (x : Config p c n) (base e : Fin n) (hh : 0<h)
    (hmI : (x (incoming base 0)).mark=true) (hmJ : (x (incoming base h)).mark=true)
    (vac : ∀ k, k<h → (x (liftedSite base k)).stock=false)
    (non : ∀ k, k<h → (x (liftedSite base k)).leader=false) :
    let i := (moved x base e 0).toNat
    moved x base e h=false ∧
    ∀ k, k<h-i → (step x e (liftedSite (liftedSite base i) k)).stock=false := by
  let i := (moved x base e 0).toNat
  obtain ⟨hJ, hEmpty⟩ := drained_step hn x base e hh hmI hmJ vac non
  refine ⟨hJ,?_⟩
  intro k hk
  change (step x e (liftedSite (liftedSite base i) k)).stock=false
  rw [RestartGeometry.lift_add]
  exact hEmpty _ (by omega)

end L4.WindowA0Drained

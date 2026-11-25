import Leader.L4.RearTrackGeometry
import Leader.L4.StockTokenRows

namespace L4.RearFrontStock

open StockTokenRows

private def stockLabel (b : Bool) : Option Unit := if b then some () else none

private theorem stockLabel_some (b : Bool) : (stockLabel b).isSome = b := by
  cases b <;> rfl

private theorem row_bits {p c : Nat} (u v : Site p c) :
    let a := update (row u v) (stockLabel u.stock) (stockLabel v.stock) ()
    (a.1.isSome,a.2.isSome) = ((pairStep u v).1.stock,(pairStep u v).2.stock) :=
  pair_labels u v _ _ () (stockLabel_some u.stock) (stockLabel_some v.stock)

/-- Stock occupancy in exact integer units. -/
def stockBit {p c : Nat} (u : Site p c) : Int := u.stock.toNat

/-- No selected initiator acquires stock from its responder. -/
theorem left_stock_le {p c : Nat} (u v : Site p c) :
    stockBit (pairStep u v).1 ≤ stockBit u := by
  have h := congrArg Prod.fst (row_bits u v)
  dsimp only at h
  unfold stockBit
  rw [← h]
  cases ha : row u v <;> cases u.stock <;> cases v.stock <;> decide

/-- A nonleader cannot create stock in the selected pair. This includes
native kills and ordinary P2 transport, and P5 preserves stock. -/
theorem pair_stock_le_of_nonleader {p c : Nat} (u v : Site p c)
    (h : u.leader = false) :
    stockBit (pairStep u v).1 + stockBit (pairStep u v).2 ≤ stockBit u + stockBit v := by
  have h₁ := congrArg Prod.fst (row_bits u v)
  have h₂ := congrArg Prod.snd (row_bits u v)
  dsimp only at h₁ h₂
  unfold stockBit
  rw [← h₁, ← h₂]
  cases ha : row u v with
  | mint =>
    have hh := (row_mint_input u v ha).2.1
    simp [h] at hh
  | stay =>
    simp [update, stockLabel_some]
  | drop =>
    simp [update, stockLabel_some]; omega
  | transfer =>
    simp [update,stockLabel_some]; omega

/-- The selected P3 mark's old donor loses its stock, including when the
payment is made by a living donor rather than by a resident token. -/
theorem paid_donor_empty {p c : Nat} (u v : Site p c)
    (h : geometricPay u v = true) : (pairStep u v).1.stock = false := by
  have hh := congrArg Prod.fst (row_bits u v)
  dsimp only at hh
  have hr : row u v = .drop := by
    let a := native (materialize u v) v
    change (!a.2.leader && a.1.mark && payer a.1) = true at h
    change action a.1 a.2 = .drop
    cases hL : a.2.leader <;> cases hM : a.1.mark <;> cases hP : payer a.1 <;>
      simp_all [action]
  rw [hr] at hh
  exact hh.symm

/-- Strict front inventory, with both the carrier (offset zero) and the
first marked donor (offset d) excluded. -/
def InFront {n : Nat} (b : Fin n) (d : Nat) (i : Fin n) : Prop :=
  ∃ j : Nat, 0 < j ∧ j < d ∧ liftedSite b j = i

noncomputable def maskedStock {p c n : Nat} (x : Config p c n) (b : Fin n)
    (d : Nat) (i : Fin n) : Int := by
  classical
  exact if InFront b d i then stockBit (x i) else 0

noncomputable def inventory {p c n : Nat} (x : Config p c n) (b : Fin n)
    (d : Nat) : Int :=
  BarrierIID.edgeSum (maskedStock x b d)

private theorem sum_succ {n : Nat} (f : Fin (n+1) → Int) :
    BarrierIID.edgeSum f = f 0 + BarrierIID.edgeSum (fun e : Fin n => f e.succ) := by
  simp [BarrierIID.edgeSum,List.ofFn_succ]

private theorem sum_mono {n : Nat} (f g : Fin n → Int) (h : ∀ i, f i ≤ g i) :
    BarrierIID.edgeSum f ≤ BarrierIID.edgeSum g := by
  induction n with
  | zero => simp [BarrierIID.edgeSum]
  | succ n ih => rw [sum_succ,sum_succ g]; exact Int.add_le_add (h 0) (ih _ _ (fun i => h i.succ))

private theorem sum_add {n : Nat} (f g : Fin n → Int) :
    BarrierIID.edgeSum (fun e => f e + g e) = BarrierIID.edgeSum f + BarrierIID.edgeSum g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_succ,sum_succ f,sum_succ g,ih]; omega

private theorem sum_sub {n : Nat} (f g : Fin n → Int) :
    BarrierIID.edgeSum (fun e => f e - g e) = BarrierIID.edgeSum f - BarrierIID.edgeSum g := by
  have h := sum_add (fun e => f e - g e) g
  have hg : (fun e => f e - g e + g e) = f := funext (fun e => by omega)
  rw [hg] at h
  omega

private theorem sum_const {n : Nat} (a : Int) :
    BarrierIID.edgeSum (fun _ : Fin n => a) = (n : Int) * a := by
  induction n with
  | zero => simp [BarrierIID.edgeSum]
  | succ n ih => rw [sum_succ,ih]; simp [Int.natCast_succ,Int.add_mul,Int.add_comm]

/-- A finite sum comparison with a possible redistribution between the
two selected physical endpoints. -/
theorem sum_pair_bound {n : Nat} (f g : Fin n → Int) (u v : Fin n) (hne : u ≠ v)
    (hoff : ∀ i, i ≠ u → i ≠ v → f i ≤ g i) (debit : Int)
    (hpair : f u + f v + debit ≤ g u + g v) :
    BarrierIID.edgeSum f + debit ≤ BarrierIID.edgeSum g := by
  let d := fun i => f i - g i
  let h := fun i => (if i = u then d u else 0) + (if i = v then d v else 0)
  have he : BarrierIID.edgeSum d ≤ BarrierIID.edgeSum h := by
    apply sum_mono
    intro i
    by_cases hu : i = u
    · subst i; simp [h,hne]
    · by_cases hv : i = v
      · subst i; simp [h,hne.symm]
      · have hh := hoff i hu hv
        simp [h,hu,hv,d]
        omega
  change BarrierIID.edgeSum (fun i => f i - g i) ≤ BarrierIID.edgeSum h at he
  rw [sum_sub] at he
  unfold h at he
  rw [sum_add,BarrierIID.edgeSum_selector,BarrierIID.edgeSum_selector] at he
  dsimp [d] at he
  omega

/-- Bounds are independent of the scheduler and hold at every truncation. -/
theorem inventory_interval {p c n : Nat} (x : Config p c n) (b : Fin n) (d : Nat) :
    0 ≤ inventory x b d ∧ inventory x b d ≤ (n : Int) := by
  classical
  unfold inventory
  have localB (i : Fin n) : 0 ≤ maskedStock x b d i ∧ maskedStock x b d i ≤ 1 := by
    by_cases h : InFront b d i <;> cases hc : (x i).stock <;> simp [maskedStock,stockBit,h,hc]
  constructor
  · rw [← show BarrierIID.edgeSum (fun _ : Fin n => 0) = 0 by simp [sum_const]]
    exact sum_mono _ _ (fun i => (localB i).1)
  · rw [← show BarrierIID.edgeSum (fun _ : Fin n => 1) = (n : Int) by simp [sum_const]]
    exact sum_mono _ _ (fun i => (localB i).2)


private theorem rn_ne {n : Nat} (hn : 4 ≤ n) (e : Fin n) : e ≠ rightNeighbor e := by
  intro hh
  apply Nat.zero_ne_one
  apply liftedSite_inj e (by omega : 0 < n) (by omega : 1 < n)
  rw [liftedSite_succ, liftedSite_zero]; exact hh

private theorem rn_inj {n : Nat} {a b : Fin n} (h : rightNeighbor a = rightNeighbor b) : a = b := by
  have hh := congrArg Fin.val h
  change (a.val+1)%n = (b.val+1)%n at hh
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  by_cases ha' : a.val+1 < n <;> by_cases hb' : b.val+1 < n
  · rw [Nat.mod_eq_of_lt ha',Nat.mod_eq_of_lt hb'] at hh; omega
  · rw [Nat.mod_eq_of_lt ha',show b.val+1=n by omega,Nat.mod_self] at hh; omega
  · rw [show a.val+1=n by omega,Nat.mod_self,Nat.mod_eq_of_lt hb'] at hh; omega
  · omega

private theorem no_leader_inside {p c n : Nat} {x : Config p c n} {b i : Fin n} {d : Nat}
    (hc : MCOV x) (h : FirstMark x b d) (hi : InFront b d i) : (x i).leader = false := by
  obtain ⟨j,hj,hjd,rfl⟩ := hi
  have hj' : liftedSite b j = rightNeighbor (liftedSite b (j-1)) := by
    rw [← liftedSite_succ,show j-1+1=j by omega]
  apply Bool.eq_false_iff.mpr
  intro ha
  exact h.before (j-1) (by omega) (hc _ (Or.inl (hj' ▸ ha)))

private theorem previous_inside {n : Nat} {b e : Fin n} {d : Nat}
    (he : e ≠ b) (h : InFront b d (rightNeighbor e)) : InFront b d e := by
  obtain ⟨j,hj,hjd,hi⟩ := h
  have hd : liftedSite b (j-1) = e := by
    apply rn_inj
    rw [← liftedSite_succ,show j-1+1=j by omega,hi]
  refine ⟨j-1, ?_,by omega,hd⟩
  by_cases hJ : j=1
  · simp [hJ,liftedSite_zero] at hd
    exact (he hd.symm).elim
  · omega

private theorem at_right {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) (e : Fin n) :
    step x e (rightNeighbor e) = (pairStep (x e) (x (rightNeighbor e))).2 := by
  simp [step,(rn_ne hn e).symm]

private theorem at_left {p c n : Nat} (x : Config p c n) (e : Fin n) :
    step x e e = (pairStep (x e) (x (rightNeighbor e))).1 := by simp [step]

private theorem at_other {p c n : Nat} (x : Config p c n) (e i : Fin n)
    (h₁ : i ≠ e) (h₂ : i ≠ rightNeighbor e) : step x e i = x i := by simp [step,h₁,h₂]

private theorem sb_nonneg {p c : Nat} (u : Site p c) : 0 ≤ stockBit u := by simp [stockBit]

private theorem mask_nonneg {p c n : Nat} (x : Config p c n) (b : Fin n) (d : Nat) (i : Fin n) :
    0 ≤ maskedStock x b d i := by
  classical
  by_cases h : InFront b d i
  · simpa [maskedStock,h] using sb_nonneg (x i)
  · simp [maskedStock,h]

private theorem mask_le_stock {p c n : Nat} (x : Config p c n) (b : Fin n) (d : Nat) (i : Fin n) :
    maskedStock x b d i ≤ stockBit (x i) := by
  classical
  by_cases h : InFront b d i
  · simp [maskedStock,h]
  · simpa [maskedStock,h] using sb_nonneg (x i)

private theorem mask_mono_after_frame {p c n : Nat} (x y : Config p c n)
    (b b' i : Fin n) (d d' : Nat) (hf : y i = x i)
    (h : InFront b' d' i → InFront b d i) :
    maskedStock y b' d' i ≤ maskedStock x b d i := by
  classical
  by_cases hi : InFront b' d' i
  · simp [maskedStock,hi,h hi,hf]
  · simp only [maskedStock,if_neg hi]
    exact mask_nonneg x b d i

/-- With the carrier stationary, front inventory never increases under
a raw mark, including a shift that exposes the old first donor. -/
theorem inventory_stationary {p c n d d' : Nat} (hn : 4 ≤ n) {x : Config p c n}
    (b e : Fin n) (hc : MCOV x) (h : FirstMark x b d) (h' : FirstMark (step x e) b d')
    (he : e ≠ b) :
    inventory (step x e) b d' ≤ inventory x b d := by
  classical
  let y := step x e
  let v := rightNeighbor e
  obtain ⟨q,hq,hqle⟩ := firstMark_stationary_step hn x hc b e h
  have hqd := h'.unique hq
  have hbound : d' ≤ d + frontPayment x b e d := hqd.symm ▸ hqle
  have hsum := sum_pair_bound (maskedStock y b d') (maskedStock x b d) e v (rn_ne hn e)
  rw [← Int.add_zero (inventory y b d')]
  refine hsum ?_ 0 ?_
  · intro i h₁ h₂
    apply mask_mono_after_frame x y b b i d d' (at_other x e i h₁ h₂)
    rintro ⟨j,hj,hjd,hji⟩
    refine ⟨j,hj,?_,hji⟩
    by_cases hh : j < d
    · exact hh
    · by_cases hp : e = liftedSite b d ∧ geometricPay (x e) (x v) = true
      · have h1 : frontPayment x b e d = 1 := if_pos hp
        rw [h1] at hbound
        have hh' : j=d := by omega
        rw [hh',← hp.1] at hji
        exact (h₁ hji.symm).elim
      · have h0 : frontPayment x b e d = 0 := if_neg hp
        rw [h0] at hbound
        omega
  · simp only [Int.add_zero]
    by_cases hp : e = liftedSite b d ∧ geometricPay (x e) (x v) = true
    · have hzero : (y e).stock = false := by
        change (step x e e).stock = false
        rw [at_left]; exact paid_donor_empty _ _ hp.2
      have hleft : maskedStock y b d' e = 0 := by simp [maskedStock,stockBit,hzero]
      have hright : ¬ InFront b d' v := by
        rintro ⟨j,hj,hjd,hji⟩
        have hp1 : frontPayment x b e d = 1 := if_pos hp
        have hb : d' ≤ d+1 := hp1 ▸ hbound
        have hv : liftedSite b (d+1) = v := by rw [liftedSite_succ,← hp.1]
        by_cases hwrap : d+1 = n
        · rw [hwrap,liftedSite_full] at hv
          have hEq := liftedSite_inj b (by have := h'.lt; omega : j<n) (by omega : 0<n)
            (hji.trans (hv.symm.trans (liftedSite_zero b).symm))
          omega
        · have hEq := liftedSite_inj b (by have := h'.lt; omega : j<n)
            (by have := h.lt; omega : d+1<n) (hji.trans hv.symm)
          omega
      rw [hleft,show maskedStock y b d' v = 0 by simp [maskedStock,hright]]
      exact Int.add_nonneg (mask_nonneg x b d e) (mask_nonneg x b d v)
    · have hp0 : frontPayment x b e d = 0 := if_neg hp
      have hbd : d' ≤ d := by rw [hp0,Nat.add_zero] at hbound; exact hbound
      have hsub (i : Fin n) : InFront b d' i → InFront b d i :=
        fun ⟨j,a,c,h⟩ => ⟨j,a,by omega,h⟩
      by_cases hve : InFront b d v
      · have he' : InFront b d e := previous_inside he hve
        rw [show maskedStock x b d e = stockBit (x e) by simp [maskedStock,he'],
            show maskedStock x b d v = stockBit (x v) by simp [maskedStock,hve]]
        apply Int.le_trans (Int.add_le_add (mask_le_stock y b d' e) (mask_le_stock y b d' v))
        change stockBit (step x e e) + stockBit (step x e (rightNeighbor e)) ≤ _
        rw [at_left,at_right hn]
        exact pair_stock_le_of_nonleader _ _ (no_leader_inside hc h he')
      · have hv' : ¬ InFront b d' v := fun a => hve (hsub v a)
        have hz : maskedStock y b d' v = 0 := by simp [maskedStock,hv']
        rw [hz,show maskedStock x b d v = 0 by simp [maskedStock,hve]]
        simp only [Int.add_zero]
        by_cases he' : InFront b d e
        · rw [show maskedStock x b d e = stockBit (x e) by simp [maskedStock,he']]
          apply Int.le_trans (mask_le_stock y b d' e)
          change stockBit (step x e e) ≤ _
          rw [at_left]
          exact left_stock_le _ _
        · have hE : ¬ InFront b d' e := fun a => he' (hsub e a)
          simp [maskedStock,he',hE]


/-- Numerator of entering a site that held one physical stock token on the
old mark. Used only if the existing tagged carrier actually transfers. -/
def landingBit {p c n : Nat} (x : Config p c n) (b : Fin n) : Int :=
  stockBit (x (rightNeighbor b))

private theorem landing_range {p c n : Nat} (x : Config p c n) (b : Fin n) :
    0 ≤ landingBit x b ∧ landingBit x b ≤ 1 := by
  cases h : (x (rightNeighbor b)).stock <;> simp [landingBit,stockBit,h]

private theorem unmarked_pay_false {p c n : Nat} {x : Config p c n}
    (hc : MCOV x) (i : Fin n) (hm : (x i).mark = false) :
    geometricPay (x i) (x (rightNeighbor i)) = false := by
  by_cases hh : geometricPay (x i) (x (rightNeighbor i)) = true
  · have hx := covered_pair_marks (x i) (x (rightNeighbor i)) (hc i)
    simp [hh,hm] at hx
  · exact Bool.eq_false_iff.mpr hh

private theorem transfer_distance {p c n d d' : Nat} (hn : 4 ≤ n) {x : Config p c n}
    (b : Fin n) (hc : MCOV x) (h : FirstMark x b d)
    (ht : tagTransfer (x b) (x (rightNeighbor b)) = true)
    (h' : FirstMark (step x b) (rightNeighbor b) d') :
    d'+1 ≤ d := by
  have hm := ((tagTransfer_iff _ _).mp ht).2.2.2.1
  have hp := unmarked_pay_false hc b hm
  obtain ⟨q,hq,hL⟩ := firstMark_transport_step hn x hc b h ht
  rw [← h'.unique hq] at hL
  simp [frontPayment,hp] at hL
  omega

/-- A live transfer debits the landing's original stock if this landing
was in the strict inventory; the excluded donor case debits zero here. -/
theorem inventory_transport {p c n d d' : Nat} (hn : 4 ≤ n) {x : Config p c n}
    (b : Fin n) (hc : MCOV x) (h : FirstMark x b d)
    (ht : tagTransfer (x b) (x (rightNeighbor b)) = true)
    (h' : FirstMark (step x b) (rightNeighbor b) d') :
    inventory (step x b) (rightNeighbor b) d' +
      (if 1 < d then landingBit x b else 0) ≤ inventory x b d := by
  classical
  let v := rightNeighbor b
  let y := step x b
  have hd := transfer_distance hn b hc h ht h'
  have hsub (i : Fin n) : InFront v d' i → InFront b d i := by
    rintro ⟨j,hj,hj',hji⟩
    exact ⟨j+1,by omega,by omega,(liftedSite_advance b j).symm.trans hji⟩
  change BarrierIID.edgeSum (maskedStock y v d') + _ ≤ BarrierIID.edgeSum (maskedStock x b d)
  refine sum_pair_bound _ _ b v (rn_ne hn b) ?_ _ ?_
  · intro i h₁ h₂
    exact mask_mono_after_frame x y b v i d d' (at_other x b i h₁ h₂) (hsub i)
  · have hb : ¬ InFront v d' b := by
      intro H
      rcases hsub b H with ⟨j,hj,hj',hji⟩
      have eq := liftedSite_inj b (by have := h.lt; omega : j<n) (by omega : 0<n)
        (hji.trans (liftedSite_zero b).symm)
      omega
    have hv : ¬ InFront v d' v := by
      rintro ⟨j,hj,hj',hji⟩
      have eq := liftedSite_inj v (by have := h'.lt; omega : j<n) (by omega : 0<n)
        (hji.trans (liftedSite_zero v).symm)
      omega
    rw [show maskedStock y v d' b = 0 by simp [maskedStock,hb],
        show maskedStock y v d' v = 0 by simp [maskedStock,hv]]
    by_cases hD : 1 < d
    · have hv' : InFront b d v := ⟨1,by omega,hD,by rw [show 1=0+1 from rfl,liftedSite_succ,liftedSite_zero]⟩
      rw [if_pos hD,show maskedStock x b d v = stockBit (x v) by simp [maskedStock,hv']]
      have hf := mask_nonneg x b d b
      change 0+0+stockBit (x v) ≤ _
      omega
    · rw [if_neg hD]
      simp only [Int.add_zero]
      exact Int.add_nonneg (mask_nonneg x b d b) (mask_nonneg x b d v)

/-- Add a single reserve unit for the only possible exceptional landing:
the move from one-before-the-first-donor onto the excluded donor itself. -/
noncomputable def reserve {p c n : Nat} (x : Config p c n) (b : Fin n) (d : Nat) : Int :=
  inventory x b d + if d = 0 then 0 else 1

theorem reserve_interval {p c n : Nat} (x : Config p c n) (b : Fin n) (d : Nat) :
    0 ≤ reserve x b d ∧ reserve x b d ≤ (n : Int) + 1 := by
  have hi := inventory_interval x b d
  unfold reserve
  split <;> omega

private theorem zero_first_stationary {p c n d' : Nat} (hn : 4 ≤ n) {x : Config p c n}
    (b e : Fin n) (hc : MCOV x) (h : FirstMark x b 0) (h' : FirstMark (step x e) b d')
    (he : e ≠ b) : d' = 0 := by
  obtain ⟨j,hj,hj'⟩ := firstMark_stationary_step hn x hc b e h
  rw [← h'.unique hj] at hj'
  simp [frontPayment,liftedSite_zero,he] at hj'
  exact hj'

/-- A stationary mark spends no reserve. In particular, the reserve unit
cannot reappear once the old first marked donor is at the carrier. -/
theorem reserve_stationary {p c n d d' : Nat} (hn : 4 ≤ n) {x : Config p c n}
    (b e : Fin n) (hc : MCOV x) (h : FirstMark x b d) (h' : FirstMark (step x e) b d')
    (he : e ≠ b) :
    reserve (step x e) b d' ≤ reserve x b d := by
  have hI := inventory_stationary hn b e hc h h' he
  by_cases hD : d=0
  · subst d
    have hh := zero_first_stationary hn b e hc h h' he
    rw [hh] at hI ⊢
    simpa [reserve] using hI
  · unfold reserve
    rw [if_neg hD]
    split <;> omega

/-- Every physically occupied landing on survival spends one reserve unit. -/
theorem reserve_transport {p c n d d' : Nat} (hn : 4 ≤ n) {x : Config p c n}
    (b : Fin n) (hc : MCOV x) (h : FirstMark x b d)
    (ht : tagTransfer (x b) (x (rightNeighbor b)) = true)
    (h' : FirstMark (step x b) (rightNeighbor b) d') :
    reserve (step x b) (rightNeighbor b) d' + landingBit x b ≤ reserve x b d := by
  have hd := transfer_distance hn b hc h ht h'
  have h0 : d ≠ 0 := by omega
  have hI := inventory_transport hn b hc h ht h'
  unfold reserve
  rw [if_neg h0]
  by_cases hD : 1 < d
  · rw [if_pos hD] at hI
    split <;> omega
  · rw [if_neg hD] at hI
    have hd' : d'=0 := by omega
    rw [if_pos hd']
    have hL := (landing_range x b).2
    omega


open TaggedTrace

/-- Successful outgoing transport is counted using the physical tag observer;
the stock bit is sampled from the destination before that mark. -/
def occupiedMark {p c n : Nat} (s : Obs p c n) (e : Fin n) : Int :=
  if s.carrier = some e ∧ (advance s e).carrier.isSome
  then landingBit s.config e else 0

/-- Total occupied landings of the tracked identity, not visits by later
replacement bullets at the same physical sites. -/
def occupiedLandings {p c n : Nat} (s : Obs p c n) : List (Fin n) → Int
  | [] => 0
  | e::w => occupiedMark s e + occupiedLandings (advance s e) w

/-- Telescoped reserve along every finite surviving covered word. Neither
freshness nor a bound on the number of other births or mints is assumed. -/
theorem occupiedLandings_reserve {p c n d : Nat} (hn : 4 ≤ n)
    (s : Obs p c n) (b : Fin n) (w : List (Fin n))
    (hb : s.carrier = some b) (h : FirstMark s.config b d)
    (hc : CoveredGeometryWord s.config w) (ha : ¬ ended (track s w)) :
    ∃ b' d', (track s w).carrier = some b' ∧ FirstMark (track s w).config b' d' ∧
      reserve (track s w).config b' d' + occupiedLandings s w ≤ reserve s.config b d := by
  induction w generalizing s b d with
  | nil => exact ⟨b,d,hb,h,by simp [occupiedLandings,track]⟩
  | cons e w ih =>
    have hmc : MCOV s.config := hc.1
    have htail : CoveredGeometryWord (advance s e).config w := by rw [projection_step]; exact hc.2
    have hSurv : ¬ ended (advance s e) := fun q => ha (ended_run (advance s e) w q)
    obtain ⟨b', hcar⟩ : ∃ b', carrierStep s.config e (some b) = some b' := by
      cases hC : carrierStep s.config e (some b)
      · exact False.elim (hSurv (by simp [ended,advance,hb,hC]))
      · exact ⟨_,rfl⟩
    have hC : (advance s e).carrier = some b' := by simp [advance,hb,hcar]
    have hlocal : ∃ d₁, FirstMark (advance s e).config b' d₁ ∧
        reserve (advance s e).config b' d₁ + occupiedMark s e ≤ reserve s.config b d := by
      rw [projection_step]
      by_cases he : e = b
      · subst e
        obtain ⟨hEq,hT⟩ := carrierStep_selected_survives s.config b b' hcar
        subst b'
        obtain ⟨d₁,hd₁,_⟩ := firstMark_transport_step hn s.config hmc b h hT
        refine ⟨d₁,hd₁,?_⟩
        simpa [occupiedMark,hb,hC] using reserve_transport hn b hmc h hT hd₁
      · have hEq := carrierStep_not_selected_stays s.config e b b' (Ne.symm he) hcar
        subst b'
        obtain ⟨d₁,hd₁,_⟩ := firstMark_stationary_step hn s.config hmc b e h
        refine ⟨d₁,hd₁,?_⟩
        simpa [occupiedMark,hb,Ne.symm he] using reserve_stationary hn b e hmc h hd₁ he
    obtain ⟨d₁,hd₁,hLe⟩ := hlocal
    obtain ⟨z,k,hk,hfirst,hbound⟩ := ih (advance s e) b' hC hd₁ htail ha
    refine ⟨z,k,hk,hfirst,?_⟩
    change reserve (track (advance s e) w).config z k +
      (occupiedMark s e + occupiedLandings (advance s e) w) ≤ reserve s.config b d
    omega

/-- Exact all-size occupied-landing bound on the actual paper trace.
The unit reserve absorbs the one possible excluded-donor landing. -/
theorem occupiedLandings_le_size_add_one {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (i : Fin n) (w : List (Fin n))
    (hm : MCOV x) (hnd : (∃ j : Fin n, (x j).mark = true)) (ha : ¬ ended (track (init x i) w)) :
    occupiedLandings (init x i) w ≤ (n : Int) + 1 := by
  have hi : (init x i).carrier = some i := by
    rcases hH : (x i).bullet == .live with _ | _
    · exact False.elim (ha (ended_run _ _ (by simp [ended,init,hH])))
    · simp [init,hH]
  obtain ⟨d,hd⟩ := firstMark_exists x i hnd
  obtain ⟨b',d',_,_,h⟩ := occupiedLandings_reserve hn (init x i) i w hi hd
    (coveredGeometryWord_of_mcov hn x w hm) ha
  have hl := (reserve_interval (track (init x i) w).config b' d').1
  have hr := (reserve_interval x i d).2
  change reserve (track (init x i) w).config b' d' +
    occupiedLandings (init x i) w ≤ reserve x i d at h
  omega

end L4.RearFrontStock

#print axioms L4.RearFrontStock.inventory_stationary
#print axioms L4.RearFrontStock.inventory_transport
#print axioms L4.RearFrontStock.occupiedLandings_reserve
#print axioms L4.RearFrontStock.occupiedLandings_le_size_add_one

namespace L4.RearFrontStock

open StockTokenRows
/-- The recipient's stock is unchanged whenever an incoming mark is
already materialized. Native rows and P5 do not touch that stock. -/
theorem marked_right_stock {p c : Nat} (u v : Site p c) (hm : u.mark = true) :
    (pairStep u v).2.stock = v.stock := by
  have hM : (materialize u v).mark = true := by simp [materialize,hm]
  have hi (a : Site p c) : (fireInitiator a).mark = a.mark := by
    unfold fireInitiator; split <;> rfl
  have hp (a b : Site p c) : (impact a b).1.mark = a.mark := by
    unfold impact; split
    · split <;> rfl
    · rfl
  have hf (g : Bool) (a b : Site p c) : (followerBullet g a b).1.mark = a.mark := by
    unfold followerBullet; split
    · split <;> rfl
    · rfl
  have hn : (native (materialize u v) v).1.mark = true := by
    unfold native
    let z := impact (fireInitiator (materialize u v)) (fireResponder v)
    exact (hf (pinned z.1 z.2) z.1 z.2).trans
      ((hp _ _).trans ((hi _).trans hM))
  have hh := congrArg Prod.snd (row_bits u v)
  dsimp only at hh
  let a := native (materialize u v) v
  have hA : row u v = .drop ∨ row u v = .stay := by
    change action a.1 a.2 = .drop ∨ action a.1 a.2 = .stay
    cases hL : a.2.leader <;> cases hP : payer a.1 <;> simp [action,hL,hP,show a.1.mark=true from hn]
  rcases hA with h|h <;> simpa only [h,update,stockLabel_some] using hh.symm

/-- Inclusive corridor from the fixed or moving rear to the tag. -/
def InRear {n : Nat} (r : Fin n) (d : Nat) (i : Fin n) : Prop :=
  ∃ j : Nat, j ≤ d ∧ liftedSite r j = i

noncomputable def rearStock {p c n : Nat} (x : Config p c n) (r : Fin n)
    (d : Nat) (i : Fin n) : Int := by
  classical
  exact if InRear r d i then stockBit (x i) else 0

noncomputable def rearInventory {p c n : Nat} (x : Config p c n) (r : Fin n)
    (d : Nat) : Int := BarrierIID.edgeSum (rearStock x r d)

private theorem rear_mask_nonneg {p c n : Nat} (x : Config p c n) (r : Fin n) (d : Nat) (i : Fin n) :
    0 ≤ rearStock x r d i := by
  classical
  by_cases h : InRear r d i
  · simpa [rearStock,h] using sb_nonneg (x i)
  · simp [rearStock,h]

private theorem rear_mask_le {p c n : Nat} (x : Config p c n) (r : Fin n) (d : Nat) (i : Fin n) :
    rearStock x r d i ≤ stockBit (x i) := by
  classical
  by_cases h : InRear r d i
  · simp [rearStock,h]
  · simpa [rearStock,h] using sb_nonneg (x i)

theorem rearInventory_interval {p c n : Nat} (x : Config p c n) (r : Fin n) (d : Nat) :
    0 ≤ rearInventory x r d ∧ rearInventory x r d ≤ (n : Int) := by
  classical
  unfold rearInventory
  constructor
  · rw [← show BarrierIID.edgeSum (fun _ : Fin n => 0) = 0 by simp [sum_const]]
    exact sum_mono _ _ (fun i => rear_mask_nonneg x r d i)
  · rw [← show BarrierIID.edgeSum (fun _ : Fin n => 1) = (n : Int) by simp [sum_const]]
    apply sum_mono
    intro i
    apply Int.le_trans (rear_mask_le x r d i)
    cases h : (x i).stock <;> simp [stockBit,h]

private theorem rear_mask_frame {p c n : Nat} (x y : Config p c n)
    (r r' i : Fin n) (d d' : Nat) (hf : y i = x i)
    (h : InRear r' d' i → InRear r d i) :
    rearStock y r' d' i ≤ rearStock x r d i := by
  classical
  by_cases hi : InRear r' d' i
  · simp [rearStock,hi,h hi,hf]
  · simp only [rearStock,if_neg hi]
    exact rear_mask_nonneg x r d i

/-- The inclusive rear inventory is nonincreasing with fixed endpoints
throughout a ghost phase: the corridor has no living donor, and marked
incoming service cannot import stock into the rear. -/
theorem rearInventory_stationary {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (r e : Fin n) (d : Nat)
    (hInterior : ∀ i, InRear r d i → (x i).leader = false)
    (hIncoming : rightNeighbor e = r → (x e).mark = true) :
    rearInventory (step x e) r d ≤ rearInventory x r d := by
  classical
  let y := step x e
  let v := rightNeighbor e
  change BarrierIID.edgeSum (rearStock y r d) ≤ BarrierIID.edgeSum (rearStock x r d)
  rw [← Int.add_zero (BarrierIID.edgeSum (rearStock y r d))]
  refine sum_pair_bound _ _ e v (rn_ne hn e) ?_ 0 ?_
  · intro i h₁ h₂
    exact rear_mask_frame x y r r i d d (at_other x e i h₁ h₂) id
  · rw [Int.add_zero]
    by_cases he : InRear r d e <;> by_cases hv : InRear r d v
    · simp only [rearStock,if_pos he,if_pos hv]
      change stockBit (step x e e) + stockBit (step x e (rightNeighbor e)) ≤ _
      rw [at_left,at_right hn]
      exact pair_stock_le_of_nonleader _ _ (hInterior e he)
    · simp only [rearStock,if_pos he,if_neg hv,Int.add_zero]
      change stockBit (step x e e) ≤ _
      rw [at_left]
      exact left_stock_le _ _
    · have hr : v = r := by
        obtain ⟨j,hj,hh⟩ := hv
        by_cases hJ : j=0
        · rw [hJ,liftedSite_zero] at hh
          exact hh.symm
        · refine False.elim (he ⟨j-1,by omega,?_⟩)
          apply rn_inj
          rw [← liftedSite_succ,show j-1+1=j by omega,hh]
      simp only [rearStock,if_neg he,if_pos hv,Int.zero_add]
      change stockBit (step x e (rightNeighbor e)) ≤ _
      rw [at_right hn]
      unfold stockBit
      rw [marked_right_stock _ _ (hIncoming hr)]
      exact Int.le_refl _
    · simp [rearStock,he,hv]

/-- A successful tag move enlarges the rear corridor by exactly one
physical site, and spends no more than that new site's old stock. -/
theorem rearInventory_tag_grow {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (r : Fin n) (d : Nat) (hD : d+1 < n)
    (hDonor : (x (liftedSite r d)).leader = false) :
    rearInventory (step x (liftedSite r d)) r (d+1) ≤
      rearInventory x r d + landingBit x (liftedSite r d) := by
  classical
  let e := liftedSite r d
  let v := rightNeighbor e
  let y := step x e
  have hv : liftedSite r (d+1) = v := liftedSite_succ r d
  have hE : InRear r d e := ⟨d,Nat.le_refl _,rfl⟩
  have hE' : InRear r (d+1) e := ⟨d,by omega,rfl⟩
  have hV : ¬ InRear r d v := by
    rintro ⟨j,hj,hh⟩
    have hEq := liftedSite_inj r (by omega : j<n) hD (hh.trans hv.symm)
    omega
  have hV' : InRear r (d+1) v := ⟨d+1,Nat.le_refl _,hv⟩
  have hLocal :
      BarrierIID.edgeSum (rearStock y r (d+1)) + (-landingBit x e) ≤
        BarrierIID.edgeSum (rearStock x r d) := by
    refine sum_pair_bound _ _ e v (rn_ne hn e) ?_ _ ?_
    · intro i he hv'
      apply rear_mask_frame x y r r i d (d+1) (at_other x e i he hv')
      rintro ⟨j,hj,hj'⟩
      refine ⟨j,?_,hj'⟩
      by_cases hJ : j=d+1
      · exact (hv' (hj'.symm.trans (hJ.symm ▸ hv))).elim
      · omega
    · simp only [rearStock,if_neg hV,if_pos hE,if_pos hE',if_pos hV',Int.add_zero]
      have hh := pair_stock_le_of_nonleader (x e) (x v) hDonor
      have hL : stockBit (y e) + stockBit (y v) ≤ stockBit (x e) + stockBit (x v) := by
        change stockBit (step x e e) + stockBit (step x e (rightNeighbor e)) ≤ _
        simpa [at_left,at_right hn] using hh
      change stockBit (y e) + stockBit (y v) + -stockBit (x v) ≤ stockBit (x e)
      omega
  change BarrierIID.edgeSum (rearStock y r (d+1)) ≤
    BarrierIID.edgeSum (rearStock x r d) + landingBit x e
  omega

/-- A surviving counted rear advance removes its old site's stock from
the corridor inventory. The only excluded edge case is the selected
tag donor itself, which is not a stationary surviving preemption. -/
theorem rearInventory_rear_drop {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (r e : Fin n) (d : Nat)
    (hD : d < n) (hp : 0 < d)
    (hr : rightNeighbor e = r) (he : e ≠ liftedSite r d) :
    rearInventory (step x e) (rightNeighbor r) (d-1) + stockBit (x r) ≤
      rearInventory x r d := by
  classical
  let y := step x e
  have hEar : InRear r d r := ⟨0,Nat.zero_le _,liftedSite_zero r⟩
  have hOldE : ¬ InRear r d e := by
    rintro ⟨j,hj,hje⟩
    have hNext : liftedSite r (j+1) = r := by rw [liftedSite_succ,hje,hr]
    by_cases hJ : j+1=n
    · have hEq : j=d := by omega
      exact he (hje.symm.trans (hEq ▸ rfl))
    · have hEq := liftedSite_inj r (by omega : j+1<n) (by omega : 0<n)
        (hNext.trans (liftedSite_zero r).symm)
      omega
  have hSub (i : Fin n) : InRear (rightNeighbor r) (d-1) i → InRear r d i := by
    rintro ⟨j,hj,hji⟩
    exact ⟨j+1,by omega,(liftedSite_advance r j).symm.trans hji⟩
  have hNewE : ¬ InRear (rightNeighbor r) (d-1) e := fun a => hOldE (hSub _ a)
  have hNewR : ¬ InRear (rightNeighbor r) (d-1) r := by
    rintro ⟨j,hj,hji⟩
    have hEq := liftedSite_inj r (by omega : j+1<n) (by omega : 0<n)
      ((liftedSite_advance r j).symm.trans (hji.trans (liftedSite_zero r).symm))
    omega
  change BarrierIID.edgeSum (rearStock y (rightNeighbor r) (d-1)) + stockBit (x r) ≤
    BarrierIID.edgeSum (rearStock x r d)
  refine sum_pair_bound _ _ e (rightNeighbor e) (rn_ne hn e) ?_ _ ?_
  · intro i h₁ h₂
    exact rear_mask_frame x y r (rightNeighbor r) i d (d-1) (at_other x e i h₁ h₂) (hSub i)
  · simp [hr,rearStock,hEar,hOldE,hNewE,hNewR]

end L4.RearFrontStock

#print axioms L4.RearFrontStock.rearInventory_stationary
#print axioms L4.RearFrontStock.rearInventory_tag_grow
#print axioms L4.RearFrontStock.rearInventory_rear_drop

namespace L4.RearFrontStock

/-- The exact no-living-donor premise of the ghost inventory follows from
MCOV, an old rear ghost, and the absence of marked bonds inside the arc. -/
theorem rearInterior_of_ghost_and_marks {p c n : Nat}
    {x : Config p c n} {r : Fin n} {d : Nat} (hc : MCOV x)
    (hg : (x r).leader = false) (hmarks : ∀ j, j < d → (x (liftedSite r j)).mark = false) :
    ∀ i, InRear r d i → (x i).leader = false := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := hi
  cases j with
  | zero => simpa [liftedSite_zero] using hg
  | succ j =>
    rw [liftedSite_succ]
    apply Bool.eq_false_iff.mpr
    intro hh
    have hm := hc (liftedSite r j) (Or.inl hh)
    rw [hmarks j (by omega)] at hm
    contradiction

/-- A surviving tag does not wrap into the actual marked rear. -/
theorem rear_tag_grow_lt {p c n : Nat} {x : Config p c n} {r : Fin n} {d : Nat}
    (hD : d < n)
    (hmark : ∀ e, rightNeighbor e = r → (x e).mark = true)
    (hT : tagTransfer (x (liftedSite r d)) (x (rightNeighbor (liftedSite r d))) = true) :
    d+1<n := by
  have hm := ((tagTransfer_iff _ _).mp hT).2.2.2.1
  by_cases hh : d+1=n
  · have he : rightNeighbor (liftedSite r d) = r := by
      rw [← liftedSite_succ,hh,liftedSite_full]
    rw [hmark _ he] at hm
    contradiction
  · omega

/-- Finite physical corridor evolution certificates. Every constructor
uses the literal transition; case selection and phase integration are
separate from the inventory arithmetic. -/
inductive CorridorWord {p c n : Nat} :
    Config p c n → Fin n → Nat → List (Fin n) →
    Config p c n → Fin n → Nat → Int → Int → Prop where
  | nil (x : Config p c n) (r : Fin n) (d : Nat) :
      CorridorWord x r d [] x r d 0 0
  | stationary {x y : Config p c n} {r z e : Fin n} {d k : Nat} {w : List (Fin n)}
      {filled landed : Int}
      (hi : ∀ i, InRear r d i → (x i).leader = false)
      (he : rightNeighbor e = r → (x e).mark = true)
      (hStay : e ≠ liftedSite r d)
      (rest : CorridorWord (step x e) r d w y z k filled landed) :
      CorridorWord x r d (e::w) y z k filled landed
  | grow {x y : Config p c n} {r z : Fin n} {d k : Nat} {w : List (Fin n)}
      {filled landed : Int} (hd : d+1<n) (hl : (x (liftedSite r d)).leader = false)
      (rest : CorridorWord (step x (liftedSite r d)) r (d+1) w y z k filled landed) :
      CorridorWord x r d (liftedSite r d::w) y z k filled
        (landingBit x (liftedSite r d)+landed)
  | drop {x y : Config p c n} {r z e : Fin n} {d k : Nat} {w : List (Fin n)}
      {filled landed : Int} (hd : d<n) (hp : 0<d) (hr : rightNeighbor e = r)
      (he : e ≠ liftedSite r d)
      (rest : CorridorWord (step x e) (rightNeighbor r) (d-1) w y z k filled landed) :
      CorridorWord x r d (e::w) y z k (stockBit (x r)+filled) landed

/-- Summed stock inequality, including the final residual inventory, for
every truncated certified ghost-phase subword. -/
theorem CorridorWord.ledger {p c n : Nat} (hn : 4 ≤ n)
    {x y : Config p c n} {r z : Fin n} {d k : Nat} {w : List (Fin n)} {filled landed : Int}
    (h : CorridorWord x r d w y z k filled landed) :
    filled + rearInventory y z k ≤ rearInventory x r d + landed := by
  induction h with
  | nil => simp
  | @stationary x y r z e d k w f l hi he _ rest ih =>
    have hs := rearInventory_stationary hn x r e d hi he
    omega
  | @grow x y r z d k w f l hD hL rest ih =>
    have hs := rearInventory_tag_grow hn x r d hD hL
    omega
  | @drop x y r z e d k w f l hD hp hr he rest ih =>
    have hs := rearInventory_rear_drop hn x r e d hD hp hr he
    omega

/-- Once the rear geometry identifies a ghost-phase subword, only landing
stock can augment its initial inventory of at most n particles. -/
theorem CorridorWord.filled_le_size_add_landings {p c n : Nat} (hn : 4 ≤ n)
    {x y : Config p c n} {r z : Fin n} {d k : Nat} {w : List (Fin n)} {filled landed : Int}
    (h : CorridorWord x r d w y z k filled landed) : filled ≤ (n : Int) + landed := by
  have hL := h.ledger hn
  have hI := (rearInventory_interval x r d).2
  have hF := (rearInventory_interval y z k).1
  omega

end L4.RearFrontStock

#print axioms L4.RearFrontStock.CorridorWord.ledger
#print axioms L4.RearFrontStock.CorridorWord.filled_le_size_add_landings

namespace L4.RearFrontStock
open TaggedTrace

/-- Successful occupied landing counts are nonnegative on every word,
including continuations after extinction. -/
theorem occupiedLandings_nonneg {p c n : Nat} (s : Obs p c n) (w : List (Fin n)) :
    0 ≤ occupiedLandings s w := by
  induction w generalizing s with
  | nil => exact Int.le_refl _
  | cons e w ih =>
    rw [occupiedLandings]
    apply Int.add_nonneg _ (ih (advance s e))
    unfold occupiedMark
    split
    · exact (landing_range _ _).1
    · exact Int.le_refl _

/-- The count for a literal word splits at the corresponding tag observer,
with no reset of the identity or stock. -/
theorem occupiedLandings_append {p c n : Nat}
    (s : Obs p c n) (u v : List (Fin n)) :
    occupiedLandings s (u++v) =
      occupiedLandings s u + occupiedLandings (track s u) v := by
  induction u generalizing s with
  | nil => simp [occupiedLandings,track]
  | cons e u ih =>
    simp only [List.cons_append,occupiedLandings,track,ih,Int.add_assoc]

private theorem live_step_carrier {p c n : Nat} {s : Obs p c n}
    {e b : Fin n} (hc : s.carrier = some b) (hLive : ¬ ended (advance s e)) :
    ∃ b', (advance s e).carrier = some b' ∧ carrierStep s.config e (some b) = some b' := by
  cases hs : carrierStep s.config e (some b) with
  | none => exact False.elim (hLive (by simp [ended,advance,hc,hs]))
  | some j => exact ⟨j,by simp [advance,hc,hs],rfl⟩

private theorem corridor_stay_tag {p c n : Nat} {s : Obs p c n} {e b : Fin n}
    (hc : s.carrier = some b) (he : e ≠ b) (hLive : ¬ ended (advance s e)) :
    (advance s e).carrier = some b ∧ occupiedMark s e = 0 := by
  obtain ⟨b',hNew,hRel⟩ := live_step_carrier hc hLive
  have eq := carrierStep_not_selected_stays s.config e b b' (Ne.symm he) hRel
  exact ⟨eq ▸ hNew,by simp [occupiedMark,hc,Ne.symm he]⟩

private theorem corridor_grow_tag {p c n : Nat} {s : Obs p c n} {e : Fin n}
    (hc : s.carrier = some e) (hLive : ¬ ended (advance s e)) :
    (advance s e).carrier = some (rightNeighbor e) ∧ occupiedMark s e = landingBit s.config e := by
  obtain ⟨b',hNew,hRel⟩ := live_step_carrier hc hLive
  have eq := (carrierStep_selected_survives s.config e b' hRel).1
  exact ⟨eq ▸ hNew,by simp [occupiedMark,hc,hNew]⟩

/-- The landing charge in a certified phase is exactly the physical
observer's occupied-landing count on that subword. -/
theorem CorridorWord.landed_eq_observer {p c n : Nat}
    {x y : Config p c n} {r z : Fin n} {d k : Nat} {w : List (Fin n)} {filled landed : Int}
    (h : CorridorWord x r d w y z k filled landed)
    (s : Obs p c n) (hc : s.config = x) (ht : s.carrier = some (liftedSite r d))
    (ha : ¬ ended (track s w)) :
    landed = occupiedLandings s w := by
  induction h generalizing s with
  | nil => rfl
  | @stationary x y r z e d k w f l hi he hStay rest ih =>
    have hSurv : ¬ ended (advance s e) := fun he => ha (ended_run (advance s e) w he)
    have hC := corridor_stay_tag ht hStay hSurv
    have hconf : (advance s e).config = step x e := by rw [projection_step,hc]
    rw [occupiedLandings,hC.2,Int.zero_add]
    exact ih (advance s e) hconf hC.1 ha
  | @grow x y r z d k w f l hD hL rest ih =>
    have hSurv : ¬ ended (advance s (liftedSite r d)) :=
      fun he => ha (ended_run (advance s (liftedSite r d)) w he)
    have hC := corridor_grow_tag ht hSurv
    have hconf : (advance s (liftedSite r d)).config = step x (liftedSite r d) := by rw [projection_step,hc]
    rw [occupiedLandings,hC.2,hc]
    have hNext : (advance s (liftedSite r d)).carrier = some (liftedSite r (d+1)) := by
      rw [liftedSite_succ]; exact hC.1
    rw [ih (advance s (liftedSite r d)) hconf hNext ha]
  | @drop x y r z e d k w f l hD hp hr he rest ih =>
    have hSurv : ¬ ended (advance s e) := fun he => ha (ended_run (advance s e) w he)
    have hC := corridor_stay_tag ht he hSurv
    have hconf : (advance s e).config = step x e := by rw [projection_step,hc]
    rw [occupiedLandings,hC.2,Int.zero_add]
    have hNext : (advance s e).carrier = some (liftedSite (rightNeighbor r) (d-1)) := by
      rw [liftedSite_advance,show d-1+1=d by omega]; exact hC.1
    exact ih (advance s e) hconf hNext ha

/-- A certified ghost phase after any preceding word pays at most 2n+1
for filled rear departures. The first n terms come from its initial
stock; the other n+1 come from the global tag's occupied-landing bound,
without treating the phase as a new tag. -/
theorem CorridorWord.filled_le_twice_size_add_one
    {p c n : Nat} (hn : 4 ≤ n)
    {x y : Config p c n} {r z : Fin n} {d k : Nat} {w : List (Fin n)} {filled landed : Int}
    (h : CorridorWord x r d w y z k filled landed)
    (x₀ : Config p c n) (i : Fin n) (before : List (Fin n))
    (hm : MCOV x₀) (hnd : (∃ j : Fin n, (x₀ j).mark = true))
    (hc : (track (init x₀ i) before).config = x)
    (ht : (track (init x₀ i) before).carrier = some (liftedSite r d))
    (ha : ¬ ended (track (init x₀ i) (before ++ w))) :
    filled ≤ 2*(n : Int)+1 := by
  have hLand := occupiedLandings_le_size_add_one hn x₀ i (before++w) hm hnd ha
  have hPrefix := occupiedLandings_nonneg (init x₀ i) before
  rw [occupiedLandings_append] at hLand
  have hAlive : ¬ ended (track (track (init x₀ i) before) w) := by
    rw [← track_append]
    exact ha
  have hExact := h.landed_eq_observer (track (init x₀ i) before) hc ht hAlive
  have hF := h.filled_le_size_add_landings hn
  omega

end L4.RearFrontStock

#print axioms L4.RearFrontStock.CorridorWord.landed_eq_observer
#print axioms L4.RearFrontStock.CorridorWord.filled_le_twice_size_add_one

namespace L4.RearFrontStock
open RearTrace

/-- Convert a forward offset within a backward-offset arc. -/
theorem liftedSite_back_within {n : Nat} (b : Fin n) (d j : Nat) (hd : d < n) (hj : j ≤ d) :
    liftedSite (back b d) j = back b (d-j) := by
  apply Fin.ext
  change (((b.val+(n-d))%n)+j)%n = (b.val+(n-(d-j)))%n
  rw [Nat.mod_add_mod]
  congr 1
  omega

/-- The inclusive arc ends at the same tag used to choose the rear. -/
theorem liftedSite_back_end {n : Nat} (b : Fin n) (d : Nat) (hd : d<n) :
    liftedSite (back b d) d = b := by
  rw [liftedSite_back_within b d d hd (Nat.le_refl _),Nat.sub_self,back_zero]

/-- The closest marked rear is a marked incoming root, and every bond
between that root and the tag has an unmarked initiator. -/
theorem firstRear_corridor_marks {p c n d : Nat} {x : Config p c n} {b : Fin n}
    (hf : FirstRear x b d) :
    (∀ e, rightNeighbor e = back b d → (x e).mark = true) ∧
    (∀ j, j < d → (x (liftedSite (back b d) j)).mark = false) := by
  constructor
  · intro e he
    have heq := rn_inj (he.trans (right_predecessor (back b d)).symm)
    rw [heq]
    exact hf.marked
  · intro j hj
    have he : rightNeighbor (liftedSite (back b d) j) = back b (d-(j+1)) := by
      rw [← liftedSite_succ, liftedSite_back_within b d (j+1) hf.lt (by omega)]
    rw [← predecessor_right (liftedSite (back b d) j),he]
    exact Bool.eq_false_iff.mpr (hf.before (d-(j+1)) (by omega))

end L4.RearFrontStock

#print axioms L4.RearFrontStock.firstRear_corridor_marks

namespace L4.RearFrontStock
open RearTrace TaggedTrace

/-- The physical ghost-phase conditions at each premark. A possible
terminal preemption mark is omitted; terminal birth is allowed. -/
def GhostPremarks {p c n : Nat} (i : Fin n) (s : Observer p c n) :
    List (Fin n) → Prop
  | [] => True
  | e::w =>
      s.phase = .ghost ∧
      (∀ r, s.rear = some r → (s.tag.config r).leader = false) ∧
      (rearAdvance i s e).phase ≠ .pinned ∧
      GhostPremarks i (rearAdvance i s e) w

/-- An actual displaced rear contributes its old resident stock bit.
The ghost subword excludes its possible terminal preemption mark. -/
def filledRearMark {p c n : Nat} (s : Observer p c n) (e : Fin n) : Int :=
  match s.rear with
  | none => 0
  | some r => if rearShifts s e r then stockBit (s.tag.config r) else 0

def filledRearDepartures {p c n : Nat} (i : Fin n) (s : Observer p c n) :
    List (Fin n) → Int
  | [] => 0
  | e::w => filledRearMark s e + filledRearDepartures i (rearAdvance i s e) w

private theorem rear_next {p c n : Nat} (i e r : Fin n) (s : Observer p c n)
    (hp : s.phase = .ghost) (hr : s.rear = some r) :
    (rearAdvance i s e).rear =
      some (if rearShifts s e r then rightNeighbor r else r) := by
  simp [rearAdvance,hr,hp,show (Phase.ghost == Phase.pinned) = false from rfl]

private theorem rear_phase_next {p c n : Nat} (i e r : Fin n) (s : Observer p c n)
    (hp : s.phase = .ghost) (hr : s.rear = some r) :
    (rearAdvance i s e).phase =
      phaseAfter s (advance s.tag e)
        (if rearShifts s e r then rightNeighbor r else r) (rearShifts s e r) := by
  simp [rearAdvance,hr,hp,show (Phase.ghost == Phase.pinned) = false from rfl]

/-- Extract the literal corridor subword and its exact filled counter from
the physical rear observer while its premarks are in the ghost phase. -/
theorem corridorWord_of_ghostPremarks {p c n : Nat} (hn : 4 ≤ n)
    (i : Fin n) (s : Observer p c n) (w : List (Fin n)) (b : Fin n) (d : Nat)
    (hm : MCOV s.tag.config) (hb : s.tag.carrier = some b)
    (hr : s.rear = some (back b d)) (hf : FirstRear s.tag.config b d)
    (hg : GhostPremarks i s w) (ha : ¬ ended (track s.tag w)) :
    ∃ z k landed,
      CorridorWord s.tag.config (back b d) d w (rearFold i s w).tag.config z k
        (filledRearDepartures i s w) landed := by
  induction w generalizing s b d with
  | nil => exact ⟨_,_,0,.nil _ _ _⟩
  | cons e w ih =>
    have hp := hg.1
    let x := s.tag.config
    let r := back b d
    have hGhost := hg.2.1 r hr
    have hmarks := firstRear_corridor_marks hf
    have hout : liftedSite r d = b := liftedSite_back_end b d hf.lt
    have hI := rearInterior_of_ghost_and_marks hm hGhost hmarks.2
    have ha₁ : ¬ ended (advance s.tag e) := fun h => ha (ended_run (advance s.tag e) w h)
    obtain ⟨b',hb',hcar⟩ := live_step_carrier hb ha₁
    have hConf : (rearAdvance i s e).tag.config = step x e := by
      rw [rearAdvance_tag,projection_step]
    have hTailLive : ¬ ended (track (rearAdvance i s e).tag w) := by
      rw [rearAdvance_tag]; exact ha
    have hC : (rearAdvance i s e).tag.carrier = some b' := by rwa [rearAdvance_tag]
    have hm' : MCOV (rearAdvance i s e).tag.config := by
      rw [hConf]; exact mcov_step hn x hm e
    by_cases he : e = b
    · subst e
      obtain ⟨heq,htr⟩ := carrierStep_selected_survives x b b' hcar
      subst b'
      obtain ⟨hfn,hrn⟩ := firstRear_tag_moves hn x hm b hf htr
      have hpays := unmarked_pay_false hm b ((tagTransfer_iff _ _).mp htr).2.2.2.1
      have hns : rearShifts s b r = false := by
        apply Bool.eq_false_iff.mpr
        intro hs
        have hpy := ((paid_moves_rear_iff hm i b r s rfl).mp hs).2
        simp [hpays] at hpy
      have hR := rear_next i b r s hp hr
      simp only [hns,Bool.false_eq_true,if_false] at hR
      have hNextRear : (rearAdvance i s b).rear = some (back (rightNeighbor b) (d+1)) := by
        rw [hrn]; exact hR
      obtain ⟨z,k,landed,hword⟩ := ih (rearAdvance i s b) (rightNeighbor b) (d+1)
        hm' hC hNextRear (hConf.symm ▸ hfn) hg.2.2.2 hTailLive
      rw [hConf,hrn] at hword
      have hword' : CorridorWord (step x (liftedSite r d)) r (d+1) w
          (rearFold i (rearAdvance i s b) w).tag.config z k
          (filledRearDepartures i (rearAdvance i s b) w) landed := by
        rw [hout]
        exact hword
      refine ⟨z,k,landingBit x b + landed,?_⟩
      have hh := CorridorWord.grow hfn.lt (hI (liftedSite r d) ⟨d,Nat.le_refl _,rfl⟩) hword'
      rw [hout] at hh
      have hns' : rearShifts s b (back b d) = false := hns
      simpa [rearFold,filledRearDepartures,filledRearMark,hr,hns'] using hh
    · have hEq := carrierStep_not_selected_stays x e b b' (Ne.symm he) hcar
      subst b'
      by_cases hs : rearShifts s e r = true
      · obtain ⟨heR,hpy⟩ := (paid_moves_rear_iff hm i e r s rfl).mp hs
        have hpr : rightNeighbor e = r := by rw [heR,right_predecessor]
        have hnot : d ≠ 0 := by
          intro h0
          have hbr : r = b := by
            change back b d = b
            rw [h0,back_zero]
          have hP := rear_phase_next i e r s hp hr
          rw [hs] at hP
          apply hg.2.2.1
          rw [hP]
          apply (phaseAfter_pinned _ _ _ _).mpr
          have hsr : s.rear = some b := hr.trans (congrArg some hbr)
          exact Or.inr ⟨rfl,hb.trans hsr.symm⟩
        have hpy' : geometricPay (x (predecessor (back b d))) (x (back b d)) = true := by
          change geometricPay (x (predecessor r)) (x r) = true
          rw [← heR]
          exact hpr ▸ hpy
        have hnext := firstRear_moves hn x hm b hf hpy'
        simp only [if_neg hnot] at hnext
        rw [← heR] at hnext
        have hR := rear_next i e r s hp hr
        rw [hs,if_pos rfl] at hR
        obtain ⟨z,k,landed,hword⟩ := ih (rearAdvance i s e) b (d-1)
          hm' hC (by rw [hnext.2]; exact hR) (hConf.symm ▸ hnext.1) hg.2.2.2 hTailLive
        rw [hConf,hnext.2] at hword
        refine ⟨z,k,landed,?_⟩
        have hh := CorridorWord.drop hf.lt (by omega) hpr (by rwa [hout]) hword
        have hs' : rearShifts s e (back b d) = true := hs
        simpa [rearFold,filledRearDepartures,filledRearMark,hr,hs'] using hh
      · have hs' := Bool.eq_false_iff.mpr hs
        have hnext := firstRear_stationary hn x hm b e hf
          (fun h => hs ((paid_moves_rear_iff hm i e r s rfl).mpr h))
        have hR := rear_next i e r s hp hr
        rw [if_neg hs] at hR
        obtain ⟨z,k,landed,hword⟩ := ih (rearAdvance i s e) b d
          hm' hC hR (hConf.symm ▸ hnext) hg.2.2.2 hTailLive
        rw [hConf] at hword
        refine ⟨z,k,landed,?_⟩
        have hh := CorridorWord.stationary hI (hmarks.1 e) (by rwa [hout]) hword
        have hs'' : rearShifts s e (back b d) = false := hs'
        simpa [rearFold,filledRearDepartures,filledRearMark,hr,hs''] using hh

end L4.RearFrontStock

namespace L4.RearFrontStock
open RearTrace TaggedTrace

/-- The complete conditional inventory estimate for an actual phase
suffix of the original observer. The only phase premise is its physical
ghost/non-preempted classification and the nearest rear at entry. -/
theorem filledRearDepartures_bound {p c n : Nat} (hn : 4 ≤ n)
    (x₀ : Config p c n) (i : Fin n) (before w : List (Fin n))
    (hm : MCOV x₀) (hnd : (∃ j : Fin n, (x₀ j).mark = true))
    (ha : ¬ ended (track (init x₀ i) (before++w)))
    (b : Fin n) (d : Nat)
    (hb : (rearTrack x₀ i before).tag.carrier = some b)
    (hr : (rearTrack x₀ i before).rear = some (back b d))
    (hf : FirstRear (rearTrack x₀ i before).tag.config b d)
    (hg : GhostPremarks i (rearTrack x₀ i before) w) :
    filledRearDepartures i (rearTrack x₀ i before) w ≤ 2*(n : Int)+1 := by
  let s := rearTrack x₀ i before
  have hmc : MCOV s.tag.config := by
    change MCOV (rearTrack x₀ i before).tag.config
    rw [rearTrack_tag,projection_run]
    have preserves (y : Config p c n) (t : List (Fin n)) (hy : MCOV y) : MCOV (run y t) := by
      induction t generalizing y with
      | nil => exact hy
      | cons e t ih => exact ih (step y e) (mcov_step hn y hy e)
    exact preserves x₀ before hm
  have hAl : ¬ ended (track s.tag w) := by
    change ¬ ended (track (rearTrack x₀ i before).tag w)
    rw [rearTrack_tag,← track_append]
    exact ha
  obtain ⟨z,k,l,hw⟩ := corridorWord_of_ghostPremarks hn i s w b d hmc hb hr hf hg hAl
  have hCfg : (track (init x₀ i) before).config = s.tag.config := by
    change (track (init x₀ i) before).config = (rearTrack x₀ i before).tag.config
    rw [rearTrack_tag]
  have hTag : (track (init x₀ i) before).carrier = some (liftedSite (back b d) d) := by
    rw [liftedSite_back_end b d hf.lt,← rearTrack_tag]
    exact hb
  exact hw.filled_le_twice_size_add_one hn x₀ i before hm hnd hCfg hTag ha

end L4.RearFrontStock

#print axioms L4.RearFrontStock.corridorWord_of_ghostPremarks
#print axioms L4.RearFrontStock.filledRearDepartures_bound

import Leader.L4.WindowScopedFourHead

namespace L4.WindowFourHeadStock
open RearFrontStock

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

private theorem rn_ne {n : Nat} (hn : 4 ≤ n) (e : Fin n) : e ≠ rightNeighbor e := by
  intro hh
  apply Nat.zero_ne_one
  apply liftedSite_inj e (by omega : 0 < n) (by omega : 1 < n)
  rw [liftedSite_succ, liftedSite_zero]; exact hh

private theorem at_right {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) (e : Fin n) :
    step x e (rightNeighbor e) = (pairStep (x e) (x (rightNeighbor e))).2 := by
  simp [step,(rn_ne hn e).symm]

private theorem at_left {p c n : Nat} (x : Config p c n) (e : Fin n) :
    step x e e = (pairStep (x e) (x (rightNeighbor e))).1 := by simp [step]

private theorem at_other {p c n : Nat} (x : Config p c n) (e i : Fin n)
    (h₁ : i ≠ e) (h₂ : i ≠ rightNeighbor e) : step x e i = x i := by simp [step,h₁,h₂]

private theorem sb_nonneg {p c : Nat} (u : Site p c) : 0 ≤ stockBit u := by simp [stockBit]

private theorem rear_mask_frame {p c n : Nat} (x y : Config p c n)
    (r r' i : Fin n) (d d' : Nat) (hf : y i = x i)
    (h : InRear r' d' i → InRear r d i) :
    rearStock y r' d' i ≤ rearStock x r d i := by
  classical
  by_cases hi : InRear r' d' i
  · simp [rearStock,hi,h hi,hf]
  · simp only [rearStock,if_neg hi]
    split
    · exact sb_nonneg _
    · omega


theorem grow_paid_no_increase {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (r : Fin n) (d : Nat) (hD : d+1 < n)
    (hDonor : (x (liftedSite r d)).leader = false)
    (hm : (x (liftedSite r d)).mark = true)
    (hp : geometricPay (x (liftedSite r d)) (x (rightNeighbor (liftedSite r d))) = true) :
    rearInventory (step x (liftedSite r d)) r (d+1) ≤
      rearInventory x r d := by
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
  change BarrierIID.edgeSum (rearStock y r (d+1)) ≤ BarrierIID.edgeSum (rearStock x r d)
  rw [← Int.add_zero (BarrierIID.edgeSum (rearStock y r (d+1)))]
  refine sum_pair_bound _ _ e v (rn_ne hn e) ?_ 0 ?_
  · intro i he hv'
    apply rear_mask_frame x y r r i d (d+1) (at_other x e i he hv')
    rintro ⟨j,hj,hj'⟩
    refine ⟨j,?_,hj'⟩
    by_cases hJ : j=d+1
    · exact (hv' (hj'.symm.trans (hJ.symm ▸ hv))).elim
    · omega
  · simp only [rearStock,if_neg hV,if_pos hE,if_pos hE',if_pos hV',Int.add_zero]
    have hh := WindowScopedFourHead.paid_nonliving_stock_charge (x e) (x v) hDonor hm hp
    have hL : stockBit (y e) + stockBit (y v) + 1 = stockBit (x e) + stockBit (x v) := by
      change stockBit (step x e e) + stockBit (step x e (rightNeighbor e)) + 1 = _
      simpa [at_left,at_right hn] using hh
    have hBit : stockBit (x v) ≤ 1 := by cases h : (x v).stock <;> simp [stockBit,h]
    omega


/-- A counted W payment reaches two strictly retained sockets. The full
interval inventory spends exactly (at least) one byte on this physical mark. -/
theorem fixed_paid_decreases {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (r e : Fin n) (d : Nat)
    (ha : InRear r d e) (hb : InRear r d (rightNeighbor e))
    (hnL : (x e).leader = false) (hm : (x e).mark = true)
    (hp : geometricPay (x e) (x (rightNeighbor e)) = true) :
    rearInventory (step x e) r d + 1 ≤ rearInventory x r d := by
  classical
  let y := step x e
  let v := rightNeighbor e
  change BarrierIID.edgeSum (rearStock y r d) + 1 ≤ BarrierIID.edgeSum (rearStock x r d)
  refine sum_pair_bound _ _ e v (rn_ne hn e) ?_ 1 ?_
  · intro i hi hv
    exact rear_mask_frame x y r r i d d (at_other x e i hi hv) id
  · change InRear r d v at hb
    simp only [rearStock,if_pos ha,if_pos hb]
    have hh := WindowScopedFourHead.paid_nonliving_stock_charge (x e) (x v) hnL hm hp
    change stockBit (step x e e) + stockBit (step x e (rightNeighbor e)) + 1 ≤ _
    simpa [at_left,at_right hn] using Int.le_of_eq hh

/-- A single verified moving-interval row. The coordinate d is the
offset of K's incoming bond from J, so the inclusive inventory is
[J,K−1]. Only a W mark consumes one displacement credit. -/
inductive Row {p c n : Nat} (x : Config p c n) (r e : Fin n) (d : Nat) :
    Fin n → Nat → Nat → Prop where
  | stationary (inside : ∀ i, InRear r d i → (x i).leader=false)
      (incoming : rightNeighbor e=r → (x e).mark=true) : Row x r e d r d 0
  | wPaid (ha : InRear r d e) (hb : InRear r d (rightNeighbor e))
      (hl : (x e).leader=false) (hm : (x e).mark=true)
      (hp : geometricPay (x e) (x (rightNeighbor e))=true) :
      Row x r e d r d 1
  | jPaid (hD : d<n) (hp : 0<d) (hr : rightNeighbor e=r)
      (he : e≠liftedSite r d) : Row x r e d (rightNeighbor r) (d-1) 0
  | kPaid (hD : d+1<n) (he : e=liftedSite r d)
      (hl : (x e).leader=false) (hm : (x e).mark=true)
      (hp : geometricPay (x e) (x (rightNeighbor e))=true) :
      Row x r e d r (d+1) 0

theorem Row.charge {p c n : Nat} (hn : 4≤n)
    {x : Config p c n} {r e r' : Fin n} {d d' delta : Nat}
    (h : Row x r e d r' d' delta) :
    rearInventory (step x e) r' d' + (delta : Int) ≤ rearInventory x r d := by
  cases h with
  | stationary h1 h2 => simpa using rearInventory_stationary hn x r e d h1 h2
  | wPaid h1 h2 h3 h4 h5 => simpa using fixed_paid_decreases hn x r e d h1 h2 h3 h4 h5
  | jPaid h1 h2 h3 h4 =>
    have h := rearInventory_rear_drop hn x r e d h1 h2 h3 h4
    simp only [Int.natCast_zero,Int.add_zero]
    have hs := sb_nonneg (x r)
    omega
  | kPaid h1 he h2 h3 h4 =>
    subst e
    simpa using grow_paid_no_increase hn x r d h1 h2 h3 h4

/-- Certificate on a raw word, with no global-death or retirement test.
A coordinate/roster observer must select the correct row at each mark. -/
inductive LedgerWord {p c n : Nat} : Config p c n → Fin n → Nat → List (Fin n) → Nat → Prop where
  | nil {x r d} : LedgerWord x r d [] 0
  | cons {x r d e r' d' delta w k} : Row x r e d r' d' delta →
      LedgerWord (step x e) r' d' w k → LedgerWord x r d (e::w) (delta+k)

theorem LedgerWord.bound {p c n : Nat} (hn : 4≤n)
    {x : Config p c n} {r : Fin n} {d : Nat} {w : List (Fin n)} {k : Nat}
    (h : LedgerWord x r d w k) :
    (k : Int) ≤ rearInventory x r d := by
  induction h with
  | nil => exact (rearInventory_interval _ _ _).1
  | cons hrow _ ih =>
    have hstep := hrow.charge hn
    omega

#print axioms Row.charge
#print axioms LedgerWord.bound

private theorem oneSite_sum {n : Nat} (r : Fin n) :
    BarrierIID.edgeSum (fun i => if i=r then 1 else 0) = 1 := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
    rw [sum_succ]
    refine Fin.cases ?_ (fun j => ?_) r
    · have hzero (m : Nat) : BarrierIID.edgeSum (fun _ : Fin m => 0) = 0 := by
        induction m with
        | zero => rfl
        | succ m ih => rw [sum_succ,ih]; rfl
      rw [show (fun i : Fin n => if i.succ=(0 : Fin (n+1)) then (1:Int) else 0) =
          (fun _ : Fin n => 0) from funext (fun i => by
            rw [if_neg (fun h => by have H := congrArg Fin.val h; simp at H)])]
      simp [hzero]
    · rw [show (fun i : Fin n => if i.succ=j.succ then (1:Int) else 0) =
          (fun i : Fin n => if i=j then (1:Int) else 0) from funext (fun i => by simp),
        ih]
      rw [if_neg (show (0 : Fin (n+1)) ≠ j.succ from fun h => by
        have H := congrArg Fin.val h
        simp at H),Int.zero_add]

theorem interval_size_cap {p c n : Nat} (x : Config p c n) (r : Fin n) (d : Nat) :
    rearInventory x r d ≤ (d : Int)+1 := by
  classical
  have hOne (i : Fin n) : stockBit (x i)≤1 := by cases h : (x i).stock <;> simp [stockBit,h]
  induction d with
  | zero =>
    change BarrierIID.edgeSum (rearStock x r 0) ≤ 0+1
    rw [Int.zero_add,← oneSite_sum r]
    apply sum_mono
    intro i
    by_cases h : InRear r 0 i
    · obtain ⟨j,hj,he⟩ := h
      have hz : j=0 := by omega
      have hi : i=r := by simpa [hz,liftedSite_zero] using he.symm
      simp [rearStock,hi,show InRear r 0 r from ⟨0,by omega,liftedSite_zero r⟩,hOne]
    · simp only [rearStock,if_neg h]
      split <;> omega
  | succ d ih =>
    have h : rearInventory x r (d+1) ≤ rearInventory x r d + 1 := by
      change BarrierIID.edgeSum (rearStock x r (d+1)) ≤ BarrierIID.edgeSum (rearStock x r d)+1
      rw [← oneSite_sum (liftedSite r (d+1)), ← sum_add]
      apply sum_mono
      intro i
      by_cases hs : InRear r d i
      · have hn : InRear r (d+1) i := by
          obtain ⟨j,hj,he⟩ := hs
          exact ⟨j,by omega,he⟩
        simp only [rearStock,if_pos hs,if_pos hn]
        split <;> omega
      · by_cases hh : InRear r (d+1) i
        · have hex := hh
          obtain ⟨j,hj,he⟩ := hex
          have hj' : j=d+1 := by
            by_cases h : j≤d
            · exact (hs ⟨j,h,he⟩).elim
            · omega
          have hi : i=liftedSite r (d+1) := he.symm.trans (congrArg (liftedSite r) hj')
          simp only [rearStock,if_pos hh,if_neg hs,if_pos hi]
          simpa using hOne i
        · simp only [rearStock,if_neg hh,if_neg hs]
          split <;> omega
    omega

theorem LedgerWord.count_le_size {p c n : Nat} (hn : 4≤n)
    {x : Config p c n} {r : Fin n} {d : Nat} {w : List (Fin n)} {k : Nat}
    (h : LedgerWord x r d w k) : k≤d+1 := by
  have h1 := h.bound hn
  have h2 := interval_size_cap x r d
  omega

#print axioms LedgerWord.count_le_size
end L4.WindowFourHeadStock

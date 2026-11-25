import Leader.L4.RankPhysical
import Leader.L4.RearRefillTrack
import Leader.L4.GGStockPhysical

namespace L4.RankRootless
open RearFrontStock

/-- The premark condition for the rootless stock-drain stage. -/
def NoLiving {p c n : Nat} (x : Config p c n) : Prop :=
  ∀ i, (x i).leader = false

/-- Number of physical stock tokens, calculated over the raw site set. -/
def stockCount {p c n : Nat} (x : Config p c n) : Int :=
  BarrierIID.edgeSum (fun j => stockBit (x j))

/-- No physical stock bit is set. -/
def NoStock {p c n : Nat} (x : Config p c n) : Prop :=
  ∀ i, (x i).stock = false

private theorem no_self {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by
    simpa [liftedSite_succ,liftedSite_zero] using h
  have he' := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

private theorem atom_ge_zero {p c : Nat} (u : Site p c) : 0 ≤ stockBit u := by simp [stockBit]

/-- A rootless premark cannot mint stock, even on the first birth mark. -/
theorem no_mint {p c n : Nat} (x : Config p c n) (h : NoLiving x) (e : Fin n) :
    StockTokenRows.row (x e) (x (rightNeighbor e)) ≠ .mint :=
  GGStockPhysical.no_mint_from_ghost _ _ (h e)

private theorem pay_stock {p c : Nat} (u v : Site p c)
    (hl : u.leader = false) (hp : geometricPay u v = true) : u.stock = true := by
  have h := RearTrace.geometricPay_ready u v hp
  simpa [payer,hl] using h

/-- At every covered rootless premark, each selected P3 consumes one
stock token and no literal row adds stock. Includes the marked stop step. -/
theorem stockCount_paid_le {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) (e : Fin n)
    (hm : MCOV x) (hl : NoLiving x) :
    stockCount (step x e) + ((geometricPay (x e) (x (rightNeighbor e))).toNat : Int) ≤
      stockCount x := by
  let v := rightNeighbor e
  have hL : step x e e = (pairStep (x e) (x v)).1 := by simp [step,v]
  have hR : step x e v = (pairStep (x e) (x v)).2 := by simp [step,v,no_self hn e]
  unfold stockCount
  refine sum_pair_bound _ _ e v (Ne.symm (no_self hn e)) ?_ _ ?_
  · intro j h₁ h₂
    have h := show step x e j = x j by simp [step,h₁,h₂,v]
    simp [h]
  · rw [hL,hR]
    by_cases hp : geometricPay (x e) (x v) = true
    · have hs := pay_stock _ _ (hl e) hp
      have hmark := RearTrace.paid_was_marked hm e hp
      have hx := GGStockPhysical.marked_stock_consumed (x e) (x v) hmark hs
      have hp' : geometricPay (x e) (x (rightNeighbor e)) = true := hp
      simp [hp',stockBit,hs,hx.1,hx.2] <;> omega
    · have hf : geometricPay (x e) (x v) = false := Bool.eq_false_iff.mpr hp
      change stockBit (pairStep (x e) (x v)).1 + stockBit (pairStep (x e) (x v)).2 +
        ((geometricPay (x e) (x v)).toNat : Int) ≤ _
      simpa [hf] using pair_stock_le_of_nonleader (x e) (x v) (hl e)

/-- Stock does not grow while its premark configuration has no leader. -/
theorem stockCount_nonincrease {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e : Fin n) (hm : MCOV x) (hl : NoLiving x) :
    stockCount (step x e) ≤ stockCount x := by
  have h := stockCount_paid_le hn x e hm hl
  omega

/-- A covered zero-stock rootless state has no possible P3 payment. -/
theorem payment_disabled {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hl : NoLiving x) (hs : NoStock x) :
    geometricPay (x e) (x (rightNeighbor e)) = false := by
  apply Bool.eq_false_iff.mpr
  intro hp
  have hh := pay_stock _ _ (hl e) hp
  simp [hs e] at hh

/-- Marks and residues are exactly fixed at a covered zero-stock rootless
premark. A P5 birth may change the type but does not alter this geometry. -/
theorem zero_stock_static {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e : Fin n) (hm : MCOV x) (hl : NoLiving x) (hs : NoStock x) :
    ∀ i, (step x e i).mark = (x i).mark ∧ (step x e i).residue = (x i).residue := by
  let v := rightNeighbor e
  have hp := payment_disabled x e hl hs
  have gg := pair_geometric_fields (x e) (x v)
  have hR : (pairStep (x e) (x v)).2.residue = (x v).residue := by
    simpa [v,hp] using gg.2.2
  intro i
  constructor
  · rw [covered_step_mark hn x hm]; simp [hp]
  · by_cases hE : i = e
    · subst i; simpa [step,v] using gg.1
    · by_cases hV : i = v
      · subst i; simpa [step,v,no_self hn e] using hR
      · simp [step,hE,hV,v]

/-- Zero stock remains zero through every rootless mark, including
a terminating birth. -/
theorem zero_stock_preserved {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e : Fin n) (hl : NoLiving x) (hs : NoStock x) :
    NoStock (step x e) := by
  let v := rightNeighbor e
  have h := pair_stock_le_of_nonleader (x e) (x v) (hl e)
  have hL : (pairStep (x e) (x v)).1.stock = false := by
    cases hx : (pairStep (x e) (x v)).1.stock
    · rfl
    · have hh := atom_ge_zero (pairStep (x e) (x v)).2
      simp [stockBit,hs e,hs v,hx] at h hh
      omega
  have hR : (pairStep (x e) (x v)).2.stock = false := by
    cases hx : (pairStep (x e) (x v)).2.stock
    · rfl
    · have hh := atom_ge_zero (pairStep (x e) (x v)).1
      simp [stockBit,hs e,hs v,hx] at h hh
      omega
  intro i
  by_cases hE : i = e
  · subst i; simpa [step,v] using hL
  · by_cases hV : i = v
    · subst i; simpa [step,v,no_self hn e] using hR
    · simpa [step,hE,hV,v] using hs i

end L4.RankRootless

namespace L4.RankRootless
open RearFrontStock

/-- The selected payment loses exactly one stock, not merely at least one. -/
theorem stockCount_paid_eq_of_pay {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (e : Fin n) (hm : MCOV x) (hl : NoLiving x)
    (hp : geometricPay (x e) (x (rightNeighbor e)) = true) :
    stockCount (step x e) + 1 = stockCount x := by
  have hle := stockCount_paid_le hn x e hm hl
  rw [hp] at hle
  let v := rightNeighbor e
  have hs := pay_stock (x e) (x v) (hl e) hp
  have hz := GGStockPhysical.marked_stock_consumed (x e) (x v)
    (RearTrace.paid_was_marked hm e hp) hs
  have hL : step x e e = (pairStep (x e) (x v)).1 := by simp [step,v]
  have hR : step x e v = (pairStep (x e) (x v)).2 := by simp [step,v,no_self hn e]
  have hge : stockCount x + (-1) ≤ stockCount (step x e) := by
    unfold stockCount
    refine sum_pair_bound _ _ e v (Ne.symm (no_self hn e)) ?_ (-1) ?_
    · intro j hj hv
      simp [step,hj,hv,v]
    · rw [hL,hR]
      simp [stockBit,hz.1,hz.2,hs] <;> omega
  change stockCount (step x e) + 1 ≤ stockCount x at hle
  omega

/-- A count is nonnegative and cannot exceed one token per physical site. -/
theorem stockCount_interval {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n) :
    0 ≤ stockCount x ∧ stockCount x ≤ (n : Int) := by
  let r : Fin n := ⟨0,by omega⟩
  have hh : stockCount x = rearInventory x r (n-1) := by
    unfold stockCount rearInventory
    apply congrArg BarrierIID.edgeSum
    funext i
    obtain ⟨d,hd,h⟩ := liftedSite_of_site r i
    have he : InRear r (n-1) i := ⟨d,by omega,h⟩
    simp [rearStock,he]
  rw [hh]
  exact rearInventory_interval x r (n-1)

/-- An exact finite word all of whose premark states are rootless. The
final state can have just realized the designated birth stop. -/
def RootlessWord {p c n : Nat} (x : Config p c n) : List (Fin n) → Prop
  | [] => True
  | e::w => NoLiving x ∧ RootlessWord (step x e) w

/-- Number of selected physical P3 marks along an actual word. -/
def paymentCount {p c n : Nat} (x : Config p c n) : List (Fin n) → Int
  | [] => 0
  | e::w => (geometricPay (x e) (x (rightNeighbor e))).toNat +
      paymentCount (step x e) w

/-- Rootless stock is a decreasing pathwise resource, including truncated
words that end at the first birth or first retirement. -/
theorem rootless_trace_stock {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (w : List (Fin n)) (hm : MCOV x) (h : RootlessWord x w) :
    stockCount (run x w) + paymentCount x w ≤ stockCount x := by
  induction w generalizing x with
  | nil => simp [run,paymentCount]
  | cons e w ih =>
    have hS := stockCount_paid_le hn x e hm h.1
    have hW := ih (step x e) (mcov_step hn x hm e) h.2
    simp only [run,paymentCount]
    omega

/-- Every covered rootless word has at most n paid shifts before its stop. -/
theorem rootless_paymentCount_le_size {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (w : List (Fin n)) (hm : MCOV x) (h : RootlessWord x w) :
    paymentCount x w ≤ (n : Int) := by
  have hS := rootless_trace_stock hn x w hm h
  have h0 := (stockCount_interval hn (run x w)).1
  have h1 := (stockCount_interval hn x).2
  omega

/-- Zero-stock geometry and stock stay fixed over all rootless premarks. -/
theorem zero_stock_rootless_run {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (w : List (Fin n)) (hm : MCOV x) (h0 : NoStock x)
    (h : RootlessWord x w) :
    NoStock (run x w) ∧
    ∀ i, (run x w i).mark = (x i).mark ∧ (run x w i).residue = (x i).residue := by
  induction w generalizing x with
  | nil => exact ⟨h0,fun _ => ⟨rfl,rfl⟩⟩
  | cons e w ih =>
    obtain ⟨hS,hF⟩ := ih (step x e) (mcov_step hn x hm e)
      (zero_stock_preserved hn x e h.1 h0) h.2
    refine ⟨hS,fun i => ?_⟩
    have hI := zero_stock_static hn x e hm h.1 h0 i
    exact ⟨(hF i).1.trans hI.1,(hF i).2.trans hI.2⟩

end L4.RankRootless


import Leader.L4.BarrierRows

namespace L4.StockTokenRows
open L4

inductive Action where
  | stay | drop | transfer | mint
  deriving DecidableEq

/-- Read the stock action after R0 and native impact, exactly where P0/P2/P3
take their guards. A mint is the P2 branch with an empty donor stock. -/
def action {p c : Nat} (u v : Site p c) : Action :=
  if v.leader then .drop
  else if !u.mark && !v.stock && payer u then
    if u.stock then .transfer else .mint
  else if u.mark && payer u then .drop
  else .stay

def row {p c : Nat} (u v : Site p c) : Action :=
  let w := native (materialize u v) v
  action w.1 w.2

/-- Ghost labels are not fields of the protocol. A supplied mint label is used
only in the mint branch; freshness, if needed, is a separate global premise. -/
def update {α : Type} (a : Action) (l r : Option α) (mint : α) :
    Option α × Option α :=
  match a with
  | .stay => (l,r)
  | .drop => (none,r)
  | .transfer => (none,l)
  | .mint => (none,some mint)

private theorem nativeStocks {p c : Nat} (u v : Site p c) :
    ((native u v).1.stock, (native u v).2.stock) = (u.stock,v.stock) := by
  have a : (fireInitiator u).stock = u.stock := by unfold fireInitiator; split <;> rfl
  have b : (fireResponder v).stock = v.stock := by
    unfold fireResponder
    split
    · cases v.signal <;> rfl
    · rfl
  change ((followerBullet (pinned (impact (fireInitiator u) (fireResponder v)).1
      (impact (fireInitiator u) (fireResponder v)).2)
      (impact (fireInitiator u) (fireResponder v)).1
      (impact (fireInitiator u) (fireResponder v)).2).1.stock,
      (followerBullet (pinned (impact (fireInitiator u) (fireResponder v)).1
      (impact (fireInitiator u) (fireResponder v)).2)
      (impact (fireInitiator u) (fireResponder v)).1
      (impact (fireInitiator u) (fireResponder v)).2).2.stock) = _
  generalize ha : fireInitiator u = x at a ⊢
  generalize hb : fireResponder v = y at b ⊢
  rw [← a, ← b]
  have h₁ : ((impact x y).1.stock, (impact x y).2.stock) = (x.stock,y.stock) := by
    unfold impact
    split
    · split <;> rfl
    · rfl
  have h₂ (g : Bool) (s t : Site p c) :
      ((followerBullet g s t).1.stock, (followerBullet g s t).2.stock) =
        (s.stock,t.stock) := by unfold followerBullet; split <;> (try split) <;> rfl
  exact (h₂ _ _ _).trans h₁

private theorem paymentLabels {p c : Nat} {α : Type} (u v : Site p c)
    (l r : Option α) (mint : α) (hl : l.isSome = u.stock) (hr : r.isSome = v.stock) :
    (let t := update (action u v) l r mint; (t.1.isSome,t.2.isSome)) =
      ((payment u v).1.stock,(payment u v).2.stock) := by
  unfold action payment
  split
  · simp [update, hr]
  · split
    · split
      · rename_i hs
        simp [update, hl, hs]
      · rfl
    · split <;> simp [update, hl, hr]

theorem pair_labels {p c : Nat} {α : Type} (u v : Site p c)
    (l r : Option α) (mint : α) (hl : l.isSome = u.stock) (hr : r.isSome = v.stock) :
    (let t := update (row u v) l r mint; (t.1.isSome,t.2.isSome)) =
      ((pairStep u v).1.stock,(pairStep u v).2.stock) := by
  rw [pairStep_stocks_eq_prefix]
  let w := native (materialize u v) v
  have hm : (materialize u v).stock = u.stock := by unfold materialize; split <;> rfl
  have hs := nativeStocks (materialize u v) v
  have hleft : w.1.stock = u.stock := (congrArg Prod.fst hs).trans hm
  have hright : w.2.stock = v.stock := congrArg Prod.snd hs
  exact paymentLabels w.1 w.2 l r mint (hl.trans hleft.symm) (hr.trans hright.symm)

theorem mint_guard {p c : Nat} (u v : Site p c) (h : action u v = .mint) :
    v.leader = false ∧ u.mark = false ∧ v.stock = false ∧
      u.stock = false ∧ u.leader = true := by
  cases hv : v.leader <;> cases hm : u.mark <;> cases hs : v.stock <;>
    cases hu : u.stock <;> cases hl : u.leader <;>
    simp_all [action, payer]

/-- In particular, the living empty donor is an input-site fact, not just
a property of a native intermediate. Neither materialization nor the native
rows change the initiator's leader bit. -/
theorem row_mint_input {p c : Nat} (u v : Site p c) (h : row u v = .mint) :
    u.stock = false ∧ u.leader = true ∧ v.stock = false := by
  let w := native (materialize u v) v
  have hg := mint_guard w.1 w.2 h
  have hm : (materialize u v).stock = u.stock := by unfold materialize; split <;> rfl
  have hs := nativeStocks (materialize u v) v
  have left : w.1.stock = u.stock := (congrArg Prod.fst hs).trans hm
  have right : w.2.stock = v.stock := congrArg Prod.snd hs
  have materializeLeader : (materialize u v).leader = u.leader := by
    unfold materialize; split <;> rfl
  have fireLeader (x : Site p c) : (fireInitiator x).leader = x.leader := by
    unfold fireInitiator; split <;> rfl
  have impactLeader (x y : Site p c) : (impact x y).1.leader = x.leader := by
    unfold impact; split <;> rfl
  have followerLeader (g : Bool) (x y : Site p c) :
      (followerBullet g x y).1.leader = x.leader := by
    unfold followerBullet; split <;> (try split) <;> rfl
  let z := impact (fireInitiator (materialize u v)) (fireResponder v)
  have lead : w.1.leader = u.leader := by
    change (followerBullet (pinned z.1 z.2) z.1 z.2).1.leader = u.leader
    rw [followerLeader]
    dsimp [z]
    rw [impactLeader,fireLeader,materializeLeader]
  exact ⟨left.symm.trans hg.2.2.2.1, lead.symm.trans hg.2.2.2.2,
    right.symm.trans hg.2.2.1⟩

#print axioms pair_labels
#print axioms mint_guard
#print axioms row_mint_input
end L4.StockTokenRows

import Leader.L4.GGStock
import Leader.L4.StockTokenRows
import Leader.L4.TaggedGeometry

namespace L4.GGStockPhysical
open StockTokenRows

private theorem native_stock_mark {p c : Nat} (u v : Site p c) :
    (native u v).1.stock = u.stock ∧ (native u v).2.stock = v.stock ∧
      (native u v).1.mark = u.mark := by
  have hi : (fireInitiator u).stock = u.stock ∧ (fireInitiator u).mark = u.mark := by
    unfold fireInitiator
    split <;> exact ⟨rfl,rfl⟩
  have hj : (fireResponder v).stock = v.stock ∧ (fireResponder v).leader = v.leader := by
    unfold fireResponder
    split
    · cases v.signal <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  have hI (a b : Site p c) :
      (impact a b).1.stock = a.stock ∧ (impact a b).2.stock = b.stock ∧
      (impact a b).1.mark = a.mark ∧ ((impact a b).2.leader = true → b.leader = true) := by
    unfold impact
    split
    · split <;> simp
    · simp
  have hF (g : Bool) (a b : Site p c) :
      (followerBullet g a b).1.stock = a.stock ∧ (followerBullet g a b).2.stock = b.stock ∧
      (followerBullet g a b).1.mark = a.mark ∧ (followerBullet g a b).2.leader = b.leader := by
    unfold followerBullet
    split
    · split <;> exact ⟨rfl,rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl,rfl,rfl⟩
  unfold native
  simp only
  exact ⟨(hF _ _ _).1.trans ((hI _ _).1.trans hi.1),
    (hF _ _ _).2.1.trans ((hI _ _).2.1.trans hj.1),
    (hF _ _ _).2.2.1.trans ((hI _ _).2.2.1.trans hi.2)⟩

private theorem old_mark_materialized {p c : Nat} (u v : Site p c)
    (h : u.mark = true) : (materialize u v).mark = true := by
  unfold materialize; split
  · rfl
  · exact h

private theorem old_stock_materialized {p c : Nat} (u v : Site p c) :
    (materialize u v).stock = u.stock := by
  unfold materialize; split <;> rfl

/-- Stock at the upstream endpoint of a marked boundary is removed on
that edge regardless of whether the boundary is currently a leader or
ghost, and regardless of a simultaneous native kill of a leader. The
post-native leader branch is P0; otherwise the marked payer branch is P3. -/
theorem marked_stock_drop {p c : Nat} (u v : Site p c)
    (hm : u.mark = true) (hs : u.stock = true) : row u v = .drop := by
  let w := native (materialize u v) v
  have hs' : w.1.stock = true :=
    (native_stock_mark _ _).1.trans ((old_stock_materialized _ _).trans hs)
  have hm' : w.1.mark = true :=
    (native_stock_mark _ _).2.2.trans (old_mark_materialized _ _ hm)
  change action w.1 w.2 = .drop
  cases h : w.2.leader <;> simp [action,payer,h,hm',hs']

/-- The physical stock projection actually deletes the upstream token.
This is the local mechanism that disposes of a quarantined k-resident,
before k could create more room in front of it. -/
theorem marked_stock_consumed {p c : Nat} (u v : Site p c)
    (hm : u.mark = true) (hs : u.stock = true) :
    (pairStep u v).1.stock = false ∧ (pairStep u v).2.stock = v.stock := by
  let l : Option Unit := some ()
  let r : Option Unit := if v.stock then some () else none
  have hl : l.isSome = u.stock := hs.symm
  have hr : r.isSome = v.stock := by cases hv : v.stock <;> simp [r,hv]
  have h := pair_labels u v l r () hl hr
  rw [marked_stock_drop u v hm hs] at h
  simp only [update,Option.isSome_none,hr] at h
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

/-- An already occupied receiver retains its exact stock label on its
incoming edge: no concurrent deposit can overwrite a resident token. -/
theorem incoming_retains_label {p c : Nat} {α : Type} (u v : Site p c)
    (l : Option α) (r mint : α) (hs : v.stock = true) :
    (update (row u v) l (some r) mint).2 = some r := by
  let w := native (materialize u v) v
  have hs' : w.2.stock = true := (native_stock_mark _ _).2.1.trans hs
  change (update (action w.1 w.2) l (some r) mint).2 = _
  unfold action
  by_cases h : w.2.leader = true
  · simp [h, update]
  · have hp : w.2.leader = false := Bool.eq_false_iff.mpr h
    simp only [hp, Bool.false_eq_true, if_false, hs', Bool.not_true, Bool.and_false,
      Bool.false_and]
    by_cases hpay : (w.1.mark && payer w.1) = true
    · simp [hpay, update]
    · simp [hpay, update]

/-- The narrow stop rule guarantees ghost initiators i and j; the literal
row cannot mint on such a mark, not even on an otherwise dirty timer mark. -/
theorem no_mint_from_ghost {p c : Nat} (u v : Site p c)
    (hl : u.leader = false) : row u v ≠ .mint := by
  intro h
  have he := (row_mint_input u v h).2.1
  rw [hl] at he
  contradiction

/-- The global, not yet established, physical projection required by the
abstract stock ledger: enumerate all nonterminal paid moves, each at its
actual predecessor site, and supply chronological no-reuse credits.
This definition is deliberately a proposition about any intended literal
observer, not a claim that the predicate holds for an existing simulation. -/
def ProjectsGGStock {α : Type} (advanceCount : α → Nat) (admitted : α → Prop)
    (s : Nat) : Prop :=
  ∀ x, admitted x →
    ∃ tape : List (GGStock.PaidJ s), advanceCount x = tape.length ∧
      GGStock.CreditTrace (List.finRange s) tape

theorem projected_paid_count_le {α : Type} (advanceCount : α → Nat)
    (admitted : α → Prop) (s : Nat)
    (projection : ProjectsGGStock advanceCount admitted s)
    (x : α) (hx : admitted x) : advanceCount x ≤ s := by
  obtain ⟨tape,he,ht⟩ := projection x hx
  rw [he]
  exact GGStock.paid_j_le_initial_span ht

#print axioms marked_stock_drop
#print axioms marked_stock_consumed
#print axioms incoming_retains_label
#print axioms no_mint_from_ghost
#print axioms projected_paid_count_le

end L4.GGStockPhysical

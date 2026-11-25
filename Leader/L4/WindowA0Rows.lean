import Leader.L4.WindowA0
import Leader.L4.RearFrontStock

/-! Literal A0 release rows and a guard counterexample. -/
namespace L4.WindowA0Rows

theorem pinned_turn_new_source {Q : Nat} (a : Rail) :
    (patrol true true false (.off : Source Q) a .ui).right = .di ∧
    (patrol true true false (.off : Source Q) a .uc).right = .dc := by
  cases a <;> exact ⟨rfl,rfl⟩

theorem return_release_empty_or_trail {Q : Nat} (a : Rail)
    (ha : a = .di ∨ a = .dc) (b : Rail)
    (hb : b = .e ∨ b = .t) :
    (patrol false false false (.off : Source Q) a b).left = .e ∧
    (patrol false false false (.off : Source Q) a b).right = a := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact ⟨rfl,rfl⟩

theorem return_lost_at_break {Q : Nat} (a : Rail) (ha : a = .di ∨ a = .dc) :
    (patrol false false false (.off : Source Q) a .x).left = .e ∧
    (patrol false false false (.off : Source Q) a .x).right = .x := by
  rcases ha with rfl | rfl <;> exact ⟨rfl,rfl⟩

def blank : Config 2 12 16 := fun i => {
  residue := ⟨i.val%2,Nat.mod_lt _ (by decide)⟩
  mark := i.val == 15 || i.val == 2 || i.val == 4
  leader := false
  bullet := .none
  shield := false
  signal := .zero
  stock := false
  source := if i.val == 3 then .i1 else .off
  rail := if i.val == 1 then .ui else .e
}

def dirtyTop : Config 2 12 16 := fun i =>
  if i.val == 0 then {blank i with rail := .x} else blank i

def paidAtTop : Config 2 12 16 := fun i =>
  { blank i with
    stock := i.val == 15
    rail := if i.val == 0 then .ui else .e }

/-- Paper order [worker-to-top, incoming-turn, return] does not release
if the old top was not X-free. Compare the same tape from `blank`. -/
theorem dirty_release_counter : MCOV dirtyTop ∧ COV dirtyTop ∧
    (∀ i, (dirtyTop i).stock = false) ∧
    ((run dirtyTop [0,15]) 0).rail = .di ∧
    ((run dirtyTop [0,15]) 1).rail = .x ∧
    ((run dirtyTop [0,15,0]) 1).rail = .x ∧
    (∀ i, ((run dirtyTop [0,15,0]) i).rail ≠ .di) ∧
    ((run blank [0,15,0]) 1).rail = .di := by
  unfold MCOV COV
  decide

/-- At a payable top, servicing an already-present upward worker does
not turn it. P3 transfers the mark and then M sends the worker left.
This is a dirty guard control, not a reachable first-adjacency claim. -/
theorem paid_already_top_counter : MCOV paidAtTop ∧ COV paidAtTop ∧
    (∀ i : Fin 16, i ≠ 15 → (paidAtTop i).stock = false) ∧
    geometricPay (paidAtTop 15) (paidAtTop 0) = true ∧
    ((step paidAtTop 15) 15).rail = .ui ∧
    ((step paidAtTop 15) 0).mark = true ∧
    (∀ i, ((step paidAtTop 15) i).rail ≠ .di) ∧
    (∀ i, ((step paidAtTop 15) i).leader = false) := by
  unfold MCOV COV
  decide

def paidAdjacent : Config 2 12 16 := fun i =>
  {blank i with stock := i.val == 15}

theorem paid_adjacent_releases : MCOV paidAdjacent ∧ COV paidAdjacent ∧
    (∀ i : Fin 16, i ≠ 15 → (paidAdjacent i).stock = false) ∧
    ((run paidAdjacent [15]) 0).mark = true ∧
    ((run paidAdjacent [15,0]) 1).rail = .di ∧
    ((run paidAdjacent [15,0,1]) 2).rail = .di ∧
    (∀ i, ((run paidAdjacent [15,0,1]) i).stock = false) ∧
    (∀ i, ((run paidAdjacent [15,0,1]) i).leader = false) := by
  unfold MCOV COV
  decide

/-- At a marked incoming edge an empty ghost receiver cannot receive
stock, even when its predecessor was full. An actual paid advance also
leaves the predecessor empty, so a further advance needs a refill. -/
theorem marked_paid_empty {p c : Nat} (u v : Site p c)
    (hm : u.mark = true) (hv : v.stock = false)
    (hp : geometricPay u v = true) :
    (pairStep u v).1.stock = false ∧ (pairStep u v).2.stock = false :=
  ⟨RearFrontStock.paid_donor_empty u v hp,
   (RearFrontStock.marked_right_stock u v hm).trans hv⟩

/-- An empty pair with nonliving initiator remains empty through all
patrol bytes. This includes the edge into the adjacent empty target ghost. -/
theorem unstocked_nonleader_pair {p c : Nat} (u v : Site p c)
    (hu : u.leader = false) (hs : u.stock = false) (ht : v.stock = false) :
    (pairStep u v).1.stock = false ∧ (pairStep u v).2.stock = false := by
  have h := RearFrontStock.pair_stock_le_of_nonleader u v hu
  cases h1 : (pairStep u v).1.stock <;> cases h2 : (pairStep u v).2.stock <;>
    simp_all [RearFrontStock.stockBit]

end L4.WindowA0Rows

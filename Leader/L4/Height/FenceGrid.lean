import Leader.L4.Height.FenceCrossings

namespace L4.Height.FenceGrid
open FenceCrossings FenceComparison

/-- A predicate at a crossing can differ from its predicates at the two
predecessors. Each cut is on the same real candidate tape. -/
inductive Cert {n : Nat} : Tree n → (List (Fin n) → Prop) → Prop
  | already {G} (done : ∀ w,G w) : Cert .paid G
  | joint {l r A B G} (e : Fin n) (left : Cert l A) (right : Cert r B)
      (step : ∀ a b c, A a → B a → G (a++e::(b++e::c))) : Cert (.node e l r) G

theorem cert_done {n : Nat} (t : Tree n) (G : List (Fin n) → Prop) (proof : Cert t G)
    (w : List (Fin n)) (clear : ∀ p∈paths t,p.Sublist w) : G w := by
  let F := fun (v : Tree n) (a : List (Fin n)) => ∀ H, Cert v H → H a
  have leaf (a : List (Fin n)) : F .paid a := by
    intro H h
    cases h with
    | already done => exact done a
  have step (e : Fin n) (l r : Tree n) (a b c : List (Fin n))
      (L : F l a) (R : F r a) : F (.node e l r) (a++e::(b++e::c)) := by
    intro H h
    cases h with
    | joint _ left right cross => exact cross a b c (L _ left) (R _ right)
  exact forces F leaf step t w clear G proof

/-- C(w,k) counts occupied sites among the first k in travel order.
Whenever its two neighbours have paid, two candidate hits clear the
current level. The exit has no downstream prerequisite. -/
structure Line (n h : Nat) where
  bond : Nat → Fin n
  C : List (Fin n) → Nat → Nat
  limit : ∀ a k, C a k≤k
  paid : ∀ k j, 0<j → j≤k → k≤h → ∀ a b c,
    C a (k-1)<j → (k<h → C a (k+1)≤j) →
    C (a++bond k::(b++bond k::c)) k<j

/-- Distance on the two-predecessor grid. The upstream cut keeps the
level and decreases k. The downstream cut increases both k and j. -/
def grid {n h : Nat} (F : Line n h) : Nat → Nat → Nat → Tree n
  | 0,_,_ => .paid
  | fuel+1,k,j => .node (F.bond k)
      (if j<k then grid F fuel (k-1) j else .paid)
      (if k<h then grid F fuel (k+1) (j+1) else .paid)

private theorem grid_depth {n h : Nat} (F : Line n h) (fuel k j : Nat) :
    height (grid F fuel k j) ≤ fuel := by
  induction fuel generalizing k j with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    simp only [grid,height]
    have l := ih (k-1) j
    have r := ih (k+1) (j+1)
    split <;> split <;> simp [height] <;> omega

theorem grid_cert {n h : Nat} (F : Line n h) (fuel k j : Nat)
    (hj : 0<j) (hjk : j≤k) (hk : k≤h) (budget : h+k+1-2*j≤fuel) :
    Cert (grid F fuel k j) (fun a => F.C a k<j) := by
  induction fuel generalizing k j with
  | zero =>
    by_cases reached : k=j ∧ k=h
    · obtain ⟨rfl,rfl⟩ := reached
      omega
    · omega
  | succ fuel ih =>
    let P := fun a => F.C a (k-1)<j
    let Q := fun a => k<h → F.C a (k+1)≤j
    have L : Cert (if j<k then grid F fuel (k-1) j else .paid) P := by
      split
      next h₁ => exact ih _ _ hj (by omega) (by omega) (by omega)
      next h₁ =>
        exact .already (fun a => by have := F.limit a (k-1); dsimp [P]; omega)
    by_cases next : k<h
    · have right := ih (k+1) (j+1) (by omega) (by omega) (by omega) (by omega)
      simp only [grid,if_pos next]
      exact .joint (F.bond k) L right (fun a b c l r => F.paid k j hj hjk hk a b c l (fun _ => by omega))
    · have right : Cert .paid Q := .already (fun _ h₁ => (next h₁).elim)
      simp only [grid,if_neg next]
      exact .joint (F.bond k) L right (F.paid k j hj hjk hk)

def root {n h : Nat} (F : Line n h) := grid F (2*h-1) h 1

theorem root_clears {n h : Nat} (hh : 0<h) (F : Line n h) (w : List (Fin n))
    (matched : ∀ p∈paths (root F),p.Sublist w) : F.C w h=0 := by
  have G := grid_cert F (2*h-1) h 1 (by decide) hh (Nat.le_refl _) (by omega)
  have H : F.C w h<1 := cert_done _ _ G w matched
  omega

theorem root_size {n h : Nat} (F : Line n h) :
    (paths (root F)).length≤2^(2*h-1) ∧ ∀ p∈paths (root F),p.length≤2*(2*h-1) := by
  have h := grid_depth F (2*h-1) h 1
  obtain ⟨sz,len⟩ := path_size (root F)
  exact ⟨Nat.le_trans sz (Nat.pow_le_pow_right (by decide) h),
    fun p mem => Nat.le_trans (len p mem) (Nat.mul_le_mul_left 2 h)⟩

#print axioms root_clears
#print axioms root_size
end L4.Height.FenceGrid

import Leader.L4.Height.FenceComparison

namespace L4.Height.FenceCrossings
open FenceComparison FencePathPotential

/-- The same two final occurrences serve every predecessor path. -/
private theorem last_mark {n : Nat} (e : Fin n) (w : List (Fin n)) (h : e∈w) :
    ∃ a b,w=a++e::b ∧ e∉b := by
  induction w with
  | nil => simp at h
  | cons f w ih =>
    by_cases later : e∈w
    · obtain ⟨a,b,eq,N⟩ := ih later
      exact ⟨f::a,b,congrArg (List.cons f) eq,N⟩
    · have same := (List.mem_cons.mp h).resolve_right later
      subst f
      exact ⟨[],w,rfl,later⟩

private theorem strip_last {n : Nat} (e : Fin n) (a b p : List (Fin n)) (N : e∉b)
    (h : (p++[e]).Sublist (a++e::b)) : p.Sublist a := by
  induction a generalizing p with
  | nil =>
    cases p with
    | nil => exact List.Sublist.slnil
    | cons f p =>
      rcases List.sublist_cons_iff.mp h with skip|⟨u,eq,sub⟩
      · exact (N (skip.subset (by simp))).elim
      · have tail : p++[e]=u := (List.cons.inj eq).2
        exact (N (sub.subset (tail ▸ (by simp : e∈p++[e])))).elim
  | cons f a ih =>
    cases p with
    | nil => exact List.nil_sublist _
    | cons j p =>
      rcases List.sublist_cons_iff.mp h with skip|⟨u,eq,sub⟩
      · exact (ih _ skip).cons f
      · have heads : j=f := (List.cons.inj eq).1
        have tail : p++[e]=u := (List.cons.inj eq).2
        subst j
        exact (ih p (tail.symm ▸ sub)).cons_cons f

/-- Each node pays its predecessors and then its own bond twice. The leaf
stands for a crossing already satisfied at the start of the comparison. -/
inductive Tree (n : Nat)
  | paid
  | node (e : Fin n) (left right : Tree n)

def paths {n : Nat} : Tree n → List (List (Fin n))
  | .paid => [[]]
  | .node e l r => (paths l++paths r).map (fun p => p++[e,e])

def height {n : Nat} : Tree n → Nat
  | .paid => 0
  | .node _ l r => max (height l) (height r)+1

private theorem paths_nonempty {n : Nat} (t : Tree n) : ∃ p,p∈paths t := by
  induction t with
  | paid => exact ⟨[],by simp [paths]⟩
  | node e l r hl _ =>
    obtain ⟨p,h⟩ := hl
    exact ⟨p++[e,e],List.mem_map.mpr ⟨p,List.mem_append_left _ h,rfl⟩⟩

theorem path_size {n : Nat} (t : Tree n) :
    (paths t).length≤2^height t ∧ ∀ p ∈ paths t,p.length≤2*height t := by
  induction t with
  | paid => simp [paths,height]
  | node e l r hl hr =>
    have L := Nat.pow_le_pow_right (n:=2) (by decide) (Nat.le_max_left (height l) (height r))
    have R := Nat.pow_le_pow_right (n:=2) (by decide) (Nat.le_max_right (height l) (height r))
    obtain ⟨a,b⟩ := hl
    obtain ⟨c,d⟩ := hr
    constructor
    · simp only [paths,List.length_map,List.length_append,height,Nat.pow_succ]
      omega
    · intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      rcases List.mem_append.mp hq with h|h
      · have := b q h
        simp [height]
        omega
      · have := d q h
        simp [height]
        omega

/-- Completion of the path family forces each crossing using only its local
law after both predecessors have cleared. The common cut is immediately
before the penultimate occurrence of this node's bond on the actual tape. -/
theorem forces {n : Nat} (goal : Tree n → List (Fin n) → Prop)
    (leaf : ∀ w,goal .paid w)
    (cross : ∀ e l r a b c,goal l a → goal r a →
      goal (.node e l r) (a++e::(b++e::c)))
    (t : Tree n) (w : List (Fin n)) (h : ∀ p ∈ paths t,p.Sublist w) : goal t w := by
  induction t generalizing w with
  | paid => exact leaf w
  | node e l r il ir =>
    have all (p : List (Fin n)) (mem : p∈paths l++paths r) :
        ((p++[e])++[e]).Sublist w := by
      simpa only [List.append_assoc,List.singleton_append] using
        h (p++[e,e]) (List.mem_map.mpr ⟨p,mem,rfl⟩)
    obtain ⟨p,hp⟩ := paths_nonempty l
    have M := all p (List.mem_append_left _ hp)
    obtain ⟨u,c,eq,nc⟩ := last_mark e w (M.subset (by simp))
    subst w
    have once (q : List (Fin n)) (hq : q∈paths l++paths r) :=
      strip_last e u c (q++[e]) nc (all q hq)
    obtain ⟨a,b,eq,nb⟩ := last_mark e u ((once p (List.mem_append_left _ hp)).subset (by simp))
    subst u
    have twice (q : List (Fin n)) (hq : q∈paths l++paths r) := strip_last e a b q nb (once q hq)
    simpa only [List.append_assoc,List.cons_append] using
      cross e l r a b c (il a (fun q hq => twice q (List.mem_append_left _ hq)))
        (ir a (fun q hq => twice q (List.mem_append_right _ hq)))

private theorem matched {n : Nat} (p a : List (Fin n)) (clear : unpaid p a=[]) : p.Sublist a := by
  induction a generalizing p with
  | nil =>
    change p=[] at clear
    subst p
    exact List.Sublist.slnil
  | cons e a ih =>
    cases p with
    | nil => exact List.nil_sublist _
    | cons f p =>
      change unpaid (dropMark e (f::p)) a=[] at clear
      by_cases h : e=f
      · subst e
        exact (ih p (by simpa [dropMark] using clear)).cons_cons f
      · exact (ih _ (by simpa [dropMark,h] using clear)).cons e

theorem matched_of_clear {n : Nat} (p : List (List (Fin n))) (a : List (Fin n))
    (clear : load p a=0) : ∀ q ∈ p,q.Sublist a := by
  induction p with
  | nil => simp
  | cons f p ih =>
    change weight (unpaid f a).length+load p a=0 at clear
    have empty : unpaid f a=[] := by
      cases h : unpaid f a with
      | nil => rfl
      | cons e w => simp [h,weight] at clear
    intro q hq
    rcases List.mem_cons.mp hq with rfl|h
    · exact matched _ a empty
    · exact ih (by omega) q h

end L4.Height.FenceCrossings

import Leader.L4.BStarFenceLineGeometry

/-! Same-emitted-mark occupancy for directed open exclusion. The
ports are labels in the full raw alphabet, not a filtered edge clock.
Both lanes may use the same mark (on disjoint typed cells). -/
namespace L4.BStarFenceShadow

def succIdx {k : Nat} (j : Fin k) (h : j.val+1<k) : Fin k := ⟨j.val+1,h⟩
def predIdx {k : Nat} (j : Fin k) (h : 0<j.val) : Fin k := ⟨j.val-1,by omega⟩

/-- One shadow update driven by the actual emitted argument. Injective
ports within a line ensure a mark cannot hit two bonds of that line. -/
def update {n k : Nat} (port : Fin k → Fin n) (e : Fin n)
    (z : Fin k → Bool) (j : Fin k) : Bool :=
  if e=port j then
    if h : j.val+1<k then z j && z (succIdx j h) else false
  else if h : 0<j.val then
    if e=port (predIdx j h) then z (predIdx j h) || z j else z j
  else z j

def Below {k : Nat} (x z : Fin k→Bool) : Prop := ∀ j,x j=true→z j=true

/-- Local clauses needed at one real old-pair mark. The overlap is
intentionally excluded only within this line, not between lines. -/
structure Mark {n k : Nat} (port : Fin k→Fin n) (e : Fin n)
    (x y : Fin k→Bool) : Prop where
  hop : ∀ j (h : j.val+1<k), e=port j →
    (y j=true→(x j && x (succIdx j h))=true) ∧
    (y (succIdx j h)=true→(x j || x (succIdx j h))=true)
  outlet : ∀ j, ¬j.val+1<k → e=port j → y j=false
  quiet : ∀ j, e≠port j → (∀ h : 0<j.val,e≠port (predIdx j h)) → y j=x j

theorem mark_below {n k : Nat} (port : Fin k→Fin n) (e : Fin n)
    {x y z : Fin k→Bool} (M : Mark port e x y) (B : Below x z) :
    Below y (update port e z) := by
  intro j hy
  unfold update
  split
  · next H =>
    split
    · next h =>
      obtain ⟨H1,H2⟩ := Bool.and_eq_true_iff.mp ((M.hop j h H).1 hy)
      exact Bool.and_eq_true_iff.mpr ⟨B j H1,B _ H2⟩
    · next h =>
      rw [M.outlet j h H] at hy
      contradiction
  · next H =>
    split
    · next h =>
      split
      · next E =>
        have sr : (predIdx j h).val+1<k := by
          change j.val-1+1<k
          have := j.isLt
          omega
        have eq : succIdx (predIdx j h) sr=j := Fin.ext (by
          change j.val-1+1=j.val
          omega)
        have Q := (M.hop (predIdx j h) sr E).2
        rw [eq] at Q
        exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp (Q hy)).imp (B _) (B j))
      · next E =>
        exact B j ((M.quiet j H (fun _ => E)).symm.trans hy)
    · next h =>
      exact B j ((M.quiet j H (fun p => (h p).elim)).symm.trans hy)

structure Two {l r : Nat} where
  left : Fin l→Bool
  right : Fin r→Bool

def Two.below {l r : Nat} (x z : Two (l:=l) (r:=r)) : Prop :=
  Below x.left z.left ∧ Below x.right z.right

def Two.advance {n l r : Nat} (L : Fin l→Fin n) (R : Fin r→Fin n)
    (e : Fin n) (z : Two (l:=l) (r:=r)) : Two (l:=l) (r:=r) :=
  ⟨update L e z.left,update R e z.right⟩

theorem same_emitted {n l r : Nat} (L : Fin l→Fin n) (R : Fin r→Fin n)
    (e : Fin n) {x y z : Two (l:=l) (r:=r)}
    (A : Mark L e x.left y.left) (B : Mark R e x.right y.right)
    (h : x.below z) : y.below (Two.advance L R e z) :=
  ⟨mark_below L e A h.1,mark_below R e B h.2⟩

/-- Integrate over an arbitrary candidate word. The augmented physical
state can store the full predictable prefix. Stop before invoking the
one-mark premise once the paid FENCE phase is over. -/
def sweep {S : Type} {n l r : Nat} (L : Fin l→Fin n) (R : Fin r→Fin n)
    (step : S→Fin n→S) (emit : S→Fin n→Fin n) (active : S→Bool) :
    S → Two (l:=l) (r:=r) → List (Fin n) → S × Two (l:=l) (r:=r)
  | s,z,[] => (s,z)
  | s,z,e::w => if active s then
      sweep L R step emit active (step s e) (Two.advance L R (emit s e) z) w
    else (s,z)

theorem sweep_below {S : Type} {n l r : Nat} (L : Fin l→Fin n) (R : Fin r→Fin n)
    (step : S→Fin n→S) (emit : S→Fin n→Fin n) (active : S→Bool)
    (P : S→Prop) (phys : S→Two (l:=l) (r:=r))
    (closed : ∀ s e,P s→active s=true→P (step s e))
    (one : ∀ s e,P s→active s=true→
      Mark L (emit s e) (phys s).left (phys (step s e)).left ∧
      Mark R (emit s e) (phys s).right (phys (step s e)).right)
    (w : List (Fin n)) (s : S) (z : Two (l:=l) (r:=r))
    (h : P s) (dom : (phys s).below z) :
    let t := sweep L R step emit active s z w
    P t.1 ∧ (phys t.1).below t.2 := by
  induction w generalizing s z with
  | nil => exact ⟨h,dom⟩
  | cons e w ih =>
    simp only [sweep]
    split
    · next act =>
      exact ih _ _ (closed s e h act)
        (same_emitted L R (emit s e) (one s e h act).1 (one s e h act).2 dom)
    · exact ⟨h,dom⟩

end L4.BStarFenceShadow

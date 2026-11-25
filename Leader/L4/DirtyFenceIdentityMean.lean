import Leader.L4.BStarFenceEscrowMonitor

namespace L4.DirtyFenceIdentityMean
open L4.Height BStarFenceShadow BStarFenceSweepClock
variable {S : Type} {n l r : Nat}

private theorem emit_identity (a w : List (Fin n)) :
    BStarSteeredLikelihood.emit (fun _ e => e) a w = w := by
  induction w generalizing a with
  | nil => rfl
  | cons e w ih =>
    change e :: BStarSteeredLikelihood.emit (fun _ q => q) (a++[e]) w = e::w
    rw [ih]

private theorem emitted_identity (next : S→Fin n→S) (s : S) (w : List (Fin n)) :
    emitted next (fun _ e=>e) s w=w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih =>
    change e::emitted next (fun _ q=>q) (next s e) w=e::w
    rw [ih]

/-- The two-line clearance theorem specialized to an unchanged IID
raw tape. The caller supplies the exact all-mark occupancy comparison;
there is no generated-opcode or mark-redirection hypothesis here. -/
theorem identity_stopped_expected
    (hn : 0<n) (L : Fin l→Fin n) (R : Fin r→Fin n)
    (hl : 0<l) (hr : 0<r)
    (linj : ∀ i j,L i=L j→i=j) (rinj : ∀ i j,R i=R j→i=j)
    (next : S→Fin n→S) (active : S→Bool) (P : S→Prop)
    (phys : S→Two (l:=l) (r:=r))
    (closed : ∀ s e,P s→active s=true→P (next s e))
    (one : ∀ s e,P s→active s=true→
      Mark L e (phys s).left (phys (next s e)).left ∧
      Mark R e (phys s).right (phys (next s e)).right)
    (s : S) (init : P s) :
    Height.IIDExpectedHittingTimeAtMost next (Done active phys) s (92*n*max l r) := by
  intro t
  have bound := physical_stopped_mean hn L R hl hr linj rinj
    (fun _ e=>e) [] (fun b e u v _=>by
      rw [emit_identity]
      exact List.mem_append_right _ (List.mem_cons_self))
    next (fun _ e=>e) active P phys closed one s init t
    (fun w=>(emitted_identity next s w).trans (emit_identity [] w).symm)
  rw [BStarFenceEscrowMonitor.cost_eq_wordSum]
  have E : Thru.wordSum (Thru.wait next (Done active phys) s) t =
      Thru.wordSum (actual next active phys s t) t := by
    apply Thru.wordSum_congr_length
    intro w len
    unfold actual
    exact (Nat.min_eq_right (len ▸ Thru.wait_le_length next _ s w)).symm
  rwa [E]

#print axioms identity_stopped_expected
end L4.DirtyFenceIdentityMean

import Leader.L4.WindowScopedRace
import Leader.L4.TripleDummyWait

namespace L4.WindowScopedDummy
open WindowScopedRace WindowLocal BarrierIID TriplePhase TripleBoundary TripleVulnerable
open TripleDummyWait (phaseValue)

def entered {p c n : Nat} (x : WindowScopedRace.State p c n) : Prop :=
  x.exited=true ∨ x.right=.forward .dummy 0

def value {p c n : Nat} (b : Nat) (x : WindowScopedRace.State p c n) : Nat :=
  if x.exited then 0 else phaseValue b x.right

private theorem value_row {p c n : Nat} (group cert : List (Fin n)) (v : Fin n)
    (a b : Nat) (x : WindowScopedRace.State p c n) (e : Fin n) (hs : x.exited=false) :
    value b (WindowScopedRace.next group cert v a b x e) =
      if (decide (route group cert none x.ledger e ≠ Event.keep) : Bool)
      then 0 else phaseValue b (x.right.tick (liftedSite v (a+1)) b e) := by
  simp [value,WindowScopedRace.next,hs]

private theorem es_mono {n : Nat} (f g : Fin n → Int) (h : ∀ e, f e≤g e) :
    edgeSum f≤edgeSum g := by
  induction n with
  | zero => exact Int.le_refl _
  | succ n ih =>
    simp only [edgeSum,List.ofFn_succ,List.sum_cons] at *
    exact Int.add_le_add (h 0) (ih _ _ (fun j => h j.succ))

private theorem es_add {n : Nat} (f g : Fin n → Int) :
    edgeSum (fun e => f e+g e)=edgeSum f+edgeSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [edgeSum,List.ofFn_succ,List.sum_cons] at *
    rw [ih]
    omega

private theorem value_fwd (b q : Nat) (k : Kind)
    (hi : k≠.dummy ∨ q≠0) : phaseValue b (.forward k q)=2*b+2+(2*b+1-q) := by
  cases k <;> cases q <;> simp_all [phaseValue]

private theorem ready_drift {p c n : Nat} (group cert : List (Fin n)) (s : Fin n) (a b : Nat) (x : WindowScopedRace.State p c n)
    (hp : Paired x.ledger.config s a b x.left x.right)
    (hx : x.right=.ready) (hs : x.exited=false) (hb : 0<b) :
    1≤edgeSum (fun e => (value b x:Int) - (value b (WindowScopedRace.next group cert s a b x e):Int)) := by
  let l := liftedSite s a
  let r := liftedSite s (a+1)
  have hne : l≠r := by
    intro he
    have he' := liftedSite_inj s (i:=a) (j:=a+1) (by have := hp.geom.at_least_two; omega)
      hp.geom.at_least_two he
    omega
  have pred (e : Fin n) : rightNeighbor e=r ↔ e=l := by
    have H : rightNeighbor l=r := (liftedSite_succ s a).symm
    rw [←H]
    exact ⟨FreshSeparation.succ_inj,congrArg rightNeighbor⟩
  let f := fun e : Fin n => (if e=l then (2*b+2:Int) else 0)+(if e=r then -(2*b:Int) else 0)
  have hsum : edgeSum f=2 := by
    unfold f
    rw [es_add,edgeSum_selector,edgeSum_selector]
    omega
  suffices h : edgeSum f≤edgeSum (fun e => (value b x:Int) - (value b (WindowScopedRace.next group cert s a b x e):Int)) by omega
  apply es_mono
  intro e
  rw [value_row group cert s a b x e hs]
  simp only [value,hs,Bool.false_eq_true,if_false,hx,phaseValue]
  by_cases hl : e=l
  · have hP : rightNeighbor l=r := (pred l).2 rfl
    change _ ≤ (2*b+2:Int) - Int.ofNat (if (decide (route group cert none x.ledger e ≠ Event.keep) : Bool) then 0 else
      phaseValue b (Phase.tick r b .ready e))
    simp [f,hl,hne,Phase.tick,hP,phaseValue]
  by_cases hr : e=r
  · change _ ≤ (2*b+2:Int) - Int.ofNat (if (decide (route group cert none x.ledger e ≠ Event.keep) : Bool) then 0 else
      phaseValue b (Phase.tick r b .ready e))
    cases hs' : (decide (route group cert none x.ledger r ≠ Event.keep) : Bool) <;>
      simp [f,hr,hne.symm,hs',Phase.tick,Nat.ne_of_gt hb,phaseValue] <;> omega
  · have hP : ¬rightNeighbor e=r := fun h => hl ((pred e).1 h)
    change _ ≤ (2*b+2:Int) - Int.ofNat (if (decide (route group cert none x.ledger e ≠ Event.keep) : Bool) then 0 else
      phaseValue b (Phase.tick r b .ready e))
    cases hs' : (decide (route group cert none x.ledger e ≠ Event.keep) : Bool) <;>
      simp [f,hl,hr,Phase.tick,hP,phaseValue] <;> omega

private theorem forward_drift {p c n : Nat} (group cert : List (Fin n)) (s : Fin n) (a b : Nat) (x : WindowScopedRace.State p c n)
    (hp : Paired x.ledger.config s a b x.left x.right) (k : Kind) (q : Nat)
    (hx : x.right=.forward k q) (hs : x.exited=false) (hb : 0<b)
    (he : k≠.dummy ∨ q≠0) :
    1≤edgeSum (fun e => (value b x:Int) - (value b (WindowScopedRace.next group cert s a b x e):Int)) := by
  let r := liftedSite s (a+1)
  let d := liftedSite r q
  have ht := hp.target
  rw [hx] at ht
  have hq := ht.within
  have hsum : edgeSum (fun e => if e=d then (1:Int) else 0)=1 := edgeSum_selector _ _
  suffices h : edgeSum (fun e => if e=d then (1:Int) else 0)≤
      edgeSum (fun e => (value b x:Int) - (value b (WindowScopedRace.next group cert s a b x e):Int)) by omega
  apply es_mono
  intro e
  rw [value_row group cert s a b x e hs]
  simp only [value,hs,Bool.false_eq_true,if_false,hx,value_fwd b q k he]
  by_cases h : e=d
  · change _ ≤ _ - Int.ofNat (if (decide (route group cert none x.ledger e ≠ Event.keep) : Bool) then 0 else phaseValue b
      (Phase.tick r b (.forward k q) e))
    by_cases qlt : q<b
    · simp [h,d,Phase.tick,qlt,value_fwd b (q+1) k (Or.inr (by omega))]
      split <;> omega
    · simp [h,d,Phase.tick,qlt,Nat.ne_of_gt hb,phaseValue]
      split <;> omega
  · change _ ≤ _ - Int.ofNat (if (decide (route group cert none x.ledger e ≠ Event.keep) : Bool) then 0 else phaseValue b
      (Phase.tick r b (.forward k q) e))
    simp [h,Phase.tick,show e≠liftedSite r q from h,value_fwd b q k he]
    split <;> omega

private theorem return_drift {p c n : Nat} (group cert : List (Fin n)) (s : Fin n) (a b : Nat) (x : WindowScopedRace.State p c n)
    (k : Kind) (q : Nat) (hx : x.right=.returning k q) (hs : x.exited=false) :
    1≤edgeSum (fun e => (value b x:Int) - (value b (WindowScopedRace.next group cert s a b x e):Int)) := by
  let r := liftedSite s (a+1)
  let d := liftedSite r q
  have hsum : edgeSum (fun e => if e=d then (1:Int) else 0)=1 := edgeSum_selector _ _
  suffices h : edgeSum (fun e => if e=d then (1:Int) else 0)≤
      edgeSum (fun e => (value b x:Int) - (value b (WindowScopedRace.next group cert s a b x e):Int)) by omega
  apply es_mono
  intro e
  rw [value_row group cert s a b x e hs]
  simp only [value,hs,Bool.false_eq_true,if_false,hx,phaseValue]
  by_cases h : e=d
  · change _ ≤ _ - Int.ofNat (if (decide (route group cert none x.ledger e ≠ Event.keep) : Bool) then 0 else phaseValue b
      (Phase.tick r b (.returning k q) e))
    by_cases h0 : q=0
    · simp [h,d,Phase.tick,h0,phaseValue]
      split <;> omega
    · simp [h,d,Phase.tick,h0,phaseValue]
      split <;> omega
  · change _ ≤ _ - Int.ofNat (if (decide (route group cert none x.ledger e ≠ Event.keep) : Bool) then 0 else phaseValue b
      (Phase.tick r b (.returning k q) e))
    simp [h,Phase.tick,show e≠liftedSite r q from h,phaseValue]
    split <;> omega

/-- Reach a fresh target dummy, or the actual scoped exit, with all
outside marks still applied to the full tagged ledger. -/
theorem mean {p c n a b : Nat} {initial : Config p c n} {group cert : List (Fin n)}
    {v : Fin n} (C : Context initial group cert v a b) (hb : 0<b)
    (x : WindowScopedRace.State p c n) (hG : C.Good x) :
    IIDExpectedHittingTimeAtMost (WindowScopedRace.next group cert v a b) entered x (n*(4*b+3)) := by
  have calcMean := TripleControlled.mean_of_potential (WindowScopedRace.next group cert v a b) entered
    C.Good (value b) (fun y e hy _ => C.good_step y e hy)
    (by
      intro z hz hno
      have hs := Bool.eq_false_iff.mpr (fun h => hno (Or.inl h))
      have hp := ((hz.resolve_left (fun h => hno (Or.inl h))).2.paired C.size)
      cases hx : z.right with
      | ready => exact ready_drift group cert v a b z hp hx hs hb
      | forward k q =>
        have he : k≠.dummy ∨ q≠0 := by
          by_cases hk : k=.dummy
          · exact Or.inr (fun hq => hno (Or.inr (by simp [hx,hk,hq])))
          · exact Or.inl hk
        exact forward_drift group cert v a b z hp k q hx hs hb he
      | returning k q => exact return_drift group cert v a b z k q hx hs)
    x hG
  have cap : value b x≤4*b+3 := by
    by_cases hs : x.exited=true
    · simp [value,hs]
    have hF := Bool.eq_false_iff.mpr hs
    have hp := ((hG.resolve_left hs).2.paired C.size)
    cases hx : x.right with
    | ready => simp [value,hF,hx,phaseValue]; omega
    | forward k q =>
      cases k <;> cases q <;> simp [value,hF,hx,phaseValue] <;> omega
    | returning k q =>
      have ht := hp.target
      rw [hx] at ht
      have hq := ht.1.le
      simp [value,hF,hx,phaseValue]
      omega
  exact TripleRenewal.expected_mono calcMean (Nat.mul_le_mul_left _ cap)

end L4.WindowScopedDummy

#print axioms L4.WindowScopedDummy.mean

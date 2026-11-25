import Leader.L4.WindowProtectedEntry

/-! A once-only jump from an arbitrary pre-protection observer to the
authenticated, literal G7 protected monitor. -/
namespace L4.WindowProtectedOuter
open SevenTagCharge WindowProtectedMass RankRenewal TaggedTail Classical

structure Entry {p c n : Nat} (z0 : Config p c n) (group : List (Fin n)) where
  supplier : Fin n
  victim : Fin n
  donor : Nat
  ledger : Ledger p c n
  inGroup : victim ∈ group
  auth : Authenticated z0 supplier victim donor ⟨ledger,[]⟩

structure Running {p c n : Nat} (z0 : Config p c n) (group : List (Fin n)) where
  start : Entry z0 group
  q : WindowProtectedMass.State p c n

def startRunning {p c n : Nat} {z0 : Config p c n} {group : List (Fin n)}
    (e : Entry z0 group) : Running z0 group :=
  ⟨e,initial e.ledger e.donor⟩

def pushNext {p c n : Nat} {z0 : Config p c n} {group : List (Fin n)}
    (r : Running z0 group) (e : Fin n) : Running z0 group :=
  { r with q := next r.start.supplier group (someSupplier r.start) r.start.victim r.q e }
where
  -- Only the named supplier's tag may cause a prefix-death exit.
  someSupplier (x : Entry z0 group) : List (Fin n) :=
    (x.ledger.slots (RearTrace.predecessor x.supplier)).toList

def joinedNext {α : Type} {p c n : Nat} {z0 : Config p c n} {group : List (Fin n)}
    (front : α → Fin n → Sum α (Entry z0 group)) :
    Sum α (Running z0 group) → Fin n → Sum α (Running z0 group)
  | .inl s, e => (front s e).map id startRunning
  | .inr p, e => .inr (pushNext p e)

def bad {α : Type} {p c n : Nat} {z0 : Config p c n} {group : List (Fin n)} :
    Sum α (Running z0 group) → Prop
  | .inl _ => False
  | .inr r => failed r.q

private theorem sum_le {n : Nat} {f g : Fin n→Nat} (h : ∀ e, f e≤g e) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))

private theorem sum_const (n z : Nat) : sumEdge (fun _ : Fin n => z)=n*z := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.succ_mul,Nat.add_comm]

private theorem sum_scale {n : Nat} (A : Nat) (f : Fin n→Nat) :
    sumEdge (fun e => A*f e)=A*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.mul_add]

private theorem inr_mass {α : Type} {p c n : Nat} {z0 : Config p c n} {group : List (Fin n)}
    (front : α → Fin n → Sum α (Entry z0 group)) (t : Nat) (q : Running z0 group) :
    endpointSum (joinedNext front) (fun x => if bad x then 1 else 0) t (.inr q) =
    endpointSum (next q.start.supplier group (pushNext.someSupplier q.start) q.start.victim)
      (fun x => if failed x then 1 else 0) t q.q := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih =>
    simp only [endpointSum]
    apply congrArg sumEdge
    funext e
    exact ih (pushNext q e)

/-- No factor for the time or identity of the unique named kill. A
front observer runs on the original labels and must supply a certified
entry at its cut (or never enter). After entering, this monitor cannot
reset the protected trial or condition on its eventual duration. -/
theorem outer_failure_mass {α : Type} {p c n : Nat} {z0 : Config p c n} {group : List (Fin n)}
    (hn : 4≤n) (hc : 12≤c) (front : α → Fin n → Sum α (Entry z0 group))
    (t : Nat) (q : α) :
    1000*endpointSum (joinedNext front) (fun x => if bad x then 1 else 0)
      t (.inl q)≤11*n^t := by
  induction t generalizing q with
  | zero => simp [endpointSum,bad]
  | succ t ih =>
    rw [endpointSum,←sum_scale]
    calc
      _ ≤ sumEdge (fun _ : Fin n => 11*n^t) := by
        apply sum_le
        intro e
        cases h : front q e with
        | inl w =>
          change 1000*endpointSum (joinedNext front) _ t ((front q e).map id startRunning)≤_
          rw [h]
          exact ih w
        | inr g =>
          change 1000*endpointSum (joinedNext front) _ t ((front q e).map id startRunning)≤_
          rw [h]
          change 1000*endpointSum (joinedNext front) _ t (.inr (startRunning g))≤_
          rw [inr_mass]
          exact protected_failure_mass hn hc g.supplier group (pushNext.someSupplier g) g.victim
            g.inGroup g.ledger g.auth t
      _ = 11*n^(t+1) := by rw [sum_const,Nat.pow_succ]; ac_rfl

#print axioms outer_failure_mass
end L4.WindowProtectedOuter

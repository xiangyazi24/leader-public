import Leader.L4.ConcreteDebt

/-!
# The predictable rear-root clock
The following observer adds a resident-identity root track and five phase
values to the existing tagged trace. Nothing is added to physical states.
-/

namespace L4.RearTrace
open TaggedTrace

/-- Unwrapped distances are retained as a cumulative count; a backwards
offset is converted to a physical site modulo the ring length. -/
def back {n : Nat} (i : Fin n) (d : Nat) : Fin n := liftedSite i (n-d)

def predecessor {n : Nat} (i : Fin n) : Fin n := back i 1

def rearAt {p c n : Nat} (x : Config p c n) (i : Fin n) : Option (Fin n) :=
  ((List.finRange n).find? (fun k => (x (predecessor (back i k.val))).mark)).map
    (fun k => back i k.val)

inductive Phase
  | initial | initialLeader | ghost | finalLeader | pinned
  deriving DecidableEq, BEq, Repr

structure Observer (p c n : Nat) where
  tag : Obs p c n
  rear : Option (Fin n)
  rearMoves : Nat
  phase : Phase
  rearHits : Nat

/-- Cut sites and counter all refer to the same tagged cover instance. -/
def rearInit {p c n : Nat} (x : Config p c n) (i : Fin n) : Observer p c n :=
  ⟨init x i, rearAt x i, 0, .initial, 0⟩

def outBond {p c n : Nat} (i : Fin n) (s : Observer p c n) : Fin n :=
  s.tag.carrier.getD i

/-- In the moving phase, the incoming rear bond or the refill bond
is nominated according to the donor's premark readiness. -/
def rearBond {p c n : Nat} (i : Fin n) (s : Observer p c n) : Fin n :=
  if s.phase == .ghost then
    match s.rear with
    | none => outBond i s
    | some r =>
      let donor := predecessor r
      if payer (s.tag.config donor) then donor else predecessor donor
  else outBond i s

/-- A resident root is unaffected by an incoming merger into its site.
It advances only on its own incoming bond when that old mark clears. -/
def rearShifts {p c n : Nat} (s : Observer p c n) (e r : Fin n) : Bool :=
  (e == predecessor r) && (s.tag.config e).mark &&
    !(pairStep (s.tag.config e) (s.tag.config (rightNeighbor e))).1.mark

def phaseAfter {p c n : Nat} (s : Observer p c n) (t : Obs p c n)
    (r : Fin n) (moved : Bool) : Phase :=
  if s.phase == .pinned || (moved && s.tag.carrier == s.rear) then .pinned
  else
    match s.phase with
    | .initial =>
      if 2*n ≤ t.moveCount then
        if (t.config r).leader then .initialLeader else .ghost
      else .initial
    | .initialLeader => if (t.config r).leader then .initialLeader else .ghost
    | .ghost => if (t.config r).leader then .finalLeader else .ghost
    | .finalLeader => .finalLeader
    | .pinned => .pinned

/-- Hit on the cut, loss, and birth marks is charged on the PRE-mark phase.
Subsequent rerooting is suppressed after preemption. -/
def rearAdvance {p c n : Nat} (i : Fin n) (s : Observer p c n) (e : Fin n) :
    Observer p c n :=
  let t := advance s.tag e
  let h := s.rearHits + (e == rearBond i s).toNat
  match s.rear with
  | none => { s with tag := t, rearHits := h }
  | some r =>
    let m := !(s.phase == .pinned) && rearShifts s e r
    let r' := if m then rightNeighbor r else r
    ⟨t, some r', s.rearMoves + m.toNat, phaseAfter s t r' m, h⟩

def rearFold {p c n : Nat} (i : Fin n) (s : Observer p c n) :
    List (Fin n) → Observer p c n
  | [] => s
  | e :: w => rearFold i (rearAdvance i s e) w

def rearTrack {p c n : Nat} (x : Config p c n) (i : Fin n) (w : List (Fin n)) :
    Observer p c n := rearFold i (rearInit x i) w

theorem rearAdvance_tag {p c n : Nat} (i : Fin n) (s : Observer p c n) (e : Fin n) :
    (rearAdvance i s e).tag = advance s.tag e := by
  unfold rearAdvance
  split <;> rfl

theorem rearAdvance_hits {p c n : Nat} (i : Fin n) (s : Observer p c n) (e : Fin n) :
    (rearAdvance i s e).rearHits = s.rearHits + (e == rearBond i s).toNat := by
  unfold rearAdvance
  split <;> rfl

theorem rearFold_tag {p c n : Nat} (i : Fin n) (s : Observer p c n) (w : List (Fin n)) :
    (rearFold i s w).tag = track s.tag w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih => rw [rearFold, ih, rearAdvance_tag, track]

theorem rearTrack_tag {p c n : Nat} (x : Config p c n) (i : Fin n) (w : List (Fin n)) :
    (rearTrack x i w).tag = track (init x i) w := rearFold_tag i (rearInit x i) w

theorem rearFold_append {p c n : Nat} (i : Fin n) (s : Observer p c n)
    (a b : List (Fin n)) : rearFold i s (a ++ b) = rearFold i (rearFold i s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons e a ih => exact ih (rearAdvance i s e)

def scaledDebt {p c n : Nat} (s : Observer p c n) : Int :=
  2*(s.tag.outHits : Int) - (s.rearHits : Int)

/-- The exact restart contract on the deterministic observer above. -/
def ConcreteRearDebt : Prop :=
  ∀ {p c n : Nat} (x : Config p c n) (i : Fin n) (w : List (Fin n)),
    LiveCoveredTrace x i w →
    2 * (track (init x i) w).outHits ≤ (rearTrack x i w).rearHits + 12*n + 2

def markDebt {n : Nat} (a b e : Fin n) : Int :=
  (if e = a then 2 else 0) - (if e = b then 1 else 0)

theorem markDebt_range {n : Nat} (a b e : Fin n) :
    -1 ≤ markDebt a b e ∧ markDebt a b e ≤ 2 := by
  unfold markDebt
  split <;> split <;> decide

theorem scaledDebt_step {p c n : Nat} (i e : Fin n) (s : Observer p c n)
    (h : ¬ ended s.tag) :
    scaledDebt (rearAdvance i s e) = scaledDebt s + markDebt (outBond i s) (rearBond i s) e := by
  rw [scaledDebt, rearAdvance_tag, rearAdvance_hits]
  cases hc : s.tag.carrier with
  | none => exact (h hc).elim
  | some b =>
    simp only [scaledDebt, advance, hc, outBond, Option.getD_some, markDebt]
    have count (x y : Fin n) : ((x == y).toNat : Int) = (if x = y then 1 else 0) := by
      by_cases h : x=y
      · subst y; simp
      · simp [h]
    simp only [Int.natCast_add, count]
    by_cases hb : e = b <;> by_cases hr : e = rearBond i s
    all_goals
      first
      | simp only [if_pos hb, if_pos hb.symm, if_pos hr]; omega
      | simp only [if_pos hb, if_pos hb.symm, if_neg hr]; omega
      | simp only [if_neg hb, if_neg (Ne.symm hb), if_pos hr]; omega
      | simp only [if_neg hb, if_neg (Ne.symm hb), if_neg hr]; omega

/-- Combine the four deterministic ledger clauses without returning to
the superseded first-barrier stock budget. -/
theorem debt_of_phase_accounts {n N X Z P M F : Nat}
    (hN : N ≤ 5*n+X) (hReady : 2*X ≤ P+F+1)
    (hStock : F ≤ n+M) (hLand : M ≤ n+1) (hHits : P ≤ Z) :
    2*N ≤ Z + 12*n + 2 := by omega

end L4.RearTrace

#print axioms L4.RearTrace.rearTrack_tag
#print axioms L4.RearTrace.rearFold_append
#print axioms L4.RearTrace.scaledDebt_step
#print axioms L4.RearTrace.debt_of_phase_accounts

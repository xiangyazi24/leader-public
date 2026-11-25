import Leader.L4.RearTrace
import Leader.L4.StockTokenRows

/-! # Empty-departure charges and local donor readiness -/

namespace L4.RearTrace

/-- An unready donor cannot acquire stock or a leader bit on its outgoing
bond. The carrier observer therefore need not charge outgoing service of
this site as a potential refill. -/
theorem unready_initiator {p c : Nat} (u v : Site p c) (h : payer u = false) :
    payer (pairStep u v).1 = false := by
  have hs : u.stock = false := by cases he : u.stock <;> simp_all [payer]
  have hl : u.leader = false := by cases he : u.leader <;> simp_all [payer]
  let rt : Option Unit := if v.stock then some () else none
  have hr : rt.isSome = v.stock := by cases hv : v.stock <;> simp [rt,hv]
  have ht := StockTokenRows.pair_labels u v (none : Option Unit) rt () hs.symm hr
  have hleft : (pairStep u v).1.stock = false := by
    have hm := (congrArg Prod.fst ht).symm
    cases he : StockTokenRows.row u v <;> simpa [he,StockTokenRows.update] using hm
  have hL := (pair_geometric_fields u v).2.1.trans hl
  simp [payer,hleft,hL]

/-- Readiness can be obtained only by service of the site's incoming bond,
including the possibility of receiving a P5 leader bit. -/
theorem unready_off_incoming {p c n : Nat} (x : Config p c n) (i e : Fin n)
    (he : i ≠ rightNeighbor e) (h : payer (x i) = false) :
    payer (step x e i) = false := by
  by_cases h' : i = e
  · subst i
    simpa [step] using unready_initiator (x e) (x (rightNeighbor e)) h
  · simpa [step,h',he] using h

/-- Refill receipts are distinct by construction. An empty departure
leaves an obligation, a refill hits it, and an outstanding obligation
prevents using the next ready advance until that refill occurs. -/
inductive ClockEvent
  | idle | hit | refill | filledAdvance | emptyAdvance
  deriving DecidableEq

structure ClockAccount where
  advances : Nat
  filled : Nat
  hits : Nat
  pending : Bool

def ClockAccount.zero : ClockAccount := ⟨0,0,0,false⟩

def ClockAccount.update (s : ClockAccount) : ClockEvent → ClockAccount
  | .idle => s
  | .hit => {s with hits := s.hits+1}
  | .refill => {s with hits := s.hits+1, pending := false}
  | .filledAdvance => {s with advances := s.advances+1, filled := s.filled+1, hits := s.hits+1}
  | .emptyAdvance => {s with advances := s.advances+1, hits := s.hits+1, pending := true}

def ClockAccount.Allowed (s : ClockAccount) : ClockEvent → Prop
  | .filledAdvance | .emptyAdvance => s.pending = false
  | _ => True

def ClockAccount.Balanced (s : ClockAccount) : Prop :=
  2*s.advances ≤ s.hits+s.filled+s.pending.toNat

theorem clock_oneStep (s : ClockAccount) (e : ClockEvent)
    (h : s.Balanced) (he : s.Allowed e) : (s.update e).Balanced := by
  cases s with
  | mk adv f hit pending =>
    cases pending <;> cases e <;>
      simp_all [ClockAccount.Balanced,ClockAccount.Allowed,ClockAccount.update] <;> omega

inductive ClockTrace : ClockAccount → List ClockEvent → ClockAccount → Prop
  | nil (s) : ClockTrace s [] s
  | cons {s t : ClockAccount} {e : ClockEvent} {w : List ClockEvent}
      (ok : s.Allowed e) (suffix : ClockTrace (s.update e) w t) :
      ClockTrace s (e::w) t

theorem clockTrace_balanced {s t : ClockAccount} {w : List ClockEvent}
    (h : ClockTrace s w t) (hb : s.Balanced) : t.Balanced := by
  induction h with
  | nil => exact hb
  | cons ok _ ih => exact ih (clock_oneStep _ _ hb ok)

theorem count_refills {t : ClockAccount} {w : List ClockEvent}
    (h : ClockTrace ClockAccount.zero w t) :
    2*t.advances ≤ t.hits+t.filled+1 := by
  have h' := clockTrace_balanced h (by change 0 ≤ 0; omega)
  unfold ClockAccount.Balanced at h'
  cases hp : t.pending <;> simp [hp] at h' <;> omega

end L4.RearTrace

#print axioms L4.RearTrace.unready_initiator
#print axioms L4.RearTrace.unready_off_incoming
#print axioms L4.RearTrace.clock_oneStep
#print axioms L4.RearTrace.count_refills

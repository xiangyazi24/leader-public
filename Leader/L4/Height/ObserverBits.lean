import Leader.L4.BStarLapTransfer

/-! Observation bits of the fixed-reference observer. These equations
read the old pair and the ordinary public output before the seed OR. -/
namespace L4.Height.ObserverBits

open BStarLapTransfer AllSizeProtocol

def leftSlot (ref : Bool) (x : BStarLapTransfer.Site) : Nat :=
  if ref then x.b else x.a

def crossing (before ordinary : Pair Bool) : Bool :=
  before.1 && !ordinary.1 && ordinary.2

def commitBit (v : BStarLapTransfer.Site) (rb : Bool) : Bool := rb && (v.pc==2)

def seesLeft (t : Nat) (before ordinary : Pair Bool) (seed : Bool) : Bool :=
  t==3 || before.1 || ordinary.1 || seed

def seesRight (t : Nat) (before ordinary : Pair Bool) : Bool :=
  t==3 || before.2 || ordinary.2

def seesHop (t : Nat) (before ordinary : Pair Bool) (seed : Bool) : Bool :=
  t==3 || before.2 || ordinary.1 || seed || crossing before ordinary

def rightAfter (u v : BStarLapTransfer.Site) (ra rb : Bool)
    (before ordinary : Pair Bool) : BStarLapTransfer.Site :=
  (plan u v ra rb ra rb before ordinary).1.2.site v

def leftAfter (u v : BStarLapTransfer.Site) (ra rb : Bool)
    (before ordinary : Pair Bool) : BStarLapTransfer.Site :=
  (plan u v ra rb ra rb before ordinary).1.1.site u

theorem front_codes {t : Nat} (h : front t=true) : t=2 ∨ t=3 := by
  simpa [front, Bool.or_eq_true] using h

private theorem flag_normal (hit : Bool) : normal 5 (flag hit % 8)=flag hit := by
  cases hit <;> rfl

private theorem front_not_back {t : Nat} (h : front t=true) : back t=false := by
  rcases front_codes h with h|h <;> simp [back,h]

private theorem front_ne_empty {t : Nat} (h : front t=true) : (t==0)=false := by
  rcases front_codes h with h|h <;> simp [h]

private theorem flag_hit_iff (b : Bool) : flag b=3 ↔ b=true := by
  cases b <;> decide

/-- The generated front wins the path overwrite, with a true reading
when the carrier makes the opposite hop on the same physical mark. -/
theorem hop_bit (u v : BStarLapTransfer.Site) (ra rb : Bool)
    (before ordinary : Pair Bool) (h : front v.a=true) :
    leftSlot ra (leftAfter u v ra rb before ordinary)=
      flag (seesHop v.a before ordinary (commitBit v rb)) := by
  cases ra with
  | false =>
    simp [leftAfter, plan, leftSlot, h, seesHop, crossing, commitBit, Writes.site,
      Set.site, flag_normal]
  | true =>
    by_cases issue : (u.pc==0)=true
    · simp [leftAfter, plan, leftSlot, h, seesHop, crossing, commitBit, Writes.site,
        Set.site, flag_normal, issue]
    · by_cases consume : ((u.pc==1) && (back u.a || u.a==0))=true
      · simp [leftAfter, plan, leftSlot, h, seesHop, crossing, commitBit, Writes.site,
          Set.site, flag_normal, issue, consume]
      · simp [leftAfter, plan, leftSlot, h, seesHop, crossing, commitBit, Writes.site,
          Set.site, flag_normal, issue, consume]

/-- A stationary front in the selected left path slot survives when
the old right slot does not send an overwriting front. -/
theorem left_stay_bit (u v : BStarLapTransfer.Site) (ra rb : Bool)
    (before ordinary : Pair Bool) (left : front (leftSlot ra u)=true) (right : front v.a=false) :
    leftSlot ra (leftAfter u v ra rb before ordinary)=
      flag (seesLeft (leftSlot ra u) before ordinary (commitBit v rb)) := by
  cases ra with
  | false =>
    have ft : front u.a=true := left
    have d := front_not_back ft
    have e := front_ne_empty ft
    cases watch : front u.b <;>
      simp [leftAfter, plan, leftSlot, right, ft, d, e, seesLeft, commitBit,
        touched, Writes.site, Set.site, flag_normal, watch]
  | true =>
    have ft : front u.b=true := left
    have d := front_not_back ft
    have e := front_ne_empty ft
    by_cases issue : (u.pc==0)=true
    · simp [leftAfter, plan, leftSlot, right, ft, d, e, seesLeft, commitBit,
        touched, Writes.site, Set.site, flag_normal, issue]
    · by_cases consume : ((u.pc==1) && (back u.a || u.a==0))=true
      · simp [leftAfter, plan, leftSlot, right, ft, d, e, seesLeft, commitBit,
          touched, Writes.site, Set.site, flag_normal, issue, consume]
      · simp [leftAfter, plan, leftSlot, right, ft, d, e, seesLeft, commitBit,
          touched, Writes.site, Set.site, flag_normal, issue, consume]

/-- The terminal observes the old and ordinary post-state marker at
the reference and freezes the bit carried by its departing reply. -/
theorem turn_bit (u v : BStarLapTransfer.Site) (ra : Bool)
    (before ordinary : Pair Bool) (h : front v.b=true) :
    (rightAfter u v ra true before ordinary).b =
      if seesRight v.b before ordinary then 5 else 4 := by
  by_cases pending : (v.pc==2)=true <;>
    simp [rightAfter, plan, h, pending, Writes.site, Set.site, seesRight] <;>
    split <;> decide

/-- An ISSUE launch observes both old and post-mark carriers at the
source while replacing all inherited door bits. -/
theorem launch_bit (u v : BStarLapTransfer.Site) (rb : Bool)
    (before ordinary : Pair Bool) (h : u.pc=0) :
    (leftAfter u v true rb before ordinary).a =
      flag (seesLeft 2 before ordinary (commitBit v rb)) := by
  simp [leftAfter, plan, h, Writes.site, Set.site, flag_normal, seesLeft, commitBit]

/-- A waiting source door is distinct from the selected path's
terminal slot. Its stationary front observes the source bond. -/
theorem door_stay_bit (u v : BStarLapTransfer.Site) (rb : Bool)
    (before ordinary : Pair Bool) (waiting : u.pc=1) (oldFront : front u.a=true) :
    (leftAfter u v true rb before ordinary).a =
      flag (seesLeft u.a before ordinary (commitBit v rb)) := by
  have d := front_not_back oldFront
  have e := front_ne_empty oldFront
  cases watch : front u.b <;> by_cases send : front v.a = true <;>
    by_cases receive : back u.b = true <;>
    simp [leftAfter, plan, waiting, d, e, seesLeft, commitBit,
      touched, oldFront, watch, send, receive, Writes.site, Set.site, flag_normal] <;>
    split <;> simp [Writes.site, Set.site, flag_normal]

theorem front_flag_observed {a : Nat} {hit : Bool} (eq : a=flag hit) :
    (a==3)=true ↔ hit=true := by
  simpa [eq] using flag_hit_iff hit

#print axioms hop_bit
#print axioms left_stay_bit
#print axioms turn_bit
#print axioms launch_bit
#print axioms door_stay_bit
#print axioms front_flag_observed

end L4.Height.ObserverBits

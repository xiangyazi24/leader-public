import Leader.L4.BStarCopyFIFO

/-! The COPY capacity bound starts from cleared destination queues.
It does not infer the first-cell budget or intercell provenance from a
dirty physical start. -/
namespace L4.BStarCopyCapacity
open AllSizeProtocol BStarCopyFIFO BStarLongClaims BStarLongPackets
open BStarLongPrep BStarLongCommandData

/-- Any finite sequence of valid old-vacancy receives, sends and holds
from a cleared destination. -/
inductive CleanRun {Label : Type} : Queue Label → Prop
  | init : CleanRun Queue.init
  | step {q q' : Queue Label} : CleanRun q → Queue.Step q q' → CleanRun q'

theorem clean_custody {Label : Type} {q : Queue Label} (H : CleanRun q) :
    q.Custody := by
  induction H with
  | init => exact Queue.init_custody
  | step _ s ih => exact Queue.step_custody ih s

/-- The most recent accepted arrival is retained and cannot be lost by
a send; the empty-history branch has never created a mobile. -/
theorem clean_retained {Label : Type} {q : Queue Label} (H : CleanRun q) :
    q.retained=none ↔ q.arrivals=[] := by
  induction H with
  | init => simp [Queue.init]
  | step _ s ih =>
    cases s with
    | idle => exact ih
    | send => exact ih
    | receive a _ => simp [Queue.receive]

theorem clean_send_cap {Label : Type} {q : Queue Label} (H : CleanRun q) :
    q.sent.length ≤ q.arrivals.length-1 := by
  have custody := clean_custody H
  cases R : q.retained with
  | none =>
    have E := (clean_retained H).mp R
    have C := congrArg List.length custody
    simp only [E,List.length_nil,List.length_append] at C
    omega
  | some a => have C := Queue.sent_lt q a custody R; omega

/-- At most one accepted arrival leaves the mobile empty forever
within that prefix: a mobile is a displaced old retained tuple. -/
theorem clean_mobile_empty {Label : Type} {q : Queue Label} (H : CleanRun q)
    (atMostOne : q.arrivals.length≤1) : q.mobile=none := by
  have custody := clean_custody H
  cases M : q.mobile with
  | none => rfl
  | some a =>
    have C := congrArg List.length custody
    simp only [List.length_append,M,Option.toList_some,List.length_cons,List.length_nil] at C
    have R : q.retained≠none := by
      intro h
      have A := (clean_retained H).mp h
      simp only [A,List.length_nil] at C
      omega
    cases E : q.retained with
    | none => exact (R E).elim
    | some b =>
      simp only [E,Option.toList_some,List.length_cons,List.length_nil] at C
      omega

/-- Zero-based ordinal form of A_i ≤ r−i+1. Counts refer to the
same prefix. Gaps in service, padding, or delay may decrease the
next receiver's count, but may not invent additional arrivals. -/
theorem arrival_cap {Label : Type} (cells : Nat → Queue Label) (r : Nat)
    (first : (cells 0).arrivals.length≤r)
    (clean : ∀ i, i<r → CleanRun (cells i))
    (handoff : ∀ i, i+1<r → (cells (i+1)).arrivals.length≤(cells i).sent.length) :
    ∀ i, i<r → (cells i).arrivals.length≤r-i := by
  intro i
  induction i with
  | zero => intro _; simpa using first
  | succ i ih =>
    intro h
    have a := ih (by omega)
    have b := clean_send_cap (clean i (by omega))
    have c := handoff i h
    omega

theorem terminal_mobile_empty {Label : Type} (cells : Nat → Queue Label) (r : Nat)
    (hr : 0<r) (first : (cells 0).arrivals.length≤r)
    (clean : ∀ i, i<r → CleanRun (cells i))
    (handoff : ∀ i, i+1<r → (cells (i+1)).arrivals.length≤(cells i).sent.length) :
    (cells (r-1)).mobile=none := by
  have cap := arrival_cap cells r first clean handoff (r-1) (by omega)
  exact clean_mobile_empty (clean _ (by omega)) (by omega)

/-- If the selected terminal receiver is the clean final destination,
the actual END claim emits no assignment at all (not even an
idempotent clear or sticky-error write). -/
theorem end_no_disposal {Label : Type} (digits : Label → BitVec 36)
    (cells : Nat → Queue Label) (r : Nat)
    (hr : 0<r) (first : (cells 0).arrivals.length≤r)
    (clean : ∀ i, i<r → CleanRun (cells i))
    (handoff : ∀ i, i+1<r → (cells (i+1)).arrivals.length≤(cells i).sent.length)
    (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW)) (t : At Sheet)
    (matched : Compatible digits (cells (r-1)) (view x t)) :
    dataEffects g (view x) (ending t)=[] := by
  have e := terminal_mobile_empty cells r hr first clean handoff
  have empty : (view x t).mobile=.empty := by simpa [encode,e] using matched.1
  simp [dataEffects,ending,endEffects,empty]

private theorem fold_away (A : List (At Sheet × Leaf)) (old : At Sheet → Lane)
    (t : At Sheet) (away : ∀ a, (t,a)∉A) :
    (A.foldl update old) t=old t := by
  induction A generalizing old with
  | nil => rfl
  | cons a A ih =>
    have ne : t≠a.1 := fun H => away a.2 (by cases a; simp_all)
    rw [List.foldl_cons,ih (update old a) (fun a h => away a (List.mem_cons_of_mem _ h))]
    simp [update,ne]

/-- A selected END with empty old mobile leaves the entire destination
lane unchanged in the literal COPY patch. Its ownership excludes
same-mark PREP and every competing incoming HOP to that lane. -/
theorem selected_end_holds (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (t : At Sheet) (hc : ending t∈orderedData g (reserved (round g x).prep))
    (empty : (view x t).mobile=.empty) :
    view (patchPair (patch g x) x) t = view x t := by
  let P := (round g x).prep
  let old := view x
  let L := orderedData g (reserved P)
  have slot : t∈(ending t).slots := by simp [Claim.slots,ending]
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp hc
  change L=l++ending t::r at E
  have K := data_reservations g (reserved P)
  have H : L.Pairwise (fun a b => ∀ s∈b.slots, s∉a.slots) := K.1
  rw [E] at H
  have away (a : Leaf) : (t,a)∉prepAssignments old P ++ L.flatMap (dataEffects g old) := by
    intro Hm
    rcases List.mem_append.mp Hm with M|M
    · exact K.2 (ending t) hc t slot (prep_lane_reserved old P t a M)
    · rw [E,List.flatMap_append,List.flatMap_cons] at M
      rcases List.mem_append.mp M with M|M
      · obtain ⟨c,hc,M⟩ := List.mem_flatMap.mp M
        exact (H.rel_of_mem_append hc (by simp : ending t∈ending t::r))
          t slot (data_lane_claim g old c t a M)
      · rcases List.mem_append.mp M with M|M
        · simp [dataEffects,ending,endEffects,old,empty] at M
        · obtain ⟨c,hc,M⟩ := List.mem_flatMap.mp M
          have Q := (List.pairwise_cons.mp (List.pairwise_append.mp H).2.1).1 c hc
          exact Q t (data_lane_claim g old c t a M) slot
  rw [BStarLongCommandData.round_transfer]
  exact fold_away _ old t away

/-- The finite-prefix capacity bound discharges the real selected
terminal's old-vacancy premise, so even a terminal mark cannot
dispose of a tagged packet in such a prefix. -/
theorem terminal_selected_holds {Label : Type} (digits : Label → BitVec 36)
    (cells : Nat → Queue Label) (r : Nat)
    (hr : 0<r) (first : (cells 0).arrivals.length≤r)
    (clean : ∀ i, i<r → CleanRun (cells i))
    (handoff : ∀ i, i+1<r → (cells (i+1)).arrivals.length≤(cells i).sent.length)
    (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW)) (t : At Sheet)
    (matched : Compatible digits (cells (r-1)) (view x t))
    (hc : ending t∈orderedData g (reserved (round g x).prep)) :
    view (patchPair (patch g x) x) t = view x t := by
  have e := terminal_mobile_empty cells r hr first clean handoff
  exact selected_end_holds g x t hc (by simpa [encode,e] using matched.1)

#print axioms clean_send_cap
#print axioms arrival_cap
#print axioms terminal_mobile_empty
#print axioms end_no_disposal
#print axioms selected_end_holds
#print axioms terminal_selected_holds
end L4.BStarCopyCapacity

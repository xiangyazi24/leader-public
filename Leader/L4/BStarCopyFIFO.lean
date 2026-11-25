import Leader.L4.BStarLongCopyFence

/-! FIFO custody at a retained COPY destination. Labels are ghost
source occurrences, not byte decodings; duplicate payloads are allowed. -/
namespace L4.BStarCopyFIFO
open AllSizeProtocol BStarLongClaims BStarLongPackets
open BStarLongPrep BStarLongCommandData

structure Queue (Label : Type) where
  arrivals : List Label
  sent : List Label
  mobile : Option Label
  retained : Option Label

/-- All accepted arrivals are accounted for, in order. The penultimate
arrival is allowed to still be mobile while the latest is retained. -/
def Queue.Custody {Label : Type} (q : Queue Label) : Prop :=
  q.arrivals = q.sent ++ q.mobile.toList ++ q.retained.toList

def Queue.init {Label : Type} : Queue Label := ⟨[],[],none,none⟩

def Queue.receive {Label : Type} (q : Queue Label) (a : Label) : Queue Label :=
  ⟨q.arrivals++[a],q.sent,q.retained,some a⟩

def Queue.send {Label : Type} (q : Queue Label) : Queue Label :=
  ⟨q.arrivals,q.sent++q.mobile.toList,none,q.retained⟩

theorem Queue.init_custody {Label : Type} : (Queue.init (Label:=Label)).Custody := rfl

/-- Old vacancy is the exact condition needed to preserve every label;
the previous retained label goes into mobile on the same arrival. -/
theorem Queue.receive_custody {Label : Type} (q : Queue Label) (a : Label)
    (h : q.Custody) (vacant : q.mobile=none) : (q.receive a).Custody := by
  unfold Custody receive at *
  simp only [vacant,Option.toList_none,List.append_nil,Option.toList_some] at h ⊢
  rw [h]

theorem Queue.send_custody {Label : Type} (q : Queue Label) (h : q.Custody) :
    q.send.Custody := by
  simpa [Custody,send] using h

/-- Arbitrary interleavings preserve FIFO provided every receive
samples old vacancy. An idle step records no custody change. -/
inductive Queue.Step {Label : Type} : Queue Label → Queue Label → Prop
  | idle (q : Queue Label) : Step q q
  | receive (q : Queue Label) (a : Label) : q.mobile=none → Step q (q.receive a)
  | send (q : Queue Label) : Step q q.send

theorem Queue.step_custody {Label : Type} {q q' : Queue Label}
    (h : q.Custody) (s : Step q q') : q'.Custody := by
  cases s with
  | idle => exact h
  | receive a H => exact q.receive_custody a h H
  | send => exact q.send_custody h

/-- A drained occupied cell forwarded every arrival except its last. -/
theorem Queue.drained {Label : Type} (q : Queue Label) (a : Label)
    (h : q.Custody) (empty : q.mobile=none) (held : q.retained=some a) :
    q.arrivals=q.sent++[a] := by
  simpa [Custody,empty,held] using h

def encode {Label : Type} (digits : Label → BitVec 36) : Option Label → Digit9
  | none => .empty
  | some a => .data (digits a)

def Compatible {Label : Type} (digits : Label → BitVec 36) (q : Queue Label) (l : Lane) : Prop :=
  l.mobile=encode digits q.mobile ∧ l.retained=encode digits q.retained

/-- The actual COPY patch at a chosen retained receiver performs the
FIFO receive on arbitrary raw words when the old lanes match the
ghost labels. The proof never assumes the payload encoding injective. -/
theorem literal_receive {Label : Type} (digits : Label → BitVec 36)
    (q : Queue Label) (a : Label) (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (selected : c∈orderedData g (reserved (round g x).prep)) (hne : u≠v)
    (ret : retains g v=true) (gates : ((view x u).gate && (view x v).gate)=true)
    (input : (view x u).mobile=.data (digits a))
    (old : Compatible digits q (view x v)) (vacant : q.mobile=none) (custody : q.Custody) :
    Compatible digits (q.receive a) (view (patchPair (patch g x) x) v) ∧ (q.receive a).Custody := by
  have empty : (view x v).mobile=.empty := by simpa [encode,vacant] using old.1
  have H := BStarLongCopyFence.retained_shift g x u v c hs hd hh selected hne ret gates
    (by simp [input]) empty
  refine ⟨?_,q.receive_custody a custody vacant⟩
  rw [H]
  exact ⟨old.2,input⟩

private theorem fold_away (A : List (At Sheet × Leaf)) (old : At Sheet → Lane)
    (s : At Sheet) (ha : ∀ a, (s,a)∉A) :
    (A.foldl update old) s=old s := by
  induction A generalizing old with
  | nil => rfl
  | cons a A ih =>
    have ne : s≠a.1 := fun H => ha a.2 (by cases a; simp_all)
    rw [List.foldl_cons,ih (update old a) (fun a h => ha a (List.mem_cons_of_mem _ h))]
    simp [update,ne]

private theorem fold_at (s : At Sheet) (A : List Leaf) (old : At Sheet → Lane) :
    ((A.map (s,·)).foldl update old) s=typedLeaves (old s) A := by
  induction A generalizing old with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons,List.foldl_cons,ih]
    simp [typedLeaves,update]

/-- The selected COPY patch has exactly the winning hop's old-source
effects at its sender. No preparation or other data claim writes it. -/
theorem sender_exact (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (hsel : c∈orderedData g (reserved (round g x).prep)) (hne : u≠v) :
    let read := view x
    let post := view (patchPair (patch g x) x)
    post u=typedLeaves (read u) (hopEffects (read u) (read v) (retains g v)).1 := by
  let P := (round g x).prep
  let old := view x
  let L := orderedData g (reserved P)
  have hV : u∈c.slots := by simp [Claim.slots,hs]
  have K := data_reservations g (reserved P)
  have notPre (a : Leaf) : (u,a)∉prepAssignments old P :=
    fun h => K.2 c hsel u hV (prep_lane_reserved old P u a h)
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp hsel
  change L=l++c::r at E
  have H : L.Pairwise (fun a b => ∀ s∈b.slots, s∉a.slots) := K.1
  rw [E] at H
  have awayL (a : Leaf) : (u,a)∉l.flatMap (dataEffects g old) := by
    intro h
    obtain ⟨b,hb,hB⟩ := List.mem_flatMap.mp h
    exact (H.rel_of_mem_append hb (by simp : c∈c::r)) u hV (data_lane_claim g old b u a hB)
  have awayR (a : Leaf) : (u,a)∉r.flatMap (dataEffects g old) := by
    intro h
    obtain ⟨b,hb,hB⟩ := List.mem_flatMap.mp h
    have H' := (List.pairwise_cons.mp (List.pairwise_append.mp H).2.1).1 b hb
    exact H' u (data_lane_claim g old b u a hB) hV
  have C : dataEffects g old c=
      ((hopEffects (old u) (old v) (retains g v)).1.map (u,·)) ++
      ((hopEffects (old u) (old v) (retains g v)).2.map (v,·)) := by
    simp [dataEffects,hs,hd,hh]
  have awayReceiver (a : Leaf) :
      (u,a)∉(hopEffects (old u) (old v) (retains g v)).2.map (v,·) := by
    intro H
    obtain ⟨b,_,hb⟩ := List.mem_map.mp H
    exact hne (congrArg Prod.fst hb).symm
  dsimp only
  rw [BStarLongCommandData.round_transfer]
  change ((prepAssignments old P ++ L.flatMap (dataEffects g old)).foldl update old) u=_
  rw [E,List.flatMap_append,List.flatMap_cons,C]
  simp only [List.foldl_append]
  rw [fold_away _ _ _ awayR,fold_away _ _ _ awayReceiver,fold_at,fold_away _ _ _ awayL,
    fold_away _ _ _ notPre]

/-- Both endpoints of an actual chosen retaining hop refine the
same ghost handoff, with the old mobile label used at the sender
and the old vacancy tested at the receiver. -/
theorem literal_hop_fifo {Label : Type} (digits : Label → BitVec 36)
    (q s : Queue Label) (a : Label) (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (selected : c∈orderedData g (reserved (round g x).prep)) (hne : u≠v)
    (ret : retains g v=true) (gates : ((view x u).gate && (view x v).gate)=true)
    (outgoing : q.mobile=some a) (oldSender : Compatible digits q (view x u))
    (oldReceiver : Compatible digits s (view x v)) (vacant : s.mobile=none)
    (hc : q.Custody) (hr : s.Custody) :
    let post := view (patchPair (patch g x) x)
    (Compatible digits q.send (post u) ∧ q.send.Custody) ∧
      (Compatible digits (s.receive a) (post v) ∧ (s.receive a).Custody) := by
  have input : (view x u).mobile=.data (digits a) := by simpa [outgoing,encode] using oldSender.1
  have empty : (view x v).mobile=.empty := by simpa [vacant,encode] using oldReceiver.1
  refine ⟨⟨?_,q.send_custody hc⟩,
    literal_receive digits s a g x u v c hs hd hh selected hne ret gates input oldReceiver vacant hr⟩
  rw [sender_exact g x u v c hs hd hh selected hne]
  simpa [Compatible,Queue.send,encode,typedLeaves,Leaf.put,hopEffects,ret,gates,input,empty] using oldSender.2

private theorem offered_mem {C : Type} (k : C → Nat) (xs : List C) (c : C) :
    c∈offers k xs → c∈xs := by
  induction xs with
  | nil => simp [offers]
  | cons a t ih =>
    change c∈BStarLongClaims.insert k a (offers k t) → _
    rw [mem_insert]
    exact fun H => List.mem_cons.mpr (H.imp_right ih)

/-- Reservations only suppress candidates; every accepted COPY
hop is on one of the exact six oriented lane links. No selected
hop switches travel direction or skips a physical site. -/
theorem selected_orientation (g : Pair LongGeometry) (reserved : List (At Sheet))
    (c : DataClaim) (hc : c∈orderedData g reserved) (hs : c.kind=.hop) :
    c=hop (L .ls) (R .ld) ∨ c=hop (R .rs) (L .rd) ∨
    c=hop (L .ls) (R .ls) ∨ c=hop (R .rd) (L .rd) ∨
    c=hop (L .ld) (R .ld) ∨ c=hop (R .rs) (L .rs) := by
  have M := offered_mem _ _ _ ((select_sublist ..).subset hc)
  obtain ⟨x,y⟩ := g
  simp only [dataClaims,ends] at M
  cases X : x.inside <;> cases Y : y.inside <;> cases Z : x.last <;> cases H : y.axes.h6 <;>
    simp only [X,Y,Z,H,Bool.false_and,Bool.true_and,Bool.not_true,Bool.not_false,
      Bool.false_eq_true,if_false,if_true,List.nil_append,List.append_nil,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at M
  all_goals
    repeat first
      | (subst c; first | decide +kernel | simp [ending] at hs)
      | (rcases M with M|M)

/-- A line of drained retained cells, chained in travel order. Each
cell outputs exactly the preceding list except its last member. -/
inductive DrainedLine {Label : Type} : List Label → List Label → List Label → Prop
  | tail (input : List Label) : DrainedLine input [] input
  | retain (forwarded : List Label) (a : Label) (retained residual : List Label) :
      DrainedLine forwarded retained residual →
      DrainedLine (forwarded++[a]) (a::retained) residual

/-- End-to-end ordering, even when the payload bytes are all equal:
the retained labels in travel order are the reverse of delivery. -/
theorem DrainedLine.order {Label : Type} {input retained residual : List Label}
    (h : DrainedLine input retained residual) : input=residual++retained.reverse := by
  induction h with
  | tail => simp
  | retain forwarded a retained residual H ih =>
    rw [List.reverse_cons,←List.append_assoc,←ih]

theorem DrainedLine.complete {Label : Type} {input retained : List Label}
    (h : DrainedLine input retained []) : retained=input.reverse := by
  simpa using congrArg List.reverse h.order.symm

/-- At any time with a retained label, the already forwarded list is
a strict prefix of arrivals. This is the per-cell capacity loss used
in the transport budget. -/
theorem Queue.sent_lt {Label : Type} (q : Queue Label) (a : Label) (h : q.Custody)
    (held : q.retained=some a) : q.sent.length < q.arrivals.length := by
  have e := congrArg List.length h
  simp only [List.length_append,held,Option.toList_some,List.length_cons,List.length_nil] at e
  omega

/-- Left releases occur in descending ordinal; the retained left
destination travel order is ascending. -/
theorem left_offsets (r : Nat) (held : List Nat)
    (h : DrainedLine (List.range r).reverse held []) : held=List.range r := by
  simpa only [List.reverse_reverse] using h.complete

/-- Right releases occur in ascending ordinal; the retained right
destination travel order is descending. Any nonretaining center
padding lies outside the retained list. -/
theorem right_offsets (r : Nat) (held : List Nat)
    (h : DrainedLine (List.range r) held []) : held=(List.range r).reverse :=
  h.complete

#print axioms Queue.step_custody
#print axioms literal_receive
#print axioms sender_exact
#print axioms literal_hop_fifo
#print axioms selected_orientation
#print axioms DrainedLine.complete
#print axioms Queue.sent_lt
#print axioms left_offsets
#print axioms right_offsets
end L4.BStarCopyFIFO

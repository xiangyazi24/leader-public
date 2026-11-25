import Leader.L4.BStarCopyInjection

/-! A finite-word COPY ledger for one clean, fixed owner line. The
geometry/protection proof must identify and enumerate these events;
the ledger itself neither assumes divestment-free FENCE nor concludes
that a finite prefix has delivered every release. -/
namespace L4.BStarCopyMarkedLedger
open BStarCopyFIFO BStarCopyCapacity BStarCopyInjection

structure Ledger (Label : Type) where
  release : ReleaseHistory Label
  cells : Nat → Queue Label

/-- A capped program stage stays in its prescribed release order.
Every first-receiver arrival has an already accounted-for release,
and every interior arrival has an accounted-for predecessor send. -/
structure Valid {Label : Type} (plan : List Label) (s : Ledger Label) : Prop where
  follows : s.release.Follows plan
  clean : ∀ j, CleanRun (s.cells j)
  first : (s.cells 0).arrivals.length ≤ s.release.released.length
  handoff : ∀ j, (s.cells (j+1)).arrivals.length ≤ (s.cells j).sent.length

def Ledger.init {Label : Type} (plan : List Label) : Ledger Label :=
  ⟨ReleaseHistory.init plan,fun _ => Queue.init⟩

def Ledger.receiveFirst {Label : Type} (s : Ledger Label) (tag : Label) : Ledger Label :=
  {s with cells := fun j => if j=0 then (s.cells 0).receive tag else s.cells j}

def Ledger.transfer {Label : Type} (s : Ledger Label) (i : Nat) (tag : Label) : Ledger Label :=
  {s with cells := fun j => if j=i then (s.cells i).send
    else if j=i+1 then (s.cells (i+1)).receive tag else s.cells j}

def Ledger.releaseOne {Label : Type} (s : Ledger Label) (tag : Label) (todo : List Label) :
    Ledger Label := {s with release := ⟨s.release.released++[tag],todo⟩}

/-- Accounting events. A release alone does not imply a delivery.
The strict counter credit at first entry permits arbitrary delays in
the nonretaining prefix, but not creation of an additional arrival. -/
inductive Step {Label : Type} : Ledger Label → Ledger Label → Prop
  | idle (s : Ledger Label) : Step s s
  | release (s : Ledger Label) (tag : Label) (todo : List Label) :
      s.release.pending=tag::todo → Step s (s.releaseOne tag todo)
  | first (s : Ledger Label) (tag : Label) :
      (s.cells 0).mobile=none →
      (s.cells 0).arrivals.length<s.release.released.length →
      Step s (s.receiveFirst tag)
  | transfer (s : Ledger Label) (i : Nat) (tag : Label) :
      (s.cells i).mobile=some tag → (s.cells (i+1)).mobile=none →
      Step s (s.transfer i tag)

theorem valid_init {Label : Type} (plan : List Label) : Valid plan (Ledger.init plan) :=
  ⟨rfl,fun _ => .init,Nat.le_refl 0,fun _ => Nat.le_refl 0⟩

private theorem first_recv_cell {Label : Type} (s : Ledger Label) (tag : Label)
    (j : Nat) : (s.receiveFirst tag).cells j =
      if j=0 then (s.cells 0).receive tag else s.cells j := rfl

private theorem transfer_cell {Label : Type} (s : Ledger Label) (tag : Label)
    (i j : Nat) : (s.transfer i tag).cells j =
      if j=i then (s.cells i).send else if j=i+1 then (s.cells (i+1)).receive tag else s.cells j := rfl

theorem valid_step {Label : Type} (plan : List Label) {s u : Ledger Label}
    (V : Valid plan s) (T : Step s u) : Valid plan u := by
  cases T with
  | idle => exact V
  | release tag todo pending =>
    refine ⟨?_,V.clean,?_,V.handoff⟩
    · have H := V.follows
      unfold ReleaseHistory.Follows at H ⊢
      simpa [Ledger.releaseOne,List.append_assoc,pending] using H
    · have H := V.first
      simp only [Ledger.releaseOne,List.length_append,List.length_cons,List.length_nil]
      omega
  | first tag empty credit =>
    refine ⟨V.follows,?_,?_,?_⟩
    · intro j
      rw [first_recv_cell]
      split
      · exact .step (V.clean 0) (.receive _ _ empty)
      · exact V.clean j
    · rw [first_recv_cell,if_pos rfl]
      simp only [Queue.receive,List.length_append,List.length_cons,List.length_nil]
      exact credit
    · intro j
      rw [first_recv_cell,first_recv_cell,if_neg (by omega : j+1≠0)]
      split
      · rename_i H; subst j; exact V.handoff 0
      · exact V.handoff j
  | transfer i tag outgoing vacant =>
    have NE : i+1≠i := by omega
    refine ⟨V.follows,?_,?_,?_⟩
    · intro j
      rw [transfer_cell]
      split
      · exact .step (V.clean i) (.send _)
      · split
        · exact .step (V.clean (i+1)) (.receive _ _ vacant)
        · exact V.clean j
    · rw [transfer_cell]
      have H := V.first
      by_cases S : i=0
      · subst i; exact H
      · rw [if_neg (Ne.symm S),if_neg (by omega : 0≠i+1)]
        exact H
    · intro j
      rw [transfer_cell,transfer_cell]
      have H := V.handoff j
      by_cases S : j=i
      · subst j
        simp only [NE,if_false,if_true,Queue.receive,Queue.send,List.length_append,
          List.length_cons,List.length_nil,outgoing,Option.toList_some]
        omega
      · rw [if_neg S]
        have G : j+1≠i+1 := by omega
        by_cases A : j+1=i
        · rw [if_pos A,if_neg (by omega : j≠i+1)]
          simpa [Queue.send,A] using H
        · rw [if_neg A,if_neg G]
          by_cases B : j=i+1
          · rw [if_pos B]
            simpa [Queue.receive,B] using H
          · rw [if_neg B]
            exact H

/-- Mark blocks may have more than one independent accounting event.
Premises are checked at the corresponding old lane before extension. -/
inductive Prefix {Label : Type} (plan : List Label) : Ledger Label → Prop
  | empty : Prefix plan (Ledger.init plan)
  | mark {s u : Ledger Label} : Prefix plan s → Step s u → Prefix plan u

theorem prefix_valid {Label : Type} {plan : List Label} {s : Ledger Label}
    (P : Prefix plan s) : Valid plan s := by
  induction P with
  | empty => exact valid_init plan
  | mark _ e ih => exact valid_step plan ih e

theorem prefix_cap {Label : Type} {plan : List Label} {s : Ledger Label}
    (P : Prefix plan s) (j : Nat) (h : j<plan.length) :
    (s.cells j).arrivals.length≤plan.length-j := by
  have V := prefix_valid P
  exact arrival_cap _ _ (first_arrival_cap _ _ _ V.follows V.first)
    (fun i _ => V.clean i) (fun i _ => V.handoff i) j h

theorem terminal_empty {Label : Type} {plan : List Label} {s : Ledger Label}
    (P : Prefix plan s) (h : 0<plan.length) :
    (s.cells (plan.length-1)).mobile=none := by
  have V := prefix_valid P
  exact terminal_mobile_empty _ _ h (first_arrival_cap _ _ _ V.follows V.first)
    (fun i _ => V.clean i) (fun i _ => V.handoff i)

#print axioms valid_step
#print axioms prefix_cap
#print axioms terminal_empty

open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarLongToken BStarLongCommand

/-- One actual selected retaining HOP extends the count ledger and
provides the byte/labeled correspondence at *both* changing lanes. -/
theorem physical_transfer {Label : Type} (digits : Label → BitVec 36) (plan : List Label)
    (s : Ledger Label) (pre : Prefix plan s) (i : Nat) (tag : Label)
    (g : Pair LongGeometry) (x : Pair (BitVec LW)) (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (selected : c∈orderedData g (reserved (round g x).prep)) (hne : u≠v)
    (ret : retains g v=true) (gates : ((view x u).gate && (view x v).gate)=true)
    (outgoing : (s.cells i).mobile=some tag) (S : Compatible digits (s.cells i) (view x u))
    (R : Compatible digits (s.cells (i+1)) (view x v)) (vacant : (s.cells (i+1)).mobile=none) :
    let t := s.transfer i tag
    let post := view (patchPair (patch g x) x)
    Prefix plan t ∧ Compatible digits (t.cells i) (post u) ∧
      Compatible digits (t.cells (i+1)) (post v) := by
  have V := prefix_valid pre
  have H := literal_hop_fifo digits (s.cells i) (s.cells (i+1)) tag g x u v c hs hd
    hh selected hne ret gates outgoing S R vacant (clean_custody (V.clean _))
    (clean_custody (V.clean _))
  dsimp only
  refine ⟨.mark pre (.transfer s i tag outgoing vacant),?_,?_⟩
  · rw [transfer_cell,if_pos rfl]
    exact H.1.1
  · rw [transfer_cell,if_neg (by omega : i+1≠i),if_pos rfl]
    exact H.2.1

/-- At the first receiver, a literal chosen retaining HOP extends
the ledger after one already released tuple traverses the external
nonretaining prefix. Its label match and count credit are streaming
inputs, not silently inferred from the payload bytes. -/
theorem physical_first {Label : Type} (digits : Label → BitVec 36) (plan : List Label)
    (s : Ledger Label) (pre : Prefix plan s) (tag : Label)
    (g : Pair LongGeometry) (x : Pair (BitVec LW)) (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (selected : c∈orderedData g (reserved (round g x).prep)) (hne : u≠v)
    (ret : retains g v=true) (gates : ((view x u).gate && (view x v).gate)=true)
    (input : (view x u).mobile=.data (digits tag))
    (R : Compatible digits (s.cells 0) (view x v)) (vacant : (s.cells 0).mobile=none)
    (credit : (s.cells 0).arrivals.length<s.release.released.length) :
    let t := s.receiveFirst tag
    Prefix plan t ∧ Compatible digits (t.cells 0) (view (patchPair (patch g x) x) v) := by
  have H := literal_receive digits (s.cells 0) tag g x u v c hs hd hh selected hne ret gates input R
    vacant (clean_custody ((prefix_valid pre).clean _))
  dsimp only
  rw [first_recv_cell,if_pos rfl]
  exact ⟨.mark pre (.first s tag vacant credit),H.1⟩

/-- An authenticated old INJECT at its own active source consumes
the next planned label and releases it into the exact actual mobile.
A release alone does not increment the first receiver's arrival count. -/
theorem physical_release {Label : Type} (digits : Label → BitVec 36) (plan : List Label)
    (s : Ledger Label) (pre : Prefix plan s) (tag : Label) (todo : List Label)
    (pending : s.release.pending=tag::todo)
    (g : Pair LongGeometry) (x : Pair (BitVec LW)) (c : CommandClaim) (p : Payload)
    (side : Side) (reverse : Bool)
    (selected : c∈orderedCommands g) (door : c.kind≠.door)
    (origin : c.source=⟨side,sourceOccurrence reverse⟩)
    (old : bind (geometry g c.source.side) c.source.occurrence (oldTokens x c.source)=.forward p)
    (clean : p.fault=0) (opcode : p.opcode.toNat=10) (inside : (geometry g side).inside=true)
    (unique : ∀ z∈(round g x).prep, z.claim.lane=(injection side reverse).claim.lane →
      z=injection side reverse)
    (enabled : (view x (injection side reverse).claim.lane).gate=true)
    (frozen : (view x (injection side reverse).claim.lane).frozen=.data (digits tag))
    (vacant : (view x (injection side reverse).claim.lane).mobile=.empty) :
    let a := (injection side reverse).claim.lane
    let lane := view (patchPair (patch g x) x) a
    Prefix plan (s.releaseOne tag todo) ∧ lane.mobile=.data (digits tag) ∧ lane.frozen=.empty := by
  have H := literal_inject digits tag g x c p side reverse selected door origin old clean opcode
    inside unique enabled frozen vacant
  refine ⟨.mark pre (.release s tag todo pending),?_,?_⟩
  · rw [H.2]; rfl
  · rw [H.2]

#print axioms physical_transfer
#print axioms physical_first
#print axioms physical_release
end L4.BStarCopyMarkedLedger

import Leader.L4.BStarCopyMarkedLedger
import Leader.L4.BStarLongFencePrefix
import Leader.L4.BStarFenceTerminalData
import Leader.L4.BStarClearanceMobileJoined
import Leader.L4.BStarResetSchedule
import Leader.L4.BStarH6WordChart

namespace L4.BStarCopyFenceSaturation
open BStarCopyFIFO BStarCopyCapacity BStarCopyMarkedLedger BStarCopyInjection

/-- Atomic retaining transfers record the very same ghost label at both
ends, a stronger invariant than Valid.handoff's numerical inequality. -/
def ExactHandoff {L : Type} (s : Ledger L) : Prop :=
  ∀ j, (s.cells (j+1)).arrivals=(s.cells j).sent

theorem exact_handoff_step {L : Type} {s t : Ledger L} (H : ExactHandoff s)
    (E : Step s t) : ExactHandoff t := by
  intro j
  have J := H j
  cases E with
  | idle => exact J
  | release _ _ _ => exact J
  | first _ _ _ =>
    simp only [Ledger.receiveFirst,show j+1≠0 by omega,if_false]
    by_cases Z : j=0
    · subst j
      exact J
    · simpa only [Z,if_false] using J
  | transfer i a out _ =>
    by_cases jj : j=i
    · subst j
      simp only [Ledger.transfer,show i+1≠i by omega,if_false,if_true,Queue.receive,Queue.send,
        out,Option.toList_some,J]
    · simp only [Ledger.transfer,jj,if_false]
      by_cases A : j+1=i
      · simp only [A,if_true,Queue.send,show j≠i+1 by omega,if_false]
        simpa only [A] using J
      · by_cases K : j=i+1
        · rw [if_neg A,if_neg (show j+1≠i+1 by omega),if_pos K]
          simpa only [K,Queue.receive] using J
        · simp only [A,show j+1≠i+1 by omega,if_false,K]
          exact J

theorem exact_handoff {L : Type} {plan : List L} {s : Ledger L} (P : Prefix plan s) :
    ExactHandoff s := by
  induction P with
  | empty => intro _; rfl
  | mark _ E ih => exact exact_handoff_step ih E

/-- Work backward from a retained last receiver. Every numerical cap
is forced to equality on the same prefix; no FENCE progress hypothesis. -/
theorem arrival_saturation {L : Type} {plan : List L} {s : Ledger L}
    (P : Prefix plan s) (hr : 0<plan.length)
    (terminal : (s.cells (plan.length-1)).retained≠none) :
    ∀ j, j<plan.length → (s.cells j).arrivals.length=plan.length-j := by
  let r := plan.length
  have V := prefix_valid P
  have lastPos : 0<(s.cells (r-1)).arrivals.length := by
    cases H : (s.cells (r-1)).arrivals with
    | nil => exact (terminal ((clean_retained (V.clean _)).mpr H)).elim
    | cons a h => simp
  have lower (k : Nat) : ∀ j, j+k=r-1 → r-j≤(s.cells j).arrivals.length := by
    induction k with
    | zero =>
      intro j h
      have J : j=r-1 := by omega
      subst j
      omega
    | succ k ih =>
      intro j h
      have A := ih (j+1) (by omega)
      have S := clean_send_cap (V.clean j)
      have F := V.handoff j
      omega
  intro j hj
  have h := lower (r-1-j) j (by omega)
  exact Nat.le_antisymm (prefix_cap P j hj) h

theorem cell_saturation {L : Type} {plan : List L} {s : Ledger L}
    (P : Prefix plan s) (hr : 0<plan.length)
    (terminal : (s.cells (plan.length-1)).retained≠none) :
    ∀ j, j<plan.length →
      (s.cells j).arrivals.length=plan.length-j ∧
      (s.cells j).sent.length=plan.length-j-1 ∧ (s.cells j).mobile=none ∧
      ∃ a,(s.cells j).retained=some a := by
  intro j hj
  have V := prefix_valid P
  have A := arrival_saturation P hr terminal j hj
  have C := clean_send_cap (V.clean j)
  have S : (s.cells j).sent.length=plan.length-j-1 := by
    by_cases J : j+1<plan.length
    · have next := arrival_saturation P hr terminal (j+1) J
      have le := V.handoff j
      omega
    · omega
  have held : (s.cells j).retained≠none := by
    intro R
    have emp := (clean_retained (V.clean j)).mp R
    simp only [emp,List.length_nil] at A
    omega
  cases R : (s.cells j).retained with
  | none => exact (held R).elim
  | some a =>
    have M : (s.cells j).mobile=none := by
      have H := congrArg List.length (clean_custody (V.clean j))
      cases B : (s.cells j).mobile with
      | none => rfl
      | some b =>
        simp only [List.length_append,R,B,Option.toList_some,List.length_cons,List.length_nil] at H
        omega
    exact ⟨A,S,M,a,rfl⟩

/-- The original count-only ledger is insufficient at the first
receiver. This extra state is exactly the audited ordered boundary
relation: prior arrivals followed by upstream mobile labels in data
travel order is the issued release list. -/
def OrderedBoundary {L : Type} (s : Ledger L) (upstream : List L) : Prop :=
  (s.cells 0).arrivals++upstream=s.release.released

theorem boundary_release {L : Type} (s : Ledger L) (upstream : List L) (tag : L) (todo : List L)
    (B : OrderedBoundary s upstream) :
    OrderedBoundary (s.releaseOne tag todo) (upstream++[tag]) := by
  simpa [OrderedBoundary,Ledger.releaseOne,List.append_assoc] using congrArg (·++[tag]) B

theorem boundary_cross {L : Type} (s : Ledger L) (upstream : List L) (tag : L)
    (B : OrderedBoundary s (tag::upstream)) :
    OrderedBoundary (s.receiveFirst tag) upstream := by
  simpa [OrderedBoundary,Ledger.receiveFirst,Queue.receive,List.append_assoc] using B

theorem boundary_transfer {L : Type} (s : Ledger L) (upstream : List L) (tag : L) (j : Nat)
    (B : OrderedBoundary s upstream) :
    OrderedBoundary (s.transfer j tag) upstream := by
  cases j with
  | zero => exact B
  | succ j => exact B

theorem saturated_release {L : Type} {plan : List L} {s : Ledger L} {upstream : List L}
    (P : Prefix plan s) (hr : 0<plan.length)
    (terminal : (s.cells (plan.length-1)).retained≠none)
    (B : OrderedBoundary s upstream) :
    upstream=[] ∧ s.release.pending=[] ∧ (s.cells 0).arrivals=plan := by
  have A := arrival_saturation P hr terminal 0 hr
  have C := congrArg List.length B
  have F := (prefix_valid P).follows
  have D := congrArg List.length F
  simp only [List.length_append] at C D
  have U : upstream=[] := List.length_eq_zero_iff.mp (by omega)
  have Q : s.release.pending=[] := List.length_eq_zero_iff.mp (by omega)
  exact ⟨U,Q,(by simpa only [U,List.append_nil,Q] using B.trans (by simpa only [Q,List.append_nil] using F.symm))⟩

/-- Retained labels in physical data-travel order. -/
def heldFrom {L : Type} (cells : Nat→Queue L) (i : Nat) : Nat → List L
  | 0 => []
  | k+1 => (cells i).retained.toList ++ heldFrom cells (i+1) k

theorem drained_suffix {L : Type} (cells : Nat→Queue L) (i count : Nat)
    (custody : ∀ j, i≤j → j<i+count → (cells j).Custody)
    (mobile : ∀ j, i≤j → j<i+count → (cells j).mobile=none)
    (held : ∀ j, i≤j → j<i+count → ∃ a,(cells j).retained=some a)
    (handoff : ∀ j,(cells (j+1)).arrivals=(cells j).sent)
    (done : (cells (i+count)).arrivals=[]) :
    DrainedLine (cells i).arrivals (heldFrom cells i count) [] := by
  induction count generalizing i with
  | zero =>
    have Q : (cells i).arrivals=[] := done
    rw [Q]
    exact .tail []
  | succ count ih =>
    obtain ⟨a,R⟩ := held i (by omega) (by omega)
    have H := custody i (by omega) (by omega)
    unfold Queue.Custody at H
    rw [mobile i (by omega) (by omega),R] at H
    simp only [Option.toList_none,List.append_nil,Option.toList_some] at H
    have rest := ih (i+1) (fun j lo hi => custody j (by omega) (by omega))
      (fun j lo hi => mobile j (by omega) (by omega))
      (fun j lo hi => held j (by omega) (by omega))
      (by rw [show i+1+count=i+(count+1) by omega]; exact done)
    rw [handoff i] at rest
    rw [H]
    simpa only [heldFrom,R,Option.toList_some,List.singleton_append] using
      (DrainedLine.retain _ a _ [] rest)

theorem retained_reverse {L : Type} {plan : List L} {s : Ledger L} {upstream : List L}
    (P : Prefix plan s) (hr : 0<plan.length)
    (terminal : (s.cells (plan.length-1)).retained≠none)
    (B : OrderedBoundary s upstream) :
    heldFrom s.cells 0 plan.length=plan.reverse := by
  have all := cell_saturation P hr terminal
  have hand := exact_handoff P
  have done : (s.cells plan.length).arrivals=[] := by
    have A := (all (plan.length-1) (by omega)).2.1
    have E : plan.length-1+1=plan.length := by omega
    have H := hand (plan.length-1)
    rw [E] at H
    exact H.trans (List.length_eq_zero_iff.mp (by omega))
  have H := drained_suffix s.cells 0 plan.length
    (fun j _ _ => clean_custody ((prefix_valid P).clean j))
    (fun j _ hi => (all j (by omega)).2.2.1)
    (fun j _ hi => (all j (by omega)).2.2.2) hand (by simpa using done)
  rw [(saturated_release P hr terminal B).2.2] at H
  exact H.complete

#print axioms exact_handoff
#print axioms cell_saturation
#print axioms retained_reverse

open AllSizeProtocol BStarLongClaims BStarLongPackets BStarLongFencePrefix

/-- The physical receiver line is read in its travel order. -/
def laneRead (lanes : Nat→Lane) (i : Nat) : Nat→List Digit9
  | 0 => []
  | n+1 => (lanes i).retained :: laneRead lanes (i+1) n

private theorem lane_read_map {L : Type} (digits : L→BitVec 36)
    (cells : Nat→Queue L) (lanes : Nat→Lane) (i n : Nat)
    (matchLane : ∀ j,i≤j → j<i+n → Compatible digits (cells j) (lanes j))
    (held : ∀ j,i≤j → j<i+n → ∃ a,(cells j).retained=some a) :
    laneRead lanes i n=(heldFrom cells i n).map (Digit9.data ∘ digits) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    obtain ⟨a,A⟩ := held i (by omega) (by omega)
    have top := (matchLane i (by omega) (by omega)).2
    rw [A] at top
    have tail := ih (i+1) (fun j lo hi => matchLane j (by omega) (by omega))
      (fun j lo hi => held j (by omega) (by omega))
    simp only [laneRead,heldFrom,A,Option.toList_some,List.singleton_append,List.map_cons,top,encode,
      Function.comp_apply,tail]

/-- At the actual successful old retaining test, the whole old line
already holds the exact reversed release word and every mobile is
empty. No no-refill premise on all earlier FENCE visits. -/
theorem physical_terminal {L : Type} (digits : L→BitVec 36)
    {plan : List L} {s : Ledger L} {upstream : List L}
    (P : Prefix plan s) (hr : 0<plan.length)
    (order : OrderedBoundary s upstream)
    (lanes : Nat→Lane)
    (agree : ∀ j,j<plan.length → Compatible digits (s.cells j) (lanes j))
    (g : Pair LongGeometry) (opt : At Sheet→Lane) (a : At Sheet)
    (located : opt a=lanes (plan.length-1)) (retaining : retains g a=true)
    (passed : Passed g opt a) :
    (∀ j,j<plan.length → (lanes j).mobile=.empty) ∧
    laneRead lanes 0 plan.length=plan.reverse.map (Digit9.data ∘ digits) ∧
    upstream=[] ∧ s.release.pending=[] := by
  obtain ⟨d,D⟩ := BStarFenceTerminalData.passed_retaining retaining passed
  rw [located] at D
  have R := (agree (plan.length-1) (by omega)).2
  have terminal : (s.cells (plan.length-1)).retained≠none := by
    intro E
    rw [E] at R
    rw [D] at R
    cases R
  have all := cell_saturation P hr terminal
  have read := lane_read_map digits s.cells lanes 0 plan.length
    (fun j _ H => agree j (by omega))
    (fun j _ H => (all j (by omega)).2.2.2)
  rw [retained_reverse P hr terminal order] at read
  have finish := saturated_release P hr terminal order
  refine ⟨?_,read,finish.1,finish.2.1⟩
  intro j J
  have E := (agree j J).1
  rw [(all j J).2.2.1] at E
  exact E

#print axioms physical_terminal

/-- Accept exactly the upstream head, never a label guessed from equal
packet bytes. Raw upstream adapters may attach this ordered protocol
to the physical line without changing the existing numeric ledger. -/
inductive OrderedStep {L : Type} : Ledger L → List L → Ledger L → List L → Prop
  | hold (s : Ledger L) (u : List L) : OrderedStep s u s u
  | issue (s : Ledger L) (u : List L) (a : L) (todo : List L) :
      s.release.pending=a::todo → OrderedStep s u (s.releaseOne a todo) (u++[a])
  | cross (s : Ledger L) (u : List L) (a : L) :
      (s.cells 0).mobile=none → (s.cells 0).arrivals.length<s.release.released.length →
      OrderedStep s (a::u) (s.receiveFirst a) u
  | interior (s : Ledger L) (u : List L) (j : Nat) (a : L) :
      (s.cells j).mobile=some a → (s.cells (j+1)).mobile=none →
      OrderedStep s u (s.transfer j a) u

inductive OrderedPrefix {L : Type} (plan : List L) : Ledger L → List L → Prop
  | init : OrderedPrefix plan (Ledger.init plan) []
  | mark {s t : Ledger L} {u v : List L} :
      OrderedPrefix plan s u → OrderedStep s u t v → OrderedPrefix plan t v

theorem ordered_prefix {L : Type} {plan : List L} {s : Ledger L} {u : List L}
    (P : OrderedPrefix plan s u) : Prefix plan s ∧ OrderedBoundary s u := by
  induction P with
  | init => exact ⟨.empty,rfl⟩
  | mark pre st ih =>
    cases st with
    | hold => exact ih
    | issue _ a todo pending =>
      exact ⟨.mark ih.1 (.release _ a todo pending),boundary_release _ _ a todo ih.2⟩
    | cross _ a vacant budget =>
      exact ⟨.mark ih.1 (.first _ a vacant budget),boundary_cross _ _ a ih.2⟩
    | interior _ j a fromLabel vacant =>
      exact ⟨.mark ih.1 (.transfer _ j a fromLabel vacant),boundary_transfer _ _ a j ih.2⟩

theorem ordered_physical_terminal {L : Type} (digits : L→BitVec 36)
    {plan : List L} {s : Ledger L} {upstream : List L}
    (P : OrderedPrefix plan s upstream) (hr : 0<plan.length)
    (lanes : Nat→Lane)
    (agree : ∀ j,j<plan.length → Compatible digits (s.cells j) (lanes j))
    (g : Pair LongGeometry) (opt : At Sheet→Lane) (a : At Sheet)
    (located : opt a=lanes (plan.length-1)) (retaining : retains g a=true)
    (passed : Passed g opt a) :
    (∀ j,j<plan.length → (lanes j).mobile=.empty) ∧
    laneRead lanes 0 plan.length=plan.reverse.map (Digit9.data ∘ digits) ∧
    upstream=[] ∧ s.release.pending=[] :=
  physical_terminal digits (ordered_prefix P).1 hr (ordered_prefix P).2 lanes agree g opt a
    located retaining passed

#print axioms ordered_prefix
#print axioms ordered_physical_terminal


open BStarLongPrep BStarLongCommandData BStarTrace BStarH6WordChart BStarLongWork

private theorem fold_away (A : List (At Sheet × Leaf)) (old : At Sheet → Lane)
    (s : At Sheet) (ha : ∀ a, (s,a)∉A) :
    (A.foldl update old) s=old s := by
  induction A generalizing old with
  | nil => rfl
  | cons a A ih =>
    have ne : s≠a.1 := fun H => ha a.2 (by cases a; simp_all)
    rw [List.foldl_cons,ih (update old a) (fun a h => ha a (List.mem_cons_of_mem _ h))]
    simp [update,ne]

set_option maxHeartbeats 1200000 in
/-- No selected COPY statement changes a passed lane when the old
sender on every selected incoming link to it is empty. Its own old
emptiness rules out a send or END error. Reservation alone is not
the invariant: it must exclude prep and nonempty incoming traffic. -/
theorem empty_patch_frame (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW)) (s : At Sheet)
    (h : (view x s).mobile=.empty)
    (noPrep : s∉reserved (round g x).prep)
    (noIncoming : ∀ c∈orderedData g (reserved (round g x).prep),
      c.destination=some s → (view x c.source).mobile=.empty) :
    view (patchPair (patch g x) x) s=view x s := by
  rw [BStarLongCommandData.round_transfer]
  apply fold_away
  intro a ha
  rcases List.mem_append.mp ha with hp|hd
  · exact noPrep (prep_lane_reserved _ _ _ _ hp)
  · obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp hd
    have hSlot := data_lane_claim g (view x) c s a hd
    obtain ⟨kind,u,v⟩ := c
    change s∈u::v.toList at hSlot
    cases kind with
    | ending =>
      have H : u=s := by
        unfold dataEffects at hd
        simp only at hd
        obtain ⟨b,_,he⟩ := List.mem_map.mp hd
        exact congrArg Prod.fst he
      subst u
      simp [dataEffects,endEffects,h] at hd
    | hop =>
      cases v with
      | none => simp [dataEffects] at hd
      | some v =>
        have E : s=u ∨ s=v := by simpa only [Option.toList_some,List.mem_cons,List.not_mem_nil,or_false] using hSlot
        have zero : (view x u).mobile=.empty := by
          rcases E with e|e
          · rw [←e]; exact h
          · subst v
            exact noIncoming ⟨.hop,u,some s⟩ hc rfl
        simp only [dataEffects, hopEffects, zero, if_true, List.map_nil, List.nil_append, List.not_mem_nil] at hd


variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Geometry/exclusion needed to carry the already saturated *one*
line, plus its drained upstream, through arbitrary later marks. -/
def FrozenRegion (P : Fin n → Sheet → Prop) (x : X) (e : Fin n) : Prop :=
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let rsv := reserved (round g raw).prep
  (∀ a : At Sheet,P (site e a.side) a.occurrence → a∉rsv) ∧
  ∀ c∈orderedData g rsv, ∀ v : At Sheet, P (site e v.side) v.occurrence →
      c.destination=some v → P (site e c.source.side) c.source.occurrence

theorem region_frame (P : Fin n → Sheet → Prop) (x : X) (e : Fin n)
    (sep : e≠rightNeighbor e) (scope : FrozenRegion hp P x e)
    (old : ∀ i sh,P i sh → (readLane (Sheet.index sh) (x i).long).mobile=.empty) :
    ∀ i sh,P i sh → readLane (Sheet.index sh) (step x e i).long=
      readLane (Sheet.index sh) (x i).long := by
  intro i sh hP
  have touch (s : Side) (H : site e s=i) :
      readLane (Sheet.index sh) (step x e i).long=readLane (Sheet.index sh) (x i).long := by
    subst i
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let a : At Sheet := ⟨s,sh⟩
    have bridge (v : At Sheet) : view raw v=readLane (Sheet.index v.occurrence) (x (site e v.side)).long := by
      obtain ⟨s,j⟩ := v
      cases s <;> rfl
    have H := empty_patch_frame g raw a
      ((congrArg Lane.mobile (bridge a)).trans (old _ _ hP)) (scope.1 a hP)
      (fun c hc dst => (congrArg Lane.mobile (bridge c.source)).trans
        (old _ _ (scope.2 c hc a hP dst)))
    have J := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e))
    have eq := (congrFun J a).trans H
    cases s <;> simpa [a,view,site,lane,BStarTrace.lane,Pair.map,AllSizeS1Geometry.step,Ne.symm sep] using eq
  by_cases l : i=e
  · exact touch .left l.symm
  · by_cases rr : i=rightNeighbor e
    · exact touch .right rr.symm
    · rw [show step x e i=x i from by simp [AllSizeS1Geometry.step,l,rr]]

/-- A drained region's whole decoded lanes are stable through the
original word whenever actual old incoming incidence stays in the
same region and no selected prep touches it. This permits the other
line to finish at a different mark. -/
theorem drained_word_frame (P : Fin n → Sheet → Prop) (x : X) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (old : ∀ i sh,P i sh → (readLane (Sheet.index sh) (x i).long).mobile=.empty)
    (scope : ∀ a e b,w=a++e::b → FrozenRegion hp P (play x a) e) :
    ∀ i sh,P i sh → readLane (Sheet.index sh) (play x w i).long=
      readLane (Sheet.index sh) (x i).long := by
  induction w generalizing x with
  | nil => intro _ _ _; rfl
  | cons e w ih =>
    have frame := region_frame hp P x e (sep e) (scope [] e w rfl) old
    intro i sh yes
    have J := ih (step x e) (fun i sh H => (congrArg Lane.mobile (frame i sh H)).trans (old i sh H))
      (fun a b c E => scope (e::a) b c (congrArg (List.cons e) E)) i sh yes
    exact J.trans (frame i sh yes)

#print axioms drained_word_frame

/-- No reservation at PC11 or later once authoritative preparation
provenance has identified the opcode of winners at this lane. -/
theorem no_prep_late (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (a : At Sheet)
    (pc : Nat) (late : 11≤pc)
    (ownerCode : ∀ offer∈(arbitration (round g raw).prep).1, offer.claim.lane=a →
      prepOf pc=some offer.claim.op) :
    a∉reserved (round g raw).prep := by
  intro mem
  obtain ⟨offer,win,loc⟩ := List.mem_map.mp mem
  have op := ownerCode offer win loc
  unfold prepOf at op
  split at op <;> first | contradiction | omega

#print axioms no_prep_late

/-- Checked negative control: the count-only Prefix can synthesize
the wrong first-receiver tag order while saturating both cells. -/
theorem counts_not_identity :
    ∃ s : Ledger Nat, Prefix [1,0] s ∧ (s.cells 1).retained≠none ∧
      heldFrom s.cells 0 2≠([1,0] : List Nat).reverse := by
  let a : Ledger Nat := Ledger.init [1,0]
  let b := a.releaseOne 1 [0]
  let c := b.releaseOne 0 []
  let d := c.receiveFirst 0
  let e := d.receiveFirst 1
  let f := e.transfer 0 0
  have aP : Prefix [1,0] a := .empty
  have bP : Prefix [1,0] b := .mark aP (.release a 1 [0] rfl)
  have cP : Prefix [1,0] c := .mark bP (.release b 0 [] rfl)
  have dP : Prefix [1,0] d := .mark cP (.first c 0 rfl (by decide +kernel))
  have eP : Prefix [1,0] e := .mark dP (.first d 1 rfl (by decide +kernel))
  have fP : Prefix [1,0] f := .mark eP (.transfer e 0 0 rfl rfl)
  exact ⟨f,fP,by decide +kernel,by decide +kernel⟩

#print axioms counts_not_identity
end L4.BStarCopyFenceSaturation

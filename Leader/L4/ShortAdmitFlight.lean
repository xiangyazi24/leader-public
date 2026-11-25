import Leader.L4.ShortAdmitForward

namespace L4.ShortAdmitFlight
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetForwardH2
open ShortResetCycle ShortResetChart ShortResetFlow ShortHelloAdmitCodec
open ShortAdmitForward ShortClearLaunch
set_option maxRecDepth 8192

variable {s n : Nat} {h : Fin n → Bool}

inductive State
  | forward (i : Nat) (won : Bool) (race : Nat)
  | reverse (i : Nat) (won : Bool)
  | done (won : Bool)

def next {n : Nat} {h : Fin n → Bool} (C : Chart h) (g : Nat) (e : Fin n) : State → State
  | .forward i won race =>
    match nextForward C g e i won race with
    | .fwd j w r => .forward j w r
    | .rev j w => .reverse j w
  | .reverse 0 w => if rightNeighbor e=C.root then .done w else .reverse 0 w
  | .reverse (i+1) w => if e=nextAt C.root i then .reverse i w else .reverse (i+1) w
  | .done w => .done w

def Live : State → Prop
  | .done _ => False
  | _ => True

def Flight (C : Chart h) (x : Raw s n) (g : Nat) (st : State) : Prop :=
  ShortHelloForward.NoGrants C.route x ∧
  match st with
  | .forward i w r => ShortAdmitFlightSync.Fwd C x i w r ∧ Valid g i w r
  | .reverse i w => ShortAdmitFlightSync.Rev C x i w
  | .done w => ClearIssue C x (if w then 3 else 0)

private theorem reverse_no_ask (C : Chart h) (x : Raw s n) (heads : ∀ q,header x q=h q)
    (i : Nat) (w : Bool) (F : ShortAdmitFlightSync.Rev C x i w) :
    ShortPreReadGrants.NoAsk C.route x := by
  intro j J H
  have hd : header x (nextAt C.root j)=true := (heads _).trans H
  apply ShortPreReadGrants.pre_read_no_ask
  have B := F.2.2 j J
  by_cases A : j<i
  · rw [if_pos A] at B
    have B := slot_of_bits C.route x j T trail_decode B
    change oldK (header x (nextAt C.root j)) _ _ = _ at B
    rw [hd] at B
    exact .inr (.inl B)
  · by_cases E : j=i
    · subst j
      rw [if_neg A,if_pos rfl] at B
      have B := slot_of_bits C.route x i (admitReply w) (fun g => decode_admit_reply g w) B
      change oldK (header x (nextAt C.root i)) _ _ = _ at B
      rw [hd] at B
      exact .inr (.inr (.inr (.inr (.inl ⟨w,B⟩))))
    · rw [if_neg A,if_neg E] at B
      have B := slot_of_bits C.route x j MISByteCodec.E empty_decode B
      change oldK (header x (nextAt C.root j)) _ _ = _ at B
      rw [hd] at B
      exact .inl B

theorem launch (C : Chart h) (x : Raw s n) (heads : ∀ q,header x q=h q)
    (g : Nat) (gp : 0<g) (A : ClearIssue C x 2) (G : ShortHelloForward.NoGrants C.route x) :
    Flight C (rawNext s x (RearTrace.predecessor C.root)) g (.forward 0 false 0) := by
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  have S : ShortPreReadGrants.NoAsk C.route x := by
    intro j J H
    have V := slot_of_bits C.route x j E empty_decode (A.2.1 j J)
    change oldK (header x (nextAt C.root j)) (x (nextAt C.root j)).mis1 (C.route.port j)=E at V
    have HH : header x (nextAt C.root j)=true := (heads _).trans H
    rw [HH] at V
    exact ShortPreReadGrants.pre_read_no_ask _ _ (.inl V)
  exact ⟨ShortPreReadGrants.no_ask_keeps_grants_absent C.route x _
    (edge_sep N _) heads G S, ShortAdmitFlightSync.actual_launch C x heads A,
    ⟨fun _ => rfl, by simp [show 0≠g by omega]⟩⟩

theorem active_step (Frames : WireFrames s n) (C : Chart h) (x : Raw s n)
    (heads : ∀ q,header x q=h q) (e : Fin n) (g : Nat) (gp : 0<g) (gL : g+1<C.L)
    (gates : ∀ j, j<C.L → (gated C x j=true ↔ j=g))
    (st : State) (L : Live st) (A : Flight C x g st) :
    Flight C (rawNext s x e) g (next C g e st) := by
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  cases st with
  | done w => exact False.elim L
  | forward i w r =>
    have V := forward_all_mark Frames C x heads e g gp gL gates i w r A.2.1 A.2.2
    have G := ShortPreReadGrants.no_ask_keeps_grants_absent C.route x e (edge_sep N e) heads A.1
      (forward_no_ask C x heads i w r A.2.1
        (valid_decode C x g i w r (gates _ A.2.1.1) A.2.2))
    cases E : nextForward C g e i w r <;>
      exact ⟨G, by simpa only [next,E,ValidState] using V⟩
  | reverse i w =>
    have G := ShortPreReadGrants.no_ask_keeps_grants_absent C.route x e (edge_sep N e) heads A.1
      (reverse_no_ask C x heads i w A.2)
    refine ⟨G,?_⟩
    have V := ShortAdmitReverse.returning_step C x N heads e i
      (ShortAdmitReverse.of_sync C x i w A.2)
    dsimp only at V
    cases i with
    | zero =>
      by_cases H : rightNeighbor e=C.root
      · simpa only [next,nextStage,if_pos H] using V
      · simpa only [next,if_neg H] using (show ShortAdmitFlightSync.Rev C (rawNext s x e) 0 w from
          ShortAdmitReverse.to_sync C _ 0 w (by simpa only [nextStage,if_neg H] using V))
    | succ j =>
      by_cases H : e=nextAt C.root j
      · simpa only [next,if_pos H] using
          ShortAdmitReverse.to_sync C _ j w (by simpa only [nextStage,if_pos H] using V)
      · simpa only [next,if_neg H] using
          ShortAdmitReverse.to_sync C _ (j+1) w (by simpa only [nextStage,if_neg H] using V)

/-- The gate location is a property of the persistent H2Ready geometry,
not an additional condition on the packet history. -/
def FixedGate (C : Chart h) (g : Nat) : Prop :=
  ∀ y : Raw s n, H2Ready y → (∀ q,header y q=h q) →
    ∀ j, j<C.L → (gated C y j=true ↔ j=g)

def scan (C : Chart h) (g : Nat) (w : List (Fin n)) (st : State) : State :=
  match w with
  | [] => st
  | e::q => scan C g q (next C g e st)

theorem active_run (Frames : WireFrames s n) (C : Chart h) (x : Raw s n)
    (N : 5≤n) (X : H2Ready x) (heads : ∀ q,header x q=h q)
    (g : Nat) (gp : 0<g) (gL : g+1<C.L) (gates : FixedGate (s:=s) C g)
    (st : State) (A : Flight C x g st) (w : List (Fin n))
    (live : ∀ (p : List (Fin n)) m q, w=p++m::q → Live (scan C g p st)) :
    Flight C (rawRun x w) g (scan C g w st) := by
  induction w generalizing x st with
  | nil => exact A
  | cons e w ih =>
    have h' : ∀ j,header (rawNext s x e) j=h j :=
      fun j=>(H1.raw_h1_selected_frozen N x e j X.1).trans (heads j)
    have B := active_step Frames C x heads e g gp gL (gates x X heads) st (live [] e w rfl) A
    exact ih (rawNext s x e) (h2_ready_closed N x e X) h' (next C g e st) B
      (fun p m q W => live (e::p) m q (congrArg (List.cons e) W))

theorem first_consume_is_clear (Frames : WireFrames s n) (C : Chart h) (x : Raw s n)
    (N : 5≤n) (X : H2Ready x) (heads : ∀ q,header x q=h q)
    (g : Nat) (gp : 0<g) (gL : g+1<C.L) (gates : FixedGate (s:=s) C g)
    (clear : ClearIssue C x 2) (grants : ShortHelloForward.NoGrants C.route x)
    (w : List (Fin n)) (won : Bool)
    (live : ∀ (p : List (Fin n)) m q, w=p++m::q → Live (scan C g p (.forward 0 false 0)))
    (done : scan C g w (.forward 0 false 0)=.done won) :
    let y := rawRun x (RearTrace.predecessor C.root::w)
    ShortHelloForward.NoGrants C.route y ∧ ClearIssue C y (if won then 3 else 0) := by
  let e := RearTrace.predecessor C.root
  have h' : ∀ j,header (rawNext s x e) j=h j :=
    fun j=>(H1.raw_h1_selected_frozen N x e j X.1).trans (heads j)
  have F := active_run Frames C (rawNext s x e) N (h2_ready_closed N x e X) h'
    g gp gL gates (.forward 0 false 0) (launch C x heads g gp clear grants) w live
  rw [done] at F
  exact F

#print axioms launch
#print axioms active_step
#print axioms active_run
#print axioms first_consume_is_clear
end L4.ShortAdmitFlight

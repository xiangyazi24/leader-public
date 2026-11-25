import Leader.L4.ShortHelloReverseSplice
import Leader.L4.ShortPreReadGrants
import Leader.L4.ShortResetHelloSplice

namespace L4.ShortHelloFlight
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetCycle ShortResetChart ShortResetForwardH2 ShortResetRow ShortResetFlow

def Live : Stage → Prop
  | .done => False
  | _ => True

/-- One HELLO frontier or reverse reply, and no grants anywhere on
this owner's chart. Done is exactly the canonical ADMIT launch cut. -/
def Flight {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (st : Stage) : Prop :=
  ShortHelloForward.NoGrants C.route x ∧
    match st with
    | .fwd i => ShortHelloForward.BeforeTurn C.route x i ∧
        ShortHelloForward.ClearSuffix C.route x i
    | .rev i => ShortHelloReverseChart.Returning C x i
    | .done => ShortClearLaunch.ClearIssue C x 2

theorem actual_launch {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (heads : ∀ j,header x j=h j)
    (P : ShortResetHelloSplice.Parked C x) :
    Flight C (rawNext s x (RearTrace.predecessor C.root)) (.fwd 0) := by
  let e := RearTrace.predecessor C.root
  let y := rawNext s x e
  have A : ShortClearLaunch.ClearIssue C x 1 :=
    P.1
  have F := ShortClearLaunch.clean_launch C x heads 1 A
  have G : ShortHelloForward.NoGrants C.route x := P.2
  have S : ShortPreReadGrants.NoAsk C.route x := by
    intro j J H
    have V := slot_of_bits C.route x j E empty_decode (P.1.2.1 j J)
    change oldK (header x (nextAt C.root j)) (x (nextAt C.root j)).mis1 (C.route.port j)=E at V
    have Hd : header x (nextAt C.root j)=true := (heads _).trans H
    rw [Hd] at V
    exact ShortPreReadGrants.pre_read_no_ask _ _ (.inl V)
  refine ⟨ShortPreReadGrants.no_ask_keeps_grants_absent C.route x e
    (edge_sep (by have := C.positive; have := C.length_lt; omega) e) heads G S,
    ⟨C.positive,⟨F.1,F.2.1⟩,fun j J=>False.elim (by omega),F.2.2.1⟩,F.2.2.2⟩

theorem active_step {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (heads : ∀ j,header x j=h j) (e : Fin n) (st : Stage)
    (L : Live st) (A : Flight C x st) :
    Flight C (rawNext s x e) (nextStage C e st) := by
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  cases st with
  | done => exact False.elim L
  | fwd i =>
    have F := ShortHelloReverseSplice.forward_all_mark C x heads e i A.2.1
    have S := ShortHelloForward.clear_suffix_step C.route x e (edge_sep N e) heads i A.2.2
    refine ⟨ShortHelloForward.no_grants_step C.route x e (edge_sep N e) heads i A.2.1 A.2.2 A.1,?_⟩
    by_cases M : e=nextAt C.root i
    · by_cases J : i+1<C.L
      · simp only [nextStage,if_pos M,if_pos J] at F ⊢
        exact ⟨F,by simpa only [ShortHelloForward.ahead,if_pos (show e=nextAt C.route.root i from M)] using S⟩
      · simpa only [nextStage,if_pos M,if_neg J] using F
    · simp only [nextStage,if_neg M] at F ⊢
      exact ⟨F,by simpa only [ShortHelloForward.ahead,if_neg (show e≠nextAt C.route.root i from M)] using S⟩
  | rev i =>
    have F := ShortHelloReverseChart.returning_step C x N heads e i A.2
    have G : ShortPreReadGrants.NoAsk C.route x := by
      intro j J H
      have K : bits C.route x j=encode (ShortHelloReverseChart.trailAt i j) := A.2.2.2 j J
      have V := slot_of_bits C.route x j (ShortHelloReverseChart.trailAt i j) (by
        intro gate
        unfold ShortHelloReverseChart.trailAt
        split
        · exact trail_decode gate
        · split
          · exact (ShortHelloAdmitCodec.decode_hello gate).2
          · exact empty_decode gate) K
      change oldK (header x (nextAt C.route.root j)) (x (nextAt C.route.root j)).mis1
        (C.route.port j)=_ at V
      rw [(heads _).trans H] at V
      apply ShortPreReadGrants.pre_read_no_ask
      by_cases W : j<i
      · exact .inr (.inl (by simpa [ShortHelloReverseChart.trailAt,W] using V))
      by_cases W' : j=i
      · exact .inr (.inr (.inr (.inl (by simpa [ShortHelloReverseChart.trailAt,W,W'] using V))))
      · exact .inl (by simpa [ShortHelloReverseChart.trailAt,W,W'] using V)
    refine ⟨ShortPreReadGrants.no_ask_keeps_grants_absent C.route x e (edge_sep N e) heads A.1 G,?_⟩
    dsimp only at F
    cases S : nextStage C e (.rev i) with
    | fwd j => rw [S] at F; exact False.elim F
    | rev j => simpa only [S] using F
    | done =>
      rw [S] at F
      exact ⟨by decide,F.1,F.2.1,F.2.2⟩

/-- Track the checked stage on the unchanged raw schedule; stop at
the first .done, rather than silently ignoring later own-door events. -/
def scan {n : Nat} {h : Fin n → Bool} (C : Chart h) (w : List (Fin n))
    (st : Stage) : Stage :=
  match w with
  | [] => st
  | e::tail => scan C tail (nextStage C e st)

theorem active_run {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (N : 5≤n) (X : H2Ready x) (heads : ∀ j,header x j=h j)
    (st : Stage) (A : Flight C x st) (w : List (Fin n))
    (live : ∀ (p : List (Fin n)) m q, w=p++m::q → Live (scan C p st)) :
    Flight C (rawRun x w) (scan C w st) := by
  induction w generalizing x st with
  | nil => exact A
  | cons e w ih =>
    have h' : ∀ j,header (rawNext s x e) j=h j :=
      fun j=>(H1.raw_h1_selected_frozen N x e j X.1).trans (heads j)
    have B := active_step C x heads e st (live [] e w rfl) A
    exact ih (rawNext s x e) (h2_ready_closed N x e X) h' (nextStage C e st) B
      (fun p m q W => live (e::p) m q (congrArg (List.cons e) W))

/-- Starting at a genuine RESET0's parked state, a sampled own launch
and the stopped HELLO tape give an empty, grant-free ADMIT ISSUE2. -/
theorem first_consume_is_clean_admit {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (N : 5≤n) (X : H2Ready x) (heads : ∀ j,header x j=h j)
    (P : ShortResetHelloSplice.Parked C x) (w : List (Fin n))
    (live : ∀ (p : List (Fin n)) m q, w=p++m::q → Live (scan C p (.fwd 0)))
    (done : scan C w (.fwd 0)=.done) :
    let y := rawRun x (RearTrace.predecessor C.root::w)
    ShortHelloForward.NoGrants C.route y ∧ ShortClearLaunch.ClearIssue C y 2 := by
  let e := RearTrace.predecessor C.root
  have h' : ∀ j,header (rawNext s x e) j=h j :=
    fun j=>(H1.raw_h1_selected_frozen N x e j X.1).trans (heads j)
  have F := active_run C (rawNext s x e) N (h2_ready_closed N x e X) h'
    (.fwd 0) (actual_launch C x heads P) w live
  rw [done] at F
  exact F

end L4.ShortHelloFlight

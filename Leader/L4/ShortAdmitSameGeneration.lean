import Leader.L4.ShortAdmitFlight
import Leader.L4.ShortAdmitInert

namespace L4.ShortAdmitSameGeneration
open AllSizeProtocol PhysicalCustody MISByteCodec ShortResetMIS1Ring ShortResetRow
open ShortResetChart ShortResetCycle ShortResetForwardH2 ShortHelloAdmitCodec
open ShortAdmitForward ShortAdmitInert ShortAdmitFlight ShortClearLaunch

theorem wire_frames {s n : Nat} : WireFrames s n := by
  constructor
  · intro x e j k won race sep dst trail trailWire wire old norace
    have A := trail_before_live x e sep j k dst trail (.inr (by rw [old]; rfl))
    have no : (oldK (header x e) (x e).mis1 j).tag≠2 := by rw [trail]; decide
    refine ⟨A.trans trailWire,?_⟩
    generalize H : atGate (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k = gate
    cases gate
    · have R : race=0 := by
        exact norace H
      subst race
      exact (incoming_ungated x e sep j k dst no _ old rfl rfl rfl H).trans wire
    · by_cases R : race=1 ∨ race=3
      · have T := ShortAdmitMIS1Ring.parked_admit_right_raw x e sep j k dst no _ old rfl rfl rfl H R
        rcases R with rfl|rfl <;> exact T
      · have r1 : race≠1 := fun E => R (.inl E)
        have r3 : race≠3 := fun E => R (.inr E)
        have T := incoming_race245 x e sep j k dst no _ old rfl rfl rfl H ⟨r1,r3⟩
        simpa [ingressRace,r1,r3] using T.trans wire
  · intro x e j k sep dst old gate left wire
    have right := ShortEmptyOwnership.canonical_empty_oldK (header x (rightNeighbor e)) _ _ wire
    exact ⟨(outgoing_race3 x e sep j _ old rfl rfl rfl gate rfl).trans left,
      (parked_outgoing_right_empty x e sep j k dst _ old rfl rfl rfl gate (by decide)
        right wire).trans wire.symm⟩
  · intro x e j k r sep dst old gate race right wire
    exact parked_outgoing_right_empty x e sep j k dst _ old rfl rfl rfl gate
      (by rcases race with rfl|rfl|rfl <;> decide) right wire


variable {s n : Nat} {h : Fin n → Bool}

private theorem raw_app (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (rawNext s x e)

private theorem clear_wait (C : Chart h) (x : Raw s n) (N : 5≤n) (X : H2Ready x)
    (heads : ∀ q,header x q=h q) (o : Nat) (A : ClearIssue C x o)
    (G : ShortHelloForward.NoGrants C.route x) (w : List (Fin n))
    (stop : RearTrace.predecessor C.root ∉ w) :
    ClearIssue C (rawRun x w) o ∧ ShortHelloForward.NoGrants C.route (rawRun x w) := by
  induction w generalizing x with
  | nil => exact ⟨A,G⟩
  | cons e w ih =>
    have other : e≠RearTrace.predecessor C.root := fun E=>stop (by simp [E])
    have S : ShortPreReadGrants.NoAsk C.route x := by
      intro j J H
      have V := slot_of_bits C.route x j E ShortResetFlow.empty_decode (A.2.1 j J)
      change oldK (header x (nextAt C.root j)) (x (nextAt C.root j)).mis1 (C.route.port j)=E at V
      have hh : header x (nextAt C.root j)=true := (heads _).trans H
      rw [hh] at V
      exact ShortPreReadGrants.pre_read_no_ask _ _ (.inl V)
    have G' := ShortPreReadGrants.no_ask_keeps_grants_absent C.route x _
      (edge_sep (by omega) e) heads G S
    have head' := fun j=>(H1.raw_h1_selected_frozen N x e j X.1).trans (heads j)
    exact ih _ (h2_ready_closed N x e X) head' (clear_issue_nondoor C x heads o A e other)
      G' (fun E=>stop (List.mem_cons_of_mem _ E))

/-- Actual forward and reverse ADMIT processing along the same stopped raw
tape. There are no local-row frame hypotheses: every relevant row is checked. -/
theorem first_admit_consume {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (N : 5≤n) (X : H2Ready x) (heads : ∀ q,header x q=h q)
    (g : Nat) (gp : 0<g) (gL : g+1<C.L) (gates : FixedGate (s:=s) C g)
    (clear : ClearIssue C x 2) (grants : ShortHelloForward.NoGrants C.route x)
    (w : List (Fin n)) (won : Bool)
    (live : ∀ (p : List (Fin n)) m q, w=p++m::q → Live (scan C g p (.forward 0 false 0)))
    (done : scan C g w (.forward 0 false 0)=.done won) :
    let y := rawRun x (RearTrace.predecessor C.root::w)
    ShortHelloForward.NoGrants C.route y ∧ ClearIssue C y (if won then 3 else 0) :=
  first_consume_is_clear wire_frames C x N X heads g gp gL gates clear grants w won live done

/-- E2. From the actual parked owner, stop at that HELLO's first consume,
then that ADMIT's first consume. Intervening nondoor marks stay on the
original tape. The synchronized single frontier/reply and the only real
ADMIT gate supply the payload; no inherited response is counted. -/
theorem mis1_admit_same_generation_to_clear_issue3_or_reset
    (C : Chart h) (x : Raw s n) (N : 5≤n) (X : H2Ready x) (heads : ∀ q,header x q=h q)
    (P : ShortResetHelloSplice.Parked C x)
    (g : Nat) (gp : 0<g) (gL : g+1<C.L) (gates : FixedGate (s:=s) C g)
    (before hello middle admit : List (Fin n)) (won : Bool)
    (waiting1 : RearTrace.predecessor C.root ∉ before)
    (helloLive : ∀ (p : List (Fin n)) m q, hello=p++m::q →
      ShortHelloFlight.Live (ShortHelloFlight.scan C p (.fwd 0)))
    (helloDone : ShortHelloFlight.scan C hello (.fwd 0)=.done)
    (waiting2 : RearTrace.predecessor C.root ∉ middle)
    (admitLive : ∀ (p : List (Fin n)) m q, admit=p++m::q →
      Live (scan C g p (.forward 0 false 0)))
    (admitDone : scan C g admit (.forward 0 false 0)=.done won) :
    let d := RearTrace.predecessor C.root
    let y := rawRun x (before ++ (d::hello) ++ middle ++ (d::admit))
    ShortHelloForward.NoGrants C.route y ∧ ClearIssue C y (if won then 3 else 0) := by
  dsimp only
  let d := RearTrace.predecessor C.root
  let x1 := rawRun x before
  let x2 := rawRun x1 (d::hello)
  let x3 := rawRun x2 middle
  have ready (y : Raw s n) (Y : H2Ready y) (H : ∀ q,header y q=h q) (w : List (Fin n)) :
      H2Ready (rawRun y w) ∧ ∀ q,header (rawRun y w) q=h q :=
    ⟨ready_run N y Y w,fun q => ((header_run N y Y.1 w).2 q).trans (H q)⟩
  have R1 := ready x X heads before
  have P1 := clear_wait C x N X heads 1 P.1 P.2 before waiting1
  have H1 := ShortHelloFlight.first_consume_is_clean_admit C x1 N R1.1 R1.2 P1 hello helloLive helloDone
  have R2 := ready x1 R1.1 R1.2 (d::hello)
  have R3 := ready x2 R2.1 R2.2 middle
  have P3 := clear_wait C x2 N R2.1 R2.2 2 H1.2 H1.1 middle waiting2
  have T := first_admit_consume C x3 N R3.1 R3.2 g gp gL gates P3.1 P3.2 admit won admitLive admitDone
  rw [raw_app,raw_app,raw_app]
  exact T

#print axioms wire_frames
#print axioms first_admit_consume
#print axioms mis1_admit_same_generation_to_clear_issue3_or_reset
end L4.ShortAdmitSameGeneration

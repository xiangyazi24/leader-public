import Leader.L4.ShortFiveWinningWord
import Leader.L4.ShortAdmitSameGeneration

namespace L4.ShortFiveWordEntry
open PhysicalCustody ShortResetMIS1Ring ShortResetForwardH2 ShortResetCycle ShortResetChart
open ShortFiveWinningWord ShortAdmitSameGeneration ShortAdmitForward ShortClearLaunch

variable {n : Nat} {h : Fin n → Bool}

abbrev HScan (C : Chart h) := ShortHelloFlight.scan C
abbrev AScan (C : Chart h) (g : Nat) := ShortAdmitFlight.scan C g

private theorem h_app (C : Chart h) (u v : List (Fin n)) (st : Stage) :
    HScan C (u++v) st=HScan C v (HScan C u st) := by
  induction u generalizing st with
  | nil => rfl
  | cons e u ih => exact ih (nextStage C e st)

private theorem a_app (C : Chart h) (g : Nat) (u v : List (Fin n)) (st : ShortAdmitFlight.State) :
    AScan C g (u++v) st=AScan C g v (AScan C g u st) := by
  induction u generalizing st with
  | nil => rfl
  | cons e u ih => exact ih (ShortAdmitFlight.next C g e st)

private theorem h_fwd (C : Chart h) (i k : Nat) (I : i+k<C.L) :
    HScan C ((List.range' i k).map (nextAt C.root)) (.fwd i)=.fwd (i+k) := by
  induction k generalizing i with
  | zero => simp [ShortHelloFlight.scan]
  | succ k ih =>
    rw [List.range'_succ,List.map_cons]
    change HScan C ((List.range' (i+1) k).map (nextAt C.root))
      (nextStage C (nextAt C.root i) (.fwd i))=_
    rw [show nextStage C (nextAt C.root i) (.fwd i) = .fwd (i+1) by
      simp [nextStage,show i+1<C.L by omega]]
    exact (ih (i+1) (by omega)).trans (congrArg Stage.fwd (by omega))

private theorem a_fwd (C : Chart h) (g i k : Nat) (I : i+k<C.L)
    (S : i+k<g ∨ g<i) (w : Bool) :
    AScan C g ((List.range' i k).map (nextAt C.root)) (.forward i w 0)=.forward (i+k) w 0 := by
  induction k generalizing i with
  | zero => simp [ShortAdmitFlight.scan]
  | succ k ih =>
    rw [List.range'_succ,List.map_cons]
    change AScan C g ((List.range' (i+1) k).map (nextAt C.root))
      (ShortAdmitFlight.next C g (nextAt C.root i) (.forward i w 0))=_
    have A : i≠g := by rcases S with S|S <;> omega
    have B : i+1≠g := by rcases S with S|S <;> omega
    rw [show ShortAdmitFlight.next C g (nextAt C.root i) (.forward i w 0) = .forward (i+1) w 0 by
      simp [ShortAdmitFlight.next,nextForward,A,B,show i+1<C.L by omega]]
    exact (ih (i+1) (by omega) (by rcases S with S|S <;> omega)).trans
      (congrArg (fun p => ShortAdmitFlight.State.forward p w 0) (by omega))

private theorem h_rev (C : Chart h) (k : Nat) :
    HScan C ((List.range k).reverse.map (nextAt C.root)) (.rev k)=.rev 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ,List.reverse_append,List.map_append]
    simpa [ShortHelloFlight.scan,nextStage] using ih

private theorem a_rev (C : Chart h) (g k : Nat) (won : Bool) :
    AScan C g ((List.range k).reverse.map (nextAt C.root)) (.reverse k won)=.reverse 0 won := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ,List.reverse_append,List.map_append]
    simpa [ShortAdmitFlight.scan,ShortAdmitFlight.next] using ih

private theorem prefix_before_last {A : Type} (v p : List A) (d e : A) (q : List A)
    (E : v++[d]=p++e::q) : ∃ t, v=p++t := by
  induction p generalizing v with
  | nil => exact ⟨v,rfl⟩
  | cons a p ih =>
    cases v with
    | nil =>
      have L := congrArg List.length E
      simp at L
    | cons b v =>
      have ⟨B,R⟩ := List.cons.inj E
      obtain ⟨t,T⟩ := ih v R
      exact ⟨t,by rw [B,T]; rfl⟩

private theorem h_done (C : Chart h) (v : List (Fin n)) : HScan C v .done=.done := by
  induction v with
  | nil => rfl
  | cons e v ih => exact ih

private theorem a_done (C : Chart h) (g : Nat) (v : List (Fin n)) (w : Bool) :
    AScan C g v (.done w)=.done w := by
  induction v with
  | nil => rfl
  | cons e v ih => exact ih

private theorem h_live_before_last (C : Chart h) (v : List (Fin n)) (start : Stage)
    (V : ShortHelloFlight.Live (HScan C v start)) (d : Fin n) :
    ∀ (p : List (Fin n)) e q, v++[d]=p++e::q → ShortHelloFlight.Live (HScan C p start) := by
  intro p e q E
  have sub := prefix_before_last v p d e q E
  obtain ⟨t,F⟩ := sub
  rw [F,h_app] at V
  cases O : HScan C p start
  · trivial
  · trivial
  · rw [O] at V
    rw [h_done] at V
    exact V

private theorem a_live_before_last (C : Chart h) (g : Nat) (v : List (Fin n))
    (start : ShortAdmitFlight.State) (V : ShortAdmitFlight.Live (AScan C g v start)) (d : Fin n) :
    ∀ (p : List (Fin n)) e q, v++[d]=p++e::q → ShortAdmitFlight.Live (AScan C g p start) := by
  intro p e q E
  have sub := prefix_before_last v p d e q E
  obtain ⟨t,F⟩ := sub
  rw [F,a_app] at V
  cases O : AScan C g p start
  · trivial
  · trivial
  · rw [O] at V
    rw [a_done] at V
    exact V

def helloBody (C : Chart h) : List (Fin n) :=
  (List.range C.L).map (nextAt C.root) ++ (List.range (C.L-1)).reverse.map (nextAt C.root)

theorem hello_body_scans (C : Chart h) : HScan C (helloBody C) (.fwd 0)=.rev 0 := by
  have P := C.positive
  have E : C.L=C.L-1+1 := by omega
  have H : HScan C ((List.range C.L).map (nextAt C.root)) (.fwd 0)=.rev (C.L-1) := by
    conv => lhs; arg 2; rw [E]
    rw [List.range_succ,List.map_append,h_app,List.range_eq_range']
    have V := h_fwd C 0 (C.L-1) (by omega)
    simp only [Nat.zero_add] at V
    rw [V]
    simp [ShortHelloFlight.scan,nextStage,show ¬ C.L-1+1<C.L by omega]
  rw [helloBody,h_app,H,h_rev]


def admitBody (C : Chart h) (g : Nat) : List (Fin n) :=
  (List.range g).map (nextAt C.root) ++
  [nextAt C.root g,nextAt C.root (g-1),nextAt C.root g] ++
  (List.range' (g+1) (C.L-(g+1))).map (nextAt C.root) ++
  (List.range (C.L-1)).reverse.map (nextAt C.root)

theorem admit_body_scans (C : Chart h) (g : Nat) (gp : 0<g) (gL : g+1<C.L) :
    AScan C g (admitBody C g) (.forward 0 false 0)=.reverse 0 true := by
  have arrive : AScan C g ((List.range g).map (nextAt C.root)) (.forward 0 false 0) =
      .forward g false 1 := by
    have E : g=g-1+1 := by omega
    conv => lhs; arg 3; rw [E]
    rw [List.range_succ,List.map_append,a_app,List.range_eq_range']
    have A := a_fwd C g 0 (g-1) (by omega) (.inl (by omega)) false
    simp only [Nat.zero_add] at A
    rw [A]
    simp [ShortAdmitFlight.scan,ShortAdmitFlight.next,nextForward,show g-1≠g by omega,
      show g<C.L by omega,show g-1+1=g by omega]
  have race : AScan C g [nextAt C.root g,nextAt C.root (g-1),nextAt C.root g]
      (.forward g false 1)=.forward (g+1) true 0 := by
    have E : rightNeighbor (nextAt C.root (g-1))=nextAt C.root g := by
      conv => rhs; rw [show g=g-1+1 by omega]
      rfl
    have K : nextAt C.root (g-1)≠nextAt C.root g := by
      intro K
      have eq := nextAt_injective_under C.root _ _ (by have := C.length_lt; omega)
        (by have := C.length_lt; omega) K
      omega
    simp [ShortAdmitFlight.scan,ShortAdmitFlight.next,nextForward,ingressRace,E,K]
  have toTurn : AScan C g ((List.range' (g+1) (C.L-(g+1))).map (nextAt C.root))
      (.forward (g+1) true 0)=.reverse (C.L-1) true := by
    have e : C.L-(g+1)=(C.L-1-(g+1))+1 := by omega
    rw [e,List.range'_1_concat,List.map_append,a_app]
    have A := a_fwd C g (g+1) (C.L-1-(g+1)) (by omega) (.inr (by omega)) true
    rw [show g+1+(C.L-1-(g+1))=C.L-1 by omega] at A ⊢
    rw [A]
    simp [ShortAdmitFlight.scan,ShortAdmitFlight.next,nextForward,show C.L-1≠g by omega,
      show ¬ C.L-1+1<C.L by omega]
  rw [admitBody,a_app,a_app,a_app,arrive,race,toTurn,a_rev]

private theorem hello_end (C : Chart h) :
    HScan C (helloBody C++[RearTrace.predecessor C.root]) (.fwd 0)=.done := by
  rw [h_app,hello_body_scans]
  simp [ShortHelloFlight.scan,nextStage,RearTrace.right_predecessor]

private theorem admit_end (C : Chart h) (g : Nat) (gp : 0<g) (gl : g+1<C.L) :
    AScan C g (admitBody C g++[RearTrace.predecessor C.root]) (.forward 0 false 0)=.done true := by
  rw [a_app,admit_body_scans C g gp gl]
  simp [ShortAdmitFlight.scan,ShortAdmitFlight.next,RearTrace.right_predecessor]

/-- First two literal tours of the five-Parked witness. The gate winner
is true on this very physical tape, not a nondeterministic choice. -/
theorem winning_entry {s : Nat} (C : Chart h) (x : Raw s n)
    (N : 5≤n) (X : H2Ready x) (heads : ∀ q,header x q=h q)
    (P : ShortResetHelloSplice.Parked C x)
    (g : Nat) (gp : 0<g) (gL : g+1<C.L) (gates : ShortAdmitFlight.FixedGate (s:=s) C g) :
    let y := rawRun x (tour C ++ admit C g)
    ShortHelloForward.NoGrants C.route y ∧ ClearIssue C y 3 := by
  let d := RearTrace.predecessor C.root
  have H : ShortHelloFlight.Live (HScan C (helloBody C) (.fwd 0)) := by
    rw [hello_body_scans]; trivial
  have A : ShortAdmitFlight.Live (AScan C g (admitBody C g) (.forward 0 false 0)) := by
    rw [admit_body_scans C g gp gL]; trivial
  have P := mis1_admit_same_generation_to_clear_issue3_or_reset C x N X heads P
    g gp gL gates [] (helloBody C++[d]) [] (admitBody C g++[d]) true
    (by simp) (h_live_before_last C _ _ H d) (hello_end C)
    (by simp) (a_live_before_last C g _ _ A d) (admit_end C g gp gL)
  simpa [tour,admit,helloBody,admitBody,d,List.append_assoc] using P

#print axioms hello_body_scans
#print axioms admit_body_scans
#print axioms winning_entry
end L4.ShortFiveWordEntry

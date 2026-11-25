import Leader.L4.BStarNativeNeedLift

namespace L4.BStarNeedCompletionInvariant
open L4.Compiler.Native
open BStarNativePortGeometry BStarH6WordChart BStarAcquireAnchors

/-- On every non-NEED edit, the literal snapshot does not depend on the
selected BIT, including phase 1 when the anchor is absent or z is nonzero. -/
theorem phase_ignores_unused (B phase : Nat) (L C R : Snapshot) (a b : Bool)
    (N : ¬ (phase=1 ∧ C.anchor=true ∧ C.z=0)) :
    phaseUpdate B phase L C R a = phaseUpdate B phase L C R b := by
  unfold phaseUpdate
  split
  · rfl
  · have H : ¬ (C.anchor=true ∧ C.z=0) := fun K=>N ⟨rfl,K⟩
    cases A : C.anchor with
    | false => simp only [Bool.false_and]
    | true =>
      have Z : C.z≠0 := fun hz=>H ⟨A,hz⟩
      simp only [if_neg Z]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem finish_ignores_unused (B : Nat) (L C R : NativeRecord) (act : ClockAction)
    (a b : Bool) (N : pendingNeed act C=false) :
    finishNative B L C R act a=finishNative B L C R act b := by
  cases act
  all_goals try rfl
  rename_i t
  have H : ¬ (C.tick%32=1 ∧ C.curr.anchor=true ∧ C.curr.z=0) := by
    intro Y
    simp [pendingNeed,Y.1,Y.2.1,Y.2.2] at N
  simp only [finishNative]
  rw [phase_ignores_unused B _ _ _ _ a b H]

noncomputable def consults {n r : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (before : Header h→NativeRecord) (center : Header h) : Bool :=
  let l := before (neighborHeader hh center 0)
  let c := before (neighborHeader hh center 1)
  let z := before (neighborHeader hh center 2)
  pendingNeed (nativeClock (modulus r) l c z) c

theorem activate_agrees {n r : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (before : Header h→NativeRecord) (center : Header h) (a b : Bool)
    (H : consults (r:=r) hh before center=true → a=b) :
    activate (r:=r) hh before center a=activate (r:=r) hh before center b := by
  cases N : consults (r:=r) hh before center with
  | true => rw [H N]
  | false =>
    funext i
    by_cases E : i=center
    · simp only [activate,if_pos E]
      exact finish_ignores_unused _ _ _ _ _ a b N
    · simp only [activate,if_neg E]

/-- Compare two streams of supplied BITs on the same marked decoded path.
The current record on the reference path determines which value is relevant. -/
def AgreesOnNeed {n r : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true) :
    (Header h→NativeRecord)→List (Header h × Bool × Bool)→Prop
  | _, [] => True
  | x, (center,a,b)::w =>
      (consults (r:=r) hh x center=true→a=b) ∧
      AgreesOnNeed (r:=r) hh (activate (r:=r) hh x center a) w

noncomputable def recordTrace {n r : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (alt : Bool) : (Header h→NativeRecord)→List (Header h × Bool × Bool)→
      List (Header h→NativeRecord)
  | x, [] => [x]
  | x, (center,a,b)::w =>
      x::recordTrace (r:=r) hh alt (activate (r:=r) hh x center (if alt then b else a)) w

/-- Completing all unused bits arbitrarily leaves every decoded snapshot
of the native path unchanged, not just its terminal record. -/
theorem recordTrace_agrees {n r : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (x : Header h→NativeRecord) (w : List (Header h × Bool × Bool))
    (A : AgreesOnNeed (r:=r) hh x w) :
    recordTrace (r:=r) hh false x w=recordTrace (r:=r) hh true x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    obtain ⟨i,a,b⟩ := e
    have A₁ := A.1
    have A₂ := A.2
    simp only [recordTrace, Bool.false_eq_true, if_false, if_true, List.cons.injEq, true_and]
    rw [←activate_agrees (r:=r) hh x i a b A₁]
    exact ih _ A₂

end L4.BStarNeedCompletionInvariant

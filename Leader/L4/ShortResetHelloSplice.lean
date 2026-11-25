import Leader.L4.ShortResetReleased
import Leader.L4.ShortHelloForward
import Leader.L4.ShortClearLaunch

namespace L4.ShortResetHelloSplice
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetForwardH2 ShortResetFlow
open ShortResetRow ShortResetReleased ShortClearLaunch ShortEmptyOwnership
open ShortHelloForward

def Parked {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) : Prop :=
  ClearIssue C x 1 ∧ NoGrants C.route x

/-- The complete state of one genuinely consumed RESET0 starts a
grant-free, empty ISSUE1 owner. This is owner-local, not a statement
about any of the overlapping owners' slots. -/
theorem parked_after_consume {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (K : Complete C x) (G : Released C x .done) : Parked C x :=
  ⟨⟨by decide,K.1,K.2.1,K.2.2⟩,fun i I H=>G i I H trivial⟩

private theorem empty_no_grant_birth {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (heads : ∀ j,header x j=h j) (A : Clear C x) (G : NoGrants C.route x)
    (e : Fin n) : NoGrants C.route (rawNext s x e) := by
  have N := C.length_lt
  have P := C.positive
  intro i I H
  let j := C.route.port i
  let q := nextAt C.root i
  have hd : header x q=true := (heads _).trans H
  have tok : oldK true (x q).mis1 j=E := canonical_empty_oldK _ _ _ (A i I)
  refine ShortGrantPersistence.absent_until_ask x e q j (edge_sep (by omega) e)
    hd (G i I H) (fun _=>?_ )
  change ((oldK true (x q).mis1 j).tag==2 && !(oldK true (x q).mis1 j).fault &&
    (oldK true (x q).mis1 j).opcode==3)=false
  rw [tok]
  rfl

theorem parked_nondoor {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (heads : ∀ j,header x j=h j) (A : Parked C x)
    (e : Fin n) (E : e≠RearTrace.predecessor C.root) :
    Parked C (rawNext s x e) :=
  ⟨clear_issue_nondoor C x heads 1 A.1 e E,empty_no_grant_birth C x heads A.1.2.1 A.2 e⟩

def Flying {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) : Prop :=
  ∃ i, BeforeTurn C.route x i ∧ ClearSuffix C.route x i ∧ NoGrants C.route x

theorem launch_grant_free {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (heads : ∀ j,header x j=h j) (A : Parked C x) :
    Flying C (rawNext s x (RearTrace.predecessor C.root)) := by
  have K := clean_launch C x heads 1 A.1
  exact ⟨0,⟨C.positive,⟨K.1,K.2.1⟩,fun i I=>False.elim (by omega),K.2.2.1⟩,
    K.2.2.2,empty_no_grant_birth C x heads A.1.2.1 A.2 _⟩

/-- Left-rival case: the original sampled suffix without its own door
preserves the entire grant-free clean ISSUE1 state. -/
theorem parked_without_door {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (x : Raw s n) (X : H2Ready x) (heads : ∀ j,header x j=h j)
    (A : Parked C x) (w : List (Fin n)) (noDoor : RearTrace.predecessor C.root ∉ w) :
    Parked C (rawRun x w) := by
  induction w generalizing x with
  | nil => exact A
  | cons e w ih =>
    have E : e≠RearTrace.predecessor C.root := fun h=>noDoor (by simp [h])
    exact ih (rawNext s x e) (h2_ready_closed N x e X)
      (fun j=>(H1.raw_h1_selected_frozen N x e j X.1).trans (heads j))
      (parked_nondoor C x heads A e E) (fun h=>noDoor (List.mem_cons_of_mem e h))

/-- Right-rival case: it may launch HELLO, but until its terminal is
sampled it can neither leave WAIT1 nor reacquire a grant. -/
theorem parked_or_flying_without_terminal {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (x : Raw s n) (X : H2Ready x) (heads : ∀ j,header x j=h j)
    (A : Parked C x) (w : List (Fin n)) (noTerminal : terminalMark C.route ∉ w) :
    Parked C (rawRun x w) ∨ Flying C (rawRun x w) := by
  induction w generalizing x with
  | nil => exact .inl A
  | cons e w ih =>
    have Y := h2_ready_closed N x e X
    have H := fun j=>(H1.raw_h1_selected_frozen N x e j X.1).trans (heads j)
    have E : terminalMark C.route ∉ w := fun z=>noTerminal (List.mem_cons_of_mem e z)
    by_cases D : e=RearTrace.predecessor C.root
    · have F : Flying C (rawNext s x e) := by rw [D]; exact launch_grant_free C x heads A
      obtain ⟨i,B,Q,G⟩ := F
      exact .inr (clear_grant_free_before_terminal C.route N _ Y H i B Q G w E)
    · exact ih (rawNext s x e) Y H (parked_nondoor C x heads A e D) E

/-- Whole splice from old ISSUE0 through a genuine RESET0 round trip on
the actual tape, then retention of a grant-free rival under the
route's terminal omission. -/
theorem from_reset_then_without_terminal {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (x : Raw s n) (X : H2Ready x) (heads : ∀ j,header x j=h j)
    (I : ShortActualIssueClock.Issuable C x) (reset tail : List (Fin n))
    (B : BeforeConsume C (.fwd 0) reset) (D : stageRun C (.fwd 0) reset=.done)
    (noTerminal : terminalMark C.route ∉ tail) :
    let y := rawRun (rawRun x (RearTrace.predecessor C.root :: reset)) tail
    Parked C y ∨ Flying C y := by
  let w := RearTrace.predecessor C.root :: reset
  obtain ⟨K,G⟩ := released_from_actual_issue C N x X heads I reset B D
  have keep (v : List (Fin n)) (z : Raw s n) (A : H2Ready z)
      (H : ∀ j,header z j=h j) :
      H2Ready (rawRun z v) ∧ ∀ j,header (rawRun z v) j=h j := by
    induction v generalizing z with
    | nil => exact ⟨A,H⟩
    | cons e v ih =>
      exact ih _ (h2_ready_closed N z e A)
        (fun j=>(H1.raw_h1_selected_frozen N z e j A.1).trans (H j))
  have Y := keep w x X heads
  exact parked_or_flying_without_terminal C N _ Y.1 Y.2
    (parked_after_consume C _ K G) tail noTerminal

end L4.ShortResetHelloSplice

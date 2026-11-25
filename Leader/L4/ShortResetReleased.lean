import Leader.L4.ShortResetCycle
import Leader.L4.ShortResetAuthority
import Leader.L4.ShortGrantPersistence
import Leader.L4.ShortActualIssueClock

namespace L4.ShortResetReleased
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetForwardH2
open ShortResetReverseChart ShortResetFlow ShortResetRow

def passed (st : Stage) (k : Nat) : Prop :=
  match st with
  | .fwd i => k<i
  | .rev _ | .done => True

def Released {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (st : Stage) : Prop :=
  ∀ k, k<C.L → h (nextAt C.root k)=true → passed st k →
    (x (nextAt C.root k)).mis1.getLsbD (91-(lane C.a C.b k).val)=false

private theorem ask_false {b : BitVec 96} {j : Fin 3} {t : Token}
    (E : oldK true b j=t) (K : t=T ∨ t=MISByteCodec.E ∨ t=resetReply) :
    (headerGrantView b).ask j=false := by
  change ((oldK true b j).tag == 2 && !(oldK true b j).fault &&
    (oldK true b j).opcode == 3) = false
  rw [E]
  rcases K with rfl|rfl|rfl <;> rfl

private theorem slot_header {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (k : Nat) (H : header x (nextAt C.root k)=true)
    (t : Token) (D : ∀ gate, decode gate (encode t)=t) (B : bits C.route x k=encode t) :
    oldK true (x (nextAt C.root k)).mis1 (lane C.a C.b k)=t := by
  have E := slot_of_bits C.route x k t D B
  change oldK (header x (nextAt C.root k)) (x (nextAt C.root k)).mis1 (lane C.a C.b k)=t at E
  simpa only [H] using E

private def in_range (L : Nat) : Stage → Prop
  | .fwd i => i<L
  | .rev _ | .done => True

private theorem passed_next {n : Nat} {h : Fin n → Bool} (C : Chart h)
    (e : Fin n) (st : Stage) (k : Nat) (K : k<C.L)
    (old : in_range C.L st)
    (H : passed (nextStage C e st) k) :
    passed st k ∨ ∃ i, st=.fwd i ∧ k=i ∧ e=nextAt C.root k := by
  cases st with
  | done => exact .inl trivial
  | rev _ => exact .inl trivial
  | fwd i =>
    change i<C.L at old
    simp only [nextStage] at H
    by_cases E : e=nextAt C.root i
    · rw [if_pos E] at H
      by_cases F : i+1<C.L
      · rw [if_pos F] at H
        change k<i+1 at H
        by_cases V : k=i
        · exact .inr ⟨i,rfl,V,V.symm ▸ E⟩
        · exact .inl (show k<i by omega)
      · by_cases V : k=i
        · exact .inr ⟨i,rfl,V,V.symm ▸ E⟩
        · exact .inl (show k<i by omega)
    · rw [if_neg E] at H
      exact .inl H

private theorem stage_limit {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (st : Stage) (A : Active C x st) :
    in_range C.L st := by
  cases st
  · exact A.1
  · trivial
  · trivial

/-- A genuine RESET0, amidst any raw marks on the same fixed layout,
keeps every grant it already cleared absent. At reversal all three
owned header incidences have been cleared. -/
theorem step_released {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (e : Fin n) (N : 1<n)
    (heads : ∀ j, header x j=h j) (st : Stage) (running : st≠.done)
    (A : Active C x st) (R : Released C x st) :
    Released C (rawNext s x e) (nextStage C e st) := by
  intro k K H P
  let q := nextAt C.root k
  let j := lane C.a C.b k
  have head : header x q=true := (heads q).trans H
  obtain O|⟨i,S,E,mark⟩ := passed_next C e st k K (stage_limit C x st A) P
  · apply ShortGrantPersistence.absent_until_ask x e q j (edge_sep N e) head (R k K H O)
    intro _
    cases st with
    | done => exact False.elim (running rfl)
    | fwd i =>
      have F : bits C.route x k=encode T := A.2.2.1 k O
      exact ask_false (slot_header C x k head T trail_decode F) (.inl rfl)
    | rev i =>
      have F : bits C.route x k=encode (trailAt i k) := A.2.2 k K
      unfold trailAt at F
      split at F
      · exact ask_false (slot_header C x k head T trail_decode F) (.inl rfl)
      · split at F
        · exact ask_false (slot_header C x k head resetReply resetReply_decode F) (.inr (.inr rfl))
        · exact ask_false (slot_header C x k head MISByteCodec.E empty_decode F) (.inr (.inl rfl))
  · subst st
    subst i
    change e=q at mark
    rw [←mark] at head
    have old := slot_header C x k (show header x q=true from mark ▸ head)
      resetForward resetForward_decode A.2.2.2
    change oldK true (x q).mis1 j=resetForward at old
    change (rawNext s x e q).mis1.getLsbD (91-j.val)=false
    rw [←mark] at old ⊢
    exact ShortResetAuthority.reset_release_grant_raw x e j head old

theorem released_at_issue {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) : Released C x (.fwd 0) := by
  intro k _ _ P
  change k<0 at P
  omega

def stageRun {n : Nat} {h : Fin n → Bool} (C : Chart h) :
    Stage → List (Fin n) → Stage
  | st, [] => st
  | st, e::w => stageRun C (nextStage C e st) w

/-- The last mark may consume the reset. No marks after that consume
are credited to the reset's release certificate. -/
def BeforeConsume {n : Nat} {h : Fin n → Bool} (C : Chart h) :
    Stage → List (Fin n) → Prop
  | _, [] => True
  | st, e::w => st≠.done ∧ BeforeConsume C (nextStage C e st) w

theorem raw_run_released {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (w : List (Fin n)) (x : Raw s n) (st : Stage)
    (H : H2Ready x) (heads : ∀ j,header x j=h j)
    (A : Active C x st) (R : Released C x st) (B : BeforeConsume C st w) :
    Active C (rawRun x w) (stageRun C st w) ∧
      Released C (rawRun x w) (stageRun C st w) := by
  induction w generalizing x st with
  | nil => exact ⟨A,R⟩
  | cons e w ih =>
    change st≠.done ∧ BeforeConsume C (nextStage C e st) w at B
    have n1 : 1<n := by omega
    exact ih (rawNext s x e) (nextStage C e st) (h2_ready_closed N x e H)
      (fun j=>(H1.raw_h1_selected_frozen N x e j H.1).trans (heads j))
      (active_step C x e n1 heads st B.1 A)
      (step_released C x e n1 heads st B.1 A R) B.2

theorem genuine_reset_done_released {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (w : List (Fin n)) (x : Raw s n) (H : H2Ready x)
    (heads : ∀ j, header x j=h j) (A : Active C x (.fwd 0))
    (B : BeforeConsume C (.fwd 0) w) (D : stageRun C (.fwd 0) w=.done) :
    Complete C (rawRun x w) ∧ Released C (rawRun x w) .done := by
  have X := raw_run_released C N w x (.fwd 0) H heads A (released_at_issue C x) B
  rw [D] at X
  exact X

/-- Begin at the literal old ISSUE0, execute the real door mark, and
carry the released grants through every mark to the actual consume. -/
theorem released_from_actual_issue {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (x : Raw s n) (H : H2Ready x) (heads : ∀ j, header x j=h j)
    (I : ShortActualIssueClock.Issuable C x) (w : List (Fin n))
    (B : BeforeConsume C (.fwd 0) w) (D : stageRun C (.fwd 0) w=.done) :
    let y := rawRun x (RearTrace.predecessor C.root :: w)
    Complete C y ∧ Released C y .done := by
  let d := RearTrace.predecessor C.root
  have A : Active C (rawNext s x d) (.fwd 0) :=
    (ShortActualIssueClock.actual_issue C N x heads I).2
  exact genuine_reset_done_released C N w (rawNext s x d) (h2_ready_closed N x d H)
    (fun i => (H1.raw_h1_selected_frozen N x d i H.1).trans (heads i)) A B D

end L4.ShortResetReleased

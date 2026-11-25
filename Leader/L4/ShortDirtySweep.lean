import Leader.L4.ShortDirtyMIS1Ring
import Leader.L4.ShortResetCycle
import Leader.L4.ShortPacketTag

namespace L4.ShortDirtySweep
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow
open ShortDirtyMIS1Ring ShortResetCycle ShortResetForwardH2 ShortResetChart ShortPacketTag

set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def kind {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n) (j : Nat) :=
  (slot C.route x j).tag

def NoForward {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n) : Prop :=
  ∀ j, j<C.L → kind C x j≠2

def PackedTail {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n) (i : Nat) : Prop :=
  (kind C x i=0 ∨ kind C x i=3) ∧ ∀ j, i<j → j<C.L → kind C x j=0

private theorem kind_lt {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n) (j : Nat) :
    kind C x j<4 := by
  unfold kind slot oldK
  dsimp only
  rw [inherited_decode_tag]
  exact (BitVec.extractLsb' 17 2 _).isLt

private theorem kind_of_bytes {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x y : Raw s n) (j : Nat)
    (frame : bits C.route y j=bits C.route x j) : kind C y j=kind C x j := by
  unfold kind slot oldK
  dsimp only
  change (decode _ (bits C.route y j)).tag=(decode _ (bits C.route x j)).tag
  rw [frame]
  exact no_kind_change _ _ _

private theorem kind_of_normal {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x y : Raw s n) (j : Nat)
    (frame : bits C.route y j=normalizedNoForward (header x (nextAt C.root j))
      (x (nextAt C.root j)).mis1 (C.route.port j)) : kind C y j=kind C x j := by
  unfold normalizedNoForward at frame
  dsimp only at frame
  split at frame
  · unfold kind slot oldK
    dsimp only
    change (decode _ (bits C.route y j)).tag=(decode _ (bits C.route x j)).tag
    rw [frame]
    exact encode_decoded_tag _ _ _
  · exact kind_of_bytes C x y j frame

private theorem kind_of_E {s n : Nat} {h : Fin n→Bool} (C : Chart h) (y : Raw s n) (j : Nat)
    (frame : bits C.route y j=encode E) : kind C y j=0 := by
  have H := slot_of_bits C.route y j E ShortResetFlow.empty_decode frame
  exact congrArg Token.tag H

private theorem kind_of_reply {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x y : Raw s n)
    (i j : Nat) (reply : kind C x j=3)
    (frame : bits C.route y i=encode (slot C.route x j)) : kind C y i=3 := by
  unfold kind slot oldK at reply ⊢
  dsimp only at reply ⊢
  change (decode _ (bits C.route y i)).tag=3
  rw [frame]
  exact (encode_decoded_tag _ _ _).trans reply

private theorem hold_except {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n)
    (i j : Nat) (I : i<C.L) (J : j<C.L) (A : j≠i) (B : j≠i+1) :
    kind C (rawNext s x (nextAt C.root i)) j=kind C x j := by
  apply kind_of_bytes
  unfold bits
  apply congrArg ((kField (C.route.port j)).read)
  apply reset_remote_frame_raw
  · exact fun E=>A (nextAt_injective_under _ _ _ (by have := C.length_lt; omega)
      (by have := C.length_lt; omega) E)
  · change nextAt C.root j≠nextAt C.root (i+1)
    exact fun E=>B (nextAt_injective_under _ _ _ (by have := C.length_lt; omega)
      (by have := C.length_lt; omega) E)

/-- One selected descending outgoing chart mark: packs the next position
and empties the old tail boundary. The terminal uses the same actual row. -/
theorem descending_mark {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (i : Nat) (I : i<C.L)
    (frozen : ∀ q, header x q=h q) (nf : NoForward C x)
    (tail : i+1<C.L → PackedTail C x (i+1)) :
    let y := rawNext s x (nextAt C.root i)
    NoForward C y ∧ PackedTail C y i := by
  dsimp only
  let e := nextAt C.root i
  let y := rawNext s x e
  have sep : e≠rightNeighbor e := by
    intro H
    have Z : nextAt C.root i=nextAt C.root (i+1) := H
    have J := nextAt_injective_under _ _ _ (by have := C.length_lt; omega)
      (by have := C.length_lt; omega) Z
    omega
  have no : (oldK (header x e) (x e).mis1 (C.route.port i)).tag≠2 := nf i I
  have D := C.actual_dst x frozen i I
  have prove (H : kind C y i=0 ∨ kind C y i=3)
      (next : i+1<C.L → kind C y (i+1)=0)
      (later : ∀ j, i+1<j → j<C.L → kind C x j=0) :
      NoForward C y ∧ PackedTail C y i := by
    have clear : ∀ j, i<j → j<C.L → kind C y j=0 := by
      intro j J K
      by_cases E : j=i+1
      · subst j; exact next K
      · rw [hold_except C x i j I K (by omega) E]
        exact later j (by omega) K
    refine ⟨?_,H,clear⟩
    intro j J
    by_cases ij : j=i
    · subst j
      rcases H with H|H <;> omega
    by_cases ji : i<j
    · have z := clear j ji J
      omega
    · rw [hold_except C x i j I J ij (by omega)]
      exact nf j J
  by_cases k : i+1<C.L
  · have H := tail k
    have d : destination (header x (rightNeighbor e)) (C.route.port i)
        =some (C.route.port (i+1)) := by
      simpa only [Chart.route,if_pos k] using D
    rcases H.1 with emp|rep
    · have B := dirty_nonforward_empty_raw x e sep _ _ d no emp
      have next := kind_of_normal C x y (i+1) B.2
      have old : bits C.route y i=
          if kind C x i=1 then encode E else normalizedNoForward (header x e) (x e).mis1 (C.route.port i) := B.1
      have first : kind C y i=0 ∨ kind C y i=3 := by
        by_cases trail : kind C x i=1
        · rw [if_pos trail] at old
          exact .inl (kind_of_E C y i old)
        · rw [if_neg trail] at old
          rw [kind_of_normal C x y i old]
          have U := kind_lt C x i
          have F := nf i I
          omega
      exact prove first (fun _=>next.trans emp) H.2
    · have B := dirty_nonforward_reply_raw x e sep _ _ d no rep
      exact prove (.inr (kind_of_reply C x y i (i+1) rep B.1))
        (fun _=>kind_of_E C y (i+1) B.2) H.2
  · have d : destination (header x (rightNeighbor e)) (C.route.port i)=none := by
      simpa only [Chart.route,if_neg k] using D
    have B : bits C.route y i=
        if kind C x i=1 then encode E else normalizedNoForward (header x e) (x e).mis1 (C.route.port i) :=
      dirty_nonforward_terminal_raw x e sep _ d no
    have T : kind C y i=0 ∨ kind C y i=3 := by
      by_cases trail : kind C x i=1
      · rw [if_pos trail] at B
        exact .inl (kind_of_E C y i B)
      · rw [if_neg trail] at B
        rw [kind_of_normal C x y i B]
        have U := kind_lt C x i
        have F := nf i I
        omega
    exact prove T (fun H=>(k H).elim) (fun j J K=>False.elim (by omega))

/-- The fixed sweep lists actual clockwise labels in decreasing chart order. -/
def sweepWord {n : Nat} {h : Fin n→Bool} (C : Chart h) : Nat → List (Fin n)
  | 0 => []
  | k+1 => nextAt C.root k :: sweepWord C k

theorem sweepWord_length {n : Nat} {h : Fin n→Bool} (C : Chart h) (k : Nat) :
    (sweepWord C k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sweepWord,ih]

theorem sweepWord_no_door {n : Nat} {h : Fin n→Bool} (C : Chart h) (k : Nat) (K : k≤C.L) :
    RearTrace.predecessor C.root ∉ sweepWord C k := by
  induction k with
  | zero => simp [sweepWord]
  | succ k ih =>
    simp only [sweepWord,List.mem_cons,not_or]
    refine ⟨?_,ih (by omega)⟩
    intro E
    have H : nextAt C.root (k+1)=nextAt C.root 0 := by
      change rightNeighbor (nextAt C.root k)=C.root
      rw [←E,RearTrace.right_predecessor]
    have S := nextAt_injective_under C.root (k+1) 0 (by have := C.length_lt; omega)
      (by have := C.length_lt; omega) H
    omega

private theorem sweep_down {s n : Nat} {h : Fin n→Bool} (C : Chart h) (N : 5≤n)
    (k : Nat) (K : 0<k) (B : k≤C.L) (x : Raw s n)
    (Q : H2Ready x) (frozen : ∀ q,header x q=h q)
    (nf : NoForward C x) (tail : k<C.L → PackedTail C x k) :
    let y := rawRun x (sweepWord C k)
    H2Ready y ∧ (∀ q,header y q=h q) ∧ NoForward C y ∧ PackedTail C y 0 := by
  induction k generalizing x with
  | zero => omega
  | succ j ih =>
    let y := rawNext s x (nextAt C.root j)
    have new := descending_mark C x j (by omega) frozen nf (fun b=>tail b)
    have Q' := h2_ready_closed N x (nextAt C.root j) Q
    have frozen' (q : Fin n) : header y q=h q :=
      (PhysicalCustody.H1.raw_h1_selected_frozen N x _ q Q.1).trans (frozen q)
    change H2Ready (rawRun y (sweepWord C j)) ∧
      (∀ q,header (rawRun y (sweepWord C j)) q=h q) ∧
      NoForward C (rawRun y (sweepWord C j)) ∧ PackedTail C (rawRun y (sweepWord C j)) 0
    by_cases Z : j=0
    · subst j
      exact ⟨Q',frozen',new.1,new.2⟩
    · exact ih (Nat.pos_of_ne_zero Z) (by omega) y Q' frozen' new.1 (fun _=>new.2)

/-- Once inherited forward traffic is absent, this deterministic tape
clears every nonroot chart lane, leaving the root old E or old D. The
actual tape has one mark per site and never activates the root door. -/
theorem packed_of_no_forward {s n : Nat} {h : Fin n→Bool} (C : Chart h) (N : 5≤n)
    (x : Raw s n) (Q : H2Ready x) (heads : ∀ q,header x q=h q) (nf : NoForward C x) :
    let w := sweepWord C C.L
    let y := rawRun x w
    w.length=C.L ∧ RearTrace.predecessor C.root ∉ w ∧
       H2Ready y ∧ (∀ q,header y q=h q) ∧ NoForward C y ∧ PackedTail C y 0 := by
  exact ⟨sweepWord_length C _,sweepWord_no_door C _ (Nat.le_refl _),
    sweep_down C N _ C.positive (Nat.le_refl _) x Q heads nf (fun f=>(Nat.lt_irrefl _ f).elim)⟩

end L4.ShortDirtySweep

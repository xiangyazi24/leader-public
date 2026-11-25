import Leader.L4.ShortDirtyMIS1Ring
import Leader.L4.ShortResetCycle

namespace L4.ShortEmptyOwnership
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow
open ShortDirtyMIS1Ring ShortResetFlow ShortResetCycle ShortResetChart ShortResetForwardH2

theorem canonical_empty_oldK (h : Bool) (b : BitVec 96) (j : Fin 3)
    (H : (kField j).read b=encode E) : oldK h b j=E := by
  unfold oldK
  rw [H,empty_decode]

theorem canonical_empty_norm (h : Bool) (b : BitVec 96) (j : Fin 3)
    (H : (kField j).read b=encode E) : normalizedNoForward h b j=encode E := by
  unfold normalizedNoForward
  rw [canonical_empty_oldK _ _ _ H]
  exact H

/-- Raw incoming K0 proof; the old responder's source outcome completely
determines the result, and no left-side lane can inject a packet. -/
theorem source_door_k0_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true) :
    let old := (x (rightNeighbor e)).mis1
    let out := source old (oldK true old 0)
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1 =
      match out.2 with
      | none => normalizedNoForward true old 0
      | some t => encode t := by
  have W := (work_to_raw x e sep 0).2
  simp only [pairHeader,pairIn,eligible] at W
  exact W.trans (source_door_k0_pair _ _ _)

theorem empty_link_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (A : (kField j).read (x e).mis1=encode E)
    (B : (kField k).read (x (rightNeighbor e)).mis1=encode E) :
    (kField j).read (rawNext s x e e).mis1=encode E ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=encode E := by
  have X := canonical_empty_oldK (header x e) _ _ A
  have Y := canonical_empty_oldK (header x (rightNeighbor e)) _ _ B
  obtain ⟨H,I⟩ := dirty_nonforward_empty_raw x e sep j k dst
    (by rw [X]; decide) (by rw [Y]; decide)
  rw [X] at H
  exact ⟨H.trans (canonical_empty_norm _ _ _ A),I.trans (canonical_empty_norm _ _ _ B)⟩

theorem empty_terminal_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=none)
    (A : (kField j).read (x e).mis1=encode E) :
    (kField j).read (rawNext s x e e).mis1=encode E := by
  have X := canonical_empty_oldK (header x e) _ _ A
  have H := dirty_nonforward_terminal_raw x e sep j dst (by rw [X]; decide)
  rw [X] at H
  exact H.trans (canonical_empty_norm _ _ _ A)

def Clear {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) : Prop :=
  ∀ i, i<C.L → bits C.route x i=encode E

/-- Closed on every nondoor mark. The only mark that can inject into a
whole empty owner lane is the mark at its own controller door. -/
theorem clear_nondoor {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (heads : ∀ q, header x q=h q) (e : Fin n)
    (neDoor : e≠RearTrace.predecessor C.root) (A : Clear C x) :
    Clear C (rawNext s x e) := by
  have N := C.length_lt
  have L := C.positive
  have sep := edge_sep (by omega) e
  intro i I
  by_cases S : e=nextAt C.root i
  · subst e
    let e := nextAt C.root i
    have D := C.actual_dst x heads i I
    by_cases B : i+1<C.L
    · have d : destination (header x (rightNeighbor e)) (C.route.port i)
          =some (C.route.port (i+1)) := by simpa only [Chart.route,if_pos B] using D
      exact (empty_link_raw x e sep _ _ d (A i I) (A (i+1) B)).1
    · have d : destination (header x (rightNeighbor e)) (C.route.port i)
          =none := by simpa only [Chart.route,if_neg B] using D
      exact empty_terminal_raw x e sep _ d (A i I)
  by_cases B : rightNeighbor e=nextAt C.root i
  · cases i with
    | zero =>
      have F := congrArg RearTrace.predecessor B
      rw [RearTrace.predecessor_right] at F
      exact False.elim (neDoor F)
    | succ j =>
      have F := congrArg RearTrace.predecessor B
      change RearTrace.predecessor (rightNeighbor e)=
        RearTrace.predecessor (rightNeighbor (nextAt C.root j)) at F
      rw [RearTrace.predecessor_right,RearTrace.predecessor_right] at F
      subst e
      let e := nextAt C.root j
      have D := C.actual_dst x heads j (by omega)
      have d : destination (header x (rightNeighbor e)) (C.route.port j)
          =some (C.route.port (j+1)) := by simpa only [Chart.route,if_pos I] using D
      exact (empty_link_raw x e sep _ _ d (A j (by omega)) (A (j+1) I)).2
  · unfold bits
    change (kField (C.route.port i)).read (rawNext s x e (nextAt C.root i)).mis1=_
    rw [reset_remote_frame_raw _ _ _ (Ne.symm S) (Ne.symm B)]
    exact A i I

/-- The owner door is not incident to any nonroot slot. Thus it can
launch one owner packet at K0 but cannot write another slot on this chart. -/
theorem clear_door_except_root {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (A : Clear C x) (i : Nat) (L : i<C.L) (O : i≠0) :
    bits C.route (rawNext s x (RearTrace.predecessor C.root)) i=encode E := by
  let d := RearTrace.predecessor C.root
  have R : rightNeighbor d=C.root := RearTrace.right_predecessor C.root
  have J := C.length_lt
  have E : nextAt C.root i≠d := by
    intro U
    have V : nextAt C.root (i+1)=nextAt C.root 0 := (congrArg rightNeighbor U).trans R
    have B := nextAt_injective_under C.root (i+1) 0 (by omega) (by omega) V
    omega
  have F : nextAt C.root i≠rightNeighbor d := by
    intro U
    have B := nextAt_injective_under C.root i 0 (by omega) (by omega) (U.trans R)
    exact O B
  unfold bits
  change (kField (C.route.port i)).read (rawNext s x d (nextAt C.root i)).mis1=_
  rw [reset_remote_frame_raw _ _ _ E F]
  exact A i L

/-- If literal source creates no nonempty K0 token, the entire owner
chart remains clear even on its own door. -/
theorem clear_door_without_launch {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (H : header x C.root=true) (A : Clear C x)
    (own : (source (x C.root).mis1 (oldK true (x C.root).mis1 0)).2=none ∨
      (source (x C.root).mis1 (oldK true (x C.root).mis1 0)).2=some E) :
    Clear C (rawNext s x (RearTrace.predecessor C.root)) := by
  let d := RearTrace.predecessor C.root
  have R : rightNeighbor d=C.root := RearTrace.right_predecessor C.root
  have L := C.length_lt
  have P := C.positive
  intro i I
  by_cases Z : i=0
  · subst i
    have W := source_door_k0_raw x d (edge_sep (by omega) d) (by rwa [R])
    dsimp only at W
    rw [R] at W
    change (kField (lane C.a C.b 0)).read (rawNext s x d C.root).mis1=_
    rw [C.rootPort,W]
    rcases own with O|O
    · rw [O]
      apply canonical_empty_norm
      have T := A 0 P
      change (kField (lane C.a C.b 0)).read (x C.root).mis1=encode E at T
      rwa [C.rootPort] at T
    · rw [O]
  · exact clear_door_except_root C x A i I Z

/-- The first loss of an initially canonical-clear chart has a genuine
local source birth in its tape prefix. This theorem traces the first
birth only; it does not classify later in-flight payloads. -/
theorem first_birth_exists {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (x : Raw s n) (Q : H2Ready x) (heads : ∀ q,header x q=h q)
    (A : Clear C x) (w : List (Fin n)) (lost : ¬Clear C (rawRun x w)) :
    ∃ u e v t, w=u++e::v ∧ e=RearTrace.predecessor C.root ∧
      Clear C (rawRun x u) ∧ t≠E ∧
      (source (rawRun x u C.root).mis1 (oldK true (rawRun x u C.root).mis1 0)).2=some t := by
  induction w generalizing x with
  | nil => exact False.elim (lost A)
  | cons e v ih =>
    have Q' := h2_ready_closed N x e Q
    have H' : ∀ q,header (rawNext s x e) q=h q :=
      fun q=>(PhysicalCustody.H1.raw_h1_selected_frozen N x e q Q.1).trans (heads q)
    have recover (B : Clear C (rawNext s x e)) :
        ∃ u f v' t, e::v=u++f::v' ∧ f=RearTrace.predecessor C.root ∧
          Clear C (rawRun x u) ∧ t≠E ∧
          (source (rawRun x u C.root).mis1 (oldK true (rawRun x u C.root).mis1 0)).2=some t := by
      obtain ⟨u,f,v',t,Z,D,L,P,T⟩ := ih (rawNext s x e) Q' H' B lost
      exact ⟨e::u,f,v',t,congrArg (fun a=>e::a) Z,D,L,P,T⟩
    by_cases D : e=RearTrace.predecessor C.root
    · subst e
      generalize X : (source (x C.root).mis1 (oldK true (x C.root).mis1 0)).2=o
      cases o with
      | none =>
        exact recover (clear_door_without_launch C x ((heads _).trans C.rootHeader) A (.inl X))
      | some t =>
        by_cases E' : t=E
        · subst t
          exact recover (clear_door_without_launch C x ((heads _).trans C.rootHeader) A (.inr X))
        · exact ⟨[],_,v,t,rfl,rfl,A,E',X⟩
    · exact recover (clear_nondoor C x heads e D A)

end L4.ShortEmptyOwnership

import Leader.L4.ShortHelloReverseChart

namespace L4.ShortHelloReverseSplice
open AllSizeProtocol MISByteCodec ShortResetFlow ShortResetRow ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetForwardH2 PhysicalCustody
open ShortHelloReverseChart ShortHelloForward

/-- The real terminal HELLO mark starts the reverse stage at the same
coordinate, holding the full trail and the actual WAIT1 controller. -/
theorem from_terminal {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (heads : ∀ q, header x q=h q) (A : BeforeTurn C.route x (C.L-1)) :
    Returning C (rawNext s x (terminalMark C.route)) (C.L-1) := by
  let e := terminalMark C.route
  have I : C.L-1<C.L := by have := C.positive; omega
  have L : ¬ C.L-1+1<C.route.length := by change ¬ C.L-1+1<C.L; have := C.positive; omega
  have Sep := edge_sep (by have := C.length_lt; have := C.positive; omega : 1<n) e
  have F := forward_step C.route x e Sep heads A.2.1.1 A.2.1.2 (C.L-1) I A.2.2.1 A.2.2.2
  have V : e=nextAt C.route.root (C.L-1) := rfl
  simp only [if_pos V,if_neg L] at F
  have hd : header x C.root=true := (heads _).trans C.rootHeader
  have W := wait1_held_step x C.root e Sep hd A.2.1 (fun _ => by
    by_cases Z : C.L-1=0
    · have H : bits C.route x 0=encode helloForward := Z ▸ A.2.2.2
      have X := slot_of_bits C.route x 0 helloForward (by intro g; cases g <;> decide) H
      change oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)=_ at X
      rw [hd,C.rootPort] at X
      exact .inr (by rw [X]; rfl)
    · have H := A.2.2.1 0 (by omega)
      have X := slot_of_bits C.route x 0 T trail_decode H
      change oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)=_ at X
      rw [hd,C.rootPort] at X
      exact .inl (by rw [X]; rfl))
  refine ⟨I,W,?_⟩
  intro j J
  change bits C.route (rawNext s x e) j=encode (trailAt (C.L-1) j)
  by_cases B : j<C.L-1
  · simpa [trailAt,B] using F.1 j B
  · have D : j=C.L-1 := by omega
    subst j
    simpa [trailAt] using F.2

/-- A mark on the terminal edge before the current front arrives is
an ordinary nonprogress mark. Only the literal front turn changes to .rev. -/
theorem forward_all_mark {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (heads : ∀ q, header x q=h q) (e : Fin n) (i : Nat)
    (A : BeforeTurn C.route x i) :
    match nextStage C e (.fwd i) with
    | .fwd k => BeforeTurn C.route (rawNext s x e) k
    | .rev k => Returning C (rawNext s x e) k
    | .done => False := by
  obtain ⟨I,W,Tp,Fp⟩ := A
  have Sep := edge_sep (by have := C.positive; have := C.length_lt; omega : 1<n) e
  have Hd : header x C.root=true := (heads _).trans C.rootHeader
  have B := forward_step C.route x e Sep heads W.1 W.2 i I Tp Fp
  have W' := wait1_held_step x C.root e Sep Hd W (fun _ => by
    by_cases Z : i=0
    · subst i
      have X := slot_of_bits C.route x 0 helloForward (by intro g; cases g <;> decide) Fp
      change oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)=_ at X
      rw [Hd,C.rootPort] at X
      exact .inr (by rw [X]; rfl)
    · have X := slot_of_bits C.route x 0 T trail_decode (Tp 0 (by omega))
      change oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)=_ at X
      rw [Hd,C.rootPort] at X
      exact .inl (by rw [X]; rfl))
  by_cases M : e=nextAt C.root i
  · rw [nextStage,if_pos M]
    by_cases J : i+1<C.L
    · rw [if_pos J]
      change e=nextAt C.route.root i at M
      change i+1<C.route.length at J
      simp only [if_pos M,if_pos J] at B
      refine ⟨J,W',?_,B.2.2⟩
      intro j Kj
      by_cases Q : j=i
      · simpa only [Q] using B.2.1
      · exact B.1 j (by omega)
    · rw [if_neg J]
      have I' : i=C.L-1 := by change i<C.L at I; omega
      subst i
      subst e
      exact from_terminal C x heads ⟨I,W,Tp,Fp⟩
  · rw [nextStage,if_neg M]
    change e≠nextAt C.route.root i at M
    simp only [if_neg M] at B
    exact ⟨I,W',B.1,B.2⟩

#print axioms forward_all_mark
#print axioms from_terminal
end L4.ShortHelloReverseSplice

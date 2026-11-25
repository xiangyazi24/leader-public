
import Leader.L4.ReportPrelaunchK1Geometry

namespace L4.ReportPrelaunchK1Lift

open AllSizeProtocol PhysicalCustody ReportResetRawHooks
open ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportPrelaunchRank ReportPrelaunchClock
open ReportByteRows ReportPrelaunchK1Geometry
open BStarH6Ordinal

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

variable {s n : Nat} {h : Fin n→Bool}

theorem raw_internal_of_weights (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) sheet Q)
    (N : 1<n) (x : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (i : Nat) (I : i+1<C.L)
    (Event : Prop)
    (K : let y := rawNext s x (out C i)
         let a : Fin C.L := ⟨i,by omega⟩
         let b : Fin C.L := ⟨i+1,I⟩
         ((weight sheet C y a≤weight sheet C x a ∧ weight sheet C y b≤weight sheet C x b) ∨
          weight sheet C y a+weight sheet C y b<weight sheet C x a+weight sheet C x b) ∧
         (Event→weight sheet C y a+weight sheet C y b<weight sheet C x a+weight sheet C x b))
 :
    (Weak sheet C x (rawNext s x (out C i)) ∨ Paid sheet C x (rawNext s x (out C i))) ∧
      (Event→Paid sheet C x (rawNext s x (out C i))) := by
  let e := out C i
  let y := rawNext s x e
  let a : Fin C.L := ⟨i,by omega⟩
  let b : Fin C.L := ⟨i+1,I⟩
  have CF := ReportOwnerResetDrain.cached_fibre sheet N hh Q F
  have Y : ReportOwnerResetDrain.Cached sheet hh Q y := CF.closed x e X
  have doorN : e≠door C := Ne.symm (ReportChartPartition.door_not_outgoing C i a.isLt)
  have PC := debt_frame sheet C x e N (CF.mask x X) doorN
  have frame : ∀ r : Fin C.L,r≠a→r≠b→weight sheet C y r=weight sheet C x r := by
    intro r A D
    exact weight_frame sheet C hh B x y X Y r
      (raw_link_frame sheet C x i r.val a.isLt r.isLt
        (fun E=>A (Fin.ext E)) (fun E=>D (Fin.ext E)))
  have ab : a≠b := by intro E; have V := congrArg Fin.val E; dsimp [a,b] at V; omega
  have pay (H : weight sheet C y a+weight sheet C y b<
        weight sheet C x a+weight sheet C x b) : Paid sheet C x y :=
    .inl ⟨PC,.inr ⟨a,b,ab,frame,H⟩⟩
  refine ⟨?_,fun H=>pay (K.2 H)⟩
  rcases K.1 with H|H
  · left
    refine ⟨PC,?_⟩
    intro r
    by_cases A : r=a
    · subst r; exact H.1
    · by_cases D : r=b
      · subst r; exact H.2
      · exact Nat.le_of_eq (frame r A D)
  · exact .inr (pay H)

/-- A terminal edge has only one occurrence of this owner chart.
    Its actual right endpoint belongs to a different owner lane. -/
theorem raw_end_of_weights (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) sheet Q)
    (N : 1<n) (x : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (i : Nat) (I : i+1=C.L)
    (Event : Prop)
    (K : let y := rawNext s x (out C i)
         let a : Fin C.L := ⟨i,by omega⟩
         weight sheet C y a≤weight sheet C x a ∧ (Event→weight sheet C y a<weight sheet C x a))
 :
    Weak sheet C x (rawNext s x (out C i)) ∧
      (Event→Paid sheet C x (rawNext s x (out C i))) := by
  let e := out C i
  let y := rawNext s x e
  let a : Fin C.L := ⟨i,by omega⟩
  have CF := ReportOwnerResetDrain.cached_fibre sheet N hh Q F
  have Y : ReportOwnerResetDrain.Cached sheet hh Q y := CF.closed x e X
  have PC := debt_frame sheet C x e N (CF.mask x X)
    (Ne.symm (ReportChartPartition.door_not_outgoing C i a.isLt))
  have frame : ∀ r : Fin C.L,r≠a→weight sheet C y r=weight sheet C x r := by
    intro r A
    exact weight_frame sheet C hh B x y X Y r
      (raw_link_frame sheet C x i r.val a.isLt r.isLt
        (fun E=>A (Fin.ext E)) (by have := r.isLt; omega))
  refine ⟨⟨PC,?_⟩,?_⟩
  · intro r
    by_cases A : r=a
    · subst r; exact K.1
    · exact Nat.le_of_eq (frame r A)
  · intro E
    exact .inl ⟨PC,.inl ⟨a,frame,K.2 E⟩⟩

end L4.ReportPrelaunchK1Lift

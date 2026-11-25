import Leader.L4.ShortFiveReadTour
import Leader.L4.ShortWriteFlight

namespace L4.ShortFiveWriteTour
open PhysicalCustody ShortResetMIS1Ring ShortResetChart ShortResetCycle
open ShortWriteFlight ShortWriteCentreWitness ShortWriteChartHop
open ShortFiveWinningWord ShortFiveReadTour
open MISByteCodec

variable {s n : Nat}

def preCentre {h : Fin n→Bool} (C : Chart h) : List (Fin n) :=
  RearTrace.predecessor C.root :: (List.range C.a).map (nextAt C.root)

private theorem backSweep (x : Raw s n) (C : Chart (header x)) (cmd : Cmd)
    (d : Fin 8) (w : List (Fin n)) (k : Nat)
    (G : Generated x C cmd d w (.back k false)) :
    Generated x C cmd d (w++(List.range k).reverse.map (nextAt C.root)) (.back 0 false) := by
  induction k generalizing w with
  | zero => simpa using G
  | succ k IH =>
    let e := nextAt C.root k
    have S := Generated.snoc e G (by trivial)
    have T : Generated x C cmd d (w++[e]) (.back k false) := by
      simpa [e,next,nextStage] using S
    have R := IH _ T
    simpa [List.range_succ,List.reverse_append,List.map_append,List.append_assoc,e] using R

theorem generated_success_on_tour (x : Raw s n) (C : Chart (header x))
    (cmd : Cmd) (d : Fin 8)
    (I : ShortClearLaunch.ClearIssue C x cmd.op)
    (D : d.val=issuedDescriptor (x C.root).mis1)
    (_center : C.a+1<C.L)
    (A : cmd.accepts ((rawRun x (preCentre C)) (nextAt C.root C.a)).mis1 d=true) :
    Generated x C cmd d (tour C) (.done false) := by
  let door := RearTrace.predecessor C.root
  let pfx := fun k=>door::(List.range k).map (nextAt C.root)
  have front (k : Nat) (K : k<C.L) : Generated x C cmd d (pfx k) (.front k false) := by
    induction k with
    | zero => exact .launch I D
    | succ k IH =>
      let e := nextAt C.root k
      have G := IH (by omega)
      have P := Generated.snoc e G (by trivial)
      have G0 : advanceBad cmd d C (rawRun x (pfx k)) k false=false := by
        by_cases H : k=C.a
        · subst k
          change (false || ((C.a==C.a) &&
            !(cmd.accepts ((rawRun x (preCentre C)) (nextAt C.root C.a)).mis1 d)))=false
          rw [A]
          simp
        · simp [advanceBad,H]
      have B : Generated x C cmd d (pfx k++[e]) (.front (k+1) false) := by
        simpa only [next,e,if_pos rfl,if_pos K,G0,if_true] using P
      simpa only [pfx,List.range_succ,List.map_append,List.cons_append,List.map_cons,List.map_nil,e] using B
  let k := C.L-1
  have L : k<C.L := by have := C.positive; dsimp [k]; omega
  have turn := Generated.snoc (nextAt C.root k) (front k L) (by trivial)
  have B : ¬k+1<C.L := by have := C.positive; dsimp [k]; omega
  have turn' : Generated x C cmd d (pfx k++[nextAt C.root k]) (.back k false) := by
    simpa only [next,if_pos rfl,if_neg B,if_true] using turn
  have E : C.L=k+1 := by have := C.positive; dsimp [k]; omega
  have T : pfx k++[nextAt C.root k]=pfx C.L := by
    conv => rhs; rw [E]
    simp [pfx,List.range_succ]
  rw [T] at turn'
  have Q := backSweep x C cmd d _ k turn'
  have F := Generated.snoc door Q (by trivial)
  simpa [next, nextStage, door, RearTrace.right_predecessor, pfx, tour, k,List.append_assoc] using F

#print axioms generated_success_on_tour
end L4.ShortFiveWriteTour

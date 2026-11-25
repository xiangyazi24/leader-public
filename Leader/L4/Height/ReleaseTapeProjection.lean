import Leader.L4.Height.SerialProduction
import Leader.L4.Height.ProductionCustody
import Leader.L4.Height.OpenFenceLine

namespace L4.Height.ReleaseTapeProjection
open Classical PhysicalCustody ProductionCustody BStarSteeredLikelihood
noncomputable section
theorem after_tape {s n : Nat} (c : Word n → Fin n → Fin n)
    (i : Fin n) (y : History s n) (a : Word n) :
    let u := runWord (next c i) y a
    let tape := emit c y.emitted a
    u.emitted = y.emitted++tape ∧ u.physical = rawRun y.physical tape := by
  induction a generalizing y with
  | nil => simp [runWord,emit,rawRun,BStarResetSchedule.run]
  | cons e w ih =>
    let z := next c i y e
    let f := c y.emitted e
    have run : runWord (next c i) y (e::w)=runWord (next c i) z w := rfl
    rw [run]
    have E := ih z
    simpa only [z, f, next, emit, rawRun, BStarResetSchedule.run, List.append_assoc,
      List.singleton_append] using E

theorem consistency_after {s n : Nat} {x : Raw s n} {c : Word n → Fin n → Fin n}
    {i : Fin n} {y : History s n} (ok : Consistent x c i y) (a : Word n) :
    Consistent x c i (runWord (next c i) y a) := by
  induction a generalizing y with
  | nil => exact ok
  | cons e a ih => exact ih (consistent_next x c i y ok e)

theorem emit_append {n : Nat} (c : Word n → Fin n → Fin n) (a u v : Word n) :
    emit c a (u ++ v) = emit c a u ++ emit c (a ++ emit c a u) v := by
  induction u generalizing a with
  | nil => simp [emit]
  | cons e u ih => simp only [List.cons_append, emit, ih, List.append_assoc, List.nil_append]

theorem emit_shifted {n : Nat} (c : Word n → Fin n → Fin n) (pre a w : Word n) :
    emit (fun b => c (pre++b)) a w = emit c (pre++a) w := by
  induction w generalizing a with
  | nil => rfl
  | cons e w ih => simp only [emit, ih, List.append_assoc]

/-- The same candidate replay after a nonempty stopped prefix. The
comparison sees the actual emitted suffix, not the candidate suffix. -/
theorem shifted_twice {n : Nat} (c : Word n → Fin n → Fin n)
    (pre : Word n) (two : OpenFenceLine.Twice (fun a => c (emit c [] a))) :
    OpenFenceLine.Twice (fun a => (fun b => c (emit c [] pre++b))
      (emit (fun b => c (emit c [] pre++b)) [] a)) := by
  intro a e between
  obtain ⟨u,f,v,eq,out⟩ := two (pre++a) e between
  refine ⟨u,f,v,eq,?_⟩
  have E : emit (fun b => c (emit c [] pre++b)) [] (a++u)=emit c (emit c [] pre) (a++u) := by
    simpa only [List.append_nil] using emit_shifted c (emit c [] pre) [] (a++u)
  change c (emit c [] pre ++ emit (fun b => c (emit c [] pre++b)) [] (a++u)) f=e
  rw [E]
  have joined := emit_append c [] pre (a++u)
  simp only [List.nil_append] at joined
  rw [←joined]
  simpa only [List.append_assoc] using out

open AllSizeProtocol BStarLongDoor BStarH6WordChart BStarAcquireLiteralChain
open BStarAcquireVisitOrder BStarResetChartTouch BStarGeneratedOwner BStarOwnerControlHistory
theorem mark_releases {s n : Nat} {base origin x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true} {o : Owners (oldH6 (rows s) base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart (by decide : 0<2) base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {w : Word n} (replay : x=rawRun origin w)
    {m d : Mode} (e : Fin n)
    (hist : GeneratedOwner (by decide : 0<2) base (fun j => S.getD j fall) len origin .idle w m)
    (cur : Current (by decide : 0<2) base (fun j => S.getD j fall) len x m)
    (ev : Event (by decide : 0<2) (fun j => S.getD j fall) len x e m d)
    (paid : releaseEvent m d=true) :
    let root := (S.getD 0 fall).1
    e=RearTrace.predecessor root ∧ (ctrlOp.read (x root).long).toNat=2 ∧
      (ctrlOp.read (rawNext s x e root).long).toNat=3 := by
  cases ev with
  | idle_hold | bad_issue | launch | transit | arrived_hold => simp [releaseEvent] at paid
  | consume op own cleared =>
    have eq : op=2 := by simpa [releaseEvent] using paid
    subst op
    exact ⟨own,cur.1.2.2.2,generated_reset_receipt (by decide : 0<2) C sep replay 2 (by decide)
      e hist cur (.consume 2 own cleared)⟩

end
end L4.Height.ReleaseTapeProjection

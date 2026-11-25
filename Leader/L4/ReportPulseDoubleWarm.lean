import Leader.L4.ReportPulseWarmup

namespace L4.ReportPulseDoubleWarm
open AllSizeProtocol ReportByteRows ReportPulseWarmup ReportPulseRaw

variable {n : Nat} {X : Type}

private theorem new_hit_cleans (J : Nat) (a b e : Fin n) (old : ReportPulseWait.State)
    (O : old.hit=false)
    (H : (ReportPulseWait.step J a b e old).hit=true) :
    Clean (ReportPulseWait.step J a b e old) := by
  rcases old with ⟨ph,k,h⟩
  change h=false at O
  subst h
  cases ph <;> by_cases A : e=a <;> by_cases B : e=b <;>
    simp_all [ReportPulseWait.step,ReportPulseWait.side,Clean]
  all_goals
    by_cases E : ReportPulseWait.effective J k+1=J
    · rw [if_pos E]
      exact ⟨rfl,rfl⟩
    · rw [if_neg E] at H
      contradiction

/-- A literal paint immediately establishes the same clean boundary
used by warm-up. Unlike a mere completion, this resets the streak. -/
theorem actual_paint_clean
    {raw : X→Fin n→X} {b : Fin n} {Q : X→Prop}
    {p : Params} {bytes : X→BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n) (A : rightNeighbor a=b) (D : a≠b)
    (J : 0<p.streak) (x : X) (H : Q x) (e : Fin n)
    (E : countedPaint b p bytes x e=true) :
    Clean (readClock p bytes (raw x e)) := by
  have C := wire_clock_eq F a A D J x e false H
  rw [E,Bool.false_or] at C
  have T : (ReportPulseWait.step p.streak a b e (readClock p bytes x)).hit=true :=
    (congrArg ReportPulseWait.State.hit C).symm
  have K := new_hit_cleans p.streak a b e (readClock p bytes x) rfl T
  unfold readClock at K
  rw [←C] at K
  exact K

/-- Two credited pulses at the same gate have certified fresh rounds
in physically disjoint portions of the word. Rebase the second witness
to the first actual paint, not merely to an arbitrary earlier cut. -/
theorem same_gate_two_credits
    {raw : X→Fin n→X} {b : Fin n} {Q : X→Prop}
    {p : Params} {bytes : X→BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n) (A : rightNeighbor a=b) (D : a≠b)
    (J : 0<p.streak) (x : X) (H : Q x) (I : Clean (readClock p bytes x))
    (u v : List (Fin n)) (e f : Fin n)
    (E : countedPaint b p bytes (u.foldl raw x) e=true)
    (E' : countedPaint b p bytes (v.foldl raw (raw (u.foldl raw x) e)) f=true) :
    let y := raw (u.foldl raw x) e
    Credit a b p.streak (cleanAt raw p bytes x) (u++[e]) ∧
    Credit a b p.streak (cleanAt raw p bytes y) (v++[f]) := by
  let y := raw (u.foldl raw x) e
  have W := wire_fresh_from_clean F a A D J x H I u
  have C1 := (wire_fresh_mark F a A D J x H u e W).2 E
  have Y := F.stays _ e (wire_run_good F x u H)
  have C := actual_paint_clean F a A D J _ (wire_run_good F x u H) e E
  have W' := wire_fresh_from_clean F a A D J y Y C v
  exact ⟨C1,(wire_fresh_mark F a A D J y Y v f W').2 E'⟩

end L4.ReportPulseDoubleWarm

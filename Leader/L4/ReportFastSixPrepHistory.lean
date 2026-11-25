import Leader.L4.ReportFastSixPrepPlateau

namespace L4.ReportFastSixPrepHistory
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportFastSixPrepPlateau

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

abbrev Base (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n→Prop) :=
  ReportFastSixPrep.State d hh Q

def phase {d : Sheet} {hh : ∃ i,h i=true} (z : Base d hh Q) : Nat :=
  match z.2 with
  | none => 6
  | some (j,_) => j.val

def RawReceipt (d : Sheet) (C : Chart h) (x : Raw s n) (w : List (Fin n)) : Prop :=
  ∃ pre u post : List (Fin n),
    w=pre++u++post ∧ Generated d C (rawRun x pre) u .done

private theorem run_append {Z : Type} (f : Z→Fin n→Z) (x : Z)
    (u v : List (Fin n)) :
    SequentialMarkClock.run f x (u++v)=
      SequentialMarkClock.run f (SequentialMarkClock.run f x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons a u IH => exact IH (f x a)

theorem run_raw (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : Base d hh Q) (w : List (Fin n)) :
    (SequentialMarkClock.run (ReportFastSixPrep.step d C N hh F) z w).1.val=
      rawRun z.1.val w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w IH => exact IH _

structure Chronology (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (w : List (Fin n)) (z : Base d hh Q) : Prop where
  raw : z.1.val=rawRun x w
  past : ∀ j : Fin 6,j.val<phase z→RawReceipt d (C j) x w
  active : ∀ j st,z.2=some (j,st)→
    ∃ pre u : List (Fin n), ∃ x0 : {y : Raw s n // Cached d hh Q y},
      w=pre++u ∧ x0.val=rawRun x pre ∧
      SequentialMarkClock.run (ReportFastFreshReset.step d (C j) N hh F) (x0,none) u=(z.1,st)

theorem start_history (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : {y : Raw s n // Cached d hh Q y}) :
    Chronology d C N hh F x.val [] (ReportFastSixPrep.init d hh x) := by
  refine ⟨rfl,?_,?_⟩
  · intro j J
    exact False.elim (Nat.not_lt_zero _ J)
  · intro j st E
    have H : (0:Fin 6)=j ∧ (none:Option Stage)=st := by
      simpa [ReportFastSixPrep.init] using E
    rcases H with ⟨rfl,rfl⟩
    exact ⟨[],[],x,rfl,rfl,rfl⟩

private theorem extend_receipt (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (e : Fin n) (H : RawReceipt d C x w) :
    RawReceipt d C x (w++[e]) := by
  obtain ⟨p,u,v,E,R⟩ := H
  exact ⟨p,u,v++[e],by simp [E,List.append_assoc],R⟩

set_option maxHeartbeats 5000000 in
theorem append_step (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (w : List (Fin n)) (z : Base d hh Q)
    (H : Chronology d C N hh F x w z) (e : Fin n) :
    Chronology d C N hh F x (w++[e]) (ReportFastSixPrep.step d C N hh F z e) := by
  let y := ReportFastSixPrep.step d C N hh F z e
  have Yr : y.1.val=rawRun x (w++[e]) := by
    rw [ShortOwnerEpochJS.raw_snoc,←H.raw]; rfl
  refine ⟨Yr,?_,?_⟩
  · intro j J
    cases E : z.2 with
    | none =>
      exact extend_receipt d (C j) x w e (H.past j (by simp [phase,E,j.isLt]))
    | some q =>
      rcases q with ⟨i,st⟩
      let m := ReportFastFreshReset.step d (C i) N hh F (z.1,st) e
      by_cases L : j.val<i.val
      · exact extend_receipt d (C j) x w e (H.past j (by simpa only [phase,E] using L))
      · have D : m.2=some .done := by
          apply Classical.byContradiction
          intro K
          have Y : y.2=some (i,m.2) := by simp [y,ReportFastSixPrep.step,E,m,K]
          have HH : phase y=i.val := by simp [phase,Y]
          change j.val<phase y at J
          omega
        have JI : j=i := by
          have Y : phase y=i.val+1 := by
            by_cases U : i.val+1<6
            · have S : y.2=some ((⟨i.val+1,U⟩:Fin 6),none) := by
                simp [y,ReportFastSixPrep.step,E,m,D,U]
              rw [phase,S]
            · have S : y.2=none := by simp [y,ReportFastSixPrep.step,E,m,D,U]
              rw [phase,S]
              have := i.isLt
              change 6=i.val+1
              omega
          apply Fin.ext
          change j.val<phase y at J
          omega
        subst j
        obtain ⟨p,u,x0,W,X0,R⟩ := H.active i st E
        have RD : ReportOwnerReceiptClock.done
            (SequentialMarkClock.run (ReportFastFreshReset.step d (C i) N hh F)
              (x0,none) (u++[e])) := by
          rw [run_append,R]
          exact D
        obtain ⟨p',u',v',W',Gen,_⟩ :=
          ReportFastFreshReset.receipt_history d (C i) N hh F x0 (u++[e]) RD
        refine ⟨p++p',u',v',?_,?_⟩
        · rw [W,List.append_assoc,W']
          simp only [List.append_assoc]
        · rw [ShortOwnerEpochJS.raw_append,←X0]
          exact Gen
  · intro j st Y
    cases E : z.2 with
    | none =>
      simp [ReportFastSixPrep.step,E] at Y
    | some q =>
      rcases q with ⟨i,st0⟩
      let m := ReportFastFreshReset.step d (C i) N hh F (z.1,st0) e
      by_cases D : m.2=some .done
      · by_cases U : i.val+1<6
        · have K : y.2=some ((⟨i.val+1,U⟩:Fin 6),none) := by
            simp [y,ReportFastSixPrep.step,E,m,D,U]
          change y.2=some (j,st) at Y
          rw [K] at Y
          have A := Prod.mk.inj (Option.some.inj Y)
          rcases A with ⟨_,rfl⟩
          exact ⟨w++[e],[],y.1,by simp,Yr,rfl⟩
        · simp [ReportFastSixPrep.step,E,m,D,U] at Y
      · have K : y.2=some (i,m.2) := by simp [y,ReportFastSixPrep.step,E,m,D]
        change y.2=some (j,st) at Y
        rw [K] at Y
        rcases Prod.mk.inj (Option.some.inj Y) with ⟨rfl,rfl⟩
        obtain ⟨p,u,x0,W,X0,R⟩ := H.active i st0 E
        refine ⟨p,u++[e],x0,by rw [W,List.append_assoc],X0,?_⟩
        rw [run_append,R]
        change m=(y.1,m.2)
        exact Prod.ext rfl rfl

theorem run_history (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (w : List (Fin n)) (z : Base d hh Q)
    (H : Chronology d C N hh F x w z) (u : List (Fin n)) :
    Chronology d C N hh F x (w++u)
      (SequentialMarkClock.run (ReportFastSixPrep.step d C N hh F) z u) := by
  induction u generalizing w z with
  | nil => simpa [SequentialMarkClock.run] using H
  | cons e u IH =>
    simpa only [List.append_assoc,List.singleton_append,SequentialMarkClock.run] using
      IH (w++[e]) _ (append_step d C N hh F x w z H e)

theorem prepared_receipts (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : {y : Raw s n // Cached d hh Q y}) (w : List (Fin n))
    (H : (SequentialMarkClock.run (ReportFastSixPrep.step d C N hh F)
      (ReportFastSixPrep.init d hh x) w).2=none) :
    ∀ j : Fin 6,RawReceipt d (C j) x.val w := by
  have T := run_history d C N hh F x.val [] _ (start_history d C N hh F x) w
  intro j
  exact T.past j (by simp [phase,H,j.isLt])

#print axioms append_step
#print axioms prepared_receipts
end L4.ReportFastSixPrepHistory

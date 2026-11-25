import Leader.L4.ReportFastFreshReset

namespace L4.ReportFastSixPrep
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportPrelaunchRank
open ReportOwnerCommandRail
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

abbrev State (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n→Prop) :=
  {x : Raw s n // Cached d hh Q x} × Option (Fin 6 × Option Stage)

def target : Fin 6 := 5

def init (d : Sheet) (hh : ∃ i,h i=true)
    (x : {x : Raw s n // Cached d hh Q x}) : State d hh Q :=
  (x,some (0,none))

def Inv (d : Sheet) (C : Fin 6→Chart h) (hh : ∃ i,h i=true)
    (z : State d hh Q) : Prop :=
  (∀ j,StrongSerial d (C j) z.1.val) ∧
  ∀ j st,z.2=some (j,st) →
    st≠some .done ∧ ReportFastFreshReset.Inv d (C j) hh (z.1,st)

def step (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (e : Fin n) : State d hh Q :=
  let x' : {x : Raw s n // Cached d hh Q x} :=
    ⟨rawNext s z.1.val e,(cached_fibre d N hh Q F).closed _ e z.1.property⟩
  (x',match z.2 with
    | none => none
    | some (j,st) =>
      let m := ReportFastFreshReset.step d (C j) N hh F (z.1,st) e
      if m.2=some .done then
        if H : j.val+1<6 then some (⟨j.val+1,H⟩,none) else none
      else some (j,m.2))

theorem step_raw (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (e : Fin n) :
    (step d C N hh F z e).1.val=rawNext s z.1.val e := rfl

theorem init_inv (d : Sheet) (C : Fin 6→Chart h) (hh : ∃ i,h i=true)
    (x : {x : Raw s n // Cached d hh Q x})
    (S : ∀ j,StrongSerial d (C j) x.val) :
    Inv d C hh (init d hh x) := by
  refine ⟨S,?_⟩
  intro j st E
  have H : (0:Fin 6)=j ∧ (none:Option Stage)=st := by simpa [init] using E
  rcases H with ⟨rfl,rfl⟩
  exact ⟨by decide,ReportFastFreshReset.initial_inv d (C 0) hh x (S 0)⟩

theorem step_closed (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (z : State d hh Q) (I : Inv d C hh z)
    (e : Fin n) : Inv d C hh (step d C N hh F z e) := by
  have S (j : Fin 6) := strong_step d (C j) N hh G F _ z.1.property (I.1 j) digit e
  refine ⟨S,?_⟩
  intro j st E
  cases H : z.2 with
  | none => simp [step,H] at E
  | some q =>
    rcases q with ⟨i,old⟩
    let m := ReportFastFreshReset.step d (C i) N hh F (z.1,old) e
    have E' : (if m.2=some .done then
        if H : i.val+1<6 then some ((⟨i.val+1,H⟩:Fin 6),none) else none
        else some (i,m.2))=some (j,st) := by simpa only [step,H] using E
    by_cases B : m.2=some .done
    · by_cases J : i.val+1<6
      · simp only [if_pos B,dif_pos J,Option.some.injEq,Prod.mk.injEq] at E'
        rcases E' with ⟨rfl,rfl⟩
        exact ⟨by decide,ReportFastFreshReset.initial_inv d _ hh _ (S _)⟩
      · simp [B,J] at E'
    · simp only [if_neg B,Option.some.injEq,Prod.mk.injEq] at E'
      rcases E' with ⟨rfl,rfl⟩
      refine ⟨B,?_⟩
      change ReportFastFreshReset.Inv d (C i) hh m
      exact ReportFastFreshReset.inv_closed d (C i) N hh G F digit (z.1,old) e (I.2 i old H).2

noncomputable def debt (d : Sheet) (C : Fin 6→Chart h) (hh : ∃ i,h i=true)
    (W : Nat) (z : State d hh Q) : Nat :=
  match z.2 with
  | none => ReportFastFreshReset.pubReserve (params d s).digits W
  | some (j,st) => ReportFastFreshReset.prepDebt (params d s).digits W (5-j.val)
      (ReportFastFreshReset.freshDebt d (C j) hh (z.1,st))

theorem debt_bound (d : Sheet) (C : Fin 6→Chart h) (hh : ∃ i,h i=true)
    (W : Nat) (W3 : 3≤W) (Width : ∀ j,(C j).L≤3*W)
    (digit : 0<(params d s).digits) (z : State d hh Q) (I : Inv d C hh z) :
    debt d C hh W z≤518*(params d s).digits*W := by
  apply ReportFastFreshReset.service_fresh_reset_bound (Inv d C hh)
    (debt d C hh W) (params d s).digits W _ z I
  intro y P
  rcases H : y.2 with _|⟨j,st⟩
  · exact .inr (by simp [debt,H])
  · exact .inl ⟨5-j.val,_,by omega,
      ReportFastFreshReset.local_reserve d (C j) hh digit W W3 (Width j) _
        (P.2 j st H).2, by simp [debt,H]⟩

def CurrentConsume (d : Sheet) (C : Fin 6→Chart h) (hh : ∃ i,h i=true)
    (z : State d hh Q) (j : Fin 6) (st : Option Stage) (e : Fin n) : Prop :=
  z.2=some (j,st) ∧ ReportFastFreshReset.FreshConsume d (C j) hh (z.1,st) e

theorem tracked_consume (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (I : Inv d C hh z)
    (j : Fin 6) (st : Option Stage) (H : z.2=some (j,st)) (e : Fin n)
    (Done : (ReportFastFreshReset.step d (C j) N hh F (z.1,st) e).2=some .done) :
    CurrentConsume d C hh z j st e ∧
      (step d C N hh F z e).2=
        (if J : j.val+1<6 then some (⟨j.val+1,J⟩,none) else none) := by
  have T : ¬ReportOwnerReceiptClock.done (z.1,st) := (I.2 j st H).1
  refine ⟨⟨H,(ReportFastFreshReset.consume_crossing d (C j) N hh F
    (z.1,st) (I.2 j st H).2 e).mp ⟨T,Done⟩⟩,?_⟩
  simp [step,H,Done]

theorem target_finish (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (I : Inv d C hh z) (e : Fin n)
    (Live : z.2≠none) (End : (step d C N hh F z e).2=none) :
    ∃ st,CurrentConsume d C hh z target st e ∧
      readPC d (C target) (step d C N hh F z e).1.val=(1,1) ∧
      FullParked d (C target) (step d C N hh F z e).1.val := by
  cases H : z.2 with
  | none => exact False.elim (Live H)
  | some q =>
    rcases q with ⟨j,st⟩
    let m := ReportFastFreshReset.step d (C j) N hh F (z.1,st) e
    have E : (if m.2=some .done then
      if J : j.val+1<6 then some ((⟨j.val+1,J⟩:Fin 6),none) else none
      else some (j,m.2))=none := by simpa only [step,H] using End
    have D : m.2=some .done := by
      by_cases K : m.2=some .done
      · exact K
      · simp [K] at E
    have J : j.val+1≥6 := by
      by_cases K : j.val+1<6
      · simp [D,K] at E
      · omega
    have Je : j=target := by apply Fin.ext; have := j.isLt; change j.val=5; omega
    subst j
    have Pack := tracked_consume d C N hh F z I target st H e D
    have Park := ReportFastFreshReset.crossing_parked d (C target) N hh F
      (z.1,st) (I.2 target st H).2 e ⟨(I.2 target st H).1,D⟩
    exact ⟨st,Pack.1,Park.1,Park.2.1⟩

theorem debt_step (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (W : Nat) (W3 : 3≤W)
    (Width : ∀ j,(C j).L≤3*W) (z : State d hh Q) (I : Inv d C hh z) (e : Fin n) :
    debt d C hh W (step d C N hh F z e)≤debt d C hh W z ∧
      ((step d C N hh F z e).2.map Prod.fst≠z.2.map Prod.fst →
        debt d C hh W (step d C N hh F z e)<debt d C hh W z) := by
  let y := step d C N hh F z e
  change debt d C hh W y≤debt d C hh W z ∧
    (y.2.map Prod.fst≠z.2.map Prod.fst → debt d C hh W y<debt d C hh W z)
  cases H : z.2 with
  | none =>
    have H' : y.2=none := by simp [y,step,H]
    simp [debt,H,H']
  | some q =>
    rcases q with ⟨j,st⟩
    let m := ReportFastFreshReset.step d (C j) N hh F (z.1,st) e
    have Cur := I.2 j st H
    by_cases D : m.2=some .done
    · have A : ReportFastFreshReset.freshDebt d (C j) hh (z.1,st)=1 :=
        (ReportFastFreshReset.crossing_debt d (C j) N hh F (z.1,st) e ⟨Cur.1,D⟩).1
      have E := (tracked_consume d C N hh F z I j st H e D).2
      have LT : debt d C hh W y<debt d C hh W z := by
        by_cases J : j.val+1<6
        · let i : Fin 6 := ⟨j.val+1,J⟩
          have V : y.2=some (i,none) := by simpa only [dif_pos J] using E
          have IC := step_closed d C N hh G F digit z I e
          have R := ReportFastFreshReset.local_reserve d (C i) hh digit W W3 (Width i)
            (y.1,none) (IC.2 i none V).2
          simp only [debt,V,H,A,ReportFastFreshReset.prepDebt]
          have K : 5-j.val=(5-i.val)+1 := by change 5-j.val=5-(j.val+1)+1; omega
          rw [K,Nat.add_mul,Nat.one_mul]
          omega
        · have V : y.2=none := by simpa only [dif_neg J] using E
          simp only [debt,V,H,A,ReportFastFreshReset.prepDebt]
          omega
      exact ⟨Nat.le_of_lt LT,fun _=>LT⟩
    · have V : y.2=some (j,m.2) := by simp [y,step,H,D,m]
      have R := ReportFastFreshReset.freshDebt_idle d (C j) N hh G F digit (z.1,st) Cur.2 e
      change ReportFastFreshReset.freshDebt d (C j) hh (y.1,m.2)≤
        ReportFastFreshReset.freshDebt d (C j) hh (z.1,st) at R
      simp only [debt,H,V,Option.map_some,ne_eq,not_true_eq_false]
      exact ⟨ReportFastFreshReset.prep_idle R,False.elim⟩

#print axioms step_closed
#print axioms debt_bound
#print axioms debt_step
#print axioms tracked_consume
#print axioms target_finish
end L4.ReportFastSixPrep

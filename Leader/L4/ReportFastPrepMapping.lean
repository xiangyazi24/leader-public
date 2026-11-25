import Leader.L4.ReportFastSixPrepTrack
import Leader.L4.ReportFastSixPrepHistory
import Leader.L4.ReportFastDenySteering

namespace L4.ReportFastPrepMapping
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportFastOwnerSupport ReportGateGeometry
open ReportAdaptiveFibre ReportFastRefractory ReportFastSteeringMap
open ReportFastNominationBridge ReportFastDenySteering

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem active_eq_armed (d : Sheet) (B : Fin 5→Chart h) (x : Raw s n)
    (j : Fin 5) : activeRaw d B x j = armed d (B j) x := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [armed_iff]
  simp [activeRaw]

theorem prep_merge_eq_steer (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (B : Fin 5→Chart h)
    (inj : Function.Injective (fun j=>center (B j)))
    (z : ReportFastSixPrepTrack.Base d hh Q) (e : Fin n) :
    mergeSide (ReportFastSixPrepTrack.prepBan d B z) e =
      steerRaw d B denySides z.1.val e := by
  have A : activeRaw d B z.1.val = fun j=>armed d (B j) z.1.val :=
    funext (active_eq_armed d B z.1.val)
  unfold ReportFastSixPrepTrack.prepBan steerRaw
  rw [A]
  generalize (fun j=>armed d (B j) z.1.val)=active
  cases H : makeBan B active denySides e with
  | none =>
    cases K : gateBan B active denySides e with
    | none => simp [mergeSide,H,K]
    | some a =>
      have J := (gate_ban_spec hh G B inj active denySides e a).mp K
      have D := (makeBan_spec hh G B inj active denySides e a).mpr J
      rw [H] at D
      contradiction
  | some a =>
    have J := (makeBan_spec hh G B inj active denySides e a).mp H
    have K := (gate_ban_spec hh G B inj active denySides e a).mpr J
    simp [mergeSide,H,K]

theorem mappedWord_append (d : Sheet) (B : Fin 5→Chart h)
    (policy : Nat → Raw s n → Fin 5 → Bool) (t : Nat)
    (x : Raw s n) (u v : List (Fin n)) :
    mappedWord d B policy t x (u++v) =
      mappedWord d B policy t x u ++
        mappedWord d B policy (t+u.length) (rawRun x (mappedWord d B policy t x u)) v := by
  induction u generalizing t x with
  | nil => simp [mappedWord,rawRun,BStarResetSchedule.run]
  | cons e u IH =>
    let m := steerRaw d B (policy t x) x e
    change m::mappedWord d B policy (t+1) (rawNext s x m) (u++v) =
      (m::mappedWord d B policy (t+1) (rawNext s x m) u) ++
        mappedWord d B policy (t+(e::u).length)
          (rawRun x (m::mappedWord d B policy (t+1) (rawNext s x m) u)) v
    rw [IH]
    rw [show t+1+u.length=t+(e::u).length by simp; omega]
    rfl

theorem mappedWord_length (d : Sheet) (B : Fin 5→Chart h)
    (policy : Nat → Raw s n → Fin 5 → Bool) (t : Nat)
    (x : Raw s n) (v : List (Fin n)) :
    (mappedWord d B policy t x v).length=v.length := by
  induction v generalizing t x with
  | nil => rfl
  | cons e v IH => simp only [mappedWord,List.length_cons,IH]

/-- Recover the precise driver suffix for a boundary already certified on
the actual mapped tape. This does not commute or resample any mark. -/
theorem receiptSuffix_of_mapped_split (d : Sheet) (B : Fin 5→Chart h)
    (policy : Nat → Raw s n → Fin 5 → Bool) (t : Nat)
    (x : Raw s n) (v pre reset post : List (Fin n)) (j : Fin 5)
    (genuine : Generated d (B j) (rawRun x pre) reset .done)
    (split : mappedWord d B policy t x v = pre++reset++post) :
    ReceiptSuffix d B policy x (mappedWord d B policy t x v) j := by
  let k := (pre++reset).length
  let u := v.take k
  let r := v.drop k
  have K : k≤v.length := by
    have E := congrArg List.length split
    rw [mappedWord_length,List.length_append] at E
    change k≤v.length
    omega
  have U : u.length=k := by
    change (v.take k).length=k
    simp [List.length_take,Nat.min_eq_left K]
  have Eq := mappedWord_append d B policy t x u r
  rw [show u++r=v from List.take_append_drop k v,split] at Eq
  have A : (mappedWord d B policy t x u).length=(pre++reset).length :=
    (mappedWord_length d B policy t x u).trans U
  have H : pre++reset=mappedWord d B policy t x u :=
    List.append_inj_left Eq A.symm
  refine ⟨pre,reset,r,t+u.length,genuine,?_⟩
  rw [split,←ShortOwnerEpochJS.raw_append]
  simpa only [←H] using Eq

theorem mappedWord_policy_prefix (d : Sheet) (B : Fin 5→Chart h)
    (P R : Nat → Raw s n → Fin 5 → Bool)
    (t : Nat) (x : Raw s n) (u : List (Fin n))
    (E : ∀ a y,t≤a → a<t+u.length → P a y=R a y) :
    mappedWord d B P t x u=mappedWord d B R t x u := by
  induction u generalizing t x with
  | nil => rfl
  | cons e u IH =>
    have H : P t x=R t x := E t x (Nat.le_refl _) (by simp)
    simp only [mappedWord,H,List.cons.injEq,true_and]
    exact IH _ _ (fun a y L U=>E a y (by omega) (by simp at *; omega))

/-- Use the all-deny preparation monitor on exactly the same word as the
raw steering map. The next observer state is taken at the mapped physical
edge, not at the preimage label. -/
theorem prep_run_mapped (d : Sheet) (C : Fin 6→Chart h)
    (B : Fin 5→Chart h) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q)
    (inj : Function.Injective (fun j=>center (B j)))
    (z : ReportFastSixPrepTrack.Base d hh Q) (v : List (Fin n)) (t : Nat) :
    SequentialMarkClock.run
        (fun z e=>ReportFastSixPrep.step d C N hh F z
          (mergeSide (ReportFastSixPrepTrack.prepBan d B z) e)) z v =
      SequentialMarkClock.run (ReportFastSixPrep.step d C N hh F) z
        (mappedWord d B (fun _ _=>denySides) t z.1.val v) := by
  induction v generalizing z t with
  | nil => rfl
  | cons e v IH =>
    simp only [SequentialMarkClock.run,mappedWord,
      prep_merge_eq_steer d hh G B inj z e]
    rw [IH]
    rfl

/-- All five rivals use genuine own RESET histories from one preparation
word, and later driver draws keep their actual chronology. The profile
may change after the preparation prefix. -/
theorem prepared_mapped_receiptSuffix
    (d : Sheet) (C : Fin 6→Chart h) (B : Fin 5→Chart h)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (inj : Function.Injective (fun j=>center (B j)))
    (incl : ∀ j, ∃ i,C i=B j)
    (x : {y : Raw s n // Cached d hh Q y}) (v tail : List (Fin n)) (t : Nat)
    (policy : Nat → Raw s n → Fin 5 → Bool)
    (prior : ∀ a y,t≤a → a<t+v.length → policy a y=denySides)
    (done : (SequentialMarkClock.run
      (fun z e=>ReportFastSixPrep.step d C N hh F z
        (mergeSide (ReportFastSixPrepTrack.prepBan d B z) e))
      (ReportFastSixPrep.init d hh x) v).2=none) :
    ∀ j, ReceiptSuffix d B policy x.val (mappedWord d B policy t x.val (v++tail)) j := by
  have E := mappedWord_policy_prefix d B policy (fun _ _=>denySides) t x.val v prior
  have H := prep_run_mapped d C B N hh G F inj (ReportFastSixPrep.init d hh x) v t
  rw [H] at done
  change (SequentialMarkClock.run (ReportFastSixPrep.step d C N hh F)
    (ReportFastSixPrep.init d hh x) (mappedWord d B (fun _ _=>denySides) t x.val v)).2=none at done
  rw [←E] at done
  have R := ReportFastSixPrepHistory.prepared_receipts d C N hh F x _ done
  intro j
  obtain ⟨i,I⟩ := incl j
  obtain ⟨pre,u,post,S,U⟩ := R i
  rw [I] at U
  apply receiptSuffix_of_mapped_split d B policy t x.val (v++tail) pre u
    (post++mappedWord d B policy (t+v.length) (rawRun x.val (mappedWord d B policy t x.val v)) tail) j U
  rw [mappedWord_append]
  calc
    mappedWord d B policy t x.val v ++
        mappedWord d B policy (t+v.length) (rawRun x.val (mappedWord d B policy t x.val v)) tail =
      (pre++u++post) ++
        mappedWord d B policy (t+v.length) (rawRun x.val (mappedWord d B policy t x.val v)) tail :=
        congrArg (fun z=>z++_) S
    _ = _ := List.append_assoc _ _ _

#print axioms active_eq_armed
#print axioms prep_merge_eq_steer
#print axioms mappedWord_append
#print axioms mappedWord_length
#print axioms receiptSuffix_of_mapped_split
#print axioms mappedWord_policy_prefix
#print axioms prep_run_mapped
#print axioms prepared_mapped_receiptSuffix

end L4.ReportFastPrepMapping

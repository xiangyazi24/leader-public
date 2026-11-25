import Leader.L4.ReportFastSixPrepPlateau
import Leader.L4.ReportFastNominationBridge

namespace L4.ReportFastSixPrepTrack
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportFastSixPrepPlateau
open ReportFastNominationBridge ReportFastOwnerSupport

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
abbrev Base (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n→Prop) :=
  ReportFastSixPrep.State d hh Q

def hit {d : Sheet} {hh : ∃ i,h i=true} (z : Base d hh Q) : Prop := z.2=none

def nom (d : Sheet) (C : Fin 6→Chart h) (hh : ∃ i,h i=true)
    (z : Base d hh Q) (q : Fin n) : Prop :=
  ∃ j st,z.2=some (j,st) ∧ ReportFastFreshReset.NomAt d (C j) hh (z.1,st) q

noncomputable def prepBan {hh : ∃ i,h i=true} (d : Sheet) (B : Fin 5→Chart h)
    (z : Base d hh Q) : Fin n→Option (Fin n) :=
  makeBan B (activeRaw d B z.1.val) denySides

theorem prep_rows (d : Sheet) (C : Fin 6→Chart h) (B : Fin 5→Chart h)
    (inc : ∀ j,∃ i,C i=B j)
    (inj : Function.Injective (fun j=>center (B j))) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (W : Nat) (W3 : 3≤W) (Width : ∀ j,(C j).L≤3*W) :
    ReportFastNominationBridge.Rows (ReportFastSixPrep.step d C N hh F) (ReportFastSixPrep.Inv d C hh) hit
      (ReportFastSixPrep.debt d C hh W) (prepBan d B) (nom d C hh)
      (fun z q=>Spent d B z.1.val q) := by
  have SS (z : Base d hh Q) (I : ReportFastSixPrep.Inv d C hh z) (j : Fin 5) :
      ReportOwnerCommandRail.StrongSerial d (B j) z.1.val := by
    obtain ⟨i,E⟩ := inc j
    exact E ▸ I.1 i
  constructor
  · intro z e I
    exact ReportFastSixPrep.step_closed d C N hh G F digit z I e
  · intro z e _ H
    change z.2=none at H
    simp [hit,ReportFastSixPrep.step,H]
  · intro z e I _
    exact (ReportFastSixPrep.debt_step d C N hh G F digit W W3 Width z I e).1
  · intro z I H
    cases E : z.2 with
    | none => exact False.elim (H E)
    | some p =>
      rcases p with ⟨j,st⟩
      obtain ⟨q,A⟩ := ReportFastFreshReset.nom_exists d (C j) hh (z.1,st)
        (I.2 j st E).2 (I.2 j st E).1
      exact ⟨q,j,st,E,A⟩
  · intro z q I _ H
    obtain ⟨j,st,E,A⟩ := H
    have L := ReportFastFreshReset.nom_pays d (C j) N hh G F digit
      (z.1,st) (I.2 j st E).2 q A
    have D := ReportFastSixPrep.debt_step d C N hh G F digit W W3 Width z I q
    by_cases H : (ReportFastSixPrep.step d C N hh F z q).2.map Prod.fst=some j
    · have NE : ReportFastSixPrep.debt d C hh W (ReportFastSixPrep.step d C N hh F z q) ≠
          ReportFastSixPrep.debt d C hh W z :=
        fun eq=>Nat.ne_of_lt L ((same_phase_debt_iff d C N hh F W z j st E q H).mp eq)
      exact Nat.lt_of_le_of_ne D.1 NE
    · apply D.2
      simpa only [E,Option.map_some] using H
  · intro z q e I _ H Eq
    obtain ⟨j,st,E,A⟩ := H
    have D := ReportFastSixPrep.debt_step d C N hh G F digit W W3 Width z I e
    have Ret : (ReportFastSixPrep.step d C N hh F z e).2.map Prod.fst=some j := by
      apply Classical.byContradiction
      intro H
      have L := D.2 (by simpa only [E,Option.map_some] using H)
      exact Nat.ne_of_lt L Eq
    obtain ⟨Stage,Raw,_⟩ := retained_stage_of_same_index d C N hh F z j st E e Ret
    have Local := ReportFastFreshReset.nom_plateau d (C j) N hh G F digit (z.1,st)
      (I.2 j st E).2 q e A ((same_phase_debt_iff d C N hh F W z j st E e Ret).mp Eq)
    refine ⟨j,_,Stage,?_⟩
    rw [Raw]
    exact Local
  · intro z q a I _ E
    exact ban_mate_spends d N hh G F B z.1.val z.1.property (SS z I)
      (activeRaw d B z.1.val) denySides (prepBan d B z)
      (makeBan_spec hh G B inj _ _) (activeRaw_sound d B z.1.val) q a E
  · intro z q e I _ A E
    exact spent_step d N hh G F B z.1.val z.1.property (SS z I) q e E A
  · intro z q _ _ A
    exact spent_unblocked d hh G B inj z.1.val q (activeRaw d B z.1.val)
      denySides (prepBan d B z) (makeBan_spec hh G B inj _ _)
      (activeRaw_sound d B z.1.val) A

abbrev Prepared (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n→Prop) :=
  Track (Base d hh Q) n

section Runner
variable (d : Sheet) (C : Fin 6→Chart h) (B : Fin 5→Chart h)
variable (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) (W : Nat)

def good (z : Prepared d hh Q) : Prop :=
  GoodTrack (ReportFastSixPrep.Inv d C hh) hit (nom d C hh)
    (fun z q=>Spent d B z.1.val q) z

noncomputable def step (z : Prepared d hh Q) (e : Fin n) : Prepared d hh Q :=
  next (ReportFastSixPrep.step d C N hh F) (ReportFastSixPrep.debt d C hh W)
    (prepBan d B) (nom d C hh) z e

theorem step_raw (z : Prepared d hh Q) (e : Fin n) :
    (step d C B N hh F W z e).base.1.val=rawNext s z.base.1.val e := by
  rw [step, next_base]
  rfl

theorem hit_sticky (z : Prepared d hh Q) (e : Fin n) (H : hit z.base) :
    hit (step d C B N hh F W z e).base := by
  rw [step,next_base]
  exact show (ReportFastSixPrep.step d C N hh F z.base e).2=none by
    simp [ReportFastSixPrep.step,show z.base.2=none from H]

theorem exact_final_cut (z : Prepared d hh Q) (e : Fin n)
    (I : good d C B hh z) (L : ¬hit z.base) (H : hit (step d C B N hh F W z e).base) :
    ∃ st,ReportFastSixPrep.CurrentConsume d C hh z.base ReportFastSixPrep.target st e ∧
      ReportPrelaunchClock.readPC d (C ReportFastSixPrep.target)
        (step d C B N hh F W z e).base.1.val=(1,1) ∧
      FullParked d (C ReportFastSixPrep.target) (step d C B N hh F W z e).base.1.val := by
  rw [step,next_base] at H ⊢
  exact ReportFastSixPrep.target_finish d C N hh F z.base I.1 e L H

variable (inc : ∀ j,∃ i,C i=B j)
variable (inj : Function.Injective (fun j=>center (B j))) (G : GapInput h)
variable (digit : 0<(params d s).digits) (W3 : 3≤W) (Width : ∀ j,(C j).L≤3*W)

include inc inj G digit W3 Width
include N F W in
theorem start_good (x : {x : Raw s n // Cached d hh Q x})
    (S : ∀ j,ReportOwnerCommandRail.StrongSerial d (C j) x.val) (e : Fin n) :
    good d C B hh (start (nom d C hh) (ReportFastSixPrep.init d hh x) e) :=
  ReportFastNominationBridge.start_good _ _ _ _ _ _ _
    (prep_rows d C B inc inj N hh G F digit W W3 Width) _ e
    (ReportFastSixPrep.init_inv d C hh x S)

theorem all_mark (z : Prepared d hh Q) (e : Fin n) (I : good d C B hh z) :
    good d C B hh (step d C B N hh F W z e) :=
  track_closed _ _ _ _ _ _ _ (prep_rows d C B inc inj N hh G F digit W W3 Width) z e I

theorem service_debt :
    let D := debt (ReportFastSixPrep.debt d C hh W)
    let S := step d C B N hh F W
    let b := ban (prepBan d B)
    ∀ z e,good d C B hh z→finish hit z≠true→
      D (S z (ReportAdaptiveFibre.mergeSide (b z) e))≤D z :=
  service_phase_debt _ _ _ _ _ _ _ (prep_rows d C B inc inj N hh G F digit W W3 Width)

omit inc inj G digit W3 Width
theorem service_credit :
    let D := debt (ReportFastSixPrep.debt d C hh W)
    let S := step d C B N hh F W
    let b := ban (prepBan d B)
    ∀ z e,good d C B hh z→finish hit z≠true→
      D (S z (ReportAdaptiveFibre.mergeSide (b z) e))=D z→
      (credit (S z (ReportAdaptiveFibre.mergeSide (b z) e))).toNat≤(credit z).toNat :=
  service_no_rearm_credit _ _ hit _ _ _ _

include inc inj G digit W3 Width
theorem service_nominate :
    let D := debt (ReportFastSixPrep.debt d C hh W)
    let S := step d C B N hh F W
    let b := ban (prepBan d B)
    ∀ z,good d C B hh z→finish hit z≠true→
      ∃ a e,ReportAdaptiveFibre.mergeSide (b z) e=a ∧
        (D (S z a)<D z ∨ (D (S z a)=D z ∧ credit z=true ∧ credit (S z a)=false)) :=
  service_phase_nominate _ _ _ _ _ _ _ (prep_rows d C B inc inj N hh G F digit W W3 Width)

end Runner

#print axioms prep_rows
#print axioms hit_sticky
#print axioms exact_final_cut
#print axioms start_good
#print axioms all_mark
#print axioms service_debt
#print axioms service_credit
#print axioms service_nominate
end L4.ReportFastSixPrepTrack

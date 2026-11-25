import Leader.L4.ScoredTapeRenewal
import Leader.L4.PhysicalRaceExactCut

namespace L4.ScoredTapeCertificates
open ScoredTapeSerial ScoredTapeRenewal
open ResetReturnIID
open PhysicalRaceExactCut
open StoppedDoorRaceIID (Decision score)

structure Certificate (n a b A : Nat) (P : Word n→Prop) where
  reader : Reader n a b A
  sound : ∀ x : Reader.Passed reader, P (reader.word x.val)

namespace Certificate
variable {n a b c A B : Nat} {P : Word n→Prop}

noncomputable def bind (hn : 0<n) (L : Certificate n a b A P)
    (S : Word n→Word n→Prop)
    (R : ∀ w, P w→Certificate n b c B (S w)) :
    Certificate n a c (A+B) (fun w=>∃ u v,w=u++v ∧ P u ∧ S u v) where
  reader := Reader.bind L.reader (fun x=>(R _ (L.sound x)).reader) hn
  sound := by
    intro z
    obtain ⟨x,y,_,yv,yd,yr,W⟩ := Reader.accepted_bind _ _ hn z.val z.property.1 z.property.2.1 z.property.2.2
    exact ⟨_,_,W,L.sound x,(R _ (L.sound x)).sound ⟨y,yv,yd,yr⟩⟩

def map {Q : Word n→Prop} (L : Certificate n a b A P) (imp : ∀ w,P w→Q w) :
    Certificate n a b A Q where
  reader := L.reader
  sound := fun x=>imp _ (L.sound x)

def idle (P : Word n→Prop) (a A : Nat) (cap : a≤729)
    (mean : Height.IIDExpectedHittingTimeAtMost appendTape P [] A) : Certificate n a a A P where
  reader := wait P a A cap mean
  sound := fun x=>x.property.2.1
end Certificate

def RaceOutcome {n : Nat} (P : Word n→Prop) (d : Fin n) (k : Nat) (w : Word n) : Prop :=
  ∃ pre raced,w=pre++raced ∧ P pre ∧ Exact d k raced

/-- Exact first-arrival plus an incident race, retaining no padding in
the scored certificate. Padding is managed only by the renewal lift. -/
noncomputable def race {n : Nat} (hn : 4≤n) (P : Word n→Prop) (d : Fin n)
    (later k : Nat) (hk : 0<k) (hc : later+k≤6) (A : Nat)
    (mean : Height.IIDExpectedHittingTimeAtMost appendTape P [] A) :
    Certificate n (score later (.live k)) (score later .accept) (A+n*k) (RaceOutcome P d k) where
  reader := {
    State := OrderedRaceTape.State n
    start := OrderedRaceTape.enter P k []
    tick := OrderedRaceTape.tick P d k
    word := OrderedRaceTape.word
    word_start := OrderedRaceTape.word_enter P k []
    word_step := OrderedRaceTape.word_tick P d k
    valid := ValidFirst P d k
    valid_start := validFirst_start P d k
    valid_step := validFirst_step P d k
    done := OrderedRaceTape.done
    reject := OrderedRaceTape.rejected
    credit := OrderedRaceTape.reserve later k
    initial_credit := OrderedRaceTape.reserve_enter P k later []
    cap := by
      intro x _
      cases x with
      | waiting w => exact AdaptiveDoorCredit.score_cap (.live (later+k))
      | racing pre v q =>
        cases q with
        | live j => exact AdaptiveDoorCredit.score_cap (.live (later+j))
        | accept => exact AdaptiveDoorCredit.score_cap (.live later)
        | reject => exact Nat.zero_le _
    lost := by
      intro x _ D F
      cases x with
      | waiting w => cases D
      | racing pre v q =>
        cases q with
        | live j => cases D
        | accept => cases F
        | reject => rfl
    paid := by
      intro x _ D F
      cases x with
      | waiting w => cases D
      | racing pre v q =>
        cases q with
        | live j => cases D
        | accept => rfl
        | reject => exact (F trivial).elim
    localLaw := by
      intro x V D
      apply OrderedRaceTape.reserve_localLaw hn P d later k hc x D
      intro pre v j hx
      subst x
      exact OrderedRaceTape.remaining_bounded d k hk v j V.1.2.symm
    mean := OrderedRaceTape.combined_expected (by omega) P d k hk A mean }
  sound := by
    rintro ⟨x,V,D,F⟩
    cases x with
    | waiting w => cases D
    | racing pre v q =>
      cases q with
      | live j => cases D
      | reject => exact (F trivial).elim
      | accept =>
        obtain ⟨H,E⟩ := exact_of_validFirst_accept P d k hk pre v V
        exact ⟨pre,v,rfl,H.1,E⟩

end L4.ScoredTapeCertificates

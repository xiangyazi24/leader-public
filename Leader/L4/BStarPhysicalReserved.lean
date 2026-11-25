import Leader.L4.BStarRecoveredReveal
import Leader.L4.BStarLiveReservation
import Leader.L4.BStarEpochLift

namespace L4.BStarPhysicalReserved
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarPhysicalPairLaw BStarGrantWriterHistory BStarLiveReservation BStarEpochLift BStarReceiptKey
set_option maxRecDepth 4096

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

noncomputable def admittedRead (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (w : List (Fin n)) (t : Nat) : Option (Fin n×Bool) := by
  classical
  exact if H : t<w.length then
    (BStarRecoveredReveal.reveal hp base initial hh start (w.take t) w[t]).map
      (fun v => (v.1.1,v.2))
  else none

def publishes (initial : X) (w : List (Fin n)) (t : Nat) (i : Fin n) : Prop :=
  ∃ H : t<w.length, ¬NoPublication hp (run initial (w.take t)) w[t] i

noncomputable def cutReserved (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (i : Fin n) : Option Bool :=
  reserved (admittedRead hp base initial hh start history) (publishes hp initial history) history.length i

theorem read_prefix (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history w : List (Fin n)) (t : Nat) (old : t<history.length) :
    admittedRead hp base initial hh start (history++w) t =
      admittedRead hp base initial hh start history t := by
  have full : t<(history++w).length := by simp only [List.length_append]; omega
  unfold admittedRead
  rw [dif_pos full,dif_pos old,List.take_append_of_le_length (Nat.le_of_lt old),
    List.getElem_append_left old]

theorem publication_prefix (initial : X) (history w : List (Fin n)) (t : Nat)
    (i : Fin n) (old : t<history.length) :
    publishes hp initial (history++w) t i ↔ publishes hp initial history t i := by
  have full : t<(history++w).length := by simp only [List.length_append]; omega
  have eq : (history++w).take t=history.take t := List.take_append_of_le_length (Nat.le_of_lt old)
  constructor
  · rintro ⟨h,pub⟩
    refine ⟨old,?_⟩
    rw [eq,List.getElem_append_left old] at pub
    exact pub
  · rintro ⟨h,pub⟩
    refine ⟨full,?_⟩
    rw [eq,List.getElem_append_left old]
    exact pub

/-- A recovery-admitted read identified retrospectively by an actual
publication transports to the cut's retained bit. The checker only
requires separation by physical publications before the cut, not that
those earlier publications were counted as native increments. -/
theorem cut_reserved_of_read (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history future : List (Fin n)) (i : Fin n)
    (separate : ∀ a b p q, a<b → b<history.length →
      admittedRead hp base initial hh start history a=some (i,p) →
      admittedRead hp base initial hh start history b=some (i,q) →
      ∃ j,a≤j ∧ j<b ∧ publishes hp initial history j i)
    (atRead atWrite : Nat) (b : Bool) (earlier : atRead<history.length)
    (later : history.length≤atWrite)
    (readOk : admittedRead hp base initial hh start (history++future) atRead=some (i,b))
    (before : ∀ j,atRead≤j → j<atWrite → ¬publishes hp initial (history++future) j i) :
    cutReserved hp base initial hh start history i=some b := by
  unfold cutReserved
  apply receipt_uses_reserved _ _ _ _ separate atRead atWrite b earlier later
  · exact (read_prefix hp base initial hh start history future atRead earlier).symm.trans readOk
  · intro j a W pub
    by_cases old : j<history.length
    · exact before j a W ((publication_prefix hp initial history future j i old).mpr pub)
    · obtain ⟨h,_⟩ := pub
      omega

noncomputable def reserveAtKey (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (i : Fin n) (tick : Nat) : Option Bool :=
  if tick=traceCount hp base initial hh start history i then
    cutReserved hp base initial hh start history i else none

/-- An earlier admitted read matched to a later publication uses the
stopped owner's current key, not a pre-recovery first-hit key. -/
theorem old_receipt_key (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history future : List (Fin n)) (i : Fin n)
    (separate : ∀ a b p q, a<b → b<history.length →
      admittedRead hp base initial hh start history a=some (i,p) →
      admittedRead hp base initial hh start history b=some (i,q) →
      ∃ j,a≤j ∧ j<b ∧ publishes hp initial history j i)
    (atRead : Nat) (b : Bool) (earlier : atRead<history.length)
    (readOk : admittedRead hp base initial hh start (history++future) atRead=some (i,b))
    (before : ∀ j,atRead≤j → j<(history++future).length →
      ¬publishes hp initial (history++future) j i) :
    reserveAtKey hp base initial hh start history i
      (traceCount hp base initial hh start (history++future) i)=some b := by
  have live : cutReserved hp base initial hh start history i=some b :=
    cut_reserved_of_read hp base initial hh start history future i separate atRead _
      b earlier (by simp) readOk before
  have silent : BeforePublication hp (run initial history) i future := by
    intro pre e tail split
    apply Classical.byContradiction
    intro bad
    have tape : history++future=(history++pre)++e::tail :=
      (congrArg (history++·) split).trans (List.append_assoc _ _ _).symm
    let j := (history++pre).length
    have jt : j<(history++future).length := by rw [tape]; simp [j]
    have old : atRead≤j := by simp only [j,List.length_append]; omega
    have prev : (history++future).take j=history++pre := by
      rw [tape]
      exact List.take_append_length
    have mark : (history++future)[j]=e := by
      apply Option.some.inj
      rw [←List.getElem?_eq_getElem jt,tape]
      change (((history++pre)++e::tail)[(history++pre).length]?)=some e
      rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
      rfl
    refine before j old jt ⟨jt,?_⟩
    rw [prev,mark,BStarResetSchedule.run_append]
    exact bad
  have eq : traceCount hp base initial hh start (history++future) i=
      traceCount hp base initial hh start history i :=
    count_before_publication hp base initial hh start history future i silent
  simp only [reserveAtKey,eq,if_true,live]

#print axioms old_receipt_key
#print axioms read_prefix
#print axioms publication_prefix
#print axioms cut_reserved_of_read
end L4.BStarPhysicalReserved

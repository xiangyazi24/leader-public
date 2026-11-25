import Leader.L4.BStarRecoveredReadSeparation
import Leader.L4.BStarPhysicalReserved

namespace L4.BStarReservationJoin
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarCustodyCuts BStarLongFixedRouting BStarAcquireRailCoverage BStarClearanceOffset
open BStarPhysicalPairLaw BStarRecoveredReadSeparation BStarPhysicalReserved BStarEpochLift

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- The admitted observer is exactly the original observer on any
suffix starting at or after the common recovery cut. -/
theorem first_after_common {base initial : X} (hh : ∃ i,oldH6 B base i=true)
    (u v : List (Fin n)) (cuts : CutFacts hp base initial u v) (start : Fin n→Nat)
    (key : Key n) (past w : List (Fin n)) :
    firstRaw (BStarRecoveredReveal.reveal hp base initial hh start) key ((u++v)++past) w =
      firstRaw (reveal hp base hh initial (ownerAt hp base hh) start) key ((u++v)++past) w := by
  induction w generalizing past with
  | nil => rfl
  | cons e w ih =>
    simp only [firstRaw]
    have here := BStarRecoveredReveal.agrees_if_admitted hp base initial hh start ((u++v)++past) e
      (fun gate _=> BStarRecoveredReveal.admitted_append hp past
        (BStarRecoveredReveal.common_admission hp hh u v cuts gate))
    rw [here, List.append_assoc (u++v) past [e]]
    have tailEq := ih (past++[e])
    cases z : reveal hp base hh initial (ownerAt hp base hh) start ((u++v)++past) e with
    | none => exact tailEq
    | some p =>
      obtain ⟨j,b⟩ := p
      rw [tailEq]

/-- For a genuinely admitted pending read, the cut reservation is
forced at the same absolute key used by any later matching receipt.
The separation premise is discharged by prior same-owner physical
publication, without reusing an INC semantics before common custody. -/
theorem reserved_of_admitted_old_receipt {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    (Q : X→Prop) (I : Q initial) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (offset : correct (oldH6 B base) hh 5 initial)
    (coherent : ∀ x,Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (start : Fin n→Nat) (history future : List (Fin n)) (i : Fin n)
    (atRead : Nat) (b : Bool) (earlier : atRead<history.length)
    (readOk : admittedRead hp base initial hh start (history++future) atRead=some (i,b))
    (before : ∀ j,atRead≤j → j<(history++future).length →
      ¬publishes hp initial (history++future) j i) :
    reserveAtKey hp base initial hh start history i
      (traceCount hp base initial hh start (history++future) i)=some b := by
  exact old_receipt_key hp base initial hh start history future i
    (separates_stopped_tape hp Q I fiber closed sep offset coherent heads cont start history i)
    atRead b earlier readOk before

end L4.BStarReservationJoin

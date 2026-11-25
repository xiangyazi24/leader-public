import Leader.L4.BStarGrantReaderHistory
import Leader.L4.BStarWonCapture
import Leader.L4.BStarFirstCut
import Leader.L4.BStarBodyBankHistory
import Leader.L4.BStarGrantWriterHistory

namespace L4.BStarCapturedHeader
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken
open BStarH6WordChart BStarLongTransport BStarLongEvents BStarLongGrant
open BStarGrantBirth BStarCaptureInterval BStarFirstCut

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A reader's packed header sample is from its actual winning mark.
On this same word it agrees with the physical readout at all later
live prefixes. This does not assert body digits or source receipt
provenance. -/
theorem reader_same_tape (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (w : List (Fin n)) (i : Fin n) (j : Fin 3) (ne : j≠1) (t : Nat)
    (born : BirthAfter hp x w i j t) :
    ∃ lead e tail, w=lead++e::tail ∧ t≤lead.length ∧
      let old := run x lead
      let g := oldPair B old e
      let raw : Pair (BitVec LW) := ((old e).long,(old (rightNeighbor e)).long)
      (∃ C p,
        (C,BStarLongCommand.Offer.advance (capture (old i).long j p true))∈actualOffers g raw) ∧
      ∀ u v, tail=u++v →
        let y := run x (lead++e::u)
        selectedHeader (y i).long=selectedHeader (old i).long ∧
        headerBits (y i).long=headerBits (old i).long := by
  obtain ⟨lead,e,tail,W,T,_,won,life⟩ := born
  obtain ⟨C,p,_,_,_,_,_,_,_,A⟩ := BStarWonCapture.won_capture hp _ e i j won
  refine ⟨lead,e,tail,W,T,⟨C,p,A⟩,?_⟩
  intro u v E
  simp only [BStarResetSchedule.run_append]
  exact BStarGrantReaderHistory.header_readout_interval hp sep (run x lead) e i j ne won tail life u v E

/-- Once body custody is supplied on the same interval, the full
reader operand, not only its packed header, has a common physical
readout. The body witness includes the acquisition mark itself. -/
theorem reader_operand (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (e i : Fin n) (j : Fin 3) (ne : j≠1)
    (won : WonAt hp x e i j) (w : List (Fin n))
    (life : Continuous hp (step x e) i j w)
    (sites : Fin r → Fin n)
    (custody : ∀ (d : Fin r), sites d≠i → ∀ pre m tail, e::w=pre++m::tail →
      BStarBodyBankHistory.BodyCustody hp (run x pre) m (sites d)
        (BStarLongPublication.readSel (x i).long)) :
    let y := run x (e::w)
    selectedHeader (y i).long=selectedHeader (x i).long ∧
      ∀ d, (payloadView (BStarLongPublication.readSel (y i).long) (y (sites d)).long).1=
        (payloadView (BStarLongPublication.readSel (x i).long) (x (sites d)).long).1 := by
  dsimp only
  have T := BStarGrantReaderHistory.header_interval hp sep x e i j ne won w life w [] (by simp)
  have R := BStarGrantReaderHistory.header_readout_interval hp sep x e i j ne won w life w [] (by simp)
  refine ⟨R.1,?_⟩
  intro d
  have E : BStarLongPublication.readSel ((run x (e::w)) i).long=
      BStarLongPublication.readSel (x i).long := T.1
  rw [E]
  by_cases head : sites d=i
  · rw [head]
    exact congrArg Prod.fst T.2.1
  · have h := BStarBodyBankHistory.body_interval hp sep x (sites d)
      (BStarLongPublication.readSel (x i).long) (e::w) (custody d head)
    exact congrArg Prod.fst (held_trace_reads h).2

/-- The center writer keeps the same selected operand until its
first authorized publication. Own STAGE/SEAL at the header need no
extra assumption here; only protected body-digit custody is supplied. -/
theorem writer_operand (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (e i : Fin n) (won : WonAt hp x e i 1) (w : List (Fin n))
    (life : Continuous hp (step x e) i 1 w)
    (pre : BStarGrantWriterHistory.BeforePublication hp (step x e) i w)
    (sites : Fin r → Fin n)
    (custody : ∀ (d : Fin r), sites d≠i → ∀ lead m tail, e::w=lead++m::tail →
      BStarBodyBankHistory.BodyCustody hp (run x lead) m (sites d)
        (BStarLongPublication.readSel (x i).long)) :
    let y := run x (e::w)
    selectedHeader (y i).long=selectedHeader (x i).long ∧
      ∀ d, (payloadView (BStarLongPublication.readSel (y i).long) (y (sites d)).long).1=
        (payloadView (BStarLongPublication.readSel (x i).long) (x (sites d)).long).1 := by
  dsimp only
  obtain ⟨S,V,_,_,_⟩ := BStarGrantWriterHistory.header_interval hp sep x e i won w life pre w [] (by simp)
  have E : BStarLongPublication.readSel ((run x (e::w)) i).long=
      BStarLongPublication.readSel (x i).long := S
  have V' : payloadView (BStarLongPublication.readSel (x i).long) ((run x (e::w)) i).long=
      payloadView (BStarLongPublication.readSel (x i).long) (x i).long := V
  constructor
  · unfold selectedHeader
    rw [E,V']
  · intro d
    rw [E]
    by_cases head : sites d=i
    · rw [head]
      exact congrArg Prod.fst V'
    · have h := BStarBodyBankHistory.body_interval hp sep x (sites d)
        (BStarLongPublication.readSel (x i).long) (e::w) (custody d head)
      exact congrArg Prod.fst (held_trace_reads h).2

end L4.BStarCapturedHeader

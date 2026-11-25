import Leader.L4.BStarCopyLeftOneCapture
import Leader.L4.BStarCopyRightAcquireBank
import Leader.L4.BStarPostCutOperands

namespace L4.BStarCopyLeftAcquireBank
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarCopyRightStrip (addr)
open BStarCopyLeftStrip BStarCopyLeftInjectionMark
open BStarCopyRightAcquireBank (packed_eq_of_nibbles truncate)
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors BStarResetChartTouch
open BStarClearanceDataChart BStarLongFiberOwner BStarLongLayout
open BStarCommitOperands BStarCutOperandReadout BStarCaptureInterval
open BStarLongCommandData BStarGrantBirth BStarGrantWriterHistory BStarLongDoor

/-- The two high capture bits are the original left incidence,
not the controller's current selector or the centre operand. -/
theorem left_capture_val (x : BitVec LW) :
    ((capturedSelector 0).read x).toNat=(captures.read x).toNat/16%4 := by
  have E : (capturedSelector 0).read x=(captures.read x).extractLsb' 4 2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have H : 4+i<6 := by omega
    simp [Field.read,capturedSelector,captures,hi,H]
    congr 1
    omega
  rw [E,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

theorem left_bank_from_ack (launch ack : BitVec LW) (bank s : Fin 3)
    (fromLaunch : bank.val=(captures.read launch).toNat/16%4)
    (sameCapture : captures.read launch=captures.read ack)
    (fromAck : ((capturedSelector 0).read ack).toNat=s.val) :
    bank=s := by
  apply Fin.ext
  rw [fromLaunch,sameCapture,←left_capture_val,fromAck]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- The source LS word starts at the owner K0 header and every inside
source digit is in that same word, not the adjacent center word. -/
theorem ls_word_sites {base : X} (hh : ∃ v,oldH6 B base v=true)
    (owner : Owners (oldH6 B base)) (a : Fin n) (seam width : Nat)
    (strip : Strip B base a seam width)
    (root : a=(endpoint (oldH6 B base) hh owner 0).1) (bound : r≤seam) :
    WordSites (oldH6 B base) (endpoint (oldH6 B base) hh owner 0).1
      (fun d : Fin r => addr a d.val) := by
  intro d ne
  have pos : 0<d.val := by
    by_cases Z : d.val=0
    · have E : addr a 0=a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
      exact (ne (by change addr a d.val=_; rw [Z,E,root])).elim
    · omega
  have K : d.val<seam := Nat.lt_of_lt_of_le d.isLt bound
  exact ⟨strip.ls_body _ pos K,root ▸ (ls_same_word hp strip hh _ K).symm⟩

#print axioms left_capture_val
#print axioms left_bank_from_ack
#print axioms ls_word_sites

/-- The full left packed-bank operand is invariant at every earlier
LOAD cut under the original unbroken left ACQUIRE reader lifetime.
The bank used by LOAD is matched to ACK's high/left captured selector
rather than compared to whatever the source door's selector is now. -/
theorem packed_before_load {base x : X} {cut whole : List (Fin n)}
    (hh : ∃ v,oldH6 B base v=true)
    (owner : Owners (oldH6 B base)) (a : Fin n) (seam width : Nat)
    (strip : Strip B base a seam width)
    (root : a=(endpoint (oldH6 B base) hh owner 0).1)
    (bound : r≤seam)
    (A : Acquisition hp x cut whole (endpoint (oldH6 B base) hh owner 0).1 0)
    (u v loadTail : List (Fin n)) (split : A.post=u++v)
    (exactLoad : cut++loadTail=A.lead++A.mark::u)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ w,oldH6 B (play x (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play x (cut++w)) e z
      (endpoint (oldH6 B base) hh owner 0).1)
    (launch ack : BitVec LW) (bank : Fin 3)
    (bank8 : bank.val=(captures.read launch).toNat/16%4)
    (hold : captures.read launch=captures.read ack)
    (ack0 : ((capturedSelector 0).read ack).toNat=
      (BStarLongPublication.readSel ((play x A.lead) (endpoint (oldH6 B base) hh owner 0).1).long).val) :
    ∀ digit : Fin r,
      let i := addr a digit.val
      let old := play x (cut++loadTail)
      let captured := play x A.lead
      let header := (endpoint (oldH6 B base) hh owner 0).1
      oldBankPacket (old i).long bank =
        oldBankPacket (captured i).long (BStarLongPublication.readSel (captured header).long) := by
  let header := (endpoint (oldH6 B base) hh owner 0).1
  let sites := fun d : Fin r => addr a d.val
  let short := truncate hp A u v loadTail split exactLoad
  have WS : WordSites (oldH6 B base) header sites :=
    ls_word_sites hp hh owner a seam width strip root bound
  have E := operand_at_acquire hp base x cut loadTail header 0 sites short sep layout auth WS
  let old := play x (cut++loadTail)
  let captured := play x A.lead
  let sel := BStarLongPublication.readSel (captured header).long
  have equalSel : BStarLongPublication.readSel (old header).long=sel :=
    congrArg (fun z => z.1.1) E
  have equalDigits (d : Fin r) :
      (payloadView (BStarLongPublication.readSel (old header).long) (old (sites d)).long).1 =
        (payloadView sel (captured (sites d)).long).1 := by
    exact congrFun (congrArg Prod.snd E) d
  have bankSel : bank=sel := left_bank_from_ack launch ack bank sel bank8 hold ack0
  intro d
  dsimp only
  change oldBankPacket (old (sites d)).long bank=oldBankPacket (captured (sites d)).long sel
  rw [bankSel]
  apply packed_eq_of_nibbles
  intro j
  have F := equalDigits d
  rw [equalSel] at F
  exact congrFun F j

#print axioms packed_before_load
end L4.BStarCopyLeftAcquireBank

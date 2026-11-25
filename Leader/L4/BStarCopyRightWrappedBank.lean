import Leader.L4.BStarCopyRightAcquireBank
import Leader.L4.BStarCopyRightWrappedReleaseClass

namespace L4.BStarCopyRightWrappedBank
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarCopyRightStrip BStarCopyRightWrappedGeometry
open BStarCopyRightWrappedReleaseClass (strip_same_owner)
open BStarCopyRightAcquireBank (truncate right_bank_from_ack packed_eq_of_nibbles)
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors BStarResetChartTouch
open BStarClearanceDataChart BStarLongFiberOwner BStarLongLayout
open BStarCommitOperands BStarCutOperandReadout BStarCaptureInterval
open BStarLongCommandData BStarGrantBirth BStarGrantWriterHistory BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- RS is owned by the same displacement (2) as the right ACQUIRE
K2 incidence. Its header is therefore the strip seam, not a data
receiver site or a centre selector alias. -/
theorem right_header {base : X} (hh : ∃ v,oldH6 B base v=true)
    (o : Owners (oldH6 B base)) (a : Fin n) (seam tail : Nat)
    (strip : WrappedStrip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val) :
    addr a seam=(endpoint (oldH6 B base) hh o 2).1 := by
  have own := (strip_same_owner strip seam strip.seam_le_tail).trans ownerHead
  have eq : rail seam seam=.rs := if_neg (by omega)
  rw [eq] at own
  exact congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o 2).2.2
    (addr a seam) strip.rs_header own)

private theorem same_right_word {base : X} (hh : ∃ v,oldH6 B base v=true)
    (a : Fin n) (seam tail : Nat) (strip : WrappedStrip B base a seam tail)
    (i : Nat) (ilo : seam≤i) (ihi : i≤tail) :
    word (oldH6 B base) (addr a seam)=word (oldH6 B base) (addr a i) := by
  let h := oldH6 B base
  have fst := strip_same_owner strip seam strip.seam_le_tail
  have snd := strip_same_owner strip i ihi
  have eq1 : rail seam seam=.rs := if_neg (by omega)
  have eq2 : rail seam i=.rs := if_neg (by omega)
  rw [eq1] at fst
  rw [eq2] at snd
  have same := fst.trans snd.symm
  change owner (total h) (word h (addr a seam)) 2=owner (total h) (word h (addr a i)) 2 at same
  have displaced := congrArg (fun u : Int => addressWord (total h) u 2) same
  rw [address_inverse,address_inverse] at displaced
  rw [Int.emod_eq_of_lt (word_range h _ hh).1 (word_range h _ hh).2,
      Int.emod_eq_of_lt (word_range h _ hh).1 (word_range h _ hh).2] at displaced
  exact displaced

/-- Canonical right RS addresses satisfy the exact body/readout map
used for continuous reader custody. Padding RD does not enter. -/
theorem rs_word_sites {base : X} (hh : ∃ v,oldH6 B base v=true)
    (a : Fin n) (seam tail : Nat) (strip : WrappedStrip B base a seam tail)
    (bound : seam+r-1≤tail) :
    WordSites (oldH6 B base) (addr a seam) (fun d : Fin r => addr a (seam+d.val)) := by
  intro d ne
  have pos : seam<seam+d.val := by
    by_cases P : d.val=0
    · exact (ne (by simp [P])).elim
    · omega
  have le : seam+d.val≤tail := by have := d.isLt; omega
  exact ⟨strip.rs_nonheader _ pos le,same_right_word hp hh a seam tail strip _ (by omega) le⟩

/-- The full right packed-bank operand is invariant at every earlier
LOAD cut under the original unbroken right ACQUIRE reader lifetime.
The bank used by LOAD is matched to ACK's low/right captured selector
rather than compared to whatever the source door's selector is now. -/
theorem packed_before_load {base x : X} {cut whole : List (Fin n)}
    (hh : ∃ v,oldH6 B base v=true)
    (owner : Owners (oldH6 B base)) (a : Fin n) (seam tail : Nat)
    (strip : WrappedStrip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=owner.val)
    (width : seam+r-1≤tail)
    (A : Acquisition hp x cut whole (endpoint (oldH6 B base) hh owner 2).1 2)
    (u v loadTail : List (Fin n)) (split : A.post=u++v)
    (exactLoad : cut++loadTail=A.lead++A.mark::u)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ w,oldH6 B (play x (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play x (cut++w)) e z
      (endpoint (oldH6 B base) hh owner 2).1)
    (launch ack : BitVec LW) (bank : Fin 3)
    (bank8 : bank.val=(captures.read launch).toNat%4)
    (hold : captures.read launch=captures.read ack)
    (ack2 : ((capturedSelector 2).read ack).toNat=
      (BStarLongPublication.readSel ((play x A.lead) (endpoint (oldH6 B base) hh owner 2).1).long).val) :
    ∀ digit : Fin r,
      let i := addr a (seam+digit.val)
      let old := play x (cut++loadTail)
      let captured := play x A.lead
      let header := (endpoint (oldH6 B base) hh owner 2).1
      oldBankPacket (old i).long bank =
        oldBankPacket (captured i).long (BStarLongPublication.readSel (captured header).long) := by
  let header := (endpoint (oldH6 B base) hh owner 2).1
  let sites := fun d : Fin r => addr a (seam+d.val)
  let short := truncate hp A u v loadTail split exactLoad
  have H := right_header hp hh owner a seam tail strip ownerHead
  have WS : WordSites (oldH6 B base) header sites := by
    change WordSites (oldH6 B base) (endpoint (oldH6 B base) hh owner 2).1 sites
    rw [←H]
    exact rs_word_sites hp hh a seam tail strip width
  have E := operand_at_acquire hp base x cut loadTail header 2 sites short sep layout auth WS
  let old := play x (cut++loadTail)
  let captured := play x A.lead
  let sel := BStarLongPublication.readSel (captured header).long
  have equalSel : BStarLongPublication.readSel (old header).long=sel :=
    congrArg (fun z => z.1.1) E
  have equalDigits (d : Fin r) :
      (payloadView (BStarLongPublication.readSel (old header).long) (old (sites d)).long).1 =
        (payloadView sel (captured (sites d)).long).1 := by
    exact congrFun (congrArg Prod.snd E) d
  have bankSel : bank=sel := right_bank_from_ack launch ack bank sel bank8 hold ack2
  intro d
  dsimp only
  change oldBankPacket (old (sites d)).long bank=oldBankPacket (captured (sites d)).long sel
  rw [bankSel]
  apply packed_eq_of_nibbles
  intro j
  have F := equalDigits d
  rw [equalSel] at F
  exact congrFun F j

end L4.BStarCopyRightWrappedBank

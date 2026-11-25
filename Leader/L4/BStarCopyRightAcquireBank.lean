import Leader.L4.BStarCopyRightOneCapture
import Leader.L4.BStarPostCutOperands

namespace L4.BStarCopyRightAcquireBank
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarCopyRightStrip BStarCopyRightAuthority
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors BStarResetChartTouch
open BStarClearanceDataChart BStarLongFiberOwner BStarLongLayout
open BStarCommitOperands BStarCutOperandReadout BStarCaptureInterval
open BStarLongCommandData BStarGrantBirth BStarGrantWriterHistory BStarLongDoor

/-- The complete 36-bit raw LOAD field is exactly its nine nibbles,
with the literal reversed nibble index. Equality of the selected
operand's digit vector therefore gives equality of the packed field. -/
theorem packed_eq_of_nibbles (b : Fin 3) (u v : BitVec LW)
    (H : ∀ j : Fin 9, (bankDigit b j).read u=(bankDigit b j).read v) :
    oldBankPacket u b=oldBankPacket v b := by
  unfold oldBankPacket
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin 9 := ⟨8-i/4,by omega⟩
  have K := congrArg (fun w : BitVec 4 => w.getLsbD (i%4)) (H j)
  have r : i%4<4 := Nat.mod_lt _ (by decide)
  simp only [Field.read,BitVec.getLsbD_extractLsb',r,hi,decide_true,Bool.true_and,bankDigit,bankPart] at K ⊢
  change u.getLsbD ((bankBase b + (9+4*(8-(8-i/4))))+i%4) =
    v.getLsbD ((bankBase b + (9+4*(8-(8-i/4))))+i%4) at K
  have e : (bankBase b + (9+4*(8-(8-i/4))))+i%4=(bankBase b+9)+i := by omega
  rwa [e] at K

/-- The two low capture bits are the original right incidence,
not the controller's current selector or the centre operand. -/
theorem right_capture_val (x : BitVec LW) :
    ((capturedSelector 2).read x).toNat=(captures.read x).toNat%4 := by
  have E : (capturedSelector 2).read x=(captures.read x).extractLsb' 0 2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have H : i<6 := by omega
    simp [Field.read,capturedSelector,captures,hi,H]
  rw [E,BitVec.extractLsb'_toNat]
  rfl

theorem right_bank_from_ack (launch ack : BitVec LW) (bank s : Fin 3)
    (fromLaunch : bank.val=(captures.read launch).toNat%4)
    (sameCapture : captures.read launch=captures.read ack)
    (fromAck : ((capturedSelector 2).read ack).toNat=s.val) :
    bank=s := by
  apply Fin.ext
  rw [fromLaunch,sameCapture,←right_capture_val,fromAck]

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
    (strip : Strip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val) :
    addr a seam=(endpoint (oldH6 B base) hh o 2).1 := by
  have own := (strip_same_owner strip seam strip.seam_le_tail).trans ownerHead
  have eq : rail seam seam=.rs := if_neg (by omega)
  rw [eq] at own
  exact congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o 2).2.2
    (addr a seam) strip.rs_header own)

private theorem same_right_word {base : X} (hh : ∃ v,oldH6 B base v=true)
    (a : Fin n) (seam tail : Nat) (strip : Strip B base a seam tail)
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
    (a : Fin n) (seam tail : Nat) (strip : Strip B base a seam tail)
    (bound : seam+r-1≤tail) :
    WordSites (oldH6 B base) (addr a seam) (fun d : Fin r => addr a (seam+d.val)) := by
  intro d ne
  have pos : seam<seam+d.val := by
    by_cases P : d.val=0
    · exact (ne (by simp [P])).elim
    · omega
  have le : seam+d.val≤tail := by have := d.isLt; omega
  exact ⟨strip.rs_nonheader _ pos le,same_right_word hp hh a seam tail strip _ (by omega) le⟩

/-- Downward retention interface for the actual fixed acquisition
witness: crop the original tape before a later mark without proving
a new grant birth or reacquiring bytes. -/
def truncate {x : X} {cut whole : List (Fin n)} {header : Fin n} {port : Fin 3}
    (A : Acquisition hp x cut whole header port)
    (u v tail : List (Fin n)) (split : A.post=u++v)
    (E : cut++tail=A.lead++A.mark::u) :
    Acquisition hp x cut (cut++tail) header port where
  lead := A.lead
  mark := A.mark
  post := u
  exactTape := E
  afterCut := A.afterCut
  won := A.won
  live := fun a b H => A.live a (b++v)
    (by rw [split,H,List.append_assoc])
  writerBefore := fun w a e b H => A.writerBefore w a e (b++v)
    (by rw [split,H,List.append_assoc,List.cons_append])

/-- The full right packed-bank operand is invariant at every earlier
LOAD cut under the original unbroken right ACQUIRE reader lifetime.
The bank used by LOAD is matched to ACK's low/right captured selector
rather than compared to whatever the source door's selector is now. -/
theorem packed_before_load {base x : X} {cut whole : List (Fin n)}
    (hh : ∃ v,oldH6 B base v=true)
    (owner : Owners (oldH6 B base)) (a : Fin n) (seam tail : Nat)
    (strip : Strip B base a seam tail)
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

end L4.BStarCopyRightAcquireBank

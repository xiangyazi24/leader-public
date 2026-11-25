import Leader.L4.ReportItemNineTrace
import Leader.L4.ReportFreshSealLineage

namespace L4.ReportItemNineStaging
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportByteRows ReportPrelaunchK1Geometry ReportPrelaunchClock ReportPrelaunchRank
open ReportOwnerCommandRail ReportOwnerAcquireReturn ReportLeaseOwner
open ReportIndexedSourcePrefix ReportGoodEightCut ReportGenerationAncestry
open ReportItemNineTrace ReportDigitArithmetic

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- EXACT single remaining staged-bank frame supplier, identical
    to StagedPrefixFrame. No all-future output equality is
    assumed. -/
def ItemNineStagedFrame (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) : Prop :=
  ∀ (r : Owner h) (x : Raw s n) (e : Fin n)
    (j : Fin (params d s).digits) (prior : Nat),
    let C := charter G r
    let p := params d s
    FirstCut d hh Q G x → StrongSerial d C x →
    (logical p.digits (writeOp p+j.val)<logical p.digits (readPC d C x).2) →
    (readPC d C x).2≤commitOp p →
    j.val<C.b →
    reportDigitPair p (selectBytes d (rawNext s x e (nextAt (centre C) j.val))) (1-prior)=
      reportDigitPair p (selectBytes d (x (nextAt (centre C) j.val))) (1-prior)

private theorem strong_bound (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : StrongSerial d C x) : (readPC d C x).2≤commitOp (params d s) := by
  rcases S.1 with A|⟨k,A⟩|⟨k,A⟩
  · exact A.1
  · exact A.1.2
  · exact A.1.2

/-- All later actual positive ACK/hold marks frame a credited
    index. WRITE→READ is increasing in logical order, not in
    numeric opcode. This includes SEAL flight/ACK and COMMIT
    pre-ingress flight. -/
theorem staged_on_ack_tape (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (M : 0<(params d s).digits) (Frame : ItemNineStagedFrame d hh Q G)
    (r : Owner h) (x : Raw s n) (w : List (Fin n)) (l : List Receipt)
    (A : FirstCut d hh Q G x) (S : StrongSerial d (charter G r) x)
    (j : Fin (params d s).digits) (prior : Nat) (J : j.val<(charter G r).b)
    (Past : logical (params d s).digits (writeOp (params d s)+j.val)<
      logical (params d s).digits (readPC d (charter G r) x).2)
    (T : AckTape d (charter G r) x w l) :
    reportDigitPair (params d s) (selectBytes d (rawRun x w
      (nextAt (centre (charter G r)) j.val))) (1-prior)=
    reportDigitPair (params d s) (selectBytes d (x
      (nextAt (centre (charter G r)) j.val))) (1-prior) := by
  induction T with
  | nil => rfl
  | @hold x e w l H T IH =>
    have A' := first_cut_closed d N hh G F M x e A
    have S' := strong_step d (charter G r) N hh G F x A.1.1.1 S M e
    have P' : logical (params d s).digits (writeOp (params d s)+j.val)<
        logical (params d s).digits (readPC d (charter G r) (rawNext s x e)).2 := by
      rw [H.1]
      exact Past
    exact (IH A' S' P').trans (Frame r x e j prior A S Past (strong_bound d _ x S) J)
  | @credit x e w l H T IH =>
    have A' := first_cut_closed d N hh G F M x e A
    have S' := strong_step d (charter G r) N hh G F x A.1.1.1 S M e
    have P' : logical (params d s).digits (writeOp (params d s)+j.val)<
        logical (params d s).digits (readPC d (charter G r) (rawNext s x e)).2 := by
      rw [preview_logical H.2.2.2.2.2.2.2.1]
      omega
    exact (IH A' S' P').trans (Frame r x e j prior A S Past (strong_bound d _ x S) J)

/-- Physical WRITE certificate, projected from WriteFlightResult.
    The issued token is the real old F of this successful command;
    its staged pair is installed at the matching ACK, and the
    payload equals the literal source send field at issue. -/
def WriteCredits (d : Sheet) (C : Chart h) (b : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (prior : Nat) : Prop :=
  let p := params d s
  ∀ r∈l,∀ j : Fin p.digits,r.1=writeOp p+j.val →
    ∃ pre flight tail : List (Fin n),∃ f : Tok,
      w=pre++(door C::(flight++(door C::tail))) ∧
      let issue := rawRun b pre
      let old := rawRun (rawNext s issue (door C)) flight
      let after := rawNext s old (door C)
      readPC d C issue=(1,writeOp p+j.val) ∧
      readPC d C old=(2,writeOp p+j.val) ∧
      r.2=tok d C old 0 ∧ CreditAt d C old (door C) ∧
      ancestryWriteTarget p f=1-prior ∧
      f.payload%2^(2*ReportByteRows.d p)=ancestrySendDigits p (rootBytes d C issue) ∧
      reportDigitPair p (selectBytes d (after (nextAt (centre C) j.val))) (1-prior)=
        BitVec.ofNat (2*ReportByteRows.d p) (f.payload%2^(2*ReportByteRows.d p))

private theorem logical_write_formula (p : Params) (j : Nat) (J : j<p.digits) :
    logical p.digits (writeOp p+j)=2*p.digits+4+2*j := by
  unfold logical writeOp
  rw [if_neg (by omega),if_neg (by omega),if_pos (by omega),
    show 3*p.digits+3+j-(3*p.digits+3)=j by omega]

/-- Exactly one matching WRITE index occurs in the ordered prefix
    ending at the genuine SEAL issue. No index inferred from the
    current physical digit bytes. -/
theorem every_write_receipt (d : Sheet) (C : Chart h) (b : Raw s n)
    (w : List (Fin n)) (l : List Receipt)
    (B : (readPC d C b).2=cmpOp (params d s))
    (E : (readPC d C (rawRun b w)).2=sealOp (params d s))
    (T : AckTape d C b w l) (j : Fin (params d s).digits) :
    ∃ r∈l,r.1=writeOp (params d s)+j.val := by
  let p := params d s
  have L : l.length=3*p.digits := at_seal_count d C b w l B E T
  have O := tape_order d C b w l T
  unfold logicalPC at O
  rw [B,logical_cmp] at O
  have J : j.val<p.digits := j.isLt
  have K : p.digits+1+2*j.val<l.length := by omega
  obtain ⟨r,Mem,Log⟩ := ordered_complete p (cmpOp p) l O _ K
  have Eq : logical p.digits (writeOp p+j.val)=cmpOp p+(p.digits+1+2*j.val) := by
    rw [logical_write_formula p j.val J]
    unfold cmpOp
    omega
  have Range := ordered_range p (cmpOp p) l O r Mem
  have rBound : r.1<4*p.digits+5 := by
    apply Nat.lt_of_not_ge
    intro H
    have R0 : 4*p.digits+5≤r.1 := by omega
    have V : logical p.digits r.1=r.1 := by
      unfold logical
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    rw [V,L] at Range
    unfold cmpOp at Range
    omega
  exact ⟨r,Mem,logical_injective p.digits _ _ rBound
    (by change writeOp p+j.val<4*p.digits+5; unfold writeOp; omega) (Log.trans Eq.symm)⟩

/-- All staged pairs at the actual SEAL issue, from the original
    successful WRITE entries and the literal source recurrence.
    This theorem uses no hypothesis about the finished staged file. -/
theorem staged_at_seal (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (M : 0<(params d s).digits) (Frame : ItemNineStagedFrame d hh Q G)
    (r : Owner h) (b : Raw s n) (w : List (Fin n)) (l : List Receipt)
    (I : ItemNineInputs) (B : 2≤(params d s).beta)
    (XL : I.left<(params d s).beta^(params d s).digits)
    (XR : I.right<(params d s).beta^(params d s).digits)
    (R : (params d s).radius<(params d s).beta^(params d s).digits)
    (A : FirstCut d hh Q G b) (S : StrongSerial d (charter G r) b)
    (PC : (readPC d (charter G r) b).2=cmpOp (params d s))
    (Seed : ItemNineAt (params d s) I (readPC d (charter G r) b).2
      (item9Read (params d s) (rootBytes d (charter G r) b)))
    (End : (readPC d (charter G r) (rawRun b w)).2=sealOp (params d s))
    (T : AckTape d (charter G r) b w l) (D : ReadReceipts (params d s) I l)
    (Writes : WriteCredits d (charter G r) b w l I.prior)
    (Room : (params d s).digits≤(charter G r).b) :
    let C := charter G r
    let p := params d s
    ∀ j,j<p.digits →
      reportDigitPair p (selectBytes d (rawRun b w (nextAt (centre C) j))) (1-I.prior)=
        BitVec.ofNat (2*ReportByteRows.d p) (item9Send p I j) := by
  dsimp only
  let C := charter G r
  let p := params d s
  intro j J
  let idx : Fin p.digits := ⟨j,J⟩
  obtain ⟨rc,Mem,Op⟩ := every_write_receipt d C b w l PC End T idx
  obtain ⟨pre,flight,tail,f,E,Issue,Old,_,Credit,_,Send,Installed⟩ := Writes rc Mem idx Op
  let a := rawRun b pre
  let old := rawRun (rawNext s a (door C)) flight
  let after := rawNext s old (door C)
  -- split at the real issue; then split just before the ACK
  rw [E] at T
  obtain ⟨la,lr,LE,TA,TR⟩ := split_ack d C b pre _ l T
  have RA : ReadReceipts p I la := by
    intro q Q
    exact D q (by rw [LE]; exact List.mem_append.mpr (.inl Q))
  have Math := math_run d C I B XL XR R b pre la TA Seed RA
  rw [Issue] at Math
  have SendEq := item9_at_write p I (rootBytes d C a) j J Math
  have Split : (door C::(flight++(door C::tail)))=
      (door C::flight)++(door C::tail) := by rfl
  rw [Split] at TR
  obtain ⟨lc,ld,_,_,TD⟩ := split_ack d C a (door C::flight) _ lr TR
  change AckTape d C old (door C::tail) ld at TD
  obtain ⟨lf,_,TF⟩ := ack_credit_head d C old (door C) tail ld TD Credit
  have Wold : rawRun b (pre++(door C::flight))=old := by
    rw [ShortOwnerEpochJS.raw_append]
    rfl
  have Aold := first_cut_run d N hh G F M b A (pre++(door C::flight))
  have Sold := (strong_run d C N hh G F M b A.1.1.1 S (pre++(door C::flight))).2.1
  rw [Wold] at Aold Sold
  have Aa := first_cut_closed d N hh G F M old (door C) Aold
  have Sa := strong_step d C N hh G F old Aold.1.1.1 Sold M (door C)
  have P := preview_logical Credit.2.2.2.2.2.2.2.1
  change logical p.digits (readPC d C after).2=logical p.digits (readPC d C old).2+1 at P
  rw [Old] at P
  have Past : logical p.digits (writeOp p+j)<logical p.digits (readPC d C after).2 := by
    change logical p.digits (readPC d C after).2=logical p.digits (writeOp p+j)+1 at P
    omega
  have Frame' := staged_on_ack_tape d N hh G F M Frame r after tail lf Aa Sa idx I.prior
    (by omega) Past TF
  have WE : rawRun b w=rawRun after tail := by
    rw [E,ShortOwnerEpochJS.raw_append]
    change rawRun (rawNext s a (door C)) (flight++(door C::tail))=_
    rw [ShortOwnerEpochJS.raw_append]
    rfl
  rw [WE]
  exact Frame'.trans (Installed.trans (by rw [Send,SendEq]))

/-- Transport the ENTIRE staged file from the actual final-WRITE /
    ISSUE(SEAL) cut to the old accepted COMMIT cut. Uses the same
    one-mark supplier, no additional frame assumption. -/
theorem staged_after_seal (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (M : 0<(params d s).digits) (Frame : ItemNineStagedFrame d hh Q G)
    (r : Owner h) (x : Raw s n) (w : List (Fin n)) (l : List Receipt)
    (I : ItemNineInputs) (A : FirstCut d hh Q G x)
    (S : StrongSerial d (charter G r) x)
    (PC : (readPC d (charter G r) x).2=sealOp (params d s))
    (T : AckTape d (charter G r) x w l)
    (Room : (params d s).digits≤(charter G r).b)
    (Staged : ∀ j,j<(params d s).digits →
      reportDigitPair (params d s) (selectBytes d (x
        (nextAt (centre (charter G r)) j))) (1-I.prior)=
          BitVec.ofNat (2*ReportByteRows.d (params d s)) (item9Send (params d s) I j)) :
    ∀ j,j<(params d s).digits →
      reportDigitPair (params d s) (selectBytes d (rawRun x w
        (nextAt (centre (charter G r)) j))) (1-I.prior)=
          BitVec.ofNat (2*ReportByteRows.d (params d s)) (item9Send (params d s) I j) := by
  intro j J
  let p := params d s
  have Past : logical p.digits (writeOp p+j)<logical p.digits (readPC d (charter G r) x).2 := by
    change logical p.digits (writeOp p+j)<logical p.digits (readPC d (charter G r) x).2
    rw [show (readPC d (charter G r) x).2=sealOp p from PC,
      logical_seal,logical_write_formula p j J]
    have JP : j<p.digits := J
    unfold sealOp
    omega
  exact (staged_on_ack_tape d N hh G F M Frame r x w l A S ⟨j,J⟩ I.prior
    (by omega) Past T).trans (Staged j J)

#print axioms staged_on_ack_tape
#print axioms every_write_receipt
#print axioms staged_at_seal
#print axioms staged_after_seal
end L4.ReportItemNineStaging

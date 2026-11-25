import Leader.L4.ReportSnapshotLease
import Leader.L4.ReportGoodEightBank
import Leader.L4.ReportJoinedBankFrame
import Leader.L4.ReportDigitWord

namespace L4.ReportProtectedWords
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportRawProjection ReportGoodEightBank ReportLeaseOwner ReportWriterPayload
open ReportGenerationAncestry ReportLeaseStep ReportJoinedBankFrame ReportDigitWord
open ReportPrelaunchClock ReportStaticSpacing

variable {s n : Nat} {h : Fin n→Bool}

/-- No left WRITE can modify the centre's selected bank, including at its
header digit: bank safety is attached to the unique lane-1 owner. -/
theorem left_selected_digit_frame (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (x : Raw s n) (e hdr : Fin n)
    (Mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (Hdr : h hdr=true) {len j : Nat} (Gap : Gap h hdr len) (J : j<len)
    (E : e=nextAt hdr j) (Safe : BankSafe d G x) :
    reportDigitPair (params d s) (selectBytes d (rawNext s x e e)) (rawSelector d x hdr)=
    reportDigitPair (params d s) (selectBytes d (x e)) (rawSelector d x hdr) := by
  let p := params d s
  let u := selectBytes d (x e)
  let v := selectBytes d (x (rightNeighbor e))
  let sel := rawSelector d x hdr
  let t := publicationToken p (h e) u 1
  have S : sel<2 := ancestry_selector_lt _ _
  have L : reportDigitPair p (selectBytes d (rawNext s x e e)) sel=
      reportDigitPair p ((row p (h e,h (rightNeighbor e)) (u,v)).1.apply u) sel := by
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    have K := raw_low_pair d x e N Mask (reportBankDigitAddress p sel i)
      (reportBankDigitAddress_lt p sel i I)
    simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    exact K.1
  refine L.trans ?_
  by_cases W : WriteDigitEnabled p (h e) u
  · obtain ⟨r,k,K,F,_⟩ := unique_cell hh G e 1
    have Pos : out (charter G r) k=e := congrArg Prod.fst F
    have Lane : (charter G r).route.port k=1 := congrArg Prod.snd F
    have Same := ReportReaderWordOwner.lane1_owner_centre hh G r k Lane Hdr Gap J (Pos.trans E)
    have Tok : tok d (charter G r) x k=t := by
      rw [ReportOwnerProvenanceTransport.predecessor_projection,Pos,Lane]
      rfl
    have Ready : rankReady p (h e) u 1=true := W.1
    have Live : t.fault=false := W.2.1
    have Low : writeOp p≤t.opcode := W.2.2.1
    have High : t.opcode<sealOp p := W.2.2.2.1
    have Offset : reportOldOffset p (h e) u=t.opcode-writeOp p := W.2.2.2.2
    have Cmd : WriteCommand p (tok d (charter G r) x k) := by
      rw [Tok]
      exact ⟨((rankReady_iff ..).mp Ready).1,Live,Low,High⟩
    obtain ⟨Old,Target⟩ := Safe r k K Cmd
    rw [Tok,Same] at Old Target
    let off : Fin p.digits := ⟨t.opcode-writeOp p,by
      unfold sealOp at High
      unfold writeOp at Low ⊢
      omega⟩
    have Op : t.opcode=writeOp p+off.val := by dsimp only [off]; omega
    by_cases Hu : h e=false
    · exact indexed_left_write_other p (h e) (h (rightNeighbor e)) u v off Ready Live Op
        Offset (.inl Hu) sel S (Ne.symm Target)
    · have Head : h e=true := by cases Z : h e <;> simp_all
      have EZ : j=0 := by
        cases j with
        | zero => rfl
        | succ k =>
          have FalseHeader : h e=false := by rw [E]; exact Gap.interior _ (by omega) J
          exact False.elim (Bool.noConfusion (Head.symm.trans FalseHeader))
      have EH : e=hdr := by rw [EZ] at E; exact E
      have EqSel : publicationSelector p u=t.payload/2^(2*ReportByteRows.d p+1) := by
        change rawSelector d x e=ancestryWriteOld p t
        rw [EH]
        exact Old.symm
      by_cases Grant : reportOldGrant p u 1=true
      · exact indexed_left_write_other p (h e) (h (rightNeighbor e)) u v off Ready Live Op
          Offset (.inr ⟨Grant,EqSel⟩) sel S (Ne.symm Target)
      · rw [Head]
        change reportDigitPair p ((row p (true,h (rightNeighbor e)) (u,v)).1.apply u) sel=reportDigitPair p u sel
        apply BitVec.eq_of_getLsbD_eq
        intro i I
        simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
        apply Patch.hold
        exact report_header_denied_left_digit_mask p (h (rightNeighbor e)) u v
          (Bool.eq_false_iff.mpr Grant) sel i I
  · exact indexed_left_no_write_bank_frame p (h e) (h (rightNeighbor e)) u v sel W

/-- A physical mark without an accepted incoming COMMIT at the selected
header preserves both directional values; arbitrary other words may write. -/
theorem value_frame_without_ingress (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (x : Raw s n) (e hdr : Fin n)
    (Mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (Hdr : h hdr=true) {len : Nat} (Gap : Gap h hdr len)
    (Width : (params d s).digits≤len) (Safe : BankSafe d G x)
    (No : ¬(hdr=rightNeighbor e ∧ oldCommitAt d x e)) (dir : Bool) :
    reportValue (params d s) (fun i=>selectBytes d (rawNext s x e i)) hdr dir =
      reportValue (params d s) (fun i=>selectBytes d (x i)) hdr dir := by
  let p := params d s
  let sel := rawSelector d x hdr
  have Sel := raw_selector_frame d x e hdr N No
  change publicationSelector p (selectBytes d (rawNext s x e hdr))=
    publicationSelector p (selectBytes d (x hdr)) at Sel
  unfold reportValue
  dsimp only
  rw [Sel]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j J
  let i := nextAt hdr j
  have I : j<len := Nat.lt_of_lt_of_le (List.mem_range.mp J) Width
  have Digit : reportDigitPair p (selectBytes d (rawNext s x e i)) sel=
      reportDigitPair p (selectBytes d (x i)) sel := by
    by_cases L : e=i
    · rw [←L]
      exact left_selected_digit_frame d N hh G x e hdr Mask Hdr Gap I L Safe
    · by_cases R : i=rightNeighbor e
      · rw [R]
        exact raw_right_bank_frame d x e N Mask sel
      · rw [raw_spectator x e i (Ne.symm L) R]
  have S (k : Fin 3) (K : k=0 ∨ k=2) :
      indexedSample p (selectBytes d (rawNext s x e i)) sel k =
        indexedSample p (selectBytes d (x i)) sel k := by
    rcases K with rfl|rfl
    · rw [ReportIndexedReadLedger.sample_hi,ReportIndexedReadLedger.sample_hi,Digit]
    · rw [ReportIndexedReadLedger.sample_lo,ReportIndexedReadLedger.sample_lo,Digit]
  apply congrArg (fun z=>z*p.beta^j)
  cases dir
  · exact S 2 (.inr rfl)
  · exact S 0 (.inl rfl)

end L4.ReportProtectedWords

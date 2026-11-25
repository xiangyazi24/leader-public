import Leader.L4.ReportJoinedBankFrame
import Leader.L4.ReportOwnerCommandRail
import Leader.L4.ReportReaderWordOwner
import Leader.L4.ReportDigitHits
import Leader.L4.ReportGoodEightCut

namespace L4.ReportJoinedWriteValue
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportByteRows ReportLeaseStep ReportRawProjection
open ReportPrelaunchK1Geometry ReportOwnerProvenanceTransport
open ReportGenerationAncestry ReportLeaseOwner ReportReaderWordOwner
open ReportOwnerCommandRail ReportPrelaunchClock ReportPrelaunchRank
open ReportOwnerAcquireReturn ReportGoodEightCut
open ReportDigitHits BStarH6Ordinal

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem raw_left_digit_projection (d : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (sel : Nat) :
    let p := params d s
    let u := selectBytes d (x e)
    let v := selectBytes d (x (rightNeighbor e))
    reportDigitPair p (selectBytes d (rawNext s x e e)) sel=
      reportDigitPair p ((row p (h e,h (rightNeighbor e)) (u,v)).1.apply u) sel := by
  dsimp only
  let p := params d s
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have L := (raw_low_pair d x e N mask (reportBankDigitAddress p sel i)
    (reportBankDigitAddress_lt p sel i I)).1
  simpa only [reportDigitPair,reportBankDigitAddress,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    using L

/-- Both endpoint orientations. The last equality is the outgoing
    endpoint's selector, not an unconditional right-selector frame. -/
theorem raw_write_hit (d : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (j : Fin (params d s).digits)
    (T : rankReady (params d s) (h e) (selectBytes d (x e)) 1=true)
    (Live : (publicationToken (params d s) (h e) (selectBytes d (x e)) 1).fault=false)
    (Op : (publicationToken (params d s) (h e) (selectBytes d (x e)) 1).opcode=
      writeOp (params d s)+j.val)
    (Off : reportOldOffset (params d s) (h e) (selectBytes d (x e))=j.val)
    (Permit : h e=false ∨ (reportOldGrant (params d s) (selectBytes d (x e)) 1=true ∧
      publicationSelector (params d s) (selectBytes d (x e))=
        (publicationToken (params d s) (h e) (selectBytes d (x e)) 1).payload/
          2^(2*ReportByteRows.d (params d s)+1))) :
    let p := params d s
    let t := publicationToken p (h e) (selectBytes d (x e)) 1
    let y := rawNext s x e
    reportDigitPair p (selectBytes d (y e)) (ancestryWriteTarget p t)=
      BitVec.ofNat (2*ReportByteRows.d p) (t.payload%2^(2*ReportByteRows.d p)) ∧
    (∀ sel,sel<2→sel≠ancestryWriteTarget p t→
      reportDigitPair p (selectBytes d (y e)) sel=reportDigitPair p (selectBytes d (x e)) sel) ∧
    (∀ sel,reportDigitPair p (selectBytes d (y (rightNeighbor e))) sel=
      reportDigitPair p (selectBytes d (x (rightNeighbor e))) sel) ∧
    rawSelector d y e=rawSelector d x e := by
  dsimp only
  let p := params d s
  let u := selectBytes d (x e)
  let v := selectBytes d (x (rightNeighbor e))
  refine ⟨?_,?_,?_,?_⟩
  · exact (raw_left_digit_projection d x e N mask _).trans
      (indexed_left_write_value p (h e) (h (rightNeighbor e)) u v j T Live Op Off Permit)
  · intro sel S Other
    exact (raw_left_digit_projection d x e N mask sel).trans
      (indexed_left_write_other p (h e) (h (rightNeighbor e)) u v j T Live Op Off Permit sel S Other)
  · intro sel
    exact ReportJoinedBankFrame.raw_right_bank_frame d x e N mask sel
  · exact raw_selector_frame d x e e N (fun H=>edge_sep N e H.1)

/-- All three mark dispositions for a staged physical site.
    Incoming COMMIT metadata does not write a digit bank. -/
theorem raw_digit_frame (d : Sheet) (x : Raw s n) (a e : Fin n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (sel : Nat) (H : ¬WriteDigitEnabled (params d s) (h a) (selectBytes d (x a))) :
    reportDigitPair (params d s) (selectBytes d (rawNext s x e a)) sel=
      reportDigitPair (params d s) (selectBytes d (x a)) sel := by
  by_cases E : e=a
  · subst e
    exact (raw_left_digit_projection d x a N mask sel).trans
      (indexed_left_no_write_bank_frame (params d s) (h a) (h (rightNeighbor a))
        (selectBytes d (x a)) (selectBytes d (x (rightNeighbor a))) sel H)
  · by_cases R : a=rightNeighbor e
    · rw [R]
      exact ReportJoinedBankFrame.raw_right_bank_frame d x e N mask sel
    · rw [raw_spectator x e a (Ne.symm E) R]

theorem raw_chart_not_forward_frame (d : Sheet) (C : Chart h)
    (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k : Nat) (Lane : C.route.port k=1) (Tag : (tok d C x k).tag≠2)
    (sel : Nat) :
    reportDigitPair (params d s) (selectBytes d (rawNext s x e (out C k))) sel=
      reportDigitPair (params d s) (selectBytes d (x (out C k))) sel := by
  apply raw_digit_frame d x (out C k) e N mask sel
  apply writehit_not_enabled_of_tag
  rw [predecessor_projection,Lane] at Tag
  exact Tag

/-- The terminal is on lane 2, so every middle-lane digit occurs
    strictly before the terminal. This follows from C.dst, not an
    extra length hypothesis on the canonical chart. -/
theorem middle_before_terminal (C : Chart h) : C.a+C.b<C.L := by
  have P := C.positive
  have D := end_dest C (C.L-1) (by omega)
  have T : C.route.port (C.L-1)=2 := by
    unfold reset0Destination at D
    split at D
    · split at D
      · assumption
      · contradiction
    · contradiction
  change lane C.a C.b (C.L-1)=2 at T
  unfold lane at T
  split at T
  · contradiction
  · split at T
    · contradiction
    · omega

theorem middle_position (G : GapInput h) (r : Owner h) (j : Nat)
    (J : j<(charter G r).b) :
    let C := charter G r
    let k := C.a+j
    k<C.L ∧ C.route.port k=1 ∧ out C k=nextAt (centre C) j := by
  dsimp only
  let C := charter G r
  have B := middle_before_terminal C
  change j<C.b at J
  change C.a+j<C.L ∧ C.route.port (C.a+j)=1 ∧ out C (C.a+j)=nextAt (centre C) j
  refine ⟨by omega,?_,?_⟩
  · exact (lane1 C.a C.b (C.a+j)).mpr ⟨by omega,by omega⟩
  · change nextAt C.root (C.a+j)=nextAt (nextAt C.root C.a) j
    exact nextAt_add C.root C.a j

theorem cached_offsets (d : Sheet) (hh : ∃ i,h i=true)
    (x : Raw s n) (X : Cached d hh Q x) (i : Fin n) :
    reportOldOffset (params d s) (h i) (selectBytes d (x i))=
      min (max 3 (params d s).digits) (ordinal h hh i) := by
  change effectiveOffset (params d s) (h i) (selectBytes d (x i))=_
  apply offset_from_cache (params d s) h hh (fun a=>selectBytes d (x a)) _ i
  cases d
  · exact report1_cache_is_literal hh x X
  · exact report2_cache_is_literal hh x X

/-- Literal unique old hit, for every cached prefix; includes wrap
    and arbitrary changes in unrelated work fields. -/
theorem middle_offset (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (r : Owner h) (j : Fin (params d s).digits)
    (J : j.val<(charter G r).b) (x : Raw s n) (X : Cached d hh Q x) :
    let C := charter G r
    let k := C.a+j.val
    reportOldOffset (params d s) (h (out C k)) (selectBytes d (x (out C k)))=j.val := by
  dsimp only
  let C := charter G r
  let k := C.a+j.val
  have Lane := (middle_position G r j.val J).2.1
  have O := (canonical_middle_offset hh G r k Lane).2.2
  change ordinal h hh (out C k)=k-C.a at O
  rw [cached_offsets d hh x X (out C k),O]
  have E : k-C.a=j.val := by dsimp [k]; omega
  rw [E]
  exact Nat.min_eq_right (Nat.le_trans (Nat.le_of_lt j.isLt) (Nat.le_max_right _ _))

theorem middle_hit_unique (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (r : Owner h) (j : Fin (params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat)
    (Lane : (charter G r).route.port k=1)
    (Off : reportOldOffset (params d s) (h (out (charter G r) k))
      (selectBytes d (x (out (charter G r) k)))=j.val) :
    k=(charter G r).a+j.val := by
  let C := charter G r
  have M := canonical_middle_offset hh G r k Lane
  change k=C.a+j.val
  have B := (lane1 C.a C.b k).mp Lane
  rw [cached_offsets d hh x X _,M.2.2] at Off
  change min (max 3 (params d s).digits) (k-C.a)=j.val at Off
  have J := j.isLt
  by_cases H : k-C.a≤max 3 (params d s).digits
  · rw [Nat.min_eq_right H] at Off
    omega
  · have E : max 3 (params d s).digits≤k-C.a := by omega
    rw [Nat.min_eq_left E] at Off
    have U := Nat.le_max_right 3 (params d s).digits
    omega

/-- The previously credited index cannot be an enabled matching
    WRITE in ANY later logical instruction, including a later WRITE.
    No weaker BankSafe implication is used: that protects the other
    bank, not the staged bank. This works for either physical bank. -/
theorem staged_prefix_step (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (r : Owner h) (x : Raw s n) (e : Fin n)
    (j : Fin (params d s).digits) (sel : Nat)
    (X : Cached d hh Q x) (A : StrongSerial d (charter G r) x)
    (Past : logical (params d s).digits (writeOp (params d s)+j.val)<
      logical (params d s).digits (readPC d (charter G r) x).2)
    (J : j.val<(charter G r).b) :
    reportDigitPair (params d s)
      (selectBytes d (rawNext s x e (nextAt (centre (charter G r)) j.val))) sel=
    reportDigitPair (params d s)
      (selectBytes d (x (nextAt (centre (charter G r)) j.val))) sel := by
  let C := charter G r
  let p := params d s
  let k := C.a+j.val
  obtain ⟨K,Lane,Site⟩ := middle_position G r j.val J
  have Off := middle_offset d hh G r j J x X
  have No : ¬WriteDigitEnabled p (h (out C k)) (selectBytes d (x (out C k))) := by
    intro H
    let t := publicationToken p (h (out C k)) (selectBytes d (x (out C k))) 1
    change rankReady p (h (out C k)) (selectBytes d (x (out C k))) 1=true ∧
      t.fault=false ∧ writeOp p≤t.opcode ∧ t.opcode<sealOp p ∧
      reportOldOffset p (h (out C k)) (selectBytes d (x (out C k)))=
        t.opcode-writeOp p at H
    have Eq : tok d C x k=t := by rw [predecessor_projection,Lane]; rfl
    have Tag := ((rankReady_iff p _ _ 1).mp H.1).1
    have Al := A.2 k K
    rw [Eq] at Al
    have Op := Al (.inl Tag) H.2.1
    have W : t.opcode=writeOp p+j.val := by
      have E := H.2.2.2.2
      rw [Off] at E
      have := H.2.2.1
      omega
    have P : (readPC d C x).2=writeOp p+j.val := Op.symm.trans W
    change logical p.digits (writeOp p+j.val)<logical p.digits (readPC d C x).2 at Past
    rw [P] at Past
    exact (Nat.lt_irrefl _ Past)
  rw [←Site]
  exact raw_digit_frame d x (out C k) e N
    ((cached_fibre d N hh Q F).mask x X) sel No

theorem staged_prefix_run (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (r : Owner h) (x : Raw s n) (w : List (Fin n))
    (j : Fin (params d s).digits) (sel : Nat)
    (X : Cached d hh Q x) (A : StrongSerial d (charter G r) x)
    (PC : PostAcqPC (params d s) (readPC d (charter G r) x))
    (Past : logical (params d s).digits (writeOp (params d s)+j.val)<
      logical (params d s).digits (readPC d (charter G r) x).2)
    (J : j.val<(charter G r).b)
    (NR : NoRestartTape d (charter G r) x w) :
    reportDigitPair (params d s)
      (selectBytes d (rawRun x w (nextAt (centre (charter G r)) j.val))) sel=
    reportDigitPair (params d s)
      (selectBytes d (x (nextAt (centre (charter G r)) j.val))) sel := by
  induction w generalizing x with
  | nil => rfl
  | cons e w IH =>
    let C := charter G r
    have NZ : (readPC d C x).2≠0 := by
      have L := PC.2.1
      change cmpOp (params d s) ≤ (readPC d C x).2 at L
      unfold cmpOp at L
      omega
    obtain ⟨Y,PC',_⟩ := raw_postacq_step d C hh F N x X e PC digit NR.1
    have A' := strong_step d C N hh G F x X A digit e
    have Past' : logical (params d s).digits (writeOp (params d s)+j.val)<
        logical (params d s).digits (readPC d C (rawNext s x e)).2 := by
      rcases positive_pc_step d C N hh G F digit x X A e NZ with R|E|E
      · exact (NR.1 R.1).elim
      · rw [E]; exact Past
      · rw [preview_logical E]
        change logical (params d s).digits (writeOp (params d s)+j.val) <
          logical (params d s).digits (readPC d C x).2 at Past
        omega
    exact (IH (rawNext s x e) Y A' PC' Past' NR.2).trans
      (staged_prefix_step d N hh G F r x e j sel X A Past J)

end L4.ReportJoinedWriteValue

import Leader.L4.ReportItemNineStaging
import Leader.L4.ReportRawCommitDigits
import Leader.L4.ReportCommitValue
import Leader.L4.ReportIngressOwnership

namespace L4.ReportItemNinePublication
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportByteRows ReportRawProjection ReportPrelaunchK1Geometry
open ReportLeaseOwner ReportIngressOwnership ReportGenerationAncestry
open ReportOwnerProvenanceTransport ReportRawCommitSnapshot ReportRawCommitDigits
open ReportDigitArithmetic ReportDigitWord ReportStaticSpacing
open ReportItemNineTrace ReportItemNineStaging
open ReportIndexedSourcePrefix ReportOwnerCommandRail ReportGoodEightCut

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem actual_params_fit (d : Sheet) (S : 0<s) :
    2≤(params d s).beta ∧ (params d s).radius<(params d s).beta^(params d s).digits := by
  cases d with
  | first =>
    change 2≤s+1 ∧ s<(s+1)^1
    simp only [Nat.pow_one]
    omega
  | second =>
    change 2≤2 ∧ radiusTwo s<2^ell (radiusTwo s+1)
    exact ⟨by decide,Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (power_of_ell _)⟩

/-- Read either half of an exact staged digit pair. The physical
    readout clips at beta−1, but a correct emitted radix digit
    already lies below beta, so no extra clipping occurs. -/
theorem selected_digit_of_pack (p : Params) (v : BitVec p.w)
    (ix a b : Nat) (B : 2≤p.beta) (A : a<p.beta) (C : b<p.beta)
    (E : reportDigitPair p v ix=BitVec.ofNat (2*ReportByteRows.d p)
      (2^ReportByteRows.d p*a+b)) :
    selectedDigit p ix true v=a ∧ selectedDigit p ix false v=b := by
  let w := ReportByteRows.d p
  let k := sealBase p+5+(1-ix)*bankW p
  have H : p.beta≤2^w := power_of_ell p.beta
  have Aa := Nat.lt_of_lt_of_le A H
  have Bb := Nat.lt_of_lt_of_le C H
  have Fit := item9_pack_bound p a b Aa Bb
  have Half := item9_pack_halves p a b Bb
  have Sub (z : Nat) (Z : z+w≤2*w) :
      v.extractLsb' (k+z) w=
        (reportDigitPair p v ix).extractLsb' z w := by
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    change _=((v.extractLsb' k (2*w)).extractLsb' z w).getLsbD i
    have J : z+i<2*w := by omega
    simp only [BitVec.getLsbD_extractLsb',I,J,decide_true,Bool.true_and,Nat.add_assoc]
  have Hi : (v.extractLsb' (k+w) w).toNat=a := by
    rw [Sub w (by omega),E]
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt Fit]
    rw [Half.1,Nat.mod_eq_of_lt Aa]
  have Lo : (v.extractLsb' k w).toNat=b := by
    have U := Sub 0 (by omega)
    rw [Nat.add_zero,E] at U
    rw [U]
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt Fit,Nat.pow_zero,Nat.div_one]
    exact Half.2
  constructor
  · change min (p.beta-1) (v.extractLsb' (k+w) w).toNat=a
    rw [Hi,Nat.min_eq_right (by omega)]
  · change min (p.beta-1) (v.extractLsb' k w).toNat=b
    rw [Lo,Nat.min_eq_right (by omega)]

/-- Convert the accepted old-byte guard into the checked raw
    publication/retention interface for either actual sheet. -/
theorem raw_commit_metadata (d : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (H : h (rightNeighbor e)=true) (delta : Nat)
    (G : CommitGuard (params d s) (h e) (selectBytes d (x e))
      (selectBytes d (x (rightNeighbor e))) delta) :
    let p := params d s
    let v := selectBytes d (x (rightNeighbor e))
    let y := selectBytes d (rawNext s x e (rightNeighbor e))
    let ix := (delta/4)%2
    publicationSelector p y=ix ∧ publicationA p y ix=Z p v ∧
      publicationPair p y ix=delta%4 ∧
      Z p y=(if paints p true 1 v then publicationPair p v (publicationSelector p v)==0 else Z p v) ∧
      ∀ sel,reportDigitPair p y sel=reportDigitPair p v sel := by
  cases d with
  | first =>
    have Hd : (oldHeaders (rows s) (x (rightNeighbor e))).h4=true :=
      (mask _).trans H
    have Guard : CommitGuard (firstParams s) (oldHeaders (rows s) (x e)).h4
        (x e).report1 (x (rightNeighbor e)).report1 delta := by
      rw [show (oldHeaders (rows s) (x e)).h4=h e from mask e]
      exact G
    have A := report1_commit_same_mark x e (edge_sep N e) Hd delta Guard
    exact ⟨A.1,A.2.1,A.2.2.1,A.2.2.2,
      fun sel=>report1_commit_keeps_digits x e (edge_sep N e) Hd delta sel Guard⟩
  | second =>
    have Hd : (oldHeaders (rows s) (x (rightNeighbor e))).h5=true :=
      (mask _).trans H
    have Guard : CommitGuard (secondParams s) (oldHeaders (rows s) (x e)).h5
        (x e).report2 (x (rightNeighbor e)).report2 delta := by
      rw [show (oldHeaders (rows s) (x e)).h5=h e from mask e]
      exact G
    have A := report2_commit_same_mark x e (edge_sep N e) Hd delta Guard
    exact ⟨A.1,A.2.1,A.2.2.1,A.2.2.2,
      fun sel=>report2_commit_keeps_digits x e (edge_sep N e) Hd delta sel Guard⟩

/-- The initiator of this COMMIT is outside the centre's digit
    word; only offset zero can be the responder. Hence the
    same-mark preservation theorem extends to ALL word digits,
    not merely to the centre digit. -/
theorem commit_keeps_whole_word (d : Sheet) (G : GapInput h) (r : Owner h)
    (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (atCentre : rightNeighbor e=centre (charter G r))
    (Room : (params d s).digits≤(charter G r).b)
    (delta sel : Nat)
    (Accept : CommitGuard (params d s) (h e) (selectBytes d (x e))
      (selectBytes d (x (rightNeighbor e))) delta) :
    let C := charter G r
    let p := params d s
    ∀ j,j<p.digits →
      reportDigitPair p (selectBytes d (rawNext s x e (nextAt (centre C) j))) sel=
        reportDigitPair p (selectBytes d (x (nextAt (centre C) j))) sel := by
  dsimp only
  let C := charter G r
  let p := params d s
  obtain ⟨A,K,Hdr,Lane,_⟩ := canonical_centre G r
  obtain ⟨J,Cell⟩ := ingress_cell G r e atCentre
  have Ce : out C (C.a-1)=e := congrArg Prod.fst Cell
  have Len : C.a+C.b≤C.L := by
    have End := end_dest C (C.L-1) (by have := C.positive; omega)
    have Port : C.route.port (C.L-1)=2 := by
      unfold reset0Destination at End
      split at End
      · split at End
        · assumption
        · contradiction
      · contradiction
    change ShortResetChart.lane C.a C.b (C.L-1)=2 at Port
    unfold ShortResetChart.lane at Port
    split at Port
    · contradiction
    · split at Port <;> (first | contradiction | omega)
  change (params d s).digits≤C.b at Room
  change 0<C.a at A
  have RH : h (rightNeighbor e)=true := by rw [atCentre]; exact Hdr
  have Meta := raw_commit_metadata d x e N mask RH delta Accept
  intro j D
  let site := nextAt (centre C) j
  have Site : site=out C (C.a+j) := by
    change nextAt (nextAt C.root C.a) j=nextAt C.root (C.a+j)
    exact (nextAt_add C.root C.a j).symm
  have NE : site≠e := by
    intro E
    have Eq := Site.symm.trans (E.trans Ce.symm)
    change nextAt C.root (C.a+j)=nextAt C.root (C.a-1) at Eq
    have U := nextAt_injective_under C.root (C.a+j) (C.a-1)
      (by have := C.length_lt; omega) (by have := C.length_lt; omega) Eq
    omega
  by_cases H : site=rightNeighbor e
  · change reportDigitPair p (selectBytes d (rawNext s x e site)) sel=reportDigitPair p (selectBytes d (x site)) sel
    rw [H]
    exact Meta.2.2.2.2 sel
  · exact congrArg (fun z=>reportDigitPair p (selectBytes d z) sel)
      (raw_spectator x e site NE H)

/-- Exact packet identity of the accepted ingress gives the
    CommitGuard of the checked old-snapshot effect. -/
theorem guard_of_lineage (d : Sheet) (G : GapInput h) (r : Owner h)
    (x : Raw s n) (e : Fin n) (delta : Nat)
    (atCentre : rightNeighbor e=centre (charter G r))
    (Accept : ancestryCommitOpportunity (params d s) (h e) true
      (selectBytes d (x e)) (selectBytes d (x (centre (charter G r)))))
    (Packet : tok d (charter G r) x ((charter G r).a-1)=
      ({tag:=2,opcode:=commitOp (params d s),payload:=delta}:Tok)) :
    CommitGuard (params d s) (h e) (selectBytes d (x e))
      (selectBytes d (x (rightNeighbor e))) delta := by
  let C := charter G r
  let p := params d s
  obtain ⟨_,Cell⟩ := ingress_cell G r e atCentre
  have Site : out C (C.a-1)=e := congrArg Prod.fst Cell
  have Lane : C.route.port (C.a-1)=0 := congrArg Prod.snd Cell
  have T : publicationToken p (h e) (selectBytes d (x e)) 0=
      ({tag:=2,opcode:=commitOp p,payload:=delta}:Tok) := by
    rw [predecessor_projection,Site,Lane] at Packet
    exact Packet
  have Guard := Accept.2.2.2.2
  rw [T] at Guard
  have G' : reportOldGrant p (selectBytes d (x (centre C))) 1=true ∧
      publicationSelector p (selectBytes d (x (centre C)))=delta/8 ∧
      reportOldSeal p (selectBytes d (x (centre C)))=some delta := by
    simpa [packetCommitGuard,Bool.and_eq_true,beq_iff_eq,and_assoc,
      reportOldGrant,reportOldSeal] using Guard
  unfold CommitGuard
  rw [atCentre]
  exact ⟨T,G'.1,G'.2.1,G'.2.2⟩

/-- Final item-9 semantic publication on one actual raw mark.
    The ONLY remaining digit premise is the before-mark staged
    file, which staged_at_seal + staged_after_seal supply. -/
theorem publish_of_staged_computation (d : Sheet) (N : 1<n)
    (G : GapInput h) (r : Owner h) (x : Raw s n) (e : Fin n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (atCentre : rightNeighbor e=centre (charter G r))
    (I : ItemNineInputs) (B : 2≤(params d s).beta)
    (R : (params d s).radius<(params d s).beta^(params d s).digits)
    (Room : (params d s).digits≤(charter G r).b)
    (delta : Nat)
    (Desc : delta=ReportCommitValue.descriptor I.prior (params d s).radius
      (updateDist (params d s).radius I.leftRoot I.left)
      (updateDist (params d s).radius I.rightRoot I.right))
    (Guard : CommitGuard (params d s) (h e) (selectBytes d (x e))
      (selectBytes d (x (rightNeighbor e))) delta)
    (Staged : ∀ j,j<(params d s).digits →
      reportDigitPair (params d s) (selectBytes d (x
        (nextAt (centre (charter G r)) j))) (1-I.prior)=
          BitVec.ofNat (2*ReportByteRows.d (params d s)) (item9Send (params d s) I j)) :
    let p := params d s
    let c := centre (charter G r)
    let y := rawNext s x e
    let post := fun i=>selectBytes d (y i)
    let a := updateDist p.radius I.leftRoot I.left
    let b := updateDist p.radius I.rightRoot I.right
    publicationSelector p (selectBytes d (x c))=I.prior ∧
    publicationSelector p (post c)=1-I.prior ∧
    publicationSelector p (post c)≠publicationSelector p (selectBytes d (x c)) ∧
    reportValue p post c true=a ∧ reportValue p post c false=b ∧
    publicationPair p (post c) (publicationSelector p (post c))=
      2*(decide (reportValue p post c true<p.radius)).toNat+
        (decide (reportValue p post c false<p.radius)).toNat ∧
    publicationA p (post c) (publicationSelector p (post c))=
      Z p (selectBytes d (x c)) := by
  dsimp only
  let p := params d s
  let C := charter G r
  let c := centre C
  let y := rawNext s x e
  let post := fun i=>selectBytes d (y i)
  let a := updateDist p.radius I.leftRoot I.left
  let b := updateDist p.radius I.rightRoot I.right
  have Prior : I.prior≤1 := by unfold ItemNineInputs.prior; omega
  have D := ReportCommitValue.descriptor_fields I.prior p.radius a b Prior
  rw [←Desc] at D
  obtain ⟨_,_,Hdr,_,_⟩ := canonical_centre G r
  have RH : h (rightNeighbor e)=true := by rw [atCentre]; exact Hdr
  have Meta := raw_commit_metadata d x e N mask RH delta Guard
  rw [atCentre] at Meta
  have Old : publicationSelector p (selectBytes d (x c))=I.prior := by
    have H := Guard.2.2.1
    rw [atCentre] at H
    exact H.trans D.1
  have Sel : publicationSelector p (post c)=1-I.prior := Meta.1.trans D.2.1
  have Digits (j : Nat) (J : j<p.digits) :
      selectedDigit p (1-I.prior) true (post (nextAt c j))=digit p.beta j a ∧
      selectedDigit p (1-I.prior) false (post (nextAt c j))=digit p.beta j b := by
    have F := commit_keeps_whole_word d G r x e N mask atCentre Room delta
      (1-I.prior) Guard j J
    have E := F.trans (Staged j J)
    rw [item9_send_digits p I j B] at E
    exact selected_digit_of_pack p _ _ _ _ B
      (Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide : 0<2) B))
      (Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide : 0<2) B)) E
  have L := ReportCommitValue.value_of_preserved_digits p post c true (1-I.prior)
    I.left I.leftRoot B R Sel (fun j J=>(Digits j J).1)
  have U := ReportCommitValue.value_of_preserved_digits p post c false (1-I.prior)
    I.right I.rightRoot B R Sel (fun j J=>(Digits j J).2)
  refine ⟨Old,Sel,?_,L,U,?_,?_⟩
  · rw [Sel,Old]
    omega
  · rw [Sel,←D.2.1,L,U]
    exact Meta.2.2.1.trans D.2.2
  · rw [Sel,←D.2.1]
    exact Meta.2.1

end L4.ReportItemNinePublication

namespace L4.ReportItemNinePublication
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportByteRows ReportPrelaunchK1Geometry ReportPrelaunchClock
open ReportLeaseOwner ReportOwnerCommandRail ReportGoodEightCut
open ReportIndexedSourcePrefix ReportItemNineTrace ReportItemNineStaging
open ReportDigitArithmetic ReportStaticSpacing ReportGenerationAncestry

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- ITEM9H1, concrete consumer. The single unfinished staging
    frame is Frame. Reads/Writes are the actual item-8 per-credit
    certificates, not claims about the final arithmetic result. -/
theorem item9_handoff (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Frame : ItemNineStagedFrame d hh Q G)
    (r : Owner h) (b : Raw s n) (pre late : List (Fin n))
    (l ll : List Receipt) (e : Fin n)
    (A : FirstCut d hh Q G b) (Serial : StrongSerial d (charter G r) b)
    (PC : readPC d (charter G r) b=(1,cmpOp (params d s)))
    (SeedZero : item9Read (params d s) (rootBytes d (charter G r) b) .input=0)
    (T : AckTape d (charter G r) b pre l)
    (Late : AckTape d (charter G r) (rawRun b pre) late ll)
    (SealPC : readPC d (charter G r) (rawRun b pre)=(1,sealOp (params d s)))
    (Reads : SnapshotReceipts d (charter G r) b l)
    (Writes : WriteCredits d (charter G r) b pre l
      (snapshotInputs d (charter G r) b).prior)
    (Room : (params d s).digits≤(charter G r).b)
    (atCentre : rightNeighbor e=centre (charter G r))
    (Accept : let x := rawRun (rawRun b pre) late
      ancestryCommitOpportunity (params d s) (h e) true (selectBytes d (x e))
        (selectBytes d (x (centre (charter G r)))))
    (Lineage : let C := charter G r
      let p := params d s
      let x := rawRun (rawRun b pre) late
      tok d C x (C.a-1)=({tag:=2,opcode:=commitOp p,payload:=ReportSealDescriptor.descriptor p (rootBytes d C (rawRun b pre))}:Tok)) :
    let C := charter G r
    let p := params d s
    let I := snapshotInputs d C b
    let x := rawRun (rawRun b pre) late
    let post := fun i=>selectBytes d (rawNext s x e i)
    let c := centre C
    let delta := ReportSealDescriptor.descriptor p (rootBytes d C (rawRun b pre))
    let a := updateDist p.radius I.leftRoot I.left
    let z := updateDist p.radius I.rightRoot I.right
    delta=ReportCommitValue.descriptor I.prior p.radius a z ∧
      delta/8=I.prior ∧ (delta/4)%2=1-I.prior ∧
      publicationSelector p (selectBytes d (x c))=I.prior ∧
      publicationSelector p (post c)=1-I.prior ∧
      publicationSelector p (post c)≠publicationSelector p (selectBytes d (x c)) ∧
      reportValue p post c true=a ∧ reportValue p post c false=z ∧
      publicationPair p (post c) (publicationSelector p (post c))=
        2*(decide (reportValue p post c true<p.radius)).toNat+
          (decide (reportValue p post c false<p.radius)).toNat ∧
      publicationA p (post c) (publicationSelector p (post c))=Z p (selectBytes d (x c)) := by
  dsimp only
  let C := charter G r
  let p := params d s
  let I := snapshotInputs d C b
  let atSeal := rawRun b pre
  let x := rawRun atSeal late
  let delta := ReportSealDescriptor.descriptor p (rootBytes d C atSeal)
  have M := ReportPrelaunchDoorProducer.digits_positive d Spos
  obtain ⟨B,R⟩ := actual_params_fit d Spos
  obtain ⟨XL,XR⟩ := snapshot_bounds d C b B
  have Seed : ItemNineAt p I (readPC d C b).2 (item9Read p (rootBytes d C b)) := by
    rw [PC]
    exact item9_seed p I _ M rfl rfl SeedZero
  have Data := snapshot_receipts_to_math d C b l B Reads
  have H := math_run d C I B XL XR R b pre l T Seed Data
  rw [SealPC] at H
  have Desc : delta=ReportCommitValue.descriptor I.prior p.radius
      (updateDist p.radius I.leftRoot I.left) (updateDist p.radius I.rightRoot I.right) :=
    semantic_seal_descriptor p I _ B R H
  have St := staged_at_seal d N hh G F M Frame r b pre l I B XL XR R A Serial
    (congrArg Prod.snd PC) Seed (congrArg Prod.snd SealPC) T Data Writes Room
  have AS := first_cut_run d N hh G F M b A pre
  have SS := (strong_run d C N hh G F M b A.1.1.1 Serial pre).2.1
  have OldStaged := staged_after_seal d N hh G F M Frame r atSeal late ll I AS SS
    (congrArg Prod.snd SealPC) Late Room St
  have AX := first_cut_run d N hh G F M atSeal AS late
  have Guard := guard_of_lineage d G r x e delta atCentre Accept Lineage
  have Result := publish_of_staged_computation d N G r x e
    ((cached_fibre d N hh Q F).mask x AX.1.1.1) atCentre I B R Room delta Desc Guard OldStaged
  have Prior : I.prior≤1 := by unfold ItemNineInputs.prior; omega
  have D := ReportCommitValue.descriptor_fields I.prior p.radius
    (updateDist p.radius I.leftRoot I.left) (updateDist p.radius I.rightRoot I.right) Prior
  rw [←Desc] at D
  exact ⟨Desc,D.1,D.2.1,Result⟩

end L4.ReportItemNinePublication

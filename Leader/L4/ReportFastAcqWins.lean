import Leader.L4.ReportAcquireAllCaptures
import Leader.L4.ReportFastLeaseSupport
import Leader.L4.ReportFastFiveGeometry
import Leader.L4.ReportDigitHits
import Leader.L4.ReportFastFreshReset

namespace L4.ReportFastAcqWins
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportRawProjection ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerForwardControl ReportOwnerReverseShape
open ReportOwnerReverseControl ReportOwnerIssueControl ReportPrelaunchClock
open ReportOwnerAcquireProvenance ReportOwnerAcquireReturn
open ReportAcquireAllWins ReportAcquireAllCaptures
open ReportJoinedGrants ReportLeaseGrants ReportOwnerCommandRail
open ReportFastLeaseSupport

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- Six actual old incidences, two at each of three target headers.
    No claim about the target's own incumbent is hidden here. -/
def RivalFence (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  ∀ i, i<C.L → h (out C i)=true →
    ∀ j : Fin 3, j≠C.route.port i →
      grantAsk (params d s) true (selectBytes d (x (out C i)))
        (acqOp (params d s)) j=false ∧
      rawGrant d x (out C i) j=false

def ClearFrom (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Prop :=
  ∀ i, k≤i → i<C.L → h (out C i)=true →
    rawGrant d x (out C i) (C.route.port i)=false

abbrev OwnClear (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  ClearFrom d C x 0

private theorem old_lane_token (d : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) (H : h (out C i)=true) :
    tok d C x i = publicationToken (params d s) true
      (selectBytes d (x (out C i))) (C.route.port i) := by
  rw [predecessor_projection, H]
  rfl

private theorem ask_lane_iff (d : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) (H : h (out C i)=true) :
    (oldView (params d s) true (selectBytes d (x (out C i)))).ask
        (C.route.port i)=true ↔
      (tok d C x i).tag=2 ∧ (tok d C x i).fault=false ∧
        (tok d C x i).opcode=acqOp (params d s) := by
  -- CHECK: oldView, ReportJoinedGrants.lean:7; compare the proof
  -- of release_old_token in ReportLeaseGrants.lean:187–191.
  change (((publicationToken (params d s) true (selectBytes d (x (out C i)))
      (C.route.port i)).tag==2) &&
    !(publicationToken (params d s) true (selectBytes d (x (out C i)))
      (C.route.port i)).fault &&
    (publicationToken (params d s) true (selectBytes d (x (out C i)))
      (C.route.port i)).opcode==acqOp (params d s))=true ↔ _
  rw [←old_lane_token d C x i H]
  simp [Bool.and_eq_true,beq_iff_eq,and_assoc]

private theorem lane_no_ask (d : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) (H : h (out C i)=true)
    (T : (tok d C x i).tag≠2) :
    (oldView (params d s) true (selectBytes d (x (out C i)))).ask
      (C.route.port i)=false := by
  apply Bool.eq_false_iff.mpr
  intro A
  exact T ((ask_lane_iff d C x i H).mp A).1

/-- Absent incidence stays absent unless its *own outgoing* row asks.
    The incoming and spectator branches do not require no-ASK. -/
theorem absent_step (d : Sheet) (x : Raw s n) (e a : Fin n)
    (j : Fin 3) (N : 1<n)
    (Hdr : lower d (oldHeaders (rows s) (x a))=true)
    (O : rawGrant d x a j=false)
    (A : e=a → (oldView (params d s) true (selectBytes d (x a))).ask j=false) :
    rawGrant d (rawNext s x e) a j=false := by
  by_cases E : e=a
  · subst e
    have R := (raw_grant_rows d x a (edge_sep N a) j).1
    rw [Hdr] at R
    exact R.trans (no_ask_no_create _ j O (A rfl))
  · by_cases B : a=rightNeighbor e
    · subst a
      exact incoming_no_create_raw d x e N j O
    · unfold rawGrant
      rw [raw_spectator x e a (Ne.symm E) B]
      exact O

/-- Pre-first-ACQ prefix from the actual fresh RESET receipt.
    The final issue state is allowed to have opcode ACQ. -/
def PreACQPrefix (d : Sheet) (C : Chart h) :
    Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x, e::w => (readPC d C x).2≠acqOp (params d s) ∧
      PreACQPrefix d C (rawNext s x e) w

theorem own_clear_pre_run (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (A : StrongSerial d C x)
    (O : OwnClear d C x) (w : List (Fin n))
    (W : PreACQPrefix d C x w) :
    OwnClear d C (rawRun x w) := by
  induction w generalizing x with
  | nil => exact O
  | cons e w IH =>
    have CF := cached_fibre d N hh Q F
    have Y := CF.closed x e X
    have B := strong_step d C N hh G F x X A digit e
    have O' : OwnClear d C (rawNext s x e) := by
      intro i _ I H
      apply absent_step d x e (out C i) (C.route.port i) N
        ((CF.mask x X _).trans H) (O i (Nat.zero_le _) I H)
      intro _
      apply Bool.eq_false_iff.mpr
      intro K
      obtain ⟨Tag,Live,Op⟩ := (ask_lane_iff d C x i H).mp K
      exact W.1 ((A.2 i I (.inl Tag) Live).symm.trans Op)
    exact IH _ Y B O' W.2

theorem own_clear_from_receipt (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (reset pre : List (Fin n)) (R : Generated d C x reset .done)
    (W : PreACQPrefix d C (rawRun x reset) pre) :
    OwnClear d C (rawRun (rawRun x reset) pre) := by
  obtain ⟨Y,P⟩ := cached_genuine_full_parked d C N hh F x X reset R
  have A := seed_receipt d C N hh F x X reset R
  have O : OwnClear d C (rawRun x reset) := by
    intro i _ I H
    exact P.1.2.2 i I H
  exact own_clear_pre_run d C N hh G F digit _ Y A O pre W

theorem issue_clear (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (O : OwnClear d C x) :
    OwnClear d C (rawNext s x (door C)) := by
  intro i _ K H
  apply absent_step d x (door C) (out C i) (C.route.port i) N
    (((cached_fibre d N hh Q F).mask x X _).trans H)
    (O i (Nat.zero_le _) K H)
  intro _
  apply lane_no_ask d C x i H
  rw [I.2.2 i K]
  decide

/-- A fully joined real win, not a success inferred from a return.
    The last conjunct verifies that the production mask cannot discard the
    real assignment. The raw equality is from both joined endpoints. -/
theorem actual_header_win (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (mask : ∀ i, lower d (oldHeaders (rows s) (x i))=h i)
    (k q : Nat) (R : FState d C x k q)
    (Hdr : h (out C k)=true) (RF : RivalFence d C x)
    (Own : rawGrant d x (out C k) (C.route.port k)=false) :
    let p := params d s
    let e := out C k
    let u := selectBytes d (x e)
    let v := selectBytes d (x (rightNeighbor e))
    let j := C.route.port k
    acqFlightWin p true u j=true ∧
      rawGrant d (rawNext s x e) e j=true ∧
      (BStarShort.reportWork p (true,h (rightNeighbor e)) (u,v)).1.mask.getLsbD
        (grantAddr p j) =
      (row p (true,h (rightNeighbor e)) (u,v)).1.mask.getLsbD
        (grantAddr p j) := by
  dsimp only
  let p := params d s
  let e := out C k
  let u := selectBytes d (x e)
  let j := C.route.port k
  have I := R.shape.2.1
  have T : publicationToken p true u j=acqFlightF p q :=
    (old_lane_token d C x k Hdr).symm.trans R.packet
  have Ask : grantAsk p true u (acqOp p) j=true := by
    rw [plain_departure_ask p u (acqOp p) j (by unfold acqOp admitOp; omega)]
    change (((publicationToken p true u j).tag==2) &&
      !(publicationToken p true u j).fault &&
      (publicationToken p true u j).opcode==acqOp p)=true
    rw [T]
    simp [acqFlightF]
  have NoRel : grantAsk p true u 0 j=false := by
    rw [plain_departure_ask p u 0 j (by unfold admitOp; omega)]
    change (((publicationToken p true u j).tag==2) &&
      !(publicationToken p true u j).fault &&
      (publicationToken p true u j).opcode==0)=false
    rw [T]
    simp [acqFlightF,acqOp]
  have Free (l : Fin 3) : rawGrant d x e l=false := by
    by_cases L : l=j
    · subst l; exact Own
    · exact (RF k I Hdr l L).2
  have Rival : j≠1 → grantAsk p true u (acqOp p) 1=false := by
    intro J
    exact (RF k I Hdr 1 (Ne.symm J)).1
  have W : acqFlightWin p true u j=true :=
    old_grant_free_wins p u (grantAsk p true u (acqOp p))
      (grantAsk p true u 0) j Free Ask NoRel Rival
  have Held := free_win_raw d x e N ((mask e).trans Hdr) j Free Ask NoRel Rival
  have V : (oldView p true u).win j=true :=
    (raw_outgoing_fresh_exact d x e (edge_sep N e) ((mask e).trans Hdr)
      j Own).symm.trans Held
  exact ⟨W,Held,keep_real_grant_assignment p true (h (rightNeighbor e)) u
    (selectBytes d (x (rightNeighbor e))) j (.inl V)⟩

/-- Public duplicate of just the arithmetic content of the private
    acqFlight_edit_low, ReportByteRows.lean:7650–7659. No byte-layout
    definition is altered. -/
private def lowEdit (q j : Nat) (b : Bool) : Nat :=
  if (q >>> j)%2==1 then
    if b then q else q-2^j
  else if b then q+2^j else q

private theorem low_edit_bound (q j : Nat) (b : Bool) (Q0 : q<128)
    (J : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5) :
    lowEdit q j b<128 ∧ lowEdit q j b/64=q/64 := by
  rcases J with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp [lowEdit,Nat.shiftRight_eq_div_pow] <;>
    split <;> omega

theorem win_keeps_success (p : Params) (u : BitVec p.w) (j : Fin 3)
    (q : Nat) (B : q<128) (W : acqFlightWin p true u j=true) :
    acqFlightNext p true u j q/64=q/64 := by
  rw [acqFlightNext,if_pos rfl,if_pos W]
  -- CHECK: the private writeBit and bit at ReportByteRows.lean:35,194–195;
  -- change uses their bodies definitionally, never their private names.
  change lowEdit (lowEdit q (5-j.val) (publicationSelector p u==1))
    (2-j.val) (publicationA p u (publicationSelector p u))/64=q/64
  have J := j.isLt
  have A := low_edit_bound q (5-j.val) (publicationSelector p u==1) B (by omega)
  have D := low_edit_bound (lowEdit q (5-j.val) (publicationSelector p u==1))
    (2-j.val) (publicationA p u (publicationSelector p u)) A.1 (by omega)
  exact D.2.trans A.2

theorem actual_header_capture (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (mask : ∀ i, lower d (oldHeaders (rows s) (x i))=h i)
    (k q : Nat) (R : FState d C x k q) (S : q/64=1)
    (Hdr : h (out C k)=true) (RF : RivalFence d C x)
    (Own : rawGrant d x (out C k) (C.route.port k)=false) :
    let p := params d s
    let e := out C k
    let u := selectBytes d (x e)
    let j := C.route.port k
    let r := stepPayload d C x k q
    r/64=1 ∧
    acqPair r j=(publicationSelector p u,(publicationA p u (publicationSelector p u)).toNat) ∧
    acqFlightWin p true u j=true ∧ rawGrant d (rawNext s x e) e j=true := by
  dsimp only
  let p := params d s
  let u := selectBytes d (x (out C k))
  let j := C.route.port k
  have V := actual_header_win d C N x mask k q R Hdr RF Own
  have S' : acqFlightNext p true u j q/64=1 :=
    (win_keeps_success p u j q R.bound V.1).trans S
  have B := acqFlight_capture_pair p u j q R.bound S'
  refine ⟨?_,?_,V.1,V.2.1⟩
  · simpa only [stepPayload,bytesL,Hdr] using S'
  · simpa only [stepPayload,bytesL,Hdr] using B.2

/-- The current cursor is the sole possible own ACQ ASK. Thus an
    unvisited incidence is framed on every mark except its own departure. -/
theorem clear_unvisited (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (mask : ∀ i, lower d (oldHeaders (rows s) (x i))=h i)
    (k q : Nat) (R : FState d C x k q) (O : ClearFrom d C x k)
    (e : Fin n) (i : Nat) (K : k≤i) (I : i<C.L) (H : h (out C i)=true)
    (M : ¬(e=out C k ∧ i=k)) :
    rawGrant d (rawNext s x e) (out C i) (C.route.port i)=false := by
  apply absent_step d x e (out C i) (C.route.port i) N
    ((mask _).trans H) (O i K I H)
  intro E
  have J : i≠k := by
    intro V
    exact M ⟨by simpa only [V] using E,V⟩
  apply lane_no_ask d C x i H
  rw [R.shape.2.2 i I]
  simp [frontTag,show ¬i<k by omega,J]

/-- An actual forward departure cannot be the stationary branch of F_step.
    This is checked on the actual next decoded token, not on a chosen cursor. -/
theorem forward_depart (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k q : Nat)
    (R : FState d C x k q) :
    let y := rawNext s x (out C k)
    (k+1<C.L ∧ FState d C y (k+1) (stepPayload d C x k q)) ∨
    (k+1=C.L ∧ DState d C y k (stepPayload d C x k q)) := by
  dsimp only
  have mask := (cached_fibre d N hh Q F).mask x X
  rcases F_step d C hh G F N x X k q R (out C k) with B|⟨_,B⟩|⟨_,L,B⟩
  · by_cases J : k+1<C.L
    · have A := B.shape.2.2 (k+1) J
      rw [raw_hop d C x N mask k q J R] at A
      simp [acqFlightF,frontTag,show ¬k+1<k by omega] at A
    · have L : k+1=C.L := by have := R.shape.2.1; omega
      have A := B.shape.2.2 k R.shape.2.1
      rw [raw_turn d C x N mask k q L R] at A
      simp [frontTag] at A
  · exact .inl ⟨B.shape.2.1,B⟩
  · exact .inr ⟨L,B⟩

theorem forward_other (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k q : Nat)
    (R : FState d C x k q) (e : Fin n) (E : e≠out C k) :
    FState d C (rawNext s x e) k q := by
  rcases F_step d C hh G F N x X k q R e with B|⟨J,_⟩|⟨J,_,_⟩
  · exact B
  · exact (E J).elim
  · exact (E J).elim

/-- Exact success bit, and clear suffix while F is live. D has
    already traversed every header. No successful-return hypothesis. -/
def PhaseOK (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  (∃ k q, FState d C x k q ∧ q/64=1 ∧ ClearFrom d C x k) ∨
  (∃ k q, DState d C x k q ∧ q/64=1)

/-- Minimal use of RivalFence: only when the current mark is a live
    target F's outgoing header departure. -/
def DepartureFence (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Prop :=
  ∀ k q, FState d C x k q → e=out C k → h (out C k)=true → RivalFence d C x

theorem phase_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (A : PhaseOK d C x)
    (e : Fin n) (NC : NoConsume d C x e) (RF : DepartureFence d C x e) :
    PhaseOK d C (rawNext s x e) := by
  let mask := (cached_fibre d N hh Q F).mask x X
  rcases A with ⟨k,q,R,S,O⟩|⟨k,q,R,S⟩
  · by_cases E : e=out C k
    · subst e
      have S' : stepPayload d C x k q/64=1 := by
        by_cases H : h (out C k)=true
        · exact (actual_header_capture d C N x mask k q R S H
            (RF k q R rfl H) (O k (Nat.le_refl _) R.shape.2.1 H)).1
        · have H' : h (out C k)=false := Bool.eq_false_iff.mpr H
          simpa only [stepPayload,acqFlightNext,H',Bool.false_eq_true,if_false] using S
      rcases forward_depart d C N hh G F x X k q R with ⟨_,B⟩|⟨_,B⟩
      · left
        refine ⟨k+1,stepPayload d C x k q,B,S',?_⟩
        intro i K I H
        exact clear_unvisited d C N x mask k q R O (out C k) i
          (by omega) I H (by intro J; have := J.2; omega)
      · exact .inr ⟨k,stepPayload d C x k q,B,S'⟩
    · left
      refine ⟨k,q,forward_other d C N hh G F x X k q R e E,S,?_⟩
      intro i K I H
      exact clear_unvisited d C N x mask k q R O e i K I H (fun J=>E J.1)
  · right
    rcases D_step d C hh G F N x X k q R digit e NC with B|⟨j,_,_,B⟩
    · exact ⟨k,q,B,S⟩
    · exact ⟨j,q,B,S⟩

/-- Original raw tape before consume, with fence precisely at the steps
    where it is used. This is not a filter of the iid tape. -/
inductive FencedBefore (d : Sheet) (C : Chart h) (x0 : Raw s n) :
    List (Fin n) → Prop
  | nil : FencedBefore d C x0 []
  | snoc {w : List (Fin n)} (e : Fin n) (old : FencedBefore d C x0 w)
      (nc : NoConsume d C (rawRun x0 w) e)
      (fence : DepartureFence d C (rawRun x0 w) e) :
      FencedBefore d C x0 (w++[e])

theorem fenced_before_consume (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (T : FencedBefore d C x0 w) :
    BeforeConsume d C x0 w := by
  induction T with
  | nil => exact .nil
  | @snoc w e T NC RF IH => exact .snoc e IH NC

theorem fenced_run (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x0 : Raw s n)
    (X : Cached d hh Q x0) (A : FState d C x0 0 64) (O : OwnClear d C x0)
    (w : List (Fin n)) (T : FencedBefore d C x0 w) :
    Cached d hh Q (rawRun x0 w) ∧ PhaseOK d C (rawRun x0 w) := by
  induction T with
  | nil => exact ⟨X,.inl ⟨0,64,A,by decide,O⟩⟩
  | @snoc w e T NC RF IH =>
    rw [ShortOwnerEpochJS.raw_snoc]
    exact ⟨(cached_fibre d N hh Q F).closed _ e IH.1,
      phase_step d C N hh G F digit _ IH.1 IH.2 e NC RF⟩

/-- At a root D the success bit is forced by fenced_run. -/
theorem root_success (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : PhaseOK d C x) (Tag : (tok d C x 0).tag=3) :
    ∃ q, DState d C x 0 q ∧ q/64=1 ∧ (tok d C x 0).outcome≠1 := by
  rcases A with ⟨k,q,R,_,_⟩|⟨k,q,R,S⟩
  · rw [R.shape.2.2 0 C.positive] at Tag
    unfold frontTag at Tag
    split at Tag <;> try contradiction
    split at Tag <;> contradiction
  · have K : k=0 := by
      by_cases K : k=0
      · exact K
      · rw [R.shape.2.2 0 C.positive] at Tag
        simp [backTag,show 0<k by omega] at Tag
    subst k
    refine ⟨q,R,S,?_⟩
    rw [R.packet]
    simp [acqFlightD,S]

/-- The exact outgoing F carries the capture. If the current header is
    not the prior header, its edit leaves the prior lane's pair intact. -/
theorem earlier_capture_frames (d : Sheet) (C : Chart h) (G : GapInput h)
    (x : Raw s n) (i k q : Nat) (R : FState d C x k q)
    (I : i<k) (Hdr : h (out C i)=true) :
    acqPair (stepPayload d C x k q) (C.route.port i)=
      acqPair q (C.route.port i) := by
  have K := R.shape.2.1
  have Other : ¬(h (out C k)=true ∧ C.route.port k=C.route.port i) := by
    intro A
    have E := (header_lane_geometry C G).1 i k (by omega) K Hdr A.1 A.2.symm
    omega
  exact acqFlight_other_pair (params d s) (h (out C k))
    (selectBytes d (x (out C k))) (C.route.port k) (C.route.port i) q Other

/-- Arbitrary prefix after a real win, including all unrelated marks.
    Reuses the checked positive RAIL1 theorem, not a no-release premise. -/
theorem held_from_actual_win (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x0 : Raw s n)
    (X : Cached d hh Q x0) (A : FState d C x0 0 64)
    (i : Nat) (I : i<C.L) (H : h (out C i)=true)
    (Compat : Compatible (rawGrant d x0 (out C i)))
    (w : List (Fin n)) (T : FencedBefore d C x0 w)
    (pre : List (Fin n)) (P : (pre++[out C i]) <+: w)
    (Held : rawGrant d (rawNext s (rawRun x0 pre) (out C i))
      (out C i) (C.route.port i)=true) :
    rawGrant d (rawRun x0 w) (out C i) (C.route.port i)=true := by
  have B : rawGrant d (rawRun x0 (pre++[out C i])) (out C i)
      (C.route.port i)=true := by
    rw [ShortOwnerEpochJS.raw_snoc]
    exact Held
  exact ReportAcquireWinHold.acq_grant_from_prefix d C hh G F N x0 X A
    digit i I H Compat w (fenced_before_consume d C x0 w T) _ P B

/-- Main actual consume bridge. ND is NOT an input. The old D0
    root-tag condition describes the nominated consume, not its success.
    Each capture has an actual old departure witness on the original tape,
    and is installed in the literal six-bit source file. -/
theorem fenced_acq_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (P : readPC d C x=(1,acqOp (params d s)))
    (O : OwnClear d C x) (Compat : ∀ a,h a=true→Compatible (rawGrant d x a))
    (w : List (Fin n)) (T : FencedBefore d C (rawNext s x (door C)) w)
    (Tag : (tok d C (rawRun (rawNext s x (door C)) w) 0).tag=3) :
    let x0 := rawNext s x (door C)
    let old := rawRun x0 w
    let after := rawNext s old (door C)
    (tok d C old 0).outcome≠1 ∧
    Cached d hh Q after ∧ EmptyIssueShape d C after ∧
    readPC d C after=(1,cmpOp (params d s)) ∧
    ownerCaptureSix d C after=(tok d C old 0).payload%64 ∧
    ∀ i,i<C.L→h (out C i)=true→
      CapturedAt d C x0 w i (ownerCaptureSix d C after) ∧
      rawGrant d old (out C i) (C.route.port i)=true ∧
      rawGrant d after (out C i) (C.route.port i)=true := by
  dsimp only
  let x0 := rawNext s x (door C)
  let old := rawRun x0 w
  let after := rawNext s old (door C)
  obtain ⟨X0,A0⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N x X I P
  have O0 := issue_clear d C N hh F x X I O
  obtain ⟨Y,B⟩ := fenced_run d C N hh G F digit x0 X0 A0 O0 w T
  obtain ⟨q,R,S,ND⟩ := root_success d C old B Tag
  have Op : (readPC d C old).2=acqOp (params d s) := congrArg Prod.snd R.pc
  have K : (tok d C old 0).opcode=acqOp (params d s) := by
    rw [R.packet]
    exact acqFlightD_op _ _
  have L : (tok d C old 0).fault=false := by
    rw [R.packet]
    exact acqFlightD_live _ _
  have U := raw_acq_consume_six d C hh G F N old Y R.shape Op K L ND digit
  have BC := fenced_before_consume d C x0 w T
  refine ⟨ND,U.1,U.2.1,U.2.2.1,U.2.2.2,?_⟩
  intro i J H
  have Capt := successful_root_all_captures d C hh G F N x0 X0 A0 digit w BC Tag ND i J H
  have E : acqPair (ownerCaptureSix d C after) (C.route.port i)=
      acqPair (tok d C old 0).payload (C.route.port i) := by
    rw [U.2.2.2]
    exact acq_pair_mod _ _
  have C0 := raw_compatible_step d x (door C) (out C i)
    (edge_sep N _) (Compat _ H)
  have Held := ReportAcquireWinHold.successful_acq_grants_through_consume
    d C hh G F N x0 X0 A0 digit w BC Tag ND i J H C0
  exact ⟨capture_relabel d C x0 w i _ _ Capt E,Held.1,Held.2⟩

/-- Literal ordered zero-offset hits with varying OLD cached bytes.
    This specializes the checked digit geometry to ACQ's header test. -/
theorem ordered_acq_headers {n : Nat} (p : Params) {h : Fin n → Bool}
    (hh : ∃ i,h i=true) {r : Fin n} {a b c : Nat}
    (R : h r=true) (F : Gap h r a) (G : Gap h (nextAt r a) b)
    (I : Gap h (nextAt (nextAt r a) b) c) (room : a+b+c<n)
    (digit : 0<p.digits) (A : p.digits≤a) (B : p.digits≤b) (C : p.digits≤c)
    (snapshots : Fin (chart_of_three R F G I room).L → Fin n → BitVec p.w)
    (HC : ∀ q, ReportDigitHits.CacheCorrect p h hh (snapshots q)) :
    let chart := chart_of_three R F G I room
    ∃ q0 q1 q2 : Fin chart.L, q0.val<q1.val ∧ q1.val<q2.val ∧
      (∀ q : Fin chart.L, h (out chart q.val)=true ↔ q=q0 ∨ q=q1 ∨ q=q2) ∧
      chart.route.port q0.val=0 ∧ chart.route.port q1.val=1 ∧
      chart.route.port q2.val=2 := by
  dsimp only
  let chart := chart_of_three R F G I room
  obtain ⟨q0,q1,q2,L0,L1,H,T0,T1,T2⟩ :=
    ReportDigitHits.ordered_hits_varying_old p hh R F G I room 0 digit A B C snapshots HC
  refine ⟨q0,q1,q2,L0,L1,?_,T0,T1,T2⟩
  intro q
  have E := H q
  rw [ReportDigitHits.offset_from_cache p h hh (snapshots q) (HC q)] at E
  change (min (max 3 p.digits)
    (BStarH6Ordinal.ordinal h hh (out chart q.val))=0 ↔ _) at E
  rw [←E]
  have Z := BStarH6Ordinal.ordinal_zero h hh (out chart q.val)
  constructor
  · intro Hdr
    rw [Z.mpr Hdr,Nat.min_zero]
  · intro M
    apply Z.mp
    have T : 3≤max 3 p.digits := Nat.le_max_left _ _
    -- CHECK: ReportDigitHits.lean:39–47, ordinal_zero namespace.
    omega

/-- Specialize at the actual varying raw old snapshots for either sheet.
    No constant work-byte assumption, including at the capture fields. -/
theorem literal_cache (d : Sheet) (hh : ∃ i,h i=true)
    (x : Raw s n) (X : Cached d hh Q x) :
    ReportDigitHits.CacheCorrect (params d s) h hh (fun i=>selectBytes d (x i)) := by
  cases d
  · exact ReportDigitHits.report1_cache_is_literal hh x X
  · exact ReportDigitHits.report2_cache_is_literal hh x X

def fDebt (C : Chart h) (k : Nat) : Nat := 2*C.L-k
def dDebt (k : Nat) : Nat := k+1

/-- Exactly the raw nominated F edge. Each header win uses this edge;
    the same payment is also made on ordinary forward transport. -/
theorem forward_pays (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k q : Nat)
    (R : FState d C x k q) :
    let y := rawNext s x (out C k)
    (FState d C y (k+1) (stepPayload d C x k q) ∧ fDebt C (k+1)<fDebt C k) ∨
    (DState d C y k (stepPayload d C x k q) ∧ dDebt k<fDebt C k) := by
  dsimp only
  rcases forward_depart d C N hh G F x X k q R with ⟨J,B⟩|⟨J,B⟩
  · exact .inl ⟨B,by unfold fDebt; omega⟩
  · exact .inr ⟨B,by unfold dDebt fDebt; omega⟩

/-- Reverse payload is unchanged, and the nominated predecessor mark
    strictly decreases debt. -/
theorem reverse_pays (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (j q : Nat)
    (R : DState d C x (j+1) q) :
    DState d C (rawNext s x (out C j)) j q ∧ dDebt j<dDebt (j+1) := by
  have NC : NoConsume d C x (out C j) := by
    right
    rw [R.shape.2.2 0 C.positive]
    simp [backTag]
  have mask := (cached_fibre d N hh Q F).mask x X
  refine ⟨?_,by unfold dDebt; omega⟩
  rcases D_step d C hh G F N x X (j+1) q R digit (out C j) NC with B|⟨l,J,_,B⟩
  · have K := R.shape.2.1
    have T := B.shape.2.2 j (by omega)
    rw [raw_reverse_hop d C x N mask j q R] at T
    simp [backTag] at T
  · have E : l=j := by omega
    subst l
    exact B

theorem consume_pays : (0 : Nat)<dDebt 0 := by decide

/-- Literal local regression: even with both rival grant bits and both
    rival ASK bits zero, an incumbent OWN centre grant defeats a new
    fresh-win claim. The only live token is the actual F(64) in port 1.
    Everything outside the two declared bit fields is zero. -/
theorem incumbent_own_grant_counterexample :
    let p : Params := ⟨3,1,2,3⟩
    let u : BitVec p.w := BitVec.ofNat _
      ((resetTokenWire p (acqFlightF p 64)).toNat * 2^(tail p+tokenW p) +
        2^(grantAddr p 1))
    let v : BitVec p.w := 0
    publicationToken p true u 1=acqFlightF p 64 ∧
    grantAsk p true u (acqOp p) 0=false ∧
    grantAsk p true u (acqOp p) 2=false ∧
    u.getLsbD (grantAddr p 0)=false ∧
    u.getLsbD (grantAddr p 2)=false ∧
    u.getLsbD (grantAddr p 1)=true ∧
    acqFlightWin p true u 1=false ∧
    acqFlightNext p true u 1 64=0 ∧
    (ReportRawProjection.join p (true,false) (u,v)).1.getLsbD
      (grantAddr p 1)=true := by
  decide

end L4.ReportFastAcqWins


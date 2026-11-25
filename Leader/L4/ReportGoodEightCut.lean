import Leader.L4.ReportFirstCutGrant
import Leader.L4.ReportACQSelectedCapture
import Leader.L4.ReportReaderWordOwner
import Leader.L4.ReportGrantTimeline
import Leader.L4.ReportReaderDigitsLease

namespace L4.ReportGoodEightCut
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners
open ReportOwnerSerial ReportFirstCutGrant ReportLeaseGrants
open ReportLeaseOwner ReportGenerationAncestry ReportByteRows
open ReportOwnerIssueControl ReportOwnerDoorProjection ReportRawProjection

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem cached_run (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (w : List (Fin n)) :
    Cached d hh Q (rawRun x w) := by
  induction w generalizing x with
  | nil => exact X
  | cons e w IH =>
    exact IH _ ((cached_fibre d N hh Q F).closed x e X)

theorem charter_mem (G : GapInput h) (r : Owner h) :
    charter G r ∈ ownerCharts G := by
  unfold charter ownerCharts
  apply List.mem_filterMap.mpr
  exact ⟨r.val,by simp,dif_pos r.property⟩

/-- A real own RESET receipt, and its actual later suffix.
    This is stronger than Serial and is not a Parked snapshot. -/
def OwnerEpoch (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (y : Raw s n) : Prop :=
  ∃ a : Raw s n, ∃ reset tail : List (Fin n),
    Cached d hh Q a ∧ Generated d C a reset .done ∧
    y=rawRun (rawRun a reset) tail

theorem epoch_seed (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (a : Raw s n) (A : Cached d hh Q a) (w : List (Fin n))
    (R : Generated d C a w .done) :
    OwnerEpoch d C hh Q (rawRun a w) :=
  ⟨a,w,[],A,R,rfl⟩

theorem epoch_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (x : Raw s n) (e : Fin n) (E : OwnerEpoch d C hh Q x) :
    OwnerEpoch d C hh Q (rawNext s x e) := by
  obtain ⟨a,u,v,A,R,X⟩ := E
  refine ⟨a,u,v++[e],A,R,?_⟩
  rw [ShortOwnerEpochJS.raw_snoc,X]

theorem epoch_serial (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (E : OwnerEpoch d C hh Q x) : Serial d C x := by
  obtain ⟨a,u,v,A,R,X⟩ := E
  have B := seed_at_genuine_receipt d C N hh F a A u R
  have Y := cached_run d N hh F a A u
  have go (z : Raw s n) (Z : Cached d hh Q z)
      (T : Serial d C z) (w : List (Fin n)) :
      Serial d C (rawRun z w) := by
    induction w generalizing z with
    | nil => exact T
    | cons e w IH =>
      exact IH _ ((cached_fibre d N hh Q F).closed z e Z)
        (ReportOwnerSerial.all_mark d C N hh G F z Z T digit e)
  rw [X]
  exact go _ Y B v

/-- At T1, each owner has its real first epoch and all frozen
    header triples are compatible. No claim that all are parked. -/
def FirstCut (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) (x : Raw s n) : Prop :=
  AllSerialCompatible d hh Q G x ∧
    ∀ C∈ownerCharts G,OwnerEpoch d C hh Q x

theorem first_cut_closed (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (e : Fin n)
    (A : FirstCut d hh Q G x) :
    FirstCut d hh Q G (rawNext s x e) :=
  ⟨all_serial_compatible_closed d N hh G F digit x e A.1,
    fun C M=>epoch_step d C hh x e (A.2 C M)⟩

theorem first_cut_run (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (A : FirstCut d hh Q G x) (w : List (Fin n)) :
    FirstCut d hh Q G (rawRun x w) := by
  induction w generalizing x with
  | nil => exact A
  | cons e w IH =>
    exact IH _ (first_cut_closed d N hh G F digit x e A)

theorem first_cut_of_exact (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n))
    (U : ReportReceiptProvenance.ExactCover d N hh F (ownerCharts G) x w) :
    FirstCut d hh Q G (rawRun x.val w) := by
  have epochs : ∀ C∈ownerCharts G,OwnerEpoch d C hh Q (rawRun x.val w) := by
    intro C M
    obtain ⟨pre,flight,post,E,R,_⟩ :=
      ReportReceiptProvenance.locate_owner d N hh F (ownerCharts G) x w U C M
    refine ⟨rawRun x.val pre,flight,post,
      cached_run d N hh F x.val x.property pre,R,?_⟩
    rw [E,ShortOwnerEpochJS.raw_append,ShortOwnerEpochJS.raw_append]
  refine ⟨⟨⟨cached_run d N hh F x.val x.property w,?_⟩,?_⟩,epochs⟩
  · intro C M
    exact epoch_serial d C N hh G F digit _ (epochs C M)
  · exact headers_compatible_at_first_cut d N hh G F x w U

/-- One common anchor, and one shared suffix. Each chart's
    second reset is a generated subsegment of THAT suffix. -/
def SecondCutHistory (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) (x : Raw s n) : Prop :=
  ∃ z : Raw s n, ∃ w : List (Fin n),
    FirstCut d hh Q G z ∧ x=rawRun z w ∧
    ∀ C∈ownerCharts G,∃ pre flight post : List (Fin n),
      w=pre++flight++post ∧ Generated d C (rawRun z pre) flight .done

theorem second_history_closed (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (x : Raw s n) (e : Fin n)
    (A : SecondCutHistory d hh Q G x) :
    SecondCutHistory d hh Q G (rawNext s x e) := by
  obtain ⟨z,w,B,E,all⟩ := A
  refine ⟨z,w++[e],B,?_,?_⟩
  · rw [ShortOwnerEpochJS.raw_snoc,E]
  · intro C M
    obtain ⟨pre,flight,post,W,R⟩ := all C M
    refine ⟨pre,flight,post++[e],?_,R⟩
    rw [W,List.append_assoc]

theorem second_history_run (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (x : Raw s n)
    (A : SecondCutHistory d hh Q G x) (w : List (Fin n)) :
    SecondCutHistory d hh Q G (rawRun x w) := by
  induction w generalizing x with
  | nil => exact A
  | cons e w IH =>
    exact IH _ (second_history_closed d hh G x e A)

theorem second_has_first (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (A : SecondCutHistory d hh Q G x) : FirstCut d hh Q G x := by
  obtain ⟨z,w,B,E,_⟩ := A
  rw [E]
  exact first_cut_run d N hh G F digit z B w

-- CHECK: ReportReceiptProvenance.lean: locate_after_first_cover
-- is the already checked corollary of exact_cuts. Its first
-- endpoint is (rawRun x.val u), not a resampled configuration.
theorem second_at_finished (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n))
    (Hit : SequentialMarkClock.finished (SequentialMarkClock.run
      (SequentialMarkClock.step (ReportPrelaunchTwoCovers.advance d hh F N)
        (fun C=>ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
        (fun _=>ReportOwnerReceiptClock.done) none)
      (SequentialMarkClock.start none (ownerCharts G++ownerCharts G) x) w)) :
    ∃ u v tail : List (Fin n), w=(u++v)++tail ∧
      FirstCut d hh Q G (rawRun x.val u) ∧
      SecondCutHistory d hh Q G (rawRun x.val (u++v)) := by
  obtain ⟨u,v,tail,W,U,V⟩ :=
    ReportReceiptProvenance.locate_after_first_cover
      d N hh F (ownerCharts G) x w Hit
  have A := first_cut_of_exact d N hh G F digit x u U
  refine ⟨u,v,tail,W,A,rawRun x.val u,v,A,
    ShortOwnerEpochJS.raw_append x.val u v,?_⟩
  intro C M
  obtain ⟨pre,flight,post,E,R,_⟩ := V C M
  rw [ShortOwnerEpochJS.raw_append] at R
  exact ⟨pre,flight,post,E,R⟩

/-- Every second receipt has an actual post-T1 seed. This is the
    input of the local fresh-file induction. -/
theorem second_owner_seed (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (A : SecondCutHistory d hh Q G x)
    (C : Chart h) (M : C∈ownerCharts G) :
    ∃ a : Raw s n, ∃ flight post : List (Fin n),
      FirstCut d hh Q G a ∧ Generated d C a flight .done ∧
      FullParked d C (rawRun a flight) ∧
      x=rawRun (rawRun a flight) post := by
  obtain ⟨z,w,B,E,V⟩ := A
  obtain ⟨pre,flight,post,W,R⟩ := V C M
  have Apre := first_cut_run d N hh G F digit z B pre
  have Park := (cached_genuine_full_parked d C N hh F
    (rawRun z pre) Apre.1.1.1 flight R).2
  refine ⟨rawRun z pre,flight,post,Apre,R,Park,?_⟩
  rw [E,W,ShortOwnerEpochJS.raw_append,ShortOwnerEpochJS.raw_append]

/-- At the genuine consume, even the stronger generation tag has a
    noncircular seed. It is NOT an invariant that may be extended
    unchanged through an actual COMMIT or an actual RESET release. -/
theorem generation_seed (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (a : Raw s n) (A : Cached d hh Q a) (w : List (Fin n))
    (R : Generated d C a w .done) (num : Nat) :
    let x := rawRun a w
    ∃ g : GenerationTag, GenerationInv d C hh Q x g ∧
      g.number=num ∧ g.op=1 ∧ g.rail=.issue ∧
      g.centreWon=false ∧ g.fileInstalled=false ∧
      (∀ k,g.held k=false) ∧ g.heldSeal=none := by
  dsimp only
  let x := rawRun a w
  obtain ⟨X,P⟩ := cached_genuine_full_parked d C N hh F a A w R
  have geo := ReportOwnerAcquireProvenance.centre_geometry C G
  have K : C.a<C.L := by have := geo.1; omega
  obtain ⟨H,L⟩ := (geo.2 C.a K).mpr rfl
  let g : GenerationTag :=
    ⟨num,rawSelector d x (centre C),1,.issue,false,false,
      fun _=>false,none⟩
  have empty (k : Nat) (J : k<C.L) : tok d C x k=MISByteCodec.E := by
    rw [tok_wire,P.1.2.1 k J]
    rw [show canon (params d s) .empty =
      resetTokenWire (params d s) MISByteCodec.E from rfl,drain_decode_E]
  have pc := pc_fields d C x .issue1 (by decide) P.1.1
  refine ⟨g,?_,rfl,rfl,rfl,rfl,rfl,fun _=>rfl,rfl⟩
  refine ⟨X,K,H,L,ancestry_selector_lt _ _,rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · change controlWork (params d s) (sourceBytes d C x)=(1,1) ∧ _
    exact ⟨pc,empty⟩
  · intro k J hd
    exact P.1.2.2 k J hd
  · intro k J hd bad
    contradiction
  · intro bad
    contradiction
  · intro bad
    contradiction
  · exact drain_seal_none _ _ (P.2.2 C.a K H L)
  · intro k J W
    rw [empty k J] at W
    exact False.elim (by have := W.1; contradiction)

-- CHECK: ReportLeaseTwoCoverLift.lean:192–233 is the checked
-- model of this exact MonitorRawBridge instantiation.
theorem expected_second_history (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    IIDExpectedHittingTimeAtMost (rawNext s) (SecondCutHistory d hh Q G) x.val
      (2*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) := by
  let advance := ReportPrelaunchTwoCovers.advance d hh F N
  let phase := fun C : Chart h=>ReportOwnerReceiptClock.next d C
    (cached_fibre d N hh Q F)
  let goal := fun (_ : Chart h) (z : ReportOwnerReceiptClock.State (Cached d hh Q)) =>
    ReportOwnerReceiptClock.done z
  let next := SequentialMarkClock.step advance phase goal none
  let start := SequentialMarkClock.start (none : Option Stage)
    (ownerCharts G++ownerCharts G) x
  have phys : ∀ z e,(next z e).raw.val=rawNext s z.raw.val e := by
    intro z e
    unfold next
    rw [SequentialMarkClock.step_raw _ _ _ _ (fun _ _ _=>rfl)]
    rfl
  apply MonitorRawBridge.expected_of_monitor_words (rawNext s) next
    (fun z=>z.raw.val) SequentialMarkClock.finished
    (SecondCutHistory d hh Q G) phys start _ _
    (ReportPrelaunchAllOwners.expected d N S hh G Q F x)
  intro w B
  obtain ⟨u,v,tail,E,_,A⟩ := second_at_finished d N hh G F
    (ReportPrelaunchDoorProducer.digits_positive d S) x w B
  have runs (z : Raw s n) (w : List (Fin n)) :
      SequentialMarkClock.run (rawNext s) z w=rawRun z w := by
    induction w generalizing z with
    | nil => rfl
    | cons e w IH => exact IH (rawNext s z e)
  rw [show start.raw.val=x.val from rfl,runs,E,ShortOwnerEpochJS.raw_append]
  exact second_history_run d hh G _ A tail

open ReportGrantTimeline ReportJoinedGrants in
theorem second_grant_origin (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (A : SecondCutHistory d hh Q G x)
    (C : Chart h) (M : C∈ownerCharts G)
    (k : Nat) (K : k<C.L) (Hdr : h (out C k)=true)
    (Held : rawGrant d x (out C k) (C.route.port k)=true) :
    ∃ a : Raw s n, ∃ flight lead post : List (Fin n),
      FirstCut d hh Q G a ∧ Generated d C a flight .done ∧
      let b := rawRun a flight
      let old := rawRun b lead
      x=rawRun (rawNext s old (out C k)) post ∧
      rawGrant d old (out C k) (C.route.port k)=false ∧
      (oldView (params d s) true (selectBytes d (old (out C k)))).win
        (C.route.port k)=true ∧
      HeldAlong d (out C k) (C.route.port k)
        (rawNext s old (out C k)) post := by
  obtain ⟨a,flight,v,B,R,P,E⟩ :=
    second_owner_seed d N hh G F digit x A C M
  let b := rawRun a flight
  have B' := first_cut_run d N hh G F digit a B flight
  have Z : Cached d hh Q b := B'.1.1.1
  have Empty : rawGrant d b (out C k) (C.route.port k)=false :=
    P.1.2.2 k K Hdr
  have Headers (pre : List (Fin n)) (_ : ∃ suf,v=pre++suf) :
      lower d (oldHeaders (rows s) (rawRun b pre (out C k)))=true :=
    ((cached_fibre d N hh Q F).mask _ (cached_run d N hh F b Z pre) _).trans Hdr
  obtain ⟨lead,post,W,Old,Win,Stay⟩ :=
    last_win_after_clear d N (out C k) (C.route.port k) b v Headers
      Empty (E ▸ Held)
  refine ⟨a,flight,lead,post,B,R,?_,Old,Win,Stay⟩
  rw [E,W,ShortOwnerEpochJS.raw_append]
  rfl
end L4.ReportGoodEightCut

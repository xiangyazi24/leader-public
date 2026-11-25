import Leader.L4.ReportGrantTimeline
import Leader.L4.ReportAcquireWinHold
import Leader.L4.ReportOwnerCommandRail

namespace L4.ReportAcquireAllCaptures
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportOwnerProvenanceTransport ReportOwnerForwardLocations
open ReportOwnerReverseShape ReportOwnerReverseControl ReportOwnerAcquireProvenance
open ReportLeaseGrants ReportJoinedGrants ReportAcquireAllWins
open ReportOwnerAcquireReturn ReportOwnerIssueControl ReportOwnerCommandRail
open ReportPrelaunchClock ReportGrantTimeline

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- No second occurrence at the same header port, and all ports
    represented. This is the only additional geometric ingredient. -/
theorem header_lane_geometry (C : Chart h) (G : GapInput h) :
    (∀ i k,i<C.L→k<C.L→h (out C i)=true→h (out C k)=true→
      C.route.port i=C.route.port k→i=k) ∧
    (∀ j : Fin 3,∃ i,i<C.L ∧ h (out C i)=true ∧ C.route.port i=j) := by
  obtain ⟨a,A,A',F⟩ := G.gaps C.root C.rootHeader
  obtain ⟨b,B,B',J⟩ := G.gaps (nextAt C.root a) F.atEnd
  obtain ⟨c,D,D',K⟩ := G.gaps (nextAt (nextAt C.root a) b) J.atEnd
  have room : a+b+c<n := by have := G.room; omega
  let C' := chart_of_three C.rootHeader F J K room
  have U := ShortReadCaptureGeometry.chart_unique C C' rfl
  have L : C.L=a+b+c := U.1
  have ports (i : Nat) (I : i<C.L) : C.route.port i=lane a b i := U.2 i I
  have cls (i : Nat) (I : i<C.L) (H : h (out C i)=true) :
      i=0 ∨ i=a ∨ i=a+b := by
    by_cases Z : i=0
    · exact .inl Z
    · have T := (three_gap_exact F J K i (by omega) (by omega)).mp H
      omega
  have P0 : C.route.port 0=0 := (ports 0 (by omega)).trans
    (by simp [lane,show 0<a by omega])
  have PA : C.route.port a=1 := (ports a (by omega)).trans
    (by simp [lane,show a<a+b by omega])
  have PB : C.route.port (a+b)=2 := (ports (a+b) (by omega)).trans
    (by simp [lane,show ¬a+b<a by omega])
  constructor
  · intro i k I K0 H T E
    rcases cls i I H with rfl|rfl|rfl <;>
      rcases cls k K0 T with rfl|rfl|rfl <;>
      first | rfl |
        (simp only [P0,PA,PB] at E
         first | contradiction | exact (False.elim ((by decide : ¬ ((0:Fin 3)=1)) E)) |
           exact (False.elim ((by decide : ¬ ((0:Fin 3)=2)) E)) |
           exact (False.elim ((by decide : ¬ ((1:Fin 3)=0)) E)) |
           exact (False.elim ((by decide : ¬ ((1:Fin 3)=2)) E)) |
           exact (False.elim ((by decide : ¬ ((2:Fin 3)=0)) E)) |
           exact (False.elim ((by decide : ¬ ((2:Fin 3)=1)) E)))
  · intro j
    have Cases : j=0 ∨ j=1 ∨ j=2 := by
      by_cases A : j.val=0
      · exact .inl (Fin.ext A)
      · by_cases B : j.val=1
        · exact .inr (.inl (Fin.ext B))
        · exact .inr (.inr (Fin.ext (by have := j.isLt; change j.val=2; omega)))
    rcases Cases with rfl|rfl|rfl
    · exact ⟨0,by omega,C.rootHeader,P0⟩
    · exact ⟨a,by omega,F.atEnd,PA⟩
    · refine ⟨a+b,by omega,?_,PB⟩
      change h (nextAt C.root (a+b))=true
      rw [nextAt_add]
      exact J.atEnd

/-- A pair of authenticated historical bits in the current payload.
    Index i is the actual chart occurrence, not a guessed header. -/
def CapturedAt (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (i q : Nat) : Prop :=
  ∃ pre post : List (Fin n), ∃ r : Nat,
    w=pre++(out C i::post) ∧
    let z := rawRun x0 pre
    let p := params d s
    let u := selectBytes d (z (out C i))
    FState d C z i r ∧
    acqFlightWin p true u (C.route.port i)=true ∧
    rawGrant d (rawNext s z (out C i)) (out C i) (C.route.port i)=true ∧
    acqPair q (C.route.port i) =
      (publicationSelector p u,(publicationA p u (publicationSelector p u)).toNat)

theorem captured_won (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (i q : Nat) (A : CapturedAt d C x0 w i q) :
    WonAt d C x0 w i := by
  obtain ⟨u,v,r,E,F,W,H,_⟩ := A
  exact ⟨u,v,r,E,F,W,H⟩

theorem capture_relabel (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (i q r : Nat) (A : CapturedAt d C x0 w i q)
    (E : acqPair r (C.route.port i)=acqPair q (C.route.port i)) :
    CapturedAt d C x0 w i r := by
  obtain ⟨u,v,p,W,F,S,H,B⟩ := A
  exact ⟨u,v,p,W,F,S,H,E.trans B⟩

private theorem capture_snoc (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (e : Fin n) (i q r : Nat) (A : CapturedAt d C x0 w i q)
    (E : acqPair r (C.route.port i)=acqPair q (C.route.port i)) :
    CapturedAt d C x0 (w++[e]) i r := by
  obtain ⟨u,v,p,W,F,S,H,B⟩ := A
  exact ⟨u,v++[e],p,by rw [W,List.append_assoc]; rfl,F,S,H,E.trans B⟩

def AllCapturesFlightAt (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) : Prop :=
  (∃ k q,FState d C (rawRun x0 w) k q ∧
    (q/64=1 → ∀ i,i<k→h (out C i)=true→CapturedAt d C x0 w i q)) ∨
  (∃ k q,DState d C (rawRun x0 w) k q ∧
    (q/64=1 → ∀ i,i<C.L→h (out C i)=true→CapturedAt d C x0 w i q))

private theorem append_capture (d : Sheet) (C : Chart h) (G : GapInput h)
    (N : 1<n) (x0 : Raw s n) (w : List (Fin n))
    (mask : ∀ i,lower d (oldHeaders (rows s) (rawRun x0 w i))=h i)
    (k q : Nat) (R : FState d C (rawRun x0 w) k q)
    (Old : q/64=1 → ∀ i,i<k→h (out C i)=true→CapturedAt d C x0 w i q)
    (S : stepPayload d C (rawRun x0 w) k q/64=1)
    (i : Nat) (I : i<k+1) (Hdr : h (out C i)=true) :
    CapturedAt d C x0 (w++[out C k]) i (stepPayload d C (rawRun x0 w) k q) := by
  let p := params d s
  let z := rawRun x0 w
  let e := out C k
  by_cases K : i=k
  · subst i
    change acqFlightNext p (h e) (selectBytes d (z e)) (C.route.port k) q/64=1 at S
    rw [Hdr] at S
    have W := acqFlight_capture_pair p (selectBytes d (z e)) (C.route.port k) q R.bound S
    have E := (raw_grant_rows d z e (edge_sep N e) (C.route.port k)).1
    rw [mask e,Hdr,next_agrees] at E
    refine ⟨w,[],q,rfl,R,W.1,E.trans (acqFlight_win_grant p _ _ W.1),?_⟩
    simpa only [stepPayload,bytesL,Hdr] using W.2
  · have A := acqFlight_next_spec p (h e) (selectBytes d (z e)) (C.route.port k) q R.bound
    have K0 := R.shape.2.1
    have Other : ¬(h e=true ∧ C.route.port k=C.route.port i) := by
      intro H
      exact K ((header_lane_geometry C G).1 i k (by omega) K0 Hdr H.1 H.2.symm)
    exact capture_snoc d C x0 w e i q _ (Old (A.2.1 S) i (by omega) Hdr)
      (acqFlight_other_pair p (h e) (selectBytes d (z e)) (C.route.port k)
        (C.route.port i) q Other)

theorem all_captures_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (w : List (Fin n))
    (X : Cached d hh Q (rawRun x0 w)) (A : AllCapturesFlightAt d C x0 w)
    (digit : 0<(params d s).digits) (e : Fin n)
    (NC : NoConsume d C (rawRun x0 w) e) :
    AllCapturesFlightAt d C x0 (w++[e]) := by
  let x := rawRun x0 w
  let CF := cached_fibre d N hh Q F
  have E : rawRun x0 (w++[e])=rawNext s x e :=
    ShortOwnerEpochJS.raw_snoc x0 w e
  rcases A with ⟨k,q,R,H⟩|⟨k,q,R,H⟩
  · rcases F_step d C hh G F N x X k q R e with A|⟨J,A⟩|⟨J,T,A⟩
    · left
      exact ⟨k,q,E ▸ A,fun S i I Hd=>capture_snoc d C x0 w e i q q (H S i I Hd) rfl⟩
    · subst e
      left
      refine ⟨k+1,stepPayload d C x k q,?_,?_⟩
      · rw [E]; exact A
      · intro S i I Hd
        exact append_capture d C G N x0 w (CF.mask x X) k q R H S i I Hd
    · subst e
      right
      refine ⟨k,stepPayload d C x k q,?_,?_⟩
      · rw [E]; exact A
      · intro S i I Hd
        exact append_capture d C G N x0 w (CF.mask x X) k q R H S i (by omega) Hd
  · rcases D_step d C hh G F N x X k q R digit e NC with A|⟨j,_,_,A⟩
    · right
      exact ⟨k,q,E ▸ A,fun S i I Hd=>capture_snoc d C x0 w e i q q (H S i I Hd) rfl⟩
    · right
      exact ⟨j,q,E ▸ A,fun S i I Hd=>capture_snoc d C x0 w e i q q (H S i I Hd) rfl⟩

theorem all_captures_run (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (A : FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x0 w) :
    Cached d hh Q (rawRun x0 w) ∧ AllCapturesFlightAt d C x0 w := by
  induction T with
  | nil =>
    exact ⟨X,.inl ⟨0,64,A,fun _ i I _=>(by omega : False).elim⟩⟩
  | @snoc w e T NC IH =>
    constructor
    · rw [ShortOwnerEpochJS.raw_snoc]
      exact (cached_fibre d N hh Q F).closed _ e IH.1
    · exact all_captures_step d C hh G F N x0 w IH.1 IH.2 digit e NC

/-- The root successful D authenticates both bits of EVERY header
    occurrence, and therefore all six bits. -/
theorem successful_root_all_captures (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (A : FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x0 w)
    (Tag : (tok d C (rawRun x0 w) 0).tag=3)
    (ND : (tok d C (rawRun x0 w) 0).outcome≠1) :
    ∀ i,i<C.L→h (out C i)=true→
      CapturedAt d C x0 w i (tok d C (rawRun x0 w) 0).payload := by
  obtain ⟨_,H⟩ := all_captures_run d C hh G F N x0 X A digit w T
  rcases H with ⟨k,q,R,_⟩|⟨k,q,R,W⟩
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
    have ND0 : (acqFlightD (params d s) q).outcome≠1 := by rwa [←R.packet]
    intro i I H
    have P := acqFlight_reply_pair (params d s) q R.bound ND0 (C.route.port i)
    rw [R.packet]
    exact capture_relabel d C x0 w i q _ (W P.1 i I H) P.2

/-- Positive nonrestart suffix: all grants actually held at its
    start are retained at every prefix. In particular no own release
    can occur. It is not a promise about a later reset or new file. -/
theorem postacq_held_along (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (A : StrongSerial d C x)
    (PC : PostAcqPC (params d s) (readPC d C x))
    (w : List (Fin n)) (NR : NoRestartTape d C x w)
    (i : Nat) (I : i<C.L) (H : h (out C i)=true)
    (Compat : Compatible (rawGrant d x (out C i)))
    (Held : rawGrant d x (out C i) (C.route.port i)=true) :
    HeldAlong d (out C i) (C.route.port i) x w := by
  induction w generalizing x with
  | nil => exact Held
  | cons e w IH =>
    have NZ : (readPC d C x).2≠0 := by
      have K := PC.2.1
      unfold cmpOp at K
      omega
    obtain ⟨Y,PC',_⟩ := raw_postacq_six_step d C hh F N x X e PC digit NR.1
    exact ⟨Held,IH (rawNext s x e) Y
      (strong_step d C N hh G F x X A digit e) PC' NR.2
      (raw_compatible_step d x e _ (edge_sep N e) Compat)
      (held_incidence_step d C N x e ((cached_fibre d N hh Q F).mask x X)
        A NZ i I H Compat Held)⟩

/-- The file bits at any actual positive endpoint of this very
    successful ACQ. The same flight has real old wins, exact source
    writeback, and held grants through the actual consume and suffix. -/
theorem all_captures_after_consume (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (P : readPC d C x=(1,acqOp (params d s)))
    (Compat : ∀ i,h i=true→Compatible (rawGrant d x i))
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C (rawNext s x (door C)) w)
    (Tag : (tok d C (rawRun (rawNext s x (door C)) w) 0).tag=3)
    (ND : (tok d C (rawRun (rawNext s x (door C)) w) 0).outcome≠1)
    (v : List (Fin n))
    (NR : NoRestartTape d C (rawNext s (rawRun (rawNext s x (door C)) w) (door C)) v) :
    let x0 := rawNext s x (door C)
    let old := rawRun x0 w
    let after := rawNext s old (door C)
    let z := rawRun after v
    Cached d hh Q z ∧ PostAcqPC (params d s) (readPC d C z) ∧
    ownerCaptureSix d C z=(tok d C old 0).payload%64 ∧
    ∀ i,i<C.L→h (out C i)=true→
      CapturedAt d C x0 w i (ownerCaptureSix d C z) ∧
      HeldAlong d (out C i) (C.route.port i) after v := by
  dsimp only
  let x0 := rawNext s x (door C)
  let old := rawRun x0 w
  let after := rawNext s old (door C)
  let z := rawRun after v
  obtain ⟨X0,F0⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N x X I P
  obtain ⟨Y,R,O,K,L,_⟩ := from_genuine_issue d C hh G F N x X I P digit w T Tag ND
  have A := raw_acq_consume_six d C hh G F N old Y R O K L ND digit
  have B := acq_consume_then_run_six d C hh G F N old Y R O K L ND digit v NR
  have PC : PostAcqPC (params d s) (readPC d C after) := by
    rw [A.2.2.1]
    exact ⟨.inl rfl,Nat.le_refl _,by unfold cmpOp commitOp; omega⟩
  have Rail := seed_after_acq d C after A.2.1 A.2.2.1
  refine ⟨B.1,B.2.1,B.2.2,?_⟩
  intro i K0 H
  have Capture := successful_root_all_captures d C hh G F N x0 X0 F0 digit w T Tag ND i K0 H
  have C0 := raw_compatible_step d x (door C) (out C i)
    (edge_sep N _) (Compat (out C i) H)
  have C1 := raw_compatible_step d old (door C) (out C i) (edge_sep N _)
    (ReportAcquireWinHold.compatible_run d N x0 (out C i) C0 w)
  have Held := (ReportAcquireWinHold.successful_acq_grants_through_consume
    d C hh G F N x0 X0 F0 digit w T Tag ND i K0 H C0).2
  exact ⟨capture_relabel d C x0 w i _ _ Capture
    (by rw [B.2.2]; exact acq_pair_mod _ _),
    postacq_held_along d C hh G F N digit after A.1 Rail PC v NR i K0 H C1 Held⟩

/-- The two *literal source subfields*, separately, match the
    historical winning sample. Apply to each lane by header_lane_geometry. -/
theorem captured_file_fields (d : Sheet) (C : Chart h) (x0 z : Raw s n)
    (w : List (Fin n)) (i : Nat)
    (A : CapturedAt d C x0 w i (ownerCaptureSix d C z)) :
    ∃ pre post : List (Fin n), ∃ r : Nat,
      w=pre++(out C i::post) ∧
      let old := rawRun x0 pre
      let p := params d s
      let u := selectBytes d (old (out C i))
      let v := selectBytes d (z C.root)
      FState d C old i r ∧
      acqFlightWin p true u (C.route.port i)=true ∧
      rawGrant d (rawNext s old (out C i)) (out C i) (C.route.port i)=true ∧
      acqCaptureIndex p v/2^(2-(C.route.port i).val)%2=publicationSelector p u ∧
      acqCaptureHeader p v/2^(2-(C.route.port i).val)%2=
        (publicationA p u (publicationSelector p u)).toNat := by
  obtain ⟨pre,post,r,E,F,W,H,B⟩ := A
  change acqPair (acqCaptureSix (params d s) (selectBytes d (z C.root))) _=_ at B
  rw [acq_pair_fields] at B
  exact ⟨pre,post,r,E,F,W,H,congrArg Prod.fst B,congrArg Prod.snd B⟩

#print axioms header_lane_geometry
#print axioms successful_root_all_captures
#print axioms all_captures_after_consume
#print axioms captured_file_fields
end L4.ReportAcquireAllCaptures

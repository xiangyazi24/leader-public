import Leader.L4.ShortMISPublicationFlight
import Leader.L4.ShortMISFlightGeometry
import Leader.L4.ShortWriteFileSplice

namespace L4.ShortMISFencedWord
open AllSizeProtocol PhysicalCustody MISByteCodec
open ShortResetChart hiding lane
open ShortResetCycle ShortResetMIS1Ring ShortResetForwardH2 ShortResetFlow
open ShortResetRow ShortReadResult ShortWritePacketCodec ShortWriteCentreWitness
open ShortMISEngine ShortMISSheetParked ShortMISPublicationLift
open ShortMISPublicationHistoryLocal ShortMISPublicationFlight
open ShortMISLift (Geometry)
open ReportStaticSpacing (Lower)
open ShortFiveWinningWord ShortFiveWordEntry
open ShortFiveGuardTour (Layout centre ingress Safe Writer tourPrefix)
open ShortReadCaptureBits (bitAt)
open ShortReadForward (Forward hopPacket replyPacket)
open ShortClearLaunch (ClearIssue)
open ShortOwnerEpochJS (door)
open ShortReadCaptureTrace (Ledger Sample)

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
noncomputable section

variable {s n : Nat} {h : Fin n → Bool}

private theorem raw_app (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (rawNext s x e)

private theorem raw_snoc' (x : Raw s n) (u : List (Fin n)) (e : Fin n) :
    rawRun x (u++[e])=rawNext s (rawRun x u) e :=
  raw_app x u [e]

private theorem large9 (G : Geometry s n) (A : 2≤G.A) : 9<n := by
  obtain ⟨r,H⟩ := G.P.hh
  have B := G.width_spec (⟨r,H⟩ : Lower G.P.h)
  have S := G.seven
  omega

-- CHECK: ShortFiveWordEntry.lean:122–177; ShortFiveWinningWord.lean:13–26.
private theorem tour_body (C : Chart h) :
    tour C = door C :: (helloBody C ++ [door C]) := by
  simp [tour,helloBody,door,List.append_assoc]

private theorem admit_body (C : Chart h) (g : Nat) :
    admit C g = door C :: (admitBody C g ++ [door C]) := by
  simp [admit,admitBody,door,List.append_assoc]

/- A. The literal HELLO and ADMIT launch/consume. -/

-- CHECK: ShortHelloFlight.lean:15; ShortHelloForward.BeforeTurn/Wait1;
-- ShortHelloReverseChart.Returning/Wait1/Rev; identical byte congruence.
private theorem hello_congr (C : Chart h) (u v : Raw s n)
    (B : ∀ q,(u q).mis1=(v q).mis1) (st : Stage) :
    ShortHelloFlight.Flight C u st ↔ ShortHelloFlight.Flight C v st := by
  cases st <;>
    simp only [ShortHelloFlight.Flight,ShortHelloForward.NoGrants,
      ShortHelloForward.BeforeTurn,ShortHelloForward.Wait1,
      ShortHelloForward.ClearSuffix,ShortHelloReverseChart.Returning,
      ShortHelloReverseChart.Wait1,ShortHelloReverseChart.Rev,
      ClearIssue,ShortEmptyOwnership.Clear,TrailPrefix,bits,B]

-- CHECK: ShortAdmitFlight.lean:29; ShortAdmitFlightSync.lean:54–64.
private theorem admit_congr (C : Chart h) (u v : Raw s n)
    (B : ∀ q,(u q).mis1=(v q).mis1) (g : Nat)
    (st : ShortAdmitFlight.State) :
    ShortAdmitFlight.Flight C u g st ↔
      ShortAdmitFlight.Flight C v g st := by
  cases st <;>
    simp only [ShortAdmitFlight.Flight,ShortHelloForward.NoGrants,
      ShortAdmitFlightSync.Fwd,ShortAdmitFlightSync.Rev,
      ShortAdmitFlightSync.Wait2,ClearIssue,ShortEmptyOwnership.Clear,bits,B]

private theorem hello_absorb (C : Chart h) (v : List (Fin n)) :
    HScan C v .done=.done := by
  induction v with
  | nil => rfl
  | cons e v ih => exact ih

private theorem admit_absorb (C : Chart h) (g : Nat) (v : List (Fin n)) (b : Bool) :
    AScan C g v (.done b)=.done b := by
  induction v with
  | nil => rfl
  | cons e v ih => exact ih

private theorem hello_run_last (P : Params s n) (C : Chart P.h)
    (v : List (Fin n)) (x : Raw s n) (X : Cached P x)
    (st : Stage) (F : ShortHelloFlight.Flight C (view P x) st)
    (H : ShortHelloFlight.Live (HScan C v st)) :
    ShortHelloFlight.Flight C (view P (rawRun x (v++[door C])))
      (nextStage C (door C) (HScan C v st)) := by
  induction v generalizing x st with
  | nil =>
    exact (hello_congr C _ _ (view_next P x X (door C)) _).mp
      (ShortHelloFlight.active_step C (view P x) (view_header P x) (door C) st H F)
  | cons e v ih =>
    have L : ShortHelloFlight.Live st := by
      cases st with
      | fwd => trivial
      | rev => trivial
      | done =>
        change ShortHelloFlight.Live (HScan C (e::v) .done) at H
        rw [hello_absorb] at H
        exact H
    have Q := (hello_congr C _ (view P (rawNext s x e)) (view_next P x X e) _).mp
      (ShortHelloFlight.active_step C (view P x) (view_header P x) e st L F)
    exact ih (rawNext s x e) (P.cached_closed x e X) _ Q H

private theorem admit_run_last (P : Params s n) (C : Chart P.h)
    (v : List (Fin n)) (x : Raw s n) (X : Cached P x)
    (st : ShortAdmitFlight.State)
    (F : ShortAdmitFlight.Flight C (view P x) C.a st)
    (H : ShortAdmitFlight.Live (AScan C C.a v st)) :
    ShortAdmitFlight.Flight C (view P (rawRun x (v++[door C]))) C.a
      (ShortAdmitFlight.next C C.a (door C) (AScan C C.a v st)) := by
  have room := P.chart_gate C
  have step (y : Raw s n) (Y : Cached P y) (e : Fin n)
      (q : ShortAdmitFlight.State) (L : ShortAdmitFlight.Live q)
      (Q : ShortAdmitFlight.Flight C (view P y) C.a q) :
      ShortAdmitFlight.Flight C (view P (rawNext s y e)) C.a
        (ShortAdmitFlight.next C C.a e q) := by
    have gate : ∀ j,j<C.L →
        (ShortAdmitForward.gated C (view P y) j=true ↔ j=C.a) := by
      intro j J
      simpa only [ShortAdmitForward.gated,view_header,view_byte] using
        room.2.2.2 y Y j J
    exact (admit_congr C _ (view P (rawNext s y e)) (view_next P y Y e) C.a _).mp
      (ShortAdmitFlight.active_step ShortAdmitSameGeneration.wire_frames
        C (view P y) (view_header P y) e C.a room.1 room.2.1 gate q L Q)
  induction v generalizing x st with
  | nil => exact step x X (door C) st H F
  | cons e v ih =>
    have L : ShortAdmitFlight.Live st := by
      cases st with
      | forward => trivial
      | reverse => trivial
      | done b =>
        rw [admit_absorb] at H
        exact H
    exact ih (rawNext s x e) (P.cached_closed x e X) _
      (step x X e st L F) H

theorem winning_entry_actual (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x) (A : ShortMISLift.Parked P C x) :
    let y := rawRun x (tour C ++ admit C C.a)
    ShortHelloForward.NoGrants C.route (view P y) ∧
      ClearIssue C (view P y) 3 := by
  let e := door C
  let y := rawRun x (tour C)
  have R := P.chart_gate C
  have H0 := (hello_congr C _ (view P (rawNext s x e)) (view_next P x X e) _).mp
    (ShortHelloFlight.actual_launch C (view P x) (view_header P x)
      ((parked_view_iff P C x).mp A))
  have H1 := hello_run_last P C (helloBody C) (rawNext s x e)
    (P.cached_closed x e X) (.fwd 0) H0
    (by rw [hello_body_scans]; trivial)
  rw [hello_body_scans] at H1
  have H2 : ShortHelloForward.NoGrants C.route (view P y) ∧
      ClearIssue C (view P y) 2 := by
    change ShortHelloForward.NoGrants C.route (view P (rawRun x (tour C))) ∧
      ClearIssue C (view P (rawRun x (tour C))) 2
    rw [tour_body]
    simp [e,door,nextStage,RearTrace.right_predecessor, ShortHelloFlight.Flight] at H1
    exact H1
  have Y := cached_run_on P x X (tour C)
  have A0 := (admit_congr C _ (view P (rawNext s y e)) (view_next P y Y e) C.a _).mp
    (ShortAdmitFlight.launch C (view P y) (view_header P y) C.a R.1 H2.2 H2.1)
  have A1 := admit_run_last P C (admitBody C C.a) (rawNext s y e)
    (P.cached_closed y e Y) (.forward 0 false 0) A0
    (by rw [admit_body_scans C C.a R.1 R.2.1]; trivial)
  rw [admit_body_scans C C.a R.1 R.2.1] at A1
  dsimp only
  rw [raw_app,admit_body]
  simp [y,e,door,ShortAdmitFlight.next,RearTrace.right_predecessor,
    ShortAdmitFlight.Flight] at A1
  exact A1

/- B. Header-lane ownership in the actual five charts. -/

private def atHeader (C : Chart h) (j : Fin 3) : Nat :=
  if j=0 then 0 else if j=1 then C.a else C.a+C.b

private theorem rootAt_add (G : Geometry s n) (r : Lower G.P.h) (u v : Nat) :
    G.rootAt (G.rootAt r u) v=G.rootAt r (u+v) := by
  induction v with
  | zero => simp [Geometry.rootAt]
  | succ v ih =>
    simp only [Geometry.rootAt,ih]
    rfl

-- CHECK: ShortMISLift.lean:127–159, Geometry.chart is literally chart_of_three.
private theorem three (j : Fin 3) : j=0 ∨ j=1 ∨ j=2 := by
  have h := j.isLt
  rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with H|H|H
  · exact .inl (Fin.ext H)
  · exact .inr (.inl (Fin.ext H))
  · exact .inr (.inr (Fin.ext H))

private theorem family_site (G : Geometry s n) (i : Lower G.P.h)
    (m : Fin 5) (j : Fin 3) :
    nextAt (G.family i m).root (atHeader (G.family i m) j) =
      (G.rootAt (G.start i) (m.val+j.val)).val := by
  let r := G.rootAt (G.start i) m.val
  have E : atHeader (G.family i m) j=G.coord r j.val := by
    rcases three j with rfl|rfl|rfl <;> simp [atHeader,Geometry.coord,Geometry.family,Geometry.chart,ShortLayerGeometry.chart_of_three,Geometry.rootAt,r]
  rw [E,←rootAt_add G (G.start i) m.val j.val,G.root_coord]
  rfl

private theorem selected_lane (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (j : Fin 3) :
    atHeader C j<C.L ∧ C.route.port (atHeader C j)=j ∧
      G.P.h (nextAt C.root (atHeader C j))=true := by
  obtain ⟨a,b,c,aa,bb,cc,ca,cb,L,H⟩ := ShortMISFlightGeometry.coordinates G C
  have ap : 0<a := by omega
  have bp : 0<b := by omega
  have cp : 0<c := by omega
  have K : atHeader C j<C.L := by
    rcases three j with rfl|rfl|rfl <;> simp [atHeader,ca,cb,L] <;> omega
  refine ⟨K,?_,(H _ K).mpr ?_⟩
  · rcases three j with rfl|rfl|rfl <;>
      simp [atHeader,Chart.route,ShortResetChart.lane,ca,cb,
        show 0<a by omega,show a<a+b by omega]
  · rcases three j with rfl|rfl|rfl <;> simp [atHeader,ca,cb]

private theorem header_coordinate (G : Geometry s n) (C : Chart G.P.h)
    (k : Nat) (K : k<C.L) (H : G.P.h (nextAt C.root k)=true) :
    ∃ j : Fin 3,k=atHeader C j := by
  obtain ⟨a,b,c,aa,bb,cc,ca,cb,L,Q⟩ := ShortMISFlightGeometry.coordinates G C
  rcases (Q k K).mp H with Z|Z|Z
  · exact ⟨0,by simpa [atHeader] using Z⟩
  · exact ⟨1,by simpa [atHeader,ca] using Z⟩
  · exact ⟨2,by simpa [atHeader,ca,cb] using Z⟩

theorem rival_header_actual (G : Geometry s n) (A : 2≤G.A) (i : Lower G.P.h)
    (x : Raw s n) (X : Cached G.P x) (P : ShortMISLift.FiveParked G.P (G.family i) x)
    (w : List (Fin n)) (W : ∀ e∈w,e∈ShortResetWatch.watch (G.family i 2))
    (j k : Fin 3) (K : k≠j) :
    let C := G.family i 2
    let e := nextAt C.root (atHeader C j)
    let y := rawRun x w
    (headerGrantView (G.P.byte y e)).ask k=false ∧
      (G.P.byte y e).getLsbD (91-k.val)=false := by
  let m : Fin 5 := ⟨2+j.val-k.val,by have := j.isLt; omega⟩
  have M : m≠2 := by
    intro E
    have Q := congrArg Fin.val E
    apply K
    apply Fin.ext
    change 2+j.val-k.val=2 at Q
    have := k.isLt
    omega
  let D := G.family i m
  let C := G.family i 2
  have U := selected_lane G A D k
  have Eq : nextAt D.root (atHeader D k)=nextAt C.root (atHeader C j) := by
    rw [family_site G i m k,family_site G i 2 j]
    have E : m.val+k.val=2+j.val := by
      dsimp [m]
      have := k.isLt
      omega
    rw [E]
    rfl
  have F := actual_rivals_fenced G i x X P w W m M
  have a := F.1 (atHeader D k) U.1 U.2.2
  have b := F.2 (atHeader D k) U.1 U.2.2
  change (headerGrantView (G.P.byte (rawRun x w) (nextAt D.root (atHeader D k)))).ask
    (D.route.port (atHeader D k))=false at a
  change (G.P.byte (rawRun x w) (nextAt D.root (atHeader D k))).getLsbD
    (91-(D.route.port (atHeader D k)).val)=false at b
  rw [Eq,U.2.1] at a b
  exact ⟨a,b⟩

private def fwd (C : Chart h) (k : Nat) : List (Fin n) :=
  (List.range k).map (nextAt C.root)

private theorem fwd_succ (C : Chart h) (k : Nat) :
    fwd C (k+1)=fwd C k++[nextAt C.root k] := by
  simp [fwd,List.range_succ]

private theorem not_departed (C : Chart h) (k : Nat) (K : k<C.L) :
    nextAt C.root k ∉ door C :: fwd C k := by
  intro E
  have L := C.length_lt
  rcases List.mem_cons.mp E with E|E
  · have H : nextAt C.root (k+1)=nextAt C.root 0 :=
      (congrArg rightNeighbor E).trans (RearTrace.right_predecessor _)
    have Q := nextAt_injective_under C.root _ _ (by omega) (by omega) H
    omega
  · obtain ⟨j,J,E⟩ := List.mem_map.mp E
    have B := List.mem_range.mp J
    have Q := nextAt_injective_under C.root _ _ (by omega) (by omega) E
    omega

private theorem own_absent (P : Params s n) (x : Raw s n) (X : Cached P x)
    (e : Fin n) (H : P.h e=true) (j : Fin 3)
    (E : (P.byte x e).getLsbD (91-j.val)=false)
    (w : List (Fin n)) (W : e∉w) :
    (P.byte (rawRun x w) e).getLsbD (91-j.val)=false := by
  induction w generalizing x with
  | nil => exact E
  | cons q w ih =>
    have B := ShortGrantPersistence.absent_until_ask (view P x) q e j
      (P.sep q) ((view_header P x e).trans H) E
      (fun Q => False.elim (W (by simp [Q])))
    rw [view_next P x X q e] at B
    exact ih (rawNext s x q) (P.cached_closed x q X) B
      (fun T => W (List.mem_cons_of_mem _ T))

private theorem read_prefix_watch (C : Chart h) (room : C.a+1<C.L) (k : Nat) (K : k≤C.L) :
    ∀ e∈((tour C++admit C C.a)++(door C::fwd C k)),
      e∈ShortResetWatch.watch C := by
  intro e H
  rcases List.mem_append.mp H with H|H
  · rcases List.mem_append.mp H with H|H
    · exact tour_watch C e H
    · exact admit_watch C C.a room e H
  · rcases List.mem_cons.mp H with H|H
    · subst e
      refine (ShortResetWatch.mem_watch C _).2 (.inl ?_)
      have Q := congrArg RearTrace.predecessor (PhysicalCustody.H1.incoming_spec C.root)
      rwa [RearTrace.predecessor_right,eq_comm] at Q
    · obtain ⟨j,J,rfl⟩ := List.mem_map.mp H
      exact (ShortResetWatch.mem_watch C _).2
        (.inr ⟨j,by have := List.mem_range.mp J; omega,rfl⟩)

private theorem canonical_front (C : Chart h) (v : Raw s n) (k p : Nat)
    (A : Forward C.route v k p) :
    oldK (header v (nextAt C.root k)) (v (nextAt C.root k)).mis1
      (C.route.port k)=readFront p :=
  slot_of_bits C.route v k _ (fun z=>ShortReadForward.decode_front z p A.2.1)
    A.2.2.2.2.1

/-- Actual allocator success at every designated selected departure.
The old own grant is absent by first-departure, not by a global
grant-free assertion after READ has already started. -/
theorem read_mark_wins_actual (G : Geometry s n) (A : 2≤G.A) (i : Lower G.P.h)
    (x : Raw s n) (X : Cached G.P x) (P : ShortMISLift.FiveParked G.P (G.family i) x)
    (k p : Nat)
    (F : let C := G.family i 2
      let y := rawRun x ((tour C++admit C C.a)++(door C::fwd C k))
      Forward C.route (view G.P y) k p) :
    let C := G.family i 2
    let e := nextAt C.root k
    let y := rawRun x ((tour C++admit C C.a)++(door C::fwd C k))
    G.P.h e=true →
      readWins (G.P.h e) (G.P.h (rightNeighbor e))
        (G.P.byte y e) (G.P.byte y (rightNeighbor e)) (C.route.port k)=true := by
  let C := G.family i 2
  let u := tour C++admit C C.a
  let t := door C::fwd C k
  let z := rawRun x u
  let y := rawRun x (u++t)
  let e := nextAt C.root k
  change G.P.h e=true → _
  intro H
  have K : k<C.L := F.1
  obtain ⟨j,J⟩ := header_coordinate G C k K H
  have port : C.route.port k=j := by rw [J]; exact (selected_lane G A C j).2.1
  have Ab := (winning_entry_actual G.P C x X (P 2)).1 k K H
  have E : (G.P.byte z e).getLsbD (91-j.val)=false := by
    change (G.P.byte z e).getLsbD (91-(C.route.port k).val)=false at Ab
    rwa [port] at Ab
  have O := own_absent G.P z (cached_run_on G.P x X u) e H j E t
    (not_departed C k K)
  have O' : (G.P.byte y e).getLsbD (91-j.val)=false := by
    simpa only [y,raw_app] using O
  have head : header (view G.P y) e=true := (view_header G.P y e).trans H
  have wire := canonical_front C (view G.P y) k p F
  rw [head,port] at wire
  have rival (l : Fin 3) (L : l≠j) :
      (headerGrantView (G.P.byte y e)).ask l=false ∧
      (G.P.byte y e).getLsbD (91-l.val)=false := by
    have R := rival_header_actual G A i x X P (u++t)
      (read_prefix_watch C (G.P.chart_gate C).2.1 k (by omega)) j l L
    simpa only [C,u,t,y,e,←J] using R
  have W := ShortFiveReadWin.read_wins_no_rival (view G.P y) e j p head wire
    (fun l => by
      by_cases L : l=j
      · simpa only [L,view_byte] using O'
      · exact (rival l L).2)
    (fun l L => (rival l L).1)
  change readWins (G.P.h e) (G.P.h (rightNeighbor e)) (G.P.byte y e) (G.P.byte y (rightNeighbor e)) (C.route.port k)=true
  rw [port]
  simpa only [view_header,view_byte] using W

/- C. Positive READ from the actual tape. No success hypothesis. -/

private theorem trace_app (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (f : ShortReadFlight.Flight) (u v : List (Fin n)) :
    readTrace P C x f (u++v)=
      readTrace P C (rawRun x u) (readTrace P C x f u) v := by
  induction u generalizing x f with
  | nil => rfl
  | cons e u ih => exact ih (rawNext s x e) (readNext P C x e f)

private theorem read_absorb (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (b : Bool) (p : Fin 64) (w : List (Fin n)) :
    readTrace P C x (.consumed b p) w=.consumed b p := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (rawNext s x e)

private theorem before_last (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (f : ShortReadFlight.Flight) (v : List (Fin n)) (e : Fin n)
    (H : ShortReadFlight.live (readTrace P C x f v)) :
    beforeRead P C x f (v++[e]) := by
  induction v generalizing x f with
  | nil => exact ⟨H,trivial⟩
  | cons q v ih =>
    have L : ShortReadFlight.live f := by
      cases f with
      | forward => trivial
      | returning => trivial
      | consumed b p =>
        rw [read_absorb] at H
        exact H
    exact ⟨L,ih _ _ H⟩

private theorem before_prefix (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (f : ShortReadFlight.Flight) (u v : List (Fin n))
    (H : beforeRead P C x f (u++v)) : beforeRead P C x f u := by
  induction u generalizing x f with
  | nil => trivial
  | cons e u ih => exact ⟨H.1,ih _ _ H.2⟩

private theorem read_active_run (P : Params s n) (C : Chart P.h) (w : List (Fin n))
    (x : Raw s n) (X : Cached P x) (f : ShortReadFlight.Flight)
    (A : ReadActive P C x f) (B : beforeRead P C x f w) :
    ReadActive P C (rawRun x w) (readTrace P C x f w) := by
  induction w generalizing x f with
  | nil => exact A
  | cons e w ih =>
    exact ih (rawNext s x e) (P.cached_closed x e X) (readNext P C x e f)
      (read_step P C x X e f B.1 A) B.2

private theorem read_init (P : Params s n) (C : Chart P.h) (z : Raw s n)
    (Z : Cached P z) (I : ClearIssue C (view P z) 3) :
    ReadActive P C (rawNext s z (door C)) (.forward 0 64) :=
  (read_active_congr C _ _ (view_next P z Z (door C)) _).mp
    (ShortReadForward.forward_from_actual_issue3 C (view P z) (view_header P z) I)

private theorem back_sweep (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (k : Nat) (b : Bool) (p : Fin 64) :
    readTrace P C x (.returning k b p)
      ((List.range k).reverse.map (nextAt C.root))=.returning 0 b p := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ,List.reverse_append,List.map_append]
    simpa [readTrace,readNext,ShortReadFlight.next,nextStage] using
      ih (rawNext s x (nextAt C.root k))

theorem successful_read_actual (G : Geometry s n) (A : 2≤G.A) (i : Lower G.P.h)
    (x : Raw s n) (X : Cached G.P x) (P : ShortMISLift.FiveParked G.P (G.family i) x) :
    let C := G.family i 2
    let z := rawRun x (tour C++admit C C.a)
    let start := rawNext s z (door C)
    let w := helloBody C++[door C]
    beforeRead G.P C start (.forward 0 64) w ∧
      ∃ out : Fin 64, readTrace G.P C start (.forward 0 64) w=.consumed true out ∧
        ClearIssue C (view G.P (rawRun z (door C::w))) 4 := by
  dsimp only
  let C := G.family i 2
  let u := tour C++admit C C.a
  let z := rawRun x u
  let start := rawNext s z (door C)
  have Z := cached_run_on G.P x X u
  have S := G.P.cached_closed z (door C) Z
  have I := (winning_entry_actual G.P C x X (P 2)).2
  have init := read_init G.P C z Z I
  have phase (k : Nat) (K : k<C.L) :
      ∃ p, readTrace G.P C start (.forward 0 64) (fwd C k)=.forward k p ∧
        ReadActive G.P C (rawRun start (fwd C k)) (.forward k p) ∧ bitAt p 6=true := by
    induction k with
    | zero => exact ⟨64,rfl,init,by decide⟩
    | succ k ih =>
      obtain ⟨p,T,F,B⟩ := ih (by omega)
      let y := rawRun start (fwd C k)
      let v := view G.P y
      let e := nextAt C.root k
      let j := C.route.port k
      let q := hopPacket v e j (C.route.port (k+1))
      have Y := cached_run_on G.P start S (fwd C k)
      have state : y=rawRun x (u++(door C::fwd C k)) :=
        (raw_app x u (door C::fwd C k)).symm
      have win (H : header v e=true) :
          ShortReadCaptureBits.wins v e j=true := by
        have H' : G.P.h e=true := (view_header G.P y e).symm.trans H
        have Q := read_mark_wins_actual G A i x X P k p
          (by dsimp only; rw [←state]; exact F) H'
        simp only [ShortReadCaptureBits.wins,v,view_header,view_byte,H',Bool.true_and]
        change readWins (G.P.h e) (G.P.h (rightNeighbor e))
          (G.P.byte (rawRun x (u++(door C::fwd C k))) e)
          (G.P.byte (rawRun x (u++(door C::fwd C k))) (rightNeighbor e)) j=true at Q
        simpa only [←state,H'] using Q
      have O := canonical_front C v k p F
      have sticky := (ShortReadCaptureBits.hop_bits v e j (C.route.port (k+1)) p F.2.1 O).1
      have good : bitAt q.payload 6=true := by
        change bitAt (hopPacket v e j (C.route.port (k+1))).payload 6=true
        rw [sticky,B]
        cases H : header v e
        · rfl
        · rw [win H]; rfl
      have step := read_step G.P C y Y e (.forward k p) trivial F
      have next : readNext G.P C y e (.forward k p)=.forward (k+1) q.payload := by
        simp [readNext,ShortReadFlight.next,e,K,q,j,v]
      refine ⟨q.payload,?_,?_,good⟩
      · rw [fwd_succ,trace_app,T]
        exact next
      · rw [fwd_succ,raw_snoc']
        rw [next] at step
        exact step
  let k := C.L-1
  have K : k<C.L := by have := C.positive; dsimp [k]; omega
  obtain ⟨p,T,F,B⟩ := phase k K
  let y := rawRun start (fwd C k)
  let v := view G.P y
  let e := nextAt C.root k
  let j := C.route.port k
  let q := replyPacket v e j
  have state : y=rawRun x (u++(door C::fwd C k)) :=
    (raw_app x u (door C::fwd C k)).symm
  have win (H : header v e=true) : ShortReadCaptureBits.wins v e j=true := by
    have H' : G.P.h e=true := (view_header G.P y e).symm.trans H
    have Q := read_mark_wins_actual G A i x X P k p
      (by dsimp only; rw [←state]; exact F) H'
    simp only [ShortReadCaptureBits.wins,v,view_header,view_byte,H',Bool.true_and]
    change readWins (G.P.h e) (G.P.h (rightNeighbor e))
      (G.P.byte (rawRun x (u++(door C::fwd C k))) e)
      (G.P.byte (rawRun x (u++(door C::fwd C k))) (rightNeighbor e)) j=true at Q
    simpa only [←state,H'] using Q
  -- terminal_bits is stronger than the old MIS1 terminal-nonheader
  -- calculation. It uses the very same successful capture if needed.
  have sticky := (ShortReadCaptureBits.terminal_bits v e j p F.2.1
    (canonical_front C v k p F)).1
  have ok : (q.outcome==0)=true := by
    change ((replyPacket v e j).outcome == 0)=true
    rw [sticky,B]
    cases H : header v e
    · rfl
    · rw [win H]; rfl
  have E : C.L=k+1 := by have := C.positive; dsimp [k]; omega
  have Full : readTrace G.P C start (.forward 0 64) (fwd C C.L)=
      .returning k true (ShortReadFlight.datum q) := by
    have W : fwd C C.L=fwd C k++[e] := by rw [E,fwd_succ]
    rw [W,trace_app,T]
    change readNext G.P C y e (.forward k p)=_
    simp [readNext,ShortReadFlight.next,e,show ¬k+1<C.L by omega,q,j,v,ok]
  have Body : readTrace G.P C start (.forward 0 64) (helloBody C)=
      .returning 0 true (ShortReadFlight.datum q) := by
    change readTrace G.P C start (.forward 0 64)
      (fwd C C.L++(List.range k).reverse.map (nextAt C.root))=_
    rw [trace_app,Full,back_sweep]
  have Before := before_last G.P C start (.forward 0 64) (helloBody C) (door C)
    (by rw [Body]; trivial)
  have Done : readTrace G.P C start (.forward 0 64) (helloBody C++[door C])=
      .consumed true (ShortReadFlight.datum q) := by
    rw [trace_app,Body]
    simp [readTrace,readNext,ShortReadFlight.next,nextStage,door,RearTrace.right_predecessor]
  let pre := rawRun start (helloBody C)
  have RA := read_active_run G.P C (helloBody C) start S (.forward 0 64) init
    (before_prefix G.P C start _ _ [door C] Before)
  rw [Body] at RA
  have RR : ShortReadReverseChart.Returning C (view G.P pre) 0 true (ShortReadFlight.datum q) := RA
  have Wire := RR.2.2 0 C.positive
  change (kField (ShortResetChart.lane C.a C.b 0)).read (G.P.byte pre C.root)=
    encode (ShortReadReverseChart.trailAt true (ShortReadFlight.datum q) 0 0) at Wire
  rw [C.rootPort] at Wire
  simp only [ShortReadReverseChart.trailAt,Nat.lt_irrefl,if_false,if_true] at Wire
  have dR : rightNeighbor (door C)=C.root := RearTrace.right_predecessor _
  have Head : header (view G.P pre) C.root=true :=
    (view_header G.P pre C.root).trans C.rootHeader
  have PC := ShortReadReturnPC.consume_pc (view G.P pre) (door C) (G.P.sep (door C))
    (dR.symm ▸ Head) (dR.symm ▸ RR.2.1) true (ShortReadFlight.datum q) (dR.symm ▸ Wire)
  rw [dR,view_next G.P pre (cached_run_on G.P start S (helloBody C)) (door C) C.root] at PC
  have Ac := read_active_run G.P C (helloBody C++[door C]) start S _ init Before
  rw [Done] at Ac
  have endEq : rawRun z (door C::(helloBody C++[door C]))=rawNext s pre (door C) :=
    raw_snoc' start (helloBody C) (door C)
  refine ⟨Before,ShortReadFlight.datum q,Done,?_⟩
  rw [endEq]
  apply ShortPreReadGrants.clear_issue_of_pc C _ 4 (by decide)
  · -- CHECK: ShortReadReverseChart.lean:313 Consumed, first projection.
    rw [←endEq]
    exact Ac.1
  · exact PC

/- D. A same-tape writer lease from the checked capture theorem. -/

private def SafeTapeOn (P : Params s n) (C : Chart P.h) :
    Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x,e::w => Safe C (view P x) ∧ SafeTapeOn P C (rawNext s x e) w

private theorem safe_append_on (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (u v : List (Fin n)) :
    SafeTapeOn P C x (u++v) ↔ SafeTapeOn P C x u ∧ SafeTapeOn P C (rawRun x u) v := by
  induction u generalizing x with
  | nil => simp [SafeTapeOn,rawRun,BStarResetSchedule.run]
  | cons e u ih =>
    change (Safe C (view P x) ∧ SafeTapeOn P C (rawNext s x e) (u++v)) ↔
      (Safe C (view P x) ∧ SafeTapeOn P C (rawNext s x e) u) ∧
        SafeTapeOn P C (rawRun (rawNext s x e) u) v
    rw [ih]
    exact and_assoc.symm

private theorem read_safe_tape_on (P : Params s n) (C : Chart P.h) (L : Layout C)
    (x : Raw s n) (X : Cached P x) (f : ShortReadFlight.Flight)
    (A : ReadActive P C x f) (w : List (Fin n)) (B : beforeRead P C x f w) :
    SafeTapeOn P C x w := by
  induction w generalizing x f with
  | nil => trivial
  | cons e w ih =>
    exact ⟨ShortFiveGuardTour.read_safe C L (view P x) f A,
      ih _ (P.cached_closed x e X) _ (read_step P C x X e f B.1 A) B.2⟩

private theorem writer_step_on (P : Params s n) (C : Chart P.h) (L : Layout C)
    (x : Raw s n) (X : Cached P x) (a : Nat)
    (W : Writer C (view P x) a) (e : Fin n) (A : Safe C (view P x)) :
    Writer C (view P (rawNext s x e)) a := by
  let v := view P x
  have H : header v (centre C)=true := (view_header P x _).trans L.selected
  have no : (headerGrantView (v (centre C)).mis1).release 1=false := by
    have V := A.1 C.a (by have := L.room; omega) H
    rwa [L.outPort] at V
  have keep := ShortGrantPersistence.held_until_release v e (centre C) 1
    (P.sep e) H W.1 W.2.1 (fun _=>no)
  have coh := ShortGrantRaw.coherent_next_at v e (centre C) (P.sep e) H W.1
  have sel := ShortFiveGuardTour.selector_hold C L v A e
  -- The only possible responder selector writer is the unique old
  -- own K0 ingress; Safe excludes it. Other owners may run.
  rw [view_next P x X e (centre C)] at keep coh sel
  refine ⟨coh,keep,?_⟩
  rw [ShortSelectorParity.selector_toNat,view_byte,sel,←ShortSelectorParity.selector_toNat]
  exact W.2.2

private theorem writer_run_on (P : Params s n) (C : Chart P.h) (L : Layout C)
    (x : Raw s n) (X : Cached P x) (a : Nat)
    (W : Writer C (view P x) a) (w : List (Fin n)) (A : SafeTapeOn P C x w) :
    Writer C (view P (rawRun x w)) a := by
  induction w generalizing x with
  | nil => exact W
  | cons e w ih =>
    exact ih _ (P.cached_closed x e X) (writer_step_on P C L x X a W e A.1) A.2

theorem read_writer_actual (G : Geometry s n) (A : 2≤G.A)
    (C : Chart G.P.h) (L : Layout C) (z : Raw s n) (Z : Cached G.P z)
    (I : ClearIssue C (view G.P z) 3) (w : List (Fin n)) (out : Fin 64)
    (B : beforeRead G.P C (rawNext s z (door C)) (.forward 0 64) w)
    (R : readTrace G.P C (rawNext s z (door C)) (.forward 0 64) w=.consumed true out) :
    let y := rawRun z (door C::w)
    Writer C (view G.P y) (issuedDescriptor (G.P.byte y C.root)/4) := by
  let P := G.P
  let start := rawNext s z (door C)
  let y := rawRun start w
  let a := captureTrace P C start (.forward 0 64) (fun _=>none) w
  have S := P.cached_closed z (door C) Z
  have Init := read_init P C z Z I
  have Full := read_safe_tape_on P C L start S _ Init w B
  have H := actual_successful_read_file P C z Z I w out B R
  change ShortReadCaptureTrace.Covers C a C.L ∧ _ ∧ _ at H
  have covered := H.1 C.a (by have := L.room; omega) L.selected
  rw [L.outPort] at covered
  have someSample : ∃ p : Sample s n,a 1=some p := by
    cases E : a 1 with
    | none => rw [E] at covered; contradiction
    | some p => exact ⟨p,rfl⟩
  obtain ⟨p,Pp⟩ := someSample
  obtain ⟨lead,tail,k,b,T,O,Tr,Edge,Port,Win⟩ := H.2.2 1 p Pp
  let old := rawRun start lead
  have OldX := cached_run_on P start S lead
  have PreB : beforeRead P C start (.forward 0 64) lead := by
    apply before_prefix P C start _ lead (p.edge::tail)
    rwa [←T]
  have Act := read_active_run P C lead start S _ Init PreB
  change readTrace P C start (.forward 0 64) lead=.forward k b at Tr
  rw [Tr] at Act
  have below : k<C.L := Act.1
  have Hd : header p.old p.edge=true := (Bool.and_eq_true_iff.mp Win).1
  have W : readWins true (header p.old (rightNeighbor p.edge))
      (p.old p.edge).mis1 (p.old (rightNeighbor p.edge)).mis1 1=true := by
    have Q := (Bool.and_eq_true_iff.mp Win).2
    rwa [Hd] at Q
  have Hd' : P.h (nextAt C.root k)=true := by
    rw [←Edge]
    rw [O] at Hd
    exact (view_header P old _).symm.trans Hd
  have geo := (ShortMISFlightGeometry.flight_geometry G C A (view P old) (view_header P old)).1
  have Idx : k=C.a := (geo.2 k below).mp
    ⟨(view_header P old _).trans Hd',Port⟩
  have ec : p.edge=centre C := by simpa [centre,Idx] using Edge
  let sel := get (p.old p.edge).mis1 92 1 (by decide)
  have Capture : Writer C (view P (rawNext s old p.edge)) sel := by
    have coh := ShortGrantRaw.outgoing_coherent_at p.old p.edge Hd
    have gr := ShortReadGrantCapture.capture_winner_has_grant p.old p.edge 1 Hd W
    have same := ShortSelectorChange.selector_initiator_raw p.old p.edge
    change p.old=view P old at O
    rw [O] at coh gr same
    change (rawNext s (view P old) p.edge p.edge).mis1.getLsbD 92=(view P old p.edge).mis1.getLsbD 92 at same
    rw [view_next P old OldX p.edge p.edge] at coh gr same
    unfold Writer
    rw [←ec]
    refine ⟨coh,gr,?_⟩
    rw [ShortSelectorParity.selector_toNat,view_byte,same]
    change ((G.P.byte old p.edge).getLsbD 92).toNat = sel
    rw [←ShortSelectorParity.selector_toNat]
    simp only [sel,O,view_byte]
    rfl
  have Ftail : SafeTapeOn P C (rawNext s old p.edge) tail := by
    rw [T] at Full
    exact ((safe_append_on P C start lead (p.edge::tail)).mp Full).2.2
  have Lease := writer_run_on P C L (rawNext s old p.edge)
    (P.cached_closed old p.edge OldX) sel Capture tail Ftail
  have End : y=rawRun (rawNext s old p.edge) tail := by
    change rawRun start w=_
    rw [T,raw_app]
    rfl
  have File := (H.2.1 1).1
  have Key : issuedDescriptor (P.byte y C.root)/4=sel := by
    rw [ShortFiveGuardTour.descriptor_old_selector]
    have F : (P.byte y C.root).getLsbD 76=(p.old p.edge).mis1.getLsbD 92 := by
      have Q := (file_bit (P.byte y C.root) 4 (by decide)).trans File
      change _ = ShortReadCaptureTrace.select (a 1) at Q
      simpa only [Pp,ShortReadCaptureTrace.select,ShortReadCaptureBits.seenSelector] using Q
    rw [F,←ShortSelectorParity.selector_toNat]
  change Writer C (view P y) (issuedDescriptor (P.byte y C.root)/4)
  rw [Key,End]
  exact Lease

/- E. Joined current-field frames. These are the mask-parametric parts of
ShortFiveGuardTour.bank_step/seal_step, with the unnecessary Geom removed. -/

private theorem bank_step_on (P : Params s n) (C : Chart P.h) (L : Layout C)
    (x : Raw s n) (X : Cached P x) (e : Fin n)
    (A : ShortFiveGuardRow.BankSafe (ShortResetForwardH2.slot C.route (view P x) C.a)) :
    (lane 87 2 (by decide)).read (P.byte (rawNext s x e) (centre C))=
      (lane 87 2 (by decide)).read (P.byte x (centre C)) := by
  let v := view P x
  have head : header v (centre C)=true := (view_header P x _).trans L.selected
  rw [←view_next P x X e (centre C)]
  change (lane 87 2 (by decide)).read (rawNext s v e (centre C)).mis1=_
  by_cases E : centre C=e
  · have O := A
    change ShortFiveGuardRow.BankSafe (oldK (header v (centre C)) (v (centre C)).mis1
      (C.route.port C.a)) at O
    rw [head,L.outPort,E] at O
    rw [E] at head ⊢
    have F := ShortSheetProjection.byte_work_to_raw_field .mis1 v e
      (P.sep e) (lane 87 2 (by decide)) (by decide) (.inl (by decide))
    refine F.1.trans ?_
    change (lane 87 2 (by decide)).read
      ((MISByteRows.row (header v e,header v (rightNeighbor e))
        ((v e).mis1,(v (rightNeighbor e)).mis1)).1.apply (v e).mis1)=_
    rw [head]
    exact ShortFiveGuardRow.banks_left_frame (header v (rightNeighbor e)) _ _ O
  by_cases R : rightNeighbor e=centre C
  · rw [←R] at head ⊢
    exact ShortBankProjection.receiver_banks v e (P.sep e) head
  · rw [reset_remote_frame_raw v e _ E (Ne.symm R)]
    rfl

private theorem seal_step_on (P : Params s n) (C : Chart P.h) (L : Layout C)
    (x : Raw s n) (X : Cached P x) (e : Fin n) (A : Safe C (view P x))
    (S : ShortFiveGuardRow.SealSafe (ShortResetForwardH2.slot C.route (view P x) C.a)) :
    (lane 83 4 (by decide)).read (P.byte (rawNext s x e) (centre C))=
      (lane 83 4 (by decide)).read (P.byte x (centre C)) := by
  let v := view P x
  have head : header v (centre C)=true := (view_header P x _).trans L.selected
  have F := ShortSheetProjection.byte_work_to_raw_field .mis1 v e
    (P.sep e) (lane 83 4 (by decide)) (by decide) (.inl (by decide))
  rw [←view_next P x X e (centre C)]
  change (lane 83 4 (by decide)).read (rawNext s v e (centre C)).mis1=_
  by_cases E : centre C=e
  · have O := S
    change ShortFiveGuardRow.SealSafe (oldK (header v (centre C)) (v (centre C)).mis1
      (C.route.port C.a)) at O
    rw [head,L.outPort,E] at O
    rw [E] at head ⊢
    refine F.1.trans ?_
    change (lane 83 4 (by decide)).read
      ((MISByteRows.row (header v e,header v (rightNeighbor e))
        ((v e).mis1,(v (rightNeighbor e)).mis1)).1.apply (v e).mis1)=_
    rw [head]
    exact ShortFiveGuardRow.seal_left_frame (header v (rightNeighbor e)) _ _ O
  by_cases R : rightNeighbor e=centre C
  · have K := ShortFiveGuardTour.incoming_no_guard C L v A e R
    rw [←R] at head ⊢
    refine F.2.trans ?_
    change (lane 83 4 (by decide)).read
      ((MISByteRows.row (header v e,header v (rightNeighbor e))
        ((v e).mis1,(v (rightNeighbor e)).mis1)).2.apply (v (rightNeighbor e)).mis1)=_
    rw [head]
    exact ShortFiveGuardRow.seal_right_frame (header v e) _ _ K
  · rw [reset_remote_frame_raw v e _ E (Ne.symm R)]
    rfl

private theorem bank_bit_eq (u v : BitVec 96) (j : Nat) (J : j<2)
    (H : (lane 87 2 (by decide)).read v=(lane 87 2 (by decide)).read u) :
    v.getLsbD (88-j)=u.getLsbD (88-j) := by
  have E := congrArg (fun b : BitVec 2=>b.getLsbD (1-j)) H
  simp only [Field.read,BitVec.getLsbD_extractLsb',show 1-j<2 by omega,
    decide_true,Bool.true_and] at E
  change v.getLsbD (87+(1-j))=u.getLsbD (87+(1-j)) at E
  rwa [show 87+(1-j)=88-j by omega] at E

private theorem bank_field_eq (u v : BitVec 96) (d : Fin 8)
    (H : (lane 87 2 (by decide)).read v=(lane 87 2 (by decide)).read u) :
    (Cmd.stage.effectField d).read v=(Cmd.stage.effectField d).read u := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  change i<1 at I
  have Z : i=0 := by omega
  subst i
  simp only [Cmd.effectField,Field.read,BitVec.getLsbD_extractLsb',lane,
    Nat.add_zero,show 0<1 by decide,decide_true,Bool.true_and]
  exact bank_bit_eq u v ((d.val/2)%2) (Nat.mod_lt _ (by decide)) H

private theorem stage_bit (u : BitVec 96) (d : Fin 8)
    (A : (Cmd.stage.effectField d).read u=Cmd.stage.effectBits d) :
    sealBankMatches u d.val=true := by
  have H := congrArg (fun b : BitVec 1=>b.getLsbD 0) A
  simp only [Cmd.effectField,Cmd.effectBits,Field.read,BitVec.getLsbD_extractLsb',lane,
    Nat.add_zero,show 0<1 by decide,decide_true,Bool.true_and] at H
  have Z : (BitVec.ofNat 1 (d.val%2==1).toNat).getLsbD 0=(d.val%2==1) := by
    cases (d.val%2==1) <;> decide
  rw [Z] at H
  unfold sealBankMatches
  exact beq_iff_eq.mpr H

private theorem sealed_descriptor (u : BitVec 96) (d : Fin 8)
    (D : descValid d.val=true)
    (A : (Cmd.seal.effectField d).read u=Cmd.seal.effectBits d) :
    readSeal u=some d.val := by
  have H := congrArg BitVec.toNat A
  change get u 83 4 (by decide)=(BitVec.ofNat 4 (8+d.val)).toNat at H
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := d.isLt; omega)] at H
  have K : (8+d.val)%8=d.val := by have := d.isLt; omega
  simp [readSeal,H,K,D,show 8≤8+d.val by omega]

private theorem clear_centre_tag (C : Chart h) (L : Layout C) (v : Raw s n)
    (I : ShortEmptyOwnership.Clear C v) :
    (ShortResetForwardH2.slot C.route v C.a).tag≠2 := by
  rw [slot_of_bits C.route v C.a E empty_decode (I _ (by have := L.room; omega))]
  decide

/- F. Actual generated write flight, including current effect and file.
No reuse of a fake Generated indexed by header(view P x0). -/

private def wNext (P : Params s n) (C : Chart P.h) (cmd : Cmd) (d : Fin 8)
    (x : Raw s n) (e : Fin n) (f : ShortWriteFlight.Flight) :=
  ShortWriteFlight.next C cmd d (view P x) e f

private inductive WGen (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (cmd : Cmd) (d : Fin 8) : List (Fin n) → ShortWriteFlight.Flight → Prop
  | launch : ClearIssue C (view P x) cmd.op →
      d.val=issuedDescriptor (P.byte x C.root) →
      WGen P C x cmd d [door C] (.front 0 false)
  | snoc {w f} (e : Fin n) :
      WGen P C x cmd d w f → ShortWriteFlight.live f →
      WGen P C x cmd d (w++[e]) (wNext P C cmd d (rawRun x w) e f)

private theorem wgeom (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h) (x : Raw s n) :
    C.a+1<C.L ∧ ∀ k,k<C.L →
      (G.P.h (nextAt C.root k)=true ∧ C.route.port k=1 ↔ k=C.a) := by
  simpa only [view_header] using
    (ShortMISFlightGeometry.flight_geometry G C A (view G.P x) (view_header G.P x)).1

private theorem cgeom (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h) (x : Raw s n) :
    C.a-1+1<C.L ∧ ∀ k,k+1<C.L →
      (G.P.h (rightNeighbor (nextAt C.root k))=true ∧
        C.route.port k=0 ∧ C.route.port (k+1)=1 ↔ k=C.a-1) := by
  simpa only [view_header] using
    (ShortMISFlightGeometry.flight_geometry G C A (view G.P x) (view_header G.P x)).2.1

private theorem write_active_on (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (x : Raw s n) (X : Cached G.P x) (cmd : Cmd) (d : Fin 8)
    (D : descValid d.val=true) (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (R : WGen G.P C x cmd d w f) :
    ShortWriteFlight.Active C cmd d (view G.P (rawRun x w)) f := by
  induction R with
  | launch I E =>
    obtain ⟨b,_,B,F⟩ := ShortWriteFlight.launch C cmd (view G.P x) (view_header G.P x) I
    have Eq : b=d := Fin.ext (B.trans E.symm)
    subst b
    exact (write_active_congr C cmd d _ _ (view_next G.P x X (door C)) _).mp F
  | @snoc w f e R L IH =>
    rw [raw_snoc']
    exact (write_actual_step G.P C (large9 G A) _ (cached_run_on G.P x X w)
      (wgeom G A C x) cmd d D e f L IH).1

private theorem write_writer_on (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (L : Layout C) (x : Raw s n) (X : Cached G.P x) (cmd : Cmd) (d : Fin 8)
    (D : descValid d.val=true) (a : Nat) (W : Writer C (view G.P x) a)
    (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (R : WGen G.P C x cmd d w f) :
    Writer C (view G.P (rawRun x w)) a := by
  induction R with
  | launch I _ =>
    exact writer_step_on G.P C L x X a W (door C)
      (ShortFiveGuardTour.clear_safe C L _ I.2.1)
  | @snoc w f e R Lf IH =>
    rw [raw_snoc']
    exact writer_step_on G.P C L _ (cached_run_on G.P x X w) a IH e
      (ShortFiveGuardTour.write_safe C L _ cmd d D f
        (write_active_on G A C x X cmd d D w f R))

private theorem write_file_on (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (x : Raw s n) (X : Cached G.P x) (cmd : Cmd) (d : Fin 8)
    (D : descValid d.val=true) (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (R : WGen G.P C x cmd d w f) :
    ShortWriteFileSplice.healthy f →
      fileField.read (G.P.byte (rawRun x w) C.root)=fileField.read (G.P.byte x C.root) := by
  induction R with
  | launch I _ =>
    intro _
    have F := ShortWriteFileSplice.raw_file_step (view G.P x) C.root (door C)
      G.P.nonself ((view_header G.P x _).trans C.rootHeader) (by
        intro _
        refine .inl ⟨I.2.2.1,?_,?_⟩
        · change 0<get (G.P.byte x C.root) 78 3 (by decide)
          rw [←view_byte G.P x C.root,I.2.2.2]; cases cmd <;> decide
        · change get (G.P.byte x C.root) 78 3 (by decide)<7
          rw [←view_byte G.P x C.root,I.2.2.2]; exact ShortWriteFlight.cmd_bound cmd)
    rw [view_next G.P x X (door C) C.root] at F
    exact F
  | @snoc w f e R L IH =>
    intro H
    let y := rawRun x w
    have Y := cached_run_on G.P x X w
    have B := ShortWriteFileSplice.healthy_before C cmd d (view G.P y) e f H
    have F := ShortWriteFileSplice.raw_file_step (view G.P y) C.root e
      G.P.nonself ((view_header G.P y _).trans C.rootHeader)
      (fun _=>ShortWriteFileSplice.safe_wait_door C (view G.P y)
        ((view_header G.P y _).trans C.rootHeader) cmd d D f L B
        (write_active_on G A C x X cmd d D w f R))
    rw [view_next G.P y Y e C.root] at F
    rw [raw_snoc']
    exact F.trans (IH B)

-- The exact receipt-progress calculation used by the MIS1 proof.
private theorem receipt_progress (C : Chart h) (v : Raw s n)
    (cmd : Cmd) (d : Fin 8) (e : Fin n) (f : ShortWriteFlight.Flight)
    (I : C.a+1<C.L) (F : ShortWriteFlight.FrontInRange C.L f)
    (R : ShortWriteFlight.NeedsReceipt C (ShortWriteFlight.next C cmd d v e f)) :
    ShortWriteFlight.NeedsReceipt C f ∨
      ∃ bad, f=.front C.a bad ∧ e=nextAt C.root C.a ∧
        ShortWriteChartHop.advanceBad cmd d C v C.a bad=false := by
  cases f with
  | done bad => exact .inl R
  | back i bad =>
    left
    cases E : nextStage C e (.rev i) <;>
      simpa only [ShortWriteFlight.next,E,ShortWriteFlight.NeedsReceipt] using R
  | front i bad =>
    by_cases E : e=nextAt C.root i
    · by_cases J : i+1<C.L
      · simp only [ShortWriteFlight.next,if_pos E,if_pos J,ShortWriteFlight.NeedsReceipt] at R
        by_cases M : i=C.a
        · subst i; exact .inr ⟨bad,rfl,E,R.2⟩
        · left
          refine ⟨by omega,?_⟩
          cases bad <;> simp [ShortWriteChartHop.advanceBad] at R ⊢
      · simp only [ShortWriteFlight.next,if_pos E,if_neg J,ShortWriteFlight.NeedsReceipt] at R
        exact .inl ⟨by omega,R⟩
    · exact .inl (by simpa only [ShortWriteFlight.next,if_neg E] using R)

private theorem front_bound (C : Chart h) (v : Raw s n) (cmd : Cmd)
    (d : Fin 8) (f : ShortWriteFlight.Flight) (A : ShortWriteFlight.Active C cmd d v f) :
    ShortWriteFlight.FrontInRange C.L f := by
  cases f with
  | front => exact A.1
  | _ => trivial

private theorem write_effect_on (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (L : Layout C) (x : Raw s n) (X : Cached G.P x) (cmd : Cmd) (d : Fin 8)
    (D : descValid d.val=true) (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (R : WGen G.P C x cmd d w f) :
    ShortWriteFlight.NeedsReceipt C f →
      (cmd.effectField d).read (G.P.byte (rawRun x w) (centre C))=cmd.effectBits d := by
  induction R with
  | launch I E =>
    intro H
    exact False.elim ((Nat.not_lt_zero _) H.1)
  | @snoc w f e R Lf IH =>
    let y := rawRun x w
    let v := view G.P y
    have Y := cached_run_on G.P x X w
    have Act := write_active_on G A C x X cmd d D w f R
    have K := write_actual_step G.P C (large9 G A) y Y (wgeom G A C y)
      cmd d D e f Lf Act
    intro B
    rw [raw_snoc']
    rcases receipt_progress C v cmd d e f L.room (front_bound C v cmd d f Act) B
      with Old|⟨bad,F,E,V⟩
    · have tag := ShortFiveGuardTour.passed_centre_tag C L v cmd d D f Act Old
      have Eff := IH Old
      have Safe := ShortFiveGuardTour.write_safe C L v cmd d D f Act
      cases cmd with
      | stage =>
        exact (bank_field_eq _ _ d (bank_step_on G.P C L y Y e (.inl tag))).trans Eff
      | «seal» => exact (seal_step_on G.P C L y Y e Safe (.inl tag)).trans Eff
    · have W := (K.2 bad F E V).wrote
      rw [view_next G.P y Y e e] at W
      unfold centre
      rw [←E]
      exact W

private theorem seal_keeps_bank_on (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (L : Layout C) (x : Raw s n) (X : Cached G.P x) (d : Fin 8)
    (D : descValid d.val=true) (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (R : WGen G.P C x .seal d w f) :
    (lane 87 2 (by decide)).read (G.P.byte (rawRun x w) (centre C))=
      (lane 87 2 (by decide)).read (G.P.byte x (centre C)) := by
  induction R with
  | launch I _ =>
    exact bank_step_on G.P C L x X (door C) (.inl (clear_centre_tag C L _ I.2.1))
  | @snoc w f e R Lf IH =>
    have Q := ShortFiveGuardTour.seal_bank_safe C L (view G.P (rawRun x w)) d D f
      (write_active_on G A C x X .seal d D w f R)
    rw [raw_snoc']
    exact (bank_step_on G.P C L _ (cached_run_on G.P x X w) e Q).trans IH

private theorem prefix_succ (C : Chart h) (k : Nat) :
    tourPrefix C (k+1)=tourPrefix C k++[nextAt C.root k] := by
  simp [tourPrefix,List.range_succ,List.map_append]

private theorem write_prefix_on (P : Params s n) (C : Chart P.h) (L : Layout C)
    (x : Raw s n) (cmd : Cmd) (d : Fin 8)
    (I : ClearIssue C (view P x) cmd.op) (D : d.val=issuedDescriptor (P.byte x C.root))
    (k : Nat) (K : k≤C.a) :
    WGen P C x cmd d (tourPrefix C k) (.front k false) := by
  induction k with
  | zero => exact .launch I D
  | succ k ih =>
    have Q := WGen.snoc (nextAt C.root k) (ih (by omega)) (by trivial)
    rw [prefix_succ]
    have Z : k+1<C.L := by have := L.room; omega
    have E : k≠C.a := by omega
    have EB : (k == C.a) = false := by simp [E]
    simpa [wNext,ShortWriteFlight.next,ShortWriteChartHop.advanceBad,Z,EB] using Q

private theorem write_back (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (cmd : Cmd) (d : Fin 8) (w : List (Fin n)) (k : Nat)
    (R : WGen P C x cmd d w (.back k false)) :
    WGen P C x cmd d (w++(List.range k).reverse.map (nextAt C.root)) (.back 0 false) := by
  induction k generalizing w with
  | zero => simpa using R
  | succ k ih =>
    have Q := WGen.snoc (nextAt C.root k) R (by trivial)
    have T : WGen P C x cmd d (w++[nextAt C.root k]) (.back k false) := by
      simpa [wNext,ShortWriteFlight.next,nextStage] using Q
    simpa [List.range_succ,List.reverse_append,List.map_append,List.append_assoc] using ih _ T

private theorem write_tour_on (P : Params s n) (C : Chart P.h) (_L : Layout C)
    (x : Raw s n) (cmd : Cmd) (d : Fin 8)
    (I : ClearIssue C (view P x) cmd.op) (D : d.val=issuedDescriptor (P.byte x C.root))
    (Acc : cmd.accepts (P.byte (rawRun x (tourPrefix C C.a)) (centre C)) d=true) :
    WGen P C x cmd d (tour C) (.done false) := by
  have front (k : Nat) (K : k<C.L) :
      WGen P C x cmd d (tourPrefix C k) (.front k false) := by
    induction k with
    | zero => exact .launch I D
    | succ k ih =>
      have Q := WGen.snoc (nextAt C.root k) (ih (by omega)) (by trivial)
      have good : ShortWriteChartHop.advanceBad cmd d C
          (view P (rawRun x (tourPrefix C k))) k false=false := by
        by_cases E : k=C.a
        · subst k
          have T : cmd.accepts (P.byte (rawRun x (tourPrefix C C.a)) (nextAt C.root C.a)) d=true := Acc
          simp [ShortWriteChartHop.advanceBad,view_byte,T]
        · simp [ShortWriteChartHop.advanceBad,E]
      rw [prefix_succ]
      simpa [wNext,ShortWriteFlight.next,K,good] using Q
  let k := C.L-1
  have K : k<C.L := by have := C.positive; dsimp [k]; omega
  have E : C.L=k+1 := by have := C.positive; dsimp [k]; omega
  have Turn := WGen.snoc (nextAt C.root k) (front k K) (by trivial)
  have T : WGen P C x cmd d (tourPrefix C C.L) (.back k false) := by
    rw [E,prefix_succ]
    simpa [wNext,ShortWriteFlight.next,show ¬k+1<C.L by omega] using Turn
  have B := write_back P C x cmd d _ k T
  have Q := WGen.snoc (door C) B (by trivial)
  simpa [wNext,ShortWriteFlight.next,nextStage,door,RearTrace.right_predecessor,
    tourPrefix,tour,k,List.append_assoc] using Q

private theorem write_exit_on (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (x : Raw s n) (X : Cached G.P x) (cmd : Cmd) (d : Fin 8)
    (D : descValid d.val=true) (E : d.val=issuedDescriptor (G.P.byte x C.root))
    (R : WGen G.P C x cmd d (tour C) (.done false)) :
    ClearIssue C (view G.P (rawRun x (tour C))) (cmd.op+1) ∧
      d.val=issuedDescriptor (G.P.byte (rawRun x (tour C)) C.root) := by
  have Act := write_active_on G A C x X cmd d D _ _ R
  refine ⟨ShortPreReadGrants.clear_issue_of_pc C _ (cmd.op+1)
    (by cases cmd <;> decide) Act.1 (by cases cmd <;> exact Act.2),?_⟩
  have F := write_file_on G A C x X cmd d D _ _ R rfl
  exact E.trans (ShortWriteFileSplice.descriptor_of_same_file _ _ F).symm

private theorem stage_accepts_on (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (L : Layout C) (x : Raw s n) (X : Cached G.P x) (d : Fin 8)
    (D : descValid d.val=true) (I : ClearIssue C (view G.P x) 4)
    (E : d.val=issuedDescriptor (G.P.byte x C.root)) (W : Writer C (view G.P x) (d.val/4)) :
    Cmd.stage.accepts (G.P.byte (rawRun x (tourPrefix C C.a)) (centre C)) d=true := by
  have P := write_prefix_on G.P C L x .stage d I E C.a (Nat.le_refl _)
  have V := write_writer_on G A C L x X .stage d D _ W _ _ P
  change stageSealOwner (G.P.byte (rawRun x (tourPrefix C C.a)) (centre C)) d.val && true=true
  unfold stageSealOwner
  rw [←view_byte,V.2.1,V.2.2]
  simp

private theorem seal_accepts_on (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (L : Layout C) (x : Raw s n) (X : Cached G.P x) (d : Fin 8)
    (D : descValid d.val=true) (I : ClearIssue C (view G.P x) 5)
    (E : d.val=issuedDescriptor (G.P.byte x C.root)) (W : Writer C (view G.P x) (d.val/4))
    (Bank : (Cmd.stage.effectField d).read (G.P.byte x (centre C))=Cmd.stage.effectBits d) :
    Cmd.seal.accepts (G.P.byte (rawRun x (tourPrefix C C.a)) (centre C)) d=true := by
  have P := write_prefix_on G.P C L x .seal d I E C.a (Nat.le_refl _)
  have V := write_writer_on G A C L x X .seal d D _ W _ _ P
  have BK := bank_field_eq _ _ d (seal_keeps_bank_on G A C L x X d D _ _ P)
  have B := stage_bit _ d (BK.trans Bank)
  change (stageSealOwner (G.P.byte (rawRun x (tourPrefix C C.a)) (centre C)) d.val &&
    sealBankMatches (G.P.byte (rawRun x (tourPrefix C C.a)) (centre C)) d.val)=true
  unfold stageSealOwner
  rw [←view_byte,V.2.1,V.2.2,view_byte,B]
  simp

/- G. Stop at the OLD pending COMMIT ingress. -/

private theorem commit_prefix_on (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (L : Layout C) (x : Raw s n) (X : Cached G.P x) (d : Fin 8)
    (D : descValid d.val=true) (I : ClearIssue C (view G.P x) 6)
    (E : d.val=issuedDescriptor (G.P.byte x C.root)) (k : Nat) (K : k≤C.a-1) :
    ShortCommitFlight.Active C d (view G.P (rawRun x (tourPrefix C k))) (.front k .pending) := by
  induction k with
  | zero =>
    obtain ⟨b,_,B,F⟩ := ShortCommitFlight.launch C (view G.P x) (view_header G.P x) I
    have Eq : b=d := Fin.ext (B.trans E.symm)
    subst b
    exact (commit_active_congr C d _ _ (view_next G.P x X (door C)) _).mp F
  | succ k ih =>
    have H := ih (by omega)
    let y := rawRun x (tourPrefix C k)
    have Y := cached_run_on G.P x X (tourPrefix C k)
    have Q := (commit_actual_step G.P C (large9 G A) y Y (cgeom G A C y)
      d D (nextAt C.root k) (.front k .pending) trivial H).1
    have Z : k+1<C.L := by have := L.room; omega
    have M : k≠C.a-1 := by omega
    rw [prefix_succ,raw_snoc']
    simpa [ShortCommitFlight.next,ShortCommitChartHop.advance,Z,M] using Q

private theorem remote_on (P : Params s n) (x : Raw s n) (X : Cached P x)
    (q : Fin n) (w : List (Fin n)) (R : ∀ e∈w,q≠e ∧ q≠rightNeighbor e) :
    P.byte (rawRun x w) q=P.byte x q := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have F := reset_remote_frame_raw (view P x) e q (R e (by simp)).1 (R e (by simp)).2
    rw [view_next P x X e q] at F
    exact (ih _ (P.cached_closed x e X) (fun f H=>R f (List.mem_cons_of_mem _ H))).trans F

private theorem commit_guard_on (G : Geometry s n) (A : 2≤G.A) (C : Chart G.P.h)
    (L : Layout C) (x : Raw s n) (X : Cached G.P x) (d : Fin 8)
    (D : descValid d.val=true) (I : ClearIssue C (view G.P x) 6)
    (E : d.val=issuedDescriptor (G.P.byte x C.root)) (W : Writer C (view G.P x) (d.val/4))
    (Bank : (Cmd.stage.effectField d).read (G.P.byte x (centre C))=Cmd.stage.effectBits d)
    (Seal : (Cmd.seal.effectField d).read (G.P.byte x (centre C))=Cmd.seal.effectBits d) :
    let y := rawRun x (tourPrefix C (C.a-1))
    selectorGuard (G.P.h (ingress C)) (G.P.byte y (ingress C))
      (G.P.byte y (rightNeighbor (ingress C))) := by
  let y := rawRun x (tourPrefix C (C.a-1))
  have F := commit_prefix_on G A C L x X d D I E (C.a-1) (Nat.le_refl _)
  have Wire := F.2.2.2.1
  change (kField (C.route.port (C.a-1))).read (G.P.byte y (ingress C))=
    encode (writeFwd 6 d false) at Wire
  rw [L.inPort] at Wire
  have Eq := remote_on G.P x X (centre C) (tourPrefix C (C.a-1))
    (ShortFiveGuardTour.commit_prefix_remote C L)
  have Old := ShortCommitGenerationEvent.old_commit_token (view G.P y) (ingress C) d D false Wire
  have B := stage_bit _ d Bank
  have S := sealed_descriptor _ d D Seal
  have Acc : commitAccept (G.P.byte y (centre C)) (writeFwd 6 d false)=true := by
    rw [Eq]
    change (!false && (G.P.byte x (centre C)).getLsbD 90 &&
      get (G.P.byte x (centre C)) 92 1 (by decide)==d.val/4 &&
      readSeal (G.P.byte x (centre C))==some d.val &&
      ((G.P.byte x (centre C)).getLsbD (88-(d.val/2)%2)==(d.val%2==1)))=true
    have V : (G.P.byte x (centre C)).getLsbD (88-(d.val/2)%2)=(d.val%2==1) :=
      beq_iff_eq.mp B
    rw [←view_byte,W.2.1,W.2.2,view_byte,S,V]
    simp
  change selectorGuard (header (view G.P y) (ingress C))
    ((view G.P y) (ingress C)).mis1 ((view G.P y) (rightNeighbor (ingress C))).mis1
  -- CHECK: ShortResetRow selectorGuard_iff_commitAccept; same tuple as
  -- ShortFiveGuardTour.guarded_last_three:833–836.
  apply (selectorGuard_iff_commitAccept _ _ _).mpr
  rw [Old,ShortFiveGuardTour.ingress_right C L]
  exact ⟨rfl,rfl,rfl,Acc⟩

/-- The exact supplier of the existing mixed-sheet consumer. -/
theorem fenced_word_rows (G : Geometry s n) (A : 2≤G.A) :
    ShortMISPublicationSuppliers.FencedWordRows G := by
  intro i x Good Park
  let P := G.P
  let C := G.family i 2
  let u := tour C++admit C C.a
  let z := rawRun x u
  let w := helloBody C++[door C]
  let x4 := rawRun z (door C::w)
  let x5 := rawRun x4 (tour C)
  let x6 := rawRun x5 (tour C)
  let d : Fin 8 := ⟨issuedDescriptor (P.byte x4 C.root),
    (ShortWritePacketCodec.issued_descriptor_valid (P.byte x4 C.root)).1⟩
  have D : descValid d.val=true :=
    (ShortWritePacketCodec.issued_descriptor_valid (P.byte x4 C.root)).2
  have L := target_layout G A i
  have Z := cached_run_on P x Good.1 u
  have X4 := cached_run_on P z Z (door C::w)
  have X5 := cached_run_on P x4 X4 (tour C)
  have X6 := cached_run_on P x5 X5 (tour C)
  have I := (winning_entry_actual P C x Good.1 (Park 2)).2
  obtain ⟨Before,out,R,I4⟩ := successful_read_actual G A i x Good.1 Park
  have W4 : Writer C (view P x4) (d.val/4) :=
    read_writer_actual G A C L z Z I w out Before R
  have E4 : d.val=issuedDescriptor (P.byte x4 C.root) := rfl
  have S4 := stage_accepts_on G A C L x4 X4 d D I4 E4 W4
  have T4 := write_tour_on P C L x4 .stage d I4 E4 S4
  have W5 := write_writer_on G A C L x4 X4 .stage d D _ W4 _ _ T4
  have Bank5 := write_effect_on G A C L x4 X4 .stage d D _ _ T4 rfl
  obtain ⟨I5,E5⟩ := write_exit_on G A C x4 X4 .stage d D E4 T4
  have S5 := seal_accepts_on G A C L x5 X5 d D I5 E5 W5 Bank5
  have T5 := write_tour_on P C L x5 .seal d I5 E5 S5
  have W6 := write_writer_on G A C L x5 X5 .seal d D _ W5 _ _ T5
  have Bank6 := (bank_field_eq _ _ d (seal_keeps_bank_on G A C L x5 X5 d D _ _ T5)).trans Bank5
  have Seal6 := write_effect_on G A C L x5 X5 .seal d D _ _ T5 rfl
  obtain ⟨I6,E6⟩ := write_exit_on G A C x5 X5 .seal d D E5 T5
  have Guard := commit_guard_on G A C L x6 X6 d D I6 E6 W6 Bank6 Seal6
  have ReadWord : door C::w=tour C := (tour_body C).symm
  -- CHECK: ShortMISPublicationLift.lean:192–225. The fifth tour is
  -- SEAL, and the sixth tour is split BEFORE its ingress mark.
  change selectorGuard (P.h (ingress C)) (P.byte (rawRun x (wordLead C)) (ingress C))
    (P.byte (rawRun x (wordLead C)) (rightNeighbor (ingress C)))
  simpa only [wordLead,wordPre,raw_app,←ReadWord,x6,x5,x4,z,u] using Guard

open ShortH2RawEntrance in
theorem mis2_fenced_word_rows (N : 63<n) (x : Raw s n)
    (H : PermanentH2 (by omega : 21<n) x) :
    ShortMISPublicationSuppliers.FencedWordRows (ShortMISLift.mis2Geometry N x H) :=
  fenced_word_rows _ (by change 2≤4; decide)

theorem mis3_fenced_word_rows (N : 189<n) (x : Raw s n)
    (H : ShortMISLift.PermanentH3 (by omega : 63<n) x) :
    ShortMISPublicationSuppliers.FencedWordRows (ShortMIS3Entrance.mis3Geometry N x H) :=
  fenced_word_rows _ (by change 2≤8; decide)

open ShortH2RawEntrance in
theorem mis23_from_h2_only_protected (N : 189<n) (x : Raw s n)
    (H : PermanentH2 (by omega : 21<n) x)
    (A2 : ShortMISPublicationSuppliers.ProtectedRows
      (ShortMISLift.mis2Geometry (by omega : 63<n) x H))
    (A3 : ∀ (y : Raw s n) (Y : ShortMISLift.PermanentH3 (by omega : 63<n) y),
      ShortMISPublicationSuppliers.ProtectedRows (ShortMIS3Entrance.mis3Geometry N y Y)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (ShortMIS3Entrance.PermanentH4 N) x
      ((ShortMISLift.K_H3+ShortMISLift.K_H4)*n^2) :=
  ShortMISPublicationSuppliers.mis23_from_h2 N x H A2
    (mis2_fenced_word_rows (by omega) x H) A3 (mis3_fenced_word_rows N)

#print axioms winning_entry_actual
#print axioms rival_header_actual
#print axioms read_mark_wins_actual
#print axioms successful_read_actual
#print axioms read_writer_actual
#print axioms fenced_word_rows
#print axioms mis2_fenced_word_rows
#print axioms mis3_fenced_word_rows
#print axioms mis23_from_h2_only_protected

end
end L4.ShortMISFencedWord


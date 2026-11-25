import Leader.L4.ShortWriteFileSplice
import Leader.L4.ShortWriteFlight
import Leader.L4.ShortReadCaptureTrace
import Leader.L4.ShortWinningReaderRelay

namespace L4.ShortMIS1ReadLease
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow
open ShortResetCycle ShortResetChart ShortResetForwardH2 ShortResetFlow
open ShortReaderTrace
set_option maxRecDepth 8192

def NotReset (t : Token) : Prop := t.tag≠2 ∨ t.fault=true ∨ t.opcode≠0

theorem release_false (b : BitVec 96) (j : Fin 3)
    (S : NotReset (oldK true b j)) : (headerGrantView b).release j=false := by
  change ((oldK true b j).tag==2 && !(oldK true b j).fault &&
    (oldK true b j).opcode==0)=false
  rcases S with S|S|S
  · simp [S]
  · simp [S]
  · simp [S]

def Fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n) : Prop :=
  ∀ i, i<C.L → header x (nextAt C.root i)=true →
    (headerGrantView (x (nextAt C.root i)).mis1).release (C.route.port i)=false

theorem fence_of_wire {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (i : Nat) (t : Token)
    (W : bits C.route x i=encode t)
    (D : ∀ g,decode g (encode t)=t) (S : NotReset t)
    (H : header x (nextAt C.root i)=true) :
    (headerGrantView (x (nextAt C.root i)).mis1).release (C.route.port i)=false := by
  have B := slot_of_bits C.route x i t D W
  change oldK (header x (nextAt C.root i)) (x (nextAt C.root i)).mis1 (C.route.port i)=t at B
  rw [H] at B
  apply release_false
  rwa [B]

private theorem safe_E : NotReset E := .inl (by decide)
private theorem safe_T : NotReset T := .inl (by decide)
private theorem decode_E (g : Bool) : decode g (encode E)=E := by cases g <;> decide

theorem clear_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (A : ShortEmptyOwnership.Clear C x) : Fenced C x := by
  intro i I
  exact fence_of_wire C x i E (A i I) decode_E safe_E

theorem returning_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (op : Nat) (p : ShortCanonicalReverseChart.Reply) (j : Nat)
    (A : ShortCanonicalReverseChart.Returning C x op p j) : Fenced C x := by
  intro i I
  have W : bits C.route x i=encode (ShortCanonicalReverseChart.trailAt p j i) := A.2.2 i I
  by_cases H : i<j
  · simp only [ShortCanonicalReverseChart.trailAt,if_pos H] at W
    exact fence_of_wire C x i T W trail_decode safe_T
  · by_cases K : i=j
    · simp only [ShortCanonicalReverseChart.trailAt,if_neg H,if_pos K] at W
      exact fence_of_wire C x i p.token W p.decode_encode (.inl (by rw [p.tag]; decide))
    · simp only [ShortCanonicalReverseChart.trailAt,if_neg H,if_neg K] at W
      exact fence_of_wire C x i E W decode_E safe_E

theorem forward_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (j : Nat) (t : Token) (Tj : TrailPrefix C.route x j)
    (W : bits C.route x j=encode t) (S : ShortHelloForward.ClearSuffix C.route x j)
    (D : ∀ g,decode g (encode t)=t) (safe : NotReset t) : Fenced C x := by
  intro i I
  rcases Nat.lt_trichotomy i j with L|rfl|R
  · exact fence_of_wire C x i T (Tj i L) trail_decode safe_T
  · exact fence_of_wire C x i t W D safe
  · exact fence_of_wire C x i E (S i R I) decode_E safe_E

theorem write_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (cmd : ShortWriteCentreWitness.Cmd) (d : Fin 8)
    (D : descValid d.val=true) (f : ShortWriteFlight.Flight)
    (A : ShortWriteFlight.Active C cmd d x f) : Fenced C x := by
  cases f with
  | done => exact clear_fenced C x A.1
  | back i bad => exact returning_fenced C x cmd.op _ i A
  | front i bad =>
    exact forward_fenced C x i _ A.2.2.1 A.2.2.2.1 A.2.2.2.2
      (ShortWriteChartHop.packet_decode cmd d D bad)
      (by cases bad <;> cases cmd <;> first
          | exact .inr (.inl rfl)
          | exact .inr (.inr (by decide : 4≠0))
          | exact .inr (.inr (by decide : 5≠0)))

theorem commit_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (d : Fin 8) (D : descValid d.val=true)
    (f : ShortCommitFlight.Flight) (A : ShortCommitFlight.Active C d x f) : Fenced C x := by
  cases f with
  | done => exact clear_fenced C x A.1
  | back i p => exact returning_fenced C x 6 _ i A
  | front i p =>
    exact forward_fenced C x i _ A.2.2.1 A.2.2.2.1 A.2.2.2.2
      (ShortCommitChartHop.packet_decode d D p)
      (by cases p <;> first | exact .inr (.inl rfl) | exact .inr (.inr (by decide : 6≠0)))

theorem read_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (f : ShortReadFlight.Flight) (A : ShortReadFlight.Active C x f) :
    Fenced C x := by
  cases f with
  | consumed => exact clear_fenced C x A.1
  | returning j ok d =>
    let p : ShortCanonicalReverseChart.Reply :=
      ⟨ShortReadReturnHop.readReply ok d,by cases ok <;> rfl,
        fun g=>ShortReadReturnHop.decode_readReply g ok d⟩
    intro i I
    have W : bits C.route x i=encode (ShortCanonicalReverseChart.trailAt p j i) := by
      have Z : bits C.route x i=encode (ShortReadReverseChart.trailAt ok d j i) := A.2.2 i I
      rw [Z]
      rfl
    by_cases H : i<j
    · simp only [ShortCanonicalReverseChart.trailAt,if_pos H] at W
      exact fence_of_wire C x i T W trail_decode safe_T
    · by_cases K : i=j
      · simp only [ShortCanonicalReverseChart.trailAt,if_neg H,if_pos K] at W
        exact fence_of_wire C x i p.token W p.decode_encode (.inl (by rw [p.tag]; decide))
      · simp only [ShortCanonicalReverseChart.trailAt,if_neg H,if_neg K] at W
        exact fence_of_wire C x i E W decode_E safe_E
  | forward i d =>
    exact forward_fenced C x i _ A.2.2.2.1 A.2.2.2.2.1 A.2.2.2.2.2
      (fun g=>ShortReadForward.decode_front g d A.2.1) (.inr (.inr (by decide : 3≠0)))

def FencedTape {s n : Nat} {h : Fin n→Bool} (C : Chart h) :
    Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x, e::w => Fenced C x ∧ FencedTape C (rawNext s x e) w

theorem fence_append {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (w v : List (Fin n)) :
    FencedTape C x (w++v) ↔ FencedTape C x w ∧ FencedTape C (rawRun x w) v := by
  induction w generalizing x with
  | nil => simp [FencedTape,rawRun,BStarResetSchedule.run]
  | cons e w ih =>
    change (Fenced C x ∧ FencedTape C (rawNext s x e) (w++v)) ↔
      (Fenced C x ∧ FencedTape C (rawNext s x e) w) ∧ FencedTape C (rawRun (rawNext s x e) w) v
    rw [ih]
    exact and_assoc.symm

theorem read_prefix_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (A : H2Ready x) (N : 5≤n) (heads : ∀ q,header x q=h q)
    (f : ShortReadFlight.Flight) (P : ShortReadFlight.Active C x f)
    (w : List (Fin n)) (B : ShortReadFlight.beforeConsume C x f w) :
    FencedTape C x w := by
  induction w generalizing x f with
  | nil => trivial
  | cons e w ih =>
    obtain ⟨L,T⟩ := B
    exact ⟨read_fenced C x f P,ih _ (h2_ready_closed N x e A)
      (fun q=>(H1.raw_h1_selected_frozen N x e q A.1).trans (heads q)) _
      (ShortReadFlight.read_flight_active_step C x e (by omega) heads f L P) T⟩

theorem write_prefix_fenced {s n : Nat} (x : Raw s n) (C : Chart (header x))
    (A : H2Ready x) (N : 9<n) (cmd : ShortWriteCentreWitness.Cmd)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (G : ShortWriteFlight.Generated x C cmd d w f) : FencedTape C x w := by
  induction G with
  | launch I _ => exact ⟨clear_fenced C x I.2.1,trivial⟩
  | @snoc w f e G _ ih =>
    apply (fence_append C x w [e]).mpr
    exact ⟨ih,write_fenced C _ cmd d D f (ShortWriteFlight.generated_receipt x C A N cmd d D w f G).1,trivial⟩

theorem commit_prefix_fenced {s n : Nat} (x : Raw s n) (C : Chart (header x))
    (A : H2Ready x) (N : 9<n) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : ShortCommitFlight.Flight)
    (G : ShortCommitFlight.Generated x C d w f) : FencedTape C x w := by
  induction G with
  | launch I _ => exact ⟨clear_fenced C x I.2.1,trivial⟩
  | @snoc w f e G _ ih =>
    apply (fence_append C x w [e]).mpr
    exact ⟨ih,commit_fenced C _ d D f (ShortCommitFlight.generated_receipt x C A N d D w f G).1,trivial⟩

theorem no_release_of_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n)
    (A : H2Ready x) (N : 5≤n) (i : Nat) (I : i<C.L)
    (H : header x (nextAt C.root i)=true)
    (w : List (Fin n)) (F : FencedTape C x w) :
    NoOwnerReleaseBefore (nextAt C.root i) (C.route.port i) x w := by
  induction w generalizing x with
  | nil => trivial
  | cons e w ih =>
    exact ⟨fun _=>F.1 i I H,ih _ (h2_ready_closed N x e A)
      ((H1.raw_h1_selected_frozen N x e _ A.1).trans H) F.2⟩

/-- Only the chosen reader header is required to be normalized.
Other headers may still be in inherited epochs. -/
theorem local_reader_run {s n : Nat} (x : Raw s n) (N : 5≤n)
    (A : H2Ready x) (i : Fin n) (head : header x i=true)
    (j : Fin 3) (which : j=0 ∨ j=2)
    (C : ShortGrantRaw.Coherent (x i).mis1)
    (G : (x i).mis1.getLsbD (91-j.val)=true)
    (w : List (Fin n)) (F : NoOwnerReleaseBefore i j x w) :
    (rawRun x w i).mis1.getLsbD (91-j.val)=true ∧
    ShortReaderMIS1.selectedValue (rawRun x w i).mis1=ShortReaderMIS1.selectedValue (x i).mis1 := by
  induction w generalizing x with
  | nil => exact ⟨G,rfl⟩
  | cons e w ih =>
    have R : (x i).mis1.getLsbD 91=true ∨ (x i).mis1.getLsbD 89=true := by
      rcases which with rfl|rfl
      · exact .inl G
      · exact .inr G
    have nw := no_writer_of_reader C R
    have S := ShortReaderMIS1.held_reader_value_raw x e i head nw R
    have sep := edge_sep (by omega : 1<n) e
    have Y := ih (rawNext s x e) (h2_ready_closed N x e A)
      ((H1.raw_h1_selected_frozen N x e i A.1).trans head)
      (ShortGrantRaw.coherent_next_at x e i sep head C)
      (ShortGrantPersistence.held_until_release x e i j sep head C G F.1) F.2
    exact ⟨Y.1,Y.2.trans S⟩

/-- A winning capture normalizes this header on its own outgoing mark,
so the local relay requires H2, not globally coherent grants. -/
theorem local_winner_current {s n : Nat} (x : Raw s n) (N : 5≤n)
    (A : H2Ready x) (e : Fin n) (j : Fin 3) (which : j=0 ∨ j=2)
    (head : header x e=true)
    (win : readWins true (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1 j=true)
    (w : List (Fin n)) (R : NoOwnerReleaseBefore e j (rawNext s x e) w) :
    (rawRun (rawNext s x e) w e).mis1.getLsbD (91-j.val)=true ∧
    ShortReaderMIS1.selectedValue (rawRun (rawNext s x e) w e).mis1=
      ShortReaderMIS1.selectedValue (x e).mis1 := by
  have G := ShortReadGrantCapture.capture_winner_has_grant x e j head win
  have nw := ShortWinningReaderRelay.winning_reader_no_old_writer _ _ _ j which win
  have V := ShortReaderMIS1.no_writer_frame_raw x e e (MISByteCodec.lane 92 1 (by decide))
    (.inr ⟨by decide,by decide⟩) head nw
  have B := ShortReaderMIS1.no_writer_frame_raw x e e (MISByteCodec.lane 87 2 (by decide))
    (.inl ⟨by decide,by decide⟩) head nw
  have Y := local_reader_run (rawNext s x e) N (h2_ready_closed N x e A) e
    ((H1.raw_h1_selected_frozen N x e e A.1).trans head) j which
    (ShortGrantRaw.outgoing_coherent_at x e head) G w R
  refine ⟨Y.1,Y.2.trans ?_⟩
  unfold ShortReaderMIS1.selectedValue
  rw [B,V]

private theorem read_before_prefix {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (f : ShortReadFlight.Flight) (u v : List (Fin n))
    (B : ShortReadFlight.beforeConsume C x f (u++v)) :
    ShortReadFlight.beforeConsume C x f u := by
  induction u generalizing x f with
  | nil => trivial
  | cons e u ih => exact ⟨B.1,ih _ _ B.2⟩

/-- The old sample at each actual winning reader mark is still the
selected bit at the endpoint of the literal tape. The continuation
fence is supplied by the actual STAGE/SEAL/COMMIT phase theorems and
their empty issue intervals, not by a quiet-neighbour assumption. -/
theorem read_file_matches_current_endpoints {s n : Nat} (x : Raw s n)
    (A : H2Ready x) (C : Chart (header x)) (N : 9<n)
    (I : ShortClearLaunch.ClearIssue C x 3)
    (w v : List (Fin n)) (out : Fin 64)
    (B : ShortReadFlight.beforeConsume C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w)
    (D : ShortReadFlight.trace C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w=.consumed true out)
    (F : FencedTape C (rawRun x (RearTrace.predecessor C.root::w)) v) :
    let y := rawRun x (RearTrace.predecessor C.root::w)
    ∀ j : Fin 3, j=0 ∨ j=2 → ∃ i<C.L,
      C.route.port i=j ∧ header (rawRun y v) (nextAt C.root i)=true ∧
      (ShortReadResult.fileField.read (y C.root).mis1).getLsbD (2-j.val)=
        ShortReaderMIS1.selectedValue (rawRun y v (nextAt C.root i)).mis1 := by
  let door := RearTrace.predecessor C.root
  let x' := rawNext s x door
  let y := rawRun x' w
  have C' := h2_ready_closed (by omega : 5≤n) x door A
  have heads : ∀ q,header x' q=header x q := fun q=>H1.raw_h1_selected_frozen (by omega) x door q A.1
  have W := read_prefix_fenced C x' C' (by omega) heads (.forward 0 64)
    (ShortReadForward.forward_from_actual_issue3 C x (fun _=>rfl) I) w B
  have F' : FencedTape C y v := F
  have Full := (fence_append C x' w v).mpr ⟨W,F'⟩
  dsimp only
  intro j J
  obtain ⟨p,lead,tail,i,payload,T,O,Tr,E,P,Win,_,Bit⟩ :=
    ShortReadCaptureTrace.read_return_matches_three_captures x A C N I w out B D j
  have H : header p.old p.edge=true := (Bool.and_eq_true_iff.mp Win).1
  have V : readWins true (header p.old (rightNeighbor p.edge))
      (p.old p.edge).mis1 (p.old (rightNeighbor p.edge)).mis1 j=true := by
    have Q := (Bool.and_eq_true_iff.mp Win).2
    rwa [H] at Q
  have Below : i<C.L := by
    have B' := read_before_prefix C x' (.forward 0 64) lead (p.edge::tail) (T ▸ B)
    have Ap := ShortReadFlight.active_from_clean_issue3 C (by omega) lead x A
      (fun _=>rfl) I B'
    dsimp only at Ap
    rw [Tr] at Ap
    exact Ap.1
  have CV : H2Ready p.old := O ▸ ready_run (by omega) x' C' lead
  have Full' : FencedTape C x' (lead++p.edge::(tail++v)) := by
    rw [T,List.append_assoc] at Full
    exact Full
  have FT := ((fence_append C x' lead (p.edge::(tail++v))).mp Full').2.2
  have FT' : FencedTape C (rawNext s p.old p.edge) (tail++v) := by rwa [O]
  have CV' := h2_ready_closed (by omega : 5≤n) p.old p.edge CV
  have H' : header (rawNext s p.old p.edge) p.edge=true :=
    (H1.raw_h1_selected_frozen (by omega) p.old p.edge p.edge CV.1).trans H
  have Q := no_release_of_fenced C (rawNext s p.old p.edge) CV' (by omega) i Below
    (E ▸ H') (tail++v) FT'
  have Q' : NoOwnerReleaseBefore p.edge j (rawNext s p.old p.edge) (tail++v) := by
    rwa [P,←E] at Q
  have Relay := (local_winner_current p.old (by omega) CV p.edge j J H V (tail++v) Q').2
  have endEq : rawRun y v=rawRun (rawNext s p.old p.edge) (tail++v) := by
    change rawRun (rawRun x' w) v=_
    unfold rawRun
    rw [←BStarResetSchedule.run_append (rawNext s) x' w v,T,List.append_assoc,
      BStarResetSchedule.run_append (rawNext s) x' lead]
    change rawRun (rawNext s (rawRun x' lead) p.edge) (tail++v)=_
    rw [←O]
    rfl
  refine ⟨i,Below,P,?_,?_⟩
  · change header (rawRun y v) (nextAt C.root i)=true
    rw [endEq,←E]
    exact ((header_run (by omega) (rawNext s p.old p.edge) CV'.1 (tail++v)).2 p.edge).trans H'
  · change _=ShortReaderMIS1.selectedValue (rawRun y v (nextAt C.root i)).mis1
    rw [endEq,←E,Relay,ShortReaderMIS1.selectedValue_eq]
    exact Bit

theorem fence_cast {s n : Nat} {h k : Fin n→Bool} (E : h=k) (C : Chart h)
    (x : Raw s n) (w : List (Fin n)) :
    FencedTape (E ▸ C) x w ↔ FencedTape C x w := by cases E; rfl

theorem clear_issue_prefix_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (A : H2Ready x) (N : 5≤n) (heads : ∀ q,header x q=h q)
    (op : Nat) (I : ShortClearLaunch.ClearIssue C x op) (w : List (Fin n))
    (noDoor : ∀ e∈w,e≠RearTrace.predecessor C.root) :
    FencedTape C x w := by
  induction w generalizing x with
  | nil => trivial
  | cons e w ih =>
    have P := ShortClearLaunch.clear_issue_nondoor C x heads op I e (noDoor e (by simp))
    exact ⟨clear_fenced C x I.2.1,ih _ (h2_ready_closed N x e A)
      (fun q=>(H1.raw_h1_selected_frozen N x e q A.1).trans (heads q)) P
      (fun a H=>noDoor a (by simp [H]))⟩

/-- The two capture indices are exactly the first and third selected
headers of this chart, not arbitrary sites with the same lane number. -/
theorem read_file_matches_outer_pair {s n : Nat} (x : Raw s n)
    (A : H2Ready x) (C : Chart (header x)) (N : 9<n)
    (I : ShortClearLaunch.ClearIssue C x 3)
    (w v : List (Fin n)) (out : Fin 64)
    (B : ShortReadFlight.beforeConsume C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w)
    (D : ShortReadFlight.trace C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w=.consumed true out)
    (F : FencedTape C (rawRun x (RearTrace.predecessor C.root::w)) v) :
    let y := rawRun x (RearTrace.predecessor C.root::w)
    let z := rawRun y v
    let bits := ShortReadResult.fileField.read (y C.root).mis1
    bits.getLsbD 2=ShortReaderMIS1.selectedValue (z C.root).mis1 ∧
      bits.getLsbD 0=ShortReaderMIS1.selectedValue (z (nextAt C.root (C.a+C.b))).mis1 := by
  dsimp only
  let y := rawRun x (RearTrace.predecessor C.root::w)
  let z := rawRun y v
  have headFrozen : ∀ q,header z q=header x q := by
    intro q
    have AY := ready_run (by omega) x A (RearTrace.predecessor C.root::w)
    exact ((header_run (by omega) y AY.1 v).2 q).trans
      ((header_run (by omega) x A.1 (RearTrace.predecessor C.root::w)).2 q)
  obtain ⟨_,_,_,Geo,K0,K1,K2,_,_⟩ :=
    ShortReadCaptureGeometry.capture_chart_fields x A.1 C N
  have idx (j : Fin 3) (i : Nat) (L : i<C.L) (H : header z (nextAt C.root i)=true)
      (K : C.route.port i=j) :
      (j=0 → i=0) ∧ (j=2 → i=C.a+C.b) := by
    rw [headFrozen] at H
    change lane C.a C.b i=j at K
    rcases (Geo i L).mp H with rfl|rfl|rfl
    · rw [K0] at K
      exact ⟨fun _=>rfl,fun H=>by rw [H] at K; contradiction⟩
    · rw [K1] at K
      exact ⟨fun H=>by rw [H] at K; contradiction,fun H=>by rw [H] at K; contradiction⟩
    · rw [K2] at K
      exact ⟨fun H=>by rw [H] at K; contradiction,fun _=>rfl⟩
  have M := read_file_matches_current_endpoints x A C N I w v out B D F
  obtain ⟨a,AL,AP,AH,AV⟩ := M 0 (.inl rfl)
  obtain ⟨b,BL,BP,BH,BV⟩ := M 2 (.inr rfl)
  have E := (idx 0 a AL AH AP).1 rfl
  have F := (idx 2 b BL BH BP).2 rfl
  rw [E] at AV
  rw [F] at BV
  exact ⟨AV,BV⟩

/-- These schedules name concrete generated rolls at their real launch
cuts, expressed on the same frozen chart. No fence is assumed. -/
def WriteRoll {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (cmd : ShortWriteCentreWitness.Cmd) (d : Fin 8) (w : List (Fin n)) : Prop :=
  ∃ eq : h=header x, ShortWriteFlight.Generated x (eq ▸ C) cmd d w (.done false)

def CommitPrefix {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (d : Fin 8) (w : List (Fin n)) : Prop :=
  ∃ (eq : h=header x) (p : ShortCommitChartHop.Status),
    ShortCommitFlight.Generated x (eq ▸ C) d w (.front (C.a-1) p)

theorem write_roll_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (A : H2Ready x) (N : 9<n)
    (cmd : ShortWriteCentreWitness.Cmd) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (G : WriteRoll C x cmd d w) : FencedTape C x w := by
  obtain ⟨eq,g⟩ := G
  exact (fence_cast eq C x w).mp (write_prefix_fenced x (eq ▸ C) A N cmd d D w _ g)

theorem commit_roll_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (A : H2Ready x) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (G : CommitPrefix C x d w) : FencedTape C x w := by
  obtain ⟨eq,p,g⟩ := G
  exact (fence_cast eq C x w).mp (commit_prefix_fenced x (eq ▸ C) A N d D w _ g)

def IssueGap {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (op : Nat) (w : List (Fin n)) : Prop :=
  (∀ q,header x q=h q) ∧ ShortClearLaunch.ClearIssue C x op ∧
    (∀ e∈w,e≠RearTrace.predecessor C.root)

theorem serial_continuation_fenced {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (A : H2Ready x) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (g4 w4 g5 w5 g6 w6 : List (Fin n))
    (G4 : IssueGap C x 4 g4)
    (W4 : WriteRoll C (rawRun x g4) .stage d w4)
    (G5 : IssueGap C (rawRun (rawRun x g4) w4) 5 g5)
    (W5 : WriteRoll C (rawRun (rawRun (rawRun x g4) w4) g5) .seal d w5)
    (G6 : IssueGap C (rawRun (rawRun (rawRun (rawRun x g4) w4) g5) w5) 6 g6)
    (W6 : CommitPrefix C
      (rawRun (rawRun (rawRun (rawRun (rawRun x g4) w4) g5) w5) g6) d w6) :
    FencedTape C x (g4++(w4++(g5++(w5++(g6++w6))))) := by
  have R (p : Raw s n) (P : H2Ready p) (w : List (Fin n)) : H2Ready (rawRun p w) :=
    ready_run (by omega) p P w
  have clear (p : Raw s n) (P : H2Ready p) (op : Nat) (w : List (Fin n))
      (G : IssueGap C p op w) : FencedTape C p w :=
    clear_issue_prefix_fenced C p P (by omega) G.1 op G.2.1 w G.2.2
  apply (fence_append C x g4 _).mpr
  refine ⟨clear x A 4 g4 G4,?_⟩
  let x4 := rawRun x g4
  have A4 := R x A g4
  apply (fence_append C x4 w4 _).mpr
  refine ⟨write_roll_fenced C x4 A4 N .stage d D w4 W4,?_⟩
  let y4 := rawRun x4 w4
  have B4 := R x4 A4 w4
  apply (fence_append C y4 g5 _).mpr
  refine ⟨clear y4 B4 5 g5 G5,?_⟩
  let x5 := rawRun y4 g5
  have A5 := R y4 B4 g5
  apply (fence_append C x5 w5 _).mpr
  refine ⟨write_roll_fenced C x5 A5 N .seal d D w5 W5,?_⟩
  let y5 := rawRun x5 w5
  have B5 := R x5 A5 w5
  apply (fence_append C y5 g6 _).mpr
  exact ⟨clear y5 B5 6 g6 G6,commit_roll_fenced C _ (R y5 B5 g6) N d D w6 W6⟩

private theorem root_cast {n : Nat} {h k : Fin n→Bool} (P : h=k) (C : Chart h) :
    (P ▸ C : Chart k).root=C.root := by cases P; rfl

private theorem a_cast {n : Nat} {h k : Fin n→Bool} (P : h=k) (C : Chart h) :
    (P ▸ C : Chart k).a=C.a := by cases P; rfl

private theorem bits_cast {s n : Nat} {h k : Fin n→Bool} (P : h=k)
    (C : Chart h) (x : Raw s n) (i : Nat) :
    bits (P ▸ C : Chart k).route x i=bits C.route x i := by cases P; rfl

/-- Authentication data at the exact old pair just before the unique
COMMIT ingress, with no assumed release fence, simultaneous coherence,
or foreign scheduler restriction. -/
theorem actual_commit_guard_file {s n : Nat} (x : Raw s n)
    (A : H2Ready x) (N : 9<n) (C : Chart (header x))
    (I : ShortClearLaunch.ClearIssue C x 3)
    (w : List (Fin n)) (out : Fin 64)
    (B : ShortReadFlight.beforeConsume C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w)
    (R : ShortReadFlight.trace C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w=.consumed true out)
    (d : Fin 8) (D : descValid d.val=true)
    (g4 w4 g5 w5 g6 w6 : List (Fin n))
    (G4 : IssueGap C (rawRun x (RearTrace.predecessor C.root::w)) 4 g4)
    (W4 : WriteRoll C (rawRun (rawRun x (RearTrace.predecessor C.root::w)) g4) .stage d w4)
    (G5 : IssueGap C (rawRun (rawRun (rawRun x (RearTrace.predecessor C.root::w)) g4) w4) 5 g5)
    (W5 : WriteRoll C (rawRun (rawRun (rawRun (rawRun x (RearTrace.predecessor C.root::w)) g4) w4) g5) .seal d w5)
    (G6 : IssueGap C (rawRun (rawRun (rawRun (rawRun (rawRun x (RearTrace.predecessor C.root::w)) g4) w4) g5) w5) 6 g6)
    (W6 : CommitPrefix C
      (rawRun (rawRun (rawRun (rawRun (rawRun (rawRun x (RearTrace.predecessor C.root::w)) g4) w4) g5) w5) g6) d w6) :
    let y := rawRun x (RearTrace.predecessor C.root::w)
    let saved := (y C.root).mis1
    let z := rawRun y (g4++(w4++(g5++(w5++(g6++w6)))))
    let e := nextAt C.root (C.a-1)
    issuedDescriptor saved=d.val ∧
      saved.getLsbD 74=ShortReaderMIS1.selectedValue (z C.root).mis1 ∧
      saved.getLsbD 72=ShortReaderMIS1.selectedValue (z (nextAt C.root (C.a+C.b))).mis1 ∧
      (kField 0).read (z e).mis1=encode (ShortWritePacketCodec.writeFwd 6 d false) := by
  dsimp only
  let y := rawRun x (RearTrace.predecessor C.root::w)
  let z := rawRun y (g4++(w4++(g5++(w5++(g6++w6)))))
  have AY : H2Ready y := ready_run (by omega) x A _
  have F := serial_continuation_fenced C y AY N d D g4 w4 g5 w5 g6 w6 G4 W4 G5 W5 G6 W6
  have Bits := read_file_matches_outer_pair x A C N I w _ out B R F
  let x4 := rawRun y g4
  have File := (ShortWriteFileSplice.clear_issue_file_nondoors C y AY G4.1
    (by omega) 4 G4.2.1 g4 G4.2.2).2
  obtain ⟨eq4,h4⟩ := W4
  have D4 := ShortWriteFileSplice.generated_descriptor h4
  rw [root_cast eq4 C] at D4
  have Key := ShortWriteFileSplice.descriptor_of_same_file _ _ File
  refine ⟨(D4.trans Key).symm,?_,?_,?_⟩
  · have H := Bits.1
    exact (ShortReadResult.file_bit (y C.root).mis1 2 (by decide)).trans H
  · have H := Bits.2
    exact (ShortReadResult.file_bit (y C.root).mis1 0 (by decide)).trans H
  let x6 := rawRun (rawRun (rawRun (rawRun x4 w4) g5) w5) g6
  have A6 : H2Ready x6 := ready_run (by omega) _ (ready_run (by omega) _
    (ready_run (by omega) _ (ready_run (by omega) _ (ready_run (by omega) _ AY g4) w4) g5) w5) g6
  obtain ⟨eq6,p,H6⟩ := W6
  let C6 : Chart (header x6) := eq6 ▸ C
  have pcs := ShortCommitFlight.generated_oneCentre x6 C6 A6 N d w6 _ H6
  change p=ShortCommitChartHop.Status.pending ↔ C.a-1≤C6.a-1 at pcs
  have CA : C6.a=C.a := a_cast eq6 C
  have pending := pcs.mpr (by simp [CA])
  have Act := (ShortCommitFlight.generated_receipt x6 C6 A6 N d D w6 _ H6).1
  have Wire : bits C6.route (rawRun x6 w6) (C.a-1)=encode (ShortCommitChartHop.packet d p) :=
    Act.2.2.2.1
  rw [bits_cast eq6 C,pending] at Wire
  have E : z=rawRun x6 w6 := by
    unfold z x6 x4 rawRun
    simp only [BStarResetSchedule.run_append]
  rw [←E] at Wire
  have H := ShortPublishChart.commit_centre_pair x z A C N (fun q=>
    ((header_run (by omega) y AY.1 _).2 q).trans ((header_run (by omega) x A.1 _).2 q))
  change (kField (C.route.port (C.a-1))).read (z (nextAt C.root (C.a-1))).mis1=_ at Wire
  rw [H.2.2.1] at Wire
  exact Wire

end L4.ShortMIS1ReadLease

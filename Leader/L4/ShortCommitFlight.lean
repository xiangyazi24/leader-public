import Leader.L4.ShortCommitChartForward

namespace L4.ShortCommitFlight
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetFlow ShortResetChart ShortResetCycle ShortResetForwardH2
open ShortCommitChartHop ShortCanonicalReverseChart
open ShortControllerEntrance ShortOwnerSourceTable

inductive Flight where
  | front (i : Nat) (status : Status)
  | back (i : Nat) (status : Status)
  | done (status : Status)

def live : Flight → Prop
  | .done _ => False
  | _ => True

def next {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (d : Fin 8) (x : Raw s n) (e : Fin n) : Flight → Flight
  | .front i p =>
    if e=nextAt C.root i then
      if i+1<C.L then .front (i+1) (advance d C x i p)
      else .back i p
    else .front i p
  | .back i p =>
    match nextStage C e (.rev i) with
    | .rev j => .back j p
    | _ => .done p
  | .done p => .done p

def Active {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (d : Fin 8) (x : Raw s n) : Flight → Prop
  | .front i p => i<C.L ∧ Wait x C.root 6 ∧ TrailPrefix C.route x i ∧
      bits C.route x i=encode (packet d p) ∧ ShortHelloForward.ClearSuffix C.route x i
  | .back i p => Returning C x 6 (reply p) i
  | .done _ => ShortEmptyOwnership.Clear C x ∧
      pc (x C.root).mis1=8

theorem launch {s n : Nat} {h : Fin n → Bool} (C : Chart h) 
    (x : Raw s n) (heads : ∀ q,header x q=h q)
    (A : ShortClearLaunch.ClearIssue C x 6) :
    ∃ d : Fin 8, descValid d.val=true ∧ d.val=issuedDescriptor (x C.root).mis1 ∧
      Active C d (rawNext s x (RearTrace.predecessor C.root)) (.front 0 .pending) := by
  obtain ⟨B,D⟩ := ShortWritePacketCodec.issued_descriptor_valid (x C.root).mis1
  let d : Fin 8 := ⟨_,B⟩
  have F := ShortClearLaunch.clean_launch C x heads 6 A
  refine ⟨d,D,rfl,C.positive,⟨F.1,F.2.1⟩,fun j J=>False.elim (by omega),?_,F.2.2.2⟩
  exact F.2.2.1.trans rfl



/-- On one actual mark, the front/back invariant advances together with
a receipt if a live centre departure was taken on that mark. -/
theorem step {s n : Nat} (x0 x : Raw s n) (X0 : H2Ready x0)
    (C : Chart (header x0)) (N : 9<n) (heads : ∀ q,header x q=header x0 q)
    (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (f : Flight) (L : live f) (A : Active C d x f) :
    Active C d (rawNext s x e) (next C d x e f) ∧
      (∀ p, f=.front (C.a-1) p → e=nextAt C.root (C.a-1) →
        advance d C x (C.a-1) p=.applied → Publication d x e) := by
  have sep := edge_sep (by omega : 1<n) e
  have geom := ShortPublishChart.commit_centre x0 x X0 C N heads
  cases f with
  | done => exact False.elim L
  | front i p =>
    obtain ⟨I,W,Tp,Fp,S⟩ := A
    have U := ShortCommitChartForward.forward_step x0 x X0 C N e heads d p D
      W.1 W.2 i I Tp Fp
    have W' := wait_held_step x C.root e sep ((heads _).trans C.rootHeader) (by decide : 6<7) W (fun _=>by
      have Q : slot C.route x 0=T ∨ slot C.route x 0=packet d p := by
        by_cases Z : i=0
        · subst i
          exact .inr (slot_of_bits _ _ _ _ (packet_decode d D p) Fp)
        · exact .inl (slot_of_bits _ _ _ T trail_decode (Tp 0 (by omega)))
      have H := (heads C.root).trans C.rootHeader
      have Q' : oldK true (x C.root).mis1 0=T ∨ oldK true (x C.root).mis1 0=packet d p := by
        change oldK (header x C.root) (x C.root).mis1 (ShortResetChart.lane C.a C.b 0)=T ∨
          oldK (header x C.root) (x C.root).mis1 (ShortResetChart.lane C.a C.b 0)=_ at Q
        rwa [H,C.rootPort] at Q
      rcases Q' with P|P
      · exact .inl (by rw [P]; rfl)
      · exact .inr (by rw [P,packet_tag]))
    have S' := ShortHelloForward.clear_suffix_step C.route x e sep heads i S
    refine ⟨?_,?_⟩
    · by_cases E : e=nextAt C.root i
      · by_cases J : i+1<C.L
        · simp only [next,if_pos E,if_pos J,Active] 
          dsimp only at U
          simp only [if_pos E,if_pos J] at U
          refine ⟨J,W',?_,U.2.2.1,?_⟩
          · intro j JJ
            by_cases eq : j=i
            · simpa only [eq] using U.2.1
            · exact U.1 j (by omega)
          · have EE : e=nextAt C.route.root i := E
            simpa only [ShortHelloForward.ahead,if_pos EE] using S'
        · simp only [next,if_pos E,if_neg J,Active]
          dsimp only at U
          simp only [if_pos E,if_neg J] at U
          refine ⟨I,W',?_⟩
          intro j Q
          change bits C.route (rawNext s x e) j=encode (trailAt (reply p) i j)
          by_cases Cj : j<i
          · simpa only [trailAt,if_pos Cj] using U.1 j Cj
          · have eq : j=i := by omega
            subst j
            simpa [trailAt] using U.2
      · simp only [next,if_neg E,Active]
        dsimp only at U
        simp only [if_neg E] at U
        have EE : e≠nextAt C.route.root i := E
        exact ⟨I,W',U.1,U.2,by simpa only [ShortHelloForward.ahead,if_neg EE] using S'⟩
    · intro b F M Q
      cases F
      dsimp only at U
      rw [if_pos M,if_pos geom.1] at U
      exact U.2.2.2 rfl Q
  | back i p =>
    refine ⟨?_,fun _ F=>by contradiction⟩
    have U := returning_step C x (by omega) heads e i (by decide : 6<7) A
    dsimp only at U
    cases S : nextStage C e (.rev i) with
    | fwd j => rw [S] at U; exact False.elim U
    | rev j => simpa only [next,S,Active] using U
    | done =>
      rw [S] at U
      have J : i=0 ∧ rightNeighbor e=C.root := by
        cases i with
        | zero =>
          by_cases E : rightNeighbor e=C.root
          · exact ⟨rfl,E⟩
          · simp [nextStage,E] at S
        | succ i =>
          by_cases E : e=nextAt C.root i <;> simp [nextStage,E] at S
      obtain ⟨rfl,H⟩ := J
      obtain ⟨W,K⟩ := consume_old C x e H A
      have head : header x (rightNeighbor e)=true := by rw [H,heads,C.rootHeader]
      have old : oldK true (x (rightNeighbor e)).mis1 0=(reply p).token := by
        unfold oldK
        rw [K,(reply p).decode_encode]
      have B := raw_wait_exit_table x e sep head 6 W.1 W.2 (by decide : 6<7)
        (by rw [old,held,(reply p).tag]; decide)
      have PC := B.2
      rw [H] at PC old
      simp only [next,S,Active]
      refine ⟨U.1,?_⟩
      rw [PC,old]
      cases p <;> decide


def SampledPublication {s n : Nat} (d : Fin 8) (x : Raw s n) (e : Fin n)
    (tape : List (Fin n)) : Prop :=
  ∃ lead tail : List (Fin n), tape=lead++e::tail ∧ Publication d (rawRun x lead) e

theorem sampled_publication_extend {s n : Nat} (d : Fin 8) (x : Raw s n) (e : Fin n)
    (tape suffix : List (Fin n)) (P : SampledPublication d x e tape) :
    SampledPublication d x e (tape++suffix) := by
  obtain ⟨lead,tail,T,E⟩ := P
  exact ⟨lead,tail++suffix,by rw [T,List.append_assoc]; rfl,E⟩

theorem sampled_publication_record {s n : Nat} (d : Fin 8) (x : Raw s n) (e : Fin n)
    (marks : List (Fin n)) (P : Publication d (rawRun x marks) e) :
    SampledPublication d x e (marks++[e]) :=
  ⟨marks,[],rfl,P⟩

def NeedsReceipt {n : Nat} {h : Fin n → Bool} (C : Chart h) : Flight → Prop
  | .front i p => C.a-1<i ∧ p=.applied
  | .back _ p | .done p => p=.applied

/-- Fresh launch followed by actual marks, stopping at the first
consume. Only the literal old file can select the descriptor. -/
inductive Generated {s n : Nat} (x0 : Raw s n) (C : Chart (header x0))
    (d : Fin 8) : List (Fin n) → Flight → Prop where
  | launch : ShortClearLaunch.ClearIssue C x0 6 →
      d.val=issuedDescriptor (x0 C.root).mis1 →
      Generated x0 C d [RearTrace.predecessor C.root] (.front 0 .pending)
  | snoc {w : List (Fin n)} {f : Flight} (e : Fin n) :
      Generated x0 C d w f → live f →
      Generated x0 C d (w++[e]) (next C d (rawRun x0 w) e f)

def FrontInRange (length : Nat) : Flight → Prop
  | .front i _ => i<length
  | _ => True

private theorem receipt_progress {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (d : Fin 8) (e : Fin n) (f : Flight)
    (I : C.a-1+1<C.L)
    (F : FrontInRange C.L f)
    (R : NeedsReceipt C (next C d x e f)) :
    NeedsReceipt C f ∨
      ∃ p, f=.front (C.a-1) p ∧ e=nextAt C.root (C.a-1) ∧ advance d C x (C.a-1) p=.applied := by
  cases f with
  | done p =>
    exact .inl R
  | back i p =>
    left
    cases E : nextStage C e (.rev i) <;> simpa only [next,E,NeedsReceipt] using R
  | front i p =>
    by_cases E : e=nextAt C.root i
    · by_cases J : i+1<C.L
      · simp only [next,if_pos E,if_pos J,NeedsReceipt] at R
        by_cases M : i=C.a-1
        · subst i; exact .inr ⟨p,rfl,E,R.2⟩
        · left
          refine ⟨by omega,?_⟩
          simpa only [ShortCommitChartHop.advance,if_neg M] using R.2
      · simp only [next,if_pos E,if_neg J,NeedsReceipt] at R
        exact .inl ⟨by omega,R⟩
    · exact .inl (by simpa only [next,if_neg E] using R)

private theorem active_front_bound {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (d : Fin 8) (f : Flight) (A : Active C d x f) :
    FrontInRange C.L f := by
  cases f with
  | front => exact A.1
  | _ => trivial

/-- The ancestor's raw cut is carried through every actual mark, not
just the selected chart labels. The final receipt is historical; no
claim is made that the bank or seal is unchanged by later marks. -/
theorem generated_receipt {s n : Nat} (x0 : Raw s n) (C : Chart (header x0))
    (X0 : H2Ready x0) (N : 9<n) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : Flight) (G : Generated x0 C d w f) :
    Active C d (rawRun x0 w) f ∧
      (NeedsReceipt C f → SampledPublication d x0 (nextAt C.root (C.a-1)) w) := by
  induction G with
  | launch A E =>
    obtain ⟨dd,_,EE,L⟩ := launch C x0 (fun _=>rfl) A
    have B : dd=d := Fin.ext (EE.trans E.symm)
    subst dd
    exact ⟨L,fun H=>False.elim ((Nat.not_lt_zero _) H.1)⟩
  | @snoc w f e G L ih =>
    let x := rawRun x0 w
    have heads : ∀ q,header x q=header x0 q := (header_run (by omega) x0 X0.1 w).2
    have geo := ShortPublishChart.commit_centre x0 x X0 C N heads
    have K := step x0 x X0 C N heads d D e f L ih.1
    have APP : rawRun x0 (w++[e])=rawNext s x e :=
      BStarResetSchedule.run_append _ _ _ _
    rw [APP]
    refine ⟨K.1,fun H=>?_⟩
    have I := active_front_bound C x d f ih.1
    rcases receipt_progress C x d e f geo.1 I H with R|⟨p,F,E,V⟩
    · exact sampled_publication_extend d x0 _ w [e] (ih.2 R)
    · exact E ▸ sampled_publication_record d x0 e w (K.2 p F E V)

theorem consume_clears {s n : Nat} (x0 : Raw s n) (C : Chart (header x0))
    (X0 : H2Ready x0) (N : 9<n) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (p : Status) (G : Generated x0 C d w (.done p)) :
    ShortEmptyOwnership.Clear C (rawRun x0 w) ∧
      pc (rawRun x0 w C.root).mis1=8 ∧
      (p=.applied → SampledPublication d x0 (nextAt C.root (C.a-1)) w) := by
  obtain ⟨A,B⟩ := generated_receipt x0 C X0 N d D w _ G
  exact ⟨A.1,A.2,B⟩

/-- The unique live front is unapplied until the centre mark. Once the
centre has been crossed, there is no return to the pending phase. -/
def OneCentre {n : Nat} {h : Fin n→Bool} (C : Chart h) : Flight→Prop
  | .front i p => (p=.pending ↔ i≤C.a-1)
  | .back _ p | .done p => p≠.pending

theorem oneCentre_step {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (room : C.a-1+1<C.L) (x : Raw s n) (d : Fin 8) (e : Fin n) (f : Flight)
    (A : OneCentre C f) : OneCentre C (next C d x e f) := by
  cases f with
  | done => exact A
  | back i p =>
    cases H : nextStage C e (.rev i) <;> simpa only [next,H,OneCentre] using A
  | front i p =>
    dsimp only [OneCentre] at A
    by_cases E : e=nextAt C.root i
    · by_cases L : i+1<C.L
      · simp only [next,if_pos E,if_pos L,OneCentre]
        by_cases H : i=C.a-1
        · unfold ShortCommitChartHop.advance
          rw [if_pos H]
          have NL : ¬ i+1≤C.a-1 := by omega
          split <;> simp [NL]
        · rw [ShortCommitChartHop.advance,if_neg H,A]
          omega
      · simp only [next,if_pos E,if_neg L,OneCentre]
        intro P
        have K := A.mp P
        omega
    · simpa only [next,if_neg E,OneCentre] using A

theorem generated_oneCentre {s n : Nat} (x0 : Raw s n) (C : Chart (header x0))
    (X0 : H2Ready x0) (N : 9<n) (d : Fin 8)
    (w : List (Fin n)) (f : Flight) (G : Generated x0 C d w f) :
    OneCentre C f := by
  induction G with
  | launch => simp [OneCentre]
  | snoc e _ _ ih =>
    apply oneCentre_step _ _ _ _ _ _ ih
    exact (ShortPublishChart.commit_centre x0 x0 X0 C N (fun _=>rfl)).1

theorem no_orphan_of_clear {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n)
    (A : ShortEmptyOwnership.Clear C x) :
    ∀ i, i<C.L → slot C.route x i=E := by
  intro i H
  apply slot_of_bits
  · intro g
    cases g <;> decide
  · exact A i H

#print axioms oneCentre_step
#print axioms generated_oneCentre
#print axioms no_orphan_of_clear
#print axioms launch
#print axioms step
#print axioms generated_receipt
#print axioms consume_clears
-- CHECK: ShortCommitFlight.lean:56; original opens and options unchanged.
theorem step_fixed {s n : Nat} {h : Fin n → Bool} (x : Raw s n)
    (C : Chart h) (N : 9<n) (heads : ∀ q, header x q=h q)
    (geom : C.a-1+1<C.L ∧
      ∀ k, k+1<C.L →
        (header x (rightNeighbor (nextAt C.root k))=true ∧
          C.route.port k=0 ∧ C.route.port (k+1)=1 ↔ k=C.a-1))
    (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (f : Flight) (L : live f) (A : Active C d x f) :
    Active C d (rawNext s x e) (next C d x e f) ∧
      (∀ p, f=.front (C.a-1) p → e=nextAt C.root (C.a-1) →
        advance d C x (C.a-1) p=.applied → Publication d x e) := by
  have sep := edge_sep (by omega : 1<n) e
  cases f with
  | done => exact False.elim L
  | front i p =>
    obtain ⟨I,W,Tp,Fp,S⟩ := A
    have U := ShortCommitChartForward.forward_step_fixed x C N e heads geom d p D
      W.1 W.2 i I Tp Fp
    have W' := wait_held_step x C.root e sep ((heads _).trans C.rootHeader) (by decide : 6<7) W (fun _=>by
      have Q : slot C.route x 0=T ∨ slot C.route x 0=packet d p := by
        by_cases Z : i=0
        · subst i
          exact .inr (slot_of_bits _ _ _ _ (packet_decode d D p) Fp)
        · exact .inl (slot_of_bits _ _ _ T trail_decode (Tp 0 (by omega)))
      have H := (heads C.root).trans C.rootHeader
      have Q' : oldK true (x C.root).mis1 0=T ∨ oldK true (x C.root).mis1 0=packet d p := by
        change oldK (header x C.root) (x C.root).mis1 (ShortResetChart.lane C.a C.b 0)=T ∨
          oldK (header x C.root) (x C.root).mis1 (ShortResetChart.lane C.a C.b 0)=_ at Q
        rwa [H,C.rootPort] at Q
      rcases Q' with P|P
      · exact .inl (by rw [P]; rfl)
      · exact .inr (by rw [P,packet_tag]))
    have S' := ShortHelloForward.clear_suffix_step C.route x e sep heads i S
    refine ⟨?_,?_⟩
    · by_cases E : e=nextAt C.root i
      · by_cases J : i+1<C.L
        · simp only [next,if_pos E,if_pos J,Active] 
          dsimp only at U
          simp only [if_pos E,if_pos J] at U
          refine ⟨J,W',?_,U.2.2.1,?_⟩
          · intro j JJ
            by_cases eq : j=i
            · simpa only [eq] using U.2.1
            · exact U.1 j (by omega)
          · have EE : e=nextAt C.route.root i := E
            simpa only [ShortHelloForward.ahead,if_pos EE] using S'
        · simp only [next,if_pos E,if_neg J,Active]
          dsimp only at U
          simp only [if_pos E,if_neg J] at U
          refine ⟨I,W',?_⟩
          intro j Q
          change bits C.route (rawNext s x e) j=encode (trailAt (reply p) i j)
          by_cases Cj : j<i
          · simpa only [trailAt,if_pos Cj] using U.1 j Cj
          · have eq : j=i := by omega
            subst j
            simpa [trailAt] using U.2
      · simp only [next,if_neg E,Active]
        dsimp only at U
        simp only [if_neg E] at U
        have EE : e≠nextAt C.route.root i := E
        exact ⟨I,W',U.1,U.2,by simpa only [ShortHelloForward.ahead,if_neg EE] using S'⟩
    · intro b F M Q
      cases F
      dsimp only at U
      rw [if_pos M,if_pos geom.1] at U
      exact U.2.2.2 rfl Q
  | back i p =>
    refine ⟨?_,fun _ F=>by contradiction⟩
    have U := returning_step C x (by omega) heads e i (by decide : 6<7) A
    dsimp only at U
    cases S : nextStage C e (.rev i) with
    | fwd j => rw [S] at U; exact False.elim U
    | rev j => simpa only [next,S,Active] using U
    | done =>
      rw [S] at U
      have J : i=0 ∧ rightNeighbor e=C.root := by
        cases i with
        | zero =>
          by_cases E : rightNeighbor e=C.root
          · exact ⟨rfl,E⟩
          · simp [nextStage,E] at S
        | succ i =>
          by_cases E : e=nextAt C.root i <;> simp [nextStage,E] at S
      obtain ⟨rfl,H⟩ := J
      obtain ⟨W,K⟩ := consume_old C x e H A
      have head : header x (rightNeighbor e)=true := by rw [H,heads,C.rootHeader]
      have old : oldK true (x (rightNeighbor e)).mis1 0=(reply p).token := by
        unfold oldK
        rw [K,(reply p).decode_encode]
      have B := raw_wait_exit_table x e sep head 6 W.1 W.2 (by decide : 6<7)
        (by rw [old,held,(reply p).tag]; decide)
      have PC := B.2
      rw [H] at PC old
      simp only [next,S,Active]
      refine ⟨U.1,?_⟩
      rw [PC,old]
      cases p <;> decide

#print axioms step_fixed
end L4.ShortCommitFlight

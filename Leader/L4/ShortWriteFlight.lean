import Leader.L4.ShortWriteChartForward

namespace L4.ShortWriteFlight
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetFlow ShortResetChart ShortResetCycle ShortResetForwardH2
open ShortWriteCentreWitness ShortWriteChartHop ShortCanonicalReverseChart
open ShortControllerEntrance ShortOwnerSourceTable

inductive Flight where
  | front (i : Nat) (bad : Bool)
  | back (i : Nat) (bad : Bool)
  | done (bad : Bool)

def live : Flight → Prop
  | .done _ => False
  | _ => True

def next {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (cmd : Cmd) (d : Fin 8) (x : Raw s n) (e : Fin n) : Flight → Flight
  | .front i bad =>
    if e=nextAt C.root i then
      if i+1<C.L then .front (i+1) (advanceBad cmd d C x i bad)
      else .back i bad
    else .front i bad
  | .back i bad =>
    match nextStage C e (.rev i) with
    | .rev j => .back j bad
    | _ => .done bad
  | .done bad => .done bad

def Active {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (cmd : Cmd) (d : Fin 8) (x : Raw s n) : Flight → Prop
  | .front i bad => i<C.L ∧ Wait x C.root cmd.op ∧ TrailPrefix C.route x i ∧
      bits C.route x i=encode (packet cmd d bad) ∧ ShortHelloForward.ClearSuffix C.route x i
  | .back i bad => Returning C x cmd.op (reply cmd bad) i
  | .done bad => ShortEmptyOwnership.Clear C x ∧
      pc (x C.root).mis1=(if bad then 8 else 9+cmd.op)

theorem launch {s n : Nat} {h : Fin n → Bool} (C : Chart h) (cmd : Cmd)
    (x : Raw s n) (heads : ∀ q,header x q=h q)
    (A : ShortClearLaunch.ClearIssue C x cmd.op) :
    ∃ d : Fin 8, descValid d.val=true ∧ d.val=issuedDescriptor (x C.root).mis1 ∧
      Active C cmd d (rawNext s x (RearTrace.predecessor C.root)) (.front 0 false) := by
  obtain ⟨B,D⟩ := ShortWritePacketCodec.issued_descriptor_valid (x C.root).mis1
  let d : Fin 8 := ⟨_,B⟩
  have F := ShortClearLaunch.clean_launch C x heads cmd.op A
  refine ⟨d,D,rfl,C.positive,⟨F.1,F.2.1⟩,fun j J=>False.elim (by omega),?_,F.2.2.2⟩
  exact F.2.2.1.trans (by cases cmd <;> rfl)

theorem cmd_bound (cmd : Cmd) : cmd.op<7 := by cases cmd <;> decide

/-- On one actual mark, the front/back invariant advances together with
a receipt if a live centre departure was taken on that mark. -/
theorem step {s n : Nat} (x0 x : Raw s n) (X0 : H2Ready x0) (X : H2Ready x)
    (C : Chart (header x0)) (N : 9<n) (heads : ∀ q,header x q=header x0 q)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (f : Flight) (L : live f) (A : Active C cmd d x f) :
    Active C cmd d (rawNext s x e) (next C cmd d x e f) ∧
      (∀ bad, f=.front C.a bad → e=nextAt C.root C.a →
        advanceBad cmd d C x C.a bad=false → CentreEffect cmd d x e) := by
  have sep := edge_sep (by omega : 1<n) e
  have geom := ShortPublishChart.stage_seal_centre x0 x X0 X C N heads
  cases f with
  | done => exact False.elim L
  | front i bad =>
    obtain ⟨I,W,Tp,Fp,S⟩ := A
    have U := ShortWriteChartForward.forward_step x0 x X0 X C N e heads cmd d bad D
      W.1 W.2 i I Tp Fp
    have W' := wait_held_step x C.root e sep ((heads _).trans C.rootHeader) (cmd_bound cmd) W (fun _=>by
      have Q : slot C.route x 0=T ∨ slot C.route x 0=packet cmd d bad := by
        by_cases Z : i=0
        · subst i
          exact .inr (slot_of_bits _ _ _ _ (packet_decode cmd d D bad) Fp)
        · exact .inl (slot_of_bits _ _ _ T trail_decode (Tp 0 (by omega)))
      have H := (heads C.root).trans C.rootHeader
      have Q' : oldK true (x C.root).mis1 0=T ∨ oldK true (x C.root).mis1 0=packet cmd d bad := by
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
          change bits C.route (rawNext s x e) j=encode (trailAt (reply cmd bad) i j)
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
  | back i bad =>
    refine ⟨?_,fun _ F=>by contradiction⟩
    have U := returning_step C x (by omega) heads e i (cmd_bound cmd) A
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
      have old : oldK true (x (rightNeighbor e)).mis1 0=(reply cmd bad).token := by
        unfold oldK
        rw [K,(reply cmd bad).decode_encode]
      have B := raw_wait_exit_table x e sep head cmd.op W.1 W.2 (cmd_bound cmd)
        (by rw [old,held,(reply cmd bad).tag]; decide)
      have PC := B.2
      rw [H] at PC old
      simp only [next,S,Active]
      refine ⟨U.1,?_⟩
      rw [PC,old]
      cases cmd <;> cases bad <;> decide

def NeedsReceipt {n : Nat} {h : Fin n → Bool} (C : Chart h) : Flight → Prop
  | .front i bad => C.a<i ∧ bad=false
  | .back _ bad | .done bad => bad=false

/-- Fresh launch followed by actual marks, stopping at the first
consume. Only the literal old file can select the descriptor. -/
inductive Generated {s n : Nat} (x0 : Raw s n) (C : Chart (header x0))
    (cmd : Cmd) (d : Fin 8) : List (Fin n) → Flight → Prop where
  | launch : ShortClearLaunch.ClearIssue C x0 cmd.op →
      d.val=issuedDescriptor (x0 C.root).mis1 →
      Generated x0 C cmd d [RearTrace.predecessor C.root] (.front 0 false)
  | snoc {w : List (Fin n)} {f : Flight} (e : Fin n) :
      Generated x0 C cmd d w f → live f →
      Generated x0 C cmd d (w++[e]) (next C cmd d (rawRun x0 w) e f)

def FrontInRange (length : Nat) : Flight → Prop
  | .front i _ => i<length
  | _ => True

private theorem receipt_progress {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (cmd : Cmd) (d : Fin 8) (e : Fin n) (f : Flight)
    (I : C.a+1<C.L)
    (F : FrontInRange C.L f)
    (R : NeedsReceipt C (next C cmd d x e f)) :
    NeedsReceipt C f ∨
      ∃ bad, f=.front C.a bad ∧ e=nextAt C.root C.a ∧ advanceBad cmd d C x C.a bad=false := by
  cases f with
  | done bad =>
    exact .inl R
  | back i bad =>
    left
    cases E : nextStage C e (.rev i) <;> simpa only [next,E,NeedsReceipt] using R
  | front i bad =>
    by_cases E : e=nextAt C.root i
    · by_cases J : i+1<C.L
      · simp only [next,if_pos E,if_pos J,NeedsReceipt] at R
        by_cases M : i=C.a
        · subst i; exact .inr ⟨bad,rfl,E,R.2⟩
        · left
          refine ⟨by omega,?_⟩
          cases bad <;> simp [advanceBad] at R ⊢
      · simp only [next,if_pos E,if_neg J,NeedsReceipt] at R
        exact .inl ⟨by omega,R⟩
    · exact .inl (by simpa only [next,if_neg E] using R)

private theorem active_front_bound {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (cmd : Cmd) (d : Fin 8) (f : Flight) (A : Active C cmd d x f) :
    FrontInRange C.L f := by
  cases f with
  | front => exact A.1
  | _ => trivial

/-- The ancestor's raw cut is carried through every actual mark, not
just the selected chart labels. The final receipt is historical; no
claim is made that the bank or seal is unchanged by later marks. -/
theorem generated_receipt {s n : Nat} (x0 : Raw s n) (C : Chart (header x0))
    (X0 : H2Ready x0) (N : 9<n) (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : Flight) (G : Generated x0 C cmd d w f) :
    Active C cmd d (rawRun x0 w) f ∧
      (NeedsReceipt C f → SampledEffect cmd d x0 (nextAt C.root C.a) w) := by
  induction G with
  | launch A E =>
    obtain ⟨dd,_,EE,L⟩ := launch C cmd x0 (fun _=>rfl) A
    have B : dd=d := Fin.ext (EE.trans E.symm)
    subst dd
    exact ⟨L,fun H=>False.elim ((Nat.not_lt_zero _) H.1)⟩
  | @snoc w f e G L ih =>
    let x := rawRun x0 w
    have X : H2Ready x := ready_run (by omega) x0 X0 w
    have heads : ∀ q,header x q=header x0 q := (header_run (by omega) x0 X0.1 w).2
    have geo := ShortPublishChart.stage_seal_centre x0 x X0 X C N heads
    have K := step x0 x X0 X C N heads cmd d D e f L ih.1
    have APP : rawRun x0 (w++[e])=rawNext s x e :=
      BStarResetSchedule.run_append _ _ _ _
    rw [APP]
    refine ⟨K.1,fun H=>?_⟩
    have I := active_front_bound C x cmd d f ih.1
    rcases receipt_progress C x cmd d e f geo.1 I H with R|⟨bad,F,E,V⟩
    · exact sampled_effect_extend cmd d x0 _ w [e] (ih.2 R)
    · exact E ▸ sampled_effect_record cmd d x0 e w (K.2 bad F E V)

theorem stage_ack_after_centre {s n : Nat} (x0 : Raw s n) (C : Chart (header x0))
    (X0 : H2Ready x0) (N : 9<n) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (G : Generated x0 C .stage d w (.done false)) :
    ShortEmptyOwnership.Clear C (rawRun x0 w) ∧
      pc (rawRun x0 w C.root).mis1=13 ∧
      SampledEffect .stage d x0 (nextAt C.root C.a) w := by
  obtain ⟨A,R⟩ := generated_receipt x0 C X0 N .stage d D w _ G
  exact ⟨A.1,A.2,R rfl⟩

theorem seal_ack_after_centre {s n : Nat} (x0 : Raw s n) (C : Chart (header x0))
    (X0 : H2Ready x0) (N : 9<n) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (G : Generated x0 C .seal d w (.done false)) :
    ShortEmptyOwnership.Clear C (rawRun x0 w) ∧
      pc (rawRun x0 w C.root).mis1=14 ∧
      SampledEffect .seal d x0 (nextAt C.root C.a) w := by
  obtain ⟨A,R⟩ := generated_receipt x0 C X0 N .seal d D w _ G
  exact ⟨A.1,A.2,R rfl⟩

-- CHECK: ShortWriteFlight.lean:56; original opens and options unchanged.
theorem step_fixed {s n : Nat} {h : Fin n → Bool} (x : Raw s n)
    (C : Chart h) (N : 9<n) (heads : ∀ q, header x q=h q)
    (geom : C.a+1<C.L ∧
      ∀ k, k<C.L →
        (header x (nextAt C.root k)=true ∧ C.route.port k=1 ↔ k=C.a))
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (f : Flight) (L : live f) (A : Active C cmd d x f) :
    Active C cmd d (rawNext s x e) (next C cmd d x e f) ∧
      (∀ bad, f=.front C.a bad → e=nextAt C.root C.a →
        advanceBad cmd d C x C.a bad=false → CentreEffect cmd d x e) := by
  have sep := edge_sep (by omega : 1<n) e
  cases f with
  | done => exact False.elim L
  | front i bad =>
    obtain ⟨I,W,Tp,Fp,S⟩ := A
    have U := ShortWriteChartForward.forward_step_fixed x C N e heads geom cmd d bad D
      W.1 W.2 i I Tp Fp
    have W' := wait_held_step x C.root e sep ((heads _).trans C.rootHeader) (cmd_bound cmd) W (fun _=>by
      have Q : slot C.route x 0=T ∨ slot C.route x 0=packet cmd d bad := by
        by_cases Z : i=0
        · subst i
          exact .inr (slot_of_bits _ _ _ _ (packet_decode cmd d D bad) Fp)
        · exact .inl (slot_of_bits _ _ _ T trail_decode (Tp 0 (by omega)))
      have H := (heads C.root).trans C.rootHeader
      have Q' : oldK true (x C.root).mis1 0=T ∨ oldK true (x C.root).mis1 0=packet cmd d bad := by
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
          change bits C.route (rawNext s x e) j=encode (trailAt (reply cmd bad) i j)
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
  | back i bad =>
    refine ⟨?_,fun _ F=>by contradiction⟩
    have U := returning_step C x (by omega) heads e i (cmd_bound cmd) A
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
      have old : oldK true (x (rightNeighbor e)).mis1 0=(reply cmd bad).token := by
        unfold oldK
        rw [K,(reply cmd bad).decode_encode]
      have B := raw_wait_exit_table x e sep head cmd.op W.1 W.2 (cmd_bound cmd)
        (by rw [old,held,(reply cmd bad).tag]; decide)
      have PC := B.2
      rw [H] at PC old
      simp only [next,S,Active]
      refine ⟨U.1,?_⟩
      rw [PC,old]
      cases cmd <;> cases bad <;> decide

end L4.ShortWriteFlight

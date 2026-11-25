import Leader.L4.ShortOwnerEpochJS
import Leader.L4.ShortEpochResetOrigin
import Leader.L4.ShortAllOwnerSound
import Leader.L4.PhysicalH1Neighbors
import Leader.L4.ShortPublicationOwner

namespace L4.ShortClassifiedOwnerAuth
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetFlow ShortResetChart ShortResetCycle
open ShortResetForwardH2 ShortClearLaunch ShortOwnerEpochJS

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {s n : Nat} {h : Fin n → Bool}

/-- Exactly the first four clauses of the old literal selector guard.
    This predicate is on the actual decoded token, not the source PC. -/
def Fresh (t : Token) : Prop :=
  t.tag=2 ∧ t.fault=false ∧ t.opcode=6 ∧ t.applied=false

private theorem not_fresh_tag {t : Token} (A : t.tag≠2) : ¬Fresh t :=
  fun F => A F.1

private theorem not_fresh_op {t : Token} (A : t.opcode≠6) : ¬Fresh t :=
  fun F => A F.2.2.1

private theorem not_fresh_applied {t : Token} (A : t.applied=true) : ¬Fresh t :=
  fun F => Bool.noConfusion (A.symm.trans F.2.2.2)

private theorem not_fresh_fault {t : Token} (A : t.fault=true) : ¬Fresh t :=
  fun F => Bool.noConfusion (A.symm.trans F.2.1)

private theorem not_fresh_E : ¬Fresh E := not_fresh_tag (by decide)
private theorem not_fresh_T : ¬Fresh T := not_fresh_tag (by decide)

/-- A canonical empty route cannot contain a fresh COMMIT. -/
theorem clear_no_fresh (C : Chart h) (x : Raw s n)
    (A : ShortEmptyOwnership.Clear C x) (k : Nat) (K : k<C.L) :
    ¬ Fresh (slot C.route x k) := by
  rw [slot_of_bits C.route x k E empty_decode (A k K)]
  exact not_fresh_E

/-- The only possible fresh token in the entire owner rail is its
    unique current front, not a T predecessor or an E suffix. -/
theorem fresh_rail_index (C : Chart h) (x : Raw s n)
    (i k : Nat) (t : Token) (K : k<C.L)
    (A : ShortOwnerEpochJS.Rail C x i t) (F : Fresh (slot C.route x k)) : k=i := by
  by_cases L : k<i
  · have W : bits C.route x k=encode T := (A k K).trans (if_pos L)
    rw [slot_of_bits C.route x k T trail_decode W] at F
    exact False.elim (not_fresh_T F)
  · by_cases Q : k=i
    · exact Q
    · have W : bits C.route x k=encode E := by
        simpa only [if_neg L,if_neg Q] using A k K
      rw [slot_of_bits C.route x k E empty_decode W] at F
      exact False.elim (not_fresh_E F)

theorem fresh_rail_token (C : Chart h) (x : Raw s n)
    (i k : Nat) (t : Token) (K : k<C.L)
    (A : ShortOwnerEpochJS.Rail C x i t) (D : ∀ g,decode g (encode t)=t)
    (F : Fresh (slot C.route x k)) : k=i ∧ Fresh t := by
  have Q := fresh_rail_index C x i k t K A F
  subst k
  have W : bits C.route x i=encode t := by
    simpa using A i K
  rw [slot_of_bits C.route x i t D W] at F
  exact ⟨rfl,F⟩

theorem rail_no_fresh (C : Chart h) (x : Raw s n)
    (i : Nat) (t : Token) (A : ShortOwnerEpochJS.Rail C x i t)
    (D : ∀ g,decode g (encode t)=t) (NF : ¬Fresh t)
    (k : Nat) (K : k<C.L) : ¬Fresh (slot C.route x k) :=
  fun F => NF (fresh_rail_token C x i k t K A D F).2

/-- This covers both ordinary generated replies and canonical fault D.
    The exact tag is 3, regardless of whether the payload is good. -/
theorem canonical_reverse_no_fresh (C : Chart h) (x : Raw s n)
    (op i : Nat) (p : ShortCanonicalReverseChart.Reply)
    (A : ShortCanonicalReverseChart.Returning C x op p i)
    (k : Nat) (K : k<C.L) : ¬Fresh (slot C.route x k) := by
  -- CHECK: ShortCanonicalReverseChart.lean:22–27,323–325 and
  -- ShortOwnerEpochJS.lean:54–56. This is the same complete wire rail.
  have R : ShortOwnerEpochJS.Rail C x i p.token := by
    intro j J
    have W := A.2.2 j J
    unfold ShortCanonicalReverseChart.trailAt at W
    change bits C.route x j = _ at W
    by_cases B : j<i
    · simpa only [if_pos B] using W
    · by_cases E : j=i
      · simpa only [if_neg B,if_pos E] using W
      · simpa only [if_neg B,if_neg E] using W
  exact rail_no_fresh C x i p.token R p.decode_encode
    (not_fresh_tag (by rw [p.tag]; decide)) k K

theorem reset_no_fresh (C : Chart h) (x : Raw s n) (st : Stage)
    (A : ResetFull C x st) (k : Nat) (K : k<C.L) :
    ¬Fresh (slot C.route x k) := by
  cases st with
  | done => exact clear_no_fresh C x A.1.1 k K
  | fwd i =>
    -- ResetFull adds the empty suffix absent from the dirty drain.
    have R := rail_of_parts C x i resetForward A.1.2.2.1
      A.1.2.2.2 A.2.2
    exact rail_no_fresh C x i resetForward R resetForward_decode
      (not_fresh_op (by decide)) k K
  | rev i =>
    have R : ShortOwnerEpochJS.Rail C x i resetReply := by
      intro j J
      have W := A.1.2.2 j J
      unfold ShortResetReverseChart.trailAt at W
      change bits C.route x j = _ at W
      by_cases B : j<i
      · simpa only [if_pos B] using W
      · by_cases E : j=i
        · simpa only [if_neg B,if_pos E] using W
        · simpa only [if_neg B,if_neg E] using W
    exact rail_no_fresh C x i resetReply R resetReply_decode
      (not_fresh_tag (by decide)) k K

theorem hello_no_fresh (C : Chart h) (x : Raw s n) (st : Stage)
    (A : ShortHelloFlight.Flight C x st) (k : Nat) (K : k<C.L) :
    ¬Fresh (slot C.route x k) := by
  cases st with
  | done => exact clear_no_fresh C x A.2.2.1 k K
  | fwd i =>
    have R := rail_of_parts C x i helloForward A.2.1.2.2.1
      A.2.1.2.2.2 A.2.2
    exact rail_no_fresh C x i helloForward R
      (fun b => (ShortHelloAdmitCodec.decode_hello b).1)
      (not_fresh_op (by decide)) k K
  | rev i =>
    have R : ShortOwnerEpochJS.Rail C x i helloReply := by
      intro j J
      have W := A.2.2.2 j J
      unfold ShortHelloReverseChart.trailAt at W
      change bits C.route x j = _ at W
      by_cases B : j<i
      · simpa only [if_pos B] using W
      · by_cases E : j=i
        · simpa only [if_neg B,if_pos E] using W
        · simpa only [if_neg B,if_neg E] using W
    exact rail_no_fresh C x i helloReply R
      (fun b => (ShortHelloAdmitCodec.decode_hello b).2)
      (not_fresh_tag (by decide)) k K

theorem admit_no_fresh (C : Chart h) (x : Raw s n) (g : Nat)
    (f : ShortAdmitFlight.State) (A : ShortAdmitFlight.Flight C x g f)
    (k : Nat) (K : k<C.L) : ¬Fresh (slot C.route x k) := by
  cases f with
  | done w => exact clear_no_fresh C x A.2.2.1 k K
  | reverse i w =>
    have R : ShortOwnerEpochJS.Rail C x i (ShortHelloAdmitCodec.admitReply w) := A.2.2.2
    exact rail_no_fresh C x i _ R
      (fun b => ShortHelloAdmitCodec.decode_admit_reply b w)
      (not_fresh_tag (by decide : (3 : Nat)≠2)) k K
  | forward i w r =>
    intro F
    have R : ShortOwnerEpochJS.Rail C x i (ShortHelloAdmitCodec.admitForward w r) := A.2.1.2.2
    have Q := fresh_rail_index C x i k _ K R F
    subst k
    have W : bits C.route x i=encode (ShortHelloAdmitCodec.admitForward w r) := by
      simpa using R i K
    have B : r<8 := by
      have V := A.2.2.2
      split at V <;> omega
    -- CHECK: ShortAdmitForward.lean:13,51–57 and
    -- ShortHelloAdmitCodec.lean:28–32. Actual atGate is used.
    have O : slot C.route x i =
        if (if ShortAdmitForward.gated C x i then 1≤r ∧ r≤5 else r=0)
        then ShortHelloAdmitCodec.admitForward w r else faultToken 2 := by
      change decode (ShortAdmitForward.gated C x i) (bits C.route x i)=_
      rw [W,ShortHelloAdmitCodec.decode_admit_forward _ w r B]
    rw [O] at F
    by_cases V : (if ShortAdmitForward.gated C x i then 1≤r ∧ r≤5 else r=0)
    · rw [if_pos V] at F
      exact not_fresh_op (by decide : (2 : Nat)≠6) F
    · rw [if_neg V] at F
      exact not_fresh_fault rfl F

theorem read_no_fresh (C : Chart h) (x : Raw s n)
    (f : ShortReadFlight.Flight) (A : ShortReadFlight.Active C x f)
    (k : Nat) (K : k<C.L) : ¬Fresh (slot C.route x k) := by
  cases f with
  | consumed ok out => exact clear_no_fresh C x A.1 k K
  | returning i ok out =>
    have R : ShortOwnerEpochJS.Rail C x i (ShortReadReturnHop.readReply ok out) := by
      intro j J
      have W := A.2.2 j J
      unfold ShortReadReverseChart.trailAt at W
      change bits C.route x j = _ at W
      by_cases B : j<i
      · simpa only [if_pos B] using W
      · by_cases E : j=i
        · simpa only [if_neg B,if_pos E] using W
        · simpa only [if_neg B,if_neg E] using W
    exact rail_no_fresh C x i _ R
      (fun b => ShortReadReturnHop.decode_readReply b ok out)
      (not_fresh_tag (by decide : (3 : Nat)≠2)) k K
  | forward i data =>
    have R := rail_of_parts C x i (readFront data) A.2.2.2.1
      A.2.2.2.2.1 A.2.2.2.2.2
    exact rail_no_fresh C x i _ R
      (fun b => ShortReadForward.decode_front b data A.2.1)
      (not_fresh_op (by decide : (3 : Nat)≠6)) k K

private theorem write_packet_no_fresh (cmd : ShortWriteCentreWitness.Cmd)
    (d : Fin 8) (bad : Bool) : ¬Fresh (ShortWriteChartHop.packet cmd d bad) := by
  cases bad <;> cases cmd <;> first
    | exact not_fresh_fault rfl
    | exact not_fresh_op (by decide : (4 : Nat)≠6)
    | exact not_fresh_op (by decide : (5 : Nat)≠6)

theorem write_no_fresh (C : Chart h) (x : Raw s n)
    (cmd : ShortWriteCentreWitness.Cmd) (d : Fin 8) (D : descValid d.val=true)
    (f : ShortWriteFlight.Flight) (A : ShortWriteFlight.Active C cmd d x f)
    (k : Nat) (K : k<C.L) : ¬Fresh (slot C.route x k) := by
  cases f with
  | done bad => exact clear_no_fresh C x A.1 k K
  | back i bad =>
    exact canonical_reverse_no_fresh C x cmd.op i
      (ShortWriteChartHop.reply cmd bad) A k K
  | front i bad =>
    have R := rail_of_parts C x i (ShortWriteChartHop.packet cmd d bad)
      A.2.2.1 A.2.2.2.1 A.2.2.2.2
    exact rail_no_fresh C x i _ R
      (ShortWriteChartHop.packet_decode cmd d D bad)
      (write_packet_no_fresh cmd d bad) k K

/-- COMMIT is the only surviving opcode, but neither an already applied
    COMMIT nor a fault nor its reverse reply can classify as fresh. -/
theorem commit_fresh_front (C : Chart h) (x : Raw s n) (d : Fin 8)
    (D : descValid d.val=true) (f : ShortCommitFlight.Flight)
    (A : ShortCommitFlight.Active C d x f) (k : Nat) (K : k<C.L)
    (F : Fresh (slot C.route x k)) : f=.front k .pending := by
  cases f with
  | done p => exact False.elim (clear_no_fresh C x A.1 k K F)
  | back i p =>
    exact False.elim (canonical_reverse_no_fresh C x 6 i
      (ShortCommitChartHop.reply p) A k K F)
  | front i p =>
    have R := rail_of_parts C x i (ShortCommitChartHop.packet d p)
      A.2.2.1 A.2.2.2.1 A.2.2.2.2
    obtain ⟨Q,Tf⟩ := fresh_rail_token C x i k _ K R
      (ShortCommitChartHop.packet_decode d D p) F
    subst k
    cases p with
    | pending => rfl
    | applied => exact False.elim (not_fresh_applied rfl Tf)
    | failed => exact False.elim (not_fresh_fault rfl Tf)

/-- Extract the exact checked J/S histories required by its
    pending_commit_auth; these are outputs, not hypotheses of the
    all-owner authentication theorem. -/
def PendingAt (C : Chart h) (x : Raw s n) (k : Nat) : Prop :=
  ∃ saved a4 a5 : Raw s n,
    ReadReceipt C saved ∧
    WriteAt C saved .stage (savedDesc C saved) a4 (.done false) ∧
    WriteAt C a4 .seal (savedDesc C saved) a5 (.done false) ∧
    CommitAt C a5 (savedDesc C saved) x (.front k .pending)

theorem post_fresh_pending (C : Chart h) (saved x : Raw s n)
    (N : 9<n) (R : ReadReceipt C saved) (P : Post C saved x)
    (k : Nat) (K : k<C.L) (F : Fresh (slot C.route x k)) :
    PendingAt C x k := by
  let d := savedDesc C saved
  have D : descValid d.val=true := savedDesc_valid C saved
  cases P with
  | gap4 A =>
    exact False.elim (clear_no_fresh C x
      (gap_current C saved x (by omega) 4 A).1.2.1 k K F)
  | stage f A L =>
    exact False.elim (write_no_fresh C x .stage d D f
      (writeAt_active C saved x N .stage d D f A) k K F)
  | gap5 a4 A B =>
    exact False.elim (clear_no_fresh C x
      (gap_current C a4 x (by omega) 5 B).1.2.1 k K F)
  | «seal» a4 f A B L =>
    exact False.elim (write_no_fresh C x .seal d D f
      (writeAt_active C a4 x N .seal d D f B) k K F)
  | gap6 a4 a5 A B G =>
    exact False.elim (clear_no_fresh C x
      (gap_current C a5 x (by omega) 6 G).1.2.1 k K F)
  | commit a4 a5 f A B G L =>
    have J := commit_fresh_front C x d D f
      (commitAt_active C a5 x N d D f G).1 k K F
    rw [J] at G
    exact ⟨saved,a4,a5,R,A,B,G⟩

/-- Exhaust every constructor of the actual checked OwnerInv, rather
    than assuming that a numeric PC describes all remote K cells. -/
theorem owner_fresh_pending (C : Chart h) (x : Raw s n)
    (N : 9<n) (g : Nat) (A : OwnerInv C x g)
    (k : Nat) (K : k<C.L) (F : Fresh (slot C.route x k)) :
    PendingAt C x k := by
  rcases A.2 with I | P | B
  · exact False.elim (clear_no_fresh C x I.2.1 k K F)
  · exact False.elim (clear_no_fresh C x P.1.2.1 k K F)
  · cases B with
    | reset st L P => exact False.elim (reset_no_fresh C x st P k K F)
    | hello st P => exact False.elim (hello_no_fresh C x st P k K F)
    | admit f L P => exact False.elim (admit_no_fresh C x g f P k K F)
    | ready3 P G => exact False.elim (clear_no_fresh C x P.2.1 k K F)
    | read a w f P Q L =>
      have H : ShortReadFlight.Active C x f := by
        rw [Q]
        exact readHist_active C a (by omega) w f P
      exact False.elim (read_no_fresh C x f H k K F)
    | post saved R P => exact post_fresh_pending C saved x N R P k K F

/-! Geometry: a real chart per root suffices. On a maximal fixed
    header fibre the chart's a,b,L are all determined by its root. -/

theorem chart_eq_of_root (x : Raw s n) (X : H2Ready x) (N : 9<n)
    (C D : Chart (header x)) (R : C.root=D.root) : C=D := by
  obtain ⟨Ca,Cb,Cl,Ch,_,_,_,_,_⟩ :=
    ShortReadCaptureGeometry.capture_chart_fields x X.1 C N
  obtain ⟨Da,Db,Dl,Dh,_,_,_,_,_⟩ :=
    ShortReadCaptureGeometry.capture_chart_fields x X.1 D N
  have L := (ShortReadCaptureGeometry.chart_unique C D R).1
  have Ha : header x (nextAt D.root C.a)=true := by
    rw [←R]
    exact (Ch C.a (by omega)).mpr (.inr (.inl rfl))
  have Ia := (Dh C.a (by omega)).mp Ha
  have A : C.a=D.a := by omega
  have Hb : header x (nextAt D.root (C.a+C.b))=true := by
    rw [←R]
    exact (Ch (C.a+C.b) Cl).mpr (.inr (.inr rfl))
  have Ib := (Dh (C.a+C.b) (by omega)).mp Hb
  have B : C.b=D.b := by omega
  -- CHECK: ShortResetCycle.lean:44–55; four data fields and five
  -- propositional fields. After data substitution proof irrelevance.
  cases C with
  | mk r a b l p lt rp rh dst =>
    cases D with
    | mk r' a' b' l' p' lt' rp' rh' dst' =>
      dsimp only at R A B L
      subst r'
      subst a'
      subst b'
      subst l'
      rfl

/-- This is the weakest chart coverage needed for authentication:
    a certified OwnerInv for one chart of each actual H1 root. -/
def OwnerCover (h : Fin n → Bool) (x : Raw s n) : Prop :=
  ∀ r, h r=true → ∃ C : Chart h, C.root=r ∧ ∃ g, OwnerInv C x g

/-- Any classified flip is from the unique owner's actual pending
    generated COMMIT6, at its own incoming centre edge. -/
theorem classified_pending (x : Raw s n) (X : H2Ready x) (N : 9<n)
    (heads : ∀ q,header x q=h q) (owners : OwnerCover h x)
    (e : Fin n) (i : ShortGuardedNOR.Sites h)
    (E : ShortGuardedNOR.classifyFixed h x e=some i) :
    ∃ C : Chart h,
      C.a-1<C.L ∧ C.a<C.L ∧
      ShortChartOwnership.cell C (C.a-1)=(e,0) ∧
      ShortChartOwnership.cell C C.a=(i.val,1) ∧
      PendingAt C x (C.a-1) ∧
      (∀ D : Chart h, ∀ j, j<D.L →
        ShortChartOwnership.cell D j=(e,0) → D=C ∧ j=C.a-1) := by
  have eq : h=header x := funext (fun q => (heads q).symm)
  subst h
  have V := (ShortGuardedNOR.fixed_some x e i).mp E
  obtain ⟨R,head,changed⟩ :=
    (ShortPublicationClassifier.classify_some x e i.val).mp V
  obtain ⟨_,guard,D,k,J,DL,DR,gate,U⟩ :=
    ShortPublicationOwner.selector_change_owner x X N e i.val head changed
  obtain ⟨C,Root,g,Inv⟩ := owners D.root D.rootHeader
  have CD : C=D := chart_eq_of_root x X N C D Root
  subst D
  have site : nextAt C.root k=e := congrArg Prod.fst DL
  have port : C.route.port k=0 := congrArg Prod.snd DL
  have port' : C.route.port (k+1)=1 := congrArg Prod.snd DR
  have hd : header x (rightNeighbor (nextAt C.root k))=true := by
    rw [site,R]
    exact head
  have G := ShortPublishChart.commit_centre x x X C N (fun _=>rfl)
  have K : k=C.a-1 := (G.2.2.1 k J).mp ⟨hd,port,port'⟩
  have F : Fresh (slot C.route x k) := by
    change Fresh (oldK (header x (nextAt C.root k))
      (x (nextAt C.root k)).mis1 (C.route.port k))
    rw [site,port]
    -- CHECK: ShortResetRow.lean:2638–2643; the first four
    -- conjunctions are precisely the healthy unapplied F6.
    exact ⟨guard.1,guard.2.1,guard.2.2.1,guard.2.2.2.1⟩
  have P := owner_fresh_pending C x N g Inv k (by omega) F
  subst k
  have Pair := ShortPublishChart.commit_centre_pair x x X C N (fun _=>rfl)
  have DR' : ShortChartOwnership.cell C C.a=(i.val,1) := by
    rw [←Pair.1]
    exact DR
  refine ⟨C,by omega,Pair.2.1,DL,DR',P,?_⟩
  intro D j L T
  have Q := ShortChartOwnership.same_cell_owner D C j (C.a-1)
    L (by omega) (T.trans DL.symm)
  exact ⟨chart_eq_of_root x X N D C Q.1,Q.2⟩

/-- Physical read endpoints identify exactly the fixed-ring
    neighbours, with an independently fixed anchor x0. -/
theorem chart_read_neighbours (x0 : Raw s n)
    (X0 : H2Ready x0) (N : 9<n)
    (heads0 : ∀ q,header x0 q=h q) (C : Chart h)
    (i : ShortGuardedNOR.Sites h)
    (centre : nextAt C.root C.a=i.val) :
    ((PhysicalH1Neighbors.fixedRing X0.1 (by omega : 3<n) heads0).left i).val=C.root ∧
    ((PhysicalH1Neighbors.fixedRing X0.1 (by omega : 3<n) heads0).right i).val=
      nextAt C.root (C.a+C.b) := by
  have eq : h=header x0 := funext (fun q => (heads0 q).symm)
  subst h
  obtain ⟨A,B,L,H,_,_,_,_,_⟩ :=
    ShortReadCaptureGeometry.capture_chart_fields x0 X0.1 C N
  have HA : header x0 (nextAt C.root C.a)=true :=
    (H C.a (by omega)).mpr (.inr (.inl rfl))
  have HB : header x0 (nextAt C.root (C.a+C.b))=true :=
    (H _ L).mpr (.inr (.inr rfl))
  have C1 : ∀ k, 0<k → k<C.a → header x0 (nextAt C.root k)=false := by
    intro k P Q
    apply Bool.eq_false_iff.mpr
    intro Z
    have T := (H k (by omega)).mp Z
    omega
  have C2 : ∀ k, C.a<k → k<C.a+C.b → header x0 (nextAt C.root k)=false := by
    intro k P Q
    apply Bool.eq_false_iff.mpr
    intro Z
    have T := (H k (by omega)).mp Z
    omega
  -- CHECK: PhysicalH1Neighbors.lean:166–168,189–197.
  -- Its header is AllSizeS1Geometry.header (x0 q), defeq the
  -- actual MIS1-ring header projection (cf. ShortGateChart:62–64).
  have V := PhysicalH1Neighbors.read_sites X0.1 (by omega : 3<n)
    heads0 (⟨C.root,C.rootHeader⟩ : ShortGuardedNOR.Sites (header x0))
    A B HA HB C1 C2
  dsimp only at V
  have eqi : (⟨nextAt C.root C.a,HA⟩ : ShortGuardedNOR.Sites (header x0))=i :=
    Subtype.ext centre
  rw [eqi] at V
  exact ⟨congrArg Subtype.val V.1,V.2⟩

/-- Main E5 authentication: no assumed FromProtectedBits, no global
    grant coherence, and the actual classifier on the next raw mark. -/
theorem all_owner_auth (x0 x : Raw s n) (X0 : H2Ready x0)
    (X : H2Ready x) (N : 9<n)
    (heads0 : ∀ q,header x0 q=h q) (heads : ∀ q,header x q=h q)
    (owners : OwnerCover h x)
    (e : Fin n) (i : ShortGuardedNOR.Sites h)
    (E : ShortGuardedNOR.classifyFixed h x e=some i) :
    let ring := PhysicalH1Neighbors.fixedRing X0.1 (by omega : 3<n) heads0
    ShortPublicationClassifier.FromProtectedBits
      (ShortGuardedNOR.observe x (ring.left i))
      (ShortGuardedNOR.observe x (ring.right i))
      (oldK (header x e) (x e).mis1 0).payload := by
  dsimp only
  obtain ⟨C,K,J,DL,DR,P,_⟩ := classified_pending x X N heads owners e i E
  obtain ⟨saved,a4,a5,R,A,B,W⟩ := P
  have eEq : nextAt C.root (C.a-1)=e := congrArg Prod.fst DL
  have cEq : nextAt C.root C.a=i.val := congrArg Prod.fst DR
  have A' := pending_commit_auth C saved x a4 a5 N ⟨X,heads⟩ R A B W
  dsimp only at A'
  rw [eEq] at A'
  have nbr := chart_read_neighbours x0 X0 N heads0 C i cEq
  change ShortPublicationClassifier.FromProtectedBits
    (ShortReaderMIS1.selectedValue
      (x ((PhysicalH1Neighbors.fixedRing X0.1 (by omega : 3<n) heads0).left i).val).mis1)
    (ShortReaderMIS1.selectedValue
      (x ((PhysicalH1Neighbors.fixedRing X0.1 (by omega : 3<n) heads0).right i).val).mis1)
    (oldK (header x e) (x e).mis1 0).payload
  rw [nbr.1,nbr.2]
  exact A'

/-! E4/E5 consumer glue. Store one owner per actual root at the
    canonical gate a. The following is a concrete closed predicate,
    stronger than bare H2Ready and not a circular auth definition. -/

def AllOwnerInv (h : Fin n → Bool) (x : Raw s n) : Prop :=
  H2Ready x ∧ (∀ q,header x q=h q) ∧
    ∀ r, h r=true → ∃ C : Chart h, C.root=r ∧ OwnerInv C x C.a

theorem owner_cover (x : Raw s n) (A : AllOwnerInv h x) :
    OwnerCover h x := by
  intro r R
  obtain ⟨C,E,P⟩ := A.2.2 r R
  exact ⟨C,E,C.a,P⟩

/-- Canonical gate for any actual chart, not merely the one returned
    by an existential chart_exists_gate. -/
theorem fixed_gate (C : Chart h) (x : Raw s n) (N : 9<n)
    (G : Geom C x) :
    0<C.a ∧ C.a+1<C.L ∧ ShortAdmitFlight.FixedGate (s:=s) C C.a := by
  have eq : h=header x := funext (fun q => (G.2 q).symm)
  subst h
  have A := (ShortReadCaptureGeometry.capture_chart_fields x G.1.1 C N).1
  have L := (ShortPublishChart.stage_seal_centre x x G.1 G.1 C N
    (fun _=>rfl)).1
  refine ⟨by omega,L,?_⟩
  intro y Y heads k K
  -- CHECK: ShortPublishChart.lean:10–18, ShortGateChart.lean:7,
  -- ShortAdmitForward.lean:13, ShortAdmitFlight.lean:114–116.
  -- slotGate and gated are definitionally identical.
  exact (ShortPublishChart.stage_seal_centre x y G.1 Y C N heads).2.2.1 k K

theorem all_owner_closed (x : Raw s n) (N : 9<n)
    (e : Fin n) (A : AllOwnerInv h x) :
    AllOwnerInv h (rawNext s x e) := by
  refine ⟨h2_ready_closed (by omega) x e A.1,
    fun q => (H1.raw_h1_selected_frozen (by omega) x e q A.1.1).trans
      (A.2.1 q),?_⟩
  intro r R
  obtain ⟨C,E,P⟩ := A.2.2 r R
  obtain ⟨gp,gL,gates⟩ := fixed_gate C x N P.1
  exact ⟨C,E,owner_raw_step C x N C.a gp gL gates e P⟩

private theorem fiber_run (x : Raw s n) (N : 5≤n) (X : H2Ready x)
    (heads : ∀ q,header x q=h q) (w : List (Fin n)) :
    H2Ready (rawRun x w) ∧ ∀ q,header (rawRun x w) q=h q := by
  induction w generalizing x with
  | nil => exact ⟨X,heads⟩
  | cons e w ih =>
    exact ih _ (h2_ready_closed N x e X)
      (fun q => (H1.raw_h1_selected_frozen N x e q X.1).trans
        (heads q))

/-- Genuine first hits seed one owner at its own actual prefix.
    Other owners may already be executing subsequent tours. -/
theorem receipt_sound (x0 : Raw s n) (X0 : H2Ready x0) (N : 9<n) :
    ShortAllOwnerSound.ReceiptSound x0 (AllOwnerInv (header x0)) := by
  intro w y H
  obtain ⟨Y,cs,Roots,Cover,Hits⟩ := H
  subst y
  have G := fiber_run x0 (by omega : 5≤n) X0 (fun _=>rfl) w
  refine ⟨G.1,G.2,?_⟩
  intro r R
  obtain ⟨c,M,Root⟩ := (Cover r).mp R
  -- CHECK: ShortEpochFirstHit.lean:17–23 and
  -- ShortAllOwnerSound.lean:12–16; true FirstHitReceipts.
  obtain ⟨a,u,v,Eq,NE,Before,Goal⟩ :=
    ShortEpochFirstHit.first_goal_prefix cs x0 w Hits c M
  let C := c.chart
  let p := rawRun x0 a
  have GP : Geom C p := fiber_run x0 (by omega) X0 (fun _=>rfl) a
  have Park : ShortResetHelloSplice.Parked C (rawRun p u) :=
    (ShortEpochResetOrigin.genuine_reset_seed (by omega) C p
      GP.1 GP.2 u Before Goal).1
  have GU : Geom C (rawRun p u) :=
    geom_run C p (by omega) GP u
  obtain ⟨gp,gL,gates⟩ := fixed_gate C (rawRun p u) N GU
  have Inv := epoch_from_parked C (rawRun p u) N GU Park
    C.a gp gL gates v
  have Same : rawRun x0 w=rawRun (rawRun p u) v := by
    rw [Eq,raw_append,raw_append]
  rw [Same]
  exact ⟨C,Root,Inv⟩

set_option exponentiation.threshold 8100 in
/-- Same physical reset clock, now with the concrete closed epoch target. -/
theorem all_owner_inv_expected (x0 : Raw s n) (X0 : H2Ready x0) (N : 9<n) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (AllOwnerInv (header x0)) x0 ((10^8095+19)*n^2) :=
  ShortAllOwnerSound.raw_expected_of_receipts N x0 X0 _ (receipt_sound x0 X0 N)

/-- The exact E5 old-mark NOR update on the actual fixed ring.
    Unlike raw_step_conditional's abstract auth input, it now uses
    the concrete closed all-owner predicate. -/
theorem all_owner_nor_step (x0 x : Raw s n)
    (X0 : H2Ready x0) (N : 9<n) (heads0 : ∀ q,header x0 q=h q)
    (A : AllOwnerInv h x) (e : Fin n) :
    let ring := PhysicalH1Neighbors.fixedRing X0.1 (by omega : 3<n) heads0
    ShortGuardedNOR.observe (rawNext s x e) =
      match ShortGuardedNOR.classifyFixed h x e with
      | none => ShortGuardedNOR.observe x
      | some i => ShortNORCover.update ring (ShortGuardedNOR.observe x) i := by
  dsimp only
  exact ShortGuardedNOR.raw_step_conditional
    (PhysicalH1Neighbors.fixedRing X0.1 (by omega : 3<n) heads0)
    x e (edge_sep (by omega) e) A.2.1
    (fun i E => all_owner_auth x0 x X0 A.1 N heads0 A.2.1
      (owner_cover x A) e i E)

end L4.ShortClassifiedOwnerAuth

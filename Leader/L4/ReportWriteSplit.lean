import Leader.L4.ReportOwnerCommandRail
import Leader.L4.ReportWriteOrigin
namespace L4.ReportWriteSplit
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerDoorProjection
open ReportPrelaunchDoorLift ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerIssueControl ReportOwnerForwardControl ReportOwnerReverseControl
open ReportOwnerSerial ReportByteRows ReportRawProjection ReportOwnerCommandRail
open ReportWriteOrigin
variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

private theorem front_unique (d : Sheet) (C : Chart h) (x : Raw s n)
    (i j : Nat) (I : ForwardWait d C x i) (J : j<C.L) (T : (tok d C x j).tag=2) :
    i=j := by
  have A := I.2.2 j J
  rw [T] at A
  unfold frontTag at A
  split at A
  · contradiction
  · split at A
    · omega
    · contradiction

private theorem no_issue_tag (d : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) (J : i<C.L) (T : (tok d C x i).tag=2) (I : LegalIssue d C x) :
    False := by
  have E := I.2.2 i J
  omega

private theorem no_reverse_tag (d : Sheet) (C : Chart h) (x : Raw s n)
    (i j : Nat) (J : j<C.L) (T : (tok d C x j).tag=2)
    (I : ReverseWait d C x i) : False := by
  have E := I.2.2 j J
  rw [T] at E
  unfold backTag at E
  split at E
  · contradiction
  · split at E <;> contradiction

private theorem forward_tag (d : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) (I : ForwardWait d C x i) : (tok d C x i).tag=2 := by
  rw [I.2.2 i I.2.1]
  simp [frontTag]

/-- The sampled interior of one forward flight: every mark either holds its
cursor or effects its one real forward hop; a terminal turn is not included. -/
inductive BeforeTurn (d : Sheet) (C : Chart h) (x : Raw s n) :
    List (Fin n) → Nat → Prop where
  | nil (F : ForwardWait d C x 0) : BeforeTurn d C x [] 0
  | hold {w : List (Fin n)} {k : Nat} (R : BeforeTurn d C x w k) (e : Fin n)
      (S : ForwardWait d C (rawNext s (rawRun x w) e) k) :
      BeforeTurn d C x (w++[e]) k
  | hop {w : List (Fin n)} {k : Nat} (R : BeforeTurn d C x w k)
      (S : ForwardWait d C (rawNext s (rawRun x w) (out C k)) (k+1)) :
      BeforeTurn d C x (w++[out C k]) (k+1)

theorem forward_step_control (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat)
    (A : ForwardWait d C x k) (e : Fin n) :
    readPC d C (rawNext s x e)=readPC d C x := by
  have M := (cached_fibre d N hh Q F).mask x X
  by_cases D : e=door C
  · subst e
    let p := params d s
    let v := selectBytes d (x C.root)
    have H : (publicationToken p true v 0).tag=1 ∨
        (publicationToken p true v 0).tag=2 := by
      have E : tok d C x 0=publicationToken p true v 0 := by rw [root_tok]; rfl
      rw [←E,A.2.2 0 C.positive]
      by_cases K : k=0
      · subst k; exact .inr rfl
      · exact .inl (by simp [frontTag,show 0<k by omega])
    exact (raw_door_final d C x N M).1.trans (prelaunch_hold_controls p v _ A.1.1 A.1.2 H)
  · exact raw_nondoor_control d C x e N M D

theorem before_turn_pc (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (w : List (Fin n)) (k : Nat)
    (R : BeforeTurn d C x w k) :
    Cached d hh Q (rawRun x w) ∧ ForwardWait d C (rawRun x w) k ∧
      readPC d C (rawRun x w)=readPC d C x := by
  let CF := cached_fibre d N hh Q F
  induction R with
  | nil A => exact ⟨X,A,rfl⟩
  | hold _ e A IH =>
      rw [ShortOwnerEpochJS.raw_snoc]
      exact ⟨CF.closed _ e IH.1,A,
        (forward_step_control d C N hh F _ IH.1 _ IH.2.1 e).trans IH.2.2⟩
  | hop _ A IH =>
      rw [ShortOwnerEpochJS.raw_snoc]
      exact ⟨CF.closed _ _ IH.1,A,
        (forward_step_control d C N hh F _ IH.1 _ IH.2.1 _).trans IH.2.2⟩


/-- The backward cursor split is purely structural. No byte or WRITE
assumption is needed until the issue and original flight have been found. -/
theorem forward_issue_split (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (w : List (Fin n)) (k : Nat)
    (A : ForwardWait d C (rawRun x w) k) :
    ∃ pre fly : List (Fin n), w=pre++door C::fly ∧
      let y := rawRun x pre
      Cached d hh Q y ∧ LegalIssue d C y ∧
      (readPC d C y).2=(readPC d C (rawRun x w)).2 ∧
      BeforeTurn d C (rawNext s y (door C)) fly k := by
  have packed (z : Raw s n) (u : List (Fin n)) (Y : Cached d hh Q z)
      (J : Serial d C z) : Cached d hh Q (rawRun z u) ∧ Serial d C (rawRun z u) := by
    induction u generalizing z with
    | nil => exact ⟨Y,J⟩
    | cons e u IH =>
      exact IH _ ((cached_fibre d N hh Q F).closed z e Y)
        (ReportOwnerSerial.all_mark d C N hh G F z Y J digit e)
  revert A
  rw [←List.reverse_reverse w]
  induction w.reverse generalizing k with
  | nil =>
    intro A
    have P : (readPC d C x).1=2 := A.1.1
    have E := I.2.1
    omega
  | cons e rev IH =>
    rw [List.reverse_cons,ShortOwnerEpochJS.raw_snoc]
    intro A
    let u := rev.reverse
    let z := rawRun x u
    obtain ⟨Z,U⟩ := packed x u X (.inl I)
    have Tg := forward_tag d C _ k A
    rcases U with J|⟨j,J⟩|⟨j,J⟩
    · by_cases D : e=door C
      · subst e
        rcases ReportOwnerIssueControl.door_step d C hh G F N z Z J with R|⟨Y,P⟩
        · exact (no_issue_tag d C _ k A.2.1 Tg ⟨by rw [R.1]; exact Nat.zero_le _,R.2⟩).elim
        · have K := front_unique d C _ 0 k Y A.2.1 Tg
          subst k
          exact ⟨u,[],rfl,Z,J,P.symm,.nil Y⟩
      · exact (no_issue_tag d C _ k A.2.1 Tg
          (nondoor_preserves d C hh G F N z Z J e D).1).elim
    · obtain ⟨pre,fly,W,XP,IP,P,T⟩ := IH j J
      have PC := congrArg Prod.snd (forward_step_control d C N hh F z Z j J e)
      rcases ReportOwnerForwardControl.all_mark d C hh G F N z Z j J e with S|⟨D,S|⟨_,S⟩⟩
      · have K := front_unique d C _ j k S A.2.1 Tg
        subst k
        refine ⟨pre,fly++[e],by rw [W,List.append_assoc]; rfl,XP,IP,P.trans PC.symm,?_⟩
        apply BeforeTurn.hold T e
        simpa only [show z=rawRun (rawNext s (rawRun x pre) (door C)) fly by dsimp only [z,u]; rw [W,ShortOwnerEpochJS.raw_append]; rfl] using S
      · subst e
        have K := front_unique d C _ (j+1) k S A.2.1 Tg
        subst k
        refine ⟨pre,fly++[out C j],by rw [W,List.append_assoc]; rfl,XP,IP,P.trans PC.symm,?_⟩
        apply BeforeTurn.hop T
        simpa only [show z=rawRun (rawNext s (rawRun x pre) (door C)) fly by dsimp only [z,u]; rw [W,ShortOwnerEpochJS.raw_append]; rfl] using S
      · exact (no_reverse_tag d C _ j k A.2.1 Tg S).elim
    · rcases ReportOwnerReverseControl.all_mark d C hh G F N z Z j J digit e with S|⟨q,_,_,S⟩|⟨K,D,_⟩
      · exact (no_reverse_tag d C _ j k A.2.1 Tg S).elim
      · exact (no_reverse_tag d C _ q k A.2.1 Tg S).elim
      · subst j e
        have E := (door_consumes_root d C hh G F N z Z J digit).2 k A.2.1
        change (tok d C (rawNext s z (door C)) k).tag=0 at E
        change (tok d C (rawNext s z (door C)) k).tag=2 at Tg
        omega


theorem before_turn_as_write (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok) (W : WriteF d C x 0 t)
    (u : List (Fin n)) (k : Nat) (R : BeforeTurn d C x u k) :
    BeforeWriteTurn d C x u k := by
  induction R with
  | nil _ => exact .nil
  | @hold w j R e S IH =>
    apply BeforeWriteTurn.hold e IH
    intro E
    subst e
    obtain ⟨Z,A⟩ := write_origin_run d C hh G F N x X t W w j IH
    let z := rawRun x w
    have M := (cached_fibre d N hh Q F).mask z Z
    have J := A.shape.2.1
    have RD : readyAt d C z j=true := by
      unfold readyAt
      rw [rankReady_iff,←predecessor_projection]
      rcases A.packet with P|P
      · rw [P]
        refine ⟨A.origin.1,?_⟩
        intro S
        have L := A.origin.2.2.1
        have K := S.1.2.2
        unfold healthyAdmit at S
        change t.opcode=admitOp (params d s) at K
        unfold writeOp admitOp at *
        omega
      · rw [P]
        simp [MISByteCodec.faultToken,healthyAdmit]
    have Tag := forward_tag d C _ j S
    by_cases I : j+1<C.L
    · have F0 := (ready_locations d C z N M j I RD).1
      rw [F0] at Tag
      contradiction
    · have T := ready_turn_tag d C z N M j (by omega) RD
      change (tok d C (rawNext s z (out C j)) j).tag=2 at Tag
      omega
  | @hop w j R S IH =>
    exact .hop IH S.2.1

theorem structural_issue_emits_F (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (A : ForwardWait d C (rawNext s x (door C)) 0) :
    ∃ t : Tok,
      (source (params d s) (selectBytes d (x C.root))
        (publicationToken (params d s) true (selectBytes d (x C.root)) 0)).2=some t ∧
      t.tag=2 := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  rcases prelaunch_issue_action p v t I.2.1 I.1 with E|⟨q,E⟩
  · have W := (raw_door_final d C x N ((cached_fibre d N hh Q F).mask x X)).2
    change resetTokenRead p (selectBytes d (rawNext s x (door C) C.root)) 0=
      (match (source p v t).2 with
        | none => prelaunchDoorNormWire p v
        | some a => resetTokenWire p a) at W
    rw [E] at W
    have K := forward_tag d C _ 0 A
    rw [root_tok,W] at K
    have Y := prelaunch_empty_wire_tag p
    have bad : (2:Nat)=0 := K.symm.trans Y
    omega
  · refine ⟨_,congrArg Prod.snd E,rfl⟩

theorem before_turn_start (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (k : Nat) (B : BeforeTurn d C x w k) :
    ForwardWait d C x 0 := by
  induction B with
  | nil F => exact F
  | hold _ _ _ IH => exact IH
  | hop _ _ IH => exact IH

theorem healthy_write_split_from_receipt (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (reset w : List (Fin n)) (R : Generated d C x reset .done) (k : Nat) (K : k<C.L)
    (Health : HealthyWrite (params d s) (tok d C (rawRun (rawRun x reset) w) k)) :
    let b := rawRun x reset
    let z := rawRun b w
    ∃ pre fly : List (Fin n), ∃ t : Tok,
      w=pre++door C::fly ∧
      let a := rawRun b pre
      Cached d hh Q a ∧ LegalIssue d C a ∧
      (readPC d C a).2=(readPC d C z).2 ∧
      writeOp (params d s)≤(readPC d C a).2 ∧
      (readPC d C a).2<sealOp (params d s) ∧
      (source (params d s) (selectBytes d (a C.root))
        (publicationToken (params d s) true (selectBytes d (a C.root)) 0)).2=some t ∧
      t.tag=2 ∧ tok d C z k=t ∧
      BeforeWriteTurn d C (rawNext s a (door C)) fly k := by
  dsimp only
  let b := rawRun x reset
  let z := rawRun b w
  let CF := cached_fibre d N hh Q F
  have Xb := (cached_genuine_full_parked d C N hh F x X reset R).1
  have Sb := seed_receipt d C N hh F x X reset R
  have Ib : LegalIssue d C b := by
    rcases Sb.1 with I|⟨j,I⟩|⟨j,I⟩
    · exact I
    · have P := (cached_genuine_full_parked d C N hh F x X reset R).2.1.1
      have E := pc_fields d C b .issue1 (by decide) P
      have V : (readPC d C b).1=2 := I.1.1
      change readPC d C b=(1,1) at E
      rw [E] at V
      contradiction
    · have P := (cached_genuine_full_parked d C N hh F x X reset R).2.1.1
      have E := pc_fields d C b .issue1 (by decide) P
      have V : (readPC d C b).1=2 := I.1.1
      change readPC d C b=(1,1) at E
      rw [E] at V
      contradiction
  have Sz := (strong_run d C N hh G F digit b Xb Sb w).2.1
  have Sim := Sz.2 k K (.inl Health.1) Health.2.1
  have A : ForwardWait d C z k := by
    rcases Sz.1 with I|⟨j,I⟩|⟨j,I⟩
    · exact (no_issue_tag d C z k K Health.1 I).elim
    · simpa only [front_unique d C z j k I K Health.1] using I
    · exact (no_reverse_tag d C z j k K Health.1 I).elim
  obtain ⟨pre,fly,W,Y,I,PC,Flight⟩ := forward_issue_split d C N hh G F digit b Xb Ib w k A
  let a := rawRun b pre
  let a' := rawNext s a (door C)
  have Y' := CF.closed a (door C) Y
  have First := before_turn_start d C a' fly k Flight
  obtain ⟨t,Emit,Tag⟩ := structural_issue_emits_F d C N hh F a Y I First
  have Lo : writeOp (params d s)≤(readPC d C a).2 :=
    (PC.trans Sim.symm).symm ▸ Health.2.2.1
  have Hi : (readPC d C a).2<sealOp (params d s) :=
    (PC.trans Sim.symm).symm ▸ Health.2.2.2
  have WF := write_launch d C hh G F N a Y I t I.2.1 Lo Hi Emit Tag
  have Actual := before_turn_as_write d C N hh G F a' Y' t WF fly k Flight
  have Runs : z=rawRun a' fly := by
    dsimp only [z]
    rw [W,ShortOwnerEpochJS.raw_append]
    rfl
  have EQ := healthy_write_origin_of_run d C hh G F N a' Y' t WF fly k Actual
    (Runs ▸ Health.2.1)
  exact ⟨pre,fly,t,W,Y,I,PC,Lo,Hi,Emit,Tag,((congrArg (fun y => tok d C y k) Runs).trans EQ),Actual⟩

#print axioms healthy_write_split_from_receipt
#print axioms before_turn_as_write
#print axioms structural_issue_emits_F
#print axioms forward_issue_split
#print axioms before_turn_pc
end L4.ReportWriteSplit

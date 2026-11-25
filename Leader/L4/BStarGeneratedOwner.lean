import Leader.L4.BStarOwnerControlHistory

namespace L4.BStarGeneratedOwner
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarSeparatorParked
open BStarSeparatorJoinedTags BStarResetSchedule BStarAcquireWaitControl
open BStarLongDoor BStarResetChartService BStarSeparatorRing BStarOwnerControlHistory

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Clean suffix is an invariant while going out. Good itself checks
the clean suffix on the return leg. -/
def OutClean (len : Nat) (u : BStarSeparatingRail.Rail) : Cursor → Prop
  | .out k => ∀ j, k<j → j≤len → u j=.empty
  | .back _ => True

theorem lift_clean_word {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (Q : XX → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (w : List (Fin n)) (z : Cursor) :
    let root := (S.getD 0 fallback).1
    let track := project (fun j => S.getD j fallback)
    let step := AllSizeS1Geometry.step (n:=n) B
    Q x → Waiting hp base root op x → Good anyTag len (track x) z → OutClean len (track x) z →
    ∃ pre post d, w=pre++post ∧
      Seen step track anyTag len x z pre d ∧
      Q (BStarResetSchedule.run step x pre) ∧ Waiting hp base root op (BStarResetSchedule.run step x pre) ∧
      Good anyTag len (track (BStarResetSchedule.run step x pre)) d ∧
      OutClean len (track (BStarResetSchedule.run step x pre)) d ∧
      (d=.back 0 → Clean track anyTag len (BStarResetSchedule.run step x pre)) ∧
      (d=.back 0 ∨ post=[]) := by
  dsimp only
  let adr := fun j => S.getD j fallback
  let root := (adr 0).1
  let step := AllSizeS1Geometry.step (n:=n) B
  let track : XX → BStarSeparatingRail.Rail := project adr
  have cl {a : XX} (G : Good anyTag len (track a) (.back 0)) : Clean track anyTag len a :=
    ⟨G.2.1,G.2.2.2⟩
  induction w generalizing x z with
  | nil =>
    intro q W G oc
    exact ⟨[],[],z,rfl,.nil _ _,q,W,G,oc,fun e => cl (e ▸ G),.inr rfl⟩
  | cons e w ih =>
    intro q W G oc
    by_cases Z : z=.back 0
    · subst z
      exact ⟨[],e::w,.back 0,rfl,.nil _ _,q,W,G,oc,fun _ => cl G,.inl rfl⟩
    · have M := mark_at hp C e (distinct e) op W z Z G
      obtain ⟨d,D,G'⟩ := lift_mark M z Z G
      let y := step x e
      have q' : Q y := closed x q e
      obtain ⟨h,k⟩ := root_header hp C W.1
      have F : track x 0=atSite (x root).long 0 := by
        change atSite (x root).long (adr 0).2=_
        rw [k]
      have ctrl := step_wait k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x e root h W.2.1 W.2.2.1
        (F ▸ before_receipt G Z)
      have P := congrArg (fun q : BitVec 2 × BitVec 9 => q.1.toNat) ctrl
      have O := congrArg (fun q : BitVec 2 × BitVec 9 => q.2.toNat) ctrl
      have W' : Waiting hp base root op y :=
        ⟨fiber y q',(BStarResetWaitRing.valid_of_control_eq _ _ ctrl).trans W.2.1,
          P.trans W.2.2.1,O.trans W.2.2.2⟩
      have oc' : OutClean len (track y) d := by
        cases D with
        | stay =>
          cases z with
          | out k => exact outward_suffix hp C e (distinct e) op k k W (.inl rfl) G G' oc
          | back => exact trivial
        | forward k => exact outward_suffix hp C e (distinct e) op k (k+1) W (.inr rfl) G G' oc
        | turn => exact trivial
        | reverse => exact trivial
      obtain ⟨pre,post,z',E,T,U,V,H,oc'',A,B'⟩ := ih (x:=y) d q' W' G' oc'
      exact ⟨e::pre,post,z',congrArg (List.cons e) E,.cons Z M D G' T,U,V,H,oc'',A,B'⟩


open BStarClearanceSource BStarClearanceResidual BStarResetControllerEntry BStarLongCommand

/-- A fixed physical prefix after a genuine clean launch has one
identified carrier until its first source arrival, and the rest of the
input word is explicitly returned rather than counted as this tour. -/
theorem from_clean_launch {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (Q : XX → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (q : Q x) :
    let addr := fun j => S.getD j fallback
    let root := (addr 0).1
    let track := project addr
    let step := AllSizeS1Geometry.step (n:=n) B
    let door := RearTrace.predecessor root
    let start := step x door
    let op := (ctrlOp.read (x root).long).toNat
    (∀ j≤len, track x j=.empty) → Launch (x root).long (start root).long →
    ∃ pre post z, w=pre++post ∧
      Seen step track anyTag len start (.out 0) pre z ∧
      let here := BStarResetSchedule.run step start pre
      Q here ∧ Waiting hp base root op here ∧ Good anyTag len (track here) z ∧
      OutClean len (track here) z ∧ (z=.back 0 → Clean track anyTag len here) ∧
      (z=.back 0 ∨ post=[]) := by
  dsimp only
  intro clean launch
  let addr := fun j => S.getD j fallback
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let start := AllSizeS1Geometry.step B x door
  let track : XX → BStarSeparatingRail.Rail := project addr
  let op := (ctrlOp.read (x root).long).toNat
  have qq := closed x q door
  obtain ⟨I,a,_,E⟩ := launch
  have phase : (ctrlPhase.read (start root).long).toNat=2 :=
    congrArg (fun s : (Token × BitVec 2) × BitVec 9 => s.1.2.toNat) E
  have pc : (ctrlOp.read (start root).long).toNat=op :=
    congrArg (fun s : (Token × BitVec 2) × BitVec 9 => s.2.toNat) E
  have ok : op<413 := issue_range I
  have valid : LongDoorGuard.valid manifest (start root).long=true := by
    change ((((ctrlPhase.read (start root).long).toNat==1)||
       ((ctrlPhase.read (start root).long).toNat==2)) && decide ((ctrlOp.read (start root).long).toNat<413))=true
    rw [phase,pc]
    simp [ok]
  have W : Waiting hp base root op start := ⟨fiber _ qq,valid,phase,pc⟩
  have front : track start 0=forward op a := by
    have K := (root_header hp C (fiber _ qq)).2
    change atSite (start root).long (addr 0).2=_
    rw [K]
    exact congrArg (fun s : (Token × BitVec 2) × BitVec 9 => s.1.1) E
  have G : Good anyTag len (track start) (.out 0) :=
    ⟨Nat.zero_le _,⟨_,front⟩,fun j hj => (Nat.not_lt_zero j hj).elim⟩
  have out : OutClean len (track start) (.out 0) := fun j h hj =>
    empty_away_from_door hp C (fiber _ q) clean door (distinct door) j (.inl h) hj
  exact lift_clean_word hp C Q fiber closed distinct op w (.out 0) qq W G out


open BStarLongRouting BStarLongTransport BStarLongEvents BStarResetQuiet BStarResetQuietTable BStarResetIdleRing
open BStarSeparatorIdleClass BStarAcquireAnchors

/-- An unrelated mark does not consume the arrived source D. The
left-endpoint case is a literal DE hold, not a whole-site frame. -/
theorem arrived_nonown {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (e : Fin n) (he : e≠rightNeighbor e)
    (away : e≠RearTrace.predecessor (S.getD 0 fall).1) :
    let addr := fun j => S.getD j fall
    let root := (addr 0).1
    let y := AllSizeS1Geometry.step B x e
    Clean (project addr) anyTag len x →
    Clean (project addr) anyTag len y ∧ control (y root).long=control (x root).long := by
  dsimp only
  intro J
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let y := AllSizeS1Geometry.step B x e
  have suffix := BStarResetConsumedClean.suffix_empty_any hp C same J e he
  have R : root≠rightNeighbor e := fun r => away
    ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor r.symm))
  have Hh := root_header hp C same
  by_cases E : root=e
  · have hit : addr 0=address e (L 0) := Prod.ext E Hh.2
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    have mid : avoids (L 0) (middle g raw) := by
      apply middle_avoids_of_chart
      intro v hv ha
      have mc : v.1∈orderedCommands g := by
        rw [←actualOffers_claims g raw]
        exact List.mem_map.mpr ⟨v,hv,rfl⟩
      rcases touches hp C same e 0 (Nat.zero_le _) v.1 (L 0) mc ha hit with D|T|L|⟨i,U,_⟩
      · cases D.2.2
      · obtain ⟨Eq,k,hk,_,_,idx,H⟩ := T
        have val := congrArg (fun z : Pos n => z.2.val) (hit.symm.trans (Eq ▸ H))
        exact (by change 0=k.source.occurrence.val at val; omega : False).elim
      · obtain ⟨lim,k,d,hk,hd,src,dst⟩ := L
        have eq := address_inj e he (hit.symm.trans src)
        have old (j : Nat) (a : AtK) (h : addr j=address e a) :
            readK raw a=project addr x j :=
          (old_read x e a).trans ((congrArg (atCursor x) h).symm)
        obtain ⟨pay,dp⟩ := J.1
        have D' := (old 0 k.source src).trans dp
        have E' := (old 1 d dst).trans (J.2 1 (by decide) (by omega))
        have Lh : LinkHold (bound g (readK raw) k.source) (bound g (readK raw) d) := by
          unfold bound
          rw [D',E']
          obtain ⟨p,Bd⟩ := bound_D (geometry g k.source.side) k.source.occurrence pay
          rw [Bd]
          exact .de p
        have H := link_avoids g raw k d hk (BStarAcquireReturn.link_shape g k d hk hd).2.1 hd Lh
        exact fun w hw heq => H.1 w (List.mem_flatMap.mpr ⟨v,hv,hw⟩) (heq.trans eq)
      · omega
    have old : readK raw (L 0)=project addr x 0 :=
      (old_read x e _).trans ((congrArg (atCursor x) hit).symm)
    have new : readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) (L 0)
        =project addr y 0 :=
      (new_read B x e he _).trans ((congrArg (atCursor y) hit).symm)
    have S := joined_idle_cls k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) (L 0)
      (not_discarded hp C same e 0 (Nat.zero_le _) _ hit) mid
      (safe_nonright _ _ _ (by decide))
    have C0 := ((preserves ((congrArg cls new).symm.trans (S.trans (congrArg cls old)))).2.2.2) J.1
    refine ⟨⟨C0,suffix⟩,?_⟩
    have left : control (largePair B (x e,x (rightNeighbor e))).1.long=control (x e).long :=
      BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x e,x (rightNeighbor e)) (show oldH6 B x e=true from E ▸ Hh.1)
    exact (congrArg (fun q : Fin n => control (y q).long) E).trans
      ((show control (y e).long=control (x e).long from by simpa only [y,AllSizeS1Geometry.step,if_true] using left).trans
        (congrArg (fun q : Fin n => control (x q).long) E.symm))
  · have paid : y root=x root := by simp only [y,AllSizeS1Geometry.step,if_neg E,if_neg R]
    have pp : project addr y 0=project addr x 0 := by
      change atSite (y root).long (addr 0).2=atSite (x root).long (addr 0).2
      exact congrArg (fun q : LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁) => atSite q.long (addr 0).2) paid
    exact ⟨⟨pp.symm ▸ J.1,suffix⟩,congrArg (fun q : LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁) => control q.long) paid⟩


inductive Mode where
  | idle
  | busy (op : Nat) (cursor : Cursor)

def Current (base : XX) (addr : Nat → Pos n) (len : Nat) (x : XX) : Mode → Prop
  | .idle => Issue (x (addr 0).1).long ∧ ∀ j≤len, project addr x j=.empty
  | .busy op z => Waiting hp base (addr 0).1 op x ∧ Good anyTag len (project addr x) z ∧
      OutClean len (project addr x) z

/-- Source-corresponding history on the actual word. The only idle-to-busy
edge is a genuine own Launch; all busy edges retain its opcode until
the separate consume. No byte-equality provenance inference. -/
inductive Event (addr : Nat → Pos n) (len : Nat) (x : XX) (e : Fin n) :
    Mode → Mode → Prop
  | idle_hold (ne : e≠RearTrace.predecessor (addr 0).1) : Event addr len x e .idle .idle
  | bad_issue (eq : e=RearTrace.predecessor (addr 0).1)
      (bad : let old := (x (addr 0).1).long; initial (ctrlOp.read old).toNat old=none) :
      Event addr len x e .idle .idle
  | launch (eq : e=RearTrace.predecessor (addr 0).1)
      (good : Launch (x (addr 0).1).long (AllSizeS1Geometry.step B x e (addr 0).1).long) :
      Event addr len x e .idle (.busy (ctrlOp.read (x (addr 0).1).long).toNat (.out 0))
  | transit (op : Nat) (z d : Cursor) (live : z≠.back 0)
      (S : Seen (AllSizeS1Geometry.step B) (project addr) anyTag len x z [e] d) :
      Event addr len x e (.busy op z) (.busy op d)
  | arrived_hold (op : Nat) (ne : e≠RearTrace.predecessor (addr 0).1) :
      Event addr len x e (.busy op (.back 0)) (.busy op (.back 0))
  | consume (op : Nat) (eq : e=RearTrace.predecessor (addr 0).1)
      (E : ∀ j≤len, project addr (AllSizeS1Geometry.step B x e) j=.empty) :
      Event addr len x e (.busy op (.back 0)) .idle

inductive GeneratedOwner (base : XX) (addr : Nat → Pos n) (len : Nat) :
    XX → Mode → List (Fin n) → Mode → Prop
  | next {x a e w b dest}
      (I : Current hp base addr len x a) (E : Event hp addr len x e a b)
      (tail : GeneratedOwner base addr len (AllSizeS1Geometry.step B x e) b w dest) :
      GeneratedOwner base addr len x a (e::w) dest
  | endpoint {x a} (I : Current hp base addr len x a) :
      GeneratedOwner base addr len x a [] a

/-- One actual mark from any reachable control-language state. -/
theorem current_step {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : XX → Prop) (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (q : Q x) (e : Fin n) (m : Mode) :
    let addr := fun j => S.getD j fall
    Current hp base addr len x m →
    ∃ d, Event hp addr len x e m d ∧
      Current hp base addr len (AllSizeS1Geometry.step B x e) d := by
  dsimp only
  intro cur
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let step := AllSizeS1Geometry.step (n:=n) B
  let y := step x e
  cases m with
  | idle =>
    obtain ⟨I,clean⟩ := cur
    rcases idle_launch_or_hold hp C (fiber _ q) clean distinct e I with H|A|G
    · exact ⟨.idle,.idle_hold H.1,H.2.1,H.2.2.2⟩
    · exact ⟨.idle,.bad_issue A.1 A.2.1,issue_of_snapshot (by decide) A.2.2.1,A.2.2.2⟩
    · obtain ⟨own,L,G,K⟩ := G
      have pc : (ctrlOp.read (y root).long).toNat=(ctrlOp.read (x root).long).toNat := by
        obtain ⟨_,_,_,E⟩ := L
        exact congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.2.toNat) E
      have ph : (ctrlPhase.read (y root).long).toNat=2 := by
        obtain ⟨_,_,_,E⟩ := L
        exact congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.1.2.toNat) E
      have op : (ctrlOp.read (x root).long).toNat<413 := issue_range I
      have V : LongDoorGuard.valid manifest (y root).long=true := by
        change ((((ctrlPhase.read (y root).long).toNat==1)||
          ((ctrlPhase.read (y root).long).toNat==2)) && decide ((ctrlOp.read (y root).long).toNat<413))=true
        rw [ph,pc]
        simp [op]
      exact ⟨_,.launch own L,⟨fiber _ (closed _ q _),V,ph,pc⟩,G,K⟩
  | busy op z =>
    obtain ⟨W,G,H⟩ := cur
    by_cases live : z≠.back 0
    · obtain ⟨pre,post,d,E,S,_,Wd,Gd,Hd,_,Last⟩ :=
        lift_clean_word hp C Q fiber closed distinct op [e] z q W G H
      cases pre with
      | nil =>
        cases S
        rcases Last with A|A
        · exact (live A).elim
        · rw [A] at E
          cases E
      | cons first tail =>
        change e::[]=first::(tail++post) at E
        obtain ⟨rfl,T⟩ := List.cons.inj E
        obtain ⟨rfl,_⟩ := List.append_eq_nil_iff.mp T.symm
        exact ⟨.busy op d,.transit op z d live S,Wd,Gd,Hd⟩
    · have R : z=.back 0 := Classical.not_not.mp live
      subst z
      have clean : Clean (project addr) anyTag len x := ⟨G.2.1,G.2.2.2⟩
      by_cases own : e=RearTrace.predecessor root
      · subst e
        obtain ⟨E,ph,a,A,P⟩ := BStarSeparatorReceipt.consume hp C op distinct W clean
        have bound : a<413 := A.elim (fun H => H.symm ▸ (by decide : (0 : Nat)<413)) And.right
        exact ⟨.idle,.consume op rfl E,legal_issue _ ph (P.symm ▸ bound),E⟩
      · obtain ⟨D,K⟩ := arrived_nonown hp C W.1 e (distinct e) own clean
        have V : Waiting hp base root op y :=
          ⟨fiber _ (closed _ q _),(BStarResetWaitRing.valid_of_control_eq _ _ K).trans W.2.1,
            (congrArg (fun t : BitVec 2 × BitVec 9 => t.1.toNat) K).trans W.2.2.1,
            (congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat) K).trans W.2.2.2⟩
        refine ⟨.busy op (.back 0),.arrived_hold op own,V,⟨Nat.zero_le _,D.1,?_,D.2⟩,trivial⟩
        intro j hj
        omega

/-- All-label closure on the original tape: a busy phase has no
source relaunch until a distinct actual consume event. -/
theorem generated_word {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : XX → Prop) (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (m : Mode) :
    let addr := fun j => S.getD j fall
    let step := AllSizeS1Geometry.step (n:=n) B
    Q x → Current hp base addr len x m →
    ∃ d, GeneratedOwner hp base addr len x m w d ∧
      Q (BStarResetSchedule.run step x w) ∧ Current hp base addr len (BStarResetSchedule.run step x w) d := by
  dsimp only
  induction w generalizing x m with
  | nil =>
    intro q a
    exact ⟨m,.endpoint a,q,a⟩
  | cons e w ih =>
    intro q a
    obtain ⟨j,E,H⟩ := current_step hp C Q fiber closed distinct q e m a
    obtain ⟨d,F,K,Z⟩ := ih j (closed _ q e) H
    exact ⟨d,.next a E F,K,Z⟩

#print axioms from_clean_launch
#print axioms arrived_nonown
#print axioms current_step
#print axioms generated_word
end L4.BStarGeneratedOwner

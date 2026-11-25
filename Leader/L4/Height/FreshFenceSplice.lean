import Leader.L4.Height.FreshFenceInspection
import Leader.L4.Height.FreshPartialLedgers

namespace L4.Height.FreshFenceSplice
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongFixedRouting
open BStarH6WordChart BStarH6Ordinal BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarResetMarkAdapter BStarGeneratedOwner BStarOwnerLaunchOrigin BStarGeneratedBandScan
open BStarSeparatingRail BStarAcquireForwardTrace BStarCopyFenceCuts BStarCopyAttemptBand
open BStarCopyFIFO BStarCopyMarkedLedger BStarCopyFenceSaturation BStarClearanceDataChart
open BStarCopyRightStrip (addr rail)
open BStarCopyLeftDeposit (headFirst)
open BStarCopyRightMark (stripWord)
open BStarCopyLeftFence (ldRead)
open BStarCopyRightFence (rdRead)
open BStarCopyLeftPending (pending remaining)
open BStarCopyRightMixed (planOf)
open BStarCopyInjection (sourceOccurrence)
open FreshFenceContinuation FreshFenceGuards

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

private theorem append_history {base x : X} {slots : Nat→Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base slots len x a u b)
    (Q : GeneratedOwner hp base slots len (run x u) b v c) :
    GeneratedOwner hp base slots len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

private theorem busy_history {base x : X} {slots : Nat→Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)} (P : BusyOnly hp base slots len op x z w d) :
    GeneratedOwner hp base slots len x (.busy op z) w (.busy op d) := by
  induction P with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

private theorem seen_cursor {slots : Nat→Pos n} {x : X} {e : Fin n} {len : Nat} {z d : Cursor}
    (seen : BStarResetSchedule.Seen step (project slots) BStarSeparatorControl.anyTag len x z [e] d) :
    Advance len z d := by
  cases seen with
  | cons _ _ A _ rest => cases rest; exact A

private theorem past_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m d : Mode} (e : Fin n)
    (old : Current hp base (fun j=>S.getD j fall) len x m)
    (mark : Event hp (fun j=>S.getD j fall) len x e m d)
    (post : Current hp base (fun j=>S.getD j fall) len (step x e) d)
    (oldBand : Band x (S.getD 0 fall).1) (newBand : Band (step x e) (S.getD 0 fall).1)
    (same : ∀ i,Layout B base i=Layout B x i)
    (past : BStarCopyLeftReturn.ReleasePast len m ∨ 11≤pc x (S.getD 0 fall).1) :
    BStarCopyLeftReturn.ReleasePast len d ∨ 11≤pc (step x e) (S.getD 0 fall).1 := by
  have mono := band_step hp chart sep same e old mark post oldBand newBand
  rcases past with P|late
  · rcases P with atEnd|⟨j,atBack⟩
    · subst m
      cases mark with
      | transit _ _ _ _ seen =>
        have A := seen_cursor hp seen
        cases A with
        | stay => exact .inl (.inl rfl)
        | forward => have I := post.2.1.1; omega
        | turn => exact .inl (.inr ⟨len,rfl⟩)
    · subst m
      cases mark with
      | arrived_hold _ _ => exact .inl (.inr ⟨0,rfl⟩)
      | transit _ _ _ _ seen =>
        have A := seen_cursor hp seen
        cases A with
        | stay => exact .inl (.inr ⟨j,rfl⟩)
        | reverse => exact .inl (.inr ⟨_,rfl⟩)
      | consume _ door rests =>
        have oldPc := old.1.2.2.2
        obtain ⟨head,slot⟩ := BStarResetChartService.root_header hp chart old.1.1
        have old10 : pc x (S.getD 0 fall).1=10 := oldPc
        have enough : 7≤pc (step x e) (S.getD 0 fall).1 := by omega
        have rise := (BStarGeneratedPCAncestry.consume_to_band hp (base:=base) (x:=x)
          (addr:=fun j=>S.getD j fall) (len:=len) (op:=10) (e:=e)
          slot head (sep e) old (.consume 10 door rests) enough newBand.2).1
        change pc (step x e) (S.getD 0 fall).1=11 at rise
        exact .inr (Nat.le_of_eq rise.symm)
  · exact .inr (Nat.le_trans late mono)

/-- After the last outward INJECT release, every subsequent old cut
before a potential FENCE acceptance is either still returning INJECT
or already reads opcode at least 11. No acceptance at the far end is
required. The source transition out of PC10 is the actual consume. -/
theorem release_phase {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m d : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x m w d)
    (valid : LiveAt hp chart x w)
    (init : BStarCopyLeftReturn.ReleasePast len m ∨ 11≤pc x (S.getD 0 fall).1) :
    BStarCopyLeftReturn.ReleasePast len d ∨ 11≤pc (run x w) (S.getD 0 fall).1 := by
  induction G with
  | endpoint _ => exact init
  | @next x m e w d fin I E tail ih =>
    have A := valid [] (e::w) rfl
    have P := valid [e] w rfl
    exact ih (fun a b W=>valid (e::a) b (congrArg (List.cons e) W))
      (past_step hp chart sep e I E (BStarGeneratedTapeCuts.at_start hp tail) A.2 P.2 A.1 init)

/-- Locate the real healthy INJECT consume before the original
outward FENCE terminal. Its old and new controller words are genuine
subwords of this flight, even if the later FENCE eventually fails. -/
theorem inject_ack_between {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x (.busy 10 (.out len)) w (.busy 11 (.out len)))
    (valid : LiveAt hp chart x w) :
    ∃ pre ack post,w=pre++ack::post ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x (.busy 10 (.out len)) pre (.busy 10 (.back 0)) ∧
      BStarNativeReceiptTape.Hit hp base (fun j=>S.getD j fall) len (run x pre) ack 10 ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len (step (run x pre) ack) .idle post (.busy 11 (.out len)) := by
  have old := (BStarGeneratedTapeCuts.at_start hp G).1.2.2.2
  have new := (BStarGeneratedTapeCuts.at_end hp G).1.2.2.2
  change pc x (S.getD 0 fall).1=10 at old
  change pc (run x w) (S.getD 0 fall).1=11 at new
  obtain ⟨pre,ack,post,W,_,P,H,Q,_⟩ := first_ack hp chart sep G valid (by omega)
  rw [old] at P H
  exact ⟨pre,ack,post,W,P,H,Q⟩

private theorem owned_prep_after_release {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (same : ∀ i,Layout B base i=Layout B (run x w) i)
    (phase : BStarCopyLeftReturn.ReleasePast len m ∨ 11≤pc (run x w) (S.getD 0 fall).1)
    (e : Fin n) (a : BStarLongPrep.Offer)
    (own : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val)
    (win : a∈(arbitration (round (oldPair B (run x w) e)
      (((run x w) e).long,((run x w) (rightNeighbor e)).long)).prep).1) :
    (selectedEffects (view (((run x w) e).long,((run x w) (rightNeighbor e)).long)) a).fault=false := by
  apply owned_copy_prep_clean hp chart sep G same e _ a own win
  intro j kind C loc rev port _
  have current := BStarGeneratedTapeCuts.at_end hp G
  rw [kind] at phase current
  rcases phase with last|late
  · rcases last with E|⟨k,E⟩
    · have jEnd := Cursor.out.inj (Mode.busy.inj E).2
      subst j
      have Z : (S.getD len fall).2=10 := chart.terminal ▸ rfl
      have K : C.source.occurrence=10 := (congrArg Prod.snd loc).symm.trans Z
      cases rev <;> simp [sourceOccurrence,K] at port
    · cases E
  · have oldPc := current.1.2.2.2
    change pc (run x w) (S.getD 0 fall).1=10 at oldPc
    omega

private theorem prefix_before_last {α : Type} (tail a b : List α) (ack e : α)
    (W : tail++[ack]=a++e::b) : ∃ rest,tail=a++rest := by
  rcases List.append_eq_append_iff.mp W with ⟨rest,one,two⟩|⟨rest,one,_⟩
  · have N := congrArg List.length two
    cases rest with
    | nil => exact ⟨[],by simpa using one.symm⟩
    | cons first rest => simp at N <;> omega
  · exact ⟨rest,one⟩

private theorem run_invariant {x : X} (w : List (Fin n)) (P : X→Prop) (init : P x)
    (next : ∀ a e b,w=a++e::b → P (run x a) → P (step (run x a) e)) : P (run x w) := by
  induction w generalizing x with
  | nil => exact init
  | cons e w ih =>
    exact ih (next [] e w rfl init) (fun a b c W=>next (e::a) b c (congrArg (List.cons e) W))

/-- Starting at the actual fully emitted outward INJECT cut, recover
the old FENCE guard, canonical unit and inspected vacancy on this same
generated word. The specified turn and consume are physical marks.
Their healthy FENCE receipt and both drained images follow. -/
theorem fence_after_release {L R : Type} (lDigits : L→BitVec 36) (rDigits : R→BitVec 36)
    {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lSeam rSeam rTail : Nat) (pos : 0<r)
    (lbase dest rbase : Fin n) (lRoot : lbase=(S.getD 0 fall).1) (rRoot : dest=(S.getD len fall).1)
    (lJoin : addr lbase lSeam=dest) (rJoin : addr rbase 0=addr dest (r-1))
    (lStrip : BStarCopyLeftStrip.Strip B base lbase lSeam r)
    (rDest : BStarCopyRightRetained.Dest B base dest r)
    (rStrip : BStarCopyRightWrappedGeometry.WrappedStrip B base rbase rSeam rTail)
    (rHead : dataOwner (oldH6 B base) (addr rbase 0) (rail rSeam 0)=o.val)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r≤oldOrdinal B base hh i+1)
    (inject flight back : List (Fin n)) (turn ack : Fin n)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle inject (.busy 10 (.out len)))
    (fly : GeneratedOwner hp base (fun j=>S.getD j fall) len (run origin inject)
      (.busy 10 (.out len)) flight (.busy 11 (.out len)))
    (turnEvent : Event hp (fun j=>S.getD j fall) len (run (run origin inject) flight) turn
      (.busy 11 (.out len)) (.busy 11 (.back len)))
    (ret : BusyOnly hp base (fun j=>S.getD j fall) len 11
      (step (run (run origin inject) flight) turn) (.back len) back (.back 0))
    (consume : Event hp (fun j=>S.getD j fall) len (run (step (run (run origin inject) flight) turn) back) ack
      (.busy 11 (.back 0)) .idle)
    (scope : LiveAt hp chart origin (inject++(flight++turn::back)))
    (init : pc origin (S.getD 0 fall).1=6)
    (lPlan : List L) (rPlan : List R) (lSize : lPlan.length=r) (rSize : rPlan.length=r)
    (ls : Ledger L) (rs : Ledger R) (lLabels : Nat→Option L) (rLabels : Nat→Option R)
    (lEmitted : ls.release.pending=[]) (rEmitted : rs.release.pending=[])
    (lOrdered : OrderedPrefix lPlan ls (headFirst lSeam lLabels))
    (rOrdered : OrderedPrefix rPlan rs (stripWord rTail rLabels))
    (lRetained : BStarCopyLeftRetained.RetainedMatches lDigits (run origin inject) (addr lbase lSeam) r ls)
    (rRetained : BStarCopyRightRetained.RetainedMatches rDigits (run origin inject) dest r rs)
    (lUp : BStarCopyLeftMark.UpstreamMatches lDigits (run origin inject) lbase lSeam lLabels)
    (rUp : BStarCopyRightMark.MobileMatches rDigits (run origin inject) rbase rSeam rTail rLabels)
    (clean : CleanOwner hp base (run origin inject) o.val) :
    let y := run (step (run (run origin inject) flight) turn) back
    let z := step y ack
    BStarNativeReceiptTape.Hit hp base (fun j=>S.getD j fall) len y ack 11 ∧
      laneRead (ldRead z (addr lbase lSeam)) 0 r=lPlan.reverse.map (Digit9.data ∘ lDigits) ∧
      laneRead (rdRead z dest r) 0 r=rPlan.reverse.map (Digit9.data ∘ rDigits) ∧
      (∀ i sh,BStarCopyLeftFenceHold.Region lbase lSeam r i sh →
        (readLane (Sheet.index sh) (z i).long).mobile=.empty) ∧
      (∀ i sh,BStarCopyRightWrappedFenceHold.Region dest rbase r rSeam rTail i sh →
        (readLane (Sheet.index sh) (z i).long).mobile=.empty) := by
  let x := run origin inject
  let before := flight++turn::back
  let marked := flight++turn::(back++[ack])
  have prefixMarked : marked=before++[ack] := by simp only [marked,before,List.append_assoc,List.cons_append]
  have afterTurn : GeneratedOwner hp base (fun j=>S.getD j fall) len (run x flight)
      (.busy 11 (.out len)) (turn::back) (.busy 11 (.back 0)) :=
    .next (BStarGeneratedTapeCuts.at_end hp fly) turnEvent (busy_history hp ret)
  have travel := append_history hp fly afterTurn
  have ⟨setupScope,travelScope⟩ := split_live hp chart scope
  have pcTen : pc x (S.getD 0 fall).1=10 := (BStarGeneratedTapeCuts.at_end hp G).1.2.2.2
  obtain ⟨w9,ack9,gap,W9,G9,E9,N9⟩ := BStarCopyCleanupCuts.accepted_cut hp chart sep G setupScope 9
    (by rw [init]; decide) (by change 9<pc x (S.getD 0 fall).1; rw [pcTen]; decide)
  have setup_absolute (a b : List (Fin n)) (W : before=a++b) :
      LiveAt hp chart origin (inject++a) := by
    intro u v V
    apply scope u (v++b)
    change inject++before=u++(v++b)
    rw [W,←List.append_assoc,V,List.append_assoc]
  have cut_data (a b : List (Fin n)) (W : before=a++b) (e : Fin n) :
      OpenOwner hp base (run x a) o.val ∧
      BStarCopyLeftDataSweep.DataReady hp (run x a) lbase e lSeam r ∧
      BStarCopyRightWrappedSweep.DataReady hp (run x a) dest rbase e r rSeam rTail ∧
      (let y := run x a
       let raw := ((y e).long,(y (rightNeighbor e)).long)
       ∀ q∈(arbitration (round (oldPair B y e) raw).prep).1,
        dataOwner (oldH6 B base) (site e q.claim.lane.side) q.claim.lane.occurrence=o.val →
        (selectedEffects (view raw) q).fault=false) := by
    change flight++turn::back=a++b at W
    obtain ⟨m,T,_⟩ := BStarGeneratedTapeCuts.split hp a b (W ▸ travel)
    have aScope := (split_live hp chart (W ▸ travelScope)).1
    have phase := release_phase hp chart sep T aScope (.inl (.inl rfl))
    have scopeAbs := setup_absolute a b W
    have P := append_history hp G T
    have Z : inject++a=w9++ack9::(gap++a) := by rw [W9,List.append_assoc,List.cons_append]
    have replay : run origin (inject++a)=run x a := BStarResetSchedule.run_append ..
    have phaseAbs : BStarCopyLeftReturn.ReleasePast len m ∨ 11≤pc (run origin (inject++a)) (S.getD 0 fall).1 := by
      rwa [replay]
    have late : 10≤pc (run origin (inject++a)) (S.getD 0 fall).1 := by
      rcases phaseAbs with H|H
      · have I := BStarGeneratedTapeCuts.at_end hp P
        rcases H with E|⟨j,E⟩ <;> rw [E] at I <;> exact Nat.le_of_eq I.1.2.2.2.symm
      · omega
    have openAll := FreshPreparation.gates_after_enable hp chart sep P scopeAbs init late
    have ready := ready_after_enable hp chart sep w9 (gap++a) ack9 e m G9 E9 N9
      (Z ▸ P) (Z ▸ scopeAbs) (Z ▸ phaseAbs) r lSeam rSeam rTail lbase dest rbase lStrip lRoot
      rDest rStrip rJoin rHead
    rw [←Z,replay] at ready
    rw [replay] at openAll
    refine ⟨openAll,ready.1,ready.2,?_⟩
    dsimp only
    intro q win own
    have arena := owned_prep_after_release hp chart sep P (scopeAbs (inject++a) [] (by simp)).1 phaseAbs e q own
    rw [replay] at arena
    exact arena win
  have lReady (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (W : marked=a++e::b) :
      BStarCopyLeftDataSweep.DataReady hp (run x a) lbase e lSeam r := by
    obtain ⟨suffix,H⟩ := prefix_before_last before a b ack e (prefixMarked.symm.trans W)
    exact (cut_data a suffix H e).2.1
  have rReady (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (W : marked=a++e::b) :
      BStarCopyRightWrappedSweep.DataReady hp (run x a) dest rbase e r rSeam rTail := by
    obtain ⟨suffix,H⟩ := prefix_before_last before a b ack e (prefixMarked.symm.trans W)
    exact (cut_data a suffix H e).2.2.1
  have images (a b : List (Fin n)) (W : before=a++b) :
      ∃ l t lm rm, l.release.pending=[] ∧ t.release.pending=[] ∧
        OrderedPrefix lPlan l (headFirst lSeam lm) ∧
        OrderedPrefix rPlan t (stripWord rTail rm) ∧
        BStarCopyLeftRetained.RetainedMatches lDigits (run x a) dest r l ∧
        BStarCopyRightRetained.RetainedMatches rDigits (run x a) dest r t ∧
        BStarCopyLeftMark.UpstreamMatches lDigits (run x a) lbase lSeam lm ∧
        BStarCopyRightMark.MobileMatches rDigits (run x a) rbase rSeam rTail rm := by
    have markScope (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (E : a=u++e::v) :
        marked=u++e::(v++(b++[ack])) := by
      rw [prefixMarked,W,E]
      simp only [List.append_assoc,List.cons_append]
    obtain ⟨l,lm,pL,oL,hL,uL⟩ := BStarCopyLeftDataSweep.data_word hp lDigits x a lbase lSeam r sep
      lPlan lSize ls lLabels lOrdered lRetained lUp (fun u e v E=>lReady u e (v++(b++[ack])) (markScope u e v E))
    obtain ⟨t,rm,pR,oR,hR,uR⟩ := BStarCopyRightWrappedSweep.data_word hp rDigits x a dest rbase r rSeam rTail
      rJoin sep rPlan rSize rs rLabels rOrdered rRetained rUp (fun u e v E=>rReady u e (v++(b++[ack])) (markScope u e v E))
    rw [lJoin] at hL
    exact ⟨l,t,lm,rm,(congrArg BStarCopyInjection.ReleaseHistory.pending pL).trans lEmitted,
      (congrArg BStarCopyInjection.ReleaseHistory.pending pR).trans rEmitted,oL,oR,hL,hR,uL,uR⟩
  have cleanAt (a b : List (Fin n)) (W : before=a++b) : CleanOwner hp base (run x a) o.val := by
    apply run_invariant hp a (fun y=>CleanOwner hp base y o.val) clean
    intro u e v E old
    have raw : before=u++e::(v++b) := by rw [W,E,List.append_assoc,List.cons_append]
    obtain ⟨l,t,_,_,_,_,oL,oR,hL,hR,_,_⟩ := images u (e::(v++b)) raw
    have frame := (travelScope u (e::(v++b)) raw).1
    have endReady := end_ready_of_ledgers hp lDigits rDigits chart e r pos dest rRoot flags notShort frame
      lSize rSize (ordered_prefix oL).1 (ordered_prefix oR).1 hL hR
    have localReady := cut_data u (e::(v++b)) raw e
    exact open_owner_clean_step hp e (sep e) o.val frame old localReady.1 endReady localReady.2.2.2
  have chartFlags := fun i=>(flags i).1
  have fullFlight := append_history hp G fly
  have front := terminal_fence_visited hp chart sep fullFlight (by
    intro a e b W k I visited
    rcases List.append_eq_append_iff.mp W with ⟨gap,prefixEq,Y⟩|⟨gap,prefixEq,_⟩
    · have now : before=gap++e::(b++turn::back) := by change flight++turn::back=_; rw [Y,List.append_assoc,List.cons_append]
      have replay : run origin a=run x gap := by rw [prefixEq,BStarResetSchedule.run_append]
      let old := run x gap
      rw [replay] at I visited ⊢
      obtain ⟨l,t,lm,rm,pL,pR,oL,oR,hL,hR,uL,uR⟩ := images gap (e::(b++turn::back)) now
      have operands := FreshVisitedOperands.on_retaining_visit hp chart r lSeam rSeam rTail pos lbase dest rbase
        rRoot lJoin rJoin lStrip rDest rStrip chartFlags notShort k I.2.1.1 visited lDigits rDigits lPlan rPlan
        l t lm rm lSize rSize oL oR pL pR uL uR hL hR
      rw [rRoot] at operands
      have localReady := cut_data gap (e::(b++turn::back)) now e
      intro C _ ptr
      exact FreshFenceInspection.guard_of_operands hp chart chartFlags notShort I.1.1 k I.2.1.1 e C.source
        ptr localReady.1 (cleanAt gap (e::(b++turn::back)) now) operands.1 operands.2
    · have cap := BStarCopyCleanupOriginal.prefix_pc_le hp chart sep G setupScope a gap prefixEq
      have code := I.1.2.2.2
      change pc (run origin a) (S.getD 0 fall).1=11 at code
      change pc (run origin a) (S.getD 0 fall).1≤pc x (S.getD 0 fall).1 at cap
      omega)
  rw [BStarResetSchedule.run_append step origin inject flight] at front
  obtain ⟨lPastUp,rPastUp,lPast,rPast⟩ := earlier_strip_vacancy hp chart r lSeam rSeam rTail pos lbase dest rbase
    rRoot lJoin rJoin lStrip rDest rStrip chartFlags notShort front.2
  have ownerTerminal : dataOwner (oldH6 B base) dest .rd=o.val := by
    rw [rRoot]
    exact (BStarFenceReceiverChart.endpoints hp chart pos chartFlags notShort).2.2.2.1
  exact through_fence hp lDigits rDigits chart sep r lSeam rSeam rTail pos lbase dest rbase rRoot rJoin
    lPlan rPlan lSize rSize ls rs lLabels rLabels lEmitted rEmitted lOrdered rOrdered lRetained rRetained lUp rUp
    flight back turn ack fly front.1 ret consume lReady rReady lPastUp rPastUp (fun j bound=>lPast j (by omega)) rPast
    (clean dest .rd rfl ownerTerminal).1

/-- Run the fresh operand preparation, INJECT and FENCE on the one
original generated word. The outcome is the true FENCE acceptance
and both literal operand images at that mark, with both data regions
drained. The digit tables are read at the actual INJECT launch. -/
theorem fence_from_issue {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lSeam rSeam rTail : Nat) (pos : 0<r)
    (lbase dest rbase : Fin n) (lRoot : lbase=(S.getD 0 fall).1) (rRoot : dest=(S.getD len fall).1)
    (lJoin : addr lbase lSeam=dest) (rJoin : addr rbase 0=addr dest (r-1))
    (lStrip : BStarCopyLeftStrip.Strip B base lbase lSeam r)
    (lSize : r≤lSeam) (lFlag : ∀ j<lSeam,(longGeometry B (base (addr lbase j))).inside=true ↔ j<r)
    (rDest : BStarCopyRightRetained.Dest B base dest r)
    (rStrip : BStarCopyRightWrappedGeometry.WrappedStrip B base rbase rSeam rTail)
    (rHead : dataOwner (oldH6 B base) (addr rbase 0) (rail rSeam 0)=o.val)
    (rSize : rTail+1=rSeam+r)
    (leftCover : ∀ i,dataOwner (oldH6 B base) i .ls=o.val →
      (longGeometry B (base i)).inside=true → ∃ j,j<lSeam ∧ i=addr lbase j)
    (rightCover : ∀ i,dataOwner (oldH6 B base) i .rs=o.val →
      (longGeometry B (base i)).inside=true → ∃ j,rSeam≤j ∧ j≤rTail ∧ i=addr rbase j)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r≤oldOrdinal B base hh i+1)
    (inject flight back : List (Fin n)) (turn ack : Fin n)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle inject (.busy 10 (.out len)))
    (fly : GeneratedOwner hp base (fun j=>S.getD j fall) len (run origin inject)
      (.busy 10 (.out len)) flight (.busy 11 (.out len)))
    (turnEvent : Event hp (fun j=>S.getD j fall) len (run (run origin inject) flight) turn
      (.busy 11 (.out len)) (.busy 11 (.back len)))
    (ret : BusyOnly hp base (fun j=>S.getD j fall) len 11
      (step (run (run origin inject) flight) turn) (.back len) back (.back 0))
    (consume : Event hp (fun j=>S.getD j fall) len (run (step (run (run origin inject) flight) turn) back) ack
      (.busy 11 (.back 0)) .idle)
    (scope : LiveAt hp chart origin (inject++(flight++turn::back)))
    (init : pc origin (S.getD 0 fall).1=6) :
    ∃ lead launch tour,inject=lead++launch::tour ∧
      let before := run origin (lead++[launch])
      let lDigits := fun i=>FreshOrderedPrefix.frozenDigit (BStarCopyLeftMark.sample before lbase lSeam i)
      let rDigits := fun i=>FreshOrderedPrefix.frozenDigit (BStarCopyRightDeposit.lanes before (addr rbase (rSeam+i)) .rs)
      let y := run (step (run (run origin inject) flight) turn) back
      let z := step y ack
      BStarNativeReceiptTape.Hit hp base (fun j=>S.getD j fall) len y ack 11 ∧
        laneRead (ldRead z (addr lbase lSeam)) 0 r=(pending id r).reverse.map (Digit9.data ∘ lDigits) ∧
        laneRead (rdRead z dest r) 0 r=(planOf (fun i=>i-rSeam) rSeam rTail).reverse.map (Digit9.data ∘ rDigits) ∧
        (∀ i sh,BStarCopyLeftFenceHold.Region lbase lSeam r i sh →
          (readLane (Sheet.index sh) (z i).long).mobile=.empty) ∧
        (∀ i sh,BStarCopyRightWrappedFenceHold.Region dest rbase r rSeam rTail i sh →
          (readLane (Sheet.index sh) (z i).long).mobile=.empty) := by
  have preScope := (split_live hp chart scope).1
  obtain ⟨lead,launch,tour,W,_,_,_,_,last,first,lastBound,_,block,history⟩ :=
    FreshPartialLedgers.prepared_prefixes_from_issue hp chart sep G preScope init lbase lSeam lStrip lRoot lSize lFlag
      dest rbase rSeam rTail rStrip rDest rJoin rHead rSize leftCover rightCover
  let start := lead++[launch]
  let lDigits := fun i=>FreshOrderedPrefix.frozenDigit (BStarCopyLeftMark.sample (run origin start) lbase lSeam i)
  let rDigits := fun i=>FreshOrderedPrefix.frozenDigit (BStarCopyRightDeposit.lanes (run origin start) (addr rbase (rSeam+i)) .rs)
  have cut : tour=tour++[] := (List.append_nil _).symm
  obtain ⟨j,l,t,lLabels,rLabels,old,pL,oL,hL,uL,pR,oR,hR,uR⟩ := history tour [] cut
  have word : inject=start++tour := by simp only [W,start,List.append_assoc,List.cons_append,List.nil_append]
  have canonical := BStarGeneratedTapeCuts.at_end hp G
  have pointed := BStarGeneratedTapeCuts.at_end hp old
  rw [←word] at pointed
  have cursor := (BStarOwnerControlHistory.pointed_unique_forward _ _ _ canonical.2.1 canonical.2.2
    j pointed.2.1.1).mp pointed.2.1.2.1
  subst j
  have releasedL : l.release.pending=[] := by
    simpa [remaining,show last+1-len=0 by omega,pending] using pL
  have blockEnd := (block.address rTail block.valid (Nat.le_refl _)).1
  have releasedR := pR.trans (BStarCopyRightReleaseOrder.pending_after_block (fun i=>i-rSeam)
    rSeam rTail first len block.valid (by omega))
  have replay : run origin inject=run (run origin start) tour := by rw [word,BStarResetSchedule.run_append]
  rw [←replay] at hL uL hR uR
  obtain ⟨clead,claunch,ctour,Q,checked⟩ := FreshPartialLedgers.clean_from_issue hp chart sep G preScope init
    lbase lSeam lStrip lRoot lSize lFlag dest rbase rSeam rTail rStrip rDest rJoin rHead rSize leftCover rightCover
    lJoin rRoot flags notShort
  have safe := (checked ctour [] (List.append_nil _).symm).1
  have original : inject=(clead++[claunch])++ctour := by simp only [Q,List.append_assoc,List.cons_append,List.nil_append]
  rw [←original] at safe
  refine ⟨lead,launch,tour,W,?_⟩
  exact fence_after_release hp lDigits rDigits chart sep lSeam rSeam rTail pos lbase dest rbase lRoot rRoot
    lJoin rJoin lStrip rDest rStrip rHead flags notShort inject flight back turn ack G fly turnEvent ret consume
    scope init (pending id r) (planOf (fun i=>i-rSeam) rSeam rTail) (by simp [pending])
    (by simp [planOf]; omega) l t lLabels rLabels releasedL releasedR oL oR hL hR uL uR safe

#print axioms release_phase
#print axioms inject_ack_between
#print axioms fence_after_release
#print axioms fence_from_issue

end L4.Height.FreshFenceSplice

import Leader.L4.BStarCopyLeftRecovered
import Leader.L4.BStarCopyRightWrappedPostAck
import Leader.L4.Height.FreshFenceGuards

namespace L4.Height.FreshPartialLedgers

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

open AllSizeProtocol BStarTrace BStarLongWork BStarAcquireVisitOrder BStarGeneratedOwner
open BStarSeparatingRail BStarResetMarkAdapter

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

private theorem jumps {x : X} {addr : Nat → Pos n} {len op k j : Nat} {e : Fin n}
    (E : Event hp addr len x e (.busy op (.out k)) (.busy op (.out j))) :
    j=k ∨ j=k+1 := by
  have A : Advance len (.out k) (.out j) := by
    cases E with
    | transit _ _ _ _ N =>
      cases N with
      | cons _ _ q _ tail => cases tail; exact q
  cases A with
  | stay => exact .inl rfl
  | forward => exact .inr rfl

section Left
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarLongPackets BStarLongPrep BStarLongCommandData
open BStarCopyRightStrip (addr)
open BStarCopyLeftStrip BStarCopyLeftMark BStarCopyLeftRetained BStarCopyLeftDataSweep
open BStarCopyLeftReleaseClass BStarCopyLeftReleaseOrder BStarCopyLeftMixed
open BStarCopyLeftInjectPositive BStarCopyLeftDeposit BStarCopyLeftPending BStarCopyDownstream
open BStarCopyLeftRetainedClassify BStarCopyInjection BStarCopyFIFO BStarCopyMarkedLedger BStarCopyFenceSaturation
open BStarClearanceDataChart BStarGeneratedOwner BStarOwnerLaunchOrigin BStarGeneratedBandScan
open BStarResetSchedule BStarSeparatingRail BStarResetMarkAdapter BStarSeparatorControl
open BStarAcquireHistorySample BStarAcquireForwardTrace BStarOwnerControlHistory

/-- Observe every literal prefix of the original outward INJECT, using
the existing left data and typed release transitions. Keep the actual
cursor and its pending source suffix at the observed cut. -/
theorem left_prefixes {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam width end5 : Nat) (strip : Strip B base a seam width)
    (root : a=(S.getD 0 fall).1) (e5 : end5<len)
    (last : S.getD end5 fall=(addr a 0,5)) (ws : width≤seam)
    (ins : ∀ i<seam,(longGeometry B (base (addr a i))).inside=true ↔ i<width)
    {z : Cursor} {w : List (Fin n)}
    (tour : BusyOnly hp base (fun j=>S.getD j fall) len 10 x z w (.out len))
    (f : Payload) (F : project (fun j=>S.getD j fall) (play x w) len=.forward f)
    (clear : f.fault=0) (op : f.opcode.toNat=10)
    (plan : List Tag) (size : plan.length=width) :
    ∀ (k : Nat) (lead : List (Fin n)) (s : Ledger Tag) (lab : Nat→Option Tag),
    z=.out k → x=play origin lead →
    GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle lead (.busy 10 (.out k)) →
    OrderedPrefix plan s (headFirst seam lab) →
    RetainedMatches digits x (addr a seam) width s → UpstreamMatches digits x a seam lab →
    CutVacant x S fall len k false →
    s.release.pending=pending atSource (remaining end5 width (.out k)) →
    (∀ pre e post, w=pre++e::post →
      let y := play x pre
      (∀ j,BStarLongFixedRouting.Layout B base j=BStarLongFixedRouting.Layout B y j) ∧
      Strip B y a seam width ∧
      (∀ j<width,(readLane (Sheet.index .ld) (y (addr (addr a seam) j)).long).gate=true) ∧
      (∀ j<seam,(sample y a seam j).gate=true) ∧
      (∀ m (R : ReleaseAt hp y e a seam (fun t=>S.getD t fall) len m),
        (sample y a seam R.i).frozen=.data (digits (atSource R.i)))) →
    ∀ pre post, w=pre++post →
    ∃ (j : Nat) (t : Ledger Tag) (labels : Nat→Option Tag),
      GeneratedOwner hp base (fun q=>S.getD q fall) len origin .idle (lead++pre) (.busy 10 (.out j)) ∧
      t.release.pending=pending atSource (remaining end5 width (.out j)) ∧
      OrderedPrefix plan t (headFirst seam labels) ∧
      RetainedMatches digits (play x pre) (addr a seam) width t ∧
      UpstreamMatches digits (play x pre) a seam labels := by
  have aff := affine_chart hp chart a seam width end5 strip root e5 last
  generalize endEq : Cursor.out len=d at tour
  induction tour with
  | nil cur =>
    intro k lead s lab Z Y G P held mobile vacant pend ready pre post cut
    cases pre with
    | nil =>
      exact ⟨k,s,lab,by simpa using G,pend,P,held,mobile⟩
    | cons a pre => simp at cut
  | @cons x z d fin e w I E rest ih =>
    intro k lead s lab Z Y G P held mobile vacant pend ready pre post cut
    cases pre with
    | nil =>
      exact ⟨k,s,lab,by simpa using G,pend,P,held,mobile⟩
    | cons rawMark pre =>
      change e::w=rawMark::(pre++post) at cut
      obtain ⟨sameMark,tailCut⟩ := List.cons.inj cut
      subst rawMark
      subst z
      have goalRest : BusyOnly hp base (fun t=>S.getD t fall) len 10 (ring x e) d w (.out len) := endEq.symm ▸ rest
      obtain ⟨j,D⟩ := busy_no_back_to_out hp goalRest ⟨len,rfl⟩
      subst d
      have cur2 := busy_start hp rest
      obtain ⟨same,U,rg,ug,cap⟩ := ready [] e w rfl
      obtain ⟨rnp,q⟩ := classify_release hp chart sep lead (.busy 10 (.out k)) G (Y ▸ same)
        ((Y ▸ I).1.2.2.2) a e seam width strip root
      have RNP : NoLDPrep hp x (addr a seam) e width := Y.symm ▸ rnp
      have Q : NoLSPrep hp x a e seam ∨
          Nonempty (ReleaseAt hp x e a seam (fun t=>S.getD t fall) len (.busy 10 (.out k))) := Y.symm ▸ q
      have Ok : ∃ (t : Ledger Tag) (next : Nat→Option Tag),
        t.release.pending=pending atSource (remaining end5 width (.out j)) ∧
        OrderedPrefix plan t (headFirst seam next) ∧
        RetainedMatches digits (ring x e) (addr a seam) width t ∧ UpstreamMatches digits (ring x e) a seam next := by
        rcases Q with quiet|hasRelease
        · obtain ⟨t,next,R,W,H,M⟩ := data_mark hp digits x a e seam width U (sep e)
            s plan size lab P held mobile rg ug RNP quiet
          have V := BStarCopyLeftInjectFold.quiet_keeps_pending hp atSource chart sep a e seam width end5 k j ws e5 aff ins I E goalRest
            f F clear op quiet
          exact ⟨t,next,(congrArg ReleaseHistory.pending R).trans (pend.trans V.symm),W,H,M⟩
        · obtain ⟨rs⟩ := hasRelease
          have rsK : rs.k=k := (Cursor.out.inj (Mode.busy.inj rs.mode).2).symm
          have idx : k=end5-rs.i := by
            have Al := (aff rs.i rs.range).2
            have lens := chart.length
            exact rsK.symm.trans ((List.getD_inj (by have := rs.strict; omega)
              (by omega) chart.nodup).mp (rs.ptr.trans Al.symm))
          have rIn := release_inside hp rs
          have oldIn := congrArg (fun z : Bool × Bool × Bool => z.2.1) (same (addr a rs.i))
          have wi : rs.i<width := (ins rs.i rs.range).mp (oldIn.trans rIn)
          have l := (aff rs.i rs.range).1
          have ⟨pOld,pNew⟩ := remaining_at_actual_k5 end5 width rs.i wi l
          rw [idx] at pend
          rw [pOld,pending_succ] at pend
          have eR : Event hp (fun t=>S.getD t fall) len x e (.busy 10 (.out rs.k)) (.busy 10 (.out j)) :=
            rsK.symm ▸ E
          have past := release_before_later hp (base:=base) rs (sep e) eR (.nil cur2)
          have jEq : j=k+1 := by rcases jumps hp E with H|H <;> omega
          have pp : pending atSource (remaining end5 width (.out j))=pending atSource rs.i := congrArg (pending atSource) ((congrArg (fun t => remaining end5 width (.out t)) (jEq.trans (congrArg (·+1) idx))).trans pNew)
          have G' := rsK.symm ▸ I
          have V : CutVacant x S fall len rs.k false := rsK.symm ▸ vacant
          by_cases ord : 0<rs.i ∨ seam<n
          · obtain ⟨t,R,W,H,M⟩ := ordinary_release hp digits atSource chart a e seam width strip U root same
              _ rs G'.2.1 G'.2.2 (sep e) ord s plan size lab P held mobile rg RNP (ug _ rs.range) (cap _ rs) V pend
            exact ⟨t,_,(congrArg ReleaseHistory.pending R).trans pp.symm,W,H,M⟩
          · have si : rs.i=0 := by omega
            have ss : seam=n := by have := U.seam_le; omega
            subst seam
            have P0 : s.release.pending=[atSource 0] := by
              rw [pend,si]; rfl
            have Cp : (sample x a n 0).frozen=.data (digits (atSource 0)) := si ▸ cap _ rs
            obtain ⟨t,q,R,W,H,M⟩ := sole_release hp digits (atSource 0) chart a e width strip U root same
              _ rs si G'.2.1 G'.2.2 (sep e) s plan size lab P held mobile (rg 0 U.width_pos)
              (ug (n-1) (by have := U.seam_pos; omega)) RNP (ug 0 U.seam_pos) Cp V P0
            have Hpp : pending atSource (remaining end5 width (.out j))=[] := by rw [pp,si]; rfl
            exact ⟨t,q,(congrArg ReleaseHistory.pending R).trans Hpp.symm,W,H,M⟩
      obtain ⟨t,labels,pend',ltag,held',mobile'⟩ := Ok
      have mono : k≤j := by rcases jumps hp E with H|H <;> omega
      have V := cut_vacant_step hp chart e (sep e) 10 k j false I cur2 mono vacant
      have after : ring x e=play origin (lead++[e]) := by
        rw [BStarResetSchedule.run_append,←Y]; rfl
      have progress := generated_append hp G (Y ▸ GeneratedOwner.next I E (.endpoint cur2))
      obtain ⟨q,u,next,history,pending,ordered,image,upstream⟩ :=
        ih F endEq j (lead++[e]) t labels rfl after progress ltag held' mobile' V pend'
          (fun u mark v Eq=>ready (e::u) mark v (congrArg (List.cons e) Eq)) pre post tailCut
      have rejoin : (lead++[e])++pre=lead++e::pre := by rw [List.append_assoc] <;> rfl
      exact ⟨q,u,next,rejoin ▸ history,pending,ordered,image,upstream⟩

end Left

section Right
open BStarCopyRightInjectFold BStarCopyRightScopedDeposit BStarCopyActiveVacancy
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarLongPackets BStarLongPrep BStarLongCommandData
open BStarCopyRightStrip BStarCopyRightMark BStarCopyRightRetained BStarCopyRightDataSweep
open BStarCopyRightReleaseClass BStarCopyRightInjectStep BStarCopyRightReleaseOrder
open BStarCopyRightInjectPositive BStarCopyRightDeposit BStarCopyRightMixed BStarCopyDownstream
open BStarCopyRightK2 BStarCopyRightRetainedClassify BStarCopyInjection BStarCopyFIFO BStarCopyMarkedLedger BStarCopyFenceSaturation
open BStarClearanceDataChart BStarGeneratedOwner BStarOwnerLaunchOrigin BStarGeneratedBandScan
open BStarResetSchedule BStarSeparatingRail BStarResetMarkAdapter BStarSeparatorControl
open BStarAcquireHistorySample BStarAcquireForwardTrace BStarOwnerControlHistory
open BStarCopyRightWrappedGeometry BStarCopyRightWrappedSweep BStarCopyRightWrappedRelease


/-- Observe the original wrapped-right INJECT at any literal prefix.
Its pending source suffix is the one associated to the actual cursor. -/
theorem right_prefixes {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (root a : Fin n) (width seam tail first : Nat)
    (dest : Dest B base root width) (strip : WrappedStrip B base a seam tail)
    (join : addr a 0=addr root (width-1))
    (own : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (block : K2Block S len fall a seam tail first)
    {z : Cursor} {w : List (Fin n)}
    (tour : BusyOnly hp base (fun j=>S.getD j fall) len 10 x z w (.out len))
    (f : Payload) (F : project (fun j=>S.getD j fall) (play x w) len=.forward f)
    (clear : f.fault=0) (op : f.opcode.toNat=10)
    (size : (planOf atSource seam tail).length=width) :
    ∀ (k : Nat) (lead : List (Fin n)) (s : Ledger Tag) (lab : Nat→Option Tag),
    z=.out k → x=play origin lead →
    GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle lead (.busy 10 (.out k)) →
    OrderedPrefix (planOf atSource seam tail) s (stripWord tail lab) →
    RetainedMatches digits x root width s → MobileMatches digits x a seam tail lab →
    ActiveCutVacant hp x S fall len k true →
    s.release.pending=PendingAt atSource seam tail first k →
    (∀ pre e post, w=pre++e::post →
      let y := play x pre
      (∀ j,BStarLongFixedRouting.Layout B base j=BStarLongFixedRouting.Layout B y j) ∧
      Dest B y root width ∧ WrappedStrip B y a seam tail ∧
      (∀ j<width,(readLane (Sheet.index .rd) (y (addr root j)).long).gate=true) ∧
      (∀ j,0<j → j≤tail → (readLane (Sheet.index (rail seam j)) (y (addr a j)).long).gate=true) ∧
      (∀ m (R : ReleaseAt hp y e a seam tail (fun t=>S.getD t fall) len m),
        (lanes y (addr a R.i) .rs).frozen=.data (digits (atSource R.i)))) →
    ∀ pre post, w=pre++post →
    ∃ (j : Nat) (t : Ledger Tag) (labels : Nat→Option Tag),
      GeneratedOwner hp base (fun q=>S.getD q fall) len origin .idle (lead++pre) (.busy 10 (.out j)) ∧
      t.release.pending=PendingAt atSource seam tail first j ∧
      OrderedPrefix (planOf atSource seam tail) t (stripWord tail labels) ∧
      RetainedMatches digits (play x pre) root width t ∧
      MobileMatches digits (play x pre) a seam tail labels := by
  generalize endEq : Cursor.out len=d at tour
  induction tour with
  | nil cur =>
    intro k lead s lab Z Y G P held mobile vacant pending ready pre post cut
    cases pre with
    | nil =>
      exact ⟨k,s,lab,by simpa using G,pending,P,held,mobile⟩
    | cons a pre => simp at cut
  | @cons x z d fin e w I E rest ih =>
    intro k lead s lab Z Y G P held mobile vacant pending ready pre post cut
    cases pre with
    | nil =>
      exact ⟨k,s,lab,by simpa using G,pending,P,held,mobile⟩
    | cons rawMark pre =>
      change e::w=rawMark::(pre++post) at cut
      obtain ⟨sameMark,tailCut⟩ := List.cons.inj cut
      subst rawMark
      subst z
      have goalRest : BusyOnly hp base (fun t=>S.getD t fall) len 10 (ring x e) d w (.out len) := endEq.symm ▸ rest
      obtain ⟨j,D⟩ := busy_no_back_to_out hp goalRest ⟨len,rfl⟩
      subst d
      have cur2 := busy_start hp rest
      obtain ⟨same,C,U,rg,ug,cap⟩ := ready [] e w rfl
      let plan := planOf atSource seam tail
      obtain ⟨rnp,q⟩ := BStarCopyRightWrappedReleaseClass.classify_release hp chart sep lead (.busy 10 (.out k)) G (Y ▸ same)
        ((Y ▸ I).1.2.2.2) root a e width seam tail dest strip join own
      have RNP : NoRDPrep hp x root e width := Y.symm ▸ rnp
      have Q : NoUpPrep hp x a e seam tail ∨
          Nonempty (ReleaseAt hp x e a seam tail (fun t=>S.getD t fall) len (.busy 10 (.out k))) := Y.symm ▸ q
      have Ok : ∃ (t : Ledger Tag) (next : Nat→Option Tag),
        t.release.pending=PendingAt atSource seam tail first j ∧
        OrderedPrefix plan t (stripWord tail next) ∧
        RetainedMatches digits (ring x e) root width t ∧ MobileMatches digits (ring x e) a seam tail next := by
        rcases Q with quiet|hasRelease
        · obtain ⟨t,next,R,W,H,M⟩ := data_mark hp digits x root a e width seam tail C U join (sep e)
            s plan size lab P held mobile rg ug RNP quiet
          have V := BStarCopyRightWrappedActiveFold.quiet_keeps_pending hp atSource chart sep a e seam tail first k j strip block I E goalRest
            f F clear op quiet
          exact ⟨t,next,(congrArg ReleaseHistory.pending R).trans (pending.trans V.symm),W,H,M⟩
        · obtain ⟨rs⟩ := hasRelease
          have rsK : rs.k=k := (Cursor.out.inj (Mode.busy.inj rs.mode).2).symm
          have idx : k=first+(rs.i-seam) := rsK.symm.trans (release_position hp chart block rs)
          have pp := pending_release atSource seam tail first k rs.i rs.range.1 rs.range.2 idx
          have next := release_advances hp rs (sep e) E cur2
          have jEq : j=k+1 := (Cursor.out.inj (Mode.busy.inj next).2).trans (congrArg (·+1) rsK)
          have behind (m : Nat) (a1 : rs.i≤m) (a2 : m≤tail) :
              Unvisited S fall len k true (addr a m) := by
            obtain ⟨K,E⟩ := block.address m (Nat.le_trans rs.range.1 a1) a2
            exact ⟨first+(m-seam),by omega,Nat.le_of_lt K,E⟩
          have rsh : rail seam rs.i=.rs := if_neg (by have := rs.range.1; omega)
          have gp := ug rs.i (Nat.lt_of_lt_of_le U.seam_pos rs.range.1) rs.range.2
          rw [rsh] at gp
          have emptyBehind : ∀ m, rs.i≤m → m≤tail → lab m=none := by
            intro m mm mt
            have ss : seam≤m := Nat.le_trans rs.range.1 mm
            have pos : 0<m := Nat.lt_of_lt_of_le U.seam_pos ss
            have old := mobile m pos mt
            have H : rail seam m=.rs := if_neg (by omega)
            rw [H] at old
            have inside := U.rs_in m ss mt
            have U0 := vacant _ (behind m mm mt) (by exact inside)
            change (readLane (Sheet.index .rs) (x (addr a m)).long).mobile=.empty at U0
            rw [U0] at old
            cases h : lab m with
            | none => rfl
            | some tag => rw [h] at old; contradiction
          obtain ⟨v,newLab,R,W,H,M⟩ := wrapped_release_mark hp digits atSource x root a e width seam tail rs.i C U
            join (sep e) s size lab P held mobile rg ug RNP rs.range.1 rs.range.2 rs.markAt rs.only rs.win
            gp (cap _ rs) emptyBehind (pending.trans pp.1)
          have nextP := (congrArg ReleaseHistory.pending R).trans pp.2.symm
          rw [←jEq] at nextP
          exact ⟨v,newLab,nextP,W,H,M⟩
      obtain ⟨t,labels,pend,ltag,held',mobile'⟩ := Ok
      have mono : k≤j := by rcases jumps hp E with G'|G' <;> omega
      have V := active_step hp chart e (sep e) 10 k j true I cur2 mono vacant
      have after : ring x e=play origin (lead++[e]) := by
        rw [BStarResetSchedule.run_append,←Y]; rfl
      have progress := generated_append hp G (Y ▸ GeneratedOwner.next I E (.endpoint cur2))
      obtain ⟨q,u,next,history,pending,ordered,image,upstream⟩ :=
        ih F endEq j (lead++[e]) t labels rfl after progress ltag held' mobile' V pend
          (fun u mark v Eq=>ready (e::u) mark v (congrArg (List.cons e) Eq)) pre post tailCut
      have rejoin : (lead++[e])++pre=lead++e::pre := by rw [List.append_assoc] <;> rfl
      exact ⟨q,u,next,rejoin ▸ history,pending,ordered,image,upstream⟩

end Right

section LeftIssue
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarClearanceSource BStarLongFixedRouting
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarH6Ordinal
open BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarNativeReceiptTape BStarGeneratedTapeCuts BStarAcquireHistoryReturn
open BStarCopyRightStrip (addr)
open BStarClearanceDataChart
open BStarCopyLeftStrip BStarCopyLeftReleaseClass BStarCopyLeftReleaseOrder BStarCopyLeftMark
open BStarCopyLeftReturn BStarCopyLeftGeometryWord BStarCopyLeftRetained
open BStarCopyLeftPending BStarCopyLeftInjectFold BStarCopyLeftDeposit BStarCopyLeftFence
open BStarCopyMarkedLedger BStarCopyFenceSaturation BStarCopyLaunchEntry
open BStarCopyLeftFenceHold BStarCopyLeftDataSweep BStarLongPackets BStarCopyFenceCuts

/-- Authenticate every partial left INJECT ledger from the original
ISSUE6 word, accepted ENABLE, exact ISSUE10 launch and selected
frozen inputs. The ending cursor of the observed prefix is arbitrary. -/
theorem left_from_issue {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (digits : Nat→BitVec 36) (a : Fin n) (seam width : Nat) (strip : Strip B base a seam width)
    (root : a=(S.getD 0 fall).1) (ws : width≤seam)
    (flag : ∀ j<seam,(longGeometry B (base (addr a j))).inside=true ↔ j<width)
    (start tour lead10 : List (Fin n)) (issue10 : Fin n)
    (preIssue : start=lead10++[issue10])
    (idle10 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead10 .idle)
    (startPC : pc origin (S.getD 0 fall).1≤6)
    (oldPC : pc (play origin lead10) (S.getD 0 fall).1=10)
    (Gstart : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle start (.busy 10 (.out 0)))
    (P10 : BusyOnly hp base (fun j=>S.getD j fall) len 10
      (play origin start) (.out 0) tour (.out len))
    (w9 gap : List (Fin n)) (ack9 : Fin n)
    (enableCut : start=w9++ack9::gap)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event9 : Event hp (fun j=>S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted9 : pc (ring (play origin w9) ack9) (S.getD 0 fall).1=10)
    (full : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (start++tour) (.busy 10 (.out len)))
    (valid : LiveAt hp chart origin (start++tour))
    (f : Payload) (F : project (fun j=>S.getD j fall) (play (play origin start) tour) len=.forward f)
    (clear : f.fault=0) (op : f.opcode.toNat=10)
    (cap : ∀ u e v,tour=u++e::v →
      ∀ m (R : ReleaseAt hp (play (play origin start) u) e a seam (fun j=>S.getD j fall) len m),
      (sample (play (play origin start) u) a seam R.i).frozen=.data (digits R.i)) :
    let plan := pending id width
    ∃ end5,end5<len ∧ S.getD end5 fall=(addr a 0,5) ∧
    ∀ pre post,tour=pre++post →
      ∃ (j : Nat) (t : Ledger Nat) (labels : Nat→Option Nat),
        GeneratedOwner hp base (fun q=>S.getD q fall) len origin .idle (start++pre) (.busy 10 (.out j)) ∧
        t.release.pending=pending id (remaining end5 width (.out j)) ∧
        OrderedPrefix plan t (headFirst seam labels) ∧
        RetainedMatches digits (play (play origin start) pre) (addr a seam) width t ∧
        UpstreamMatches digits (play (play origin start) pre) a seam labels := by
  dsimp only
  let y := play origin start
  let plan := pending (id : Nat→Nat) width
  have totalEq : start++tour=w9++ack9::(gap++tour) := by
    rw [enableCut]
    simp only [List.append_assoc,List.cons_append]
  have G := left_gates_word hp chart sep w9 (gap++tour) ack9 (.busy 10 (.out len))
    G9 event9 accepted9 (totalEq ▸ full) (fun u v E=>valid u v (totalEq.trans E))
    a seam width strip root
  have initial : GeometryGates hp base y a seam width := by
    have H := G gap tour rfl
    rw [←enableCut] at H
    exact H
  have later (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (E : tour=u++e::v) :
      GeometryGates hp base (play y u) a seam width := by
    have H := G (gap++u) (e::v) (by rw [E,List.append_assoc])
    have tape : w9++ack9::(gap++u)=start++u := by
      rw [enableCut]
      simp only [List.append_assoc,List.cons_append]
    rw [tape,BStarResetSchedule.run_append] at H
    exact H
  have yEq : y=ring (play origin lead10) issue10 := by
    change play origin start=_
    rw [preIssue,BStarResetSchedule.run_append]
    rfl
  have iy : Current hp base (fun j=>S.getD j fall) len y (.busy 10 (.out 0)) := busy_start hp P10
  have clr := launch_drained hp chart sep idle10
    (fun u v E=>valid u (v++issue10::tour) (by simp only [preIssue,E,List.append_assoc,List.singleton_append]))
    startPC oldPC (yEq ▸ iy)
  have cleanY : BStarCopyCleanupWindow.DrainedOwner hp base y o.val := yEq.symm ▸ clr
  have owned := BStarCopyLeftReadyWord.all_owner hp chart a seam width strip root
  have up : ∀ j<seam,dataOwner (oldH6 B base) (addr a j) .ls=o.val :=
    fun j J => by simpa [rail,J] using owned j (by omega)
  have ld : ∀ j<width,dataOwner (oldH6 B base) (addr (addr a seam) j) .ld=o.val := by
    intro j J
    rw [address_add]
    simpa [rail,show ¬seam+j<seam by omega] using owned (seam+j) (by omega)
  obtain ⟨P,old,mob,vac⟩ := left_of_drained hp digits plan chart (addr a seam) a width seam
    (dest_of_strip hp y a seam width initial.strip) up ld cleanY
  obtain ⟨end5,es,K⟩ := k5_ordinal hp chart a seam width 0 strip root strip.seam_pos
  have aft : width≤end5+1 := by
    have F := affine_chart hp chart a seam width end5 strip root es K (seam-1) (by have := strip.seam_pos; omega)
    omega
  have pend : (Ledger.init plan).release.pending=pending id (remaining end5 width (.out 0)) := by
    change plan=pending id (min width (end5+1-0))
    rw [Nat.sub_zero,Nat.min_eq_left aft]
  have size : plan.length=width := by simp [plan,pending]
  refine ⟨end5,es,K,?_⟩
  exact left_prefixes hp digits id chart sep a seam width end5 strip root es K ws flag
    P10 f F clear op plan size 0 start (Ledger.init plan) (fun _=>none) rfl rfl Gstart P old mob
    (cutVacant_of_active hp y S fall len 0 vac) pend (fun u e v E => by
      obtain ⟨L,C,DL,LS⟩ := later u e v E
      exact ⟨L,C,DL,LS,cap u e v E⟩)

end LeftIssue

section RightIssue
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongEvents BStarLongCommand BStarLongTransport BStarLongPrep
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarCopyRightStrip BStarCopyRightReleaseClass BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarSeparatingRail BStarAcquireHistoryReturn BStarOwnerControlHistory
open BStarClearanceCommandFrame
open BStarSeparatorControl BStarResetMarkAdapter
open BStarCopyRightReleaseCapture BStarCopyRightLoadToInject BStarCopyRightDeposit
open BStarClearanceDataChart BStarCommitOperands BStarLongPublication BStarLongDoor
open BStarLongFixedRouting BStarGeneratedBandScan BStarClearanceSource
open BStarCaptureDoorHistory BStarLongLayout
open BStarCopyRightReleaseCursor BStarCopyRightActiveFold BStarCopyRightMixed BStarCopyRightReleaseOrder
open BStarCopyRightRetained BStarCopyRightMark BStarCopyMarkedLedger BStarCopyFenceSaturation
open BStarCopyRightGeometryWord BStarCopyRightReturn BStarCopyLaunchEntry
open BStarCopyRightReleaseOrder (K2Block PendingAt)

/-- Authenticate every partial wrapped-right INJECT ledger from the
original setup and accepted ENABLE, with the exact old source table. -/
theorem right_from_issue {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam tail : Nat) (strip : BStarCopyRightWrappedGeometry.WrappedStrip B base a seam tail)
    (ownHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (width : tail+1=seam+r)
    (digits : Nat→BitVec 36)
    (start tour : List (Fin n))
    (G10 : GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle start (.busy 10 (.out 0)))
    (P10 : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (play origin (start)) (.out 0) tour (.out len))
    (cap : ∀ u e v,tour=u++e::v →
      ∀ m (R : ReleaseAt hp (play (play origin start) u) e a seam tail (fun j=>S.getD j fall) len m),
      (lanes (play (play origin start) u) (addr a R.i) .rs).frozen=.data (digits (R.i-seam)))
    (root : Fin n) (dest : Dest B base root r)
    (join : addr a 0=addr root (r-1))
    (lead10 : List (Fin n)) (issue10 : Fin n)
    (preIssue : start=lead10++[issue10])
    (idle10 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead10 .idle)
    (startPC : pc origin (S.getD 0 fall).1≤6)
    (oldPC : pc (play origin lead10) (S.getD 0 fall).1=10)
    (w9 gap : List (Fin n)) (ack9 : Fin n)
    (enableCut : start=w9++ack9::gap)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event9 : Event hp (fun j=>S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted9 : pc (ring (play origin w9) ack9) (S.getD 0 fall).1=10)
    (full : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle ((start)++tour) (.busy 10 (.out len)))
    (valid : ∀ u v,((start)++tour)=u++v →
      (∀ i,Layout B base i=Layout B (play origin u) i) ∧ Band (play origin u) (S.getD 0 fall).1)
    (f : Payload) (F : project (fun j=>S.getD j fall) (play (play origin (start)) tour) len=.forward f)
    (clear : f.fault=0) (op : f.opcode.toNat=10) :
    let atSource := fun i : Nat=>i-seam
    let plan := planOf atSource seam tail
    ∃ first,BStarCopyRightReleaseOrder.K2Block S len fall a seam tail first ∧
    ∀ pre post,tour=pre++post →
      ∃ (j : Nat) (t : Ledger Nat) (labels : Nat→Option Nat),
        GeneratedOwner hp base (fun q=>S.getD q fall) len origin .idle (start++pre) (.busy 10 (.out j)) ∧
        t.release.pending=PendingAt atSource seam tail first j ∧
        OrderedPrefix plan t (stripWord tail labels) ∧
        RetainedMatches digits (play (play origin start) pre) root r t ∧
        MobileMatches digits (play (play origin start) pre) a seam tail labels := by
  dsimp only
  let lead := start
  let y := play origin lead
  let labelAt := fun i : Nat => i-seam
  have totalEq : ((start)++tour)=w9++ack9::(gap++tour) := by
    rw [enableCut]
    simp only [List.append_assoc,List.cons_append]
  have scopedValid (u v : List (Fin n)) (E : w9++ack9::(gap++tour)=u++v) := valid u v (totalEq.trans E)
  have gates := BStarCopyRightWrappedGates.right_gates_word hp chart sep w9 (gap++tour) ack9 (.busy 10 (.out len)) G9 event9
    accepted9 (totalEq ▸ full) scopedValid root a r seam tail dest strip join ownHead
  have initialGates : BStarCopyRightWrappedGates.Gates hp base y root a r seam tail := by
    have H := gates gap tour rfl
    rw [←enableCut] at H
    exact H
  have later (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (E : tour=u++e::v) :
      BStarCopyRightWrappedGates.Gates hp base (play y u) root a r seam tail := by
    have H := gates (gap++u) (e::v) (by rw [E,List.append_assoc])
    have tape : w9++ack9::(gap++u)=lead++u := by
      change _=(start)++u
      rw [enableCut]
      simp only [List.append_assoc,List.cons_append]
    rw [tape,BStarResetSchedule.run_append] at H
    exact H
  have yEq : y=ring (play origin lead10) issue10 := by
    change play origin (start)=_
    rw [preIssue,BStarResetSchedule.run_append]
    rfl
  have iy : Current hp base (fun j=>S.getD j fall) len y (.busy 10 (.out 0)) := busy_start hp P10
  have clr := launch_drained hp chart sep idle10
    (fun u v E => valid u (v++issue10::tour) (by simp only [preIssue,E,List.append_assoc,List.singleton_append]))
    startPC oldPC (yEq ▸ iy)
  have cleanY : BStarCopyCleanupWindow.DrainedOwner hp base y o.val := yEq.symm ▸ clr
  obtain ⟨first,block⟩ := BStarCopyRightWrappedReleaseClass.k2_block hp chart a seam tail strip ownHead
  obtain ⟨P,old,mob,vac,pending⟩ := BStarCopyRightWrappedEntry.right_of_drained hp digits labelAt chart root a r seam tail first
    initialGates.dest initialGates.strip join ownHead initialGates.same cleanY
  have size : (planOf labelAt seam tail).length=r := by simp [planOf]; omega
  refine ⟨first,block,?_⟩
  exact right_prefixes hp digits labelAt chart sep root a r seam tail first dest strip join ownHead
    block P10 f F clear op size 0 lead _ _ rfl rfl G10 P old mob vac pending (fun u e v E => by
      obtain ⟨L,C,U,rg,ug⟩ := later u e v E
      exact ⟨L,C,U,rg,ug,cap u e v E⟩)

end RightIssue

section Issue
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongEvents BStarLongPackets BStarLongTransport
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarLongFixedRouting BStarResetMarkAdapter BStarClearanceDataChart
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail BStarGeneratedBandScan
open BStarCopyFenceCuts BStarCopyFenceSaturation BStarCopyMarkedLedger
open BStarCopyRightStrip (addr rail)
open BStarCopyLeftDeposit (headFirst)
open BStarCopyLeftPending (pending)
open BStarCopyRightMark (stripWord)
open BStarCopyRightMixed (planOf)
open BStarLongCommandData BStarLongPrep BStarLongLiteral BStarResetQuiet
open BStarCopyInjection (sourceLane sourceOccurrence)
open BStarResetSchedule (Seen)
open BStarSeparatorControl (anyTag)
open BStarResetRailRing (old_read new_read)
open BStarResetChartTouch BStarAcquireForwardTrace
open BStarLongDoor BStarClearanceSource
open BStarLongFiberOwner (cmdDispl dataDispl)
open BStarCopyRightLoadToInject (OwnMiddle)
open FreshOrderedPrefix
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

private theorem read_frozen {a b : Lane} (same : a.frozen=b.frozen)
    (valid : ∃ d : BitVec 36,a.frozen=.data d) :
    a.frozen=.data (frozenDigit b) := by
  obtain ⟨d,V⟩ := valid
  have old := same.symm.trans V
  simp [frozenDigit,old,V]

private theorem prefix_at_front {base origin : X} {S : List (Pos n)} {len : Nat}
    {fall : Pos n} {d : Mode} (pre tail : List (Fin n)) (k : Nat)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (pre++tail) d)
    (cur : Current hp base (fun j=>S.getD j fall) len (run origin pre) (.busy 10 (.out k))) :
    GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle pre (.busy 10 (.out k)) := by
  obtain ⟨mode,P,old⟩ := BStarCopyGateAuthority.history_prefix hp pre tail G
  cases mode with
  | idle =>
    exact ((by decide : (1:Nat)≠2) (old.1.2.symm.trans cur.1.2.2.1)).elim
  | busy op z =>
    have eq : op=10 := old.1.2.2.2.symm.trans cur.1.2.2.2
    subst op
    cases z with
    | back j =>
      exact (BStarOwnerControlHistory.pointed_backward_no_forward _ _ _ old.2.1 k
        cur.2.1.1 cur.2.1.2.1).elim
    | out j =>
      have K := (BStarOwnerControlHistory.pointed_unique_forward _ _ _ old.2.1 old.2.2 k
        cur.2.1.1).mp cur.2.1.2.1
      subst j
      exact P

/-- Both partial ledgers are initialized by the old physical setup and
follow one original unreduced outward INJECT tape. At every cut they
share the actual cursor but keep the independent pending suffixes. -/
private theorem busy_generated {base x : X} {slots : Nat→Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)} (P : BusyOnly hp base slots len op x z w d) :
    GeneratedOwner hp base slots len x (.busy op z) w (.busy op d) := by
  induction P with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

theorem prepared_prefixes_from_issue {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy 10 (.out len)))
    (scope : LiveAt hp chart origin w) (init : pc origin (S.getD 0 fall).1=6)
    (lroot : Fin n) (lSeam : Nat) (lStrip : BStarCopyLeftStrip.Strip B base lroot lSeam r)
    (lRoot : lroot=(S.getD 0 fall).1) (lSize : r≤lSeam)
    (lFlag : ∀ j<lSeam,(longGeometry B (base (addr lroot j))).inside=true ↔ j<r)
    (rroot rbase : Fin n) (rSeam rTail : Nat)
    (rStrip : BStarCopyRightWrappedGeometry.WrappedStrip B base rbase rSeam rTail)
    (rDest : BStarCopyRightRetained.Dest B base rroot r)
    (rJoin : addr rbase 0=addr rroot (r-1))
    (rOwner : dataOwner (oldH6 B base) (addr rbase 0) (rail rSeam 0)=o.val)
    (rSize : rTail+1=rSeam+r)
    (leftCover : ∀ i,dataOwner (oldH6 B base) i .ls=o.val →
      (longGeometry B (base i)).inside=true → ∃ j,j<lSeam ∧ i=addr lroot j)
    (rightCover : ∀ i,dataOwner (oldH6 B base) i .rs=o.val →
      (longGeometry B (base i)).inside=true → ∃ j,rSeam≤j ∧ j≤rTail ∧ i=addr rbase j) :
    ∃ lead launch tour, w=lead++launch::tour ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead .idle ∧
      pc (run origin lead) (S.getD 0 fall).1=10 ∧
      project (fun j=>S.getD j fall) (run origin w) len=.forward injectUnit ∧
      (∀ a e b,w=a++e::b → ∀ k,
        Current hp base (fun j=>S.getD j fall) len (run origin a) (.busy 10 (.out k)) →
        ∀ C : CommandClaim,S.getD k fall=address e C.source →
          ReadyPort (oldPair B (run origin a) e) (((run origin a) e).long,((run origin a) (rightNeighbor e)).long) C) ∧
      let before := run origin (lead++[launch])
      let lDigits := fun i=>frozenDigit (BStarCopyLeftMark.sample before lroot lSeam i)
      let rDigits := fun i=>frozenDigit (BStarCopyRightDeposit.lanes before (addr rbase (rSeam+i)) .rs)
      ∃ last first,last<len ∧ S.getD last fall=(addr lroot 0,5) ∧
        BStarCopyRightReleaseOrder.K2Block S len fall rbase rSeam rTail first ∧
        ∀ pre post,tour=pre++post →
          let old := run before pre
          ∃ (j : Nat) (l t : Ledger Nat) (ql qr : Nat→Option Nat),
            GeneratedOwner hp base (fun u=>S.getD u fall) len origin .idle
              ((lead++[launch])++pre) (.busy 10 (.out j)) ∧
            l.release.pending=pending id (BStarCopyLeftPending.remaining last r (.out j)) ∧
            OrderedPrefix (pending id r) l (headFirst lSeam ql) ∧
            BStarCopyLeftRetained.RetainedMatches lDigits old (addr lroot lSeam) r l ∧
            BStarCopyLeftMark.UpstreamMatches lDigits old lroot lSeam ql ∧
            t.release.pending=BStarCopyRightReleaseOrder.PendingAt (fun i=>i-rSeam) rSeam rTail first j ∧
            OrderedPrefix (planOf (fun i=>i-rSeam) rSeam rTail) t (stripWord rTail qr) ∧
            BStarCopyRightRetained.RetainedMatches rDigits old rroot r t ∧
            BStarCopyRightMark.MobileMatches rDigits old rbase rSeam rTail qr := by
  have sourceReady (pre : List (Fin n)) (e : Fin n) (tail : List (Fin n))
      (W : w=pre++e::tail) (k : Nat)
      (old : Current hp base (fun j=>S.getD j fall) len (run origin pre) (.busy 10 (.out k)))
      (C : CommandClaim) (ptr : S.getD k fall=address e C.source) :
      ReadyPort (oldPair B (run origin pre) e) (((run origin pre) e).long,((run origin pre) (rightNeighbor e)).long) C := by
    have hist := prefix_at_front hp pre (e::tail) k (W ▸ G) old
    have scopeCut : LiveAt hp chart origin pre :=
      fun u v E=>scope u (v++e::tail) (by rw [W,E,List.append_assoc])
    apply ready_from_preparation hp chart sep hist scopeCut init e C ptr
    intro rev port inside
    let i := site e C.source.side
    let x := run origin pre
    have loc : S.getD k fall=(i,sourceOccurrence rev) := ptr.trans (Prod.ext rfl port)
    have length := chart.length
    have kL := old.2.1.1
    have mem : S.getD k fall∈S := by
      rw [←List.getElem_eq_getD (h:=show k<S.length by omega)]
      exact List.getElem_mem _
    have O := (chart.entries _ mem).2
    rw [loc] at O
    have d : dataDispl (sourceLane rev)=cmdDispl (sourceOccurrence rev) := by
      cases rev <;> decide
    have owns : dataOwner (oldH6 B base) i (sourceLane rev)=o.val := by
      unfold dataOwner
      rw [d]
      exact O
    have inNow : (longGeometry B (x i)).inside=true := by
      cases H : C.source.side <;> simpa [x,i,H,oldPair,geometry,site] using inside
    have same := congrArg (fun q : Bool×Bool×Bool=>q.2.1) (old.1.1 i)
    have inBase : (longGeometry B (base i)).inside=true := same.trans inNow
    cases rev with
    | false =>
      obtain ⟨j,range,A⟩ := leftCover i owns inBase
      have location : S.getD k fall=(addr lroot j,5) := by simpa [A,sourceOccurrence] using loc
      have active : (longGeometry B (base (addr lroot j))).inside=true := by rwa [A] at inBase
      have H := left_frozen_of_issue hp chart sep hist scopeCut init lroot lSeam r j
        lStrip lRoot active range location
      change ∃ d : BitVec 36,(readLane (Sheet.index .ls) (x i).long).frozen=.data d
      rw [A]
      simpa [BStarCopyLeftMark.sample,BStarCopyLeftStrip.rail,range] using H
    | true =>
      obtain ⟨j,lo,hi,A⟩ := rightCover i owns inBase
      have location : S.getD k fall=(addr rbase j,2) := by simpa [A,sourceOccurrence] using loc
      have H := right_frozen_of_issue hp chart sep hist scopeCut init rbase rSeam rTail j
        rStrip rOwner lo hi location
      change ∃ d : BitVec 36,(readLane (Sheet.index .rs) (x i).long).frozen=.data d
      rw [A]
      exact H
  have F := terminal_unit_of_issue hp chart sep G (fun a e b E k now C _=>sourceReady a e b E k now C)
  obtain ⟨lead,tour,launch,W,door,L,oldPC,P⟩ := from_idle hp G
  let start := lead++[launch]
  let x := run origin start
  have total : w=start++tour := by
    rw [W]
    simp [start,List.append_assoc]
  have startEq : x=step (run origin lead) launch := by
    dsimp only [x,start]
    rw [BStarResetSchedule.run_append]
    rfl
  obtain ⟨mode,Gpre,I⟩ := BStarCopyGateAuthority.history_prefix hp lead (launch::tour) (W ▸ G)
  have idle : mode=.idle := by
    cases mode with
    | idle => rfl
    | busy op z =>
      exact ((by decide : (1:Nat)≠2) (L.1.2.symm.trans I.1.2.2.1)).elim
  subst mode
  have tourP : BusyOnly hp base (fun j=>S.getD j fall) len 10 x (.out 0) tour (.out len) :=
    startEq.symm ▸ P
  have launchEvent := Event.launch (hp:=hp) (addr:=fun j=>S.getD j fall) (len:=len) door L
  rw [oldPC] at launchEvent
  have Gstart : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle start (.busy 10 (.out 0)) :=
    generated_append hp Gpre (.next I launchEvent (.endpoint (busy_start hp P)))
  have preValid : LiveAt hp chart origin lead :=
    fun a b E=>scope a (b++launch::tour) (by rw [W,E,List.append_assoc])
  obtain ⟨w9,ack,gap,W9,G9,E9,N9⟩ :=
    BStarCopyCleanupCuts.accepted_cut hp chart sep Gpre preValid 9 (by rw [init]; decide)
      (by change 9<pc (run origin lead) (S.getD 0 fall).1; change pc (run origin lead) (S.getD 0 fall).1=10 at oldPC; rw [oldPC]; decide)
  have enableCut : start=w9++ack::(gap++[launch]) := by
    simp only [start,W9,List.append_assoc,List.cons_append]
  have flyValid : LiveAt hp chart origin (start++tour) := fun a b E=>scope a b (total.trans E)
  have endWord : run origin w=run x tour := by rw [total,BStarResetSchedule.run_append]
  have atEnd : project (fun j=>S.getD j fall) (run x tour) len=.forward injectUnit := endWord ▸ F
  have layout (a b : List (Fin n)) (H : tour=a++b) :
      ∀ i,Layout B base i=Layout B (run x a) i := by
    have F := (scope (start++a) b (by rw [total,H,←List.append_assoc])).1
    rwa [BStarResetSchedule.run_append] at F
  have ownedL := BStarCopyLeftReadyWord.all_owner hp chart lroot lSeam r lStrip lRoot
  let lDigits := fun i=>frozenDigit (BStarCopyLeftMark.sample x lroot lSeam i)
  let rDigits := fun i=>frozenDigit (BStarCopyRightDeposit.lanes x (addr rbase (rSeam+i)) .rs)
  have frozenL (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tour=a++e::b)
      (m : Mode) (R : BStarCopyLeftReleaseClass.ReleaseAt hp (run x a) e lroot lSeam
        (fun j=>S.getD j fall) len m) :
      (BStarCopyLeftMark.sample (run x a) lroot lSeam R.i).frozen=.data (lDigits R.i) := by
    obtain ⟨C,p,src,move⟩ := R.advance
    have hit : S.getD R.k fall=address e C.source := by
      rw [R.ptr,src,←R.markAt] <;> rfl
    have pre := prefix_to_release hp chart e (E ▸ tourP) R.k (Nat.le_of_lt R.strict) C p hit move
    have O : dataOwner (oldH6 B base) (addr lroot R.i) .ls=o.val := by
      simpa [BStarCopyLeftStrip.rail,R.range] using ownedL R.i (by have := R.range; omega)
    have before := BStarCopyLeftPreinject.frozen_pc10_prefix hp chart sep (addr lroot R.i)
      R.k (Nat.le_of_lt R.strict) R.ptr O start rfl Gstart pre
      (fun u mark v A=>layout u ((mark::v)++e::b) (by rw [E,A,List.append_assoc]))
    have replay : run origin (start++a)=run x a := BStarResetSchedule.run_append ..
    have M : w=(start++a)++e::b := by rw [total,E,←List.append_assoc]
    have hist := generated_append hp Gstart (busy_generated hp pre)
    have scopeCut : LiveAt hp chart origin (start++a) :=
      fun u v Eq=>scope u (v++e::b) (by rw [M,Eq,List.append_assoc])
    have same := congrArg (fun q : Bool×Bool×Bool=>q.2.1) (layout a (e::b) E (addr lroot R.i))
    have inside : (longGeometry B (base (addr lroot R.i))).inside=true :=
      same.trans (BStarCopyLeftReleaseOrder.release_inside hp R)
    have H := left_frozen_of_issue hp chart sep hist scopeCut init lroot lSeam r R.i
      lStrip lRoot inside R.range R.ptr
    rw [replay] at H
    apply read_frozen _ H
    simpa [BStarCopyLeftMark.sample,BStarCopyLeftStrip.rail,R.range] using before
  have frozenR (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tour=a++e::b)
      (m : Mode) (R : BStarCopyRightReleaseClass.ReleaseAt hp (run x a) e rbase rSeam rTail
        (fun j=>S.getD j fall) len m) :
      (BStarCopyRightDeposit.lanes (run x a) (addr rbase R.i) .rs).frozen=.data (rDigits (R.i-rSeam)) := by
    obtain ⟨C,p,src,move⟩ := R.advance
    have hit : S.getD R.k fall=address e C.source := by
      rw [R.ptr,src,←R.markAt] <;> rfl
    have pre := prefix_to_release hp chart e (E ▸ tourP) R.k (Nat.le_of_lt R.strict) C p hit move
    have O := (BStarCopyRightWrappedReleaseClass.strip_same_owner rStrip R.i R.range.2).trans rOwner
    rw [show rail rSeam R.i=.rs from if_neg (Nat.not_lt_of_ge R.range.1)] at O
    have before := BStarCopyRightPreinject.frozen_pc10_prefix hp chart sep (addr rbase R.i)
      R.k (Nat.le_of_lt R.strict) R.ptr O start rfl Gstart pre
      (fun u mark v A=>layout u ((mark::v)++e::b) (by rw [E,A,List.append_assoc]))
    have replay : run origin (start++a)=run x a := BStarResetSchedule.run_append ..
    have M : w=(start++a)++e::b := by rw [total,E,←List.append_assoc]
    have hist := generated_append hp Gstart (busy_generated hp pre)
    have scopeCut : LiveAt hp chart origin (start++a) :=
      fun u v Eq=>scope u (v++e::b) (by rw [M,Eq,List.append_assoc])
    have H := right_frozen_of_issue hp chart sep hist scopeCut init rbase rSeam rTail
      R.i rStrip rOwner R.range.1 R.range.2 R.ptr
    rw [replay] at H
    have j : rSeam+(R.i-rSeam)=R.i := by have := R.range.1; omega
    unfold rDigits
    rw [j]
    exact read_frozen before H
  have left := left_from_issue hp chart sep lDigits lroot lSeam r
    lStrip lRoot lSize lFlag start tour lead launch rfl Gpre (Nat.le_of_eq init)
    oldPC Gstart tourP w9 (gap++[launch]) ack enableCut G9 E9 N9 (total ▸ G)
    flyValid injectUnit atEnd rfl rfl frozenL
  have right := right_from_issue hp chart sep rbase rSeam rTail
    rStrip rOwner rSize rDigits start tour Gstart tourP frozenR rroot rDest rJoin lead launch
    rfl Gpre (Nat.le_of_eq init) oldPC w9 (gap++[launch]) ack enableCut G9 E9 N9
    (total ▸ G) flyValid injectUnit atEnd rfl rfl
  obtain ⟨last,lastBound,lastPosition,leftTape⟩ := left
  obtain ⟨first,rightBlock,rightTape⟩ := right
  refine ⟨lead,launch,tour,W,Gpre,oldPC,F,sourceReady,last,first,lastBound,lastPosition,rightBlock,?_⟩
  intro pre post cut
  obtain ⟨jl,l,ql,GL,pL,oL,hL,uL⟩ := leftTape pre post cut
  obtain ⟨jr,t,qr,GR,pR,oR,hR,uR⟩ := rightTape pre post cut
  have currentL := BStarGeneratedTapeCuts.at_end hp GL
  have currentR := BStarGeneratedTapeCuts.at_end hp GR
  have sameCursor := (BStarOwnerControlHistory.pointed_unique_forward _ len _ currentL.2.1 currentL.2.2
    jr currentR.2.1.1).mp currentR.2.1.2.1
  subst jr
  exact ⟨jl,l,t,ql,qr,GL,pL,oL,hL,uL,pR,oR,hR,uR⟩

private theorem endready_drained {base x : X} (e : Fin n) (o : Int)
    (drained : BStarCopyCleanupWindow.DrainedOwner hp base x o) :
    FreshFenceGuards.EndReady hp base x e o := by
  intro D mem _ owner
  let g := oldPair B x e
  have act := FreshPreparation.selected_source_active g _ D mem
  have atSite : activeSheet (longGeometry B (x (site e D.source.side))) D.source.occurrence=true := by
    cases h : D.source.side <;> simpa [g,oldPair,geometry,site,h] using act
  change (view ((x e).long,(x (rightNeighbor e)).long) D.source).mobile=.empty
  rw [BStarCopyRightMark.old_access]
  exact (drained _ _ atSite owner).1

/-- Clean physical bytes and vacant actual ENDs after every partial
original INJECT cut. Neither statement needs the release pending suffix
to be empty, and the initial invariant comes from the selected CLEAR. -/
theorem clean_from_issue {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy 10 (.out len)))
    (scope : LiveAt hp chart origin w) (init : pc origin (S.getD 0 fall).1=6)
    (lroot : Fin n) (lSeam : Nat) (lStrip : BStarCopyLeftStrip.Strip B base lroot lSeam r)
    (lRoot : lroot=(S.getD 0 fall).1) (lSize : r≤lSeam)
    (lFlag : ∀ j<lSeam,(longGeometry B (base (addr lroot j))).inside=true ↔ j<r)
    (rroot rbase : Fin n) (rSeam rTail : Nat)
    (rStrip : BStarCopyRightWrappedGeometry.WrappedStrip B base rbase rSeam rTail)
    (rDest : BStarCopyRightRetained.Dest B base rroot r)
    (rJoin : addr rbase 0=addr rroot (r-1))
    (rOwner : dataOwner (oldH6 B base) (addr rbase 0) (rail rSeam 0)=o.val)
    (rSize : rTail+1=rSeam+r)
    (leftCover : ∀ i,dataOwner (oldH6 B base) i .ls=o.val →
      (longGeometry B (base i)).inside=true → ∃ j,j<lSeam ∧ i=addr lroot j)
    (rightCover : ∀ i,dataOwner (oldH6 B base) i .rs=o.val →
      (longGeometry B (base i)).inside=true → ∃ j,rSeam≤j ∧ j≤rTail ∧ i=addr rbase j)
    (joinLeft : addr lroot lSeam=rroot) (rootAt : rroot=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (BStarH6Ordinal.oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (BStarH6Ordinal.oldOrdinal B base hh i+1=r))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true →
      r≤BStarH6Ordinal.oldOrdinal B base hh i+1) :
    ∃ lead launch tour,w=lead++launch::tour ∧
      ∀ pre post,tour=pre++post →
        let y := run origin ((lead++[launch])++pre)
        FreshFenceGuards.CleanOwner hp base y o.val ∧
          ∀ e,FreshFenceGuards.EndReady hp base y e o.val := by
  obtain ⟨lead,launch,tour,W,idle,issue,_,prepared,last,first,_,_,_,ledger⟩ :=
    prepared_prefixes_from_issue hp chart sep G scope init lroot lSeam lStrip lRoot lSize lFlag
      rroot rbase rSeam rTail rStrip rDest rJoin rOwner rSize leftCover rightCover
  let start := lead++[launch]
  let lDigits := fun i=>frozenDigit (BStarCopyLeftMark.sample (run origin start) lroot lSeam i)
  let rDigits := fun i=>frozenDigit (BStarCopyRightDeposit.lanes (run origin start) (addr rbase (rSeam+i)) .rs)
  have front : LiveAt hp chart origin lead :=
    fun a b E=>scope a (b++launch::tour) (by rw [W,E,List.append_assoc])
  have drained := (FreshFenceGuards.clean_before_inject hp chart sep idle front (by omega) issue).2
  have latched (a b : List (Fin n)) (E : tour=a++b) (e : Fin n) :
      FreshFenceGuards.EndReady hp base (run origin (start++a)) e o.val := by
    obtain ⟨j,l,t,ql,qr,_,_,lOrd,lMatch,_,_,rOrd,rMatch,_⟩ := ledger a b E
    have layout := (scope (start++a) b (by rw [W,E]; simp [start,List.append_assoc])).1
    have replay : run origin (start++a)=run (run origin start) a := BStarResetSchedule.run_append ..
    rw [replay] at layout ⊢
    have N : (planOf (fun i=>i-rSeam) rSeam rTail).length=r := by simp [planOf]; omega
    exact FreshFenceGuards.end_ready_of_ledgers hp lDigits rDigits chart e r lStrip.width_pos
      rroot rootAt flags notShort layout (by simp [pending]) N (ordered_prefix lOrd).1 (ordered_prefix rOrd).1
      (by rw [joinLeft] at lMatch; exact lMatch) rMatch
  refine ⟨lead,launch,tour,W,?_⟩
  intro pre post cut
  obtain ⟨j,_,_,_,_,history,_,_,_,_,_,_,_,_⟩ := ledger pre post cut
  have tapeEq : start++pre=lead++launch::pre := by simp [start,List.append_assoc]
  have extend : w=(lead++launch::pre)++post := by simp only [W,cut,List.append_assoc,List.cons_append]
  have scopePre : LiveAt hp chart origin (lead++launch::pre) := by
    intro a b E
    apply scope a (b++post)
    rw [extend,E,List.append_assoc]
  have clean := FreshFenceGuards.clean_copy_word hp chart sep lead (launch::pre) idle
    (tapeEq ▸ history) scopePre init issue
    (fun a e b E=>by
      cases a with
      | nil => simpa using endready_drained hp e o.val drained
      | cons mark a =>
        change launch::pre=mark::(a++e::b) at E
        obtain ⟨label,split⟩ := List.cons.inj E
        subst mark
        have z : lead++launch::a=start++a := by simp [start,List.append_assoc]
        rw [z]
        exact latched a ((e::b)++post) (by rw [cut,split,List.append_assoc]) e)
    (fun a e b E k current C ptr=>by
      apply prepared (lead++a) e (b++post) _ k current C ptr
      calc
        w=(lead++launch::pre)++post := extend
        _=((lead++a)++e::b)++post := by simp only [E,List.append_assoc,List.cons_append]
        _=(lead++a)++e::(b++post) := by rw [List.append_assoc,List.cons_append])
  exact ⟨tapeEq.symm ▸ clean,latched pre post cut⟩

end Issue

#print axioms left_prefixes
#print axioms right_prefixes
#print axioms left_from_issue
#print axioms right_from_issue
#print axioms prepared_prefixes_from_issue
#print axioms clean_from_issue
end L4.Height.FreshPartialLedgers

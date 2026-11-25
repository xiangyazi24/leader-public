import Leader.L4.BStarCopyLeftInjectPositive

namespace L4.BStarCopyLeftInjectFold
set_option maxRecDepth 4096
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

/-- A quiet selected mark cannot advance across a genuine inside K5
source on a healthy actual outward flight. -/
theorem quiet_keeps_pending {Tag : Type} (atSource : Nat→Tag)
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a e : Fin n) (seam width end5 k j : Nat)
    (ws : width≤seam) ( _e5 : end5<len)
    (aff : ∀ i<seam, i≤end5 ∧ S.getD (end5-i) fall=(addr a i,5))
    (ins : ∀ i<seam,(longGeometry B (base (addr a i))).inside=true ↔ i<width)
    (cur : Current hp base (fun t=>S.getD t fall) len x (.busy 10 (.out k)))
    (E : Event hp (fun t=>S.getD t fall) len x e (.busy 10 (.out k)) (.busy 10 (.out j)))
    {w : List (Fin n)}
    (next : BusyOnly hp base (fun t=>S.getD t fall) len 10 (ring x e) (.out j) w (.out len))
    (f : Payload) (F : project (fun t=>S.getD t fall) (play (ring x e) w) len=.forward f)
    (clean : f.fault=0) (op : f.opcode.toNat=10)
    (quiet : NoLSPrep hp x a e seam) :
    pending atSource (remaining end5 width (.out j))=pending atSource (remaining end5 width (.out k)) := by
  rcases jumps hp E with st|ad
  · rw [st]
  rw [ad]
  rcases remaining_forward end5 width k with ⟨i,iw,ie,idx,_,_⟩|H
  · exfalso
    have I : i<seam := by omega
    have chartKey := (aff i I).2
    rw [←idx] at chartKey
    have O := busy_start hp next
    obtain ⟨q,L,p,P,H,Q⟩ := busy_origin hp chart sep next len (Nat.le_refl _) f F clean
    have eq := (pointed_unique_forward _ len _ O.2.1 O.2.2 q L).mp ⟨p,P⟩
    subst q
    rw [ad] at P
    obtain ⟨loc,win⟩ := healthy_k5_crossing hp chart e (sep e) k (by omega) (addr a i) chartKey
      ((ins i I).mpr iw) cur p P H ((congrArg BitVec.toNat Q).trans op)
    exact quiet i I .right loc (List.mem_map.mpr ⟨_,win,rfl⟩)
  · rw [H]

/-- Original successful outward10 tape. Exact ledger pending suffix
is derived at each mark from the actual reverse K5 cursor. The
captured byte table and old gate qualification are explicit inputs. -/
theorem inject_outward_fold {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
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
    ∃ (t : Ledger Tag) (post : Nat→Option Tag), t.release.pending=[] ∧
      OrderedPrefix plan t (headFirst seam post) ∧
      RetainedMatches digits (play x w) (addr a seam) width t ∧
      UpstreamMatches digits (play x w) a seam post := by
  have aff := affine_chart hp chart a seam width end5 strip root e5 last
  generalize endEq : Cursor.out len=d at tour
  induction tour with
  | nil cur =>
    intro k lead s lab Z Y G P held mobile vacant pend ready
    have eq := Cursor.out.inj (Z.symm.trans endEq.symm)
    have R : remaining end5 width (.out k)=0 := by
      simp [remaining,show end5+1-k=0 by omega]
    rw [R] at pend
    exact ⟨s,lab,pend,P,held,mobile⟩
  | @cons x z d fin e w I E rest ih =>
    intro k lead s lab Z Y G P held mobile vacant pend ready
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
        have V := quiet_keeps_pending hp atSource chart sep a e seam width end5 k j ws e5 aff ins I E goalRest
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
    exact ih F endEq j (lead++[e]) t labels rfl after progress ltag held' mobile' V pend'
      (fun pre mark post Eq => ready (e::pre) mark post (congrArg (List.cons e) Eq))

#print axioms inject_outward_fold
#print axioms quiet_keeps_pending
end L4.BStarCopyLeftInjectFold

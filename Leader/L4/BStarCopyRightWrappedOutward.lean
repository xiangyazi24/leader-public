import Leader.L4.BStarCopyRightWrappedReleaseClass
import Leader.L4.BStarCopyRightInjectFold
import Leader.L4.BStarCopyRightScopedDeposit
import Leader.L4.BStarCopyActiveVacancy

namespace L4.BStarCopyRightWrappedOutward
set_option maxRecDepth 4096
set_option maxHeartbeats 950000
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

open BStarCopyRightWrappedGeometry BStarCopyRightWrappedSweep BStarCopyRightWrappedRelease

open BStarCopyRightWrappedActiveFold (quiet_keeps_pending)

/-- All-mark ordered fold on a single genuine healthy outward10
flight, starting at any certified prior cursor. The source pending
list is maintained as a function of the physical cursor, never
assumed at an interior mark. Captured packed-byte matching, old
geometry, and gate qualification remain separate physical inputs. -/
theorem inject_wrapped_outward {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
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
    ∃ (t : Ledger Tag) (post : Nat→Option Tag), t.release.pending=[] ∧
      OrderedPrefix (planOf atSource seam tail) t (stripWord tail post) ∧
      RetainedMatches digits (play x w) root width t ∧ MobileMatches digits (play x w) a seam tail post := by
  generalize endEq : Cursor.out len=d at tour
  induction tour with
  | nil cur =>
    intro k lead s lab Z Y G P held mobile vacant pending ready
    have eq := Cursor.out.inj (Z.symm.trans endEq.symm)
    have last := (block.address tail block.valid (Nat.le_refl _)).1
    have out : first+(tail+1-seam)≤k := by omega
    exact ⟨s,lab,pending.trans (pending_after_block atSource seam tail first k block.valid out),P,held,mobile⟩
  | @cons x z d fin e w I E rest ih =>
    intro k lead s lab Z Y G P held mobile vacant pending ready
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
        have V := quiet_keeps_pending hp atSource chart sep a e seam tail first k j strip block I E goalRest
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
    exact ih F endEq j (lead++[e]) t labels rfl after progress ltag held' mobile' V pend
      (fun pre mark post Eq => ready (e::pre) mark post (congrArg (List.cons e) Eq))

end L4.BStarCopyRightWrappedOutward

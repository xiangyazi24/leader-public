import Leader.L4.BStarCopyRightWrappedGates
import Leader.L4.BStarCopyRightInjectFold

namespace L4.BStarCopyRightWrappedReturn
set_option maxRecDepth 4096
open BStarCopyRightReturn (ReleasePast)
open BStarCopyRightWrappedGeometry
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarLongPackets BStarCopyRightStrip BStarCopyRightMark BStarCopyRightRetained
open BStarCopyRightRetainedClassify BStarCopyRightDataSweep BStarCopyRightReleaseClass
open BStarClearanceDataChart BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarSeparatingRail BStarResetSchedule BStarResetMarkAdapter BStarSeparatorControl
open BStarCopyMarkedLedger BStarCopyFenceSaturation

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

/-- At the actual terminal old mark or any returning PC10 old mark,
there is no new release. The whole physical COPY projection is now
data-only, even though the same owner's control PC still reads 10. -/
theorem ready_release_past {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (m : Mode)
    (G : GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle w m)
    (past : ReleasePast len m)
    (root a e : Fin n) (width seam tail : Nat)
    (dest : Dest B base root width) (strip : WrappedStrip B base a seam tail)
    (join : addr a 0=addr root (width-1))
    (own : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (gate : BStarCopyRightWrappedGates.Gates hp base (play origin w) root a width seam tail) :
    BStarCopyRightWrappedSweep.DataReady hp (play origin w) root a e width seam tail := by
  have cur := BStarGeneratedTapeCuts.at_end hp G
  have pc10 : BStarGeneratedBandScan.pc (play origin w) (S.getD 0 fall).1=10 := by
    rcases past with h|⟨k,h⟩
    · rw [h] at cur
      exact cur.1.2.2.2
    · rw [h] at cur
      exact cur.1.2.2.2
  obtain ⟨rd,up⟩ := BStarCopyRightWrappedReleaseClass.classify_release hp chart sep w m G gate.same pc10 root a e width seam tail
    dest strip join own
  rcases up with quiet|actual
  · exact ⟨gate.dest,gate.strip,gate.rd,gate.up,rd,quiet⟩
  · obtain ⟨R⟩ := actual
    rcases past with K|⟨k,bk⟩
    · have H := Cursor.out.inj ((Mode.busy.inj (K.symm.trans R.mode)).2)
      have lt := R.strict
      omega
    · have H := (Mode.busy.inj (bk.symm.trans R.mode)).2
      contradiction

private theorem stays_back {x : X} {addr : Nat→Pos n} {len k : Nat} {e : Fin n}
    {z : Cursor} (Ev : Event hp addr len x e (.busy 10 (.back k)) (.busy 10 z)) :
    ∃ j,z=.back j := by
  cases Ev with
  | arrived_hold _ _ => exact ⟨0,rfl⟩
  | transit _ _ _ _ S =>
    have A : Advance len (.back k) z := by
      cases S with
      | cons _ _ T _ tail => cases tail; exact T
    cases A
    · exact ⟨k,rfl⟩
    · exact ⟨_,rfl⟩

/-- Every physical mark of the original PC10 return is already a
data-only mark; this includes exterior labels, return stutters, and
source waiting. It preserves any independently tracked ghost ledger. -/
theorem returning_ready {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (root a : Fin n) (width seam tail : Nat)
    (dest : Dest B base root width) (strip : WrappedStrip B base a seam tail)
    (join : addr a 0=addr root (width-1))
    (own : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    {z final : Cursor} {w : List (Fin n)}
    (busy : BusyOnly hp base (fun t=>S.getD t fall) len 10 x z w final) :
    ∀ (lead : List (Fin n)), x=play origin lead →
    GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle lead (.busy 10 z) →
    (∃ k,z=.back k) →
    (∀ pre e post,w=pre++e::post → BStarCopyRightWrappedGates.Gates hp base (play x pre) root a width seam tail) →
    ∀ pre e post,w=pre++e::post → BStarCopyRightWrappedSweep.DataReady hp (play x pre) root a e width seam tail := by
  induction busy with
  | nil _ =>
    intro lead eq hist back scope pre e post E
    cases pre <;> contradiction
  | @cons x z d final e w I E tail' ih =>
    intro lead Z G back scope pre mark post W
    obtain ⟨k,rfl⟩ := back
    cases pre with
    | nil =>
      obtain ⟨rfl,rfl⟩ := List.cons.inj W
      exact Z.symm ▸ ready_release_past hp chart sep lead (.busy 10 (.back k)) G
        (.inr ⟨k,rfl⟩) root a e width seam tail dest strip join own (Z ▸ scope [] e w rfl)
    | cons old pre =>
      obtain ⟨rfl,split⟩ := List.cons.inj W
      have Y : ring x e=play origin (lead++[e]) := by
        rw [BStarResetSchedule.run_append,←Z]; rfl
      have H := generated_append hp G (Z ▸ GeneratedOwner.next I E (.endpoint (busy_start hp tail')))
      exact ih (lead++[e]) Y H (stays_back hp E)
        (fun a f b eq => scope (e::a) f b (congrArg (List.cons e) eq)) pre mark post split

#print axioms ready_release_past
#print axioms returning_ready

private theorem busy_as_generated {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {a b : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x a w b) :
    GeneratedOwner hp base addr len x (.busy op a) w (.busy op b) := by
  induction P with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

/-- From the endpoint of the completed PC10 outward fold, all real
marks through the owned accepted PC10 receipt carry the same ordered
plan and immediately continue into any qualifying real PC11 tape.
No scheduler filtering at the turn, held source D, or consume. -/
theorem through_turn_return_ack {Tag : Type} (digits : Tag→BitVec 36)
    {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (root a : Fin n) (width seam tail : Nat)
    (dest : Dest B base root width) (strip : WrappedStrip B base a seam tail)
    (join : addr a 0=addr root (width-1))
    (own : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (lead back data : List (Fin n)) (turn ack : Fin n)
    (start : GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle lead (.busy 10 (.out len)))
    (turns : Event hp (fun t=>S.getD t fall) len (play origin lead) turn
      (.busy 10 (.out len)) (.busy 10 (.back len)))
    (ret : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (ring (play origin lead) turn) (.back len) back (.back 0))
    (acknowledge : Event hp (fun t=>S.getD t fall) len (play (ring (play origin lead) turn) back) ack
      (.busy 10 (.back 0)) .idle)
    (idle11 : Current hp base (fun t=>S.getD t fall) len
      (ring (play (ring (play origin lead) turn) back) ack) .idle)
    (accepted11 : BStarGeneratedBandScan.pc (ring (play (ring (play origin lead) turn) back) ack)
      (S.getD 0 fall).1=11)
    (preTurn : BStarCopyRightWrappedGates.Gates hp base (play origin lead) root a width seam tail)
    (preAck : BStarCopyRightWrappedGates.Gates hp base (play (ring (play origin lead) turn) back) root a width seam tail)
    (backScope : ∀ p e q, back=p++e::q →
      BStarCopyRightWrappedGates.Gates hp base (play (ring (play origin lead) turn) p) root a width seam tail)
    (laterScope : ∀ p e q, data=p++e::q →
      BStarCopyRightWrappedSweep.DataReady hp (play (ring (play (ring (play origin lead) turn) back) ack) p)
        root a e width seam tail)
    (plan : List Tag) (size : plan.length=width)
    (s : Ledger Tag) (labels : Nat→Option Tag)
    (finished : s.release.pending=[])
    (P : OrderedPrefix plan s (stripWord tail labels))
    (old : RetainedMatches digits (play origin lead) root width s)
    (mobile : MobileMatches digits (play origin lead) a seam tail labels) :
    let whole := ((lead++[turn])++back)++[ack]
    let endpoint := play origin (whole++data)
    GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle whole .idle ∧
      BStarGeneratedBandScan.pc (play origin whole) (S.getD 0 fall).1=11 ∧
      ∃ t post, t.release.pending=[] ∧ OrderedPrefix plan t (stripWord tail post) ∧
        RetainedMatches digits endpoint root width t ∧ MobileMatches digits endpoint a seam tail post := by
  dsimp only
  let x0 := play origin lead
  let x1 := ring x0 turn
  let x2 := play x1 back
  let x3 := ring x2 ack
  let lead1 := lead++[turn]
  let lead2 := lead1++back
  let whole := lead2++[ack]
  have origin1 : x1=play origin lead1 := by
    rw [show lead1=lead++[turn] from rfl,BStarResetSchedule.run_append]; rfl
  have origin2 : x2=play origin lead2 := by rw [show lead2=lead1++back from rfl,BStarResetSchedule.run_append,←origin1]
  have origin3 : x3=play origin whole := by rw [show whole=lead2++[ack] from rfl,BStarResetSchedule.run_append,←origin2]; rfl
  have start1 : GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle lead1 (.busy 10 (.back len)) :=
    generated_append hp start (.next (BStarGeneratedTapeCuts.at_end hp start) turns
      (.endpoint (busy_start hp ret)))
  have start2 : GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle lead2 (.busy 10 (.back 0)) :=
    generated_append hp start1 (origin1 ▸ busy_as_generated hp ret)
  have start3 : GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle whole .idle :=
    generated_append hp start2 (origin2 ▸ GeneratedOwner.next (BStarAcquireHistoryReturn.busy_end hp ret)
      acknowledge (.endpoint idle11))
  have D0 := ready_release_past hp chart sep lead (.busy 10 (.out len)) start
    (.inl rfl) root a turn width seam tail dest strip join own preTurn
  obtain ⟨t,ls,Q,A,H,I⟩ := BStarCopyRightWrappedSweep.data_mark hp digits x0 root a turn width seam tail D0.dest D0.strip
    join (sep turn) s plan size labels P old mobile D0.rdGate D0.upGate D0.rdPrep D0.upPrep
  have backReady := returning_ready hp chart sep root a width seam tail dest strip join own ret
    lead1 origin1 start1 ⟨len,rfl⟩ backScope
  obtain ⟨u,ls',R,Cc,HH,MM⟩ := BStarCopyRightWrappedSweep.data_word hp digits x1 back root a width seam tail join sep plan size
    t ls A H I backReady
  have D2 := ready_release_past hp chart sep lead2 (.busy 10 (.back 0)) start2
    (.inr ⟨0,rfl⟩) root a ack width seam tail dest strip join own (origin2 ▸ preAck)
  rw [←origin2] at D2
  obtain ⟨v,ls'',J,Pf,Mf,Nf⟩ := BStarCopyRightWrappedSweep.data_mark hp digits x2 root a ack width seam tail D2.dest D2.strip
    join (sep ack) u plan size ls' Cc HH MM D2.rdGate D2.upGate D2.rdPrep D2.upPrep
  obtain ⟨last,lastLab,E,K,D,L⟩ := BStarCopyRightWrappedSweep.data_word hp digits x3 data root a width seam tail join sep plan size
    v ls'' Pf Mf Nf laterScope
  have replay : play origin (whole++data)=play x3 data := by
    rw [BStarResetSchedule.run_append,←origin3]
  refine ⟨start3,origin3 ▸ accepted11,last,lastLab,?_,K,replay.symm ▸ D,replay.symm ▸ L⟩
  exact (congrArg BStarCopyInjection.ReleaseHistory.pending (E.trans (J.trans (R.trans Q)))).trans finished

#print axioms through_turn_return_ack
end L4.BStarCopyRightWrappedReturn

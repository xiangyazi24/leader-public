import Leader.L4.BStarCopyLeftInjectFold
import Leader.L4.BStarCopyLeftReadyWord

namespace L4.BStarCopyLeftReturn
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarCopyRightStrip (addr)
open BStarLongPackets BStarCopyLeftStrip BStarCopyLeftMark BStarCopyLeftRetained
open BStarCopyLeftRetainedClassify BStarCopyLeftDataSweep BStarCopyLeftReleaseClass
open BStarCopyLeftDeposit
open BStarClearanceDataChart BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarSeparatingRail BStarResetSchedule BStarResetMarkAdapter BStarSeparatorControl
open BStarCopyMarkedLedger BStarCopyFenceSaturation

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

structure GeometryGates (base x : X) (a : Fin n) (seam width : Nat) : Prop where
  same : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i
  strip : Strip B x a seam width
  ld : ∀ j<width,(readLane (Sheet.index .ld) (x (addr (addr a seam) j)).long).gate=true
  ls : ∀ j<seam,(sample x a seam j).gate=true

def ReleasePast (len : Nat) (m : Mode) : Prop :=
  m=.busy 10 (.out len) ∨ ∃ k,m=.busy 10 (.back k)

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
    (a e : Fin n) (seam width : Nat)
    (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
    (gate : GeometryGates hp base (play origin w) a seam width) :
    DataReady hp (play origin w) a e seam width := by
  have cur := BStarGeneratedTapeCuts.at_end hp G
  have pc10 : BStarGeneratedBandScan.pc (play origin w) (S.getD 0 fall).1=10 := by
    rcases past with h|⟨k,h⟩
    · rw [h] at cur
      exact cur.1.2.2.2
    · rw [h] at cur
      exact cur.1.2.2.2
  obtain ⟨rd,up⟩ := classify_release hp chart sep w m G gate.same pc10 a e seam width
    strip root
  rcases up with quiet|actual
  · exact ⟨gate.strip,gate.ld,gate.ls,rd,quiet⟩
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
    (a : Fin n) (seam width : Nat)
    (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
    {z final : Cursor} {w : List (Fin n)}
    (busy : BusyOnly hp base (fun t=>S.getD t fall) len 10 x z w final) :
    ∀ (lead : List (Fin n)), x=play origin lead →
    GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle lead (.busy 10 z) →
    (∃ k,z=.back k) →
    (∀ pre e post,w=pre++e::post → GeometryGates hp base (play x pre) a seam width) →
    ∀ pre e post,w=pre++e::post → DataReady hp (play x pre) a e seam width := by
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
        (.inr ⟨k,rfl⟩) a e seam width strip root (Z ▸ scope [] e w rfl)
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
    (a : Fin n) (seam width : Nat)
    (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
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
    (preTurn : GeometryGates hp base (play origin lead) a seam width)
    (preAck : GeometryGates hp base (play (ring (play origin lead) turn) back) a seam width)
    (backScope : ∀ p e q, back=p++e::q →
      GeometryGates hp base (play (ring (play origin lead) turn) p) a seam width)
    (laterScope : ∀ p e q, data=p++e::q →
      DataReady hp (play (ring (play (ring (play origin lead) turn) back) ack) p) a e seam width)
    (plan : List Tag) (size : plan.length=width)
    (s : Ledger Tag) (labels : Nat→Option Tag)
    (finished : s.release.pending=[])
    (P : OrderedPrefix plan s (headFirst seam labels))
    (old : RetainedMatches digits (play origin lead) (addr a seam) width s)
    (mobile : UpstreamMatches digits (play origin lead) a seam labels) :
    let whole := ((lead++[turn])++back)++[ack]
    let endpoint := play origin (whole++data)
    GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle whole .idle ∧
      BStarGeneratedBandScan.pc (play origin whole) (S.getD 0 fall).1=11 ∧
      ∃ t post, t.release.pending=[] ∧ OrderedPrefix plan t (headFirst seam post) ∧
        RetainedMatches digits endpoint (addr a seam) width t ∧ UpstreamMatches digits endpoint a seam post := by
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
    (.inl rfl) a turn seam width strip root preTurn
  obtain ⟨t,ls,Q,A,H,I⟩ := data_mark hp digits x0 a turn seam width D0.strip (sep turn) s plan size labels P old mobile D0.ldGate D0.lsGate D0.ldPrep D0.lsPrep
  have backReady := returning_ready hp chart sep a seam width strip root ret
    lead1 origin1 start1 ⟨len,rfl⟩ backScope
  obtain ⟨u,ls',R,Cc,HH,MM⟩ := data_word hp digits x1 back a seam width sep plan size
    t ls A H I backReady
  have D2 := ready_release_past hp chart sep lead2 (.busy 10 (.back 0)) start2
    (.inr ⟨0,rfl⟩) a ack seam width strip root (origin2 ▸ preAck)
  rw [←origin2] at D2
  obtain ⟨v,ls'',J,Pf,Mf,Nf⟩ := data_mark hp digits x2 a ack seam width D2.strip (sep ack) u plan size ls' Cc HH MM D2.ldGate D2.lsGate D2.ldPrep D2.lsPrep
  obtain ⟨last,lastLab,E,K,D,L⟩ := data_word hp digits x3 data a seam width sep plan size
    v ls'' Pf Mf Nf laterScope
  have replay : play origin (whole++data)=play x3 data := by
    rw [BStarResetSchedule.run_append,←origin3]
  refine ⟨start3,origin3 ▸ accepted11,last,lastLab,?_,K,replay.symm ▸ D,replay.symm ▸ L⟩
  exact (congrArg BStarCopyInjection.ReleaseHistory.pending (E.trans (J.trans (R.trans Q)))).trans finished

/-- Continue directly into the same original qualifying late word.
The PC9 accepted history supplies all late gates and reservation
facts; old return reservation exclusions are derived independently. -/
theorem through_ack_into_original_late {Tag : Type} (digits : Tag→BitVec 36)
    {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam width : Nat)
    (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
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
    (preTurn : GeometryGates hp base (play origin lead) a seam width)
    (preAck : GeometryGates hp base (play (ring (play origin lead) turn) back) a seam width)
    (backScope : ∀ p e q, back=p++e::q →
      GeometryGates hp base (play (ring (play origin lead) turn) p) a seam width)
    (w9 bridge : List (Fin n)) (ack9 : Fin n) (endMode : Mode)
    (G9 : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event9 : Event hp (fun j => S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted9 : (BStarLongDoor.ctrlOp.read (ring (play origin w9) ack9 (S.getD 0 fall).1).long).toNat=10)
    (sameTape : w9++ack9::bridge=((lead++[turn])++back)++[ack])
    (history : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle
      ((w9++ack9::bridge)++data) endMode)
    (valid : ∀ u v, ((w9++ack9::bridge)++data)=u++v →
      (∀ j,BStarLongFixedRouting.Layout B base j=BStarLongFixedRouting.Layout B (play origin u) j) ∧
      BStarGeneratedBandScan.Band (play origin u) (S.getD 0 fall).1)
    (plan : List Tag) (size : plan.length=width)
    (s : Ledger Tag) (labels : Nat→Option Tag)
    (finished : s.release.pending=[])
    (P : OrderedPrefix plan s (headFirst seam labels))
    (old : RetainedMatches digits (play origin lead) (addr a seam) width s)
    (mobile : UpstreamMatches digits (play origin lead) a seam labels) :
    let whole := ((lead++[turn])++back)++[ack]
    let endpoint := play origin (whole++data)
    GeneratedOwner hp base (fun t=>S.getD t fall) len origin .idle whole .idle ∧
      BStarGeneratedBandScan.pc (play origin whole) (S.getD 0 fall).1=11 ∧
      ∃ t post, t.release.pending=[] ∧ OrderedPrefix plan t (headFirst seam post) ∧
        RetainedMatches digits endpoint (addr a seam) width t ∧ UpstreamMatches digits endpoint a seam post := by
  have replay : play origin (w9++ack9::bridge)=ring (play (ring (play origin lead) turn) back) ack := by
    rw [sameTape, BStarResetSchedule.run_append,BStarResetSchedule.run_append,BStarResetSchedule.run_append]
    rfl
  have pc11 : 11≤BStarGeneratedBandScan.pc (play origin (w9++ack9::bridge)) (S.getD 0 fall).1 := by
    rw [replay,accepted11]
    exact Nat.le_refl _
  have late := BStarCopyLeftReadyWord.left_ready_word hp chart sep w9 bridge data ack9
    endMode G9 event9 accepted9 history valid pc11 a seam width strip root
  exact through_turn_return_ack hp digits chart sep a seam width strip root lead back data turn ack
    start turns ret acknowledge idle11 accepted11 preTurn preAck backScope
    (fun p e q W => replay ▸ late p e q W) plan size s labels finished P old mobile

#print axioms through_ack_into_original_late
#print axioms through_turn_return_ack
end L4.BStarCopyLeftReturn

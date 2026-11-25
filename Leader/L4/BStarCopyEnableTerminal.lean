import Leader.L4.BStarStageTerminalHealth
import Leader.L4.BStarAcquireAckAncestry

namespace L4.BStarCopyEnableTerminal
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongEvents BStarLongRouting BStarLongLiteral
open BStarResetQuiet BStarResetQuietTable BStarClearanceForward BStarLongCommandData
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatorControl BStarResetSchedule
open BStarBankTrace BStarResetChartService BStarLongDoor
open BStarAcquireAckAncestry BStarAcquireHistoryReturn

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem healthy_finish (p q : Payload) (R : finish p=.reply q)
    (H : q.fault=0) (op : q.opcode.toNat≠acquire) :
    p.fault=0 ∧ p.opcode=q.opcode := by
  unfold finish at R
  dsimp only at R
  split at R
  · change (.reply _ : Token)=.reply q at R
    cases R
    exact False.elim ((show (1 : BitVec 1)≠0 by decide) H)
  · rename_i N
    have clear : p.fault=0 := by
      apply Classical.byContradiction
      intro ne
      exact N (bne_iff_ne.mpr ne)
    split at R
    · rename_i A
      have opA : p.opcode.toNat=acquire := beq_iff_eq.mp A
      split at R <;> cases R <;> exact False.elim (op opA)
    · split at R
      · change (.reply _ : Token)=.reply q at R
        cases R
        exact False.elim ((show (1 : BitVec 1)≠0 by decide) H)
      · cases R
        exact ⟨clear,rfl⟩

private theorem not_center_carries (g : LongGeometry × LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (v : Payload) (N : C.source.occurrence.val≠1) :
    carried g raw C v=v := by
  unfold carried BStarLongArithmetic.visit
  have M : (C.source.occurrence.val != 1)=true := bne_iff_ne.mpr N
  simp only [M,Bool.true_or,if_true]
  rw [BStarLongOutgoing.noncenter_hold _ _ _ _ N]
  rfl

/-- From a genuine healthy non-ACQUIRE receipt, the original old
terminal F on the same successful physical tour is healthy and has
the matching literal opcode. No clean-forward assumption. -/
theorem terminal_old_healthy {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (turn : Fin n) (back : List (Fin n)) (op : Nat)
    (old : Current hp base (fun j => S.getD j fall) len x (.busy op (.out len)))
    (ret : BusyOnly hp base (fun j => S.getD j fall) len op (ring x turn) (.back len) back (.back 0))
    (ans : Payload) (healthy : ans.fault=0) (normal : ans.opcode.toNat≠acquire)
    (reply : let y := play (ring x turn) back
      let i := (S.getD 0 fall).1
      bind (longGeometry B (y i)) 0 (atSite (y i).long 0)=.reply ans) :
    ∃ f, project (fun j => S.getD j fall) x len=.forward f ∧
      f.fault=0 ∧ f.opcode=ans.opcode := by
  obtain ⟨p,P,_,F,E⟩ := BStarReplyBack.from_arrival hp chart sep ret ans healthy normal reply
  have NP : p.opcode.toNat≠acquire := fun k => normal ((congrArg BitVec.toNat E).symm.trans k)
  obtain ⟨C,v,sel,_,dest,tag,idx⟩ :=
    BStarStageTerminalHealth.selected_turn hp chart turn (sep turn) op old (busy_start hp ret)
  let g := oldPair B x turn
  let raw : Pair (BitVec LW) := ((x turn).long,(x (rightNeighbor turn)).long)
  have D := (new_read B x turn (sep turn) C.source).trans
    ((congrArg (atCursor (ring x turn)) idx).symm.trans P)
  have valid : C.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro eq _
    rw [eq] at tag
    contradiction
  change BStarLongToken.decode (readRaw _ C.source)=_ at D
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x turn,x (rightNeighbor turn)) C.source valid] at D
  change BStarLongToken.decode (readRaw (patchPair (longWork g raw) raw) C.source)=.reply p at D
  rw [terminal_finish g raw C v dest sel,BStarLongToken.decode_encode] at D
  change finish (carried g raw C v)=.reply p at D
  rw [not_center_carries g raw C v (by omega)] at D
  have H := healthy_finish v p D F NP
  obtain ⟨f,Y,Q,op⟩ := BStarForwardProvenance.offer_origin g raw C v sel H.1
  exact ⟨f,(congrArg (atCursor x) idx).trans ((old_read x turn C.source).symm.trans Y),
    Q,op.trans (H.2.trans E)⟩

/-- Find the genuine ISSUE9/terminal outward word, with healthy old
F9, from the actual accepted own consume to PC10. -/
theorem accepted9_terminal {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {ack : Fin n}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w (.busy 9 (.back 0)))
    (event : Event hp (fun j => S.getD j fall) len (play x w) ack (.busy 9 (.back 0)) .idle)
    (accepted : (ctrlOp.read (ring (play x w) ack (S.getD 0 fall).1).long).toNat=10) :
    ∃ (lead back : List (Fin n)) (turn : Fin n) (f : Payload),
      w=lead++turn::back ∧
      Found hp base (fun j => S.getD j fall) len 9 x lead (.out len) ∧
      project (fun j => S.getD j fall) (play x lead) len=.forward f ∧
      f.fault=0 ∧ f.opcode.toNat=9 := by
  have current := BStarGeneratedTapeCuts.at_end hp G
  obtain ⟨H,K⟩ := root_header hp chart current.1.1
  have low : 7≤(ctrlOp.read (ring (play x w) ack (S.getD 0 fall).1).long).toNat := by rw [accepted]; decide
  have high : (ctrlOp.read (ring (play x w) ack (S.getD 0 fall).1).long).toNat≤408 := by rw [accepted]; decide
  obtain ⟨_,ans,returned,healthy,op9⟩ :=
    BStarGeneratedPCAncestry.consume_to_band hp (base:=base) (x:=play x w)
      (addr:=fun j=>S.getD j fall) (len:=len) (op:=9) (e:=ack) K H (sep ack) current event low high
  obtain ⟨lead,turn,back,D,found,_,ret⟩ := found_split_turn hp (from_idle hp G)
  have keep := found
  obtain ⟨u,v,launch,L,_,_,_,F⟩ := keep
  have old : Current hp base (fun j => S.getD j fall) len (play x lead) (.busy 9 (.out len)) := by
    rw [L,BStarResetSchedule.run_append]
    change Current hp base (fun j => S.getD j fall) len (play (ring (play x u) launch) v) (.busy 9 (.out len))
    exact busy_end hp F
  have rebuilt : Found hp base (fun j=>S.getD j fall) len 9 x lead (.out len) := by assumption
  have returned' : let y := play (ring (play x lead) turn) back
      let i := (S.getD 0 fall).1
      bind (longGeometry B (y i)) 0 (atSite (y i).long 0)=.reply ans := by
    rw [D,BStarResetSchedule.run_append] at returned
    exact returned
  obtain ⟨f,FF,cl,op⟩ := terminal_old_healthy hp chart sep turn back 9 old ret ans healthy
    (by rw [op9]; decide) returned'
  exact ⟨lead,back,turn,f,D,rebuilt,FF,cl,(congrArg BitVec.toNat op).trans op9⟩

#print axioms terminal_old_healthy
#print axioms accepted9_terminal
end L4.BStarCopyEnableTerminal

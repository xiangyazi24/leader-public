import Leader.L4.BStarExactStageFlight
import Leader.L4.BStarReplyBack
import Leader.L4.BStarSeparatorRing

namespace L4.BStarStageTerminalHealth
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongLayout BStarLongDoor BStarLongTransport BStarLongEvents
open BStarLongRouting BStarResetQuiet BStarResetQuietTable BStarClearanceForward
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarResetRailRing BStarOwnerLaunchOrigin BStarGeneratedOwner
open BStarSeparatingRail BStarAcquireForwardTrace BStarSeparatorControl
open BStarSeparatorTags BStarSeparatorJoinedTags BStarResetChartService BStarSeparatorQuiet
open BStarStageProvenance

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- The actual physical turn must select the literal K10 terminal
advance. The endpoint-D fact comes from the generated return's start.
No assumption on the old forward payload's health is needed. -/
theorem selected_turn {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (op : Nat)
    (old : Current hp base (fun j => S.getD j fall) len x (.busy op (.out len)))
    (fresh : Current hp base (fun j => S.getD j fall) len (step x e) (.busy op (.back len))) :
    let g := oldPair B x e
    let raw := ((x e).long,(x (rightNeighbor e)).long)
    ∃ C q, (C,.advance q)∈actualOffers g raw ∧ C.kind=.terminal ∧ C.destination=none ∧
      C.source.occurrence.val=10 ∧ S.getD len fall=address e C.source := by
  let addr := fun j => S.getD j fall
  let g := oldPair B x e
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  have MF := frames_any hp chart old.1.1 e (.out len) (by intro eq; cases eq)
    old.2.1 old.1.2.1 old.1.2.2.1
  have quiet := quiet_any hp x e sep addr len MF
  have N : ¬ anyTag.F (project addr (step x e) len) := by
    rintro ⟨f,F⟩
    obtain ⟨d,D⟩ := fresh.2.1.2.1
    exact Token.noConfusion (F.symm.trans D)
  have term : onTerminal hp x e addr len := by
    apply Classical.byContradiction
    intro no
    have h : ¬linkAt hp x e addr len len := fun q => Nat.lt_irrefl _ q.1
    by_cases incoming : ∃ j, j+1=len ∧ linkAt hp x e addr len j
    · obtain ⟨j,E,L⟩ := incoming
      have trail := old.2.1.2.2 j (by omega)
      have f : anyTag.F (project addr x (j+1)) := by rw [E]; exact old.2.1.2.1
      have q := (quiet.tf j L trail f).2
      rw [E] at q
      exact N q
    · exact N ((quiet.idle len (Nat.le_refl _) h
          (fun j E L => incoming ⟨j,E,L⟩) (fun _ => no)).2.2.1 old.2.1.2.1)
  obtain ⟨C,hc,kind,dest,tag,idx⟩ := term
  have f : anyTag.F (readK raw C.source) :=
    ((old_read x e C.source).trans ((congrArg (atCursor x) idx).symm)).symm ▸ old.2.1.2.1
  obtain ⟨pr,P⟩ := f
  have F : anyTag.F (bound g (readK raw) C.source) := by
    unfold bound
    rw [P]
    exact bound_F _ _ _
  obtain ⟨p',D⟩ := F
  rcases forward_mark g raw C p' hc (by simp [kind]) D with held|⟨q,sel⟩
  · have safe := (frames_any hp chart old.1.1 e (.out len)
      (by intro e; cases e) old.2.1 old.1.2.1 old.1.2.2.1).safe len (Nat.le_refl _) C.source idx
    have parked := parked_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) C
      held safe.1 safe.2 ⟨p',D⟩
    rw [new_read B x e sep C.source] at parked
    change anyTag.F (atCursor (step x e) (address e C.source)) at parked
    rw [←idx] at parked
    exact (N parked).elim
  · exact ⟨C,q,sel,kind,dest,tag,idx⟩

private theorem finish_health (p q : Payload) (R : finish p=.reply q) (H : Stage q) :
    Stage p := by
  unfold finish at R
  dsimp only at R
  split at R
  · change (.reply _ : Token)=.reply q at R
    cases R
    exact ((show (1 : BitVec 1)≠0 by decide) H.1).elim
  · rename_i N
    have healthy : p.fault=0 := by
      apply Classical.byContradiction
      intro ne
      exact N (bne_iff_ne.mpr ne)
    split at R
    · rename_i A
      have op : p.opcode.toNat=acquire := beq_iff_eq.mp A
      split at R <;> cases R <;> exact False.elim ((by decide : acquire≠stageOp) (op.symm.trans H.2))
    · split at R
      · change (.reply _ : Token)=.reply q at R
        cases R
        exact ((show (1 : BitVec 1)≠0 by decide) H.1).elim
      · cases R
        exact ⟨healthy,H.2⟩

/-- Backward health at the real selected terminal, including the
joined row and old operand binding. -/
theorem selected_terminal_health {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (old : Current hp base (fun j => S.getD j fall) len x (.busy stageOp (.out len)))
    (fresh : Current hp base (fun j => S.getD j fall) len (step x e) (.busy stageOp (.back len)))
    (q : Payload) (new : project (fun j => S.getD j fall) (step x e) len=.reply q) (H : Stage q) :
    ∃ p, project (fun j => S.getD j fall) x len=.forward p ∧ Stage p := by
  obtain ⟨C,v,sel,kind,dest,tag,idx⟩ := selected_turn hp chart e sep stageOp old fresh
  let g := oldPair B x e
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  have D := (new_read B x e sep C.source).trans
    ((congrArg (atCursor (step x e)) idx).symm.trans new)
  have valid : C.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E _
    rw [E] at tag
    contradiction
  change BStarLongToken.decode (readRaw _ C.source)=_ at D
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) C.source valid] at D
  change BStarLongToken.decode (readRaw (patchPair (longWork g raw) raw) C.source)=.reply q at D
  rw [terminal_finish g raw C v dest sel,BStarLongToken.decode_encode] at D
  have vEq : carried g raw C v=v := by
    have N : C.source.occurrence.val≠1 := by omega
    unfold carried BStarLongArithmetic.visit
    have M : (C.source.occurrence.val != 1)=true := bne_iff_ne.mpr N
    simp only [M,Bool.true_or,if_true]
    rw [BStarLongOutgoing.noncenter_hold _ _ _ _ N]
    rfl
  change finish (carried g raw C v)=.reply q at D
  rw [vEq] at D
  have Hv := finish_health v q D H
  obtain ⟨p,P,Q,_⟩ := BStarStageProvenance.offer_origin g raw C v sel Hv
  exact ⟨p,(congrArg (atCursor x) idx).trans ((old_read x e C.source).symm.trans P),Q⟩

/-- Discharge the last conditional leaf of the STAGE flight extraction
with the real returned acknowledgement and literal selected old K10. -/
theorem terminal_health {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e) :
    BStarExactStageFlight.TerminalHealth hp base (fun j => S.getD j fall) len := by
  intro y turn back f old _ ret bound H
  have notA : f.opcode.toNat≠acquire := H.2.symm ▸ (by decide : stageOp≠acquire)
  obtain ⟨p,P,_,F,E⟩ := BStarReplyBack.from_arrival hp chart sep ret f H.1 notA bound
  exact selected_terminal_health hp chart turn (sep turn) old (busy_start hp ret) p P
    ⟨F,(congrArg BitVec.toNat E).trans H.2⟩

#print axioms selected_turn
#print axioms terminal_health
end L4.BStarStageTerminalHealth

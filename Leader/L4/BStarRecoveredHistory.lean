import Leader.L4.BStarOwnerRecoveryPass
import Leader.L4.BStarResetIssueClean
import Leader.L4.BStarGeneratedOwner

namespace L4.BStarRecoveredHistory
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongTransport BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarAcquireForwardTrace BStarLongFixedRouting BStarResetChartTouch BStarResetChartService
open BStarResetMarkAdapter BStarResetRailRing BStarResetSchedule
open BStarSeparatingRail BStarResetQuiet BStarResetQuietTable BStarResetIdleRing

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

open BStarResetTaggedRows BStarResetCycle BStarResetHealthyService BStarOwnerRecoveryPass BStarGeneratedOwner
open BStarClearanceResidual BStarResetControllerEntry

private theorem end_inv {Y : Type} {m : Nat} (nextMark : Y → Fin m → Y)
    (track : Y → BStarSeparatingRail.Rail) (tag : Tag) (len : Nat) (Inv : Y → Prop)
    (closed : ∀ x e z, Inv x → z≠.back 0 → Good tag len (track x) z → Inv (nextMark x e))
    {x : Y} {u v : Cursor} {w : List (Fin m)}
    (T : Seen nextMark track tag len x u w v) (I : Inv x) (G : Good tag len (track x) u) :
    Inv (BStarResetSchedule.run nextMark x w) ∧
      Good tag len (track (BStarResetSchedule.run nextMark x w)) v := by
  induction T with
  | nil => exact ⟨I,G⟩
  | cons l _ _ g _ ih =>
    exact ih (closed _ _ _ I l G) g

/-- A completed exact reset Stage, even with a dirty old suffix,
leaves its entire chart empty after the separate consumption. In
particular the actual RCLEAR Stage supplies the all-E entry of RREL. -/
theorem stage_endpoint_exact {base x y : XX} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : XX → Prop) (good : Q x)
    (fiber : ∀ x,Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (AllSizeS1Geometry.step B x e))
    (op : Nat) (ho : op<3) (w : List (Fin n))
    (st : BStarResetHealthyCycle.Stage hp (fun j => S.getD j fallback) len op x w y) :
    ((ctrlPhase.read (y (S.getD 0 fallback).1).long)=1 ∧
      (ctrlOp.read (y (S.getD 0 fallback).1).long)=BitVec.ofNat 9 (op+1)) ∧
    (∀ j≤len, project (fun j => S.getD j fallback) y j=.empty) := by
  obtain ⟨mid,W,Y,P,O,seen,Fd⟩ := st
  let adr := fun j => S.getD j fallback
  let root := (adr 0).1
  let door := RearTrace.predecessor root
  let nextMark := AllSizeS1Geometry.step (n:=n) B
  let z := nextMark x door
  let Inv := fun x => Q x ∧ Waiting hp base root op x
  have d : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C (fiber x good)
  have HH : oldH6 B x (rightNeighbor door)=true := by rw [d]; exact H
  have pp : (ctrlPhase.read (x (rightNeighbor door)).long).toNat=1 := by rw [d]; exact P
  have oo : (ctrlOp.read (x (rightNeighbor door)).long).toNat=op := by rw [d]; exact O
  have M := genuine_wait hp x door (sep door) op ho HH pp oo
  rw [d] at M
  have qz : Q z := closed x door good
  have Iz : Inv z := ⟨qz,fiber z qz,M.2.1,M.2.2⟩
  have F : project adr z 0=.forward (resetPayload op) :=
    (congrArg (atCursor z) (show adr 0=(root,0) from Prod.ext rfl K)).trans M.1
  have G : Good (healthyTag op) len (project adr z) (.out 0) :=
    ⟨Nat.zero_le _,F,fun _ H => (Nat.not_lt_zero _ H).elim⟩
  have keep (a : XX) (e : Fin n) (u : Cursor) (I : Inv a) (N : u≠.back 0)
      (G : Good (healthyTag op) len (project adr a) u) : Inv (nextMark a e) := by
    have v := closed a e I.1
    exact ⟨v,waiting_closed_at hp C e op ho (fiber _ v) u N (weak_good _ _ _ _ G) I.2⟩
  obtain ⟨I,GG⟩ := end_inv nextMark (project adr) (healthyTag op) len Inv keep seen Iz G
  have eff : Clean (project adr) (resetTag op) len (BStarResetSchedule.run nextMark z mid) :=
    ⟨weakD op _ GG.2.1,GG.2.2.2⟩
  have A := BStarResetConsumedClean.consumed_clean hp C op ho I.2 eff sep
  have X : w=door::(mid++[door]) := W
  rw [Y,X]
  have E : BStarResetSchedule.run nextMark x (door::(mid++[door])) =
      nextMark (BStarResetSchedule.run nextMark z mid) door := by
    change BStarResetSchedule.run nextMark z (mid++[door])=_
    rw [BStarResetSchedule.run_append]
    rfl
  rw [E]
  exact ⟨⟨A.2.1,A.2.2 Fd⟩,A.1⟩


private theorem run_keeps {z : XX} (Q : XX → Prop)
    (closure : ∀ x e, Q x → Q (AllSizeS1Geometry.step B x e))
    (w : List (Fin n)) (I : Q z) : Q (BStarResetSchedule.run (AllSizeS1Geometry.step B) z w) := by
  induction w generalizing z with
  | nil => exact I
  | cons e w ih => exact ih (closure _ e I)

/-- Every compatible suffix on the same physical tape after an actual
Recovered credit has a generated history based at its proved ISSUE3
boundary, with the same owner chart obtained from that credit. -/
theorem recovered_suffix {base x : XX} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {w : List (Fin n)}
    (R : Recovered hp base hh o x w)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : XX → Prop) (I : Q x)
    (fiber : ∀ x,Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (AllSizeS1Geometry.step B x e))
    (tail : List (Fin n)) :
    let st := AllSizeS1Geometry.step (n:=n) B
    let y := BStarResetSchedule.run st x w
    ∃ S len fall, Chart hp base hh o S len fall ∧
      let addr := fun j => S.getD j fall
      let root := (addr 0).1
      (ctrlOp.read (y root).long).toNat=3 ∧
      Current hp base addr len y .idle ∧
      ∃ d, GeneratedOwner hp base addr len y .idle tail d ∧
        Q (BStarResetSchedule.run st x (w++tail)) ∧
        Current hp base addr len (BStarResetSchedule.run st x (w++tail)) d := by
  dsimp only
  obtain ⟨S,len,fall,C,u,v,residual,w0,w1,w2,y1,y2,_,_,_,_,S0,S1,S2⟩ := R
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let st := AllSizeS1Geometry.step (n:=n) B
  let e := RearTrace.predecessor root
  let before := BStarResetSchedule.run st x u
  let launched := st before e
  let returned := BStarResetSchedule.run st launched v
  let consumed := st returned e
  let zero := BStarResetSchedule.run st consumed residual
  let y := BStarResetSchedule.run st x w
  have q0 : Q zero := run_keeps hp Q closed residual
    (closed _ _ (run_keeps hp Q closed v (closed _ _ (run_keeps hp Q closed u I))))
  have q1 : Q y1 := by
    obtain ⟨_,_,Eq,_,_,_,_⟩ := S0
    exact Eq.symm ▸ run_keeps hp Q closed w0 q0
  have q2 : Q y2 := by
    obtain ⟨_,_,Eq,_,_,_,_⟩ := S1
    exact Eq.symm ▸ run_keeps hp Q closed w1 q1
  have L := stage_endpoint_exact hp C sep Q q2 fiber closed 2 (by decide) w2 S2
  have phase : (ctrlPhase.read (y root).long).toNat=1 := congrArg BitVec.toNat L.1.1
  have pc : (ctrlOp.read (y root).long).toNat=3 := congrArg BitVec.toNat L.1.2
  have idle : Current hp base addr len y .idle :=
    ⟨legal_issue _ phase (pc.symm ▸ (by decide : (3 : Nat)<413)),L.2⟩
  obtain ⟨d,G,q,K⟩ := generated_word hp C Q fiber
    (fun z H e => closed z e H) sep tail .idle (run_keeps hp Q closed w I) idle
  refine ⟨S,len,fall,C,pc,idle,d,G,?_⟩
  rw [BStarResetSchedule.run_append]
  exact ⟨q,K⟩

#print axioms stage_endpoint_exact
#print axioms recovered_suffix
end L4.BStarRecoveredHistory

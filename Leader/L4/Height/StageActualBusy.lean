import Leader.L4.Height.StageScopedTurns
import Leader.L4.Height.StagePositiveAck
import Leader.L4.Height.GateResidence

namespace L4.Height.StageActualBusy
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarLongFixedRouting BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetChartService
open BStarSealBitDescriptor BStarAcquireHistoryReturn
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step
open StageScopedReplay
open BStarAcquireForwardTrace BStarSeparatingRail

def Wire (addr : Nat→Pos n) (y : X) (source : BitVec LW) : Cursor→Prop
  | .out j => project addr y j=.forward (BStarStageIssue.payload source)
  | .back j => project addr y j=.reply StageReplyForm.reply

/-- Authenticated STAGE payload induction along the supplied literal
busy tape, without any nominated subsequence or assumed successful ACK. -/
theorem wire_of_busy {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (source : BitVec LW) (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    {w : List (Fin n)} {j k : Cursor}
    (T : BusyOnly hp base (fun j=>S.getD j fall) len stageOp x j w k)
    (qx : Q x) (wire : Wire (fun j=>S.getD j fall) x source j)
    (auth : ∀ a, j=.out a → PrefixAuth hp base x (fun j=>S.getD j fall) len a source d w) :
    Wire (fun j=>S.getD j fall) (play x w) source k := by
  induction T with
  | nil _ => exact wire
  | @cons y z z' last e w I E tail ih =>
    have next := busy_start hp tail
    have new : Wire (fun j=>S.getD j fall) (step y e) source z' := by
      cases z with
      | out j =>
        have bound : j≤len := I.2.1.1
        by_cases last : j=len
        · subst j
          by_cases term : onTerminal hp y e (fun j=>S.getD j fall) len
          · obtain ⟨_,J,R⟩ := StagePositiveTerminal.nominated_turn hp C Q fiber closed sep qx e source d D I wire term
            have eq := L4.Height.current_mode_unique hp _ _ next J
            cases eq
            exact R
          · obtain ⟨_,J,R⟩ := StageScopedTurns.terminal_hold hp C Q fiber closed sep qx e source d D I wire term
            have eq := L4.Height.current_mode_unique hp _ _ next J
            cases eq
            exact R
        · obtain ⟨k,_,_,_,J,R,_⟩ := arbitrary_stage_step hp C Q fiber closed sep source d D j
            (by omega) qx e I wire ((auth j rfl) [] e w rfl j (.nil I))
          have eq := L4.Height.current_mode_unique hp _ _ next J
          cases eq
          exact R
      | back j =>
        cases j with
        | zero =>
          have off : e≠RearTrace.predecessor (S.getD 0 fall).1 := by
            cases E with
            | transit _ _ z live _ => exact (live rfl).elim
            | arrived_hold _ ne => exact ne
          have A := BStarPositiveReply.at_root_step hp C Q fiber closed sep qx e stageOp
            StageReplyForm.reply rfl I wire
          rw [if_neg off] at A
          have eq := L4.Height.current_mode_unique hp _ _ next A.2.1
          cases eq
          exact A.2.2
        | succ j =>
          obtain ⟨k,_,_,_,J,R,_⟩ := BStarPositiveReply.reverse_step hp C Q fiber closed sep qx e stageOp j
            StageReplyForm.reply rfl I wire
          have eq := L4.Height.current_mode_unique hp _ _ next J
          cases eq
          exact R
    apply ih (closed _ qx e) new
    intro a eq
    subst z'
    cases E with
    | transit _ z _ _ seen =>
      cases seen with
      | cons _ _ adv _ rest =>
        cases rest
        cases adv with
        | stay _ => exact (auth _ rfl).tail hp I (.transit _ _ _ (by intro h; cases h) (.cons (by intro h; cases h) ‹_› (.stay _) ‹_› (.nil _ _)))
        | forward => exact (auth _ rfl).tail hp I (.transit _ _ _ (by intro h; cases h) (.cons (by intro h; cases h) ‹_› (.forward _) ‹_› (.nil _ _)))


/-- A later PC2 on the same generated word forces the first literal
consume of the currently outstanding STAGE; no fairness premise. -/
theorem first_stage_consume {base x : X} {addr : Nat→Pos n} {len : Nat}
    {j : Cursor} {m : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base addr len x (.busy stageOp j) w m)
    (later : (ctrlOp.read (play x w (addr 0).1).long).toNat=2) :
    ∃ pre e tail, w=pre++e::tail ∧
      BusyOnly hp base addr len stageOp x j pre (.back 0) ∧
      Event hp addr len (play x pre) e (.busy stageOp (.back 0)) .idle := by
  generalize H : Mode.busy stageOp j = initial at T
  induction T generalizing j with
  | @endpoint y m I =>
    rw [←H] at I
    have eq := I.1.2.2.2
    change (ctrlOp.read (y (addr 0).1).long).toNat=2 at later
    rw [later] at eq
    exact ((by decide : (2:Nat)≠stageOp) eq).elim
  | @next y a e w b dest I E T ih =>
    subst a
    cases E with
    | consume _ own clean =>
      exact ⟨[],e,w,rfl,.nil I,.consume _ own clean⟩
    | transit _ z d live seen =>
      obtain ⟨pre,f,tail,W,L,F⟩ := ih (j:=d) later rfl
      exact ⟨e::pre,f,tail,congrArg (List.cons e) W,.cons I (.transit _ _ _ live seen) L,F⟩
    | arrived_hold _ ne =>
      obtain ⟨pre,f,tail,W,L,F⟩ := ih (j:=.back 0) later rfl
      exact ⟨e::pre,f,tail,congrArg (List.cons e) W,.cons I (.arrived_hold stageOp ne) L,F⟩


/-- On a real emitted continuation known to reach PC2, an already
launched authorized STAGE necessarily first reaches idle ISSUE409. -/
theorem issue409_before_pc2 {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (source : BitVec LW) (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (src : sourceDescriptor.read (x (S.getD 0 fall).1).long=sourceDescriptor.read source)
    {w : List (Fin n)} {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x (.busy stageOp (.out 0)) w m)
    (qx : Q x) (wire : Wire (fun j=>S.getD j fall) x source (.out 0))
    (auth : PrefixAuth hp base x (fun j=>S.getD j fall) len 0 source d w)
    (later : (ctrlOp.read (play x w (S.getD 0 fall).1).long).toNat=2) :
    ∃ pre e tail,w=pre++e::tail ∧
      BusyOnly hp base (fun j=>S.getD j fall) len stageOp x (.out 0) pre (.back 0) ∧
      (let y := play x pre
       Event hp (fun j=>S.getD j fall) len y e (.busy stageOp (.back 0)) .idle ∧
       BStarLongCommand.bind (longGeometry B (y (S.getD 0 fall).1)) 0 (atSite (y (S.getD 0 fall).1).long 0)=.reply StageReplyForm.reply ∧
       (ctrlOp.read (step y e (S.getD 0 fall).1).long).toNat=sealOp ∧
       BStarLongPublication.decode (sourceDescriptor.read (step y e (S.getD 0 fall).1).long)=some d) := by
  let adr := fun j=>S.getD j fall
  obtain ⟨pre,e,tail,W,L,E⟩ := first_stage_consume hp T later
  have known := wire_of_busy hp C Q fiber closed sep source d D L qx wire (fun a eq=>by
    have Z : a=0 := by injection eq; omega
    subst a
    exact auth.take hp pre (e::tail) W)
  have I := busy_end hp L
  have root := root_header hp C I.1.1
  have reply : atSite (play x pre (adr 0).1).long 0=.reply StageReplyForm.reply := by
    change atSite (play x pre (adr 0).1).long (adr 0).2=_ at known
    rwa [root.2] at known
  have folded := (busy_preserves_descriptor hp C sep L (by decide)).1.trans src
  have R : BStarLongCommand.bind (longGeometry B (play x pre (adr 0).1)) 0
      (atSite (play x pre (adr 0).1).long 0)=.reply StageReplyForm.reply := by
    rw [reply]
    exact StageReplyForm.bind_exact _ _
  obtain ⟨PC,_,DD⟩ := StageAckToSeal.stage_ack_seal_issue hp (addr:=adr)
    root.2 root.1 (sep _) I E StageReplyForm.reply rfl rfl R d ((congrArg BStarLongPublication.decode folded).trans D)
  exact ⟨pre,e,tail,W,L,E,R,PC,DD⟩

#print axioms wire_of_busy
#print axioms first_stage_consume
#print axioms issue409_before_pc2
end L4.Height.StageActualBusy

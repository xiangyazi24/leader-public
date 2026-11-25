import Leader.L4.BStarResetEndpointZero
import Leader.L4.BStarGeneratedOwner

namespace L4.BStarRRELHold
open AllSizeProtocol BStarTrace BStarLongWork BStarLongDoor BStarLongCommand
open BStarLongToken BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarAcquireAnchors BStarResetChartTouch BStarLongFixedRouting
open BStarResetMarkAdapter BStarSeparatingRail BStarResetSchedule BStarSeparatorControl
open BStarResetNoAcquire BStarGrantBirth BStarGeneratedOwner BStarResetChartService
open BStarResetHealthyService BStarResetTaggedRows BStarResetCycle

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

private theorem keep_word (Q : X → Prop)
    (closed : ∀ x e,Q x → Q (step x e)) (w : List (Fin n)) (x : X)
    (q : Q x) : Q (run x w) := by
  induction w generalizing x with
  | nil => exact q
  | cons e w ih => exact ih _ (closed _ _ q)

theorem arrived_no_win {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (L : Clean (project (fun j => S.getD j fall)) anyTag len x)
    (e i : Fin n) (j : Fin 3) (own : commandOwner (oldH6 B base) i (slot j)=o.val) :
    ¬ WonAt hp x e i j := by
  apply no_win_at hp
  apply quiet_no_acquire
  have active : BStarAcquireRailCoverage.active (longGeometry B (base i)) (slot j)=true := by
    have h := j.isLt
    unfold BStarAcquireRailCoverage.active slot
    simp [show j.val≠8 by omega,show j.val≠9 by omega]
  obtain ⟨k,lk,E⟩ := List.getElem_of_mem (C.cover (i,slot j) active own)
  have eq : S.getD k fall=(i,slot j) := (List.getElem_eq_getD _).symm.trans E
  have Ls := C.length
  have H : project (fun j => S.getD j fall) x k=BStarAcquireForwardTrace.atCursor x (i,slot j) :=
    congrArg (BStarAcquireForwardTrace.atCursor x) eq
  rw [←H]
  cases k with
  | zero => exact .inr (.inr (.inr L.1))
  | succ k => exact .inl (L.2 _ (by omega) (by omega))

/-- An arrived clean reply can be held across any sequence of foreign
marks. None creates a grant of this owner. The terminal incoming mark
also reads the old clean reply, so it cannot create a grant either. -/
theorem hold_then_ack_zero {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (init : Q x)
    (fiber : ∀ x,Q x → ∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (step x e))
    (L : Clean (project (fun j => S.getD j fall)) anyTag len x)
    (i : Fin n) (j : Fin 3) (own : commandOwner (oldH6 B base) i (slot j)=o.val)
    (Z : bit x i j=0) (w : List (Fin n))
    (away : ∀ e∈w,e≠RearTrace.predecessor (S.getD 0 fall).1) :
    let y := run x w
    bit y i j=0 ∧
      bit (step y (RearTrace.predecessor (S.getD 0 fall).1)) i j=0 := by
  have one (x : X) (L : Clean (project (fun j => S.getD j fall)) anyTag len x)
      (e : Fin n) (z : bit x i j=0) : bit (step x e) i j=0 := by
    apply zero_along hp sep x i j [e] z
    intro pre f tail E
    have N := congrArg List.length E
    simp only [List.length_cons,List.length_append,List.length_nil] at N
    have P : pre=[] := List.length_eq_zero_iff.mp (by omega)
    subst pre
    have F : e=f := (List.cons.inj E).1
    subst f
    exact arrived_no_win hp C L e i j own
  induction w generalizing x with
  | nil => exact ⟨Z,one x L _ Z⟩
  | cons e w ih =>
    have H := (arrived_nonown hp C (fiber x init) e (sep e)
      (away e (List.mem_cons_self)) L).1
    exact ih (closed _ _ init) H (one x L e Z)
      (fun d hd => away d (List.mem_cons_of_mem _ hd))

theorem first_arrival_zero {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (init : Q x)
    (fiber : ∀ x,Q x → ∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (step x e))
    (clean : ∀ j≤len, project (fun j => S.getD j fall) x j=.empty)
    (w : List (Fin n))
    (i : Fin n) (j : Fin 3) (own : commandOwner (oldH6 B base) i (slot j)=o.val) :
    let adr := fun k => S.getD k fall
    let root := (adr 0).1
    let door := RearTrace.predecessor root
    let z := step x door
    let y := run z w
    (ctrlPhase.read (x root).long).toNat=1 →
    (ctrlOp.read (x root).long).toNat=2 →
    Seen step (project adr) (healthyTag 2) len z (.out 0) w (.back 0) →
    project adr y 0=finish (resetPayload 2) →
    Q y ∧ Clean (project adr) anyTag len y ∧ bit y i j=0 := by
  dsimp only
  intro phase op seen reply
  let adr := fun k => S.getD k fall
  let root := (adr 0).1
  let door := RearTrace.predecessor root
  let z := step x door
  let y := run z w
  let Inv := fun a => Q a ∧ Waiting hp base root 2 a
  have D : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C (fiber x init)
  have HH : oldH6 B x (rightNeighbor door)=true := by rw [D]; exact H
  have P : (ctrlPhase.read (x (rightNeighbor door)).long).toNat=1 := by rw [D]; exact phase
  have O : (ctrlOp.read (x (rightNeighbor door)).long).toNat=2 := by rw [D]; exact op
  have M := genuine_wait hp x door (sep door) 2 (by decide) HH P O
  rw [D] at M
  have qz : Q z := closed _ _ init
  have Iz : Inv z := ⟨qz,fiber z qz,M.2.1,M.2.2⟩
  have F : project adr z 0=.forward (resetPayload 2) :=
    (congrArg (BStarAcquireForwardTrace.atCursor z) (show adr 0=(root,0) from Prod.ext rfl K)).trans M.1
  have G : Good (healthyTag 2) len (project adr z) (.out 0) :=
    ⟨Nat.zero_le _,F,fun _ H => (Nat.not_lt_zero _ H).elim⟩
  have keep (a : X) (e : Fin n) (u : Cursor) (I : Inv a) (N : u≠.back 0)
      (G : Good (healthyTag 2) len (project adr a) u) : Inv (step a e) := by
    have v := closed a e I.1
    exact ⟨v,waiting_closed_at hp C e 2 (by decide) (fiber _ v) u N (weak_good _ _ _ _ G) I.2⟩
  have facts (a : X) (I : Inv a) :
      (∀ i, Layout B base i=Layout B a i) ∧
      LongDoorGuard.valid manifest (a root).long=true ∧
      (ctrlPhase.read (a root).long).toNat=2 :=
    ⟨I.2.1,I.2.2.1,I.2.2.2.1⟩
  obtain ⟨pre,e,tail,W,A⟩ :=
    BStarResetReleaseHistory.incidence_release hp C sep Inv keep facts Iz G w seen i j own
  have final_good {a : X} {u v : Cursor} {w : List (Fin n)}
      (g : Good (healthyTag 2) len (project adr a) u)
      (s : Seen step (project adr) (healthyTag 2) len a u w v) :
      Good (healthyTag 2) len (project adr (run a w)) v := by
    induction s with
    | nil => exact g
    | cons _ _ _ next _ ih => exact ih next
  have back := final_good G seen
  refine ⟨keep_word hp Q closed w z qz,⟨⟨resetPayload 2,back.2.1⟩,back.2.2.2⟩,?_⟩
  have s : BStarResetHealthyCycle.Stage hp adr len 2 x (door::(w++[door]))
      (run x (door::(w++[door]))) := ⟨w,rfl,rfl,phase,op,seen,reply⟩
  change bit (run z w) i j=0
  rw [W,BStarResetSchedule.run_append]
  apply zero_along hp sep (step (run z pre) e) i j tail A
  intro a f t E
  have all : door::(w++[door])=(door::(pre++e::a))++f::(t++[door]) := by
    rw [W,E]
    simp only [List.cons_append,List.append_assoc]
  have N := BStarResetEndpointZero.stage_no_win hp C sep Q init fiber closed clean _ s
    i j own _ _ _ all
  change ¬ WonAt hp (run z (pre++e::a)) f i j at N
  rwa [BStarResetSchedule.run_append] at N

end L4.BStarRRELHold

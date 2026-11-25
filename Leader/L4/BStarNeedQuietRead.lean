import Leader.L4.BStarNeedTrace

namespace L4.BStarNeedQuietRead
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail BStarNeedTrace
open BStarClearanceRaceMark BStarOwnerControlHistory BStarSeparatorControl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- A first observation of the owner's canonical fresh BIT wire. This
uses only the literal old state and chosen raw label, not an ACK. -/
def FirstRead (base : X) (addr : Nat→Pos n) (len g : Nat) (x : X) (e : Fin n) : Prop :=
  Current hp base addr len x (.busy bitOp (.out g)) ∧
    ∃ p : Payload, project addr x g=.forward p ∧
      p.fault=0 ∧ p.opcode.toNat=bitOp ∧ p.race=1 ∧ p.outcome=0 ∧ p.argument=0 ∧
      (e=incident (addr g).1 .left ∨ e=incident (addr g).1 .right)

theorem first_read_mode {base x : X} {addr : Nat→Pos n} {len g : Nat} {e : Fin n} {m : Mode}
    (I : Current hp base addr len x m) (read : FirstRead hp base addr len g x e) :
    m=.busy bitOp (.out g) := by
  have G := read.1.2.1
  have F := G.2.1
  have J := G.1
  cases m with
  | idle =>
    rw [I.2 g J] at F
    exact (BStarSeparatorParked.forward_not_empty F).elim
  | busy op z =>
    have pc : op=bitOp := I.1.2.2.2.symm.trans read.1.1.2.2.2
    subst op
    cases z with
    | back j => exact (pointed_backward_no_forward _ len j I.2.1 g J F).elim
    | out j =>
      have K := (pointed_unique_forward _ len j I.2.1 I.2.2 g J).mp F
      rw [K]

/-- A literal generated segment whose old modes exclude a fresh
observation. The endpoint's next mark is intentionally not counted. -/
inductive Quiet (base : X) (addr : Nat→Pos n) (len g : Nat) :
    X → Mode → List (Fin n) → Mode → Prop where
  | done {x m} (I : Current hp base addr len x m) : Quiet base addr len g x m [] m
  | cons {x u v d e w} (I : Current hp base addr len x u)
      (E : Event hp addr len x e u v) (off : u≠.busy bitOp (.out g))
      (rest : Quiet base addr len g (step x e) v w d) :
        Quiet base addr len g x u (e::w) d

theorem quiet_append {base x : X} {addr : Nat→Pos n} {len g : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (U : Quiet hp base addr len g x a u b) (V : Quiet hp base addr len g (play x u) b v c) :
    Quiet hp base addr len g x a (u++v) c := by
  induction U with
  | done _ => exact V
  | cons I E off _ ih => exact .cons I E off (ih V)

theorem q_busy {base x : X} {addr : Nat→Pos n} {len g op : Nat}
    {a b : Cursor} {w : List (Fin n)}
    (T : BusyOnly hp base addr len op x a w b) (opNot : op≠bitOp) :
    Quiet hp base addr len g x (.busy op a) w (.busy op b) := by
  induction T with
  | nil I => exact .done I
  | cons I E _ ih => exact .cons I E (fun H=>opNot (Mode.busy.inj H).1) ih

theorem q_foreign {base x : X} {addr : Nat→Pos n} {len g : Nat} {b : Mode}
    {w : List (Fin n)} (T : GeneratedOwner hp base addr len x .idle w b)
    (off : ∀ e∈w,rightNeighbor e≠(addr 0).1) :
    Quiet hp base addr len g x .idle w .idle := by
  induction w generalizing x b with
  | nil => exact .done (BStarGeneratedTapeCuts.at_start hp T)
  | cons e w ih =>
    cases T with
    | next I E R =>
      have outside := off e List.mem_cons_self
      cases E with
      | idle_hold H =>
        exact .cons I (.idle_hold H) (by intro N; cases N)
          (ih R (fun a A=>off a (List.mem_cons_of_mem _ A)))
      | bad_issue eq _ => exact (outside (eq ▸ RearTrace.right_predecessor (addr 0).1)).elim
      | launch eq _ => exact (outside (eq ▸ RearTrace.right_predecessor (addr 0).1)).elim

theorem silent_span {base x : X} {addr : Nat→Pos n} {len g : Nat}
    {a b : Mode} {w : List (Fin n)} (T : Quiet hp base addr len g x a w b) :
    ∀ u e v,w=u++e::v → ¬FirstRead hp base addr len g (play x u) e := by
  induction T with
  | done _ =>
    intro u e v H
    cases u <;> contradiction
  | @cons x a z d mark word I E off T ih =>
    intro u e v H
    cases u with
    | nil =>
      intro read
      exact off (first_read_mode hp I read)
    | cons f u =>
      obtain ⟨rfl,H'⟩ := List.cons.inj H
      exact ih u e v H'

/-- Isolate the single actual BIT window from a matched tail. Both
other stretches provably contain no first-side observation. -/
theorem isolate_bit {base x : X} {addr : Nat→Pos n} {len k g : Nat}
    {sf wait1 bit wait2 com : List (Fin n)}
    (T : Phases hp base addr len k x sf wait1 bit wait2 com) :
    let door := RearTrace.predecessor (addr 0).1
    let pre := sf++door::(wait1++[door])
    let post := door::(wait2++door::com)
    let y := play x pre
    tailWord door sf wait1 bit wait2 com=pre++(bit++post) ∧
    Quiet hp base addr len g x (.busy sealOp (.out (k+1))) pre (.busy bitOp (.out 0)) ∧
    BusyOnly hp base addr len bitOp y (.out 0) bit (.back 0) ∧
    Quiet hp base addr len g (play y bit) (.busy bitOp (.back 0)) post (.busy commitOp (.out k)) := by
  let door := RearTrace.predecessor (addr 0).1
  have q₁ := q_busy hp (g:=g) T.sealFlight (by decide)
  have flight := T.bitFlight
  have atIssue := BStarGeneratedTapeCuts.at_start hp T.waitBit
  have q₂ := q_foreign hp (g:=g) T.waitBit T.beforeBitOff
  have qb := BStarGeneratedTapeCuts.at_end hp T.waitBit
  have q₃ := q_foreign hp (g:=g) T.waitCommit T.beforeCommitOff
  have qc := BStarGeneratedTapeCuts.at_end hp T.waitCommit
  have com := q_busy hp (g:=g) T.commitFlight (by decide)
  dsimp only
  refine ⟨by simp only [tailWord,List.append_assoc,List.cons_append,List.nil_append],
    quiet_append hp q₁ (.cons (BStarAcquireHistoryReturn.busy_end hp T.sealFlight) T.sealAck
      (by intro H; exact (by decide : sealOp≠bitOp) (Mode.busy.inj H).1)
      (quiet_append hp q₂ (.cons qb T.bitIssue (by intro H; cases H) (.done (busy_start hp flight))))),
    ?_,?_⟩
  · rw [BStarResetSchedule.run_append]
    change BusyOnly hp base addr len bitOp (play (step (play x sf) door) (wait1++[door])) _ _ _
    rw [BStarResetSchedule.run_append]
    exact flight
  · rw [BStarResetSchedule.run_append]
    change Quiet hp base addr len g (play (play (step (play x sf) door) (wait1++[door])) bit) _ _ _
    rw [BStarResetSchedule.run_append]
    exact .cons (BStarAcquireHistoryReturn.busy_end hp flight) T.bitAck
      (by intro H; cases (Mode.busy.inj H).2)
      (quiet_append hp q₃ (.cons qc T.commitIssue (by intro H; cases H) com))

end L4.BStarNeedQuietRead

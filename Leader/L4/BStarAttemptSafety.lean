import Leader.L4.BStarAttemptCuts
import Leader.L4.BStarBeforeCommitWindow

namespace L4.BStarAttemptSafety
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarLongFixedRouting BStarLongCommand
open BStarLongDoor BStarClearanceSource BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarGeneratedTapeCuts BStarWriterTransferWindow BStarCommitTailScan
open BStarGrantWriterHistory BStarBeforeCommitWindow

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

def PreIssue (i : Fin n) (x : X) (w : List (Fin n)) : Prop :=
  ∀ a e b,w=a++e::b →
    let old := run x a
    pc old i≠2 ∧ (Issue (old i).long ∨ pc old i≠411)

def ReleaseFree (i : Fin n) (x : X) (w : List (Fin n)) : Prop :=
  ∀ a e b,w=a++e::b → pc (run x a) i≠2

private theorem append_mark (D : X → Prop) (x : X) (u v : List (Fin n))
    (A : ∀ p e t,u=p++e::t → D (run x p))
    (B0 : ∀ p e t,v=p++e::t → D (run (run x u) p)) :
    ∀ p e t,u++v=p++e::t → D (run x p) := by
  intro p e t E
  rcases List.append_eq_append_iff.mp E with ⟨q,P,F⟩|⟨q,P,F⟩
  · rw [P,BStarResetSchedule.run_append]
    exact B0 q e t F
  · cases q with
    | nil =>
      simp only [List.append_nil] at P
      rw [←P]
      exact B0 [] e t F.symm
    | cons m q =>
      have G : e::t=m::(q++v) := F
      have E := (List.cons.inj G).1
      subst m
      exact A p e q P

theorem pre_append (i : Fin n) (x : X) (u v : List (Fin n))
    (A : PreIssue hp i x u) (B0 : PreIssue hp i (run x u) v) :
    PreIssue hp i x (u++v) :=
  append_mark hp (fun y : X => pc y i≠2 ∧ (Issue (y i).long ∨ pc y i≠411)) x u v A B0

theorem release_append (i : Fin n) (x : X) (u v : List (Fin n))
    (A : ReleaseFree hp i x u) (B0 : ReleaseFree hp i (run x u) v) :
    ReleaseFree hp i x (u++v) :=
  append_mark hp (fun y : X => pc y i≠2) x u v A B0

theorem pre_safe (i : Fin n) (x : X) (w : List (Fin n))
    (H : SafePC hp i x w) : PreIssue hp i x w := by
  intro p e t E
  exact ⟨(H p e t E).1,.inr (H p e t E).2⟩

theorem pre_band (i : Fin n) (x : X) (w : List (Fin n))
    (H : PreBand hp x i w) : PreIssue hp i x w := by
  intro p e t E
  have K := (H p (e::t) E).2
  exact ⟨by
    change 408≤pc (run x p) i ∧ pc (run x p) i≤410 at K
    omega,
    .inr (by change 408≤pc (run x p) i ∧ pc (run x p) i≤410 at K; omega)⟩

theorem pre_single (i : Fin n) (x : X) (e : Fin n)
    (H : pc x i≠2 ∧ (Issue (x i).long ∨ pc x i≠411)) :
    PreIssue hp i x [e] := by
  intro p d t E
  cases p with
  | nil => exact H
  | cons a p =>
    exfalso
    have L := congrArg List.length E
    simp only [List.length_cons,List.length_append,List.length_nil] at L
    omega

theorem pre_ready {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w : List (Fin n)} {b : Mode}
    (T : GeneratedOwner hp base addr len x .idle w b)
    (band : TailBand hp x (addr 0).1 w)
    (foreign : ∀ e∈w,rightNeighbor e≠(addr 0).1) :
    PreIssue hp (addr 0).1 x w := by
  intro p e t E
  have C := idle_foreign_prefix hp T foreign p (e::t) E
  have P := (band p (e::t) E).2.1
  change 408≤pc (run x p) (addr 0).1 at P
  exact ⟨by omega,.inl C.1⟩

/-- From the actual winning ACQUIRE mark to the old ISSUE411:
PC 5 through the successful ACK, the computed 6..408 suffix, then
408..410 through bank selection, and only ready-411 holds. -/
theorem prelude {base x : X} {addr : Nat → Pos n} {len : Nat}
    (beforeAck al ar hold : List (Fin n)) (ack pick : Fin n)
    (fromBirth : SafePC hp (addr 0).1 x beforeAck)
    (oldAck : pc (run x beforeAck) (addr 0).1=5)
    (middle : BStarGeneratedBandScan.LiveWord hp (addr 0).1 (step (run x beforeAck) ack) al)
    (pre : PreBand hp (run (step (run x beforeAck) ack) al) (addr 0).1 ar)
    (T : GeneratedOwner hp base addr len (step (run (run (step (run x beforeAck) ack) al) ar) pick)
      .idle hold .idle)
    (band : TailBand hp (step (run (run (step (run x beforeAck) ack) al) ar) pick) (addr 0).1 hold)
    (foreign : ∀ e∈hold,rightNeighbor e≠(addr 0).1) :
    PreIssue hp (addr 0).1 x (beforeAck++ack::(al++(ar++pick::hold))) := by
  refine pre_append hp _ _ beforeAck _ (pre_safe hp _ _ _ fromBirth) ?_
  change PreIssue hp _ _ ([ack]++(al++(ar++pick::hold)))
  refine pre_append hp _ _ [ack] _ (pre_single hp _ _ ack ?_) ?_
  · rw [oldAck]
    exact ⟨by decide,.inr (by decide)⟩
  change PreIssue hp _ (step (run x beforeAck) ack) (al++(ar++pick::hold))
  refine pre_append hp _ _ al _ (pre_safe hp _ _ _ (safe_band hp _ _ _ middle)) ?_
  refine pre_append hp _ _ ar _ (pre_band hp _ _ _ pre) ?_
  change PreIssue hp _ _ ([pick]++hold)
  refine pre_append hp _ _ [pick] hold (pre_single hp _ _ pick ?_) ?_
  · have P := (pre ar [] (List.append_nil _).symm).2
    change 408≤pc (run (run (step (run x beforeAck) ack) al) ar) (addr 0).1 ∧
      pc (run (run (step (run x beforeAck) ack) al) ar) (addr 0).1≤410 at P
    exact ⟨by omega,.inr (by omega)⟩
  · exact pre_ready hp T band foreign

/-- One actual attempt, beginning after a particular genuine win:
all marks before the centered publication are release-free and do
not publish at this center. The genuine idle issue itself, followed
by the in-flight 411 word, is allowed. -/
theorem safe_to_commit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (ready : Current hp base (fun j => S.getD j fall) len x .idle)
    (lead mid flight : List (Fin n)) (door i : Fin n) (j : Nat)
    (hj : j≤len) (center : S.getD j fall=(i,1))
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (pre : PreIssue hp (S.getD 0 fall).1 (run x lead) mid)
    (launch : Launch (run x (lead++mid) (S.getD 0 fall).1).long
      (step (run x (lead++mid)) door (S.getD 0 fall).1).long)
    (op : pc (run x (lead++mid)) (S.getD 0 fall).1=411)
    (F : BusyOnly hp base (fun k => S.getD k fall) len commitOp
      (step (run x (lead++mid)) door) (.out 0) flight (.out j)) :
    ReleaseFree hp (S.getD 0 fall).1 (run x lead) (mid++door::flight) ∧
    BeforePublication hp (run x lead) i (mid++door::flight) := by
  have P : run (run x lead) mid=run x (lead++mid) :=
    (BStarResetSchedule.run_append step x lead mid).symm
  have cleanMid : BeforePublication hp (run x lead) i mid := by
    intro u e v E
    have H := (pre u e v E).2
    have R := BStarResetSchedule.run_append step x lead u
    rw [←R] at H ⊢
    exact no_pub_from_issue_or_pc hp C Q I fiber closed sep ready _ i e own H
  have cleanDoor : NoPublication hp (run x (lead++mid)) door i :=
    no_pub_from_issue_or_pc hp C Q I fiber closed sep ready _ i door own (.inl launch.1)
  have cleanEnd : BeforePublication hp (step (run x (lead++mid)) door) i flight :=
    BStarCommitNoPrior.before_center hp F sep i j hj center j rfl (Nat.le_refl _)
  have pcClean : ReleaseFree hp (S.getD 0 fall).1 (step (run x (lead++mid)) door) flight := by
    intro u e v E
    have H := busy_prefix_pc hp F u (e::v) E
    change pc (run (step (run x (lead++mid)) door) u) (S.getD 0 fall).1=411 at H
    rw [H]; decide
  constructor
  · apply release_append hp _ _ mid (door::flight) (fun u e v E => (pre u e v E).1)
    rw [P]
    apply release_append hp _ _ [door] flight
    · intro u e v E
      exact (pre_single hp _ _ _ ⟨op ▸ (by decide : 411≠2),.inl launch.1⟩ u e v E).1
    · exact pcClean
  · refine before_append hp i _ mid (door::flight) cleanMid ?_
    rw [P]
    exact before_append hp i _ [door] flight (before_single hp _ i door cleanDoor) cleanEnd

#print axioms pre_ready
#print axioms prelude
#print axioms safe_to_commit
end L4.BStarAttemptSafety

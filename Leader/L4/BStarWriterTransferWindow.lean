import Leader.L4.BStarWriterOwnerInterval
import Leader.L4.BStarGeneratedBandScan

namespace L4.BStarWriterTransferWindow
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarResetSchedule BStarGeneratedOwner BStarOwnerLaunchOrigin BStarLongDoor BStarLongCommand
open BStarGrantBirth BStarGrantWriterHistory BStarCaptureInterval
open BStarGeneratedBandScan BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A prefix of an uninterrupted actual tour still has the same
physical WAIT opcode. -/
theorem busy_prefix_pc {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x z w d) :
    ∀ pre tail, w=pre++tail → pc (run x pre) (addr 0).1=op := by
  intro pre
  induction pre generalizing x z w with
  | nil =>
    intro tail E
    exact (busy_start hp P).1.2.2.2
  | cons e pre ih =>
    intro tail E
    rw [E] at P
    cases P with
    | cons J M K =>
      exact ih K _ rfl

def SafePC (i : Fin n) (x : X) (w : List (Fin n)) : Prop :=
  ∀ pre e tail, w=pre++e::tail → pc (run x pre) i≠2 ∧ pc (run x pre) i≠411

theorem safe_append (i : Fin n) (x : X) (u v : List (Fin n))
    (H : SafePC hp i x u) (K : SafePC hp i (run x u) v) :
    SafePC hp i x (u++v) := by
  intro pre e tail E
  rcases List.append_eq_append_iff.mp E with ⟨q,P,Q⟩|⟨q,P,Q⟩
  · rw [P,BStarResetSchedule.run_append]
    exact K q e tail Q
  · cases q with
    | nil =>
      simp only [List.append_nil] at P
      rw [←P]
      exact K [] e tail Q.symm
    | cons m q =>
      have Q' : e::tail=m::(q++v) := Q
      have equality := (List.cons.inj Q').1
      subst m
      exact H pre e q P

theorem safe_busy {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x z w d) (A : op≠2) (B0 : op≠411) :
    SafePC hp (addr 0).1 x w := by
  intro pre e tail E
  rw [busy_prefix_pc hp P pre (e::tail) E]
  exact ⟨A,B0⟩

theorem safe_band (i : Fin n) (x : X) (w : List (Fin n))
    (L : LiveWord hp i x w) : SafePC hp i x w := by
  intro pre e tail E
  have ⟨low,high⟩ := (L pre e tail E).1
  exact ⟨by omega,by omega⟩

theorem safe_single (i : Fin n) (x : X) (e : Fin n)
    (H : pc x i≠2 ∧ pc x i≠411) : SafePC hp i x [e] := by
  intro pre a tail E
  cases pre with
  | nil => exact H
  | cons p pre =>
    have H := congrArg List.length E
    simp only [List.length_cons,List.length_append,List.length_nil] at H
    omega

/-- A writer's actual sampled bank remains selected across a tape
that excludes its RELEASE and COMMIT opcodes. The generated
controller histories at each intermediate mark follow from the
clean start; the grant is not assumed continuously present. -/
theorem follows_safe_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (origin : Current hp base (fun j => S.getD j fall) len x .idle)
    (lead : List (Fin n)) (birth i : Fin n) (w : List (Fin n))
    (owned : commandOwner (oldH6 B base) i 1=o.val)
    (hdr : oldH6 B base i=true)
    (won : WonAt hp (run x lead) birth i 1)
    (safe : SafePC hp (S.getD 0 fall).1 (step (run x lead) birth) w) :
    let z := run x lead
    let y := step z birth
    BeforePublication hp y i w ∧ Continuous hp y i 1 w ∧
      (BStarLongPublication.readSel ((run y w) i).long=BStarLongPublication.readSel (z i).long) := by
  dsimp only
  have A := BStarWriterOwnerInterval.owned_interval hp C sep lead birth i w owned won
    (fun u e v E => by
      let tape := lead++birth::u
      obtain ⟨m,P,J,G⟩ := generated_word hp C Q fiber (fun y h e => closed y e h)
        sep tape .idle I origin
      have W : run x tape=run (step (run x lead) birth) u := by
        rw [show tape=lead++birth::u from rfl,BStarResetSchedule.run_append]
        rfl
      have F := safe u e v E
      have H6 : oldH6 B (run x tape) i=true := by
        have H := congrArg Prod.fst (fiber _ J i)
        exact H.symm.trans hdr
      refine ⟨m,P,G,?_,?_,H6⟩
      · change pc (run x tape) (S.getD 0 fall).1≠2
        rw [W]
        exact F.1
      · change pc (run x tape) (S.getD 0 fall).1≠411
        rw [W]
        exact F.2)
  exact ⟨A.1,A.2.1,(A.2.2 w [] (by simp)).1⟩

/-- Join the exact interval shapes between the center win and an old
body STAGE. An awake writer cannot release or publish during the
remaining ACQUIRE tour, its consume, normal computation, or the
single interrupted/parked STAGE tour. -/
theorem safe_through_stage {base x : X}
    {addr : Nat → Pos n} {len : Nat}
    (wA : List (Fin n)) (accept : Fin n) (mid : List (Fin n)) (issue : Fin n)
    (suffix : List (Fin n)) (out : Cursor)
    (safeA : SafePC hp (addr 0).1 x wA)
    (atAccept : pc (run x wA) (addr 0).1=acquire)
    (live : LiveWord hp (addr 0).1 (step (run x wA) accept) mid)
    (atIssue : pc (run (step (run x wA) accept) mid) (addr 0).1=stageOp)
    (inFlight : BusyOnly hp base addr len stageOp
      (step (run (step (run x wA) accept) mid) issue) (.out 0) suffix out) :
    SafePC hp (addr 0).1 x (wA++(accept::(mid++(issue::suffix)))) := by
  refine safe_append hp _ _ wA _ safeA ?_
  change SafePC hp (addr 0).1 (run x wA) ([accept]++(mid++issue::suffix))
  refine safe_append hp _ _ [accept] _ ?_ ?_
  · apply safe_single
    rw [atAccept]
    exact ⟨by decide,by decide⟩
  change SafePC hp (addr 0).1 (step (run x wA) accept) (mid++issue::suffix)
  refine safe_append hp _ _ mid _ (safe_band hp _ _ _ live) ?_
  change SafePC hp (addr 0).1 (run (step (run x wA) accept) mid) ([issue]++suffix)
  refine safe_append hp _ _ [issue] _ ?_ ?_
  · apply safe_single
    rw [atIssue]
    exact ⟨by decide,by decide⟩
  · exact safe_busy hp inFlight (by decide) (by decide)

end L4.BStarWriterTransferWindow

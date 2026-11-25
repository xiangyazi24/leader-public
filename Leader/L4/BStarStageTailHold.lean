import Leader.L4.BStarStagePast
import Leader.L4.BStarAttemptSafety

namespace L4.BStarStageTailHold
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarLongFixedRouting BStarLongFiberOwner
open BStarLongCommand BStarLongDoor BStarClearanceSource BStarOwnerLaunchOrigin
open BStarGeneratedTapeCuts BStarCommitTailScan BStarCommitGeneratedTail
open BStarStageCandidateRetention BStarStagePast BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

private theorem foreign_pc (x : X) (i e : Fin n)
    (h : oldH6 B x i=true) (ne : rightNeighbor e≠i) :
    pc (step x e) i=pc x i := by
  by_cases E : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have h' : (oldHeaders B pair.1).h6=true := h
    have t := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair h'
    unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_true]
    exact congrArg (fun y : BitVec 2 × BitVec 9 => y.2.toNat) t
  · unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm ne)]

open BStarGeneratedPCAncestry BStarStageSourceFrame BStarResetControllerEntry

private theorem bad_issue_pc {x : X} {addr : Nat → Pos n} {e : Fin n}
    (h : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e) (I : BStarClearanceSource.Issue (x (addr 0).1).long)
    (E : e=RearTrace.predecessor (addr 0).1)
    (bad : initial (pc x (addr 0).1) (x (addr 0).1).long=none) :
    pc (step x e) (addr 0).1=0 := by
  have R : rightNeighbor e=(addr 0).1 := E ▸ RearTrace.right_predecessor _
  let pair := (x e,x (rightNeighbor e))
  have hdr : (oldHeaders B pair.2).h6=true := by change oldH6 B x (rightNeighbor e)=true; rwa [R]
  have valid : LongDoorGuard.valid manifest pair.2.long=true := by
    change LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true
    rw [R]; exact I.1
  have phase : (ctrlPhase.read pair.2.long).toNat=1 := by
    change (ctrlPhase.read (x (rightNeighbor e)).long).toNat=1
    rw [R]; exact I.2
  have A := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair hdr valid phase
  have bad' : initial (ctrlOp.read pair.2.long).toNat pair.2.long=none := by
    change initial (pc x (rightNeighbor e)) (x (rightNeighbor e)).long=none
    rwa [R]
  rw [bad'] at A
  have eq : step x e (addr 0).1=(largePair B pair).2 := by
    rw [←R]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  exact congrArg (fun t : _ × BitVec 9 => t.2.toNat) (eq ▸ A)

private theorem consume_not_408 {x base : X} {addr : Nat → Pos n}
    {e : Fin n} {len op : Nat} (K : (addr 0).2=0) (h : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e) (lo : 408≤pc x (addr 0).1)
    (I : Current hp base addr len x (.busy op (.back 0)))
    (E : Event hp addr len x e (.busy op (.back 0)) .idle) :
    pc (step x e) (addr 0).1≠408 := by
  intro bad
  obtain ⟨A,_,_⟩ := consume_to_stage hp K h sep I E bad
  have P : pc x (addr 0).1=op := I.1.2.2.2
  omega

/-- All post-STAGE-ACK old prefixes of the actual 409/410 band
remain above 408. No new physical old-PC premise per mark is needed. -/
theorem before_choice_ge409 {base x : X} {addr : Nat → Pos n} {len : Nat} {a b : Mode}
    {w : List (Fin n)} (T : GeneratedOwner hp base addr len x a w b)
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (band : PreBand hp x (addr 0).1 w) (start : 409≤pc x (addr 0).1) :
    ∀ u v,w=u++v → 409≤pc (run x u) (addr 0).1 := by
  induction T with
  | endpoint I =>
    intro u v E
    cases u <;> (try contradiction)
    exact start
  | @next x a e w b dest I E T ih =>
    intro u v split
    cases u with
    | nil => exact start
    | cons m u =>
      obtain ⟨J,W⟩ := List.cons.inj split
      subst m
      have H := (band [] (e::w) rfl).1
      have L := (band [e] w rfl).2.1
      change 408≤pc (step x e) (addr 0).1 at L
      have next : 409≤pc (step x e) (addr 0).1 := by
        have other (Q : e≠RearTrace.predecessor (addr 0).1) :
            409≤pc (step x e) (addr 0).1 := by
          have A : rightNeighbor e≠(addr 0).1 := fun Qeq =>
            Q ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor Qeq))
          rw [foreign_pc hp x (addr 0).1 e H A]
          exact start
        have new := at_start hp T
        cases E with
        | idle_hold away => exact other away
        | bad_issue own bad =>
          have P := bad_issue_pc hp H (sep e) I.1 own bad
          exact False.elim ((by decide : ¬ (408:Nat)≤0) (P ▸ L))
        | launch _ L =>
          have Q : pc (step x e) (addr 0).1=pc x (addr 0).1 :=
            congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2
          exact Q.symm ▸ start
        | transit op z d live S =>
          have Q : pc (step x e) (addr 0).1=pc x (addr 0).1 :=
            new.1.2.2.2.trans I.1.2.2.2.symm
          exact Q.symm ▸ start
        | arrived_hold _ away => exact other away
        | consume op own empty =>
          have P := consume_not_408 hp K H (sep e) (Nat.le_trans (by decide : 408≤409) start) I (Event.consume op own empty)
          exact Nat.lt_of_le_of_ne L (Ne.symm P)
      exact ih (fun p q J => band (e::p) q (congrArg (List.cons e) J)) next u v W

private theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (run x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

/-- Same post-ACK generated tape: the bank survives all old
409/410 marks, not just its net write at the end of the stage. -/
theorem holds_after_ack_band {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w : List (Fin n)) (old : x=run origin lead)
    {u d : Mode}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle lead u)
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x u w d)
    (K : (S.getD 0 fall).2=0)
    (band : PreBand hp x (S.getD 0 fall).1 w) (start : 409≤pc x (S.getD 0 fall).1)
    (i : Fin n) (b : Fin 3) (own : commandOwner (oldH6 B base) i 1=o.val) :
    BankAt b (run x w i).long=BankAt b (x i).long := by
  have above := before_choice_ge409 hp T K sep band start
  subst x
  have H := word_keeps_owned hp C sep lead w i b own (by
    intro a e c E
    have A := above a (e::c) E
    have E' := BStarResetSchedule.run_append step origin lead a
    obtain ⟨m,P,_⟩ := split hp a (e::c) (E ▸ T)
    let F := generated_append hp G P
    refine ⟨m,F,at_end hp F,?_⟩
    let J := at_end hp F
    intro z eq
    subst m
    have J' : pc (run origin (lead++a)) (S.getD 0 fall).1=408 := J.1.2.2.2
    exact (by rw [←E',J'] at A; exact (by decide : ¬ (409:Nat)≤408) A))
  rwa [BStarResetSchedule.run_append] at H

theorem ready411_pc {x : X} (i : Fin n) (w : List (Fin n))
    (start : pc x i=411) (band : TailBand hp x i w)
    (foreign : ∀ e∈w,rightNeighbor e≠i) :
    ∀ u v,w=u++v → pc (run x u) i=411 := by
  intro u
  induction u generalizing x w with
  | nil => intro _ _; exact start
  | cons e u ih =>
    intro v E
    subst w
    have H := (band [] (e::(u++v)) rfl).1
    have next := (foreign_pc hp x i e H (foreign e List.mem_cons_self)).trans start
    exact ih (u++v) next (fun a b W => band (e::a) b (congrArg (List.cons e) W))
      (fun a A => foreign a (List.mem_cons_of_mem _ A)) v rfl

/-- A helper accepting an actual generated segment and exact pointwise
source PC evidence at its old prefixes. It is used for ready411 holds,
issue, travel and the final publication as well as the 409/410 band. -/
theorem holds_with_pc {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w : List (Fin n)) (old : x=run origin lead)
    {u d : Mode}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle lead u)
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x u w d)
    (safe : ∀ a e c,w=a++e::c → pc (run x a) (S.getD 0 fall).1≠408)
    (i : Fin n) (b : Fin 3) (own : commandOwner (oldH6 B base) i 1=o.val) :
    BankAt b (run x w i).long=BankAt b (x i).long := by
  subst x
  have H := word_keeps_owned hp C sep lead w i b own (by
    intro a e c E
    have A := safe a e c E
    have E' := BStarResetSchedule.run_append step origin lead a
    obtain ⟨m,P,_⟩ := split hp a (e::c) (E ▸ T)
    let F := generated_append hp G P
    refine ⟨m,F,at_end hp F,?_⟩
    let J := at_end hp F
    intro z eq
    subst m
    exact A (E'.symm ▸ (show pc (run origin (lead++a)) (S.getD 0 fall).1=408 from J.1.2.2.2)))
  rwa [BStarResetSchedule.run_append] at H

private theorem busy_word {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)} (P : BusyOnly hp base addr len op x z w d) :
    GeneratedOwner hp base addr len x (.busy op z) w (.busy op d) := by
  induction P with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

/-- Real COMMIT flight and its actual terminal physical mark preserve
all candidate bytes at every covered K1 of this owner. The last mark
may publish and change the selector, unlike a protected-operand frame. -/
theorem commit_flight_keeps {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w : List (Fin n)) (old : x=run origin lead)
    {z d : Cursor}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle lead (.busy commitOp z))
    (T : BusyOnly hp base (fun j => S.getD j fall) len commitOp x z w d)
    (mark i : Fin n) (b : Fin 3) (own : commandOwner (oldH6 B base) i 1=o.val) :
    BankAt b (step (run x w) mark i).long=BankAt b (x i).long := by
  have K := holds_with_pc hp C sep lead w old G (busy_word hp T)
    (fun u e v W => (fun bad => (by decide : commitOp≠408) ((BStarWriterTransferWindow.busy_prefix_pc hp T u (e::v) W).symm.trans bad)))
    i b own
  have tape : run origin (lead++w)=run x w := by rw [BStarResetSchedule.run_append,old]
  have WG : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle
      (lead++w) (.busy commitOp d) := generated_append hp G (old ▸ busy_word hp T)
  have noStage : RingNoStage hp (run origin (lead++w)) mark i :=
    excludes_stage hp C sep WG (at_end hp WG) mark i own (fun _ E => by
      have I := (Mode.busy.inj E).1
      contradiction)
  exact (ring_keeps hp (run x w) mark i (sep mark) b (tape ▸ noStage)).trans K

#print axioms holds_with_pc
#print axioms commit_flight_keeps
#print axioms before_choice_ge409
#print axioms holds_after_ack_band
end L4.BStarStageTailHold

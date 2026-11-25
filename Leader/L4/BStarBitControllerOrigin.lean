import Leader.L4.BStarNeedPrefixFresh
import Leader.L4.BStarCommitTailScan

namespace L4.BStarBitControllerOrigin
set_option maxHeartbeats 850000
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarResetChartService BStarClearanceSource
open BStarResetControllerEntry BStarCommitTailScan BStarCommitGeneratedTail BStarLiteralPC
open BStarResetControllerProgress BStarFirstDoorService BStarCommitIssue

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem bad_issue_zero {x : X} {addr : Nat → Pos n} {e : Fin n}
    (h : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e) (I : Issue (x (addr 0).1).long)
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

/-- A genuine controller entrance to ISSUE410 is exactly a healthy
matched 409 consume with NEED and positive low bit. The old/new
controller event is on the supplied literal mark, not a chosen replay. -/
theorem enters_bit {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {a b : Mode} (K : (addr 0).2=0) (h : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a)
    (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b)
    (old : pc x (addr 0).1≠bitOp) (new : pc (step x e) (addr 0).1=bitOp) :
    a=.busy sealOp (.back 0) ∧ b=.idle ∧
      ∃ d : Desc, ∃ f : Payload,
        bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f ∧
        f.fault=0 ∧ f.opcode.toNat=sealOp ∧ f.argument.toNat%2=1 ∧ d.need=true ∧
        BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some d := by
  have away (A : e≠RearTrace.predecessor (addr 0).1) : False := by
    have F : rightNeighbor e≠(addr 0).1 := by
      intro R
      exact A ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor R))
    have Q := BStarSealAckLegal.away_controller hp x (addr 0).1 [e]
      (fun f M=>by have E := List.mem_singleton.mp M; subst f; exact F)
      (by intro u f v W; cases u with
        | nil => exact h
        | cons a u =>
          have R := (List.cons.inj W).2
          simp at R)
    have same : pc (step x e) (addr 0).1=pc x (addr 0).1 :=
      congrArg (fun t : _ × BitVec 9 => t.2.toNat) Q
    exact old (same.symm.trans new)
  cases E with
  | idle_hold off => exact (away off).elim
  | bad_issue own bad =>
    have Z := bad_issue_zero hp h sep I.1 own bad
    exact ((by decide : (0:Nat)≠bitOp) (Z.symm.trans new)).elim
  | launch _ L =>
    have same : pc (step x e) (addr 0).1=pc x (addr 0).1 :=
      congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2
    exact (old (same.symm.trans new)).elim
  | transit _ _ _ _ _ =>
    exact (old ((J.1.2.2.2.trans I.1.2.2.2.symm).symm.trans new)).elim
  | arrived_hold _ off => exact (away off).elim
  | consume op own clear =>
    have S := consume_tail hp K h sep I (.consume op own clear) (.inr (.inl new))
    obtain ⟨_,f,R,F,Op,pcNow,_,E',_⟩ := S
    have op' : op=sealOp := E' new
    have wire : f.opcode.toNat=sealOp := Op.trans op'
    let raw : BitVec LW := (x (addr 0).1).long
    have finish : pcNext raw f=bitOp := pcNow.symm.trans new
    have oldPC : (ctrlOp.read raw).toNat=sealOp := I.1.2.2.2.trans op'
    cases Hd : BStarLongPublication.decode (sourceDescriptor.read raw) with
    | none =>
      have node : (arithKind 409).isSome=false := by decide
      have Z : pcNext raw f=0 := by simp [pcNext,oldPC,F,wire,node,nextOrdinary,Hd,sealOp]
      exact ((by decide : (0:Nat)≠bitOp) (Z.symm.trans finish)).elim
    | some d =>
      have calcPC := seal_pc raw f d oldPC F wire Hd
      rw [calcPC] at finish
      have positive : f.argument.toNat%2=1 ∧ d.need=true := by
        cases H : d.need <;> by_cases L : f.argument.toNat%2=1 <;> simp [H,L,bitOp] at finish ⊢
      exact ⟨congrArg (fun op=>Mode.busy op (.back 0)) op',rfl,d,f,R,F,wire,positive.1,positive.2,rfl⟩

private theorem last_crossing {x : X} (P : X→Prop) (w : List (Fin n))
    (old : ¬P x) (last : P (play x w)) :
    ∃ pre e tail,w=pre++e::tail ∧ ¬P (play x pre) ∧
      ∀ u v,tail=u++v → P (play (step (play x pre) e) u) := by
  classical
  have scan (rev : List (Fin n)) : P (play x rev.reverse) →
      ∃ pre e tail,rev.reverse=pre++e::tail ∧ ¬P (play x pre) ∧
        ∀ u v,tail=u++v → P (play (step (play x pre) e) u) := by
    induction rev with
    | nil =>
      intro hit
      exact (old hit).elim
    | cons e u ih =>
      rw [List.reverse_cons]
      intro hit
      let w := u.reverse
      by_cases p : P (play x w)
      · obtain ⟨pre,a,tail,W,N,H⟩ := ih p
        have full : w++[e]=pre++a::(tail++[e]) := by
          rw [show w=pre++a::tail from W,List.append_assoc,List.cons_append]
        refine ⟨pre,a,tail++[e],full,N,?_⟩
        intro u v S
        have A : u<+:tail++[e] := ⟨v,S.symm⟩
        by_cases L : u.length≤tail.length
        · obtain ⟨q,E⟩ := List.prefix_of_prefix_length_le A ⟨[e],rfl⟩ L
          exact H u q E.symm
        · have E : u=tail++[e] := A.eq_of_length_le (by simp; omega)
          rw [E]
          have place : play x (w++[e])=play (step (play x pre) a) (tail++[e]) := by
            rw [full,BStarResetSchedule.run_append]; rfl
          exact place ▸ hit
      · refine ⟨w,e,[],by simp [w],p,?_⟩
        intro a b split
        obtain ⟨rfl,_⟩ := List.append_eq_nil_iff.mp split.symm
        have eq : play x (w++[e])=step (play x w) e := by
          rw [BStarResetSchedule.run_append]; rfl
        exact eq ▸ hit
  simpa only [List.reverse_reverse] using scan w.reverse (by simpa only [List.reverse_reverse] using last)

/-- Find the last stable entrance to the BIT controller on the same
post-reset generated tape. An unrelated earlier 409 is not used:
the suffix stays at 410 before the observed read. -/
theorem last_entry_to_bit {base x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ j,Layout B base j=Layout B x j)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) {m : Mode} (w : List (Fin n))
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (old : pc x (S.getD 0 fall).1≠bitOp)
    (last : pc (play x w) (S.getD 0 fall).1=bitOp) :
    ∃ (pre : List (Fin n)) (e : Fin n) (tail : List (Fin n)) (d : Desc) (f : Payload), w=pre++e::tail ∧
      let y := play x pre
      let root := (S.getD 0 fall).1
      GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle pre (.busy sealOp (.back 0)) ∧
      Current hp base (fun j=>S.getD j fall) len y (.busy sealOp (.back 0)) ∧
      Event hp (fun j=>S.getD j fall) len y e (.busy sealOp (.back 0)) .idle ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len (step y e) .idle tail m ∧
      (∀ u v,tail=u++v → pc (play (step y e) u) root=bitOp) ∧
      bind (longGeometry B (y root)) 0 (atSite (y root).long 0)=.reply f ∧
      f.fault=0 ∧ f.opcode.toNat=sealOp ∧ f.argument.toNat%2=1 ∧ d.need=true ∧
      BStarLongPublication.decode (sourceDescriptor.read (y root).long)=some d := by
  obtain ⟨p,e,tail,split,ne,stay⟩ := last_crossing hp (fun y=>pc y (S.getD 0 fall).1=bitOp) w old last
  have cut : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle (p++e::tail) m := split ▸ T
  obtain ⟨a,lead,after⟩ := BStarGeneratedTapeCuts.split hp p (e::tail) cut
  cases after with
  | next I E R =>
    have h := root_header hp C (fiber _ (stable_word hp Q closed x p qx))
    have enter : pc (step (play x p) e) (S.getD 0 fall).1=bitOp := stay [] tail rfl
    have endReady := BStarGeneratedTapeCuts.at_start hp R
    have entry := enters_bit hp (base:=base) (x:=play x p) (addr:=fun j=>S.getD j fall)
      (len:=len) (e:=e) h.2 h.1 (sep e) I endReady E ne enter
    obtain ⟨M,N,Desc,reply,W,F,O,Bi,need,oldDesc⟩ := entry
    cases M
    cases N
    exact ⟨p,e,tail,Desc,reply,split,lead,I,E,R,stay,W,F,O,Bi,need,oldDesc⟩

end L4.BStarBitControllerOrigin

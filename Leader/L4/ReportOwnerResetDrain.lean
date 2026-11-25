import Leader.L4.ReportResetRawHooks
import Leader.L4.ReportJoinedGrants
import Leader.L4.ReportCacheAllSites
import Leader.L4.ReportResetEventClock
import Leader.L4.ShortOwnerEpochJS
import Leader.L4.ShortResetReleased

namespace L4.ReportOwnerResetDrain
open AllSizeProtocol PhysicalCustody ReportByteRows ReportRawProjection
open ReportResetRawHooks ReportResetBarrier ShortResetCycle ShortResetChart

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

variable {s n : Nat} {h : Fin n→Bool}

def Cached (sheet : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (x : Raw s n) : Prop :=
  match sheet with
  | .first => ReportCacheAllSites.Report1Correct h hh Q x
  | .second => ReportCacheAllSites.Report2Correct h hh Q x

structure Fibre (sheet : Sheet) (Q : Raw s n→Prop) : Prop where
  closed : ∀ x e,Q x→Q (rawNext s x e)
  mask : ∀ x,Q x→∀ i,lower sheet (oldHeaders (rows s) (x i))=h i

-- CHECK: ReportCacheAllSites.lean:156–175 (report1_raw/report2_raw).
theorem cached_fibre (sheet : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (Q : Raw s n→Prop)
    (F : Fibre (h:=h) sheet Q) :
    Fibre (h:=h) sheet (Cached sheet hh Q) := by
  cases sheet with
  | first =>
    constructor
    · intro x e A
      exact (ReportCacheAllSites.report1_raw N h hh Q F.closed F.mask
        x A.1).1 x e A
    · intro x A i
      exact F.mask x A.1 i
  | second =>
    constructor
    · intro x e A
      exact (ReportCacheAllSites.report2_raw N h hh Q F.closed F.mask
        x A.1).1 x e A
    · intro x A i
      exact F.mask x A.1 i

/-- Exactly the four canonical wires, not a tag-only approximation.
    The .other letter is deliberately unconstrained in the F0 suffix. -/
def tokCode : Letter→Tok
  | .empty => MISByteCodec.E
  | .trail => MISByteCodec.T
  | .forward0 => reset0Forward
  | .reply0 => reset0Reply
  | .other => MISByteCodec.E

def canon (p : Params) (a : Letter) : BitVec (tokenW p) :=
  resetTokenWire p (tokCode a)

theorem canon_decode (p : Params) (g : Bool) (a : Letter)
    (A : a≠.other) : ReportByteRows.decode p g (canon p a)=tokCode a := by
  cases a with
  | empty => exact drain_decode_E p g
  | trail => exact drain_decode_T p g
  | forward0 => exact reset0_decode_forward p g
  | reply0 => exact reset0_decode_reply p g
  | other => exact False.elim (A rfl)

private theorem canon_ne (p : Params) (a b : Letter)
    (A : a≠.other) (B : b≠.other) (H : a≠b) :
    canon p a≠canon p b := by
  intro E
  have R := congrArg (ReportByteRows.decode p false) E
  rw [canon_decode p false a A,canon_decode p false b B] at R
  have T := congrArg MISByteCodec.Token.tag R
  cases a <;> cases b <;>
    simp_all [tokCode,MISByteCodec.E,MISByteCodec.T,reset0Forward,reset0Reply]

def letterOf (p : Params) (w : BitVec (tokenW p)) : Letter :=
  if w=canon p .empty then .empty
  else if w=canon p .trail then .trail
  else if w=canon p .forward0 then .forward0
  else if w=canon p .reply0 then .reply0 else .other

private theorem view_sound (p : Params) (w : BitVec (tokenW p))
    (a : Letter) (N : a≠.other) (A : letterOf p w=a) :
    w=canon p a := by
  unfold letterOf at A
  split at A
  · rename_i H
    subst a
    exact H
  · split at A
    · rename_i H
      subst a
      exact H
    · split at A
      · rename_i H
        subst a
        exact H
      · split at A
        · rename_i H
          subst a
          exact H
        · exact False.elim (N A.symm)

private theorem view_complete (p : Params) (a : Letter) (N : a≠.other) :
    letterOf p (canon p a)=a := by
  cases a with
  | empty => simp [letterOf]
  | trail =>
    have A := canon_ne p .trail .empty (by decide) (by decide) (by decide)
    simp [letterOf,A]
  | forward0 =>
    have A := canon_ne p .forward0 .empty (by decide) (by decide) (by decide)
    have B := canon_ne p .forward0 .trail (by decide) (by decide) (by decide)
    simp [letterOf,A,B]
  | reply0 =>
    have A := canon_ne p .reply0 .empty (by decide) (by decide) (by decide)
    have B := canon_ne p .reply0 .trail (by decide) (by decide) (by decide)
    have D := canon_ne p .reply0 .forward0 (by decide) (by decide) (by decide)
    simp [letterOf,A,B,D]
  | other => exact False.elim (N rfl)

def slot (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) : Letter :=
  letterOf (params sheet s) (wire sheet C x i)

def tok (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) : Tok :=
  publicationToken (params sheet s) (h (out C i))
    (selectBytes sheet (x (out C i))) (C.route.port i)

theorem slot_wire (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) (a : Letter) (N : a≠.other) (A : slot sheet C x i=a) :
    wire sheet C x i=canon (params sheet s) a :=
  view_sound _ _ a N A

theorem slot_of_wire (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) (a : Letter) (N : a≠.other)
    (W : wire sheet C x i=canon (params sheet s) a) :
    slot sheet C x i=a := by
  unfold slot
  rw [W]
  exact view_complete _ a N

theorem tok_of_slot (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) (a : Letter) (N : a≠.other) (A : slot sheet C x i=a) :
    tok sheet C x i=tokCode a :=
  drain_read_token _ _ _ _ _ (fun g=>canon_decode _ g a N)
    (slot_wire sheet C x i a N A)

private theorem wire_zero (sheet : Sheet) (C : Chart h) (x : Raw s n) :
    wire sheet C x 0=resetTokenRead (params sheet s)
      (selectBytes sheet (x C.root)) 0 := by
  change resetTokenRead (params sheet s) (selectBytes sheet (x C.root))
    (ShortResetChart.lane C.a C.b 0)=_
  rw [C.rootPort]

private theorem tok_zero (sheet : Sheet) (C : Chart h) (x : Raw s n) :
    tok sheet C x 0=publicationToken (params sheet s) true
      (selectBytes sheet (x C.root)) 0 := by
  change publicationToken (params sheet s) (h C.root)
    (selectBytes sheet (x C.root)) (ShortResetChart.lane C.a C.b 0)=_
  rw [C.rootHeader,C.rootPort]

def pcCode : PC→Nat×Nat
  | .issue0 => (1,0)
  | .wait0 => (2,0)
  | .issue1 => (1,1)
  | .other => (0,0)

def pcView (c : Nat×Nat) : PC :=
  if c=pcCode .issue0 then .issue0
  else if c=pcCode .wait0 then .wait0
  else if c=pcCode .issue1 then .issue1 else .other

private theorem pc_sound (c : Nat×Nat) (a : PC) (N : a≠.other)
    (A : pcView c=a) : c=pcCode a := by
  unfold pcView at A
  split at A
  · rename_i H
    subst a
    exact H
  · split at A
    · rename_i H
      subst a
      exact H
    · split at A
      · rename_i H
        subst a
        exact H
      · exact False.elim (N A.symm)

private theorem pc_complete (a : PC) (N : a≠.other) :
    pcView (pcCode a)=a := by
  cases a <;> simp_all [pcView,pcCode]

def ownerPC (sheet : Sheet) (C : Chart h) (x : Raw s n) : PC :=
  pcView (controlWork (params sheet s) (selectBytes sheet (x C.root)))

theorem pc_fields (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (a : PC) (N : a≠.other) (A : ownerPC sheet C x=a) :
    controlWork (params sheet s) (selectBytes sheet (x C.root))=pcCode a :=
  pc_sound _ a N A

private theorem pc_of_fields (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (a : PC) (N : a≠.other)
    (A : controlWork (params sheet s) (selectBytes sheet (x C.root))=pcCode a) :
    ownerPC sheet C x=a := by
  unfold ownerPC
  rw [A]
  exact pc_complete a N

/-- Exact old-mask row projection for the current actual pair. -/
private theorem raw_observe (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i) :
    let p := params sheet s
    let v := rightNeighbor e
    let pair := (selectBytes sheet (x e),selectBytes sheet (x v))
    Pair.map (tokenControl p)
      (selectBytes sheet (rawNext s x e e),selectBytes sheet (rawNext s x e v)) =
      Pair.map (tokenControl p) (patchPair (row p (h e,h v) pair) pair) := by
  have R := raw_token_control sheet x e (edge_sep N e)
  dsimp only at R
  rw [mask e,mask (rightNeighbor e)] at R
  exact R

theorem raw_issue (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (I : ownerPC sheet C x=.issue0) :
    ownerPC sheet C (rawNext s x (door C))=.wait0 ∧
      slot sheet C (rawNext s x (door C)) 0=.forward0 := by
  let p := params sheet s
  let e := door C
  have R : rightNeighbor e=C.root := RearTrace.right_predecessor C.root
  have F := pc_fields sheet C x .issue0 (by decide) I
  have ph : sourcePhase p (selectBytes sheet (x C.root))=1 :=
    congrArg _root_.Prod.fst F
  have op : sourceOpcode p (selectBytes sheet (x C.root))=0 :=
    congrArg _root_.Prod.snd F
  have A := drain_row_issue p (h e) (selectBytes sheet (x e))
    (selectBytes sheet (x C.root)) ph op
  have H := raw_observe sheet x e N mask
  dsimp only at H
  rw [R,C.rootHeader] at H
  refine ⟨pc_of_fields sheet C _ .wait0 (by decide)
    ((congrArg (fun z=>z.2.2) H).trans A.1),?_⟩
  apply slot_of_wire sheet C _ 0 .forward0 (by decide)
  rw [wire_zero]
  exact (congrArg (fun z=>z.2.1 0) H).trans A.2

theorem raw_hold (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (I : ownerPC sheet C x=.wait0)
    (S : slot sheet C x 0=.trail ∨ slot sheet C x 0=.forward0) :
    ownerPC sheet C (rawNext s x (door C))=.wait0 ∧
      slot sheet C (rawNext s x (door C)) 0=slot sheet C x 0 := by
  let p := params sheet s
  let e := door C
  have R : rightNeighbor e=C.root := RearTrace.right_predecessor C.root
  have F := pc_fields sheet C x .wait0 (by decide) I
  have ph : sourcePhase p (selectBytes sheet (x C.root))=2 :=
    congrArg _root_.Prod.fst F
  have op : sourceOpcode p (selectBytes sheet (x C.root))=0 :=
    congrArg _root_.Prod.snd F
  have T : publicationToken p true (selectBytes sheet (x C.root)) 0=
      MISByteCodec.T ∨ publicationToken p true (selectBytes sheet (x C.root)) 0=
      reset0Forward := by
    rcases S with L|L
    · have K := tok_of_slot sheet C x 0 .trail (by decide) L
      rw [tok_zero] at K
      exact .inl K
    · have K := tok_of_slot sheet C x 0 .forward0 (by decide) L
      rw [tok_zero] at K
      exact .inr K
  have A := drain_row_wait_hold p (h e) (selectBytes sheet (x e))
    (selectBytes sheet (x C.root)) ph op T
  have H := raw_observe sheet x e N mask
  dsimp only at H
  rw [R,C.rootHeader] at H
  refine ⟨pc_of_fields sheet C _ .wait0 (by decide)
    ((congrArg (fun z=>z.2.2) H).trans A.1),?_⟩
  apply congrArg (letterOf p)
  rw [wire_zero,wire_zero]
  exact (congrArg (fun z=>z.2.1 0) H).trans A.2

theorem raw_consume (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (I : ownerPC sheet C x=.wait0) (S : slot sheet C x 0=.reply0) :
    ownerPC sheet C (rawNext s x (door C))=.issue1 ∧
      slot sheet C (rawNext s x (door C)) 0=.empty := by
  let p := params sheet s
  let e := door C
  have R : rightNeighbor e=C.root := RearTrace.right_predecessor C.root
  have F := pc_fields sheet C x .wait0 (by decide) I
  have ph : sourcePhase p (selectBytes sheet (x C.root))=2 :=
    congrArg _root_.Prod.fst F
  have op : sourceOpcode p (selectBytes sheet (x C.root))=0 :=
    congrArg _root_.Prod.snd F
  have T := tok_of_slot sheet C x 0 .reply0 (by decide) S
  rw [tok_zero] at T
  have A := drain_row_consume p (h e) (selectBytes sheet (x e))
    (selectBytes sheet (x C.root)) ph op T
  have H := raw_observe sheet x e N mask
  dsimp only at H
  rw [R,C.rootHeader] at H
  refine ⟨pc_of_fields sheet C _ .issue1 (by decide)
    ((congrArg (fun z=>z.2.2) H).trans A.1),?_⟩
  apply slot_of_wire sheet C _ 0 .empty (by decide)
  rw [wire_zero]
  exact (congrArg (fun z=>z.2.1 0) H).trans A.2

theorem raw_nondoor_pc (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (D : e≠door C) :
    ownerPC sheet C (rawNext s x e)=ownerPC sheet C x := by
  by_cases E : e=C.root
  · subst e
    have H := raw_observe sheet x C.root N mask
    dsimp only at H
    rw [C.rootHeader] at H
    apply congrArg pcView
    exact (congrArg (fun z=>z.1.2) H).trans
      (drain_row_left_control (params sheet s) (h (rightNeighbor C.root))
        (selectBytes sheet (x C.root)) (selectBytes sheet (x (rightNeighbor C.root))))
  · have R : C.root≠rightNeighbor e := by
      intro K
      apply D
      unfold door
      rw [K,RearTrace.predecessor_right]
    unfold ownerPC
    rw [raw_spectator x e C.root (Ne.symm E) R]

private theorem raw_idle_wire (sheet : Sheet) (C : Chart h)
    (x : Raw s n) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (j : Nat) (J : j+1<C.L)
    (H : (tok sheet C x j=MISByteCodec.T ∧
          (tok sheet C x (j+1)=MISByteCodec.T ∨
           tok sheet C x (j+1)=reset0Forward)) ∨
        ((tok sheet C x j=MISByteCodec.E ∨ tok sheet C x j=reset0Reply) ∧
          tok sheet C x (j+1)=MISByteCodec.E)) :
    wire sheet C (rawNext s x (out C j)) j=wire sheet C x j ∧
      wire sheet C (rawNext s x (out C j)) (j+1)=wire sheet C x (j+1) := by
  let e := out C j
  let r := rightNeighbor e
  have L := C.route.live j J
  change ShortResetRow.destination (h r) (C.route.port j)=
    some (C.route.port (j+1)) at L
  have P := raw_observe sheet x e N mask
  dsimp only at P
  have A := drain_row_idle (params sheet s) (h e) (h r)
    (selectBytes sheet (x e)) (selectBytes sheet (x r))
    (C.route.port j) (C.route.port (j+1)) ((dest_eq _ _).trans L) H
  exact ⟨(congrArg (fun z=>z.1.1 (C.route.port j)) P).trans A.1,
    (congrArg (fun z=>z.2.1 (C.route.port (j+1))) P).trans A.2⟩

private theorem raw_terminal_wire (sheet : Sheet) (C : Chart h)
    (x : Raw s n) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (j : Nat) (J : j+1=C.L)
    (H : tok sheet C x j=MISByteCodec.E ∨ tok sheet C x j=reset0Reply) :
    wire sheet C (rawNext s x (out C j)) j=wire sheet C x j := by
  let e := out C j
  let r := rightNeighbor e
  have L := C.route.turn
  have K : C.L-1=j := by omega
  change ShortResetRow.destination (h (rightNeighbor (out C (C.L-1))))
    (C.route.port (C.L-1))=none at L
  rw [K] at L
  have P := raw_observe sheet x e N mask
  dsimp only at P
  have A := drain_row_terminal_hold (params sheet s) (h e) (h r)
    (selectBytes sheet (x e)) (selectBytes sheet (x r)) (C.route.port j)
    ((dest_eq _ _).trans L) H
  exact (congrArg (fun z=>z.1.1 (C.route.port j)) P).trans A

/-! The only subtype is the frozen/cache fibre. No safety assumption
    about the dirty report slots, grants, bank contents or controller. -/

def advance (sheet : Sheet) {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q)
    (x : {x : Raw s n // Q x}) (e : Fin n) : {x : Raw s n // Q x} :=
  ⟨rawNext s x.val e,F.closed x.val e x.property⟩

-- CHECK: Rows field order and exact arguments, ReportResetBarrier.lean:21–47.
theorem rows_on_fibre (sheet : Sheet) (C : Chart h) (N : 1<n)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q) :
    ReportResetBarrier.Rows C (advance sheet F)
      (fun x=>slot sheet C x.val) (fun x=>ownerPC sheet C x.val) := by
  constructor
  · intro x P
    exact raw_issue sheet C x.val N (F.mask x.val x.property) P
  · intro x k P K
    exact congrArg (letterOf (params sheet s)) (raw_door_frame sheet C x.val k P K)
  · intro x P S
    exact raw_hold sheet C x.val N (F.mask x.val x.property) P S
  · intro x P S
    exact raw_consume sheet C x.val N (F.mask x.val x.property) P S
  · intro x e D
    exact raw_nondoor_pc sheet C x.val e N (F.mask x.val x.property) D
  · intro x e D H k K
    exact congrArg (letterOf (params sheet s)) (raw_off_frame sheet C x.val e D H k K)
  · intro x j J k K A B
    exact congrArg (letterOf (params sheet s)) (raw_link_frame sheet C x.val j k J K A B)
  · intro x j J H
    have T := tok_of_slot sheet C x.val j .forward0 (by decide) H
    have P := raw_forward_hop sheet C x.val (F.mask x.val x.property)
      j J (edge_sep N _) T
    exact ⟨slot_of_wire sheet C _ j .trail (by decide) P.1,
      slot_of_wire sheet C _ (j+1) .forward0 (by decide) P.2⟩
  · intro x j J H
    have T := tok_of_slot sheet C x.val j .forward0 (by decide) H
    exact slot_of_wire sheet C _ j .reply0 (by decide)
      (raw_forward_turn sheet C x.val (F.mask x.val x.property)
        j J (edge_sep N _) T)
  · intro x j J H K
    have T := tok_of_slot sheet C x.val j .trail (by decide) H
    have U : tok sheet C x.val (j+1)=MISByteCodec.T ∨
        tok sheet C x.val (j+1)=reset0Forward := by
      rcases K with K|K
      · exact .inl (tok_of_slot sheet C x.val _ .trail (by decide) K)
      · exact .inr (tok_of_slot sheet C x.val _ .forward0 (by decide) K)
    have W := raw_idle_wire sheet C x.val N (F.mask x.val x.property)
      j J (.inl ⟨T,U⟩)
    exact ⟨(congrArg (letterOf (params sheet s)) W.1).trans H,
      congrArg (letterOf (params sheet s)) W.2⟩
  · intro x j J T D
    have E := tok_of_slot sheet C x.val j .trail (by decide) T
    have R := tok_of_slot sheet C x.val (j+1) .reply0 (by decide) D
    have A : (tok sheet C x.val j).tag≠2 := by rw [E]; decide
    have W := raw_backward sheet C x.val (F.mask x.val x.property)
      j J (edge_sep N _) A R
    exact ⟨slot_of_wire sheet C _ j .reply0 (by decide) W.1,
      slot_of_wire sheet C _ (j+1) .empty (by decide) W.2⟩
  · intro x j J H K
    have T : tok sheet C x.val j=MISByteCodec.E ∨
        tok sheet C x.val j=reset0Reply := by
      rcases H with H|H
      · exact .inl (tok_of_slot sheet C x.val j .empty (by decide) H)
      · exact .inr (tok_of_slot sheet C x.val j .reply0 (by decide) H)
    have U := tok_of_slot sheet C x.val (j+1) .empty (by decide) K
    have W := raw_idle_wire sheet C x.val N (F.mask x.val x.property)
      j J (.inr ⟨T,U⟩)
    exact ⟨congrArg (letterOf (params sheet s)) W.1,
      (congrArg (letterOf (params sheet s)) W.2).trans K⟩
  · intro x j J H
    have T : tok sheet C x.val j=MISByteCodec.E ∨
        tok sheet C x.val j=reset0Reply := by
      rcases H with H|H
      · exact .inl (tok_of_slot sheet C x.val j .empty (by decide) H)
      · exact .inr (tok_of_slot sheet C x.val j .reply0 (by decide) H)
    exact congrArg (letterOf (params sheet s))
      (raw_terminal_wire sheet C x.val N (F.mask x.val x.property) j J T)

/-! Grant release uses the actual joined production grant equations,
    not the unfiltered report row. -/

def grantBit (sheet : Sheet) (x : Raw s n) (q : Fin n) (j : Fin 3) : Bool :=
  (selectBytes sheet (x q)).getLsbD (grantAddr (params sheet s) j)

-- CHECK: service_joined_grants_report1/report2, ReportJoinedGrants.lean (last two raw exports).
private theorem raw_grants (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (j : Fin 3)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i) :
    grantBit sheet (rawNext s x e) e j=
        grantNext (params sheet s) (h e) (selectBytes sheet (x e)) j ∧
    grantBit sheet (rawNext s x e) (rightNeighbor e) j=
        grantReceived (params sheet s) (h (rightNeighbor e))
          (selectBytes sheet (x (rightNeighbor e))) j := by
  cases sheet with
  | first =>
    have A := ReportJoinedGrants.service_joined_grants_report1 x e (edge_sep N e) j
    dsimp only at A
    rw [← mask e, ← mask (rightNeighbor e)]
    exact A
  | second =>
    have A := ReportJoinedGrants.service_joined_grants_report2 x e (edge_sep N e) j
    dsimp only at A
    rw [← mask e, ← mask (rightNeighbor e)]
    exact A

private theorem no_ask (p : Params) (u : BitVec p.w) (j : Fin 3)
    (H : DrainLetter (publicationToken p true u j)) :
    (ReportJoinedGrants.oldView p true u).ask j=false := by
  -- CHECK: BStarShort.reportK is definitionally the report oldK;
  -- BStarShort.lean:76-95, ReportJoinedGrants.lean:7-8.
  change ((publicationToken p true u j).tag==2 &&
    !(publicationToken p true u j).fault &&
    (publicationToken p true u j).opcode==acqOp p)=false
  rcases H with A|A|A|A <;> rw [A] <;>
    simp [MISByteCodec.E,MISByteCodec.T,reset0Forward,reset0Reply,acqOp]

private theorem reset_release (p : Params) (u : BitVec p.w) (j : Fin 3)
    (F : publicationToken p true u j=reset0Forward) :
    grantNext p true u j=false := by
  have R : (ReportJoinedGrants.oldView p true u).release j=true := by
    change ((publicationToken p true u j).tag==2 &&
      !(publicationToken p true u j).fault &&
      (publicationToken p true u j).opcode==0)=true
    rw [F]
    rfl
  rw [←ReportJoinedGrants.next_agrees]
  exact ReportJoinedGrants.release_next_false _ _ R

private theorem absent_stays (sheet : Sheet) (x : Raw s n)
    (e q : Fin n) (j : Fin 3) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (H : h q=true) (O : grantBit sheet x q j=false)
    (T : DrainLetter (publicationToken (params sheet s) true
      (selectBytes sheet (x q)) j)) :
    grantBit sheet (rawNext s x e) q j=false := by
  by_cases E : q=e
  · subst q
    have A := (raw_grants sheet x e N j mask).1
    rw [H] at A
    rw [A,←ReportJoinedGrants.next_agrees]
    exact ReportJoinedGrants.no_ask_no_create _ _ O (no_ask _ _ _ T)
  · by_cases R : q=rightNeighbor e
    · subst q
      have A := (raw_grants sheet x e N j mask).2
      rw [H] at A
      exact A.trans (ReportJoinedGrants.received_no_create _ _ _ _ O)
    · unfold grantBit
      rw [raw_spectator x e q E R]
      exact O

def Rail (sheet : Sheet) (C : Chart h) (x : Raw s n) (st : Stage) : Prop :=
  ReportResetBarrier.At C (slot sheet C) (ownerPC sheet C) x st

def Released (sheet : Sheet) (C : Chart h) (x : Raw s n) (st : Stage) : Prop :=
  ∀ k,k<C.L → h (out C k)=true → ShortResetReleased.passed st k →
    grantBit sheet x (out C k) (C.route.port k)=false

def Active (sheet : Sheet) (C : Chart h) (x : Raw s n) (st : Stage) : Prop :=
  Rail sheet C x st ∧ Released sheet C x st

def Parked (sheet : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  ownerPC sheet C x=.issue1 ∧
    (∀ k,k<C.L → wire sheet C x k=canon (params sheet s) .empty) ∧
    (∀ k,k<C.L → h (out C k)=true →
      grantBit sheet x (out C k) (C.route.port k)=false)

private theorem passed_token (sheet : Sheet) (C : Chart h)
    (x : Raw s n) (st : Stage) (A : Rail sheet C x st)
    (k : Nat) (K : k<C.L) (P : ShortResetReleased.passed st k) :
    DrainLetter (tok sheet C x k) := by
  cases st with
  | fwd i =>
    have T := tok_of_slot sheet C x k .trail (by decide) (A.2.2.2 k P)
    exact .inr (.inl T)
  | rev i =>
    have W := A.2.2 k K
    by_cases H : k<i
    · rw [if_pos H] at W
      exact .inr (.inl (tok_of_slot sheet C x k .trail (by decide) W))
    · by_cases E : k=i
      · rw [if_neg H,if_pos E] at W
        exact .inr (.inr (.inr (tok_of_slot sheet C x k .reply0 (by decide) W)))
      · rw [if_neg H,if_neg E] at W
        exact .inl (tok_of_slot sheet C x k .empty (by decide) W)
  | done =>
    exact .inl (tok_of_slot sheet C x k .empty (by decide) (A.2 k K))

private theorem passed_next (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (e : Fin n) (st : Stage) (A : Rail sheet C x st)
    (k : Nat) (K : k<C.L) (P : ShortResetReleased.passed (nextStage C e st) k) :
    ShortResetReleased.passed st k ∨
      ∃ i, st=.fwd i ∧ k=i ∧ e=out C k := by
  cases st with
  | done => exact .inl trivial
  | rev i => exact .inl trivial
  | fwd i =>
    have I : i<C.L := A.1
    simp only [nextStage] at P
    by_cases E : e=out C i
    · rw [if_pos E] at P
      by_cases J : i+1<C.L
      · rw [if_pos J] at P
        change k<i+1 at P
        by_cases V : k=i
        · exact .inr ⟨i,rfl,V,V.symm ▸ E⟩
        · exact .inl (show k<i by omega)
      · by_cases V : k=i
        · exact .inr ⟨i,rfl,V,V.symm ▸ E⟩
        · exact .inl (show k<i by omega)
    · rw [if_neg E] at P
      exact .inl P

theorem release_step (sheet : Sheet) (C : Chart h)
    (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (st : Stage) (A : Rail sheet C x st) (R : Released sheet C x st) :
    Released sheet C (rawNext s x e) (nextStage C e st) := by
  intro k K H P
  rcases passed_next sheet C x e st A k K P with O|⟨i,S,E,M⟩
  · have T := passed_token sheet C x st A k K O
    change DrainLetter (publicationToken (params sheet s) (h (out C k))
      (selectBytes sheet (x (out C k))) (C.route.port k)) at T
    rw [H] at T
    exact absent_stays sheet x e (out C k) (C.route.port k) N mask H
      (R k K H O) T
  · subst st
    subst i
    have W := tok_of_slot sheet C x k .forward0 (by decide) A.2.2.1
    change publicationToken (params sheet s) (h (out C k))
      (selectBytes sheet (x (out C k))) (C.route.port k)=reset0Forward at W
    rw [H] at W
    subst e
    have G := (raw_grants sheet x (out C k) N (C.route.port k) mask).1
    rw [H] at G
    exact G.trans (reset_release _ _ _ W)

/-- Genuine ISSUE0 can have an arbitrary inherited suffix. -/
theorem launch (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (I : ownerPC sheet C x=.issue0) :
    Active sheet C (rawNext s x (door C)) (.fwd 0) := by
  obtain ⟨P,W⟩ := raw_issue sheet C x N mask I
  refine ⟨⟨C.positive,P,W,fun k K=>False.elim (Nat.not_lt_zero k K)⟩,?_⟩
  intro k _ _ K
  change k<0 at K
  omega

/-- Main all-mark invariant: ALL actual labels, including unrelated
    labels and simultaneous foreign/sibling-port activities. -/
theorem active_step (sheet : Sheet) (C : Chart h)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q)
    (x : Raw s n) (X : Q x) (N : 1<n)
    (e : Fin n) (st : Stage) (L : st≠.done)
    (A : Active sheet C x st) :
    Active sheet C (rawNext s x e) (nextStage C e st) := by
  have M := F.mask x X
  have R := ReportResetBarrier.active_step (rows_on_fibre sheet C N F)
    (⟨x,X⟩ : {x : Raw s n // Q x}) e st L A.1
  exact ⟨R,release_step sheet C x e N M st A.1 A.2⟩

theorem parked_of_done (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (A : Active sheet C x .done) :
    Parked sheet C x :=
  ⟨A.1.1,fun k K=>slot_wire sheet C x k .empty (by decide) (A.1.2 k K),
    fun k K H=>A.2 k K H trivial⟩

/-- A first consume is at the root's actual incoming edge,
    with old WAIT0 and the canonical D0 at root K0. -/
theorem consume_step (sheet : Sheet) (C : Chart h)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q)
    (x : Raw s n) (X : Q x) (N : 1<n)
    (A : Active sheet C x (.rev 0)) :
    controlWork (params sheet s) (selectBytes sheet (x C.root))=(2,0) ∧
    resetTokenRead (params sheet s) (selectBytes sheet (x C.root)) 0=
        resetTokenWire (params sheet s) reset0Reply ∧
    Parked sheet C (rawNext s x (door C)) := by
  have R := A.1.2.2 0 C.positive
  have W : slot sheet C x 0=.reply0 := by simpa using R
  have Wire := slot_wire sheet C x 0 .reply0 (by decide) W
  rw [wire_zero] at Wire
  have K := active_step sheet C F x X N (door C) (.rev 0) (by decide) A
  have D : nextStage C (door C) (.rev 0)=.done := by
    simp [nextStage,door,RearTrace.right_predecessor]
  rw [D] at K
  exact ⟨pc_fields sheet C x .wait0 (by decide) A.1.2.1,Wire,
    parked_of_done sheet C _ K⟩

/-! Original-tape generated flight. No bare old matching D0 supplies
    this history, and no step after the first consume is credited. -/

inductive Generated (sheet : Sheet) (C : Chart h) (x0 : Raw s n) :
    List (Fin n)→Stage→Prop where
  | issue : ownerPC sheet C x0=.issue0 →
      Generated sheet C x0 [door C] (.fwd 0)
  | snoc {w : List (Fin n)} {st : Stage} (e : Fin n) :
      Generated sheet C x0 w st → st≠.done →
      Generated sheet C x0 (w++[e]) (nextStage C e st)

private theorem fibre_run (sheet : Sheet) {Q : Raw s n→Prop}
    (F : Fibre (h:=h) sheet Q) (x : Raw s n) (X : Q x)
    (w : List (Fin n)) : Q (rawRun x w) := by
  induction w generalizing x with
  | nil => exact X
  | cons e w ih => exact ih _ (F.closed x e X)

theorem generated_active (sheet : Sheet) (C : Chart h)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q)
    (x : Raw s n) (X : Q x) (N : 1<n)
    (w : List (Fin n)) (st : Stage) (G : Generated sheet C x w st) :
    Active sheet C (rawRun x w) st := by
  induction G with
  | issue I =>
    exact launch sheet C x N (F.mask x X) I
  | @snoc w st e G L ih =>
    rw [ShortOwnerEpochJS.raw_snoc]
    exact active_step sheet C F _ (fibre_run sheet F x X w) N e st L ih

private theorem done_iff (C : Chart h) (e : Fin n)
    (st : Stage) (L : st≠.done) :
    nextStage C e st=.done ↔ st=.rev 0 ∧ e=door C := by
  have Door : rightNeighbor e=C.root ↔ e=door C := by
    constructor
    · intro R
      simpa only [door,RearTrace.predecessor_right] using
        congrArg RearTrace.predecessor R
    · rintro rfl
      exact RearTrace.right_predecessor _
  cases st with
  | done => exact False.elim (L rfl)
  | fwd i =>
    by_cases E : e=out C i
    · by_cases J : i+1<C.L <;> simp [nextStage,E,J]
    · simp [nextStage,E]
  | rev i =>
    cases i with
    | zero =>
      by_cases E : rightNeighbor e=C.root
      · have D := Door.mp E
        have W : rightNeighbor (door C)=C.root := RearTrace.right_predecessor _
        simp [nextStage,E,D,W]
      · have D : e≠door C := fun K=>E (Door.mpr K)
        simp [nextStage,E,D]
    | succ i =>
      by_cases E : e=out C i <;> simp [nextStage,E]

theorem generated_last_consume (sheet : Sheet) (C : Chart h)
    (x : Raw s n) (w : List (Fin n)) (st : Stage)
    (G : Generated sheet C x w st) (D : st=.done) :
    ∃ pre : List (Fin n), w=pre++[door C] ∧
      Generated sheet C x pre (.rev 0) := by
  cases G with
  | issue I => contradiction
  | @snoc w st e G L =>
    obtain ⟨S,E⟩ := (done_iff C e st L).mp D
    subst st
    subst e
    exact ⟨w,rfl,G⟩

theorem genuine_reset_parked (sheet : Sheet) (C : Chart h)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q)
    (x : Raw s n) (X : Q x) (N : 1<n)
    (w : List (Fin n)) (G : Generated sheet C x w .done) :
    Parked sheet C (rawRun x w) ∧
      ∃ pre : List (Fin n),w=pre++[door C] ∧
        controlWork (params sheet s) (selectBytes sheet (rawRun x pre C.root))=(2,0) ∧
        resetTokenRead (params sheet s) (selectBytes sheet (rawRun x pre C.root)) 0=
          resetTokenWire (params sheet s) reset0Reply := by
  obtain ⟨pre,W,B⟩ := generated_last_consume sheet C x w .done G rfl
  have A := generated_active sheet C F x X N pre (.rev 0) B
  obtain ⟨P,R,Y⟩ := consume_step sheet C F _
    (fibre_run sheet F x X pre) N A
  refine ⟨?_,pre,W,P,R⟩
  rw [W,ShortOwnerEpochJS.raw_snoc]
  exact Y

/-! Progress-event count. This is the generated RESET drain term,
    NOT the still-separate arbitrary-dirty prelaunch event budget. -/

def InRange (C : Chart h) : Stage→Prop
  | .fwd i | .rev i => i<C.L
  | .done => True

def progress (C : Chart h) (st : Stage) (e : Fin n) : Nat :=
  if nextStage C e st=st then 0 else 1

def progressCount (C : Chart h) : Stage→List (Fin n)→Nat
  | _,[] => 0
  | st,e::w => progress C st e+progressCount C (nextStage C e st) w

private theorem range_next (C : Chart h) (st : Stage) (e : Fin n)
    (A : InRange C st) : InRange C (nextStage C e st) := by
  cases st with
  | done => trivial
  | fwd i =>
    change i<C.L at A
    by_cases E : e=out C i
    · by_cases J : i+1<C.L <;> simp [nextStage,E,J,InRange,A]
    · simp [nextStage,E,InRange,A]
  | rev i =>
    change i<C.L at A
    cases i with
    | zero => by_cases E : rightNeighbor e=C.root <;> simp [nextStage,E,InRange,A]
    | succ i =>
      by_cases E : e=out C i
      · simp [nextStage,E,InRange,show i<C.L by omega]
      · simp [nextStage,E,InRange,A]

theorem progress_debt (C : Chart h) (st : Stage) (e : Fin n)
    (A : InRange C st) :
    progress C st e+debt C.L (nextStage C e st)=debt C.L st := by
  cases st with
  | done => rfl
  | fwd i =>
    change i<C.L at A
    by_cases E : e=out C i
    · by_cases J : i+1<C.L <;>
        simp [progress,nextStage,E,J,debt] <;> omega
    · simp [progress,nextStage,E]
  | rev i =>
    change i<C.L at A
    cases i with
    | zero =>
      by_cases E : rightNeighbor e=C.root <;>
        simp [progress,nextStage,E,debt]
    | succ i =>
      by_cases E : e=out C i <;>
        simp [progress,nextStage,E,debt] <;> omega

theorem count_exact (C : Chart h) (st : Stage) (w : List (Fin n))
    (A : InRange C st) :
    progressCount C st w+debt C.L (ShortResetReleased.stageRun C st w)=
      debt C.L st := by
  induction w generalizing st with
  | nil => simp [progressCount,ShortResetReleased.stageRun]
  | cons e w ih =>
    have H := progress_debt C st e A
    have K := ih (nextStage C e st) (range_next C st e A)
    simp only [progressCount,ShortResetReleased.stageRun]
    omega

theorem reset_progress_cap (C : Chart h) (w : List (Fin n)) :
    progressCount C (.fwd 0) w≤2*C.L := by
  have H := count_exact C (.fwd 0) w C.positive
  change progressCount C (.fwd 0) w+_ =2*C.L-0 at H
  omega

theorem reset_progress_at_done (C : Chart h) (w : List (Fin n))
    (D : ShortResetReleased.stageRun C (.fwd 0) w=.done) :
    progressCount C (.fwd 0) w=2*C.L := by
  have H := count_exact C (.fwd 0) w C.positive
  rw [D] at H
  simpa [debt] using H

theorem nominate (C : Chart h) (st : Stage) (A : InRange C st)
    (L : st≠.done) : ∃ e : Fin n,progress C st e=1 := by
  obtain ⟨e,E⟩ := (ShortResetCycle.debt_step C st (by
    cases st with
    | done => exact L rfl
    | fwd k => exact A
    | rev k => exact A)).2
  have T : nextStage C e st≠st := by
    intro H
    rw [H] at E
    omega
  exact ⟨e,if_neg T⟩

/-- The checked barrier consumer now has concrete Rows on the actual
    frozen/cache fibre. Every monitor mark projects to rawNext. -/
-- CHECK: ReportResetBarrier.lean:331–369 (completed_mean).
theorem completed_mean (sheet : Sheet) (C : Chart h)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q)
    (x : Raw s n) (X : Q x) (N : 1<n)
    (I : ownerPC sheet C x=.issue0) :
    Height.IIDExpectedHittingTimeAtMost
      (ReportResetBarrier.monitor C (advance sheet F)) (fun z=>z.2=.done)
      (advance sheet F ⟨x,X⟩ (door C),.fwd 0) (2*C.L*n) :=
  ReportResetBarrier.completed_mean (rows_on_fibre sheet C N F) ⟨x,X⟩ I

/-- Prefix convention: the finishing mark is included in progressCount.
    ReportResetEventClock.events excludes the finishing mark, so it
    is bounded by the same count (and in fact one less at completion). -/
noncomputable def progressBit (C : Chart h) (st : Stage) (e : Fin n) : Bool :=
  decide (nextStage C e st≠st)

theorem counted_events_le {Y : Type} (C : Chart h) (step : Y→Fin n→Y)
    (x : Y) (st : Stage) (w : List (Fin n)) :
    ReportResetEventClock.events (ReportResetBarrier.monitor C step)
      (fun z=>z.2=.done) (fun z e=>progressBit C z.2 e) (x,st) w≤
      progressCount C st w := by
  classical
  induction w generalizing x st with
  | nil => exact Nat.le_refl _
  | cons e w ih =>
    rw [ReportResetEventClock.events]
    split
    · exact Nat.zero_le _
    · change (progressBit C st e).toNat + _ ≤ _
      simp only [ReportResetBarrier.monitor,progressCount,Prod.snd]
      have K := ih (step x e) (nextStage C e st)
      have E : (progressBit C st e).toNat=progress C st e := by
        by_cases T : nextStage C e st=st <;> simp [progressBit,progress,T]
      rw [E]
      exact Nat.add_le_add_left K _

/-- Both concrete sheets share the same post-launch bound; the digit
    count is exactly (params sheet s).digits, not an extra free field. -/
theorem reset_cap_on_fibre (sheet : Sheet) (C : Chart h)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q)
    (x : Raw s n) (X : Q x) (w : List (Fin n)) :
    ReportResetEventClock.events (ReportResetBarrier.monitor C (advance sheet F))
      (fun z=>z.2=.done) (fun z e=>progressBit C z.2 e)
      (advance sheet F ⟨x,X⟩ (door C),.fwd 0) w≤2*C.L :=
  Nat.le_trans (counted_events_le C (advance sheet F) _ _ w)
    (reset_progress_cap C w)

/-! Full structural receipt, beyond the token/grant/PC projection.
    The seal belongs to the lane-1 owner at its center header.
    Source file and raw-zero seal are observed below grantBase, where
    the joined work-bit theorem is exact. -/

-- CHECK: raw_report1_pair/raw_report2_pair, ReportRawProjection.lean:52–78.
private theorem raw_pair_work (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i) :
    (selectBytes sheet (rawNext s x e e),
      selectBytes sheet (rawNext s x e (rightNeighbor e))) =
      join (params sheet s) (h e,h (rightNeighbor e))
        (selectBytes sheet (x e),selectBytes sheet (x (rightNeighbor e))) := by
  cases sheet with
  | first =>
    have R := raw_report1_pair x e (edge_sep N e)
    dsimp only at R
    rw [← mask e, ← mask (rightNeighbor e)]
    exact R
  | second =>
    have R := raw_report2_pair x e (edge_sep N e)
    dsimp only at R
    rw [← mask e, ← mask (rightNeighbor e)]
    exact R

private theorem raw_work_low (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (i : Nat) (I : i<grantBase (params sheet s)) :
    let p := params sheet s
    let u := selectBytes sheet (x e)
    let v := selectBytes sheet (x (rightNeighbor e))
    let q := row p (h e,h (rightNeighbor e)) (u,v)
    (selectBytes sheet (rawNext s x e e)).getLsbD i=(q.1.apply u).getLsbD i ∧
    (selectBytes sheet (rawNext s x e (rightNeighbor e))).getLsbD i=(q.2.apply v).getLsbD i := by
  let p := params sheet s
  let u := selectBytes sheet (x e)
  let v := selectBytes sheet (x (rightNeighbor e))
  have P := raw_pair_work sheet x e N mask
  have J := join_work_bits p (h e,h (rightNeighbor e)) (u,v) i I
  exact ⟨(congrArg (fun z : Pair (BitVec p.w)=>z.1.getLsbD i) P).trans J.1,
    (congrArg (fun z : Pair (BitVec p.w)=>z.2.getLsbD i) P).trans J.2⟩

-- CHECK: drainFile is a literal extract (the private get unfolds).
private theorem file_eq_low (p : Params) (u v : BitVec p.w)
    (H : ∀ i,i<grantBase p→u.getLsbD i=v.getLsbD i) :
    drainFile p u=drainFile p v := by
  unfold drainFile
  change (u.extractLsb' (sourceBase p) (19+2*d p)).toNat=
    (v.extractLsb' (sourceBase p) (19+2*d p)).toNat
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  apply H
  unfold grantBase sealBase sourceW
  omega

private theorem seal_of_low (p : Params) (u v : BitVec p.w)
    (H : ∀ i,i<grantBase p→u.getLsbD i=v.getLsbD i)
    (S : drainSealZero p v) : drainSealZero p u := by
  intro i L U
  exact (H i (by unfold grantBase; omega)).trans (S i L U)

def FileClear (sheet : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  drainFile (params sheet s) (selectBytes sheet (x C.root))=0

def SealReleased (sheet : Sheet) (C : Chart h) (x : Raw s n) (st : Stage) : Prop :=
  ∀ k,k<C.L→h (out C k)=true→C.route.port k=1→ShortResetReleased.passed st k→
    drainSealZero (params sheet s) (selectBytes sheet (x (out C k)))

private theorem file_launch (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (I : ownerPC sheet C x=.issue0) : FileClear sheet C (rawNext s x (door C)) := by
  let p := params sheet s
  let e := door C
  have R : rightNeighbor e=C.root := RearTrace.right_predecessor C.root
  have F := pc_fields sheet C x .issue0 (by decide) I
  have P : sourcePhase p (selectBytes sheet (x C.root))=1 :=
    congrArg _root_.Prod.fst F
  have O : sourceOpcode p (selectBytes sheet (x C.root))=0 :=
    congrArg _root_.Prod.snd F
  let u := selectBytes sheet (x e)
  let v := selectBytes sheet (x C.root)
  have W := drain_row_file_issue p (h e) u v P O
  unfold FileClear
  apply Eq.trans _ W
  apply file_eq_low
  intro i J
  have H := (raw_work_low sheet x e N mask i J).2
  rw [R,C.rootHeader] at H
  exact H

-- CHECK: At constructor projections, ReportResetBarrier.lean:49–54.
private theorem rail_root_wait (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (st : Stage) (L : st≠.done) (A : Rail sheet C x st) :
    ownerPC sheet C x=.wait0 ∧
      (tok sheet C x 0=MISByteCodec.T ∨ tok sheet C x 0=reset0Forward ∨
       tok sheet C x 0=reset0Reply) := by
  cases st with
  | done => exact False.elim (L rfl)
  | fwd i =>
    refine ⟨A.2.1,?_⟩
    cases i with
    | zero => exact .inr (.inl (tok_of_slot sheet C x 0 .forward0 (by decide) A.2.2.1))
    | succ i => exact .inl (tok_of_slot sheet C x 0 .trail (by decide) (A.2.2.2 0 (by omega)))
  | rev i =>
    refine ⟨A.2.1,?_⟩
    have S := A.2.2 0 C.positive
    cases i with
    | zero =>
      exact .inr (.inr (tok_of_slot sheet C x 0 .reply0 (by decide) (by simpa using S)))
    | succ i =>
      exact .inl (tok_of_slot sheet C x 0 .trail (by decide) (by simpa using S))

private theorem file_step (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (e : Fin n) (st : Stage) (L : st≠.done) (A : Rail sheet C x st)
    (Z : FileClear sheet C x) : FileClear sheet C (rawNext s x e) := by
  let p := params sheet s
  unfold FileClear at Z ⊢
  by_cases E : e=C.root
  · subst e
    let u := selectBytes sheet (x C.root)
    let v := selectBytes sheet (x (rightNeighbor C.root))
    have W := drain_row_file_left p (h (rightNeighbor C.root)) u v
    apply Eq.trans _ (W.trans Z)
    apply file_eq_low
    intro i J
    have H := (raw_work_low sheet x C.root N mask i J).1
    rw [C.rootHeader] at H
    exact H
  · by_cases R : rightNeighbor e=C.root
    · have A0 := rail_root_wait sheet C x st L A
      have F := pc_fields sheet C x .wait0 (by decide) A0.1
      let u := selectBytes sheet (x e)
      let v := selectBytes sheet (x C.root)
      have P : sourcePhase p v=2 := congrArg _root_.Prod.fst F
      have O : sourceOpcode p v=0 := congrArg _root_.Prod.snd F
      have K := A0.2
      rw [tok_zero] at K
      have W := drain_row_file_wait p (h e) u v P O K
      apply Eq.trans _ (W.trans Z)
      apply file_eq_low
      intro i J
      have H := (raw_work_low sheet x e N mask i J).2
      rw [R,C.rootHeader] at H
      exact H
    · rw [raw_spectator x e C.root (Ne.symm E) (Ne.symm R)]
      exact Z

private theorem seal_hold (sheet : Sheet) (x : Raw s n)
    (e q : Fin n) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (H : h q=true)
    (T : DrainLetter (publicationToken (params sheet s) true
      (selectBytes sheet (x q)) 1))
    (A : drainSealZero (params sheet s) (selectBytes sheet (x q))) :
    drainSealZero (params sheet s) (selectBytes sheet (rawNext s x e q)) := by
  let p := params sheet s
  by_cases E : q=e
  · subst q
    have W := drain_row_seal_hold_left p (h (rightNeighbor e))
      (selectBytes sheet (x e)) (selectBytes sheet (x (rightNeighbor e))) T A
    apply seal_of_low p _ _ _ W
    intro i I
    have R := (raw_work_low sheet x e N mask i I).1
    rw [H] at R
    exact R
  · by_cases R : q=rightNeighbor e
    · subst q
      have W := drain_row_seal_hold_right p (h e)
        (selectBytes sheet (x e)) (selectBytes sheet (x (rightNeighbor e))) A
      apply seal_of_low p _ _ _ W
      intro i I
      have G := (raw_work_low sheet x e N mask i I).2
      rw [H] at G
      exact G
    · rw [raw_spectator x e q E R]
      exact A

theorem seal_release_step (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (e : Fin n) (st : Stage) (A : Rail sheet C x st) (S : SealReleased sheet C x st) :
    SealReleased sheet C (rawNext s x e) (nextStage C e st) := by
  intro k K H J P
  rcases passed_next sheet C x e st A k K P with O|⟨i,U,V,M⟩
  · have T := passed_token sheet C x st A k K O
    change DrainLetter (publicationToken (params sheet s) (h (out C k))
      (selectBytes sheet (x (out C k))) (C.route.port k)) at T
    rw [H,J] at T
    exact seal_hold sheet x e (out C k) N mask H T (S k K H J O)
  · subst st
    subst i
    subst e
    have T := tok_of_slot sheet C x k .forward0 (by decide) A.2.2.1
    change publicationToken (params sheet s) (h (out C k))
      (selectBytes sheet (x (out C k))) (C.route.port k)=reset0Forward at T
    rw [H,J] at T
    have W := drain_row_seal_release (params sheet s) (h (rightNeighbor (out C k)))
      (selectBytes sheet (x (out C k)))
      (selectBytes sheet (x (rightNeighbor (out C k)))) T
    apply seal_of_low _ _ _ _ W
    intro b B
    have R := (raw_work_low sheet x (out C k) N mask b B).1
    rw [H] at R
    exact R

def FullActive (sheet : Sheet) (C : Chart h) (x : Raw s n) (st : Stage) : Prop :=
  Active sheet C x st ∧ FileClear sheet C x ∧ SealReleased sheet C x st

def FullParked (sheet : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  Parked sheet C x ∧ FileClear sheet C x ∧
    (∀ k,k<C.L→h (out C k)=true→C.route.port k=1→
      drainSealZero (params sheet s) (selectBytes sheet (x (out C k))))

theorem full_launch (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (I : ownerPC sheet C x=.issue0) :
    FullActive sheet C (rawNext s x (door C)) (.fwd 0) := by
  refine ⟨launch sheet C x N mask I,file_launch sheet C x N mask I,?_⟩
  intro k _ _ _ P
  change k<0 at P
  omega

theorem full_active_step (sheet : Sheet) (C : Chart h)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q)
    (x : Raw s n) (X : Q x) (N : 1<n)
    (e : Fin n) (st : Stage) (L : st≠.done)
    (A : FullActive sheet C x st) :
    FullActive sheet C (rawNext s x e) (nextStage C e st) :=
  ⟨active_step sheet C F x X N e st L A.1,
    file_step sheet C x N (F.mask x X) e st L A.1.1 A.2.1,
    seal_release_step sheet C x N (F.mask x X) e st A.1.1 A.2.2⟩

theorem generated_full (sheet : Sheet) (C : Chart h)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q)
    (x : Raw s n) (X : Q x) (N : 1<n)
    (w : List (Fin n)) (st : Stage) (G : Generated sheet C x w st) :
    FullActive sheet C (rawRun x w) st := by
  induction G with
  | issue I => exact full_launch sheet C x N (F.mask x X) I
  | @snoc w st e G L ih =>
    rw [ShortOwnerEpochJS.raw_snoc]
    exact full_active_step sheet C F _ (fibre_run sheet F x X w) N e st L ih

theorem genuine_full_parked (sheet : Sheet) (C : Chart h)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q)
    (x : Raw s n) (X : Q x) (N : 1<n)
    (w : List (Fin n)) (G : Generated sheet C x w .done) :
    FullParked sheet C (rawRun x w) := by
  have A := generated_full sheet C F x X N w .done G
  exact ⟨parked_of_done sheet C _ A.1,A.2.1,fun k K H J=>A.2.2 k K H J trivial⟩

/-- With the real finished chart geometry and current cache, the
    end of a genuine flight has all fields required by the reset seed.
    The same raw word and first own consume are preserved. -/
theorem cached_genuine_full_parked (sheet : Sheet) (C : Chart h)
    (N : 1<n) (hh : ∃ i,h i=true) {Q : Raw s n→Prop}
    (F : Fibre (h:=h) sheet Q) (x : Raw s n) (X : Cached sheet hh Q x)
    (w : List (Fin n)) (G : Generated sheet C x w .done) :
    Cached sheet hh Q (rawRun x w) ∧ FullParked sheet C (rawRun x w) :=
  ⟨fibre_run sheet (cached_fibre sheet N hh Q F) x X w,
    genuine_full_parked sheet C (cached_fibre sheet N hh Q F) x X N w G⟩

#print axioms raw_pair_work
#print axioms raw_work_low
#print axioms file_launch
#print axioms file_step
#print axioms seal_release_step
#print axioms full_active_step
#print axioms generated_full
#print axioms genuine_full_parked
#print axioms cached_genuine_full_parked


#print axioms cached_fibre
#print axioms rows_on_fibre
#print axioms release_step
#print axioms active_step
#print axioms consume_step
#print axioms generated_active
#print axioms genuine_reset_parked
#print axioms count_exact
#print axioms reset_progress_cap
#print axioms nominate
#print axioms completed_mean
#print axioms counted_events_le
#print axioms reset_cap_on_fibre

end L4.ReportOwnerResetDrain

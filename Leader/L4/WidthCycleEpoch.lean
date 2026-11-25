import Leader.L4.WidthEntryEpoch

namespace L4.WidthCycleEpoch

open AllSizeProtocol PhysicalCustody BStarH6WordChart BStarH6Ordinal
open WidthSectorGeometry ShortResetChart WidthFreshForward
open WidthChooseEpoch
open BStarWidthTransferDepart (Data execute readData)
open WidthByteRows (encode decode emptyToken)
open ReportDigitArithmetic (digit cmpFold)
open FiniteUniformStoppingTree

set_option linter.unusedSimpArgs false
set_option maxRecDepth 12000
set_option maxHeartbeats 6000000

variable {s n d : Nat}
variable {h : Fin n → Bool}

private theorem raw_append (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (rawNext s x e)

private theorem raw_snoc (x : Raw s n) (u : List (Fin n)) (e : Fin n) :
    rawRun x (u++[e])=rawNext s (rawRun x u) e :=
  raw_append x u [e]

private theorem raw_clock (x : Raw s n) (w : List (Fin n)) :
    SequentialMarkClock.run (rawNext s) x w=rawRun x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (rawNext s x e)

private theorem post_run (P : WidthLower s n) (N : 1<n)
    (x : Raw s n) (X : P.Post x) (w : List (Fin n)) :
    P.Post (rawRun x w) := by
  induction w generalizing x with
  | nil => exact X
  | cons e w ih => exact ih _ (P.post_closed N x X e)

/-! The genuine clean command program. Nothing here is a stored
    additional physical bit. The iteration index is a proof witness. -/

inductive Mode where
  | reset
  | choose (j : Nat)
  | compare (j : Nat)
  | publish (j : Nat)
  | advance (j : Nat)
  | width
  deriving DecidableEq

def opcode : Mode → Nat
  | .reset => 0
  | .choose _ => 1
  | .compare _ => 2
  | .publish _ => 3
  | .advance _ => 4
  | .width => 5

def arg0 (s : Nat) : Mode → Nat
  | .publish j => publishArg s j
  | .advance _ => 1
  | _ => 0

def nextMode (L : Nat) : Mode → Mode
  | .reset => .choose 0
  | .choose j => if j<L then .compare j else .width
  | .compare j => .publish j
  | .publish j => .advance j
  | .advance j => .choose (j+1)
  | .width => .reset

def remaining (L : Nat) : Mode → Nat
  | .reset => 4*L+3
  | .choose j => 4*(L-j)+2
  | .compare j => 4*(L-j)+1
  | .publish j => 4*(L-j)
  | .advance j => 4*(L-j)-1
  | .width => 1

def Sem (s L : Nat) (v : Fin L→Data) : Mode → Prop
  | .reset => Finished s L v
  | .choose j => Outer s L v j
  | .compare j | .publish j => j<L ∧ Selected s L v j
  | .advance j => Published s L v j
  | .width => Selected s L v L

theorem op_bound (m : Mode) : opcode m≤5 := by
  cases m <;> simp [opcode]

theorem arg_good (s : Nat) (m : Mode) : FArg (opcode m) (arg0 s m) := by
  cases m with
  | publish j => exact publishArg_bound s j
  | reset => rfl
  | choose j => simp [FArg,opcode,arg0]
  | compare j => simp [FArg,opcode,arg0]
  | advance j => simp [FArg,opcode,arg0]
  | width => rfl

theorem remaining_pos {s L : Nat} {v : Fin L→Data}
    (m : Mode) (H : Sem s L v m) : 0<remaining L m := by
  cases m with
  | reset => simp [remaining]
  | choose j => simp [remaining]
  | compare j => simp [remaining]
  | publish j =>
    have J : j<L := H.1
    simp only [remaining]; omega
  | advance j =>
    have J : j<L := H.bound
    simp only [remaining]; omega
  | width => simp [remaining]

theorem remaining_step {s L : Nat} {v : Fin L→Data}
    (m : Mode) (H : Sem s L v m) (W : m≠.width) :
    remaining L (nextMode L m)+1=remaining L m := by
  cases m with
  | reset => simp [nextMode,remaining]
  | choose j =>
    have J := (show Outer s L v j from H).bound
    by_cases E : j<L <;> simp [nextMode,remaining,E] <;> omega
  | compare j => simp [nextMode,remaining]
  | publish j =>
    have J : j<L := H.1
    simp [nextMode,remaining]; omega
  | advance j =>
    have J : j<L := H.bound
    simp [nextMode,remaining]; omega
  | width => exact False.elim (W rfl)

structure Ready (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (x : Raw s n) : Prop where
  post : P.Post x
  rail : WidthChooseEpoch.Rail S x (opcode m) (.issue (arg0 s m))
  sem : Sem s (d+1) (wordData S x) m
  empty : ∀ i, wire x (site S i)=encode emptyToken

/-- All K are semantically empty, not just no visible F3/F5.
    The initial argument is from the actual root source, especially D2. -/
theorem ready_of (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (x : Raw s n) (X : P.Post x)
    (PC : Controller S x 1 (opcode m))
    (E : ∀ i, wire x (site S i)=encode emptyToken)
    (A : arg0 s m=initialArg (opcode m) (src x S.root).flags.toNat)
    (H : Sem s (d+1) (wordData S x) m) :
    Ready P S m x :=
  ⟨X,⟨arg_good s m,(fun i=>by rw [E i,WidthTokenTransport.empty_codec]; rfl),PC,A⟩,H,E⟩

def ZeroData (S : Sector h d) (x : Raw s n) : Prop :=
  ∀ i : Fin (d+1), (wordData S x i).done=0 ∧
    (wordData S x i).pick=0 ∧ (wordData S x i).count=0

def resetPlan (s L : Nat) (v : Fin L→Data) : Plan s L 0 v where
  arg := fun _=>0
  after := fun i=>{v i with done:=0,pick:=0,count:=0}
  law := by intro i; rfl

/-- Derive the actual per-command plan from the checked data invariant. -/
def plan (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (x : Raw s n) (A : Ready P S m x) :
    Plan s (d+1) (opcode m) (wordData S x) := by
  cases m with
  | reset => exact resetPlan s (d+1) _
  | choose j => exact choosePlan (show Outer s (d+1) _ j from A.sem)
  | compare j => exact comparePlan (show Selected s (d+1) _ j from A.sem.2).count
  | publish j => exact publishPlan A.sem.2
  | advance j => exact advancePlan (show Published s (d+1) _ j from A.sem).count
  | width => exact widthPlan s (d+1) _

theorem plan_initial (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (x : Raw s n) (A : Ready P S m x) :
    arg0 s m=(plan P S m x A).arg 0 := by
  -- CHECK: WidthChooseEpoch.lean:597ff, comparePlan and advancePlan
  -- use the literal low-first fold and carry; proof fields are irrelevant.
  cases m <;> simp [arg0,plan,resetPlan,choosePlan,chooseArg,comparePlan,
    compareArg,cmpFold,publishPlan,advancePlan,carry,widthPlan,Nat.mod_one]

theorem walk_to_clean (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (x : Raw s n) (A : Ready P S m x)
    (w : List (Fin n)) (f : Cursor d)
    (W : Walk P S (opcode m) x (arg0 s m) w f) :
    WidthEpochEntry.Trace P S true x (opcode m) w f := by
  induction W with
  | start X R =>
    have E : WidthEpochEntry.seedCursor S x (opcode m)=.issue (arg0 s m) :=
      congrArg Cursor.issue A.rail.source.2.symm
    exact E ▸ WidthEpochEntry.Trace.seed X A.rail.source.1 (fun _=>A.empty)
  | snoc e W L IH => exact .snoc e IH L

theorem canonical_receipt (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (x y : Raw s n) (A : Ready P S m x)
    (R : Receipt P S (opcode m) (arg0 s m) x y) :
    P.Post y ∧ wordData S y=(plan P S m x A).after ∧ R.a=(plan P S m x A).arg (d+1) ∧
    Controller S y 1 (nextOp (opcode m) (finishArg (opcode m) R.a)) ∧
    (∀ i : Fin (d+1), wire y (site S i)=encode emptyToken) ∧
    (opcode m=2 → (src y S.root).flags.toNat=finishArg (opcode m) R.a) := by
  obtain ⟨w,a,W,E⟩ := R
  subst y
  have G := WidthEpochEntry.Trace.snoc (inlet S) (walk_to_clean P S m x A w _ W) trivial
  have GC : WidthEpochEntry.Trace P S true x (opcode m) (w++[inlet S]) (.consumed a) := by
    simpa [cursorNext] using G
  have I : payload (WidthEpochEntry.seedCursor S x (opcode m))=(plan P S m x A).arg 0 :=
    A.rail.source.2.symm.trans (plan_initial P S m x A)
  have V := WidthEpochEntry.clean_receipt_word P S x (opcode m) (op_bound m)
    (plan P S m x A) I (w++[inlet S]) a GC
  rw [raw_snoc] at V
  refine ⟨V.1.1,V.2.1,V.2.2.1,?_,V.1.2.2.2,V.2.2.2⟩
  cases m <;> simp only [opcode,nextOp,WidthEpochEntry.nextOp,WidthFreshReverse.nextOp,
    WidthOwnerController.nextControl,beq_iff_eq] at V ⊢ <;> exact V.1.2.2.1

/-- Each step at a real matching consume enters the exact next
    boundary. In particular ADVANCE retains the previous PICK bit. -/
theorem next_ready (P : WidthLower s n) (S : Sector P.h d)
    (B : Room s d)
    (m : Mode) (x y : Raw s n) (A : Ready P S m x)
    (R : Receipt P S (opcode m) (arg0 s m) x y) :
    Ready P S (nextMode (d+1) m) y := by
  have V := canonical_receipt P S m x y A R
  have Y := V.1
  cases m with
  | reset =>
    have E : wordData S y=(resetPlan s (d+1) (wordData S x)).after := V.2.1
    have Z : ZeroData S y := by
      intro i
      rw [E]
      exact ⟨rfl,rfl,rfl⟩
    apply ready_of P S (.choose 0) y Y
    · simpa [opcode,WidthChooseEpoch.nextOp] using V.2.2.2.1
    · exact V.2.2.2.2.1
    · rfl
    · exact reset_seed s (d+1) _ Z
  | choose j =>
    have H : Outer s (d+1) (wordData S x) j := A.sem
    have E : wordData S y=chooseData (wordData S x) j := V.2.1
    have Q : R.a=chooseArg j (d+1) := V.2.2.1
    have K := V.2.2.2.1
    rw [Q] at K
    have F : Selected s (d+1) (wordData S y) j := E.symm ▸ choose_selected H
    by_cases J : j<d+1
    · simp only [nextMode,if_pos J]
      exact ready_of P S (.compare j) y Y
        (by simpa [opcode,nextOp,finishArg,chooseArg,J] using K)
        V.2.2.2.2.1 rfl ⟨J,F⟩
    · have E' : j=d+1 := by have := H.bound; omega
      simp only [nextMode,if_neg J]
      exact ready_of P S .width y Y
        (by simpa [opcode,nextOp,finishArg,chooseArg,J] using K)
        V.2.2.2.2.1 rfl (E' ▸ F)
  | compare j =>
    have H : j<d+1 ∧ Selected s (d+1) (wordData S x) j := A.sem
    have E : wordData S y=wordData S x := V.2.1
    have Q : R.a=compareArg s j (d+1) := V.2.2.1
    have F := V.2.2.2.2.2 rfl
    change _ = finishArg 2 R.a at F
    rw [Q,compare_complete B j H.2.bound] at F
    exact ready_of P S (.publish j) y Y (by simpa [opcode,nextOp] using V.2.2.2.1)
      V.2.2.2.2.1 (by simp [arg0,opcode,initialArg,F]) ⟨H.1,E.symm ▸ H.2⟩
  | publish j =>
    have H : j<d+1 ∧ Selected s (d+1) (wordData S x) j := A.sem
    have E : wordData S y=publishData (s:=s) (wordData S x) j := V.2.1
    exact ready_of P S (.advance j) y Y (by simpa [opcode,nextOp] using V.2.2.2.1)
      V.2.2.2.2.1 rfl (E.symm ▸ publish_published H.2 H.1)
  | advance j =>
    have E : wordData S y=advanceData (s:=s) (wordData S x) j := V.2.1
    exact ready_of P S (.choose (j+1)) y Y (by simpa [opcode,nextOp] using V.2.2.2.1)
      V.2.2.2.2.1 rfl (E.symm ▸ advance_outer A.sem)
  | width =>
    have E : wordData S y=widthData (s:=s) (wordData S x) := V.2.1
    exact ready_of P S .reset y Y (by simpa [opcode,nextOp] using V.2.2.2.1)
      V.2.2.2.2.1 rfl (E.symm ▸ width_finished A.sem)

/-! Full displayed projection. BOTH sides of the partial sweep have
    the same correct display in later cycles. No flags-only entrance. -/

def Shadow (s L j : Nat) : BitVec 1 :=
  if j<s+11 then BitVec.ofNat 1 (digit 2 j L) else 0

def Display (s L : Nat) (v : Fin L→Data) : Prop :=
  ∀ i, (v i).inside=bit (i.val<radWidth s) ∧
    (v i).last=bit (i.val+1=radWidth s) ∧ (v i).width=Shadow s L i.val

theorem display_finished {s L : Nat} {v : Fin L→Data} (H : Finished s L v) :
    Display s L v := by
  intro i
  exact ⟨(H.flags i i.isLt).1,(H.flags i i.isLt).2,H.shadow i⟩

theorem plan_display (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (x : Raw s n) (A : Ready P S m x)
    (D : Display s (d+1) (wordData S x)) :
    Display s (d+1) (plan P S m x A).after := by
  intro i
  have F := D i
  cases m with
  | reset => exact F
  | choose j => exact F
  | compare j => exact F
  | publish j =>
    -- CHECK: WidthChooseEpoch.lean:724ff; publishData updates only
    -- the unique picked site's two displayed flags, with true j.
    by_cases E : i.val=j
    · simp [plan,publishPlan,publishData,E,F.2.2]
    · simpa [plan,publishPlan,publishData,E] using F
  | advance j =>
    by_cases E : i.val<s+11 <;>
      simpa [plan,advancePlan,advanceData,E] using F
  | width =>
    exact display_finished (width_finished
      (show Selected s (d+1) (wordData S x) (d+1) from A.sem)) i

theorem walk_display (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (x : Raw s n)
    (A : Ready P S m x) (D : Display s (d+1) (wordData S x))
    (w : List (Fin n)) (f : Cursor d)
    (W : Walk P S (opcode m) x (arg0 s m) w f) :
    Display s (d+1) (wordData S (rawRun x w)) := by
  have I : payload (WidthEpochEntry.seedCursor S x (opcode m))=(plan P S m x A).arg 0 :=
    A.rail.source.2.symm.trans (plan_initial P S m x A)
  have H := WidthEpochEntry.trace_sweep P S x (opcode m) (op_bound m)
    (plan P S m x A) I w f (walk_to_clean P S m x A w f W)
  have E := plan_display P S m x A D
  intro i
  rw [H.data i]
  split
  · exact E i
  · exact D i

theorem receipt_display (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (x y : Raw s n)
    (A : Ready P S m x) (D : Display s (d+1) (wordData S x))
    (R : Receipt P S (opcode m) (arg0 s m) x y) :
    Display s (d+1) (wordData S y) := by
  have H := canonical_receipt P S m x y A R
  rw [H.2.1]
  exact plan_display P S m x A D

/-! Cursor completion is the actual inlet from old back 0.
    The consumed state itself must not be stepped as a live command. -/

theorem dead_cursor {f : Cursor d} (H : ¬WidthChooseEpoch.live f) :
    ∃ a,f=.consumed a := by
  cases f with
  | issue a => exact False.elim (H trivial)
  | out k a => exact False.elim (H trivial)
  | back k a => exact False.elim (H trivial)
  | consumed a => exact ⟨a,rfl⟩

theorem consume_iff_old (P : WidthLower s n) (S : Sector P.h d)
    (op : Nat) (x : Raw s n) (e : Fin n) (f : Cursor d) (a : Nat)
    (H : WidthChooseEpoch.live f)
    (E : cursorNext P S op x e f=.consumed a) :
    f=.back 0 a ∧ e=inlet S := by
  cases f with
  | issue b =>
    by_cases I : e=inlet S <;> simp [cursorNext,I] at E
  | out k b =>
    by_cases I : e=site S k <;> simp [cursorNext,I] at E
    split at E <;> contradiction
  | back k b =>
    by_cases Z : k.val=0
    · have K : k=0 := Fin.ext Z
      subst k
      by_cases I : e=inlet S
      · have J : b=a := by simpa [cursorNext,I] using E
        subst b
        exact ⟨rfl,I⟩
      · simp [cursorNext,I] at E
    · simp [cursorNext,Z] at E
      split at E <;> contradiction
  | consumed b => exact False.elim H

/-- Recognizable completed clean cycle. Its own full ready RESET0
    boundary includes the entire finished data and E rail. -/
def CycleCut (P : WidthLower s n) (S : Sector P.h d) (x : Raw s n) : Prop :=
  Ready P S .reset x

def WidthGood (P : WidthLower s n) (S : Sector P.h d) (x : Raw s n) : Prop :=
  ∃ seed : Raw s n, CycleCut P S seed ∧ ∃ w : List (Fin n), rawRun seed w=x

theorem cut_good (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : CycleCut P S x) : WidthGood P S x :=
  ⟨x,X,[],rfl⟩

theorem width_good_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (e : Fin n) (X : WidthGood P S x) :
    WidthGood P S (rawNext s x e) := by
  obtain ⟨z,Z,w,E⟩ := X
  exact ⟨z,Z,w++[e],by rw [raw_snoc,E]⟩

/-- The loop is a union of current authentic command flights, each
    from its own proved ready boundary and correct display. -/
def SafeFlight (P : WidthLower s n) (S : Sector P.h d) (y : Raw s n) : Prop :=
  ∃ (m : Mode) (x : Raw s n) (w : List (Fin n)) (f : Cursor d),
    Ready P S m x ∧ Display s (d+1) (wordData S x) ∧
    Walk P S (opcode m) x (arg0 s m) w f ∧ WidthChooseEpoch.live f ∧
    rawRun x w=y

theorem safe_start (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (x : Raw s n) (A : Ready P S m x)
    (D : Display s (d+1) (wordData S x)) : SafeFlight P S x :=
  ⟨m,x,[],.issue (arg0 s m),A,D,.start A.post A.rail,trivial,rfl⟩

theorem safe_step (P : WidthLower s n) (S : Sector P.h d)
    (B : Room s d)
    (y : Raw s n) (H : SafeFlight P S y) (e : Fin n) :
    SafeFlight P S (rawNext s y e) := by
  obtain ⟨m,x,w,f,A,D,W,L,E⟩ := H
  subst y
  let g := cursorNext P S (opcode m) (rawRun x w) e f
  by_cases K : WidthChooseEpoch.live g
  · exact ⟨m,x,w++[e],g,A,D,.snoc e W L,K,raw_snoc x w e⟩
  · obtain ⟨a,G⟩ := dead_cursor K
    obtain ⟨F,I⟩ := consume_iff_old P S (opcode m) (rawRun x w) e f a L G
    subst f
    subst e
    let R : Receipt P S (opcode m) (arg0 s m) x
        (rawNext s (rawRun x w) (inlet S)) := ⟨w,a,W,rfl⟩
    exact safe_start P S (nextMode (d+1) m) _ (next_ready P S B m x _ A R)
      (receipt_display P S m x _ A D R)

theorem safe_run (P : WidthLower s n) (S : Sector P.h d)
    (B : Room s d)
    (x : Raw s n) (H : SafeFlight P S x) (w : List (Fin n)) :
    SafeFlight P S (rawRun x w) := by
  induction w generalizing x with
  | nil => exact H
  | cons e w ih => exact ih _ (safe_step P S B x H e)

theorem width_good_flags (P : WidthLower s n) (S : Sector P.h d)
    (hs : 6≤s)
    (y : Raw s n) (Y : WidthGood P S y) :
    P.Post y ∧ Display s (d+1) (wordData S y) := by
  obtain ⟨x,X,w,rfl⟩ := Y
  have N : 1<n := by have := S.room; omega
  have B := room_of_post P S x X.post hs
  have D : Display s (d+1) (wordData S x) := display_finished X.sem
  obtain ⟨m,z,v,f,A,F,W,_,E⟩ :=
    safe_run P S B x (safe_start P S .reset x X D) w
  exact ⟨post_run P N x X.post w,E ▸ walk_display P S m z A F v f W⟩

/-! Rank for a clean command, before any outer-loop accounting. -/

def commandRank {d : Nat} : Cursor d→Nat
  | .issue _ => 2*(d+1)+1
  | .out k _ => 2*(d+1)-k.val
  | .back k _ => k.val+1
  | .consumed _ => 0

theorem command_rank_pos (f : Cursor d) (F : WidthChooseEpoch.live f) :
    0<commandRank f := by
  cases f with
  | issue a => simp [commandRank]
  | out k a => have := k.isLt; simp only [commandRank]; omega
  | back k a => simp [commandRank]
  | consumed a => exact False.elim F

theorem command_rank_step (P : WidthLower s n) (S : Sector P.h d)
    (op : Nat) (x : Raw s n) (f : Cursor d) (F : WidthChooseEpoch.live f) :
    ∃ b : Fin n, ∀ e : Fin n,
      commandRank (cursorNext P S op x e f)≤commandRank f ∧
      (e=b→commandRank (cursorNext P S op x e f)<commandRank f) := by
  cases f with
  | consumed a => exact False.elim F
  | issue a =>
    refine ⟨inlet S,fun e=>?_⟩
    by_cases E : e=inlet S <;> simp [cursorNext,commandRank,E]
  | out k a =>
    refine ⟨site S k,fun e=>?_⟩
    have K := k.isLt
    by_cases E : e=site S k
    · subst e
      by_cases J : k.val<d
      · simp only [cursorNext,if_true,dif_pos J,commandRank,true_implies]
        omega
      · simp only [cursorNext,if_true,dif_neg J,commandRank,true_implies]
        omega
    · simp [cursorNext,E]
  | back k a =>
    by_cases J : k.val=0
    · refine ⟨inlet S,fun e=>?_⟩
      by_cases E : e=inlet S <;> simp [cursorNext,J,E,commandRank]
    · let b : Fin (d+1) := ⟨k.val-1,by have := k.isLt; omega⟩
      refine ⟨site S b,fun e=>?_⟩
      by_cases E : e=site S b
      · subst e
        simp [cursorNext,J,b,commandRank]
        omega
      · have E' : e ≠ site S (⟨k.val-1,by have := k.isLt; omega⟩ : Fin (d+1)) := E
        simp [cursorNext,J,E',E]

/-! Actual-tape state. No auxiliary observer overwrites a raw site.
    Every intermediate tape may already contain earlier-stage marks. -/

structure Tape (s n : Nat) where
  raw : Raw s n
  marks : List (Fin n)

def tapeStep (z : Tape s n) (e : Fin n) : Tape s n :=
  ⟨rawNext s z.raw e,z.marks++[e]⟩

def tapeStart (x : Raw s n) : Tape s n := ⟨x,[]⟩

theorem tape_project (z : Tape s n) (e : Fin n) :
    (tapeStep z e).raw=rawNext s z.raw e := rfl

theorem tape_run (z : Tape s n) (w : List (Fin n)) :
    SequentialMarkClock.run tapeStep z w=
      ⟨rawRun z.raw w,z.marks++w⟩ := by
  induction w generalizing z with
  | nil => cases z; simp [SequentialMarkClock.run,rawRun,BStarResetSchedule.run]
  | cons e w ih =>
    rw [SequentialMarkClock.run,ih]
    simp [tapeStep,rawRun,BStarResetSchedule.run,List.append_assoc]

def Extension (z y : Tape s n) : Prop :=
  ∃ w : List (Fin n), y.marks=z.marks++w ∧ y.raw=rawRun z.raw w

theorem extension_trans {z y v : Tape s n}
    (H : Extension z y) (K : Extension y v) : Extension z v := by
  obtain ⟨u,U,X⟩ := H
  obtain ⟨w,W,Y⟩ := K
  exact ⟨u++w,by rw [W,U,List.append_assoc],by rw [Y,X,raw_append]⟩

/-- Contiguous actual Receipt. The final inlet mark is included in
    this segment and occurs at the actual endpoint, not some prefix
    before an unrelated later source launch. -/
def ReceiptAt (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (z y : Tape s n) : Prop :=
  ∃ R : Receipt P S (opcode m) (arg0 s m) z.raw y.raw,
    y.marks=z.marks++(R.tape++[inlet S])

theorem receipt_extension (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (z y : Tape s n) (R : ReceiptAt P S m z y) :
    Extension z y := by
  obtain ⟨r,E⟩ := R
  exact ⟨r.tape++[inlet S],E,by rw [raw_snoc]; exact r.endpoint⟩

theorem command_expected (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (z : Tape s n) (A : Ready P S m z.raw) :
    L4.IIDExpectedHittingTimeAtMost tapeStep
      (ReceiptAt P S m z) z (n*(2*(d+1)+1)) := by
  let I := fun (y : Tape s n) (r : Nat) =>
    ∃ (w : List (Fin n)) (f : Cursor d),
      y.marks=z.marks++w ∧ y.raw=rawRun z.raw w ∧
      Walk P S (opcode m) z.raw (arg0 s m) w f ∧
      WidthChooseEpoch.live f ∧ r=commandRank f
  have pos (y : Tape s n) (r : Nat) (H : I y r) : 0<r := by
    obtain ⟨w,f,_,_,_,L,E⟩ := H
    rw [E]
    exact command_rank_pos f L
  have move (y : Tape s n) (r : Nat) (H : I y r) :
      ∃ b : Fin n, ∀ e : Fin n,
        ReceiptAt P S m z (tapeStep y e) ∨
        ∃ r',I (tapeStep y e) r' ∧ r'≤r ∧ (e=b→r'<r) := by
    obtain ⟨w,f,M,Y,W,L,E⟩ := H
    subst r
    obtain ⟨b,B⟩ := command_rank_step P S (opcode m) (rawRun z.raw w) f L
    refine ⟨b,fun e=>?_⟩
    let g := cursorNext P S (opcode m) (rawRun z.raw w) e f
    by_cases G : WidthChooseEpoch.live g
    · right
      refine ⟨commandRank g,⟨w++[e],g,?_,?_,.snoc e W L,G,rfl⟩,
        (B e).1,(B e).2⟩
      · change y.marks++[e]=_
        rw [M,List.append_assoc]
      · change rawNext s y.raw e=_
        rw [Y,raw_snoc]
    · left
      obtain ⟨a,K⟩ := dead_cursor G
      obtain ⟨F,J⟩ := consume_iff_old P S (opcode m) (rawRun z.raw w) e f a L K
      subst f
      subst e
      let R : Receipt P S (opcode m) (arg0 s m) z.raw (tapeStep y (inlet S)).raw :=
        ⟨w,a,W,by change rawNext s y.raw _=_; rw [Y]⟩
      exact ⟨R,by change y.marks++[inlet S]=_; rw [M,List.append_assoc]⟩
  have H := ResetReturnIID.iid_of_relational_rank tapeStep (ReceiptAt P S m z)
    I pos move z (2*(d+1)+1)
    (.inr ⟨[],.issue (arg0 s m),by simp,rfl,.start A.post A.rail,trivial,rfl⟩)
  exact (MonitorRawBridge.height_iff_row _ _ _ _).mp H

/-! The predecessor's actual BEGIN receipt. Its arbitrary prefix may
    contain dirty traffic; only the new launch and matching return
    earn the clean zero-data seed. This is item 2, not item 4/5. -/
def BeginReceipt (P : WidthLower s n) (S : Sector P.h d)
    (z y : Tape s n) : Prop :=
  ∃ pre w : List (Fin n), ∃ op k paid : Nat,
    op≤5 ∧ WidthEpochEntry.FirstBegin P S (rawRun z.raw pre) op w k paid ∧
    y.marks=z.marks++(pre++w) ∧ y.raw=rawRun z.raw (pre++w)

theorem begin_extension (P : WidthLower s n) (S : Sector P.h d)
    (z y : Tape s n) (R : BeginReceipt P S z y) : Extension z y := by
  obtain ⟨a,w,_,_,_,_,_,M,Y⟩ := R
  exact ⟨a++w,M,Y⟩

theorem begin_ready (P : WidthLower s n) (S : Sector P.h d)
    (z y : Tape s n) (R : BeginReceipt P S z y) :
    Ready P S (.choose 0) y.raw := by
  obtain ⟨a,w,op,k,paid,O,T,_,Y⟩ := R
  have E : y.raw=rawRun (rawRun z.raw a) w := by rw [Y,raw_append]
  rw [E]
  have F := WidthEpochEntry.first_begin_facts P S (rawRun z.raw a) op O w k paid T
  have H := F.2.2.1
  exact ready_of P S (.choose 0) _ H.1 H.2.2.1 H.2.2.2 rfl
    (reset_seed s (d+1) _ F.2.2.2.1)

/-- Explicit dependencies from items 1–3. The clock must be uniform
    over every post-cache actual stopped state, not a preferred seed.
    In item 2 a prefix-labelled observer may be lifted to Tape by
    concatenating the already present marks; no extra cost. -/
structure Predecessor (P : WidthLower s n) (S : Sector P.h d) : Prop where
  begin_mean : ∀ z : Tape s n,P.Post z.raw →
    L4.IIDExpectedHittingTimeAtMost tapeStep (BeginReceipt P S z)
      z (12*n*(d+2)^2)

/-! The contiguous command chain from the actual BEGIN to the actual
    final WIDTH5 consume. The final constructor forbids another cycle. -/

inductive Finish (P : WidthLower s n) (S : Sector P.h d) :
    Mode → Tape s n → Tape s n → Prop where
  | last {z y} : ReceiptAt P S .width z y → Finish P S .width z y
  | more {m z v y} : m≠.width → ReceiptAt P S m z v →
      Finish P S (nextMode (d+1) m) v y → Finish P S m z y

theorem finish_extension (P : WidthLower s n) (S : Sector P.h d)
    (m : Mode) (z y : Tape s n) (F : Finish P S m z y) :
    Extension z y := by
  induction F with
  | last R => exact receipt_extension P S _ _ _ R
  | more H R F ih => exact extension_trans (receipt_extension P S _ _ _ R) ih

theorem finish_cut (P : WidthLower s n) (S : Sector P.h d)
    (B : Room s d)
    (m : Mode) (z y : Tape s n) (F : Finish P S m z y)
    (A : Ready P S m z.raw) : CycleCut P S y.raw := by
  induction F with
  | last R =>
    obtain ⟨r,_⟩ := R
    exact next_ready P S B .width _ _ A r
  | more H R F ih =>
    obtain ⟨r,_⟩ := R
    exact ih (next_ready P S B _ _ _ A r)

theorem finish_expected (P : WidthLower s n) (S : Sector P.h d)
    (B : Room s d)
    (r : Nat) (m : Mode) (z : Tape s n)
    (A : Ready P S m z.raw) (E : remaining (d+1) m=r) :
    L4.IIDExpectedHittingTimeAtMost tapeStep (Finish P S m z) z
      ((n*(2*(d+1)+1))*r) := by
  induction r generalizing m z with
  | zero =>
    have H := remaining_pos m A.sem
    omega
  | succ r ih =>
    by_cases W : m=.width
    · subst m
      have Z : r=0 := by simp [remaining] at E; omega
      subst r
      intro t
      have H := command_expected P S .width z A t
      exact Nat.le_trans (RankRenewal.cost_mono_target (next:=tapeStep)
        (ReceiptAt P S .width z) (Finish P S .width z)
        (fun _ R=>.last R) t z) (by simpa using H)
    · let K := n*(2*(d+1)+1)
      have D := remaining_step m A.sem W
      have R : remaining (d+1) (nextMode (d+1) m)=r := by omega
      rw [Nat.mul_succ,Nat.add_comm (K*r) K]
      apply AllSizeComposition.additive_stage tapeStep (ReceiptAt P S m z)
        (Finish P S m z) K (K*r) z (command_expected P S m z A)
      intro v V t
      obtain ⟨rec,eq⟩ := V
      have A' := next_ready P S B m z.raw v.raw A rec
      exact Nat.le_trans (RankRenewal.cost_mono_target (next:=tapeStep)
        (Finish P S (nextMode (d+1) m) v) (Finish P S m z)
        (fun _ F=>.more W ⟨rec,eq⟩ F) t v) (ih _ _ A' R t)

def CycleReceipt (P : WidthLower s n) (S : Sector P.h d)
    (z y : Tape s n) : Prop :=
  ∃ b : Tape s n, BeginReceipt P S z b ∧ Finish P S (.choose 0) b y

theorem cycle_extension (P : WidthLower s n) (S : Sector P.h d)
    (z y : Tape s n) (R : CycleReceipt P S z y) : Extension z y := by
  obtain ⟨b,B,F⟩ := R
  exact extension_trans (begin_extension P S z b B) (finish_extension P S _ _ _ F)

theorem cycle_cut (P : WidthLower s n) (S : Sector P.h d)
    (hs : 6≤s)
    (z y : Tape s n) (R : CycleReceipt P S z y) :
    CycleCut P S y.raw := by
  obtain ⟨b,B,F⟩ := R
  have A := begin_ready P S z b B
  exact finish_cut P S (room_of_post P S b.raw A.post hs) _ _ _ F A

theorem suffix_budget (L : Nat) :
    (2*L+1)*(4*L+2)≤8*(L+1)^2 := by
  calc
    _ ≤ (2*(L+1))*(4*(L+1)) := Nat.mul_le_mul (by omega) (by omega)
    _ = _ := by
      rw [Nat.pow_two]
      calc
        2*(L+1)*(4*(L+1)) = (2*4)*((L+1)*(L+1)) := by ac_rfl
        _ = _ := rfl

theorem owner_cycle_mean (P : WidthLower s n) (S : Sector P.h d)
    (C : Predecessor P S) (hs : 6≤s)
    (z : Tape s n) (X : P.Post z.raw) :
    L4.IIDExpectedHittingTimeAtMost tapeStep (CycleReceipt P S z)
      z (20*n*(d+2)^2) := by
  have E : 20*n*(d+2)^2=12*n*(d+2)^2+8*n*(d+2)^2 := by
    rw [←Nat.add_mul,←Nat.add_mul]
  rw [E]
  apply AllSizeComposition.additive_stage tapeStep (BeginReceipt P S z)
    (CycleReceipt P S z) _ _ z (C.begin_mean z X)
  intro b B t
  have A := begin_ready P S z b B
  have H := finish_expected P S (room_of_post P S b.raw A.post hs)
    (4*(d+1)+2) (.choose 0) b A (by simp [remaining])
  have M : n*(2*(d+1)+1)*(4*(d+1)+2)≤8*n*(d+2)^2 := by
    calc
      _ = n*((2*(d+1)+1)*(4*(d+1)+2)) := by rw [Nat.mul_assoc]
      _ ≤ n*(8*((d+1)+1)^2) := Nat.mul_le_mul_left _ (suffix_budget (d+1))
      _ = _ := by ac_rfl
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=tapeStep)
    (Finish P S (.choose 0) b) (CycleReceipt P S z)
    (fun y Y=>⟨b,B,Y⟩) t b) (Nat.le_trans (H t) (Nat.mul_le_mul_right _ M))

/-- The actual raw cut mean, projected from the genuine history. -/
theorem width_cycle_cut_uniform_mean (P : WidthLower s n) (S : Sector P.h d)
    (C : Predecessor P S) (hs : 6≤s) (x : Raw s n) (X : P.Post x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (CycleCut P S) x
      (20*n*(d+2)^2) := by
  have H := owner_cycle_mean P S C hs (tapeStart x) X
  refine MonitorRawBridge.expected_of_monitor_words (rawNext s) tapeStep
    (fun z=>z.raw) (CycleReceipt P S (tapeStart x)) (CycleCut P S)
    tape_project (tapeStart x) ?_ _
    ((MonitorRawBridge.height_iff_row _ _ _ _).mpr H)
  intro w D
  have R := cycle_cut P S hs _ _ D
  rw [MonitorRawBridge.run_project (rawNext s) tapeStep (fun z=>z.raw)
    tape_project (tapeStart x) w] at R
  exact R
#print axioms canonical_receipt
#print axioms next_ready
#print axioms plan_display
#print axioms safe_step
#print axioms width_good_flags
#print axioms width_good_step
#print axioms command_expected
#print axioms begin_ready
#print axioms finish_cut
#print axioms finish_expected
#print axioms owner_cycle_mean
#print axioms width_cycle_cut_uniform_mean

end L4.WidthCycleEpoch

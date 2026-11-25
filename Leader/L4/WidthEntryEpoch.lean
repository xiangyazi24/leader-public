import Leader.L4.WidthForwardEpoch
import Leader.L4.WidthFreshReverse
import Leader.L4.WidthChooseEpoch
import Leader.L4.WidthRawWaitClock
import Leader.L4.AllSizeComposition
import Leader.L4.MonitorRawBridge

namespace L4.WidthEpochEntry

open AllSizeProtocol PhysicalCustody
open BStarH6WordChart (oldH6)
open WidthSectorGeometry ShortResetChart WidthWaitDrain
open WidthFreshForward
open WidthByteRows (Token encode decode emptyToken trailToken finish)
open BStarWidthTransferDepart (Data execute)
open WidthChooseEpoch (Cursor spent payload live railToken Rail cursorNext wordData
  raw_data_at Departs)

set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

variable {s n d : Nat} {h : Fin n → Bool}

private theorem roomN (S : Sector h d) : 1<n := by
  have H := S.room
  omega

private theorem raw_snoc (x : Raw s n) (w : List (Fin n)) (e : Fin n) :
    rawRun x (w++[e])=rawNext s (rawRun x w) e := by
  induction w generalizing x with
  | nil => rfl
  | cons a w IH => exact IH (rawNext s x a)

private theorem raw_append (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u IH => exact IH (rawNext s x e)

/-! 1. Controller entrance. No asserted equality between WAIT exit
    and a legitimate ISSUE. -/

def Legit (S : Sector h d) (x : Raw s n) : Prop :=
  ∃ op, op≤5 ∧ Controller S x 1 op

abbrev Ended (S : Sector h d) (x : Raw s n) : Prop :=
  WidthRawWaitClock.WaitEnded (s:=s) S.root x

private theorem ended_src (S : Sector h d) (x : Raw s n) :
    Ended S x ↔
      ¬((src x S.root).phase.toNat=2 ∧ (src x S.root).op.toNat≤5) := by
  -- CHECK: WidthRawWaitClock:219–222; BStarWidthTransfer:16–23;
  -- WidthOwnerController:8–11. Same suffix-field projections.
  rfl

/-- Actual invalid old phase/op, not just an inherited invalid token. -/
theorem invalid_inlet (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (E : Ended S x) (I : ¬Legit S x) :
    Controller S (rawNext s x (inlet S)) 1 0 := by
  let u := src x S.root
  have W : ¬(u.phase.toNat=2 ∧ u.op.toNat≤5) := (ended_src S x).mp E
  have J : ¬(u.phase.toNat=1 ∧ u.op.toNat≤5) := by
    intro H
    exact I ⟨u.op.toNat,H.2,H.1,rfl⟩
  have C : u.phase.toNat<4 := u.phase.isLt
  have B : u.op.toNat>5 ∨ u.phase.toNat=0 ∨ u.phase.toNat=3 := by
    omega
  have R := door_source P S x X
  unfold Controller
  rw [R]
  change (BStarWidthTransferPair.rightSource u).phase.toNat=1 ∧
    (BStarWidthTransferPair.rightSource u).op.toNat=0
  -- CHECK: BStarWidthTransfer:35–51 and
  -- BStarWidthTransferPair:47–50,160–164; restart is private but reducible.
  rcases B with B|B|B <;>
    simp [BStarWidthTransferPair.rightSource,BStarWidthTransferPair.holds,
      BStarWidthTransfer.door,B] <;> decide

theorem nondoor_ended (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (E : Ended S x) (e : Fin n)
    (N : e≠inlet S) : Ended S (rawNext s x e) := by
  have R := nondoor_control P S rfl x X e N
  rw [ended_src] at E ⊢
  rw [R.1,R.2]
  exact E

theorem nondoor_legit (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (I : Legit S x) (e : Fin n)
    (N : e≠inlet S) : Legit S (rawNext s x e) := by
  obtain ⟨op,O,C⟩ := I
  exact ⟨op,O,nondoor_controller P S x X 1 op C e N⟩

/-- Reuse the checked WAIT exit, retaining Post at the cut.
    Post must not be dropped in the second-stage clock. -/
theorem wait_post_mean (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun y=>P.Post y ∧ Ended S y) x (4*n*(d+1)^2) := by
  let A := fun y : Raw s n=>P.Post y ∧ Ended S y
  have M := WidthRawWaitClock.expected_exit_closed S P.Post
    (fun y Y=>P.frozen y Y.1)
    (fun y e Y=>P.post_closed (roomN S) y Y e) x X
  have eq (t : Nat) (y : Raw s n) (Y : P.Post y) :
      Height.iidHitCost (rawNext s) A t y =
        Height.iidHitCost (rawNext s) (Ended S) t y := by
    induction t generalizing y with
    | zero => rfl
    | succ t IH =>
      by_cases B : Ended S y
      · have C : A y := ⟨Y,B⟩
        simp [Height.iidHitCost,B,C]
      · have C : ¬A y := fun H=>B H.2
        simp only [Height.iidHitCost,if_neg B,if_neg C]
        congr 2
        apply congrArg List.ofFn
        funext e
        exact IH _ (P.post_closed (roomN S) y Y e)
  apply (MonitorRawBridge.height_iff_row (rawNext s) A x _).mp
  intro t
  rw [eq t x X]
  exact M t

theorem ended_issue_mean (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (E : Ended S x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun y=>P.Post y ∧ Legit S y) x n := by
  let Stop := fun y : Raw s n=>P.Post y ∧ Legit S y
  let Live := fun (y : Raw s n) (r : Nat)=>
    P.Post y ∧ Ended S y ∧ ¬Legit S y ∧ r=1
  have move (y : Raw s n) (r : Nat) (Y : Live y r) :
      ∃ b : Fin n, ∀ e,
        Stop (rawNext s y e) ∨ ∃ r',Live (rawNext s y e) r' ∧
          r'≤r ∧ (e=b → r'<r) := by
    refine ⟨inlet S,fun e=>?_⟩
    have Z := P.post_closed (roomN S) y Y.1 e
    by_cases H : e=inlet S
    · subst e
      exact .inl ⟨Z,0,by omega,invalid_inlet P S y Y.1.1 Y.2.1 Y.2.2.1⟩
    · by_cases I : Legit S (rawNext s y e)
      · exact .inl ⟨Z,I⟩
      · exact .inr ⟨1,⟨Z,nondoor_ended P S y Y.1.1 Y.2.1 e H,I,rfl⟩,
          by have := Y.2.2.2; omega,fun F=>False.elim (H F)⟩
  have start : Stop x ∨ Live x 1 := by
    by_cases I : Legit S x
    · exact .inl ⟨X,I⟩
    · exact .inr ⟨X,E,I,rfl⟩
  have M := ResetReturnIID.iid_of_relational_rank (rawNext s) Stop Live
    (fun _ r R=>by have := R.2.2.2; omega) move x 1 start
  exact (MonitorRawBridge.height_iff_row (rawNext s) Stop x n).mp
    (by simpa using M)

theorem arbitrary_issue_mean (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun y=>P.Post y ∧ Legit S y) x (4*n*(d+1)^2+n) := by
  exact AllSizeComposition.additive_stage _ _ _ _ _ x
    (wait_post_mean P S x X)
    (fun y Y=>ended_issue_mean P S y Y.1 Y.2)

/-! 2. Exact flight adapter. Retain the final F argument through Back;
    the literal D uses finishArg, and only the real inlet consumes it. -/

abbrev nextOp := WidthFreshReverse.nextOp

def seedCursor (S : Sector h d) (x : Raw s n) (op : Nat) : Cursor d :=
  .issue (initialArg op (src x S.root).flags.toNat)

def Dirty (S : Sector h d) (x : Raw s n) (op : Nat) : Cursor d → Prop
  | .issue a =>
    Controller S x 1 op ∧ a=initialArg op (src x S.root).flags.toNat ∧ FArg op a
  | .out k a => Front S x op k.val a
  | .back k a => FArg op a ∧ WidthFreshReverse.Back S x op k.val (finishArg op a)
  | .consumed a => FArg op a ∧ WidthFreshReverse.Drained S x op (finishArg op a)

theorem dirty_seed (S : Sector h d) (x : Raw s n) (op : Nat)
    (O : op≤5) (I : Controller S x 1 op) :
    Dirty S x op (seedCursor S x op) :=
  ⟨I,rfl,initial_good op _ O (src x S.root).flags.isLt⟩

/-- A private literal expression, definitionally sourceStep.
    Naming its preparation publicly here avoids inaccessible private
    prep and does not change any protocol transition. -/
private def prep' (h : Bool) (u : BStarWidthTransfer.Source) : BStarWidthTransfer.Source :=
  let t := decode u.token
  let z := if h then u else {u with phase:=1,op:=0,flags:=0}
  if t.fault then {z with token:=encode t} else z

private def source' (c r i : Nat) (h : Pair Bool)
    (u v : BStarWidthTransfer.Source) (data : Data) : Pair BStarWidthTransfer.Source :=
  let f := decode u.token
  let b := decode v.token
  let u' := prep' h.1 u
  let v' := prep' h.2 v
  let right := BStarWidthTransferPair.rightSource v
  if f.tag==2 then
    let t := (execute c r i data f).2
    if h.2 then ({u' with token:=encode (finish t)},right)
    else ({u' with token:=16384},{v' with token:=encode t})
  else if h.2 then
    (if f.tag==1 then {u' with token:=0} else u',right)
  else if b.tag==3 then ({u' with token:=encode b},{v' with token:=0})
  else if f.tag==1 && b.tag==0 then ({u' with token:=0},v')
  else (u',v')

private theorem source'_eq (c r i : Nat) (h : Pair Bool)
    (u v : BStarWidthTransfer.Source) (data : Data) :
    sourceStep c r i h u v data=source' c r i h u v data := rfl

private theorem prep_flags (u : BStarWidthTransfer.Source) : (prep' true u).flags=u.flags := by
  unfold prep'
  simp only [if_true]
  split <;> rfl

private theorem left_flags (c r i : Nat) (h : Bool)
    (u v : BStarWidthTransfer.Source) (data : Data) :
    (sourceStep c r i (true,h) u v data).1.flags=u.flags := by
  rw [source'_eq]
  unfold source'
  dsimp only
  split
  · split <;> exact prep_flags u
  · split
    · split <;> exact prep_flags u
    · split
      · exact prep_flags u
      · split <;> exact prep_flags u

/-- Root flags hold off the inlet, including the actual outgoing F.
    This is needed at ISSUE3; phase/op preservation alone is too weak. -/
theorem nondoor_flags (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (e : Fin n) (E : e≠inlet S) :
    (src (rawNext s x e) S.root).flags=(src x S.root).flags := by
  by_cases K : e=S.root
  · subst e
    have R := (raw_sources P (roomN S) x X S.root).1
    unfold pairSources at R
    rw [S.here] at R
    rw [R]
    exact left_flags _ _ _ _ _ _ _
  · have J : S.root≠rightNeighbor e := by
      intro A
      apply E
      apply ShortChartOwnership.right_injective
      exact A.symm.trans (inlet_eq S).symm
    rw [remote_src x e S.root (Ne.symm K) J]

theorem dirty_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op : Nat) (O : op≤5)
    (f : Cursor d) (A : Dirty S x op f) (H : live f) (e : Fin n) :
    Dirty S (rawNext s x e) op (cursorNext P S op x e f) := by
  cases f with
  | consumed a => exact False.elim H
  | issue a =>
    rcases A with ⟨I,E,G⟩
    by_cases J : e=inlet S
    · subst e
      simp only [cursorNext,if_true]
      change Front S (rawNext s x (inlet S)) op 0 a
      rw [E]
      exact source_issue_fresh P S x X.1 op O I
    · simp only [cursorNext,if_neg J,Dirty]
      exact ⟨nondoor_controller P S x X.1 1 op I e J,
        by rw [nondoor_flags P S x X.1 e J]; exact E,G⟩
  | out k a =>
    have W := generated_forward_one_mark P S x X.1 op O
      (.out k.val a) A (by trivial) e
    by_cases J : e=site S k
    · subst e
      by_cases K : k.val<d
      · have B : k.val≠d := by omega
        -- CHECK: next and cursorNext.
        -- site S k is definitionally nextAt S.root k.val.
        simpa [cursorNext,WidthFreshForward.next,Active,Dirty,site,K,B] using W
      · have B : k.val=d := by have := k.isLt; omega
        have T : Turn S (rawNext s x (site S k)) op
            (finishArg op (advancedArg P x (site S k) op a)) := by
          simpa [WidthFreshForward.next,Active,site,B] using W
        simp only [cursorNext,if_true,dif_neg K,Dirty]
        refine ⟨(advanced_good P x (site S k) op a O A.arg).2,?_⟩
        simpa only [B] using WidthFreshReverse.turn_back S _ op _ T
    · have J' : e≠nextAt S.root k.val := J
      simpa [cursorNext,WidthFreshForward.next,Active,Dirty,J,J'] using W
  | back k a =>
    rcases A with ⟨G,B⟩
    have W := WidthFreshReverse.step_active P S x X.1 op k.val
      (finishArg op a) O B e
    by_cases Z : k.val=0
    · by_cases I : e=inlet S
      · simp [cursorNext,Z,I,WidthFreshReverse.next,WidthFreshReverse.nominate,
          WidthFreshReverse.At] at W ⊢
        exact ⟨G,W⟩
      · simp [cursorNext,Z,I,WidthFreshReverse.next,WidthFreshReverse.nominate,
          WidthFreshReverse.At] at W ⊢
        exact ⟨G,by simpa only [Z] using W⟩
    · let j : Fin (d+1) := ⟨k.val-1,by have := k.isLt; omega⟩
      by_cases I : e=site S j
      · have J : e=nextAt S.root (k.val-1) := I
        simpa [cursorNext,Z,j,I,Dirty] using
          (show FArg op a ∧ WidthFreshReverse.Back S (rawNext s x e) op
            (k.val-1) (finishArg op a) from
            ⟨G,by simpa [WidthFreshReverse.next,WidthFreshReverse.nominate,
              Z,J,WidthFreshReverse.At] using W⟩)
      · have J : e≠nextAt S.root (k.val-1) := I
        simpa [cursorNext,Z,j,I,Dirty] using
          (show FArg op a ∧ WidthFreshReverse.Back S (rawNext s x e) op
            k.val (finishArg op a) from
            ⟨G,by simpa [WidthFreshReverse.next,WidthFreshReverse.nominate,
              Z,J,WidthFreshReverse.At] using W⟩)

/-! 3. Canonical clean suffix. No Rail assumption is made for the
    first dirty flight. The exact E wires below are *earned*. -/

def Future (f : Cursor d) (i : Fin (d+1)) : Prop :=
  match f with
  | .issue _ => True
  | .out k _ => k.val<i.val
  | _ => False

structure Clean (S : Sector h d) (x : Raw s n) (op : Nat)
    (f : Cursor d) : Prop where
  base : Dirty S x op f
  tail : ∀ i, Future f i → wire x (site S i)=encode emptyToken

theorem clean_seed (S : Sector h d) (x : Raw s n) (op : Nat)
    (O : op≤5) (I : Controller S x 1 op)
    (E : ∀ i : Fin (d+1), wire x (site S i)=encode emptyToken) :
    Clean S x op (seedCursor S x op) :=
  ⟨dirty_seed S x op O I,fun i _=>E i⟩

private theorem prep_empty (h : Bool) (u : BStarWidthTransfer.Source)
    (E : u.token=encode emptyToken) : (prep' h u).token=encode emptyToken := by
  have D : decode u.token=emptyToken := by
    rw [E,WidthTokenTransport.empty_codec]
  cases h <;> simp only [prep',D,emptyToken,Bool.false_eq_true,if_false,if_true] <;> exact E

private theorem left_empty (c r i : Nat) (h j : Bool) (u v : BStarWidthTransfer.Source)
    (data : Data) (E : u.token=encode emptyToken)
    (H : j=true ∨ (decode v.token).tag≠3) :
    (sourceStep c r i (h,j) u v data).1.token=encode emptyToken := by
  rw [source'_eq]
  have D : decode u.token=emptyToken := by
    rw [E,WidthTokenTransport.empty_codec]
  cases j with
  | true =>
    simpa [source',D,emptyToken] using prep_empty h u E
  | false =>
    have N : (decode v.token).tag≠3 := H.resolve_left (by decide)
    simpa [source',D,emptyToken,N] using prep_empty h u E

private theorem right_empty (c r i : Nat) (h : Bool) (u v : BStarWidthTransfer.Source)
    (data : Data) (E : v.token=encode emptyToken)
    (H : (decode u.token).tag≠2) :
    (sourceStep c r i (h,false) u v data).2.token=encode emptyToken := by
  rw [source'_eq]
  have D : decode v.token=emptyToken := by
    rw [E,WidthTokenTransport.empty_codec]
  -- CHECK: sourceStep; old T/E erases only the left.
  unfold source'
  simp only [beq_false_of_ne H,if_false,D,emptyToken,Bool.false_eq_true,
    Nat.reduceBEq,Bool.and_true]
  split <;> exact prep_empty false v E

private theorem site_succ (S : Sector h d) (i : Fin (d+1))
    (H : i.val<d) :
    rightNeighbor (site S i)=site S (⟨i.val+1,by omega⟩ : Fin (d+1)) := rfl

private theorem last_eq (i : Fin (d+1)) (H : i.val=d) :
    i=WidthWaitDrain.last d := Fin.ext H

/-- An empty interval stays empty if the one possibly entering
    predecessor mark cannot import a nonempty token. The cut j may
    be zero (parked ISSUE), one after launch, or beyond a live front.
    This is about literal old pair rows, not an independence assumption. -/
theorem empty_interval_hold (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (e : Fin n) (j : Nat)
    (E : ∀ i : Fin (d+1), j≤i.val → wire x (site S i)=encode emptyToken)
    (I : e≠inlet S ∨ 0<j)
    (B : ∀ m : Fin d, e=site S (west m) → j≤m.val+1 → j≤m.val)
    (i : Fin (d+1)) (J : j≤i.val) :
    wire (rawNext s x e) (site S i)=encode emptyToken := by
  by_cases A : e=site S i
  · subst e
    have R := congrArg BStarWidthTransfer.Source.token (raw_sources P (roomN S) x X (site S i)).1
    change wire (rawNext s x (site S i)) (site S i)=_ at R
    rw [R]
    unfold pairSources
    apply left_empty
    · exact E i J
    · by_cases K : i.val=d
      · left
        rw [last_eq i K]
        exact outgoing_header S
      · right
        have V : i.val<d := by have := i.isLt; omega
        rw [site_succ S i V]
        change (decode (wire x (site S ⟨i.val+1,by omega⟩))).tag≠3
        rw [E ⟨i.val+1,by omega⟩ (by change j≤i.val+1; omega),WidthTokenTransport.empty_codec]
        decide
  · by_cases C : rightNeighbor e=site S i
    · obtain H|⟨m,H⟩ := incident S e i C
      · subst e
        have Z : i=0 := site_injective S (C.symm.trans (inlet_eq S))
        subst i
        rcases I with I|I
        · exact False.elim (I rfl)
        · exact False.elim (by change j≤0 at J; omega)
      · have K : i=east m := by
          apply site_injective S
          rw [←C,H,internal_right]
        subst i
        have G : j≤m.val := B m H (by exact J)
        have R := congrArg BStarWidthTransfer.Source.token (raw_sources P (roomN S) x X e).2
        change wire (rawNext s x e) (rightNeighbor e)=_ at R
        rw [C] at R
        rw [R]
        unfold pairSources
        rw [C,internal_nonheader S m]
        apply right_empty
        · exact E (east m) J
        · change (decode (wire x e)).tag≠2
          rw [H,E (west m) G,WidthTokenTransport.empty_codec]
          decide
    · rw [remote_wire x e (site S i) (Ne.symm A) (Ne.symm C)]
      exact E i J

theorem clean_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op : Nat) (O : op≤5)
    (f : Cursor d) (A : Clean S x op f) (H : live f) (e : Fin n) :
    Clean S (rawNext s x e) op (cursorNext P S op x e f) := by
  refine ⟨dirty_step P S x X op O f A.base H e,?_⟩
  intro i J
  cases f with
  | consumed a => exact False.elim H
  | issue a =>
    by_cases K : e=inlet S
    · subst e
      simp only [cursorNext,if_true,Future] at J
      refine empty_interval_hold P S x X.1 (inlet S) 1
        (fun q _=>A.tail q trivial) (.inr (by omega)) ?_ i ?_
      · intro m M _
        exact False.elim (inlet_not_site S (west m) M)
      · omega
    · simp only [cursorNext,if_neg K,Future] at J
      exact empty_interval_hold P S x X.1 e 0
        (fun q _=>A.tail q trivial) (.inl K) (fun _ _ _=>Nat.zero_le _) i
        (Nat.zero_le _)
  | out k a =>
    by_cases K : e=site S k
    · subst e
      by_cases L : k.val<d
      · simp only [cursorNext,if_true,dif_pos L,Future] at J
        refine empty_interval_hold P S x X.1 (site S k) (k.val+2)
          (fun q Q=>A.tail q (by change k.val<q.val; omega)) (.inr (by omega)) ?_ i ?_
        · intro m M H
          have V := congrArg Fin.val (site_injective S M)
          change k.val=m.val at V
          omega
        · omega
      · simp only [cursorNext,if_true,dif_neg L,Future] at J
    · simp only [cursorNext,if_neg K,Future] at J
      refine empty_interval_hold P S x X.1 e (k.val+1)
        (fun q Q=>A.tail q (by change k.val<q.val; omega)) (.inr (by omega)) ?_ i ?_
      · intro m M V
        have N : m.val≠k.val := by
          intro T
          exact K (M.trans (congrArg (site S) (Fin.ext T)))
        omega
      · omega
  | back k a =>
    -- CHECK: cursorNext. A back cursor can only
    -- remain back or consume; neither case has a future suffix.
    by_cases Z : k.val=0
    · by_cases E : e=inlet S <;> simp [cursorNext,Z,E,Future] at J
    · let p : Fin (d+1) := ⟨k.val-1,by have := k.isLt; omega⟩
      by_cases E : e=site S p <;> simp [cursorNext,Z,p,E,Future] at J

theorem clean_rail (S : Sector h d) (x : Raw s n) (op : Nat) (O : op≤5)
    (f : Cursor d) (C : Clean S x op f) : WidthChooseEpoch.Rail S x op f := by
  cases f with
  | issue a =>
    refine ⟨C.base.2.2,?_,C.base.1,C.base.2.1⟩
    intro i
    rw [C.tail i trivial,WidthTokenTransport.empty_codec]
    rfl
  | out k a =>
    exact WidthChooseEpoch.front_tokens S x op O k a C.base
      (fun i I=>by rw [C.tail i I,WidthTokenTransport.empty_codec])
  | back k a =>
    refine ⟨C.base.1,?_,C.base.2.control⟩
    intro i
    rw [WidthFreshReverse.back_decode S x op k.val (finishArg op a) O C.base.2 i]
    -- CHECK: slot vs railToken.
    -- The only difference is Nat equality vs Fin equality.
    by_cases H : i.val<k.val
    · simp [WidthFreshReverse.slot,railToken,H]
    · by_cases J : i=k
      · subst i
        simp [WidthFreshReverse.slot,railToken]
      · have V : i.val≠k.val := fun E=>J (Fin.ext E)
        simp [WidthFreshReverse.slot,railToken,H,J,V]
  | consumed a =>
    refine ⟨C.base.1,?_,trivial⟩
    intro i
    rw [C.base.2.empty i,WidthTokenTransport.empty_codec]
    rfl

/-! 4. Actual data credits. First, BEGIN on a dirty suffix.
    A processed slot is T/D/E and hence cannot initiate a write. -/

def ResetData (v : Data) : Prop :=
  v.done=0 ∧ v.pick=0 ∧ v.count=0

def ResetPrefix (S : Sector h d) (x : Raw s n) (f : Cursor d) : Prop :=
  ∀ i : Fin (d+1), i.val<spent f → ResetData (wordData S x i)

private theorem quiet_cursor (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (e : Fin n) (f : Cursor d)
    (H : ¬Departs S f e) :
    spent (cursorNext P S op x e f)=spent f ∧
      payload (cursorNext P S op x e f)=payload f := by
  cases f with
  | issue a => by_cases I : e=inlet S <;> simp [cursorNext,I,spent,payload]
  | out k a =>
    have J : e≠site S k := fun E=>H ⟨k,a,rfl,E⟩
    simp [cursorNext,J]
  | back k a =>
    simp only [cursorNext]
    split <;> split <;> exact ⟨rfl,rfl⟩
  | consumed a => exact ⟨rfl,rfl⟩

private theorem depart_cursor (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (k : Fin (d+1)) (a : Nat) :
    let f := cursorNext P S op x (site S k) (.out k a)
    spent f=k.val+1 ∧ payload f=advancedArg P x (site S k) op a := by
  simp only [cursorNext,if_true]
  split
  · exact ⟨rfl,rfl⟩
  · rename_i H
    have K : k.val=d := by have := k.isLt; omega
    exact ⟨by simp [spent,K],rfl⟩

private theorem processed_noF (S : Sector h d) (x : Raw s n) (op : Nat)
    (O : op≤5) (f : Cursor d) (A : Dirty S x op f)
    (i : Fin (d+1)) (I : i.val<spent f) :
    (decode (wire x (site S i))).tag≠2 := by
  cases f with
  | issue a => exact False.elim (by change i.val<0 at I; omega)
  | out k a =>
    rw [A.trail i I,WidthTokenTransport.trail_codec]
    decide
  | back k a =>
    rw [WidthFreshReverse.back_decode S x op k.val (finishArg op a) O A.2 i]
    unfold WidthFreshReverse.slot
    split
    · decide
    · split
      · simp [reply]
      · decide
  | consumed a =>
    rw [A.2.empty i,WidthTokenTransport.empty_codec]
    decide

private theorem departure_token (S : Sector h d) (x : Raw s n)
    (op : Nat) (O : op≤5) (k : Fin (d+1)) (a : Nat)
    (A : Dirty S x op (.out k a)) :
    decode (wire x (site S k))=fwd op a := by
  have W : wire x (site S k)=encode (fwd op a) := A.liveWire
  rw [W,fcodec op a O A.arg]

theorem begin_prefix_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (f : Cursor d)
    (A : Dirty S x 0 f) (R : ResetPrefix S x f) (e : Fin n) :
    ResetPrefix S (rawNext s x e) (cursorNext P S 0 x e f) := by
  intro i I
  by_cases D : Departs S f e
  · obtain ⟨k,a,F,E⟩ := D
    subst f
    subst e
    have T := departure_token S x 0 (by decide) k a A
    have K := (depart_cursor P S x 0 k a).1
    rw [K] at I
    change ResetData (dat (rawNext s x (site S k)) (site S i))
    rw [raw_data_at P (roomN S) x X.1]
    by_cases J : i=k
    · subst i
      simp [T,ResetData,execute,fwd]
    · have H : site S i≠site S k := fun E=>J (site_injective S E)
      rw [if_neg H]
      have V : i.val≠k.val := fun E=>J (Fin.ext E)
      exact R i (by change i.val<k.val; omega)
  · rw [(quiet_cursor P S x 0 e f D).1] at I
    change ResetData (dat (rawNext s x e) (site S i))
    rw [raw_data_at P (roomN S) x X.1]
    by_cases J : site S i=e
    · subst e
      have N := processed_noF S x 0 (by decide) f A i I
      simpa [N] using R i I
    · simpa [J] using R i I

/-! Zero count arithmetic on the physical word, not on c clipped
    counter positions. DONE is a BitVec 1. No finite-state search. -/
private def sumN {m : Nat} (f : Fin m→Nat) : Nat := (List.ofFn f).sum

private theorem sum_succ {m : Nat} (f : Fin (m+1)→Nat) :
    sumN f=f 0+sumN (fun i : Fin m=>f i.succ) := by
  simp [sumN,List.ofFn_succ]

private theorem sum_le_len {m : Nat} (f : Fin m→Nat) (B : ∀ i,f i≤1) :
    sumN f≤m := by
  induction m with
  | zero => simp [sumN]
  | succ m IH =>
    rw [sum_succ]
    have H := IH (fun i : Fin m=>f i.succ) (fun i=>B i.succ)
    have J := B 0
    omega

private theorem sum_zero {m : Nat} (f : Fin m→Nat) (B : ∀ i,f i=0) :
    sumN f=0 := by
  induction m with
  | zero => simp [sumN]
  | succ m IH =>
    rw [sum_succ,B 0,IH _ (fun i=>B i.succ)]

private theorem sum_change {m : Nat} (f g : Fin m→Nat) (k : Fin m)
    (E : ∀ i,i≠k → f i=g i) :
    sumN f+g k=sumN g+f k := by
  induction m with
  | zero => exact Fin.elim0 k
  | succ m IH =>
    revert E
    refine Fin.cases ?_ (fun j=>?_) k <;> intro E
    · rw [sum_succ,sum_succ]
      have H : (fun i : Fin m=>f i.succ)=(fun i : Fin m=>g i.succ) :=
        funext (fun i=>E i.succ (Fin.succ_ne_zero i))
      rw [H]
      omega
    · rw [sum_succ,sum_succ,E 0 (Ne.symm (Fin.succ_ne_zero j))]
      have H := IH (fun i : Fin m=>f i.succ) (fun i : Fin m=>g i.succ)
        j (fun i N=>E i.succ (fun Q=>N (Fin.ext (by have H := congrArg Fin.val Q; simp only [Fin.val_succ] at H; omega))))
      omega

def zeroBit (v : Data) : Nat := (v.done.toNat==0).toNat
def zeros (S : Sector h d) (x : Raw s n) : Nat :=
  sumN (fun i : Fin (d+1)=>zeroBit (wordData S x i))

theorem zeros_bound (S : Sector h d) (x : Raw s n) : zeros S x≤d+1 := by
  apply sum_le_len
  intro i
  unfold zeroBit
  cases ((wordData S x i).done.toNat==0) <;> decide

private theorem zeros_of_nonzero (S : Sector h d) (x : Raw s n)
    (H : ∀ i : Fin (d+1),(wordData S x i).done.toNat≠0) : zeros S x=0 := by
  apply sum_zero
  intro i
  simp [zeroBit,H i]

/-- Exact two-bit local CHOOSE calculation; arbitrary old pick/count,
    arbitrary old DONE, and legal carried bit. -/
theorem choose_local (c r i : Nat) (v : Data) (a : Nat) (A : a<2) :
    let z := execute c r i v (fwd 1 a)
    let b := z.2.arg
    a≤b ∧ b<2 ∧ zeroBit z.1+b=zeroBit v+a ∧
      (b=0 → z.1.done.toNat≠0) := by
  have D : v.done.toNat=0 ∨ v.done.toNat=1 := by
    have := v.done.isLt
    omega
  have B : a=0 ∨ a=1 := by omega
  -- CHECK: BStarWidthTransferDepart:31–35. BitVec.toNat_ofNat
  -- reduces the one-bit result; the four Nat.or cases are constants.
  rcases B with B|B <;> subst a <;> rcases D with D|D <;>
    simp [execute,fwd,zeroBit,D,BitVec.toNat_ofNat]

structure ChooseProgress (S : Sector h d) (x : Raw s n)
    (f : Cursor d) (z : Nat) : Prop where
  balance : zeros S x+payload f=z
  past : payload f=0 → ∀ i : Fin (d+1), i.val<spent f →
    (wordData S x i).done.toNat≠0

theorem choose_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (f : Cursor d)
    (C : Clean S x 1 f) (A : ChooseProgress S x f z) (e : Fin n) :
    ChooseProgress S (rawNext s x e) (cursorNext P S 1 x e f) z := by
  have R := clean_rail S x 1 (by decide) f C
  by_cases D : Departs S f e
  · obtain ⟨k,a,F,E⟩ := D
    subst f
    subst e
    let y := rawNext s x (site S k)
    let b := advancedArg P x (site S k) 1 a
    have T := departure_token S x 1 (by decide) k a C.base
    have U := choose_local (s+11) (radWidth s) (eff P x (site S k))
      (dat x (site S k)) a C.base.arg
    have W : wordData S y k =
      (execute (s+11) (radWidth s) (eff P x (site S k))
        (dat x (site S k)) (fwd 1 a)).1 := by
      change dat y (site S k)=_
      rw [raw_data_at P (roomN S) x X.1,if_pos rfl,T]
      rfl
    have L : a≤b ∧ b<2 ∧
        zeroBit (wordData S y k)+b=zeroBit (wordData S x k)+a ∧
        (b=0 → (wordData S y k).done.toNat≠0) := by
      rw [W]
      exact U
    have E' (i : Fin (d+1)) (I : i≠k) :
        wordData S y i=wordData S x i := by
      change dat y (site S i)=dat x (site S i)
      rw [raw_data_at P (roomN S) x X.1,if_neg (fun H=>I (site_injective S H))]
    have V := sum_change
      (fun i : Fin (d+1)=>zeroBit (wordData S y i))
      (fun i=>zeroBit (wordData S x i)) k
      (fun i I=>congrArg zeroBit (E' i I))
    change zeros S y+zeroBit (wordData S x k)=
      zeros S x+zeroBit (wordData S y k) at V
    have K := depart_cursor P S x 1 k a
    refine ⟨?_,?_⟩
    · rw [K.2]
      have Old : zeros S x+a=z := A.balance
      have Local := L.2.2.1
      change zeros S y+b=z
      omega
    · rw [K.1,K.2]
      intro B i I
      have B' : b=0 := B
      by_cases J : i=k
      · subst i
        exact L.2.2.2 B'
      · rw [E' i J]
        have A0 : a=0 := by have := L.1; omega
        have Q : i.val≠k.val := fun H=>J (Fin.ext H)
        exact A.past A0 i (by change i.val<k.val; omega)
  · have W := WidthChooseEpoch.no_depart_data P S x X 1 f R e D
    have E : zeros S (rawNext s x e)=zeros S x := by
      unfold zeros
      exact congrArg sumN (funext (fun i=>congrArg zeroBit (W i)))
    have K := quiet_cursor P S x 1 e f D
    exact ⟨by rw [K.2,E]; exact A.balance,
      by intro B i I; rw [W i]; exact A.past (K.2.symm ▸ B) i (K.1 ▸ I)⟩

private theorem other_done (c r i : Nat) (v : Data) (op a : Nat)
    (O : op≤5) (H : op≠0) (J : op≠1) :
    (execute c r i v (fwd op a)).1.done=v.done := by
  have K : op=2 ∨ op=3 ∨ op=4 ∨ op=5 := by omega
  rcases K with K|K|K|K <;> subst op <;>
    simp [execute,fwd] <;> split <;> rfl

theorem other_zeros_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op : Nat) (O : op≤5)
    (H : op≠0) (J : op≠1) (f : Cursor d) (C : Clean S x op f)
    (e : Fin n) : zeros S (rawNext s x e)=zeros S x := by
  unfold zeros
  apply congrArg sumN
  funext i
  by_cases D : Departs S f e
  · obtain ⟨k,a,F,E⟩ := D
    subst f
    subst e
    change zeroBit (dat (rawNext s x (site S k)) (site S i))=_
    rw [raw_data_at P (roomN S) x X.1]
    by_cases B : i=k
    · subst i
      rw [if_pos rfl,departure_token S x op O k a C.base]
      change zeroBit (execute _ _ _ _ (fwd op a)).1=zeroBit _
      unfold zeroBit
      rw [other_done _ _ _ _ op a O H J]
    · rw [if_neg (fun V=>B (site_injective S V))]
  · rw [WidthChooseEpoch.no_depart_data P S x X op f
      (clean_rail S x op O f C) e D i]

/-! 5. Same-tape command receipt. This stops exactly at consumption;
    it cannot advance past a terminal cursor. -/

def Credit (S : Sector h d) (x : Raw s n) (op : Nat)
    (f : Cursor d) (z : Nat) : Prop :=
  if op=1 then ChooseProgress S x f z
  else if op=0 then True else zeros S x=z

private theorem credit_seed (S : Sector h d) (x : Raw s n) (op : Nat) :
    Credit S x op (seedCursor S x op) (zeros S x) := by
  by_cases E : op=1
  · subst op
    simp only [Credit,if_true]
    refine ⟨?_,?_⟩
    · simp [seedCursor,payload,initialArg]
    · intro _ i I
      change i.val<0 at I
      omega
  · by_cases B : op=0 <;> simp [Credit,E,B]

private theorem credit_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op : Nat) (O : op≤5)
    (f : Cursor d) (C : Clean S x op f) (z : Nat)
    (A : Credit S x op f z) (e : Fin n) :
    Credit S (rawNext s x e) op (cursorNext P S op x e f) z := by
  by_cases E : op=1
  · subst op
    exact choose_step P S x X f C A e
  · by_cases B : op=0
    · simp [Credit,B]
    · simp only [Credit,if_neg E,if_neg B] at A ⊢
      exact (other_zeros_step P S x X op O B E f C e).trans A

inductive Trace (P : WidthLower s n) (S : Sector P.h d)
    (clean : Bool) (x0 : Raw s n) (op : Nat) :
    List (Fin n) → Cursor d → Prop where
  | seed : P.Post x0 → Controller S x0 1 op →
      (clean=true → ∀ i : Fin (d+1), wire x0 (site S i)=encode emptyToken) →
      Trace P S clean x0 op [] (seedCursor S x0 op)
  | snoc {w f} (e : Fin n) : Trace P S clean x0 op w f → live f →
      Trace P S clean x0 op (w++[e]) (cursorNext P S op (rawRun x0 w) e f)

structure TraceFacts (P : WidthLower s n) (S : Sector P.h d)
    (clean : Bool) (x0 x : Raw s n) (op : Nat) (f : Cursor d) : Prop where
  post : P.Post x
  dirty : Dirty S x op f
  cleanRail : clean=true → Clean S x op f
  reset : op=0 → ResetPrefix S x f
  credit : clean=true → Credit S x op f (zeros S x0)

theorem trace_facts (P : WidthLower s n) (S : Sector P.h d)
    (clean : Bool) (x0 : Raw s n) (op : Nat) (O : op≤5)
    (w : List (Fin n)) (f : Cursor d) (T : Trace P S clean x0 op w f) :
    TraceFacts P S clean x0 (rawRun x0 w) op f := by
  induction T with
  | seed X I E =>
    refine ⟨X,dirty_seed S x0 op O I,fun H=>clean_seed S x0 op O I (E H),
      ?_,fun _=>credit_seed S x0 op⟩
    intro _ i I
    change i.val<0 at I
    omega
  | @snoc w f e T H IH =>
    rw [raw_snoc]
    refine ⟨P.post_closed (roomN S) _ IH.post e,
      dirty_step P S _ IH.post op O f IH.dirty H e,
      fun K=>clean_step P S _ IH.post op O f (IH.cleanRail K) H e,
      ?_,fun K=>credit_step P S _ IH.post op O f (IH.cleanRail K) _ (IH.credit K) e⟩
    intro E
    subst op
    exact begin_prefix_step P S _ IH.post f IH.dirty (IH.reset rfl) e

/-- Cursor-to-consume is possible only on this *old* root-D inlet.
    In particular an inherited WAIT exit cannot satisfy this theorem. -/
theorem consumes_only (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (f : Cursor d) (H : live f)
    (e : Fin n) (a : Nat)
    (E : cursorNext P S op x e f=.consumed a) :
    f=.back 0 a ∧ e=inlet S := by
  cases f with
  | consumed b => exact False.elim H
  | issue b =>
    by_cases I : e=inlet S <;> simp [cursorNext,I] at E
  | out k b =>
    by_cases I : e=site S k <;> by_cases J : k.val<d <;> simp [cursorNext,I,J] at E
  | back k b =>
    by_cases Z : k.val=0
    · have K : k=0 := Fin.ext Z
      subst k
      by_cases I : e=inlet S
      · simp [cursorNext,I] at E
        subst b
        exact ⟨rfl,I⟩
      · simp [cursorNext,I] at E
    · simp only [cursorNext,dif_neg Z] at E
      split at E <;> cases E

theorem trace_last_consume (P : WidthLower s n) (S : Sector P.h d)
    (clean : Bool) (x0 : Raw s n) (op : Nat) (w : List (Fin n))
    (f : Cursor d) (T : Trace P S clean x0 op w f) (a : Nat)
    (E : f=.consumed a) :
    ∃ u, w=u++[inlet S] ∧ Trace P S clean x0 op u (.back 0 a) := by
  cases T with
  | seed X I B => cases E
  | @snoc w f e T L =>
    obtain ⟨F,J⟩ := consumes_only P S (rawRun x0 w) op f L e a E
    exact ⟨w,by rw [J],F ▸ T⟩

def CleanIssue (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) : Prop :=
  P.Post x ∧ op≤5 ∧ Controller S x 1 op ∧
    ∀ i : Fin (d+1), wire x (site S i)=encode emptyToken

theorem receipt_next (P : WidthLower s n) (S : Sector P.h d)
    (clean : Bool) (x : Raw s n) (op : Nat) (O : op≤5)
    (w : List (Fin n)) (a : Nat) (T : Trace P S clean x op w (.consumed a)) :
    CleanIssue P S (rawRun x w) (nextOp op (finishArg op a)) := by
  have H := trace_facts P S clean x op O w _ T
  exact ⟨H.post,WidthFreshReverse.nextOp_bound op _ O,H.dirty.2.control,H.dirty.2.empty⟩

theorem receipt_begin (P : WidthLower s n) (S : Sector P.h d)
    (clean : Bool) (x : Raw s n) (w : List (Fin n)) (a : Nat)
    (T : Trace P S clean x 0 w (.consumed a)) :
    CleanIssue P S (rawRun x w) 1 ∧
      ∀ i : Fin (d+1), ResetData (wordData S (rawRun x w) i) := by
  have H := trace_facts P S clean x 0 (by decide) w _ T
  refine ⟨?_,fun i=>H.reset rfl i (by exact i.isLt)⟩
  simpa [nextOp,WidthFreshReverse.nextOp,WidthOwnerController.nextControl] using
    receipt_next P S clean x 0 (by decide) w a T

/-- Arbitrary-data CHOOSE credit, *only* after a fresh flush. -/
theorem receipt_choose (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (w : List (Fin n)) (a : Nat)
    (T : Trace P S true x 1 w (.consumed a)) :
    a<2 ∧ zeros S (rawRun x w)+a=zeros S x ∧
      (a=0 → zeros S (rawRun x w)=0) := by
  have H := trace_facts P S true x 1 (by decide) w _ T
  have C : ChooseProgress S (rawRun x w) (.consumed a) (zeros S x) :=
    H.credit rfl
  refine ⟨H.dirty.1,C.balance,?_⟩
  intro A
  apply zeros_of_nonzero
  intro i
  exact C.past A i (by exact i.isLt)

theorem receipt_other (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (O : op≤5) (B : op≠0) (J : op≠1)
    (w : List (Fin n)) (a : Nat)
    (T : Trace P S true x op w (.consumed a)) :
    zeros S (rawRun x w)=zeros S x := by
  have H := (trace_facts P S true x op O w _ T).credit rfl
  simpa [Credit,J,B] using H

/-! 6. Exact command clock. L+1 to true turn, L to consume.
    Cursor rank is on the original physical alphabet, not the word. -/

def commandRank : Cursor d → Nat
  | .issue _ => 2*(d+1)+1
  | .out k _ => 2*(d+1)-k.val
  | .back k _ => k.val+1
  | .consumed _ => 0

private theorem rank_pos (f : Cursor d) (H : live f) :
    0<commandRank f := by
  cases f with
  | issue a => simp [commandRank]
  | out k a => have := k.isLt; simp only [commandRank]; omega
  | back k a => simp [commandRank]
  | consumed a => exact False.elim H

theorem command_rank_mark (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (f : Cursor d) (H : live f) :
    ∃ b : Fin n, ∀ e : Fin n,
      commandRank (cursorNext P S op x e f)≤commandRank f ∧
      (e=b → commandRank (cursorNext P S op x e f)<commandRank f) := by
  cases f with
  | consumed a => exact False.elim H
  | issue a =>
    refine ⟨inlet S,fun e=>?_⟩
    by_cases E : e=inlet S <;> simp [cursorNext,E,commandRank]
  | out k a =>
    refine ⟨site S k,fun e=>?_⟩
    by_cases E : e=site S k
    · subst e
      by_cases J : k.val<d
      · simp only [cursorNext,if_true,dif_pos J,commandRank,true_implies]
        omega
      · have K : k.val=d := by have := k.isLt; omega
        simp only [cursorNext,if_true,dif_neg J,commandRank,true_implies]
        omega
    · simp [cursorNext,E,commandRank]
  | back k a =>
    by_cases Z : k.val=0
    · refine ⟨inlet S,fun e=>?_⟩
      by_cases E : e=inlet S <;> simp [cursorNext,Z,E,commandRank]
    · let j : Fin (d+1) := ⟨k.val-1,by have := k.isLt; omega⟩
      refine ⟨site S j,fun e=>?_⟩
      by_cases E : e=site S j
      · subst e
        simp only [cursorNext,dif_neg Z,j,if_true,commandRank,true_implies]
        omega
      · simp [cursorNext,Z,j,E,commandRank]

def commandNext (P : WidthLower s n) (S : Sector P.h d) (op : Nat)
    (z : Raw s n × Cursor d) (e : Fin n) : Raw s n × Cursor d :=
  (rawNext s z.1 e,cursorNext P S op z.1 e z.2)

def commandStop (z : Raw s n × Cursor d) : Prop := ¬live z.2

theorem command_mean (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (f : Cursor d) (H : live f) :
    Height.IIDExpectedHittingTimeAtMost (commandNext P S op)
      commandStop (x,f) (n*commandRank f) := by
  let Inv := fun (z : Raw s n × Cursor d) (r : Nat)=>
    live z.2 ∧ r=commandRank z.2
  have move (z : Raw s n × Cursor d) (r : Nat) (R : Inv z r) :
      ∃ b : Fin n, ∀ e,
        commandStop (commandNext P S op z e) ∨
        ∃ r',Inv (commandNext P S op z e) r' ∧ r'≤r ∧ (e=b → r'<r) := by
    obtain ⟨b,B⟩ := command_rank_mark P S z.1 op z.2 R.1
    refine ⟨b,fun e=>?_⟩
    by_cases L : live (commandNext P S op z e).2
    · refine .inr ⟨commandRank (commandNext P S op z e).2,⟨L,rfl⟩,?_,?_⟩
      · rw [R.2]
        exact (B e).1
      · intro E
        rw [R.2]
        exact (B e).2 E
    · exact .inl L
  exact ResetReturnIID.iid_of_relational_rank (commandNext P S op)
    commandStop Inv (fun z r R=>R.2.symm ▸ rank_pos z.2 R.1) move
    (x,f) (commandRank f) (.inr ⟨H,rfl⟩)

theorem issue_command_mean (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) :
    Height.IIDExpectedHittingTimeAtMost (commandNext P S op)
      commandStop (x,seedCursor S x op) (n*(2*(d+1)+1)) :=
  command_mean P S x op _ (by trivial)

/-- Finite physical extension, complementary to the stochastic bound.
    A receipt trace never crosses its first consume. -/
theorem trace_extend (P : WidthLower s n) (S : Sector P.h d)
    (clean : Bool) (x : Raw s n) (op : Nat) (w : List (Fin n))
    (f : Cursor d) (T : Trace P S clean x op w f) :
    ∃ v a, v.length≤commandRank f ∧
      Trace P S clean x op (w++v) (.consumed a) := by
  have aux (fuel : Nat) : ∀ w f, Trace P S clean x op w f →
      commandRank f≤fuel →
      ∃ v a, v.length≤fuel ∧ Trace P S clean x op (w++v) (.consumed a) := by
    induction fuel with
    | zero =>
      intro w f T B
      cases f with
      | consumed a => exact ⟨[],a,by simp,by simpa using T⟩
      | issue a => exact False.elim (by have := rank_pos (.issue a : Cursor d) trivial; omega)
      | out k a => exact False.elim (by have := rank_pos (.out k a) trivial; omega)
      | back k a => exact False.elim (by have := rank_pos (.back k a) trivial; omega)
    | succ fuel IH =>
      intro w f T B
      by_cases H : live f
      · obtain ⟨e,E⟩ := command_rank_mark P S (rawRun x w) op f H
        have K := (E e).2 rfl
        have T' := Trace.snoc e T H
        obtain ⟨v,a,V,R⟩ := IH (w++[e]) _ T' (by omega)
        refine ⟨e::v,a,by simp; omega,?_⟩
        simpa only [List.append_assoc,List.singleton_append] using R
      · cases f with
        | consumed a => exact ⟨[],a,by simp,by simpa using T⟩
        | issue a => exact False.elim (H trivial)
        | out k a => exact False.elim (H trivial)
        | back k a => exact False.elim (H trivial)
  exact aux (commandRank f) w f T (Nat.le_refl _)

theorem complete_command (P : WidthLower s n) (S : Sector P.h d)
    (clean : Bool) (x : Raw s n) (op : Nat) (X : P.Post x)
    (I : Controller S x 1 op)
    (E : clean=true → ∀ i : Fin (d+1),wire x (site S i)=encode emptyToken) :
    ∃ w a, w.length≤2*(d+1)+1 ∧ Trace P S clean x op w (.consumed a) := by
  obtain ⟨w,a,B,T⟩ := trace_extend P S clean x op [] _
    (Trace.seed X I E)
  exact ⟨w,a,B,by simpa using T⟩

/-! 7. Command-cut potential. These are actual consumes, not
    launches, terminal turns, or observed source phase coincidences. -/

def budget (op z : Nat) : Nat :=
  match op with
  | 0 => 1
  | 1 => 4*z+3
  | 2 => 4*z+6
  | 3 => 4*z+5
  | 4 => 4*z+4
  | _ => 2

theorem budget_pos (op z : Nat) : 0<budget op z := by
  unfold budget
  split <;> omega

theorem budget_bound (op z L : Nat) (Z : z≤L) : budget op z≤4*L+6 := by
  unfold budget
  split <;> omega

/-- Both credits are useful: one for total consumes, the other for
    the exact number of successful CHOOSE iterations. -/
theorem clean_consume_descent (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (O : op≤5) (N : op≠0)
    (w : List (Fin n)) (a : Nat) (T : Trace P S true x op w (.consumed a)) :
    let y := rawRun x w
    let op' := nextOp op (finishArg op a)
    budget op' (zeros S y)<budget op (zeros S x) ∧
      zeros S y+(if op=1 ∧ a=1 then 1 else 0)≤zeros S x := by
  dsimp only
  by_cases E : op=1
  · subst op
    obtain ⟨A,Z,H⟩ := receipt_choose P S x w a T
    have K : a=0 ∨ a=1 := by omega
    rcases K with K|K
    · subst a
      have J := H rfl
      simp [nextOp,WidthFreshReverse.nextOp,WidthOwnerController.nextControl,
        finishArg,budget,J] at *
    · subst a
      simp [nextOp,WidthFreshReverse.nextOp,WidthOwnerController.nextControl,
        finishArg,budget] at *
      omega
  · have Z := receipt_other P S x op O N E w a T
    have K : op=2 ∨ op=3 ∨ op=4 ∨ op=5 := by omega
    rcases K with K|K|K|K <;> subst op <;>
      simp [nextOp,WidthFreshReverse.nextOp,WidthOwnerController.nextControl,
        budget,Z] <;> omega

/-- The first clean chain begins only at a drained fresh receipt.
    No constructor crosses a BEGIN consume. -/
inductive PreBegin (P : WidthLower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op0 : Nat) :
    List (Fin n) → Nat → Nat → Nat → Prop where
  | start : CleanIssue P S x0 op0 → PreBegin P S x0 op0 [] op0 0 0
  | more {w op k m} (v : List (Fin n)) (a : Nat) :
      PreBegin P S x0 op0 w op k m → op≠0 →
      Trace P S true (rawRun x0 w) op v (.consumed a) →
      PreBegin P S x0 op0 (w++v) (nextOp op (finishArg op a))
        (k+1) (m+(if op=1 ∧ a=1 then 1 else 0))

theorem prebegin_facts (P : WidthLower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op0 : Nat) (w : List (Fin n)) (op k m : Nat)
    (C : PreBegin P S x0 op0 w op k m) :
    CleanIssue P S (rawRun x0 w) op ∧
      k+budget op (zeros S (rawRun x0 w))≤budget op0 (zeros S x0) ∧
      m+zeros S (rawRun x0 w)≤zeros S x0 := by
  induction C with
  | start I =>
    have E : rawRun x0 []=x0 := rfl
    exact ⟨I,by rw [E,Nat.zero_add]; exact Nat.le_refl _,by rw [E,Nat.zero_add]; exact Nat.le_refl _⟩
  | @more w op k m v a C N T IH =>
    have B := clean_consume_descent P S (rawRun x0 w) op IH.1.2.1 N v a T
    have I := receipt_next P S true (rawRun x0 w) op IH.1.2.1 v a T
    rw [raw_append]
    refine ⟨I,?_,?_⟩
    · have H := IH.2.1
      have J := B.1
      omega
    · have H := IH.2.2
      have J := B.2
      omega

theorem prebegin_success_bound (P : WidthLower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op0 : Nat) (w : List (Fin n)) (op k m : Nat)
    (C : PreBegin P S x0 op0 w op k m) : m≤d+1 := by
  have H := (prebegin_facts P S x0 op0 w op k m C).2.2
  have J := zeros_bound S x0
  omega

/-- All actual non-BEGIN chains satisfy the bound. Conversely a
    finite continuation of genuine commands reaches ISSUE0, by
    induction on the cut potential; no favorable word is used to
    justify the all-mark safety/credit theorem. -/
theorem prebegin_extend_zero (P : WidthLower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op0 : Nat) (w : List (Fin n)) (op k m : Nat)
    (C : PreBegin P S x0 op0 w op k m) :
    ∃ v k' m', PreBegin P S x0 op0 (w++v) 0 k' m' := by
  have aux (fuel : Nat) :
      ∀ w op k m, PreBegin P S x0 op0 w op k m →
        budget op (zeros S (rawRun x0 w))≤fuel →
        ∃ v k' m', PreBegin P S x0 op0 (w++v) 0 k' m' := by
    induction fuel with
    | zero =>
      intro w op k m C B
      have H := budget_pos op (zeros S (rawRun x0 w))
      omega
    | succ fuel IH =>
      intro w op k m C B
      by_cases Z : op=0
      · subst op
        exact ⟨[],k,m,by simpa using C⟩
      · have I := (prebegin_facts P S x0 op0 w op k m C).1
        obtain ⟨v,a,_,T⟩ := complete_command P S true (rawRun x0 w) op
          I.1 I.2.2.1 (fun _=>I.2.2.2)
        let op' := nextOp op (finishArg op a)
        let m' := m+(if op=1 ∧ a=1 then 1 else 0)
        have C' : PreBegin P S x0 op0 (w++v) op' (k+1) m' :=
          PreBegin.more v a C Z T
        have D := (clean_consume_descent P S (rawRun x0 w) op I.2.1 Z v a T).1
        have F : budget op' (zeros S (rawRun x0 (w++v)))≤fuel := by
          rw [raw_append]
          change budget (nextOp op (finishArg op a)) (zeros S (rawRun (rawRun x0 w) v))≤fuel
          omega
        obtain ⟨u,k',m'',R⟩ := IH (w++v) op' (k+1) m' C' F
        exact ⟨v++u,k',m'',by simpa only [List.append_assoc] using R⟩
  exact aux _ w op k m C (Nat.le_refl _)

/-! 8. First actual BEGIN receipt, with its original raw word.
    The flush may itself be BEGIN. Otherwise only clean non-BEGIN
    traces occur before the final BEGIN trace. -/

inductive FirstBegin (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) : List (Fin n) → Nat → Nat → Prop where
  | flush_begin (w : List (Fin n)) (a : Nat) :
      op=0 → Trace P S false x op w (.consumed a) →
      FirstBegin P S x op w 1 0
  | after_flush (u v w : List (Fin n)) (a b k m : Nat) :
      op≠0 → Trace P S false x op u (.consumed a) →
      PreBegin P S (rawRun x u) (nextOp op (finishArg op a)) v 0 k m →
      Trace P S true (rawRun (rawRun x u) v) 0 w (.consumed b) →
      FirstBegin P S x op ((u++v)++w) (k+2) m

theorem first_begin_facts (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (O : op≤5) (w : List (Fin n))
    (k m : Nat) (T : FirstBegin P S x op w k m) :
    k≤4*(d+1)+7 ∧ m≤d+1 ∧
    CleanIssue P S (rawRun x w) 1 ∧
      (∀ i : Fin (d+1),ResetData (wordData S (rawRun x w) i)) ∧
      (∃ u, w=u++[inlet S]) := by
  cases T with
  | flush_begin w a Z T =>
    subst op
    have H := receipt_begin P S false x w a T
    obtain ⟨u,E,_⟩ := trace_last_consume P S false x 0 w _ T a rfl
    exact ⟨by omega,by omega,H.1,H.2,u,E⟩
  | after_flush u v w a b k m N F C T =>
    have H := prebegin_facts P S (rawRun x u) (nextOp op (finishArg op a))
      v 0 k m C
    have B := budget_bound (nextOp op (finishArg op a))
      (zeros S (rawRun x u)) (d+1) (zeros_bound S (rawRun x u))
    have K := H.2.1
    have M := prebegin_success_bound P S _ _ v 0 k m C
    have R := receipt_begin P S true (rawRun (rawRun x u) v) w b T
    obtain ⟨t,E,_⟩ := trace_last_consume P S true _ 0 w _ T b rfl
    change k+1≤budget (nextOp op (finishArg op a)) (zeros S (rawRun x u)) at K
    refine ⟨by omega,M,?_,?_,?_⟩
    · rw [raw_append,raw_append]
      exact R.1
    · rw [raw_append,raw_append]
      exact R.2
    · exact ⟨(u++v)++t,by simp only [E,List.append_assoc]⟩

theorem first_begin_from_issue (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op : Nat) (O : op≤5)
    (I : Controller S x 1 op) :
    ∃ w k m, FirstBegin P S x op w k m := by
  obtain ⟨u,a,_,F⟩ := complete_command P S false x op X I (by intro H; cases H)
  by_cases Z : op=0
  · exact ⟨u,1,0,FirstBegin.flush_begin u a Z F⟩
  · let y := rawRun x u
    let op' := nextOp op (finishArg op a)
    have J : CleanIssue P S y op' := receipt_next P S false x op O u a F
    obtain ⟨v,k,m,C⟩ := prebegin_extend_zero P S y op' [] op' 0 0
      (PreBegin.start J)
    have C' : PreBegin P S y op' v 0 k m := by simpa using C
    have V := (prebegin_facts P S y op' v 0 k m C').1
    obtain ⟨w,b,_,T⟩ := complete_command P S true (rawRun y v) 0
      V.1 V.2.2.1 (fun _=>V.2.2.2)
    exact ⟨(u++v)++w,k+2,m,FirstBegin.after_flush u v w a b k m Z F C' T⟩

/-! 9. Age after the first actual BEGIN. This is intentionally a
    historical predicate; the RESET bits need not stay zero after
    the next actual CHOOSE. The current chart is always clean. -/

def ResetSeed (P : WidthLower s n) (S : Sector P.h d) (y : Raw s n) : Prop :=
  ∃ x op w k m, op≤5 ∧ FirstBegin P S x op w k m ∧ y=rawRun x w

def WidthAgeFromGenuineReset (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) : Prop :=
  ∃ y w, ResetSeed P S y ∧ x=rawRun y w

theorem reset_seed_facts (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (A : ResetSeed P S x) :
    CleanIssue P S x 1 ∧ ∀ i : Fin (d+1),ResetData (wordData S x i) := by
  obtain ⟨y,op,w,k,m,O,T,rfl⟩ := A
  have H := first_begin_facts P S y op O w k m T
  exact ⟨H.2.2.1,H.2.2.2.1⟩

theorem width_reset_epoch_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (G : WidthAgeFromGenuineReset P S x) (e : Fin n) :
    WidthAgeFromGenuineReset P S (rawNext s x e) := by
  obtain ⟨y,w,A,rfl⟩ := G
  exact ⟨y,w++[e],A,(raw_snoc y w e).symm⟩

def LiveClean (P : WidthLower s n) (S : Sector P.h d) (x : Raw s n) : Prop :=
  P.Post x ∧ ∃ (op : Nat) (f : WidthChooseEpoch.Cursor d), op≤5 ∧ live f ∧ Clean S x op f

theorem live_clean_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (A : LiveClean P S x) (e : Fin n) :
    LiveClean P S (rawNext s x e) := by
  obtain ⟨X,op,f,O,H,C⟩ := A
  let y := rawNext s x e
  let g := cursorNext P S op x e f
  have D : Clean S y op g := clean_step P S x X op O f C H e
  have Y := P.post_closed (roomN S) x X e
  refine ⟨Y,?_⟩
  cases E : g with
  | issue a => exact ⟨op,.issue a,O,trivial,E ▸ D⟩
  | out k a => exact ⟨op,.out k a,O,trivial,E ▸ D⟩
  | back k a => exact ⟨op,.back k a,O,trivial,E ▸ D⟩
  | consumed a =>
    have R : Clean S y op (.consumed a) := E ▸ D
    have B := WidthFreshReverse.nextOp_bound op (finishArg op a) O
    exact ⟨nextOp op (finishArg op a),seedCursor S y _,B,trivial,
      clean_seed S y _ B R.base.2.control R.base.2.empty⟩

theorem age_has_clean (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (G : WidthAgeFromGenuineReset P S x) :
    LiveClean P S x := by
  obtain ⟨y,w,R,rfl⟩ := G
  have I := (reset_seed_facts P S y R).1
  have A : LiveClean P S y :=
    ⟨I.1,1,seedCursor S y 1,by decide,trivial,
      clean_seed S y 1 (by decide) I.2.2.1 I.2.2.2⟩
  have aux (z : Raw s n) (t : List (Fin n)) (Z : LiveClean P S z) :
      LiveClean P S (rawRun z t) := by
    induction t generalizing z with
    | nil => exact Z
    | cons e t IH => exact IH (rawNext s z e) (live_clean_step P S z Z e)
  exact aux y w A

theorem first_begin_seeds_age (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (O : op≤5) (w : List (Fin n))
    (k m : Nat) (T : FirstBegin P S x op w k m) :
    WidthAgeFromGenuineReset P S (rawRun x w) :=
  ⟨rawRun x w,[],⟨x,op,w,k,m,O,T,rfl⟩,rfl⟩

/-- All actual marks after the cut, including other owners' marks,
    retain both a genuine past and a current exact generated chart. -/
theorem age_all_marks (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (A : WidthAgeFromGenuineReset P S x) (e : Fin n) :
    WidthAgeFromGenuineReset P S (rawNext s x e) ∧
      LiveClean P S (rawNext s x e) := by
  have B := width_reset_epoch_step P S x A e
  exact ⟨B,age_has_clean P S _ B⟩

/-! 10. Cursor adapter on a receipt-generated canonical trace.
    No circular import of a completed data loop, and no assumption
    that an arbitrary decoded Rail has exact wire encodings. -/

theorem trace_sweep (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (O : op≤5)
    (A : WidthChooseEpoch.Plan s (d+1) op (wordData S x))
    (I : payload (seedCursor S x op)=A.arg 0)
    (w : List (Fin n)) (f : Cursor d) (T : Trace P S true x op w f) :
    WidthChooseEpoch.Sweep S (rawRun x w) op (wordData S x) A f := by
  induction T with
  | seed X C E =>
    exact ⟨I,fun _=>rfl⟩
  | @snoc w f e T H IH =>
    have F := trace_facts P S true x op O w f T
    rw [raw_snoc]
    exact WidthChooseEpoch.sweep_step P S _ F.post op _ A f
      (clean_rail S _ op O f (F.cleanRail rfl)) IH e

theorem clean_receipt_word (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (O : op≤5)
    (A : WidthChooseEpoch.Plan s (d+1) op (wordData S x))
    (I : payload (seedCursor S x op)=A.arg 0)
    (w : List (Fin n)) (a : Nat) (T : Trace P S true x op w (.consumed a)) :
    CleanIssue P S (rawRun x w) (nextOp op (finishArg op a)) ∧
      wordData S (rawRun x w)=A.after ∧ a=A.arg (d+1) ∧
      (op=2 → WidthOwnerController.argument (c:=s+11)
        ((rawRun x w) S.root).widthClient=finishArg op a) := by
  have H := trace_sweep P S x op O A I w _ T
  have B := trace_facts P S true x op O w _ T
  refine ⟨receipt_next P S true x op O w a T,?_,H.arg,B.dirty.2.compare⟩
  funext i
  simpa [spent,i.isLt] using H.data i

#print axioms arbitrary_issue_mean
#print axioms dirty_step
#print axioms clean_step
#print axioms begin_prefix_step
#print axioms choose_step
#print axioms trace_facts
#print axioms trace_last_consume
#print axioms command_mean
#print axioms clean_consume_descent
#print axioms first_begin_from_issue
#print axioms first_begin_facts
#print axioms age_all_marks
#print axioms clean_receipt_word

end L4.WidthEpochEntry



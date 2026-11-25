import Leader.L4.WidthForwardEpoch
import Leader.L4.WidthIssueTransport
import Leader.L4.WidthTokenTransport
import Leader.L4.ResetReturnIID

namespace L4.WidthFreshReverse

open AllSizeProtocol PhysicalCustody BStarH6WordChart
open WidthSectorGeometry ShortResetChart WidthByteRows
open WidthWaitDrain (west east)
open WidthChecksum (packet)
open BStarWidthTransferDepart (Data)
open WidthFreshForward
  (WidthLower src wire reply DArg dcodec sourceStep pairSources
   raw_sources remote_wire Controller nondoor_controller door_source
   Turn Generated generated_active generated_turn)

set_option maxRecDepth 12000
set_option maxHeartbeats 6000000

variable {s n d : Nat} {h : Fin n → Bool}

/-- Same explicit lower hypothesis as the forward epoch, not a new global
    closure axiom. All source-row lemmas below take P.Q x. -/
abbrev Lower (s n : Nat) := WidthLower s n

/-- Canonical exact slot syntax, including all raw token bits. -/
def slot (op a j k : Nat) : Token :=
  if k<j then trailToken
  else if k=j then reply op a else emptyToken

private theorem slot_before {op a j k : Nat} (H : k<j) :
    slot op a j k=trailToken := by simp [slot,H]

private theorem slot_at (op a j : Nat) :
    slot op a j j=reply op a := by simp [slot]

private theorem slot_after {op a j k : Nat} (H : j<k) :
    slot op a j k=emptyToken := by
  simp [slot,show ¬k<j by omega,show k≠j by omega]

theorem slot_codec (op a j k : Nat) (O : op≤5) (A : DArg op a) :
    decode (encode (slot op a j k))=slot op a j k := by
  unfold slot
  split
  · exact WidthTokenTransport.trail_codec
  split
  · exact dcodec op a O A
  · exact WidthTokenTransport.empty_codec

private theorem slot_noF (op a j k : Nat) :
    (slot op a j k).tag≠2 := by
  unfold slot
  split
  · decide
  split
  · simp [reply]
  · decide

private theorem slot_healthy (op a j k : Nat) :
    (slot op a j k).fault=false := by
  unfold slot
  split
  · rfl
  split <;> rfl

structure Back (S : Sector h d) (x : Raw s n)
    (op j a : Nat) : Prop where
  index : j≤d
  arg : DArg op a
  control : Controller S x 2 op
  slots : ∀ k : Fin (d+1), wire x (site S k)=
    encode (slot op a j k.val)

theorem turn_back (S : Sector h d) (x : Raw s n) (op a : Nat)
    (T : Turn S x op a) : Back S x op d a := by
  refine ⟨Nat.le_refl _,T.arg,T.control,?_⟩
  intro k
  by_cases B : k.val<d
  · rw [slot_before B]
    exact T.trail k B
  · have E : k=WidthWaitDrain.last d := by
      apply Fin.ext
      change k.val=d
      have := k.isLt
      omega
    subst k
    change wire x (site S (WidthWaitDrain.last d))=
      encode (slot op a d d)
    rw [slot_at]
    exact T.replyWire

theorem back_decode (S : Sector h d) (x : Raw s n)
    (op j a : Nat) (O : op≤5) (B : Back S x op j a)
    (k : Fin (d+1)) :
    decode (wire x (site S k))=slot op a j k.val := by
  rw [B.slots k,slot_codec op a j k.val O B.arg]

/-! The exact old-pair non-forward branch. The following private
    preparation is literally the forward prep; the equality proof
    unfolds sourceStep, so no assumed "all marks hold" field. -/

private def normalize (h : Bool) (u : BStarWidthTransfer.Source) : BStarWidthTransfer.Source :=
  let t := decode u.token
  let z := if h then u else {u with phase:=1,op:=0,flags:=0}
  if t.fault then {z with token:=encode t} else z

private theorem normalize_token (h : Bool) (u : BStarWidthTransfer.Source)
    (F : (decode u.token).fault=false) :
    (normalize h u).token=u.token := by
  cases h <;> simp [normalize,F]

private def nonFStep (h : Pair Bool) (u v : BStarWidthTransfer.Source) : Pair BStarWidthTransfer.Source :=
  let f := decode u.token
  let b := decode v.token
  let u' := normalize h.1 u
  let v' := normalize h.2 v
  let right := BStarWidthTransferPair.rightSource v
  if h.2 then
    (if f.tag==1 then {u' with token:=0} else u',right)
  else if b.tag==3 then ({u' with token:=encode b},{v' with token:=0})
  else if f.tag==1 && b.tag==0 then ({u' with token:=0},v')
  else (u',v')

private theorem source_nonF (c r i : Nat) (h : Pair Bool)
    (u v : BStarWidthTransfer.Source) (data : Data) (F : (decode u.token).tag≠2) :
    sourceStep c r i h u v data=nonFStep h u v := by
  -- CHECK: normalize is definitionally the private
  -- prep of BStarWidthTransferFull.lean:14–43, the real source.
  have FF : ((decode u.token).tag==2)=false := by simp [F]
  unfold sourceStep nonFStep
  dsimp only
  rw [FF] <;> rfl

private theorem inside_reverse (c r i : Nat) (h : Bool)
    (u v : BStarWidthTransfer.Source) (data : Data) (op a : Nat)
    (U : decode u.token=trailToken) (V : decode v.token=reply op a) :
    let z := sourceStep c r i (h,false) u v data
    z.1.token=encode (reply op a) ∧ z.2.token=encode emptyToken := by
  dsimp only
  have F : (decode u.token).tag≠2 := by rw [U]; decide
  rw [source_nonF c r i (h,false) u v data F]
  simp [nonFStep,V,reply] <;> rfl

private theorem inside_quiet (c r i : Nat) (h : Bool)
    (u v : BStarWidthTransfer.Source) (data : Data)
    (F : (decode u.token).tag≠2)
    (D : (decode v.token).tag≠3)
    (Z : ¬((decode u.token).tag=1 ∧ (decode v.token).tag=0))
    (U : (decode u.token).fault=false)
    (V : (decode v.token).fault=false) :
    let z := sourceStep c r i (h,false) u v data
    z.1.token=u.token ∧ z.2.token=v.token := by
  dsimp only
  have DD : ((decode v.token).tag==3)=false := by simp [D]
  have ZZ : ((decode u.token).tag==1 && (decode v.token).tag==0)=false := by
    apply Bool.eq_false_iff.mpr
    intro E
    exact Z (by simpa only [Bool.and_eq_true,beq_iff_eq] using E)
  rw [source_nonF c r i (h,false) u v data F]
  simp only [nonFStep,DD,ZZ,Bool.false_eq_true,if_false]
  exact ⟨normalize_token h u U,normalize_token false v V⟩

private theorem terminal_quiet (c r i : Nat) (h : Bool)
    (u v : BStarWidthTransfer.Source) (data : Data)
    (F : (decode u.token).tag≠2)
    (T : (decode u.token).tag≠1)
    (U : (decode u.token).fault=false) :
    (sourceStep c r i (h,true) u v data).1.token=u.token := by
  have TT : ((decode u.token).tag==1)=false := by simp [T]
  rw [source_nonF c r i (h,true) u v data F]
  simp only [nonFStep,if_true,TT,Bool.false_eq_true,if_false]
  exact normalize_token h u U

/-- The cursor moves precisely on the edge from k to k+1 when its
    old reply occupies k+1. No F branch exists in the reverse chart. -/
def moved (j k : Nat) : Nat := if j=k+1 then k else j

private theorem inside_slot_pair (c r i : Nat) (h : Bool)
    (u v : BStarWidthTransfer.Source) (data : Data) (op a j k : Nat)
    (O : op≤5) (A : DArg op a)
    (U : u.token=encode (slot op a j k))
    (V : v.token=encode (slot op a j (k+1))) :
    let p := sourceStep c r i (h,false) u v data
    p.1.token=encode (slot op a (moved j k) k) ∧
    p.2.token=encode (slot op a (moved j k) (k+1)) := by
  dsimp only
  have DU : decode u.token=slot op a j k :=
    (congrArg decode U).trans (slot_codec op a j k O A)
  have DV : decode v.token=slot op a j (k+1) :=
    (congrArg decode V).trans (slot_codec op a j (k+1) O A)
  by_cases M : j=k+1
  · have T : slot op a j k=trailToken := slot_before (by omega)
    have D : slot op a j (k+1)=reply op a := by
      rw [M,slot_at]
    simp only [moved,if_pos M]
    rw [slot_at,slot_after (show k<k+1 by omega)]
    exact inside_reverse c r i h u v data op a
      (DU.trans T) (DV.trans D)
  · have F : (decode u.token).tag≠2 := by
      rw [DU]
      exact slot_noF op a j k
    have D : (decode v.token).tag≠3 := by
      rw [DV]
      by_cases H : k+1<j
      · rw [slot_before H]; decide
      · rw [slot_after (show j<k+1 by omega)]; decide
    have Z : ¬((decode u.token).tag=1 ∧ (decode v.token).tag=0) := by
      rw [DU,DV]
      by_cases H : k<j
      · rw [slot_before H,slot_before (show k+1<j by omega)]
        decide
      · by_cases J : k=j
        · subst j
          rw [slot_at]
          simp [reply]
        · rw [slot_after (show j<k by omega)]
          simp [emptyToken]
    have HF : (decode u.token).fault=false := by
      rw [DU]; exact slot_healthy op a j k
    have HG : (decode v.token).fault=false := by
      rw [DV]; exact slot_healthy op a j (k+1)
    have Q := inside_quiet c r i h u v data F D Z HF HG
    simp only [moved,if_neg M]
    exact ⟨Q.1.trans U,Q.2.trans V⟩

private theorem moved_le (j k : Nat) : moved j k≤j := by
  unfold moved
  split <;> omega

private theorem slot_untouched (op a j k q : Nat)
    (A : q≠k) (B : q≠k+1) :
    slot op a j q=slot op a (moved j k) q := by
  by_cases M : j=k+1
  · subst j
    rw [show moved (k+1) k=k from if_pos rfl]
    by_cases H : q<k
    · rw [slot_before (show q<k+1 by omega),slot_before H]
    · rw [slot_after (show k+1<q by omega),
        slot_after (show k<q by omega)]
  · simp [moved,M]

/-! Lift the literal pair equations to every owned slot on the
    original physical tape; no quiet-neighbor assumption. -/

private theorem inlet_other (S : Sector h d) (x : Raw s n)
    (q : Fin (d+1)) (Q : q≠0) :
    wire (rawNext s x (inlet S)) (site S q)=wire x (site S q) :=
  remote_wire x _ _ (Ne.symm (inlet_not_site S q))
    (fun E=>Q (site_injective S (E.trans (inlet_eq S))))

theorem back_inside (P : Lower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op j a : Nat) (O : op≤5)
    (B : Back S x op j a) (k : Fin d) :
    Back S (rawNext s x (site S (west k))) op (moved j k.val) a := by
  let e := site S (west k)
  have N : 1<n := by have := S.room; omega
  have R := raw_sources P N x X e
  have K : rightNeighbor e=site S (east k) := internal_right S k
  have HH : P.h (rightNeighbor e)=false := by
    rw [K]
    exact internal_nonheader S k
  have W :
      (pairSources P x e).1.token=encode (slot op a (moved j k.val) k.val) ∧
      (pairSources P x e).2.token=encode (slot op a (moved j k.val) (k.val+1)) := by
    -- CHECK: src/token projection. The two input
    -- equations are exact raw wires, not merely decoded tags.
    unfold pairSources
    rw [HH,K]
    exact inside_slot_pair _ _ _ _ _ _ _ op a j k.val O B.arg
      (B.slots (west k)) (B.slots (east k))
  refine ⟨Nat.le_trans (moved_le j k.val) B.index,B.arg,
    nondoor_controller P S x X 2 op B.control e
      (Ne.symm (inlet_not_site S (west k))),?_⟩
  intro q
  by_cases A : q=west k
  · subst q
    exact (congrArg BStarWidthTransfer.Source.token R.1).trans W.1
  · by_cases C : q=east k
    · subst q
      rw [←K]
      exact (congrArg BStarWidthTransfer.Source.token R.2).trans W.2
    · have U : q.val≠k.val := fun E=>A (Fin.ext E)
      have V : q.val≠k.val+1 := fun E=>C (Fin.ext E)
      have F := remote_wire x e (site S q)
        (fun E=>A (site_injective S E))
        (fun E=>C (site_injective S (E.trans K)))
      exact F.trans ((B.slots q).trans
        (congrArg encode (slot_untouched op a j k.val q.val U V)))

theorem back_terminal (P : Lower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op j a : Nat) (O : op≤5)
    (B : Back S x op j a) :
    Back S (rawNext s x (site S (WidthWaitDrain.last d))) op j a := by
  let e := site S (WidthWaitDrain.last d)
  have N : 1<n := by have := S.room; omega
  have R := (raw_sources P N x X e).1
  have D : decode (src x e).token=slot op a j d :=
    back_decode S x op j a O B (WidthWaitDrain.last d)
  have F : (decode (src x e).token).tag≠2 := by
    rw [D]; exact slot_noF op a j d
  have T : (decode (src x e).token).tag≠1 := by
    rw [D]
    by_cases H : j=d
    · subst j
      rw [slot_at]
      simp [reply]
    · rw [slot_after (show j<d by have := B.index; omega)]
      decide
  have G : (decode (src x e).token).fault=false := by
    rw [D]; exact slot_healthy op a j d
  have W : (pairSources P x e).1.token=wire x e := by
    unfold pairSources
    rw [show P.h (rightNeighbor e)=true from outgoing_header S]
    exact terminal_quiet _ _ _ _ _ _ _ F T G
  refine ⟨B.index,B.arg,
    nondoor_controller P S x X 2 op B.control e
      (Ne.symm (inlet_not_site S (WidthWaitDrain.last d))),?_⟩
  intro q
  by_cases H : q=WidthWaitDrain.last d
  · subst q
    exact (congrArg BStarWidthTransfer.Source.token R).trans (W.trans (B.slots _))
  · exact (remote_wire x e (site S q)
      (fun E=>H (site_injective S E))
      (Ne.symm (outbound_not_site S q))).trans (B.slots q)

private theorem wait_on_trail (u : BStarWidthTransfer.Source) (op : Nat)
    (P : u.phase.toNat=2) (O : u.op.toNat=op) (B : op≤5)
    (T : decode u.token=trailToken) :
    BStarWidthTransferPair.rightSource u=u := by
  have N : ¬5<op := by omega
  simp [BStarWidthTransferPair.rightSource,BStarWidthTransferPair.holds,
    BStarWidthTransfer.door,P,O,N,T,trailToken]

theorem back_inlet_hold (P : Lower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op j a : Nat) (O : op≤5)
    (B : Back S x op j a) (J : 0<j) :
    Back S (rawNext s x (inlet S)) op j a := by
  have W := B.slots 0
  change (src x S.root).token=encode (slot op a j 0) at W
  rw [slot_before J] at W
  have T : decode (src x S.root).token=trailToken := by
    rw [W,WidthTokenTransport.trail_codec]
  have R := (door_source P S x X).trans
    (wait_on_trail (src x S.root) op B.control.1 B.control.2 O T)
  refine ⟨B.index,B.arg,
    ⟨(congrArg (fun u : BStarWidthTransfer.Source=>u.phase.toNat) R).trans B.control.1,
      (congrArg (fun u : BStarWidthTransfer.Source=>u.op.toNat) R).trans B.control.2⟩,?_⟩
  intro q
  by_cases Q : q=0
  · subst q
    exact (congrArg BStarWidthTransfer.Source.token R).trans (B.slots 0)
  · exact (inlet_other S x q Q).trans (B.slots q)

theorem back_exterior (P : Lower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op j a : Nat)
    (B : Back S x op j a) (e : Fin n)
    (I : e≠inlet S) (E : ¬∃ q : Fin (d+1), e=site S q) :
    Back S (rawNext s x e) op j a := by
  refine ⟨B.index,B.arg,
    nondoor_controller P S x X 2 op B.control e I,?_⟩
  intro q
  apply Eq.trans (remote_wire x e (site S q)
    (fun A=>E ⟨q,A.symm⟩) ?_) (B.slots q)
  intro A
  rcases incident S e q A.symm with H|⟨k,H⟩
  · exact I H
  · exact E ⟨west k,H⟩

/-! Actual root consumption. Non-COMPARE flag bits are deliberately
    not physically erased by the production responder. -/

def nextOp (op a : Nat) : Nat :=
  (WidthOwnerController.nextControl op a).1

theorem nextOp_bound (op a : Nat) (O : op≤5) : nextOp op a≤5 := by
  have K : op=0 ∨ op=1 ∨ op=2 ∨ op=3 ∨ op=4 ∨ op=5 := by omega
  rcases K with K|K|K|K|K|K <;> subst op <;>
    by_cases H : a=1 <;> simp [nextOp,WidthOwnerController.nextControl,H]

private def accepted (u : BStarWidthTransfer.Source) (op a : Nat) : BStarWidthTransfer.Source :=
  {u with phase:=1, op:=BitVec.ofNat 3 (nextOp op a), token:=encode emptyToken,
          flags:=(if op=2 then BitVec.ofNat 2 a else u.flags)}

private theorem right_accept (u : BStarWidthTransfer.Source) (op a : Nat)
    (P : u.phase.toNat=2) (C : u.op.toNat=op) (O : op≤5)
    (A : DArg op a) (W : u.token=encode (reply op a)) :
    BStarWidthTransferPair.rightSource u=accepted u op a := by
  have D : decode u.token=reply op a := by rw [W,dcodec op a O A]
  have K : op=0 ∨ op=1 ∨ op=2 ∨ op=3 ∨ op=4 ∨ op=5 := by omega
  -- CHECK: BStarWidthTransferPair.lean:47–50,160–164;
  -- BStarWidthTransfer.lean:25–51. The private accept holds flags
  -- unless opcode 2; its literal token 0 is encode emptyToken.
  rcases K with K|K|K|K|K|K <;>
    simp [BStarWidthTransferPair.rightSource,BStarWidthTransferPair.holds,
      BStarWidthTransfer.door,P,C,D,K,reply,accepted,nextOp,
      WidthOwnerController.nextControl] <;> first | rfl | exact ⟨rfl,rfl,rfl⟩

/-- Endpoint fact. This is intentionally not asserted to be a closed
    raw target under future marks: the next ISSUE may immediately launch. -/
structure Drained (S : Sector h d) (x : Raw s n) (op a : Nat) : Prop where
  arg : DArg op a
  control : Controller S x 1 (nextOp op a)
  empty : ∀ q : Fin (d+1), wire x (site S q)=encode emptyToken
  compare : op=2 →
    WidthOwnerController.argument (c:=s+11) (x S.root).widthClient=a

/-- This record is an actual old/new physical receipt, not the
    proposition that a current root happens to display ISSUE. -/
structure ConsumeMark (S : Sector h d) (x : Raw s n)
    (op a : Nat) : Prop where
  old : Back S x op 0 a
  post : Drained S (rawNext s x (inlet S)) op a
  dormant : op≠2 →
    (src (rawNext s x (inlet S)) S.root).flags=(src x S.root).flags

theorem back_root_consume (P : Lower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op a : Nat) (O : op≤5)
    (B : Back S x op 0 a) : ConsumeMark S x op a := by
  have N : 1<n := by have := S.room; omega
  have W := B.slots 0
  change (src x S.root).token=encode (slot op a 0 0) at W
  rw [slot_at] at W
  have R := (door_source P S x X).trans
    (right_accept (src x S.root) op a B.control.1 B.control.2 O B.arg W)
  have C : Controller S (rawNext s x (inlet S)) 1 (nextOp op a) := by
    unfold Controller
    rw [R]
    constructor
    · rfl
    · change (BitVec.ofNat 3 (nextOp op a)).toNat=nextOp op a
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by
        have := nextOp_bound op a O
        omega)]
  have Empty (q : Fin (d+1)) :
      wire (rawNext s x (inlet S)) (site S q)=encode emptyToken := by
    by_cases Q : q=0
    · subst q
      exact congrArg BStarWidthTransfer.Source.token R
    · have J : 0<q.val := by
        by_cases H : q.val=0
        · exact False.elim (Q (Fin.ext H))
        · omega
      rw [inlet_other S x q Q,B.slots q,slot_after J]
  have Compare (H : op=2) :
      WidthOwnerController.argument (c:=s+11)
        (rawNext s x (inlet S) S.root).widthClient=a := by
    have E : rightNeighbor (inlet S)=S.root := inlet_eq S
    have Header : (oldHeaders (rows s) (x S.root)).h6=true :=
      (P.frozen x X S.root).trans S.here
    have PH : WidthOwnerController.phase (c:=s+11)
        (x S.root).widthClient=2 := B.control.1
    have OP : WidthOwnerController.opcode (c:=s+11)
        (x S.root).widthClient=2 := B.control.2.trans H
    have PK : packet (c:=s+11) (x S.root).widthClient=reply op a := by
      change decode (src x S.root).token=reply op a
      rw [W,dcodec op a O B.arg]
    have A : a<4 := by simpa [DArg,H] using B.arg
    -- CHECK: WidthIssueTransport.lean:235–256 exact signature;
    -- these arguments are all facts about the old actual responder.
    have J := WidthIssueTransport.raw_incoming_compare_argument
      (s:=s) x (inlet S) (ShortResetCycle.edge_sep N (inlet S))
      (by rw [E]; exact Header)
      (by rw [E]; exact PH)
      (by rw [E]; exact OP)
      (by rw [E,PK]; rfl)
      (by rw [E,PK]; exact H)
      (by rw [E,PK]; rfl)
      (by rw [E,PK]; exact A)
    rw [E,PK] at J
    exact J
  refine ⟨B,⟨B.arg,C,Empty,Compare⟩,?_⟩
  intro H
  rw [R]
  simp [accepted,H]

/-! The actual old-pair mark classification. In this convention
    d=0 is allowed (L=1), so there are no internal marks then:
    a true turn at root needs exactly its incoming consume. -/

inductive Cursor where
  | back (j : Nat)
  | consumed
  deriving DecidableEq, Repr

def nominate (S : Sector h d) (j : Nat) : Fin n :=
  if j=0 then inlet S else nextAt S.root (j-1)

def next (S : Sector h d) (e : Fin n) : Cursor → Cursor
  | .consumed => .consumed
  | .back j =>
    if e=nominate S j then
      if j=0 then .consumed else .back (j-1)
    else .back j

private theorem nominate_site (S : Sector h d) (j : Nat)
    (J : j≤d) (Z : j≠0) :
    nominate S j=site S (⟨j-1,by omega⟩ : Fin (d+1)) := by
  simp [nominate,Z,WidthSectorGeometry.site]

private theorem inlet_nominate_iff (S : Sector h d) (j : Nat)
    (J : j≤d) : inlet S=nominate S j ↔ j=0 := by
  by_cases Z : j=0
  · simp [nominate,Z]
  · rw [nominate_site S j J Z]
    simp [inlet_not_site S _,Z]

private theorem inside_nominate_iff (S : Sector h d) (j : Nat)
    (J : j≤d) (k : Fin d) :
    site S (west k)=nominate S j ↔ j=k.val+1 := by
  by_cases Z : j=0
  · subst j
    have E : site S (west k)≠inlet S :=
      Ne.symm (inlet_not_site S (west k))
    simp [nominate,E]
  · rw [nominate_site S j J Z]
    constructor
    · intro E
      have V := congrArg Fin.val (site_injective S E)
      change k.val=j-1 at V
      omega
    · intro E
      apply congrArg (site S)
      apply Fin.ext
      change k.val=j-1
      omega

private theorem terminal_not_nominate (S : Sector h d) (j : Nat)
    (J : j≤d) : site S (WidthWaitDrain.last d)≠nominate S j := by
  by_cases Z : j=0
  · subst j
    simpa [nominate] using (Ne.symm (inlet_not_site S (WidthWaitDrain.last d)))
  · rw [nominate_site S j J Z]
    intro E
    have V := congrArg Fin.val (site_injective S E)
    change d=j-1 at V
    omega

private theorem exterior_not_nominate (S : Sector h d) (j : Nat)
    (J : j≤d) (e : Fin n)
    (I : e≠inlet S) (E : ¬∃ q : Fin (d+1), e=site S q) :
    e≠nominate S j := by
  by_cases Z : j=0
  · simpa [nominate,Z] using I
  · rw [nominate_site S j J Z]
    intro H
    exact E ⟨_,H⟩

/-- Every actual old physical mark, not just a selected itinerary.
    If the cursor stops, this very mark is the matching consume. -/
theorem generated_reverse_one_mark (P : Lower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op j a : Nat) (O : op≤5)
    (B : Back S x op j a) (e : Fin n) :
    match next S e (.back j) with
    | .back k => Back S (rawNext s x e) op k a
    | .consumed => j=0 ∧ e=inlet S ∧ ConsumeMark S x op a := by
  classical
  by_cases I : e=inlet S
  · subst e
    by_cases Z : j=0
    · subst j
      simpa [next,nominate] using
        (show 0=0 ∧ inlet S=inlet S ∧ ConsumeMark S x op a from
          ⟨rfl,rfl,back_root_consume P S x X op a O B⟩)
    · have V : inlet S≠nominate S j :=
        fun E=>Z ((inlet_nominate_iff S j B.index).mp E)
      simpa only [next,if_neg V] using
        back_inlet_hold P S x X op j a O B (by omega)
  · by_cases Q : ∃ q : Fin (d+1), e=site S q
    · obtain ⟨q,rfl⟩ := Q
      by_cases T : q.val=d
      · have E : q=WidthWaitDrain.last d := Fin.ext T
        subst q
        simpa only [next,if_neg (terminal_not_nominate S j B.index)] using
          back_terminal P S x X op j a O B
      · let k : Fin d := ⟨q.val,by have := q.isLt; omega⟩
        have E : west k=q := Fin.ext rfl
        rw [←E]
        have W := back_inside P S x X op j a O B k
        by_cases M : j=k.val+1
        · have H := (inside_nominate_iff S j B.index k).mpr M
          have Z : j≠0 := by omega
          have K : j-1=k.val := by omega
          simpa only [next,if_pos H,if_neg Z,K,moved,if_pos M] using W
        · have H : site S (west k)≠nominate S j :=
            fun E=>M ((inside_nominate_iff S j B.index k).mp E)
          simpa only [next,if_neg H,moved,if_neg M] using W
    · have H := exterior_not_nominate S j B.index e I Q
      simpa only [next,if_neg H] using back_exterior P S x X op j a B e I Q

/-! Stop at the first real consume, never use a terminal monitor flag
    to assert the cleared word at a later raw state. -/

def At (S : Sector h d) (x : Raw s n) (op a : Nat) : Cursor → Prop
  | .back j => Back S x op j a
  | .consumed => Drained S x op a

theorem step_active (P : Lower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op j a : Nat) (O : op≤5)
    (B : Back S x op j a) (e : Fin n) :
    At S (rawNext s x e) op a (next S e (.back j)) := by
  have H := generated_reverse_one_mark P S x X op j a O B e
  cases E : next S e (.back j) with
  | back k =>
    simp only [E] at H
    exact H
  | consumed =>
    simp only [E] at H
    obtain ⟨_,I,R⟩ := H
    subst e
    exact R.post

inductive Seen (P : Lower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op a : Nat) : List (Fin n) → Cursor → Prop where
  | seed : P.Post x0 → Turn S x0 op a → Seen P S x0 op a [] (.back d)
  | snoc {w j} (e : Fin n) :
      Seen P S x0 op a w (.back j) →
      Seen P S x0 op a (w++[e]) (next S e (.back j))

private theorem raw_snoc (x : Raw s n) (w : List (Fin n)) (e : Fin n) :
    rawRun x (w++[e])=rawNext s (rawRun x w) e := by
  induction w generalizing x with
  | nil => rfl
  | cons b w IH => exact IH (rawNext s x b)

private theorem raw_append (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u IH => exact IH (rawNext s x e)

theorem seen_active (P : Lower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op a : Nat) (O : op≤5)
    (w : List (Fin n)) (c : Cursor) (H : Seen P S x0 op a w c) :
    P.Post (rawRun x0 w) ∧ At S (rawRun x0 w) op a c := by
  have N : 1<n := by have := S.room; omega
  induction H with
  | seed X T => exact ⟨X,turn_back S x0 op a T⟩
  | @snoc w j e H IH =>
    rw [raw_snoc]
    exact ⟨P.post_closed N _ IH.1 e,
      step_active P S _ IH.1.1 op j a O IH.2 e⟩

theorem seen_last_consume (P : Lower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op a : Nat) (O : op≤5)
    (w : List (Fin n)) (c : Cursor) (H : Seen P S x0 op a w c)
    (E : c=.consumed) :
    ∃ u, w=u++[inlet S] ∧ Seen P S x0 op a u (.back 0) ∧
      ConsumeMark S (rawRun x0 u) op a := by
  cases H with
  | seed X T => cases E
  | @snoc w j e H =>
    have B := seen_active P S x0 op a O w (.back j) H
    have R := generated_reverse_one_mark P S (rawRun x0 w) B.1.1
      op j a O B.2 e
    -- CHECK: this is dependent elimination on Seen, not an
    -- inversion of a current source phase. E rewrites the match.
    rw [E] at R
    obtain ⟨J,I,C⟩ := R
    subst j
    subst e
    exact ⟨w,rfl,H,C⟩

/-- Feed an actual forward-generation prefix, not a caller's
    unhistorical raw Turn guess. -/
theorem seen_from_generated (P : Lower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op a : Nat) (O : op≤5) (u : List (Fin n))
    (G : Generated P S x0 op u (.turned a)) :
    Seen P S (rawRun x0 u) op a [] (.back d) :=
  .seed (generated_active P S x0 op O u (.turned a) G).1
    (generated_turn P S x0 op O u a G)

/-- A complete genuine source flight's endpoint, on the concatenated
    original tape: forward prefix, reverse prefix, last incoming mark.
    No intervening raw state is replaced with a normalized replay. -/
theorem generated_consume_clears_word (P : Lower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op a : Nat) (O : op≤5)
    (u v : List (Fin n)) (_G : Generated P S x0 op u (.turned a))
    (H : Seen P S (rawRun x0 u) op a v .consumed) :
    ∃ t, v=t++[inlet S] ∧
      ConsumeMark S (rawRun x0 (u++t)) op a ∧
      Drained S (rawRun x0 (u++v)) op a := by
  obtain ⟨t,E,_,R⟩ := seen_last_consume P S (rawRun x0 u) op a O
    v .consumed H rfl
  have D := (seen_active P S (rawRun x0 u) op a O v .consumed H).2
  refine ⟨t,E,?_,?_⟩
  · rw [raw_append]
    exact R
  · rw [raw_append]
    exact D

/-! Exact nomination count and original-mark stopped mean. -/

def rank : Cursor → Nat
  | .back j => j+1
  | .consumed => 0

def done (c : Cursor) : Prop := c=.consumed

theorem rank_mark (S : Sector h d) (j : Nat) (e : Fin n) :
    rank (next S e (.back j))=
      if e=nominate S j then j else j+1 := by
  by_cases E : e=nominate S j
  · by_cases Z : j=0 <;> simp [next,rank,E,Z] <;> omega
  · simp [next,rank,E]

def monitorNext (S : Sector h d) (z : Raw s n × Cursor)
    (e : Fin n) : Raw s n × Cursor :=
  (rawNext s z.1 e,next S e z.2)

theorem monitor_raw (S : Sector h d) (z : Raw s n × Cursor)
    (e : Fin n) :
    (monitorNext S z e).1=rawNext s z.1 e := rfl

theorem reverse_expected (P : Lower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op j a : Nat) (O : op≤5)
    (B : Back S x op j a) :
    Height.IIDExpectedHittingTimeAtMost (monitorNext S)
      (fun z=>done z.2) (x,.back j) (n*(j+1)) := by
  let Live := fun (z : Raw s n × Cursor) r =>
    ∃ k : Nat, z.2=.back k ∧ P.Post z.1 ∧
      Back S z.1 op k a ∧ r=k+1
  have N : 1<n := by have := S.room; omega
  have pos (z : Raw s n × Cursor) (r : Nat) (Z : Live z r) : 0<r := by
    obtain ⟨k,_,_,_,E⟩ := Z
    omega
  have advance (z : Raw s n × Cursor) (r : Nat) (Z : Live z r) :
      ∃ b : Fin n, ∀ e : Fin n,
        done (monitorNext S z e).2 ∨
          ∃ r',Live (monitorNext S z e) r' ∧ r'≤r ∧ (e=b → r'<r) := by
    obtain ⟨k,J,Q,A,E⟩ := Z
    subst r
    refine ⟨nominate S k,fun e=>?_⟩
    have H := generated_reverse_one_mark P S z.1 Q.1 op k a O A e
    have Q' := P.post_closed N z.1 Q e
    by_cases E : e=nominate S k
    · by_cases Z : k=0
      · left
        simp [monitorNext,J,next,E,Z,done]
      · have B' : Back S (rawNext s z.1 e) op (k-1) a := by
          simpa only [next,if_pos E,if_neg Z] using H
        right
        refine ⟨k-1+1,⟨k-1,?_,Q',B',rfl⟩,by omega,?_⟩
        · simp [monitorNext,J,next,E,Z]
        · intro _
          omega
    · have B' : Back S (rawNext s z.1 e) op k a := by
        simpa only [next,if_neg E] using H
      right
      refine ⟨k+1,⟨k,?_,Q',B',rfl⟩,Nat.le_refl _,?_⟩
      · simp [monitorNext,J,next,E]
      · intro H
        exact False.elim (E H)
  exact ResetReturnIID.iid_of_relational_rank (monitorNext S)
    (fun z=>done z.2) Live pos advance (x,.back j) (j+1)
    (.inr ⟨j,rfl,X,B,rfl⟩)

theorem turn_to_consume_mean (P : Lower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op a : Nat) (O : op≤5)
    (T : Turn S x op a) :
    Height.IIDExpectedHittingTimeAtMost (monitorNext S)
      (fun z=>done z.2) (x,.back d) (n*(d+1)) :=
  reverse_expected P S x X op d a O (turn_back S x op a T)

/-- The genuine receipt occurs at an actual prefix of the sampled word.
    Once stopped the observer may retain consumed while the raw system
    keeps running. We make no claim about Drained at that later endpoint. -/
theorem original_first_consume_receipt (P : Lower s n) (S : Sector P.h d)
    (x0 : Raw s n) (X : P.Post x0) (op a : Nat) (O : op≤5)
    (T : Turn S x0 op a) (w : List (Fin n))
    (D : done (SequentialMarkClock.run (monitorNext S)
      (x0,.back d) w).2) :
    ∃ u v, w=(u++[inlet S])++v ∧
      Seen P S x0 op a u (.back 0) ∧
      ConsumeMark S (rawRun x0 u) op a := by
  have aux (pre tail : List (Fin n)) (c : Cursor)
      (H : Seen P S x0 op a pre c)
      (D : done (SequentialMarkClock.run (monitorNext S)
        (rawRun x0 pre,c) tail).2) :
      ∃ p v, pre++tail=p++v ∧ Seen P S x0 op a p .consumed := by
    induction tail generalizing pre c with
    | nil =>
      have E : c=.consumed := D
      exact ⟨pre,[],by simp,E ▸ H⟩
    | cons e tail IH =>
      cases c with
      | consumed => exact ⟨pre,e::tail,rfl,H⟩
      | back j =>
        have H' := Seen.snoc e H
        have D' : done (SequentialMarkClock.run (monitorNext S)
            (rawRun x0 (pre++[e]),next S e (.back j)) tail).2 := by
          rw [raw_snoc]
          exact D
        -- CHECK: PhysicalCustody.lean:31–32 and the run recursion
        -- used by original_first_turn_receipt.
        obtain ⟨p,v,E,R⟩ := IH (pre++[e]) _ H' D'
        exact ⟨p,v,by simpa only [List.append_assoc,List.singleton_append]
          using E,R⟩
  obtain ⟨p,v,E,H⟩ := aux [] w (.back d) (.seed X T) D
  obtain ⟨u,U,G,R⟩ := seen_last_consume P S x0 op a O p .consumed H rfl
  refine ⟨u,v,?_,G,R⟩
  simpa only [List.nil_append,U] using E

/-- Direct history-authenticated first-consume export with the
    original forward seed included. -/
theorem original_generated_first_consume (P : Lower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op a : Nat) (O : op≤5)
    (f w : List (Fin n)) (G : Generated P S x0 op f (.turned a))
    (D : done (SequentialMarkClock.run (monitorNext S)
      (rawRun x0 f,.back d) w).2) :
    ∃ u v, w=(u++[inlet S])++v ∧
      ConsumeMark S (rawRun x0 (f++u)) op a ∧
      Drained S (rawRun x0 (f++(u++[inlet S]))) op a := by
  have X := generated_active P S x0 op O f (.turned a) G
  obtain ⟨u,v,E,_,R⟩ := original_first_consume_receipt P S
    (rawRun x0 f) X.1 op a O (generated_turn P S x0 op O f a G) w D
  refine ⟨u,v,E,?_,?_⟩
  · rw [raw_append]
    exact R
  · rw [raw_append,raw_snoc]
    exact R.post

#print axioms slot_codec
#print axioms turn_back
#print axioms source_nonF
#print axioms back_inside
#print axioms back_terminal
#print axioms back_inlet_hold
#print axioms back_root_consume
#print axioms generated_reverse_one_mark
#print axioms seen_active
#print axioms seen_last_consume
#print axioms generated_consume_clears_word
#print axioms rank_mark
#print axioms reverse_expected
#print axioms turn_to_consume_mean
#print axioms original_first_consume_receipt
#print axioms original_generated_first_consume

end L4.WidthFreshReverse


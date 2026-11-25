import Leader.L4.WidthFreshReverse
import Leader.L4.WidthPackJoint
import Leader.L4.ReportDigitArithmetic

namespace L4.WidthChooseEpoch

open AllSizeProtocol PhysicalCustody
open BStarH6WordChart (oldH6)
open BStarH6Ordinal
open WidthSectorGeometry WidthFreshForward
open BStarWidthTransferDepart (Data readData execute)
open WidthByteRows (Token encode decode emptyToken trailToken)
open ReportDigitArithmetic (digit cmp cmpFold compareCode)

set_option maxRecDepth 12000
set_option maxHeartbeats 6000000

variable {s n d : Nat}

/-! S indexes 0..d, NOT 0..d-1. L = d+1 is the physical word
length and c = s+11 is the number of counter digits. -/

abbrev wordData {h : Fin n → Bool} (S : Sector h d)
    (x : Raw s n) (i : Fin (d+1)) : Data :=
  dat x (site S i)

def bit (p : Prop) [Decidable p] : BitVec 1 := if p then 1 else 0

theorem bit_nat (p : Prop) [Decidable p] :
    (bit p).toNat = (decide p).toNat := by
  by_cases H : p <;> simp [bit,H]

theorem digit_lt_two (j x : Nat) : digit 2 j x < 2 :=
  Nat.mod_lt _ (by decide)

theorem digit_bv (j x : Nat) :
    (BitVec.ofNat 1 (digit 2 j x)).toNat = digit 2 j x := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (digit_lt_two j x)

structure Room (s d : Nat) : Prop where
  cells : s+11 ≤ d+1
  width : d+1 < 2^(s+11)
  rpos : 0 < radWidth s
  rfit : radWidth s < 2^(s+11)

/-- The production numeric room is earned from the certified actual gap,
    not by pretending that a ring contains exactly c physical cells. -/
theorem room_of_post (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (hs : 6≤s) : Room s d := by
  have M : oldH6 (rows s) x=P.h :=
    funext (P.frozen x X.1)
  have G := P.spacing x X.1
  unfold WidthPackedBridge.CertifiedSpacing at G
  rw [M] at G
  obtain ⟨l,lo,hi,g⟩ := G S.root S.here
  have E := WidthOrdinalSpan.gap_unique g S.gap
  subst l
  obtain ⟨_,U⟩ := WidthRatioArithmetic.production_bounds hs
  have H := Nat.le_trans hi U
  have Ppos : 0 < 2^s := Nat.pow_pos (by decide)
  have Rpos : 2 ≤ 2^s :=
    Nat.pow_le_pow_right (by decide : 0<2) (show 1≤s by omega)
  have R : radWidth s=2^s-1 := rfl
  have F : 2^(s+11)=2048*2^s := by rw [Nat.pow_add]; omega
  have B : 16*(s+1) ≤ 16*(s+1)*(radiusTwo s+1) := by
    simpa using Nat.mul_le_mul_left (16*(s+1))
      (show 1≤radiusTwo s+1 by omega)
  exact ⟨by omega,by omega,by omega,by omega⟩

/-! Actual all-mark data frame. This is independent of source PC,
    compare argument, inherited old K and foreign owners. -/

private theorem typed_data (c r i : Nat) (h : Pair Bool)
    (u v : BStarWidthTransferFull.Cell) :
    let z := BStarWidthTransferFull.step c r i h (u,v)
    z.1.data = (if (decode u.source.token).tag==2 then
      (execute c r i u.data (decode u.source.token)).1 else u.data) ∧
      z.2.data=v.data := by
  unfold BStarWidthTransferFull.step
  dsimp only
  split
  · split <;> exact ⟨rfl,rfl⟩
  · split
    · split <;> exact ⟨rfl,rfl⟩
    · split
      · exact ⟨rfl,rfl⟩
      · split <;> exact ⟨rfl,rfl⟩

theorem raw_data_pair (P : WidthLower s n) (N : 1<n)
    (x : Raw s n) (X : P.Q x) (e : Fin n) :
    dat (rawNext s x e) e =
      (if (decode (wire x e)).tag==2 then
        (execute (s+11) (radWidth s) (eff P x e)
          (dat x e) (decode (wire x e))).1 else dat x e) ∧
    dat (rawNext s x e) (rightNeighbor e)=dat x (rightNeighbor e) := by
  let v := rightNeighbor e
  let u0 : BitVec (WidthByteRows.W (s+11)) := (x e).widthClient
  let v0 : BitVec (WidthByteRows.W (s+11)) := (x v).widthClient
  let h := (P.h e,P.h v)
  have A := BStarWidthTransferMark.mark_transfer (c:=s+11)
    (radWidth s) h (u0,v0)
  have B := congrArg
    (fun p : Pair (BStarWidthTransferMark.Site (s+11)) =>
      (p.1.work.data,p.2.work.data)) A
  have hu : (oldHeaders (rows s) (x e)).h6=P.h e := P.frozen x X e
  have hv : (oldHeaders (rows s) (x v)).h6=P.h v := P.frozen x X v
  have L : rawNext s x e e=(largePair (rows s) (x e,x v)).1 := by
    simp [rawNext,AllSizeS1Geometry.step,v]
  have R : rawNext s x e v=(largePair (rows s) (x e,x v)).2 := by
    simp [rawNext,AllSizeS1Geometry.step,v,Ne.symm (ShortResetCycle.edge_sep N e)]
  have J : (dat (rawNext s x e) e,dat (rawNext s x e) v)=
      Pair.map BStarWidthTransferFull.Cell.data
        (BStarWidthTransferFull.step (s+11) (radWidth s) (eff P x e) h
          (BStarWidthTransferFull.read (c:=s+11) u0,
            BStarWidthTransferFull.read (c:=s+11) v0)) := by
    refine Eq.trans (b := (readData (c:=s+11) (largePair (rows s) (x e,x v)).1.widthClient,
      readData (c:=s+11) (largePair (rows s) (x e,x v)).2.widthClient)) ?_ ?_
    · exact Prod.ext
        (congrArg (fun (p : LargeSite (WidthJoinedProjection.P s)) => readData (c:=s+11) p.widthClient) L)
        (congrArg (fun (p : LargeSite (WidthJoinedProjection.P s)) => readData (c:=s+11) p.widthClient) R)
    -- CHECK: exactly the same joined-width definitional projection as
    -- raw_sources; BStarWidthTransferMark.lean:68–71.
    change
      (readData (c:=s+11)
        (patchPair ((ShortGeo.width (s+11)).patches (s+11)
          ((oldHeaders (rows s) (x e)).h6,(oldHeaders (rows s) (x v)).h6)
          (u0,v0) (BStarShort.widthWork (c:=s+11) (radWidth s)
          ((oldHeaders (rows s) (x e)).h6,(oldHeaders (rows s) (x v)).h6)
          (u0,v0))) (u0,v0)).1,
       readData (c:=s+11)
        (patchPair ((ShortGeo.width (s+11)).patches (s+11)
          ((oldHeaders (rows s) (x e)).h6,(oldHeaders (rows s) (x v)).h6)
          (u0,v0) (BStarShort.widthWork (c:=s+11) (radWidth s)
          ((oldHeaders (rows s) (x e)).h6,(oldHeaders (rows s) (x v)).h6)
          (u0,v0))) (u0,v0)).2)=_
    rw [hu,hv]
    exact B
  have T := typed_data (s+11) (radWidth s) (eff P x e) h
    (BStarWidthTransferFull.read (c:=s+11) u0)
    (BStarWidthTransferFull.read (c:=s+11) v0)
  exact ⟨(congrArg Prod.fst J).trans T.1,(congrArg Prod.snd J).trans T.2⟩

theorem raw_data_at (P : WidthLower s n) (N : 1<n)
    (x : Raw s n) (X : P.Q x) (e q : Fin n) :
    dat (rawNext s x e) q =
      if q=e then
        if (decode (wire x e)).tag==2 then
          (execute (s+11) (radWidth s) (eff P x e)
            (dat x e) (decode (wire x e))).1 else dat x e
      else dat x q := by
  by_cases H : q=e
  · subst q
    simpa only [if_true] using (raw_data_pair P N x X e).1
  · rw [if_neg H]
    by_cases J : q=rightNeighbor e
    · subst q
      exact (raw_data_pair P N x X e).2
    · simp [dat,rawNext,AllSizeS1Geometry.step,H,J]

theorem eff_site (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (i : Fin (d+1)) :
    eff P x (site S i)=min (s+11) i.val := by
  have O := WidthPackJoint.ordinal_of_gap P.hh
    ⟨S.root,S.here⟩ S.gap i.isLt
  have F := (WidthCacheAllSites.width_raw_fields P.h P.hh P.Q x X
    (site S i)).1
  change ordinal P.h P.hh (site S i)=i.val at O
  rw [O] at F
  -- CHECK: WidthByteRows.lean:11,24 and WidthCacheAllSites:10.
  change ((WidthByteRows.offField (s+11)).read
    (x (site S i)).widthClient).toNat=min (s+11) i.val at F
  by_cases Z : i.val=0
  · have I : i=0 := Fin.ext Z
    subst i
    change (if P.h S.root then 0 else _) = min (s+11) 0
    simp [S.here]
  · have H : P.h (site S i)=false :=
      S.gap.interior i.val (by omega) i.isLt
    have E := congrArg (Nat.min (s+11)) F
    unfold eff WidthByteRows.offset
    rw [H]
    simp only [Bool.false_eq_true,if_false]
    refine E.trans ?_
    exact Nat.min_eq_right (Nat.min_le_left _ _)

/-! Transport boundary: exact decoded clean rail, on the very same
    physical tape. No data equation or semantic comparison is supplied.
    A back state retains the final *forward* argument a in the ghost;
    the actual D wire contains finishArg op a. -/

inductive Cursor (d : Nat) where
  | issue (a : Nat)
  | out (i : Fin (d+1)) (a : Nat)
  | back (i : Fin (d+1)) (a : Nat)
  | consumed (a : Nat)
  deriving DecidableEq

def spent : Cursor d → Nat
  | .issue _ => 0
  | .out i _ => i.val
  | .back _ _ => d+1
  | .consumed _ => d+1

def payload : Cursor d → Nat
  | .issue a | .out _ a | .back _ a | .consumed a => a

def live : Cursor d → Prop
  | .consumed _ => False
  | _ => True

def railToken (op : Nat) (f : Cursor d) (i : Fin (d+1)) : Token :=
  match f with
  | .issue _ | .consumed _ => emptyToken
  | .out k a =>
      if i.val<k.val then trailToken else if i=k then fwd op a else emptyToken
  | .back k a =>
      if i.val<k.val then trailToken else if i=k then reply op (finishArg op a)
      else emptyToken

structure Rail {h : Fin n → Bool} (S : Sector h d)
    (x : Raw s n) (op : Nat) (f : Cursor d) : Prop where
  arg : FArg op (payload f)
  tokens : ∀ i, decode (wire x (site S i))=railToken op f i
  source : match f with
    | .issue a => Controller S x 1 op ∧ a=initialArg op (src x S.root).flags.toNat
    | .out _ _ | .back _ _ => Controller S x 2 op
    | .consumed _ => True

def cursorNext (P : WidthLower s n) (S : Sector P.h d)
    (op : Nat) (x : Raw s n) (e : Fin n) (f : Cursor d) : Cursor d :=
  match f with
  | .issue a => if e=inlet S then .out 0 a else f
  | .out k a => if e=site S k then
      let b := advancedArg P x e op a
      if J : k.val<d then .out ⟨k.val+1,by omega⟩ b else .back k b
    else f
  | .back k a =>
      if J : k.val=0 then
        if e=inlet S then .consumed a else f
      else
        let j : Fin (d+1) := ⟨k.val-1,by have := k.isLt; omega⟩
        if e=site S j then .back j a else f
  | .consumed _ => f

/-- ONLY the clean flight/return producer from the preceding rounds.
    In particular no F3 correctness, no completed-cycle safety and no
    progress bound is a field of this structure. -/
structure CleanTransport (P : WidthLower s n) (S : Sector P.h d) : Prop where
  step : ∀ x op f e, op≤5 → P.Post x → Rail S x op f → live f →
    Rail S (rawNext s x e) op (cursorNext P S op x e f)

/-- Front supplies the exact live F and protected prefix. The
    clean-age producer supplies E on the suffix; arbitrary-suffix Front
    alone does not suffice. -/
theorem front_tokens (S : Sector h d) (x : Raw s n) (op : Nat)
    (O : op≤5) (k : Fin (d+1)) (a : Nat)
    (F : Front S x op k.val a)
    (E : ∀ i : Fin (d+1), k.val<i.val →
      decode (wire x (site S i))=emptyToken) :
    Rail S x op (.out k a) := by
  refine ⟨F.arg,?_,F.control⟩
  intro i
  by_cases H : i.val<k.val
  · simp only [railToken,if_pos H]
    rw [F.trail i H,WidthTokenTransport.trail_codec]
  · by_cases J : i=k
    · subst i
      have W : wire x (site S k)=encode (fwd op a) := F.liveWire
      simp [railToken,W,fcodec op a O F.arg]
    · have I : k.val<i.val := by
        have N : i.val≠k.val := fun Z=>J (Fin.ext Z)
        omega
      simp [railToken,H,J,E i I]

def Departs {h : Fin n → Bool} (S : Sector h d)
    (f : Cursor d) (e : Fin n) : Prop :=
  ∃ k a, f=.out k a ∧ e=site S k

theorem no_depart_data (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op : Nat) (f : Cursor d)
    (R : Rail S x op f) (e : Fin n) (H : ¬Departs S f e) :
    ∀ i, wordData S (rawNext s x e) i=wordData S x i := by
  intro i
  have N : 1<n := by have := S.room; omega
  change dat (rawNext s x e) (site S i)=dat x (site S i)
  rw [raw_data_at P N x X.1 e (site S i)]
  by_cases J : site S i=e
  · subst e
    rw [if_pos rfl]
    have T := R.tokens i
    rw [T]
    have B : (railToken op f i).tag≠2 := by
      cases f with
      | issue a => simp [railToken,emptyToken]
      | consumed a => simp [railToken,emptyToken]
      | back k a =>
        simp only [railToken]
        split
        · decide
        · split
          · simp [reply]
          · decide
      | out k a =>
        have I : i≠k := by
          intro V
          subst k
          exact H ⟨i,a,rfl,rfl⟩
        simp only [railToken,if_neg I]
        split <;> decide
    simp [beq_false_of_ne B]
  · rw [if_neg J]

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

/-! A single generic sweep theorem: the semantic plan is proved against
    execute on OLD data, then attached to actual raw marks. -/

structure Plan (s L op : Nat) (v : Fin L → Data) where
  arg : Nat → Nat
  after : Fin L → Data
  law : ∀ i : Fin L,
    execute (s+11) (radWidth s) (min (s+11) i.val) (v i)
      (fwd op (arg i.val))=(after i,fwd op (arg (i.val+1)))

structure Sweep {h : Fin n → Bool} (S : Sector h d)
    (x : Raw s n) (op : Nat) (v : Fin (d+1) → Data)
    (A : Plan s (d+1) op v) (f : Cursor d) : Prop where
  arg : payload f=A.arg (spent f)
  data : ∀ i, wordData S x i =
    if i.val<spent f then A.after i else v i

theorem sweep_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op : Nat) (v : Fin (d+1)→Data)
    (A : Plan s (d+1) op v) (f : Cursor d)
    (R : Rail S x op f) (H : Sweep S x op v A f) (e : Fin n) :
    Sweep S (rawNext s x e) op v A (cursorNext P S op x e f) := by
  classical
  by_cases D : Departs S f e
  · obtain ⟨k,a,F,E⟩ := D
    subst f
    subst e
    have C : a=A.arg k.val := H.arg
    have V : wordData S x k=v k := by
      simpa [spent] using H.data k
    have T : decode (wire x (site S k))=fwd op a := by
      simpa [railToken] using R.tokens k
    have U := A.law k
    rw [←C] at U
    have Off := eff_site P S x X k
    have L : execute (s+11) (radWidth s) (eff P x (site S k))
        (dat x (site S k)) (fwd op a)=
        (A.after k,fwd op (A.arg (k.val+1))) := by
      rw [Off]
      change dat x (site S k)=v k at V
      rw [V]
      exact U
    have Arg : advancedArg P x (site S k) op a=A.arg (k.val+1) := by
      unfold advancedArg
      rw [L]
      rfl
    have N := depart_cursor P S x op k a
    refine ⟨by rw [N.1,N.2,Arg],?_⟩
    intro i
    rw [N.1]
    have NS : 1<n := by have := S.room; omega
    change dat (rawNext s x (site S k)) (site S i)=_
    rw [raw_data_at P NS x X.1]
    by_cases J : i=k
    · subst i
      simp only [T,fwd,beq_self_eq_true,if_true,if_pos (Nat.lt_succ_self k.val)]
      exact congrArg Prod.fst L
    · have NE : site S i≠site S k := fun Z=>J (site_injective S Z)
      rw [if_neg NE]
      have Old := H.data i
      change dat x (site S i)=(if i.val<k.val then A.after i else v i) at Old
      rw [Old]
      have I : i.val≠k.val := fun Z=>J (Fin.ext Z)
      by_cases B : i.val<k.val
      · simp [B,show i.val<k.val+1 by omega]
      · simp [B,show ¬i.val<k.val+1 by omega]
  · have J := quiet_cursor P S x op e f D
    refine ⟨by rw [J.1,J.2,H.arg],?_⟩
    intro i
    rw [J.1,no_depart_data P S x X op f R e D i,H.data i]

/-! A history contains all the raw marks, including every foreign
    interaction. It cannot step past its first consumed cursor. -/

inductive Walk (P : WidthLower s n) (S : Sector P.h d)
    (op : Nat) (x0 : Raw s n) (a0 : Nat) :
    List (Fin n) → Cursor d → Prop where
  | start : P.Post x0 → Rail S x0 op (.issue a0) →
      Walk P S op x0 a0 [] (.issue a0)
  | snoc {w f} (e : Fin n) :
      Walk P S op x0 a0 w f → live f →
      Walk P S op x0 a0 (w++[e])
        (cursorNext P S op (rawRun x0 w) e f)

private theorem raw_snoc (x : Raw s n) (w : List (Fin n)) (e : Fin n) :
    rawRun x (w++[e])=rawNext s (rawRun x w) e := by
  induction w generalizing x with
  | nil => rfl
  | cons i w IH => exact IH (rawNext s x i)

theorem walk_invariant (P : WidthLower s n) (S : Sector P.h d)
    (C : CleanTransport P S) (op : Nat) (O : op≤5)
    (x0 : Raw s n) (a0 : Nat) (A : Plan s (d+1) op (wordData S x0))
    (I : a0=A.arg 0) (w : List (Fin n)) (f : Cursor d)
    (W : Walk P S op x0 a0 w f) :
    P.Post (rawRun x0 w) ∧ Rail S (rawRun x0 w) op f ∧
      Sweep S (rawRun x0 w) op (wordData S x0) A f := by
  have N : 1<n := by have := S.room; omega
  induction W with
  | start X R =>
    exact ⟨X,R,⟨I,fun _=>rfl⟩⟩
  | @snoc w f e W L IH =>
    rw [raw_snoc]
    exact ⟨P.post_closed N _ IH.1 e,
      C.step _ _ _ _ O IH.1 IH.2.1 L,
      sweep_step P S _ IH.1 op _ A f IH.2.1 IH.2.2 e⟩

/-! Actual consume, not a PC-only receipt. R includes a matching D of
    the current generated command at K0, every other slot E. -/

def nextOp (op a : Nat) : Nat :=
  match op with
  | 0 => 1
  | 1 => if a=1 then 2 else 5
  | 2 => 3
  | 3 => 4
  | 4 => 1
  | _ => 0

theorem consume_pc (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op a : Nat) (O : op≤5)
    (R : Rail S x op (.back 0 a)) :
    Controller S (rawNext s x (inlet S)) 1 (nextOp op (finishArg op a)) := by
  have P0 : (src x S.root).phase.toNat=2 := R.source.1
  have O0 : (src x S.root).op.toNat=op := R.source.2
  have D : decode (src x S.root).token=reply op (finishArg op a) := by
    exact R.tokens 0
  have E := door_source P S x X.1
  have B : ¬5<op := by omega
  unfold Controller
  rw [E]
  have K : op=0 ∨ op=1 ∨ op=2 ∨ op=3 ∨ op=4 ∨ op=5 := by omega
  rcases K with K|K|K|K|K|K <;>
    simp [BStarWidthTransferPair.rightSource,BStarWidthTransferPair.holds,
      BStarWidthTransfer.door,P0,O0,D,reply,nextOp,K] <;>
    try exact ⟨rfl,rfl⟩
  by_cases J : finishArg 1 a=1 <;> simp only [J,if_true,if_false] <;> exact ⟨rfl,rfl⟩

theorem consume_compare_saved (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (a : Nat)
    (R : Rail S x 2 (.back 0 a)) :
    (src (rawNext s x (inlet S)) S.root).flags.toNat=finishArg 2 a := by
  have N : 1<n := by have := S.room; omega
  have E : rightNeighbor (inlet S)=S.root := inlet_eq S
  have H : (oldHeaders (rows s) (x S.root)).h6=true :=
    (P.frozen x X.1 S.root).trans S.here
  have D : decode (src x S.root).token=reply 2 (finishArg 2 a) := by
    exact R.tokens 0
  have A : finishArg 2 a<4 :=
    (finish_good 2 a (by decide) R.arg).2
  have Pc : WidthOwnerController.phase (c:=s+11) (x S.root).widthClient=2 :=
    R.source.1
  have Op : WidthOwnerController.opcode (c:=s+11) (x S.root).widthClient=2 :=
    R.source.2
  have K : WidthChecksum.packet (c:=s+11) (x S.root).widthClient=
      reply 2 (finishArg 2 a) := D
  have M := WidthIssueTransport.raw_incoming_compare_argument
    x (inlet S) (ShortResetCycle.edge_sep N (inlet S))
    (E.symm ▸ H) (E.symm ▸ Pc) (E.symm ▸ Op)
    (E.symm ▸ (congrArg Token.tag K)) (E.symm ▸ (congrArg Token.op K))
    (E.symm ▸ (congrArg Token.fault K))
    (E.symm ▸ (show (WidthChecksum.packet (c:=s+11)
      (x S.root).widthClient).arg<4 by rw [K]; exact A))
  rw [E,K] at M
  exact M

/-- The endpoint is tied to a literal final mark, not defined to be
    any state whose data looks like a completed command. -/
structure Receipt (P : WidthLower s n) (S : Sector P.h d)
    (op a0 : Nat) (x y : Raw s n) where
  tape : List (Fin n)
  a : Nat
  flight : Walk P S op x a0 tape (.back 0 a)
  endpoint : y=rawNext s (rawRun x tape) (inlet S)

theorem receipt_word (P : WidthLower s n) (S : Sector P.h d)
    (C : CleanTransport P S) (op : Nat) (O : op≤5)
    (x y : Raw s n) (a0 : Nat) (A : Plan s (d+1) op (wordData S x))
    (I : a0=A.arg 0) (R : Receipt P S op a0 x y) :
    P.Post y ∧ wordData S y=A.after ∧ R.a=A.arg (d+1) ∧
    Controller S y 1 (nextOp op (finishArg op R.a)) ∧
    (∀ i : Fin (d+1), decode (wire y (site S i))=emptyToken) ∧
    (op=2 → (src y S.root).flags.toNat=finishArg op R.a) := by
  obtain ⟨w,f,flight,endpoint⟩ := R
  subst y
  let z := rawRun x w
  have H := walk_invariant P S C op O x a0 A I w _ flight
  have N : 1<n := by have := S.room; omega
  have U := C.step z op (.back 0 f) (inlet S) O H.1 H.2.1 (by trivial)
  have V := sweep_step P S z H.1 op _ A (.back 0 f) H.2.1 H.2.2 (inlet S)
  have T : cursorNext P S op z (inlet S) (.back 0 f)=.consumed f := by
    simp [cursorNext]
  rw [T] at U V
  refine ⟨P.post_closed N z H.1 _,?_,H.2.2.arg,
    consume_pc P S z H.1 op f O H.2.1,?_,?_⟩
  · funext i
    simpa [spent,i.isLt] using V.data i
  · exact U.tokens
  · intro E
    subst op
    exact consume_compare_saved P S z H.1 f H.2.1

/-! The outer-loop data predicates. The dormant count digits outside c
    are irrelevant; the WIDTH5 command writes zero there. -/

def Count (s L : Nat) (v : Fin L→Data) (j : Nat) : Prop :=
  ∀ i, i.val<s+11 → (v i).count.toNat=digit 2 i.val j

def Flags (s L : Nat) (v : Fin L→Data) (j : Nat) : Prop :=
  ∀ i, i.val<j → (v i).inside=bit (i.val<radWidth s) ∧
    (v i).last=bit (i.val+1=radWidth s)

structure Outer (s L : Nat) (v : Fin L→Data) (j : Nat) : Prop where
  bound : j≤L
  done : ∀ i, (v i).done=bit (i.val<j)
  pick : ∀ i, (v i).pick=bit (i.val+1=j)
  count : Count s L v j
  flags : Flags s L v j

structure Selected (s L : Nat) (v : Fin L→Data) (j : Nat) : Prop where
  bound : j≤L
  done : ∀ i, (v i).done=bit (i.val<j+1)
  pick : ∀ i, (v i).pick=bit (i.val=j)
  count : Count s L v j
  flags : Flags s L v j

structure Published (s L : Nat) (v : Fin L→Data) (j : Nat) : Prop where
  bound : j<L
  done : ∀ i, (v i).done=bit (i.val<j+1)
  pick : ∀ i, (v i).pick=bit (i.val=j)
  count : Count s L v j
  flags : Flags s L v (j+1)

structure Finished (s L : Nat) (v : Fin L→Data) : Prop where
  done : ∀ i, (v i).done=1
  pick : ∀ i, (v i).pick=0
  count : Count s L v L
  flags : Flags s L v L
  shadow : ∀ i, (v i).width =
    if i.val<s+11 then BitVec.ofNat 1 (digit 2 i.val L) else 0

theorem reset_seed (s L : Nat) (v : Fin L→Data)
    (H : ∀ i, (v i).done=0 ∧ (v i).pick=0 ∧ (v i).count=0) :
    Outer s L v 0 := by
  refine ⟨by omega,?_,?_,?_,?_⟩
  · intro i
    simpa [bit] using (H i).1
  · intro i
    simpa [bit] using (H i).2.1
  · intro i _
    simp [H i |>.2.2,digit]
  · intro i I
    omega

/-! CHOOSE: a unique first unvisited site, including the no-choice case. -/

def chooseArg (j k : Nat) : Nat := if j<k then 1 else 0

def chooseData {L : Nat} (v : Fin L→Data) (j : Nat)
    (i : Fin L) : Data :=
  {v i with done:=bit (i.val<j+1),pick:=bit (i.val=j)}

def choosePlan {s L : Nat} {v : Fin L→Data} {j : Nat}
    (H : Outer s L v j) : Plan s L 1 v where
  arg := chooseArg j
  after := chooseData v j
  law := by
    intro i
    have D := H.done i
    rcases Nat.lt_trichotomy i.val j with B|B|B
    · have H1 : ¬j<i.val := by omega
      have H2 : ¬j<i.val+1 := by omega
      have H3 : i.val<j+1 := by omega
      have H4 : i.val≠j := by omega
      simp [execute,fwd,chooseArg,chooseData,D,bit,B,H1,H2,H3,H4]
    · have H1 : j<i.val+1 := by omega
      have H2 : ¬j<i.val := by omega
      have H3 : ¬i.val<j := by omega
      simp [execute,fwd,chooseArg,chooseData,D,bit,B]
    · have H1 : ¬i.val<j := by omega
      have H2 : ¬i.val<j+1 := by omega
      have H3 : i.val≠j := by omega
      have H4 : j<i.val+1 := by omega
      simp [execute,fwd,chooseArg,chooseData,D,bit,B,H1,H2,H3,H4]

theorem choose_selected {s L : Nat} {v : Fin L→Data} {j : Nat}
    (H : Outer s L v j) : Selected s L (chooseData v j) j :=
  ⟨H.bound,fun _=>rfl,fun _=>rfl,H.count,H.flags⟩

theorem choose_unique {s L : Nat} {v : Fin L→Data} {j : Nat}
    (_H : Outer s L v j) (J : j<L) :
    ∃ k : Fin L, (chooseData v j k).pick=1 ∧
      ∀ i, (chooseData v j i).pick=1 → i=k := by
  refine ⟨⟨j,J⟩,by simp [chooseData,bit],?_⟩
  intro i I
  by_cases E : i.val=j
  · exact Fin.ext E
  · simp [chooseData,bit,E] at I

theorem choose_none {s L : Nat} {v : Fin L→Data}
    (_H : Outer s L v L) :
    chooseArg L L=0 ∧ ∀ i, (chooseData v L i).pick=0 := by
  refine ⟨by simp [chooseArg],?_⟩
  intro i
  simp [chooseData,bit,Nat.ne_of_lt i.isLt]

/-! COMPARE: exact base-2 low-to-high fold. Use the checked radix
    prefix theorem rather than a second induction over natural bits. -/

private theorem cmp_lt_three (x y k : Nat) : cmpFold 2 y x k<3 := by
  rw [ReportDigitArithmetic.cmp_prefix 2 y x k (by decide)]
  unfold compareCode
  split
  · decide
  · split <;> decide

def compareArg (s j k : Nat) : Nat :=
  4*cmpFold 2 (radWidth s) j (min (s+11) k) +
    cmpFold 2 (radWidth s-1) j (min (s+11) k)

def comparePlan {s L : Nat} {v : Fin L→Data} {j : Nat}
    (H : Count s L v j) : Plan s L 2 v where
  arg := compareArg s j
  after := v
  law := by
    intro i
    by_cases I : i.val<s+11
    · have M : min (s+11) i.val=i.val := Nat.min_eq_right (by omega)
      have M' : min (s+11) (i.val+1)=i.val+1 := Nat.min_eq_right (by omega)
      have B := cmp_lt_three j (radWidth s-1) i.val
      have D : (compareArg s j i.val)/4=cmpFold 2 (radWidth s) j i.val := by
        unfold compareArg
        rw [M]
        omega
      have E : (compareArg s j i.val)%4=cmpFold 2 (radWidth s-1) j i.val := by
        unfold compareArg
        rw [M]
        omega
      -- CHECK: execute:36–41, ReportDigitArithmetic.cmpFold:13–15.
      simp only [execute,fwd,Bool.false_eq_true,if_false,M,I,if_pos,
        D,E,H i I,Nat.shiftRight_eq_div_pow]
      unfold compareArg
      rw [M']
      rfl
    · have M : min (s+11) i.val=s+11 := Nat.min_eq_left (by omega)
      have M' : min (s+11) (i.val+1)=s+11 := Nat.min_eq_left (by omega)
      have J : ¬min (s+11) i.val<s+11 := by rw [M]; omega
      simp [execute,fwd,compareArg,M,M']

def publishArg (s j : Nat) : Nat :=
  2*(decide (j<radWidth s)).toNat+(decide (j+1=radWidth s)).toNat

theorem publishArg_bound (s j : Nat) : publishArg s j<4 := by
  unfold publishArg
  cases (decide (j<radWidth s)) <;> cases (decide (j+1=radWidth s)) <;> decide

private theorem cmp_code_one (a b : Nat) :
    (compareCode a b==1).toNat=(decide (a<b)).toNat := by
  unfold compareCode
  by_cases H : a<b
  · simp [H]
  · by_cases J : b<a <;> simp [H,J]

private theorem cmp_code_zero (a b : Nat) :
    (compareCode a b==0).toNat=(decide (a=b)).toNat := by
  unfold compareCode
  rcases Nat.lt_trichotomy a b with H|H|H
  · simp [H,show a≠b by omega]
  · simp [H]
  · simp [H,show ¬a<b by omega,show a≠b by omega]

theorem compare_complete (R : Room s d) (j : Nat) (J : j≤d+1) :
    finishArg 2 (compareArg s j (d+1))=publishArg s j := by
  have X : j<2^(s+11) := by have := R.width; omega
  have Y : radWidth s-1<2^(s+11) := by have := R.rfit; omega
  have B := ReportDigitArithmetic.full_cmp 2 (s+11) (radWidth s)
    j (by decide) X R.rfit
  have C := ReportDigitArithmetic.full_cmp 2 (s+11) (radWidth s-1)
    j (by decide) X Y
  have L := cmp_lt_three j (radWidth s-1) (s+11)
  have M : min (s+11) (d+1)=s+11 := Nat.min_eq_left R.cells
  have D : compareArg s j (d+1)/4=cmpFold 2 (radWidth s) j (s+11) := by
    unfold compareArg
    rw [M]
    omega
  have E : compareArg s j (d+1)%4=cmpFold 2 (radWidth s-1) j (s+11) := by
    unfold compareArg
    rw [M]
    omega
  have I : (j=radWidth s-1) ↔ (j+1=radWidth s) := by
    have := R.rpos
    omega
  simp [finishArg,D,E,B,C,cmp_code_one,cmp_code_zero,publishArg,I]

/-! PUBLISH uses the saved two-bit argument from the actual matching D2.
    The old unique pick, not the direction of the current interaction,
    determines the only write to IN/LAST. -/

private theorem publish_high (s j : Nat) :
    BitVec.ofNat 1 (publishArg s j/2)=bit (j<radWidth s) := by
  by_cases A : j<radWidth s <;> by_cases B : j+1=radWidth s <;>
    simp [publishArg,bit,A,B]

private theorem publish_low (s j : Nat) :
    BitVec.ofNat 1 (publishArg s j%2)=bit (j+1=radWidth s) := by
  by_cases A : j<radWidth s <;> by_cases B : j+1=radWidth s <;>
    simp [publishArg,bit,A,B]

def publishData {s L : Nat} (v : Fin L→Data) (j : Nat)
    (i : Fin L) : Data :=
  if i.val=j then
    {v i with inside:=bit (j<radWidth s),last:=bit (j+1=radWidth s)}
  else v i

def publishPlan {s L : Nat} {v : Fin L→Data} {j : Nat}
    (H : Selected s L v j) : Plan s L 3 v where
  arg := fun _=>publishArg s j
  after := publishData (s:=s) v j
  law := by
    intro i
    have V := H.pick i
    by_cases J : i.val=j
    · simp [execute,fwd,publishData,J,V,bit,publish_high,publish_low]
    · simp [execute,fwd,publishData,J,V,bit]

theorem publish_published {s L : Nat} {v : Fin L→Data} {j : Nat}
    (H : Selected s L v j) (J : j<L) :
    Published s L (publishData (s:=s) v j) j := by
  refine ⟨J,?_,?_,?_,?_⟩
  · intro i
    by_cases E : i.val=j <;> simp [publishData,E,H.done i]
  · intro i
    by_cases E : i.val=j <;> simp [publishData,E,H.pick i]
  · intro i I
    by_cases E : i.val=j <;> simp [publishData,E,H.count i I]
  · intro i I
    by_cases E : i.val=j
    · simp [publishData,E]
    · have U : i.val<j := by omega
      simpa [publishData,E] using H.flags i U

/-! ADVANCE: independent arithmetic of the binary carry. This is
    ReportDigitArithmetic.increment_step:73–87 specialized to base 2;
    that declaration is private, so the proof is repeated, not invoked. -/

private theorem div_succ (x p : Nat) (P : 0<p) :
    (x+1)/p=x/p+(x%p+1)/p := by
  have H : x+1=x%p+1+p*(x/p) := by
    have := Nat.mod_add_div x p
    omega
  rw [H,Nat.add_mul_div_left _ _ P,Nat.add_comm]

def carry (x k : Nat) : Nat := (x%2^k+1)/2^k

theorem ripple_digit (x i : Nat) :
    (digit 2 i x+carry x i)%2=digit 2 i (x+1) ∧
    (digit 2 i x+carry x i)/2=carry x (i+1) := by
  have P : 0<2^i := Nat.pow_pos (by decide)
  unfold carry digit
  rw [div_succ x _ P,Nat.mod_add_mod]
  constructor
  · rfl
  · rw [ReportDigitArithmetic.split_prefix,Nat.pow_succ,←Nat.div_div_eq_div_mul]
    simp only [digit]
    rw [show x%2^i+2^i*(x/2^i%2)+1 =
      x%2^i+1+2^i*(x/2^i%2) by omega,
      Nat.add_mul_div_left _ _ P,Nat.add_comm ((x%2^i+1)/2^i)]

def advanceData {s L : Nat} (v : Fin L→Data) (j : Nat)
    (i : Fin L) : Data :=
  if i.val<s+11 then {v i with count:=BitVec.ofNat 1 (digit 2 i.val (j+1))}
  else v i

def advancePlan {s L : Nat} {v : Fin L→Data} {j : Nat}
    (H : Count s L v j) : Plan s L 4 v where
  arg := fun k=>carry j (min (s+11) k)
  after := advanceData (s:=s) v j
  law := by
    intro i
    by_cases I : i.val<s+11
    · have M : min (s+11) i.val=i.val := Nat.min_eq_right (by omega)
      have M' : min (s+11) (i.val+1)=i.val+1 := Nat.min_eq_right (by omega)
      have H1 := ripple_digit j i.val
      have A : (carry j i.val+digit 2 i.val j)%2=digit 2 i.val (j+1) := by
        rw [Nat.add_comm]; exact H1.1
      have B : (carry j i.val+digit 2 i.val j)/2=carry j (i.val+1) := by
        rw [Nat.add_comm]; exact H1.2
      simp [execute,fwd,advanceData,I,M,M',H i I,A,B]
    · have M : min (s+11) i.val=s+11 := Nat.min_eq_left (by omega)
      have M' : min (s+11) (i.val+1)=s+11 := Nat.min_eq_left (by omega)
      simp [execute,fwd,advanceData,I,M,M']

theorem advance_outer {s L : Nat} {v : Fin L→Data} {j : Nat}
    (H : Published s L v j) :
    Outer s L (advanceData (s:=s) v j) (j+1) := by
  refine ⟨by have := H.bound; omega,?_,?_,?_,?_⟩
  · intro i
    by_cases E : i.val<s+11 <;> simp [advanceData,E,H.done i]
  · intro i
    have Q : (i.val+1=j+1) ↔ (i.val=j) := by omega
    by_cases E : i.val<s+11 <;> simp [advanceData,E,H.pick i]
  · intro i I
    simp [advanceData,I,digit_lt_two]
  · intro i I
    by_cases E : i.val<s+11 <;> simpa [advanceData,E] using H.flags i I

theorem advance_keeps_pick {s L : Nat} (v : Fin L→Data) (j : Nat)
    (i : Fin L) : (advanceData (s:=s) v j i).pick=(v i).pick := by
  by_cases E : i.val<s+11 <;> simp [advanceData,E]

/-! WIDTH at the actual completed count, not at an inherited F5. -/

def widthData {s L : Nat} (v : Fin L→Data) (i : Fin L) : Data :=
  {v i with width:=if i.val<s+11 then (v i).count else 0}

def widthPlan (s L : Nat) (v : Fin L→Data) : Plan s L 5 v where
  arg := fun _=>0
  after := widthData (s:=s) v
  law := by
    intro i
    by_cases I : i.val<s+11
    · have M : min (s+11) i.val=i.val := Nat.min_eq_right (by omega)
      simp [execute,fwd,widthData,M,I]
    · have M : min (s+11) i.val=s+11 := Nat.min_eq_left (by omega)
      simp [execute,fwd,widthData,M,I]

theorem width_finished {s L : Nat} {v : Fin L→Data}
    (H : Selected s L v L) : Finished s L (widthData (s:=s) v) := by
  refine ⟨?_,?_,H.count,H.flags,?_⟩
  · intro i
    have I : i.val<L+1 := by have := i.isLt; omega
    simpa [widthData,bit,I] using H.done i
  · intro i
    simpa [widthData,bit,Nat.ne_of_lt i.isLt] using H.pick i
  · intro i
    by_cases I : i.val<s+11
    · simp only [widthData,if_pos I]
      apply BitVec.eq_of_toNat_eq
      rw [H.count i I,digit_bv]
    · simp [widthData,I]

/-! User-facing raw command lemmas. Every result is tied to the actual
    Receipt (actual clean-generated tape and final inlet). This is not
    an assumption that a command with the desired data can be completed. -/

theorem choose_receipt (P : WidthLower s n) (S : Sector P.h d)
    (C : CleanTransport P S) (x y : Raw s n) (j : Nat)
    (H : Outer s (d+1) (wordData S x) j)
    (R : Receipt P S 1 0 x y) :
    Selected s (d+1) (wordData S y) j ∧
    Controller S y 1 (if j<d+1 then 2 else 5) ∧
    (∀ i : Fin (d+1), decode (wire y (site S i))=emptyToken) := by
  have I : 0=(choosePlan H).arg 0 := by simp [choosePlan,chooseArg]
  have V := receipt_word P S C 1 (by decide) x y 0 (choosePlan H) I R
  have E : wordData S y=chooseData (wordData S x) j := V.2.1
  have A : R.a=chooseArg j (d+1) := V.2.2.1
  refine ⟨E.symm ▸ choose_selected H,?_,V.2.2.2.2.1⟩
  have K := V.2.2.2.1
  rw [A] at K
  by_cases J : j<d+1 <;> simpa [nextOp,finishArg,chooseArg,J] using K

theorem compare_receipt (P : WidthLower s n) (S : Sector P.h d)
    (C : CleanTransport P S) (B : Room s d) (x y : Raw s n) (j : Nat)
    (H : Selected s (d+1) (wordData S x) j)
    (R : Receipt P S 2 0 x y) :
    Selected s (d+1) (wordData S y) j ∧
    Controller S y 1 3 ∧
    (src y S.root).flags.toNat=publishArg s j ∧
    (∀ i : Fin (d+1), decode (wire y (site S i))=emptyToken) := by
  have I : 0=(comparePlan H.count).arg 0 := by
    simp [comparePlan,compareArg,cmpFold]
  have V := receipt_word P S C 2 (by decide) x y 0 (comparePlan H.count) I R
  have E : wordData S y=wordData S x := V.2.1
  have A : R.a=compareArg s j (d+1) := V.2.2.1
  have F := V.2.2.2.2.2 rfl
  rw [A,compare_complete B j H.bound] at F
  exact ⟨E.symm ▸ H,by simpa [nextOp] using V.2.2.2.1,F,V.2.2.2.2.1⟩

/-- Exact ISSUE3 seed: both saved flags are supplied by the actual D2
    consume theorem; no guessed fresh argument. The Rail invariant keeps
    this relation until the actual next inlet launch. -/
theorem publish_issue_seed (S : Sector h d) (x : Raw s n)
    (j : Nat) (PC : Controller S x 1 3)
    (A : (src x S.root).flags.toNat=publishArg s j)
    (E : ∀ i, decode (wire x (site S i))=emptyToken) :
    Rail S x 3 (.issue (publishArg s j)) := by
  refine ⟨?_,E,PC,?_⟩
  · exact publishArg_bound s j
  · simp [initialArg,A]

theorem publish_receipt (P : WidthLower s n) (S : Sector P.h d)
    (C : CleanTransport P S) (x y : Raw s n) (j : Nat) (J : j<d+1)
    (H : Selected s (d+1) (wordData S x) j)
    (R : Receipt P S 3 (publishArg s j) x y) :
    Published s (d+1) (wordData S y) j ∧ Controller S y 1 4 ∧
    (∀ i : Fin (d+1), decode (wire y (site S i))=emptyToken) := by
  have V := receipt_word P S C 3 (by decide) x y (publishArg s j)
    (publishPlan H) rfl R
  have E : wordData S y=publishData (s:=s) (wordData S x) j := V.2.1
  exact ⟨E.symm ▸ publish_published H J,
    by simpa [nextOp] using V.2.2.2.1,V.2.2.2.2.1⟩

theorem advance_receipt (P : WidthLower s n) (S : Sector P.h d)
    (C : CleanTransport P S) (x y : Raw s n) (j : Nat)
    (H : Published s (d+1) (wordData S x) j)
    (R : Receipt P S 4 1 x y) :
    Outer s (d+1) (wordData S y) (j+1) ∧ Controller S y 1 1 ∧
    (∀ i : Fin (d+1), decode (wire y (site S i))=emptyToken) := by
  have I : 1=(advancePlan H.count).arg 0 := by simp [advancePlan,carry,Nat.mod_one]
  have V := receipt_word P S C 4 (by decide) x y 1 (advancePlan H.count) I R
  have E : wordData S y=advanceData (s:=s) (wordData S x) j := V.2.1
  exact ⟨E.symm ▸ advance_outer H,
    by simpa [nextOp] using V.2.2.2.1,V.2.2.2.2.1⟩

theorem width_receipt (P : WidthLower s n) (S : Sector P.h d)
    (C : CleanTransport P S) (x y : Raw s n)
    (H : Selected s (d+1) (wordData S x) (d+1))
    (R : Receipt P S 5 0 x y) :
    Finished s (d+1) (wordData S y) ∧ Controller S y 1 0 ∧
    (∀ i : Fin (d+1), decode (wire y (site S i))=emptyToken) := by
  have V := receipt_word P S C 5 (by decide) x y 0
    (widthPlan s (d+1) (wordData S x)) rfl R
  have E : wordData S y=widthData (s:=s) (wordData S x) := V.2.1
  exact ⟨E.symm ▸ width_finished H,
    by simpa [nextOp] using V.2.2.2.1,V.2.2.2.2.1⟩

/-- One full successful iteration, with all four receipts on contiguous
    pieces of the actual word. No future receipt can be chosen on a
    different raw endpoint. -/
structure Iteration (P : WidthLower s n) (S : Sector P.h d)
    (j : Nat) (x y : Raw s n) where
  c : Raw s n
  m : Raw s n
  p : Raw s n
  choose : Receipt P S 1 0 x c
  compare : Receipt P S 2 0 c m
  publish : Receipt P S 3 (publishArg s j) m p
  advance : Receipt P S 4 1 p y

theorem iteration_outer (P : WidthLower s n) (S : Sector P.h d)
    (C : CleanTransport P S) (B : Room s d) (j : Nat) (J : j<d+1)
    (x y : Raw s n) (H : Outer s (d+1) (wordData S x) j)
    (R : Iteration P S j x y) :
    Outer s (d+1) (wordData S y) (j+1) ∧ Controller S y 1 1 ∧
    (∀ i : Fin (d+1), decode (wire y (site S i))=emptyToken) := by
  have A := choose_receipt P S C x R.c j H R.choose
  have M := compare_receipt P S C B R.c R.m j A.1 R.compare
  have Q := publish_receipt P S C R.m R.p j J M.1 R.publish
  exact advance_receipt P S C R.p y j Q.1 R.advance

/-- Finite chain of genuinely completed iterations, starting with the
    actual genuine BEGIN0-consume seed supplied by the predecessor.
    This is a trace predicate, not an existence/mean hypothesis. -/
inductive Iterations (P : WidthLower s n) (S : Sector P.h d)
    (x0 : Raw s n) : Nat → Raw s n → Prop where
  | zero : Iterations P S x0 0 x0
  | succ {j x y} : Iterations P S x0 j x → j<d+1 →
      Iteration P S j x y → Iterations P S x0 (j+1) y

theorem iterations_outer (P : WidthLower s n) (S : Sector P.h d)
    (C : CleanTransport P S) (B : Room s d)
    (x0 : Raw s n) (H : Outer s (d+1) (wordData S x0) 0)
    (j : Nat) (y : Raw s n) (R : Iterations P S x0 j y) :
    Outer s (d+1) (wordData S y) j := by
  induction R with
  | zero => exact H
  | succ R J I IH => exact (iteration_outer P S C B _ J _ _ IH I).1

theorem finish_cycle (P : WidthLower s n) (S : Sector P.h d)
    (C : CleanTransport P S) (B : Room s d)
    (x0 x u y : Raw s n)
    (Z : ∀ i : Fin (d+1), (wordData S x0 i).done=0 ∧
      (wordData S x0 i).pick=0 ∧ (wordData S x0 i).count=0)
    (R : Iterations P S x0 (d+1) x)
    (N : Receipt P S 1 0 x u)
    (W : Receipt P S 5 0 u y) :
    Finished s (d+1) (wordData S y) ∧ Controller S y 1 0 ∧
    (∀ i : Fin (d+1), decode (wire y (site S i))=emptyToken) := by
  have H := iterations_outer P S C B x0 (reset_seed s (d+1) _ Z) (d+1) x R
  have K := choose_receipt P S C x u (d+1) H N
  exact width_receipt P S C u y K.1 W

#print axioms raw_data_pair
#print axioms eff_site
#print axioms sweep_step
#print axioms walk_invariant
#print axioms consume_compare_saved
#print axioms receipt_word
#print axioms compare_complete
#print axioms ripple_digit
#print axioms iteration_outer
#print axioms finish_cycle

end L4.WidthChooseEpoch


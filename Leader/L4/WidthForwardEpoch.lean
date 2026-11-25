import Leader.L4.WidthRawWaitClock
import Leader.L4.WidthIssueTransport
import Leader.L4.WidthCacheAllSites
import Leader.L4.WidthPackedBridge
import Leader.L4.ShortChartOwnership
import Leader.L4.BStarWidthTransferMark
import Leader.L4.ResetReturnIID
import Leader.L4.MonitorRawBridge

namespace L4.WidthFreshForward

open AllSizeProtocol PhysicalCustody BStarH6WordChart
open WidthSectorGeometry ShortResetChart
open WidthByteRows WidthWaitDrain
open BStarWidthTransfer (Source readSource)
open BStarWidthTransferDepart (Data readData execute)

set_option maxRecDepth 12000
set_option maxHeartbeats 6000000

variable {s n d : Nat} {h : Fin n → Bool}

/-- Input from the genuinely permanent lower stage. Cache is *earned*
    using width_raw, not a field assumed true at the cold H6 entrance.
    No condition on WIDTH data, controller or K bytes is hidden here. -/
structure WidthLower (s n : Nat) where
  Q : Raw s n → Prop
  closed : ∀ x e, Q x → Q (rawNext s x e)
  h : Fin n → Bool
  frozen : ∀ x, Q x → ∀ i, oldH6 (rows s) x i=h i
  hh : ∃ i,h i=true
  spacing : ∀ x,Q x → WidthPackedBridge.CertifiedSpacing x

abbrev WidthLower.Post (P : WidthLower s n) (x : Raw s n) : Prop :=
  WidthCacheAllSites.WidthCorrect P.h P.hh P.Q x

theorem WidthLower.post_closed (P : WidthLower s n) (N : 1<n)
    (x : Raw s n) (X : P.Post x) (e : Fin n) :
    P.Post (rawNext s x e) :=
  (WidthCacheAllSites.width_raw N P.h P.hh P.Q P.closed P.frozen x X.1).1 x e X

theorem WidthLower.cache_mean (P : WidthLower s n) (N : 1<n)
    (x : Raw s n) (X : P.Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) P.Post x ((s+12)*n^2) :=
  (MonitorRawBridge.height_iff_row (rawNext s) P.Post x _).mp
    (WidthCacheAllSites.width_raw N P.h P.hh P.Q P.closed P.frozen x X).2

def src (x : Raw s n) (q : Fin n) : BStarWidthTransfer.Source :=
  readSource (c:=s+11) (x q).widthClient

def dat (x : Raw s n) (q : Fin n) : Data :=
  readData (c:=s+11) (x q).widthClient

def wire (x : Raw s n) (q : Fin n) : BitVec 16 := (src x q).token

def eff (P : WidthLower s n) (x : Raw s n) (q : Fin n) : Nat :=
  WidthByteRows.offset (c:=s+11) (P.h q) (x q).widthClient

/-- The logical forward/return syntax is the canonical *wire* syntax.
    The old payload is not a guessed source value. -/
def fwd (op a : Nat) : Token := {tag:=2,op:=op,arg:=a}
def reply (op a : Nat) : Token := {tag:=3,op:=op,arg:=a}

/-- Both ternary COMPARE coordinates must avoid forbidden value 3. -/
def FArg (op a : Nat) : Prop :=
  match op with
  | 0 => a=0
  | 1 => a<2
  | 2 => a/4<3 ∧ a%4<3
  | 3 => a<4
  | 4 => a<2
  | 5 => a=0
  | _ => False

def DArg (op a : Nat) : Prop :=
  if op=1 then a<2 else if op=2 then a<4 else a=0

private instance (op a : Nat) : Decidable (FArg op a) := by
  unfold FArg
  split <;> infer_instance

private instance (op a : Nat) : Decidable (DArg op a) := by
  unfold DArg
  split
  · infer_instance
  · split <;> infer_instance

private theorem fArg_bound (op a : Nat) (O : op≤5) (A : FArg op a) : a<16 := by
  have J : op=0 ∨ op=1 ∨ op=2 ∨ op=3 ∨ op=4 ∨ op=5 := by omega
  rcases J with E|E|E|E|E|E <;> subst op <;> simp [FArg] at A <;> omega

private theorem dArg_bound (op a : Nat) (A : DArg op a) : a<16 := by
  unfold DArg at A
  split at A <;> try split at A <;> omega
  all_goals omega

private theorem fcodec_fin :
    ∀ (o : Fin 6) (a : Fin 16), FArg o.val a.val →
      decode (encode (fwd o.val a.val))=fwd o.val a.val := by decide

private theorem dcodec_fin :
    ∀ (o : Fin 6) (a : Fin 16), DArg o.val a.val →
      decode (encode (reply o.val a.val))=reply o.val a.val := by decide

theorem fcodec (op a : Nat) (O : op≤5) (A : FArg op a) :
    decode (encode (fwd op a))=fwd op a :=
  fcodec_fin ⟨op,by omega⟩ ⟨a,fArg_bound op a O A⟩ A

theorem dcodec (op a : Nat) (O : op≤5) (A : DArg op a) :
    decode (encode (reply op a))=reply op a :=
  dcodec_fin ⟨op,by omega⟩ ⟨a,dArg_bound op a A⟩ A

def initialArg (op flags : Nat) : Nat :=
  if op==3 then flags else if op==4 then 1 else 0

private theorem initial_good_fin :
    ∀ (op : Fin 6) (a : Fin 4), FArg op.val (initialArg op.val a.val) := by decide

theorem initial_good (op a : Nat) (O : op≤5) (A : a<4) :
    FArg op (initialArg op a) :=
  initial_good_fin ⟨op,by omega⟩ ⟨a,A⟩

private theorem cmp_three (b x a : Nat) (A : a<3) :
    (if b<x then 1 else if x<b then 2 else a)<3 := by
  split
  · decide
  split
  · decide
  · exact A

/-- The actual typed operation table never faults a healthy issued
    token, even on arbitrary old DONE/PICK/count data. This is the
    semantic preservation needed in addition to the checked tag rank.
    COMPARE cannot generate a forbidden ternary coordinate. -/
theorem execute_good (c r i : Nat) (v : Data) (op a : Nat)
    (O : op≤5) (A : FArg op a) :
    let t := (execute c r i v (fwd op a)).2
    t=fwd op t.arg ∧ FArg op t.arg := by
  have J : op=0 ∨ op=1 ∨ op=2 ∨ op=3 ∨ op=4 ∨ op=5 := by omega
  rcases J with E|E|E|E|E|E <;> subst op
  · simpa [execute,fwd,FArg] using A
  · have U : a<2 := A
    let b := (v.done.toNat==0 && a==0).toNat
    have B : b<2 := by
      dsimp [b]
      cases (v.done.toNat==0 && a==0) <;> decide
    have H : a ||| b < 2 := Nat.or_lt_two_pow (n:=1) U B
    -- CHECK: BStarWidthTransferDepart.lean:31–35.
    exact ⟨rfl,H⟩
  · have U : a/4<3 ∧ a%4<3 := A
    by_cases I : i<c
    · let p := if v.count.toNat < (r >>> i)%2 then 1 else
          if (r >>> i)%2 < v.count.toNat then 2 else a/4
      let q := if v.count.toNat < ((r-1) >>> i)%2 then 1 else
          if ((r-1) >>> i)%2 < v.count.toNat then 2 else a%4
      have P : p<3 := cmp_three _ _ _ U.1
      have Q : q<3 := cmp_three _ _ _ U.2
      have B : FArg 2 (4*p+q) := by
        change (4*p+q)/4<3 ∧ (4*p+q)%4<3
        omega
      -- CHECK: execute:36–41; only the old count digit is read.
      simpa [execute,fwd,I,p,q] using And.intro
        (rfl : fwd 2 (4*p+q)=fwd 2 (4*p+q)) B
    · simpa [execute,fwd,I] using And.intro (rfl : fwd 2 a=fwd 2 a) A
  · by_cases I : v.pick.toNat=1 <;>
      simpa [execute,fwd,I] using And.intro (rfl : fwd 3 a=fwd 3 a) A
  · have U : a<2 := A
    have B : v.count.toNat<2 := v.count.isLt
    by_cases I : i<c
    · have H : FArg 4 ((a+v.count.toNat)/2) := by
        change (a+v.count.toNat)/2<2
        omega
      simpa [execute,fwd,I] using And.intro
        (rfl : fwd 4 ((a+v.count.toNat)/2)=fwd 4 ((a+v.count.toNat)/2)) H
    · simpa [execute,fwd,I] using And.intro (rfl : fwd 4 a=fwd 4 a) A
  · simpa [execute,fwd] using And.intro (rfl : fwd 5 a=fwd 5 a) A

def finishArg (op a : Nat) : Nat :=
  if op==1 then a else if op==2 then
    2*(a/4==1).toNat+(a%4==0).toNat else 0

private theorem finish_good_fin :
    ∀ (o : Fin 6) (a : Fin 16), FArg o.val a.val →
      finish (fwd o.val a.val)=reply o.val (finishArg o.val a.val) ∧
      DArg o.val (finishArg o.val a.val) := by decide

theorem finish_good (op a : Nat) (O : op≤5) (A : FArg op a) :
    finish (fwd op a)=reply op (finishArg op a) ∧
    DArg op (finishArg op a) :=
  finish_good_fin ⟨op,by omega⟩ ⟨a,fArg_bound op a O A⟩ A

/-! Exact old-pair source projection. The helper expression is
    definitionally the source part of the checked typed step, not an
    assumed source frame. Its fields are raw phase/op/flags/token. -/

private def prep (h : Bool) (u : BStarWidthTransfer.Source) : BStarWidthTransfer.Source :=
  let t := decode u.token
  let z := if h then u else {u with phase:=1,op:=0,flags:=0}
  if t.fault then {z with token:=encode t} else z

def sourceStep (c r i : Nat) (h : Pair Bool) (u v : BStarWidthTransfer.Source) (data : Data) :
    Pair (BStarWidthTransfer.Source) :=
  let f := decode u.token
  let b := decode v.token
  let u' := prep h.1 u
  let v' := prep h.2 v
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

theorem sourceStep_eq (c r i : Nat) (h : Pair Bool)
    (u v : BStarWidthTransferFull.Cell) :
    Pair.map BStarWidthTransferFull.Cell.source
      (BStarWidthTransferFull.step c r i h (u,v)) =
      sourceStep c r i h u.source v.source u.data := by
  -- CHECK: BStarWidthTransferFull.lean:14–43. Both private
  -- prep/canon and this prep unfold to the same record update.
  unfold BStarWidthTransferFull.step sourceStep
  dsimp only
  split
  · split <;> rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

def pairSources (P : WidthLower s n) (x : Raw s n) (e : Fin n) :
    Pair (BStarWidthTransfer.Source) :=
  sourceStep (s+11) (radWidth s) (eff P x e)
    (P.h e,P.h (rightNeighbor e)) (src x e) (src x (rightNeighbor e)) (dat x e)

set_option maxHeartbeats 200000 in
theorem raw_sources (P : WidthLower s n) (N : 1<n)
    (x : Raw s n) (X : P.Q x) (e : Fin n) :
    src (rawNext s x e) e=(pairSources P x e).1 ∧
      src (rawNext s x e) (rightNeighbor e)=(pairSources P x e).2 := by
  let v := rightNeighbor e
  let h := (P.h e,P.h v)
  let u : BitVec (WidthByteRows.W (s+11)) := (x e).widthClient
  let w : BitVec (WidthByteRows.W (s+11)) := (x v).widthClient
  have A := BStarWidthTransferMark.mark_transfer (c:=s+11) (radWidth s) h (u,w)
  have B := congrArg
    (fun p : Pair (BStarWidthTransferMark.Site (s+11)) =>
      (p.1.work.source,p.2.work.source)) A
  -- CHECK: mark_transfer:68–71 and WidthJoinedProjection:53–62.
  -- The widthClient of largePair is literally this patched work pair.
  have hu : (oldHeaders (rows s) (x e)).h6=P.h e := P.frozen x X e
  have hv : (oldHeaders (rows s) (x v)).h6=P.h v := P.frozen x X v
  have L : rawNext s x e e=(largePair (rows s) (x e,x v)).1 := by
    simp [rawNext,AllSizeS1Geometry.step,v]
  have R : rawNext s x e v=(largePair (rows s) (x e,x v)).2 := by
    simp [rawNext,AllSizeS1Geometry.step,v,Ne.symm (ShortResetCycle.edge_sep N e)]
  have H : (src (rawNext s x e) e,src (rawNext s x e) v)=
      Pair.map BStarWidthTransferFull.Cell.source
        (BStarWidthTransferFull.step (s+11) (radWidth s) (eff P x e) h
          (BStarWidthTransferFull.read (c:=s+11) u,
           BStarWidthTransferFull.read (c:=s+11) w)) := by
    refine Eq.trans (b := (readSource (c:=s+11) (largePair (rows s) (x e,x v)).1.widthClient,
      readSource (c:=s+11) (largePair (rows s) (x e,x v)).2.widthClient)) ?_ ?_
    · exact Prod.ext
        (congrArg (fun (p : LargeSite (WidthJoinedProjection.P s)) => readSource (c:=s+11) p.widthClient) L)
        (congrArg (fun (p : LargeSite (WidthJoinedProjection.P s)) => readSource (c:=s+11) p.widthClient) R)
    change
      (readSource (c:=s+11) (largePair (rows s) (x e,x v)).1.widthClient,
       readSource (c:=s+11) (largePair (rows s) (x e,x v)).2.widthClient)=_
    change
      (readSource (c:=s+11)
        (patchPair ((ShortGeo.width (s+11)).patches (s+11)
          ((oldHeaders (rows s) (x e)).h6,(oldHeaders (rows s) (x v)).h6)
          (u,w) (BStarShort.widthWork (c:=s+11) (radWidth s)
          ((oldHeaders (rows s) (x e)).h6,(oldHeaders (rows s) (x v)).h6) (u,w))) (u,w)).1,
       readSource (c:=s+11)
        (patchPair ((ShortGeo.width (s+11)).patches (s+11)
          ((oldHeaders (rows s) (x e)).h6,(oldHeaders (rows s) (x v)).h6)
          (u,w) (BStarShort.widthWork (c:=s+11) (radWidth s)
          ((oldHeaders (rows s) (x e)).h6,(oldHeaders (rows s) (x v)).h6) (u,w))) (u,w)).2)=_
    rw [hu,hv]
    exact B
  rw [sourceStep_eq] at H
  exact ⟨congrArg Prod.fst H,congrArg Prod.snd H⟩

theorem remote_src (x : Raw s n) (e q : Fin n)
    (A : q≠e) (B : q≠rightNeighbor e) :
    src (rawNext s x e) q=src x q := by
  simp [src,rawNext,AllSizeS1Geometry.step,A,B]

theorem remote_wire (x : Raw s n) (e q : Fin n)
    (A : q≠e) (B : q≠rightNeighbor e) :
    wire (rawNext s x e) q=wire x q :=
  congrArg BStarWidthTransfer.Source.token (remote_src x e q A B)

/-- At a true right header, the source is independent of the left
    terminal. This is valid even if that terminal is an inherited F. -/
private theorem right_header (c r i : Nat) (h : Bool)
    (u v : BStarWidthTransfer.Source) (data : Data) :
    (sourceStep c r i (h,true) u v data).2=
      BStarWidthTransferPair.rightSource v := by
  unfold sourceStep
  dsimp only
  split <;> rfl

private theorem left_header_control (c r i : Nat) (h : Bool)
    (u v : BStarWidthTransfer.Source) (data : Data) :
    let y := (sourceStep c r i (true,h) u v data).1
    y.phase=u.phase ∧ y.op=u.op := by
  have C : (prep true u).phase=u.phase ∧ (prep true u).op=u.op := by
    unfold prep
    dsimp only
    split <;> exact ⟨rfl,rfl⟩
  unfold sourceStep
  dsimp only
  split
  · split <;> exact C
  · split
    · split <;> exact C
    · split
      · exact C
      · split <;> exact C

private theorem wait_source_hold (u : BStarWidthTransfer.Source) (op : Nat)
    (P : u.phase.toNat=2) (O : u.op.toNat=op) (B : op≤5)
    (T : (decode u.token).tag=1 ∨ (decode u.token).tag=2)
    (F : (decode u.token).fault=false) :
    BStarWidthTransferPair.rightSource u=u := by
  have V : ¬5<op := by omega
  rcases T with T|T <;>
    simp [BStarWidthTransferPair.rightSource,BStarWidthTransferPair.holds,
      BStarWidthTransfer.door,P,O,V,T,F]

private theorem issue_source (u : BStarWidthTransfer.Source) (op : Nat)
    (P : u.phase.toNat=1) (O : u.op.toNat=op) (B : op≤5) :
    BStarWidthTransferPair.rightSource u=
      {u with phase:=2, token:=encode (fwd op (initialArg op u.flags.toNat))} := by
  have V : ¬5<op := by omega
  -- CHECK: BStarWidthTransfer.lean:25–28,37–43 and
  -- BStarWidthTransferPair.lean:47–50,160–164.
  simp [BStarWidthTransferPair.rightSource,BStarWidthTransferPair.holds,
    BStarWidthTransfer.door,P,O,V]
  rw [←O]
  rfl


def Controller (S : Sector h d) (x : Raw s n) (p op : Nat) : Prop :=
  (src x S.root).phase.toNat=p ∧ (src x S.root).op.toNat=op

theorem nondoor_control {h : Fin n→Bool} (P : WidthLower s n)
    (S : Sector h d) (H : h=P.h) (x : Raw s n) (X : P.Q x)
    (e : Fin n) (E : e≠inlet S) :
    (src (rawNext s x e) S.root).phase=(src x S.root).phase ∧
    (src (rawNext s x e) S.root).op=(src x S.root).op := by
  subst h
  have room := S.room
  have N : 1<n := by omega
  by_cases L : e=S.root
  · subst e
    have R := (raw_sources P N x X S.root).1
    unfold pairSources at R
    rw [S.here] at R
    rw [R]
    exact left_header_control _ _ _ _ _ _ _
  · have J : S.root≠rightNeighbor e := by
      intro A
      apply E
      apply ShortChartOwnership.right_injective
      exact A.symm.trans (inlet_eq S).symm
    rw [remote_src x e S.root (Ne.symm L) J]
    exact ⟨rfl,rfl⟩

theorem nondoor_controller (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (p op : Nat) (C : Controller S x p op)
    (e : Fin n) (E : e≠inlet S) :
    Controller S (rawNext s x e) p op := by
  have R := nondoor_control P S rfl x X e E
  exact ⟨(congrArg BitVec.toNat R.1).trans C.1,
    (congrArg BitVec.toNat R.2).trans C.2⟩

theorem door_source (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) :
    src (rawNext s x (inlet S)) S.root=
      BStarWidthTransferPair.rightSource (src x S.root) := by
  have room := S.room
  have N : 1<n := by omega
  have R := (raw_sources P N x X (inlet S)).2
  have E : rightNeighbor (inlet S)=S.root := inlet_eq S
  rw [E] at R
  -- pairSources still contains its original rightNeighbor internally.
  unfold pairSources at R
  rw [E,S.here] at R
  exact R.trans (right_header _ _ _ _ _ _ _)

/-! Exact sector geometry and pointwise wire frames. -/

private theorem site_root (S : Sector h d) : site S 0=S.root := rfl

private theorem interior_update (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (a : Fin d) (j : Fin (d+1)) :
    wire (rawNext s x (site S (west a))) (site S j)=
      if j=west a then (pairSources P x (site S (west a))).1.token
      else if j=east a then (pairSources P x (site S (west a))).2.token
      else wire x (site S j) := by
  have N : 1<n := by have := S.room; omega
  let e := site S (west a)
  have R := internal_right S a
  by_cases A : j=west a
  · subst j
    simp only [if_true]
    exact congrArg BStarWidthTransfer.Source.token (raw_sources P N x X e).1
  by_cases B : j=east a
  · subst j
    simp only [if_neg A]
    rw [←R]
    exact congrArg BStarWidthTransfer.Source.token (raw_sources P N x X e).2
  rw [if_neg A,if_neg B]
  exact remote_wire x e _ (fun E=>A (site_injective S E))
    (fun E=>B (site_injective S (E.trans R)))

private theorem terminal_update (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (j : Fin (d+1)) :
    wire (rawNext s x (site S (WidthWaitDrain.last d))) (site S j)=
      if j=WidthWaitDrain.last d then
        (pairSources P x (site S (WidthWaitDrain.last d))).1.token
      else wire x (site S j) := by
  have N : 1<n := by have := S.room; omega
  by_cases A : j=WidthWaitDrain.last d
  · subst j
    simp only [if_true]
    exact congrArg BStarWidthTransfer.Source.token (raw_sources P N x X _).1
  rw [if_neg A]
  exact remote_wire x _ _ (fun E=>A (site_injective S E))
    (Ne.symm (outbound_not_site S j))

private theorem inlet_other (S : Sector h d) (x : Raw s n)
    (j : Fin (d+1)) (J : j≠0) :
    wire (rawNext s x (inlet S)) (site S j)=wire x (site S j) :=
  remote_wire x _ _ (Ne.symm (inlet_not_site S j))
    (fun E=>J (site_injective S (E.trans (inlet_eq S))))

private theorem exterior (S : Sector h d) (x : Raw s n) (e : Fin n)
    (I : e≠inlet S) (J : ¬∃ j : Fin (d+1), e=site S j) :
    ∀ j : Fin (d+1), wire (rawNext s x e) (site S j)=wire x (site S j) := by
  intro j
  apply remote_wire
  · exact fun E=>J ⟨j,E.symm⟩
  · intro E
    rcases incident S e j E.symm with A|⟨a,A⟩
    · exact I A
    · exact J ⟨west a,A⟩

/-- The protected prefix has an exact T byte, not merely an
    occupied tag. An arbitrary old suffix can be overwritten. -/
structure Front (S : Sector h d) (x : Raw s n) (op j a : Nat) : Prop where
  index : j≤d
  arg : FArg op a
  control : Controller S x 2 op
  liveWire : wire x (nextAt S.root j)=encode (fwd op a)
  trail : ∀ k : Fin (d+1), k.val<j → wire x (site S k)=encode trailToken

/-- At the true turn the last site's reply is genuine and the entire
    earlier word has been overwritten by this same F generation.
    This is a reverse SEED, not the consumed receipt. -/
structure Turn (S : Sector h d) (x : Raw s n) (op a : Nat) : Prop where
  arg : DArg op a
  control : Controller S x 2 op
  replyWire : wire x (site S (WidthWaitDrain.last d))=encode (reply op a)
  trail : ∀ k : Fin (d+1), k.val<d → wire x (site S k)=encode trailToken

private theorem front_root_live (S : Sector h d) (x : Raw s n)
    (op j a : Nat) (O : op≤5) (A : Front S x op j a) :
    (decode (src x S.root).token).tag=1 ∨
      (decode (src x S.root).token).tag=2 := by
  by_cases J : j=0
  · subst j
    have E := A.liveWire
    change (src x S.root).token=encode (fwd op a) at E
    rw [E,fcodec op a O A.arg]
    exact .inr rfl
  · have E := A.trail 0 (by change 0<j; omega)
    change (src x S.root).token=encode trailToken at E
    rw [E,WidthTokenTransport.trail_codec]
    exact .inl rfl

private theorem front_root_healthy (S : Sector h d) (x : Raw s n)
    (op j a : Nat) (O : op≤5) (A : Front S x op j a) :
    (decode (src x S.root).token).fault=false := by
  by_cases J : j=0
  · subst j
    have E := A.liveWire
    change (src x S.root).token=encode (fwd op a) at E
    rw [E,fcodec op a O A.arg]
    rfl
  · have E := A.trail 0 (by change 0<j; omega)
    change (src x S.root).token=encode trailToken at E
    rw [E,WidthTokenTransport.trail_codec]
    rfl

theorem front_inlet (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op j a : Nat) (O : op≤5)
    (A : Front S x op j a) :
    Front S (rawNext s x (inlet S)) op j a := by
  have R := (door_source P S x X).trans
    (wait_source_hold (src x S.root) op A.control.1 A.control.2 O
      (front_root_live S x op j a O A) (front_root_healthy S x op j a O A))
  have Hold (k : Fin (d+1)) :
      wire (rawNext s x (inlet S)) (site S k)=wire x (site S k) := by
    by_cases E : k=0
    · subst k
      exact congrArg BStarWidthTransfer.Source.token R
    · exact inlet_other S x k E
  refine ⟨A.index,A.arg,
    ⟨(congrArg (fun u : BStarWidthTransfer.Source=>u.phase.toNat) R).trans A.control.1,
      (congrArg (fun u : BStarWidthTransfer.Source=>u.op.toNat) R).trans A.control.2⟩,?_,?_⟩
  · exact (Hold ⟨j,by have := A.index; omega⟩).trans A.liveWire
  · intro k K
    exact (Hold k).trans (A.trail k K)

def advancedArg (P : WidthLower s n) (x : Raw s n) (e : Fin n)
    (op a : Nat) : Nat :=
  (execute (s+11) (radWidth s) (eff P x e) (dat x e) (fwd op a)).2.arg

theorem advanced_good (P : WidthLower s n) (x : Raw s n) (e : Fin n)
    (op a : Nat) (O : op≤5) (A : FArg op a) :
    (execute (s+11) (radWidth s) (eff P x e) (dat x e) (fwd op a)).2=
      fwd op (advancedArg P x e op a) ∧
    FArg op (advancedArg P x e op a) :=
  execute_good _ _ _ _ op a O A

/-- Quiet T/T and T/F pairs use no routing branch. The body
    controller may be reset, but these K wires are unchanged. -/
private theorem quiet_pair (c r i : Nat) (h : Bool)
    (u v : BStarWidthTransfer.Source) (data : Data) (t : Token)
    (L : decode u.token=trailToken) (R : decode v.token=t)
    (H : t.tag=1 ∨ t.tag=2) (F : t.fault=false) :
    let z := sourceStep c r i (h,false) u v data
    z.1.token=u.token ∧ z.2.token=v.token := by
  rcases H with H|H <;>
    cases h <;> simp [sourceStep,prep,L,R,trailToken,H,F]

private theorem inside_front_pair (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (k : Fin d) (op a : Nat) (O : op≤5)
    (A : FArg op a) (W : wire x (site S (west k))=encode (fwd op a)) :
    let e := site S (west k)
    let z := pairSources P x e
    z.1.token=encode trailToken ∧
      z.2.token=encode (fwd op (advancedArg P x e op a)) := by
  dsimp only
  have T := (advanced_good P x (site S (west k)) op a O A).1
  have H : P.h (rightNeighbor (site S (west k)))=false := by
    rw [internal_right S k]
    exact internal_nonheader S k
  unfold pairSources
  rw [H]
  change (src x (site S (west k))).token=encode (fwd op a) at W
  have F : decode (src x (site S (west k))).token=fwd op a := by
    rw [W,fcodec op a O A]
  simp only [sourceStep,F,show (fwd op a).tag=2 from rfl,
    beq_self_eq_true,if_true,Bool.false_eq_true,if_false]
  -- CHECK: sourceStep and execute_good; the concrete T encoding is
  -- BitVec 16 literal 16384, equal to encode trailToken by rfl.
  exact ⟨rfl,congrArg encode T⟩

private theorem terminal_front_pair (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op a : Nat) (O : op≤5) (A : FArg op a)
    (W : wire x (site S (WidthWaitDrain.last d))=encode (fwd op a)) :
    (pairSources P x (site S (WidthWaitDrain.last d))).1.token=
      encode (reply op (finishArg op
        (advancedArg P x (site S (WidthWaitDrain.last d)) op a))) := by
  let e := site S (WidthWaitDrain.last d)
  have T := advanced_good P x e op a O A
  have D := (finish_good op _ O T.2).1
  unfold pairSources
  rw [outgoing_header S]
  change (src x e).token=encode (fwd op a) at W
  have F : decode (src x e).token=fwd op a := by rw [W,fcodec op a O A]
  change (sourceStep (s+11) (radWidth s) (eff P x e) (P.h e,true) (src x e)
    (src x (rightNeighbor e)) (dat x e)).1.token=_
  simp only [sourceStep,F,show (fwd op a).tag=2 from rfl,beq_self_eq_true,if_true]
  -- CHECK: terminal uses finish of the *departed* token.
  exact congrArg encode ((congrArg finish T.1).trans D)

/-- All old prefix/front wires hold on a nondeparture interior mark.
    If the mark lies ahead of the current cursor, its two raw endpoints
    are strictly beyond the protected interval, whatever their tokens. -/
theorem front_inside_hold (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op j a : Nat) (O : op≤5)
    (A : Front S x op j a) (k : Fin d) (K : k.val≠j) :
    Front S (rawNext s x (site S (west k))) op j a := by
  let e := site S (west k)
  have ctl := nondoor_controller P S x X 2 op A.control e
    (Ne.symm (inlet_not_site S (west k)))
  have J := A.index
  have H (q : Fin (d+1)) (Q : q.val≤j) :
      wire (rawNext s x e) (site S q)=wire x (site S q) := by
    have E := interior_update P S x X k q
    by_cases B : k.val<j
    · have L := A.trail (west k) B
      have R : wire x (site S (east k))=encode trailToken ∨
          wire x (site S (east k))=encode (fwd op a) := by
        by_cases C : k.val+1<j
        · exact .inl (A.trail (east k) C)
        · have D : k.val+1=j := by omega
          right
          change wire x (nextAt S.root (k.val+1))=_
          rw [D]
          exact A.liveWire
      have V : P.h (rightNeighbor e)=false := by
        change P.h (rightNeighbor (site S (west k)))=false
        rw [internal_right S k]
        exact internal_nonheader S k
      have LW : decode (src x e).token=trailToken := by
        change decode (wire x (site S (west k)))=_
        rw [L,WidthTokenTransport.trail_codec]
      have QP : (pairSources P x e).1.token=wire x e ∧
          (pairSources P x e).2.token=wire x (rightNeighbor e) := by
        unfold pairSources
        rw [V]
        rcases R with R|R
        · have RW : decode (src x (rightNeighbor e)).token=trailToken := by
            change decode (wire x (rightNeighbor (site S (west k))))=_
            rw [internal_right S k,R,WidthTokenTransport.trail_codec]
          exact quiet_pair _ _ _ _ _ _ _ trailToken LW RW (.inl rfl) rfl
        · have RW : decode (src x (rightNeighbor e)).token=fwd op a := by
            change decode (wire x (rightNeighbor (site S (west k))))=_
            rw [internal_right S k,R,fcodec op a O A.arg]
          exact quiet_pair _ _ _ _ _ _ _ (fwd op a) LW RW (.inr rfl) rfl
      rw [E]
      by_cases C : q=west k
      · subst q
        exact (if_pos rfl).trans QP.1
      · by_cases D : q=east k
        · subst q
          rw [if_neg C,if_pos rfl,←internal_right S k]
          exact QP.2
        · rw [if_neg C,if_neg D]
    · have U : j<k.val := by omega
      have W : q≠west k := by
        intro Z
        have Z' := congrArg Fin.val Z
        change q.val=k.val at Z'
        omega
      have V : q≠east k := by
        intro Z
        have Z' := congrArg Fin.val Z
        change q.val=k.val+1 at Z'
        omega
      rw [E,if_neg W,if_neg V]
  refine ⟨A.index,A.arg,ctl,?_,?_⟩
  · exact (H ⟨j,by omega⟩ (Nat.le_refl _)).trans A.liveWire
  · intro q Q
    exact (H q (by omega)).trans (A.trail q Q)

/-- A genuine F departure on an internal physical edge overwrites
    *any* old successor K and extends the canonical prefix. -/
theorem front_inside_advance (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op a : Nat) (O : op≤5)
    (k : Fin d) (A : Front S x op k.val a) :
    let e := site S (west k)
    Front S (rawNext s x e) op (k.val+1) (advancedArg P x e op a) := by
  dsimp only
  let e := site S (west k)
  have K := k.isLt
  have U := inside_front_pair P S x k op a O A.arg A.liveWire
  have T := advanced_good P x e op a O A.arg
  have ctl := nondoor_controller P S x X 2 op A.control e
    (Ne.symm (inlet_not_site S (west k)))
  refine ⟨by omega,T.2,ctl,?_,?_⟩
  · have E := interior_update P S x X k (east k)
    rw [if_neg (Ne.symm (west_ne_east k)),if_pos rfl] at E
    exact E.trans U.2
  · intro q Q
    have E := interior_update P S x X k q
    by_cases Z : q=west k
    · subst q
      rw [if_pos rfl] at E
      exact E.trans U.1
    · have V : q≠east k := by
        intro J
        have J' := congrArg Fin.val J
        change q.val=k.val+1 at J'
        omega
      have R : q.val<k.val := by
        have W : q.val≠k.val := fun J=>Z (Fin.ext J)
        omega
      rw [if_neg Z,if_neg V] at E
      exact E.trans (A.trail q R)

/-- A terminal mark strictly beyond the live frontier cannot touch it. -/
theorem front_terminal_hold (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op j a : Nat) (A : Front S x op j a)
    (J : j<d) :
    Front S (rawNext s x (site S (WidthWaitDrain.last d))) op j a := by
  let e := site S (WidthWaitDrain.last d)
  have C := nondoor_controller P S x X 2 op A.control e
    (Ne.symm (inlet_not_site S _))
  have H (q : Fin (d+1)) (Q : q.val≤j) :
      wire (rawNext s x e) (site S q)=wire x (site S q) := by
    have B : q≠WidthWaitDrain.last d := by
      intro E
      have E' := congrArg Fin.val E
      change q.val=d at E'
      omega
    simpa only [if_neg B] using terminal_update P S x X q
  exact ⟨A.index,A.arg,C,
    (H ⟨j,by omega⟩ (Nat.le_refl _)).trans A.liveWire,
    fun q Q=>(H q (by omega)).trans (A.trail q Q)⟩

theorem front_turn (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op a : Nat) (O : op≤5)
    (A : Front S x op d a) :
    let e := site S (WidthWaitDrain.last d)
    Turn S (rawNext s x e) op (finishArg op (advancedArg P x e op a)) := by
  dsimp only
  let e := site S (WidthWaitDrain.last d)
  have U := terminal_front_pair P S x op a O A.arg A.liveWire
  have T := advanced_good P x e op a O A.arg
  have C := nondoor_controller P S x X 2 op A.control e
    (Ne.symm (inlet_not_site S _))
  refine ⟨(finish_good op _ O T.2).2,C,?_,?_⟩
  · have E := terminal_update P S x X (WidthWaitDrain.last d)
    rw [if_pos rfl] at E
    exact E.trans U
  · intro k K
    have E := terminal_update P S x X k
    have Z : k≠WidthWaitDrain.last d := by
      intro H
      have V := congrArg Fin.val H
      change k.val=d at V
      omega
    rw [if_neg Z] at E
    exact E.trans (A.trail k K)

theorem front_exterior (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op j a : Nat) (A : Front S x op j a)
    (e : Fin n) (I : e≠inlet S) (J : ¬∃ k : Fin (d+1),e=site S k) :
    Front S (rawNext s x e) op j a := by
  have H := exterior S x e I J
  exact ⟨A.index,A.arg,nondoor_controller P S x X 2 op A.control e I,
    (H ⟨j,by have := A.index; omega⟩).trans A.liveWire,
    fun k K=>(H k).trans (A.trail k K)⟩

/-! A deterministic proof-only observer on the original raw tape.
    The op is fixed for one generation. The initial flags are read at
    the actual issue mark, not at an earlier arbitrary WAIT endpoint. -/

inductive Flight where
  | issue
  | out (j a : Nat)
  | turned (a : Nat)
  deriving DecidableEq

def live : Flight → Prop
  | .turned _ => False
  | _ => True

def Active (S : Sector h d) (x : Raw s n) (op : Nat) : Flight → Prop
  | .issue => Controller S x 1 op
  | .out j a => Front S x op j a
  | .turned a => Turn S x op a

def next (P : WidthLower s n) (S : Sector P.h d)
    (op : Nat) (x : Raw s n) (e : Fin n) : Flight → Flight
  | .issue => if e=inlet S then .out 0
        (initialArg op (src x S.root).flags.toNat) else .issue
  | .out j a => if e=nextAt S.root j then
        let a' := advancedArg P x e op a
        if j=d then .turned (finishArg op a') else .out (j+1) a'
      else .out j a
  | .turned a => .turned a

theorem source_issue_fresh (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op : Nat) (O : op≤5)
    (A : Controller S x 1 op) :
    Front S (rawNext s x (inlet S)) op 0
      (initialArg op (src x S.root).flags.toNat) := by
  have R := (door_source P S x X).trans
    (issue_source (src x S.root) op A.1 A.2 O)
  refine ⟨by omega,initial_good op _ O (src x S.root).flags.isLt,
    ?_,?_,?_⟩
  · exact ⟨congrArg (fun u : BStarWidthTransfer.Source=>u.phase.toNat) R,
      (congrArg (fun u : BStarWidthTransfer.Source=>u.op.toNat) R).trans A.2⟩
  · exact congrArg BStarWidthTransfer.Source.token R
  · intro k K
    omega

/-- Every actual physical mark. This includes the transition
    to the genuine terminal reply, but not its future reverse consume. -/
theorem generated_forward_one_mark (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Q x) (op : Nat) (O : op≤5)
    (f : Flight) (A : Active S x op f) (L : live f) (e : Fin n) :
    Active S (rawNext s x e) op (next P S op x e f) := by
  classical
  cases f with
  | turned a => exact False.elim L
  | issue =>
    by_cases I : e=inlet S
    · subst e
      simpa only [next,show site S (WidthWaitDrain.last d)=nextAt S.root d from rfl,if_true,Active] using source_issue_fresh P S x X op O A
    · simpa only [next,if_neg I,Active] using nondoor_controller P S x X 1 op A e I
  | out j a =>
    have A' : Front S x op j a := A
    have J := A'.index
    let q : Fin (d+1) := ⟨j,by omega⟩
    have frontEq : site S q=nextAt S.root j := rfl
    by_cases I : e=inlet S
    · subst e
      have E : inlet S≠nextAt S.root j := by
        rw [←frontEq]
        exact inlet_not_site S q
      simpa only [next,if_neg E,Active] using front_inlet P S x X op j a O A'
    by_cases K : ∃ k : Fin (d+1), e=site S k
    · obtain ⟨k,E⟩ := K
      subst e
      by_cases D : k.val=d
      · have V : k=WidthWaitDrain.last d := Fin.ext D
        subst k
        by_cases F : j=d
        · subst j
          simpa only [next,show site S (WidthWaitDrain.last d)=nextAt S.root d from rfl,if_true,Active] using front_turn P S x X op a O A'
        · have E : site S (WidthWaitDrain.last d)≠nextAt S.root j := by
            intro R
            have Z := site_injective S (R.trans frontEq.symm)
            have Z' := congrArg Fin.val Z
            change d=j at Z'
            omega
          simpa only [next,if_neg E,Active] using
            front_terminal_hold P S x X op j a A' (by omega)
      · let k' : Fin d := ⟨k.val,by have := k.isLt; omega⟩
        have E : west k'=k := Fin.ext rfl
        rw [←E]
        by_cases F : k'.val=j
        · have A'' : Front S x op k'.val a := by rwa [F]
          have J' : k'.val≠d := Nat.ne_of_lt k'.isLt
          -- CHECK: west/site definitions, next's physical equality.
          have M := front_inside_advance P S x X op a O k' A''
          rw [←F]
          simpa only [next,show site S (west k')=nextAt S.root k'.val from rfl,if_true,if_neg J',Active] using M
        · have E' : site S (west k')≠nextAt S.root j := by
            intro R
            have Z := site_injective S (R.trans frontEq.symm)
            exact F (congrArg Fin.val Z)
          simpa only [next,if_neg E',Active] using
            front_inside_hold P S x X op j a O A' k' F
    · have E : e≠nextAt S.root j := fun R=>K ⟨q,R.trans frontEq.symm⟩
      simpa only [next,if_neg E,Active] using front_exterior P S x X op j a A' e I K

/-- A genuine generated history can be extended only while live.
    The seed is the actual source ISSUE, and the old raw state is
    always the literal rawRun of the same recorded prefix. -/
inductive Generated (P : WidthLower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op : Nat) : List (Fin n) → Flight → Prop where
  | start : P.Post x0 → Controller S x0 1 op → Generated P S x0 op [] .issue
  | snoc {w f} (e : Fin n) :
      Generated P S x0 op w f → live f →
      Generated P S x0 op (w++[e]) (next P S op (rawRun x0 w) e f)

private theorem raw_snoc (x : Raw s n) (w : List (Fin n)) (e : Fin n) :
    rawRun x (w++[e])=rawNext s (rawRun x w) e := by
  induction w generalizing x with
  | nil => rfl
  | cons a w IH => exact IH (rawNext s x a)

theorem generated_active (P : WidthLower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op : Nat) (O : op≤5) (w : List (Fin n)) (f : Flight)
    (G : Generated P S x0 op w f) :
    P.Post (rawRun x0 w) ∧ Active S (rawRun x0 w) op f := by
  have N : 1<n := by have := S.room; omega
  induction G with
  | start X I => exact ⟨X,I⟩
  | @snoc w f e G L IH =>
    rw [raw_snoc]
    exact ⟨P.post_closed N _ IH.1 e,
      generated_forward_one_mark P S _ IH.1.1 op O f IH.2 L e⟩

theorem generated_turn (P : WidthLower s n) (S : Sector P.h d)
    (x0 : Raw s n) (op : Nat) (O : op≤5) (w : List (Fin n)) (a : Nat)
    (G : Generated P S x0 op w (.turned a)) :
    Turn S (rawRun x0 w) op a :=
  (generated_active P S x0 op O w (.turned a) G).2

/-! A genuine original-tape first-turn clock, including the actual
    ISSUE mark. No reverse return time is claimed in this clock. -/

def rank (d : Nat) : Flight → Nat
  | .issue => d+2
  | .out j _ => d+1-j
  | .turned _ => 0

def done : Flight → Prop
  | .turned _ => True
  | _ => False

def monitorNext (P : WidthLower s n) (S : Sector P.h d) (op : Nat)
    (z : Raw s n × Flight) (e : Fin n) : Raw s n × Flight :=
  (rawNext s z.1 e,next P S op z.1 e z.2)

theorem monitor_raw (P : WidthLower s n) (S : Sector P.h d) (op : Nat)
    (z : Raw s n × Flight) (e : Fin n) :
    (monitorNext P S op z e).1=rawNext s z.1 e := rfl

theorem flight_rank_pos (S : Sector h d) (x : Raw s n) (op : Nat)
    (f : Flight) (A : Active S x op f) (L : live f) :
    0<rank d f := by
  cases f with
  | issue => simp [rank]
  | out j a =>
    have J : j≤d := (show Front S x op j a from A).index
    simp only [rank]
    omega
  | turned a => exact False.elim L

theorem flight_rank_step (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (op : Nat) (f : Flight) (A : Active S x op f)
    (L : live f) :
    ∃ b : Fin n, ∀ e : Fin n,
      rank d (next P S op x e f)≤rank d f ∧
      (e=b → rank d (next P S op x e f)<rank d f) := by
  cases f with
  | turned a => exact False.elim L
  | issue =>
    refine ⟨inlet S,fun e=>?_⟩
    by_cases E : e=inlet S
    · subst e
      simp [next,rank]
    · simp [next,rank,E]
  | out j a =>
    have J := (show Front S x op j a from A).index
    refine ⟨nextAt S.root j,fun e=>?_⟩
    by_cases E : e=nextAt S.root j
    · subst e
      by_cases K : j=d
      · subst j
        simp [next,rank]
      · simp only [next,if_true,if_neg K,rank,true_implies]
        omega
    · simp [next,rank,E]

theorem first_turn_expected (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op : Nat) (O : op≤5)
    (f : Flight) (A : Active S x op f) (L : live f) :
    Height.IIDExpectedHittingTimeAtMost (monitorNext P S op)
      (fun z=>done z.2) (x,f) (n*rank d f) := by
  let Inv := fun (z : Raw s n × Flight) r =>
    P.Post z.1 ∧ Active S z.1 op z.2 ∧ live z.2 ∧ r=rank d z.2
  have N : 1<n := by have := S.room; omega
  have pos (z : Raw s n × Flight) r (Z : Inv z r) : 0<r :=
    Z.2.2.2.symm ▸ flight_rank_pos S z.1 op z.2 Z.2.1 Z.2.2.1
  have move (z : Raw s n × Flight) r (Z : Inv z r) :
      ∃ b : Fin n, ∀ e : Fin n,
        done (monitorNext P S op z e).2 ∨
        ∃ r',Inv (monitorNext P S op z e) r' ∧ r'≤r ∧ (e=b → r'<r) := by
    obtain ⟨b,B⟩ := flight_rank_step P S z.1 op z.2 Z.2.1 Z.2.2.1
    refine ⟨b,fun e=>?_⟩
    let y := monitorNext P S op z e
    by_cases H : done y.2
    · exact .inl H
    have H' : live y.2 := by
      cases E : y.2 with
      | issue => trivial
      | out j a => trivial
      | turned a => exact False.elim (H (by simp [done,E]))
    have A' := generated_forward_one_mark P S z.1 Z.1.1 op O z.2 Z.2.1 Z.2.2.1 e
    refine .inr ⟨rank d y.2,⟨P.post_closed N z.1 Z.1 e,A',H',rfl⟩,?_,?_⟩
    · rw [Z.2.2.2]
      exact (B e).1
    · intro E
      rw [Z.2.2.2]
      exact (B e).2 E
  exact ResetReturnIID.iid_of_relational_rank (monitorNext P S op)
    (fun z=>done z.2) Inv pos move (x,f) (rank d f)
    (.inr ⟨X,A,L,rfl⟩)

theorem issue_to_turn_mean (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op : Nat) (O : op≤5)
    (A : Controller S x 1 op) :
    Height.IIDExpectedHittingTimeAtMost (monitorNext P S op)
      (fun z=>done z.2) (x,.issue) (n*(d+2)) :=
  first_turn_expected P S x X op O .issue A trivial

/-- Same observer stopped at the actual first turn. A terminal
    generation certificate is not asserted after further raw marks. -/
theorem original_first_turn_receipt (P : WidthLower s n) (S : Sector P.h d)
    (x : Raw s n) (X : P.Post x) (op : Nat) (O : op≤5)
    (I : Controller S x 1 op)
    (w : List (Fin n))
    (D : done (SequentialMarkClock.run (monitorNext P S op) (x,.issue) w).2) :
    ∃ u v a, w=u++v ∧ Generated P S x op u (.turned a) ∧
      Turn S (rawRun x u) op a := by
  have aux (u v : List (Fin n)) (f : Flight) (G : Generated P S x op u f)
      (D : done (SequentialMarkClock.run (monitorNext P S op) (rawRun x u,f) v).2) :
      ∃ p t a, u++v=p++t ∧ Generated P S x op p (.turned a) := by
    induction v generalizing u f with
    | nil =>
      cases f with
      | issue => exact False.elim D
      | out j a => exact False.elim D
      | turned a => exact ⟨u,[],a,rfl,G⟩
    | cons e v IH =>
      by_cases L : live f
      · have G' := Generated.snoc e G L
        have R : done (SequentialMarkClock.run (monitorNext P S op)
          (rawRun x (u++[e]),next P S op (rawRun x u) e f) v).2 := by
          rw [raw_snoc]
          exact D
        obtain ⟨p,t,a,E,H⟩ := IH (u++[e]) _ G' R
        exact ⟨p,t,a,by simpa [List.append_assoc] using E,H⟩
      · cases f with
        | issue => exact False.elim (L trivial)
        | out j a => exact False.elim (L trivial)
        | turned a => exact ⟨u,e::v,a,rfl,G⟩
  obtain ⟨u,v,a,E,G⟩ := aux [] w .issue (.start X I) D
  exact ⟨u,v,a,E,G,generated_turn P S x op O u a G⟩

#print axioms sourceStep_eq
#print axioms raw_sources
#print axioms execute_good
#print axioms source_issue_fresh
#print axioms front_inside_hold
#print axioms front_inside_advance
#print axioms front_turn
#print axioms generated_forward_one_mark
#print axioms generated_active
#print axioms generated_turn
#print axioms first_turn_expected
#print axioms original_first_turn_receipt

end L4.WidthFreshForward


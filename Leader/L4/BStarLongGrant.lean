import Leader.L4.BStarLongCommand

/-! Old-long-header grants and in-flight ACQUIRE capture. Arbitration uses
the selected command departures, but both the lock triple and captured
operands come from the immutable old selected pair. -/
namespace L4.BStarLongGrant
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongCommand BStarLongLayout BStarLongToken

abbrev Offers := List (CommandClaim × Offer)
abbrev Ports := Fin 3 → Bool

def releaseOp : Nat := 2

def original (raw : BitVec LW) (j : Fin 3) : Bool := ((grant j).read raw).getLsbD 0

def conflict (old : Ports) : Bool := old 1 && (old 0 || old 2)

def canonical (old : Ports) (j : Fin 3) : Bool :=
  if old 1 then j==1 else old j

/-- Both reader and writer permissions are evaluated before releases. -/
def win (old release ask : Ports) (j : Fin 3) : Bool :=
  let g := canonical old
  let w := !(g 0 || g 1 || g 2) && ask 1 && !release 1
  if j=1 then w else !w && !g 1 && ask j && !g j && !release j

def result (old release ask : Ports) (j : Fin 3) : Bool :=
  (canonical old j && !release j) || win old release ask j

def requested (offers : Offers) (side : Side) (j : Fin 3) (op : Nat) : Bool :=
  offers.any fun (claim,off) =>
    claim.source.side==side && claim.source.occurrence.val==j.val &&
      match off with
      | .advance p => p.fault==0 && p.opcode.toNat==op
      | _ => false

def atOld (raw : Pair (BitVec LW)) (side : Side) : BitVec LW :=
  lane (side==.right) raw

def right (s : Side) : Bool := s==.right

/-- Full grant cleanup on nonheaders or dirty writer-reader conflicts;
otherwise exactly released or actually granted incidences write. -/
def support (header : Bool) (old release ask : Ports) (j : Fin 3) : Bool :=
  !header || conflict old || release j || win old release ask j

def siteWrites (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (offers : Offers) (side : Side) : List (Write LW) :=
  let header := (geometry g side).axes.h6
  let old := original (atOld raw side)
  let release := fun j => requested offers side j releaseOp
  let ask := fun j => requested offers side j acquire
  (List.finRange 3).filterMap fun j =>
    if support header old release ask j then
      some ⟨right side,1,grant j,BitVec.ofBool (header && result old release ask j)⟩
    else none

/-- All header captures use this old selector and this old bank. -/
def headerBits (raw : BitVec LW) : BitVec 9 :=
  let b := BStarLongPublication.readSel raw
  BitVec.ofNat 9 <| (List.finRange 9).foldl
    (fun n i => 2*n + ((bankHeader b i).read raw).toNat) 0

def replaceLane (u v : Nat) (lo wi : Nat) : Nat :=
  (u / 2^(lo+wi)) * 2^(lo+wi) + (v % 2^wi)*2^lo + u % 2^lo

/-- Success latch high; selector and header triples are high to low.
A later successful incidence never resets an earlier denial. -/
def captureFields (selector : Fin 3) (hdr : BitVec 9) (j : Fin 3)
    (p : Payload) (wins : Bool) : Payload :=
  let u := p.argument.toNat
  if wins then
    let v := replaceLane u selector.val (31-2*j.val) 2
    {p with argument:=BitVec.ofNat 34 (replaceLane v hdr.toNat (18-9*j.val) 9)}
  else
    {p with argument:=BitVec.ofNat 34 (u % 2^33)}

def capture (raw : BitVec LW) (j : Fin 3) (p : Payload) (wins : Bool) : Payload :=
  captureFields (BStarLongPublication.readSel raw) (headerBits raw) j p wins

def update (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (offers : Offers)
    (offer : CommandClaim × Offer) : CommandClaim × Offer :=
  let (claim,action) := offer
  let side := claim.source.side
  let o := claim.source.occurrence.val
  if h : o<3 then
    match action with
    | .advance p =>
      if (geometry g side).axes.h6 && p.fault==0 && p.opcode.toNat==acquire then
        let j : Fin 3 := ⟨o,h⟩
        let x := atOld raw side
        (claim,.advance (capture x j p
          (win (original x) (fun k => requested offers side k releaseOp)
            (fun k => requested offers side k acquire) j)))
      else offer
    | _ => offer
  else offer

structure GrantStage where
  writes : List (Write LW)
  departures : Offers

def run (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (offers : Offers) : GrantStage :=
  ⟨siteWrites g raw offers .left ++ siteWrites g raw offers .right,
    offers.map (update g raw offers)⟩

def GrantStage.patch (s : GrantStage) : Pair (Patch LW) :=
  lower (s.writes.map Write.patch)

theorem writer_no_same_mark_refill (old rel ask : Ports) (h : canonical old 0=true ∨
    canonical old 1=true ∨ canonical old 2=true) : win old rel ask 1=false := by
  rcases h with h|h|h <;> simp [win,h]

theorem support_exact (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (o : Offers) (s : Side) (j : Fin 3) :
    support (geometry g s).axes.h6 (original (atOld raw s))
      (fun i => requested o s i releaseOp) (fun i => requested o s i acquire) j = true ↔
    (geometry g s).axes.h6 = false ∨
      conflict (original (atOld raw s)) = true ∨ requested o s j releaseOp = true ∨
      win (original (atOld raw s)) (fun i => requested o s i releaseOp)
        (fun i => requested o s i acquire) j=true := by
  simp [support,Bool.or_assoc]

private def off : Ports := fun _ => false
private def twoReaders : Ports := fun j => j != 1

theorem arbitration_fixture :
    win twoReaders twoReaders (fun _ => true) 1=false ∧
    win off off (fun _ => true) 1=true ∧
    win off off (fun _ => true) 0=false ∧
    win off off twoReaders 0=true ∧ win off off twoReaders 2=true ∧
    support true off (fun j => j==2) off 2=true := by decide

private def sample (n : Nat) : Payload := ⟨0,5,0,0,BitVec.ofNat 34 n⟩

theorem missed_acquire_cannot_recover :
    finish (captureFields 2 255 2 (captureFields 0 0 0 (sample (2^33)) false) true) =
      .reply {sample 0 with outcome:=1} := by decide

/-- Exact packed support, directly derived from the issued grant writes. -/
theorem patch_grant_support (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (o : Offers) (side : Side) (i : Nat) :
    (lane (right side) (run g raw o).patch).mask.getLsbD i=true ↔
      ∃ j : Fin 3,
        support (geometry g side).axes.h6 (original (atOld raw side))
          (fun k => requested o side k releaseOp)
          (fun k => requested o side k acquire) j=true ∧ (grant j).offset=i := by
  let T : Trace LW Unit := ⟨(run g raw o).writes,[]⟩
  change (lane (right side) T.lower).mask.getLsbD i=true ↔ _
  rw [Trace.mask_iff]
  have leftProof (sourceSide : Side) (t : Write LW) (ht : t ∈ siteWrites g raw o sourceSide)
      (hs : t.right=right side) (hlo : t.field.offset≤i)
      (hhi : i<t.field.offset+t.width) :
      ∃ j : Fin 3,
        support (geometry g side).axes.h6 (original (atOld raw side))
          (fun k => requested o side k releaseOp)
          (fun k => requested o side k acquire) j=true ∧ (grant j).offset=i := by
    unfold siteWrites at ht
    obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp ht
    split at hj
    · rename_i hw
      cases hj
      have he : sourceSide=side := by cases sourceSide <;> cases side <;> simp_all [right]
      subst sourceSide
      change (grant j).offset≤i at hlo
      change i<(grant j).offset+1 at hhi
      exact ⟨j,hw,by omega⟩
    · contradiction
  constructor
  · rintro ⟨t,ht,hs,hlo,hhi⟩
    rcases List.mem_append.mp ht with hl|hr
    · exact leftProof .left t hl hs hlo hhi
    · exact leftProof .right t hr hs hlo hhi
  · rintro ⟨j,hj,hi⟩
    let h := (geometry g side).axes.h6
    let old := original (atOld raw side)
    let rel := fun k => requested o side k releaseOp
    let ask := fun k => requested o side k acquire
    let t : Write LW := ⟨right side,1,grant j,BitVec.ofBool (h && result old rel ask j)⟩
    have ht : t ∈ siteWrites g raw o side := by
      apply List.mem_filterMap.mpr
      exact ⟨j,List.mem_finRange j,by simp [hj,t,h,old,rel,ask]⟩
    refine ⟨t,?_,rfl,?_,?_⟩
    · exact List.mem_append.mpr (by cases side <;> simp_all)
    · change (grant j).offset≤i
      omega
    · change i<(grant j).offset+1
      omega

theorem own_capture_field_fixture :
    (captureFields 2 341 1 (sample (2^33)) true).argument.toNat =
      2^33 + 2*2^29 + 341*2^9 ∧
    (captureFields 2 341 1 (sample 3) true).argument.toNat =
      3 + 2*2^29 + 341*2^9 := by decide

end L4.BStarLongGrant

import Leader.L3.CandidateClosure

namespace L3

set_option autoImplicit false

/-! The AcceptedReceipts namespace below is partial.
Do not infer that its accepted finite classes equal the legacy W/R/D
prefix-closed ghost classes retained here for compatibility. -/

/-- Exactly (N,S,lambda,I,U) of (E.G1). -/
structure ProjW (c : Compiled) where
  native : CertNative
  ser : Ser
  siLease : Fin (c.siLeaseMax + 1)
  si : SI c.t
  u : Bool
  beta : Bool
  deriving DecidableEq, Repr

/-- Exactly W together with the raw-reader coordinates. -/
structure ProjR (c : Compiled) where
  word : ProjW c
  rawKick : Bool
  rawTok : Option (RawTok c.t)
  deriving DecidableEq, Repr

/-- TopFields retains all nine digit/TOP coordinates, including
the comparison carry's error bit. -/
structure ProjD (c : Compiled) where
  word : ProjW c
  top : TopFields c
  deriving DecidableEq, Repr

def ProjW.ofAgent {c : Compiled} (a : Agent c) : ProjW c :=
  { native := a.certNative
    ser := a.ser
    siLease := a.siLease
    si := a.si
    u := a.u
    beta := a.beta }

def ProjR.ofAgent {c : Compiled} (a : Agent c) : ProjR c :=
  { word := ProjW.ofAgent a
    rawKick := a.rawKick
    rawTok := a.rawTok }

def ProjD.ofAgent {c : Compiled} (a : Agent c) : ProjD c :=
  { word := ProjW.ofAgent a
    top :=
      { wBase := a.wBase
        wOut := a.wOut
        wIn := a.wIn
        wCarry := a.wCarry
        qOut := a.qOut
        qIn := a.qIn
        qCarry := a.qCarry
        d := a.d
        topDirty := a.topDirty } }

def piW {c : Compiled} {n : Nat}
    (C : Fin n → Agent c) : Fin n → ProjW c :=
  fun i => ProjW.ofAgent (C i)

def piR {c : Compiled} {n : Nat}
    (C : Fin n → Agent c) : Fin n → ProjR c :=
  fun i => ProjR.ofAgent (C i)

def piD {c : Compiled} {n : Nat}
    (C : Fin n → Agent c) : Fin n → ProjD c :=
  fun i => ProjD.ofAgent (C i)

/-- A representative used only to call the existing owners.
Every nonconstant coordinate comes from the projection. -/
def ProjW.lift {c : Compiled} (a : ProjW c) : Agent c :=
  { Agent.blank c with
    l := a.native.l
    b := a.native.b
    sh := a.native.sh
    sg := a.native.sg
    ser := a.ser
    siLease := a.siLease
    si := a.si
    u := a.u
    beta := a.beta }

def ProjR.lift {c : Compiled} (a : ProjR c) : Agent c :=
  { a.word.lift with
    rawKick := a.rawKick
    rawTok := a.rawTok }

def ProjD.lift {c : Compiled} (a : ProjD c) : Agent c :=
  a.top.applyTo a.word.lift

theorem ProjW.ofAgent_lift {c : Compiled} (a : ProjW c) :
    ProjW.ofAgent a.lift = a := rfl

theorem ProjR.ofAgent_lift {c : Compiled} (a : ProjR c) :
    ProjR.ofAgent a.lift = a := rfl

theorem ProjD.ofAgent_lift {c : Compiled} (a : ProjD c) :
    ProjD.ofAgent a.lift = a := rfl

def postW {c : Compiled} (x y : ProjW c) : PostE :=
  let p := certLiteralEPair x.native y.native
  { eX := p.1, eY := p.2 }

def serW {c : Compiled} (x y : ProjW c) : SerResult :=
  serializerStep c x.lift y.lift (postW x y)

def workerW {c : Compiled} (x y : ProjW c) : SIResult c.t :=
  siStep c x.lift y.lift (postW x y) (serW x y).hard

/-- E, OLD serializer and lease, OLD worker/word, then lease. -/
def pairW {c : Compiled} (x y : ProjW c) : ProjW c × ProjW c :=
  let post := postW x y
  let ser := serW x y
  let si := workerW x y
  let lease :=
    leasePair c x.siLease y.siLease
      ser.hard.hardAccept ser.hard.softAccept si.done
  ({ native := post.eX
     ser := ser.x
     siLease := lease.1
     si := si.x
     u := si.uX
     beta := si.betaX },
   { native := post.eY
     ser := ser.y
     siLease := lease.2
     si := si.y
     u := si.uY
     beta := si.betaY })

/-- OLD raw and visible coordinates, with post-E leader flags. -/
def rawR {c : Compiled} (x y : ProjR c) : RawResult c.t :=
  rawD1Step c x.lift y.lift (postW x.word y.word)

def pairR {c : Compiled} (x y : ProjR c) : ProjR c × ProjR c :=
  let w := pairW x.word y.word
  let r := rawR x y
  ({ word := w.1, rawKick := r.kickX, rawTok := r.tokX },
   { word := w.2, rawKick := r.kickY, rawTok := r.tokY })

/-- Both lanes read OLD physical leaders. The writer gets resolved
markers; liveTopPair's comparison lane still reads OLD markers. -/
def topD {c : Compiled} (x y : ProjD c) : TopResult c :=
  let w := pairW x.word y.word
  liveTopPair c x.lift y.lift w.1.beta w.2.beta

def pairD {c : Compiled} (x y : ProjD c) : ProjD c × ProjD c :=
  let w := pairW x.word y.word
  let d := topD x y
  ({ word := w.1, top := d.x },
   { word := w.2, top := d.y })

def projectedEdge {A : Type} {n : Nat}
    (ring : DirectedRing n) (pair : A → A → A × A)
    (S : Fin n → A) (e : Fin n) : Fin n → A :=
  let j := ring.rightNeighbor e
  let p := pair (S e) (S j)
  fun i =>
    if i = e then p.1
    else if i = j then p.2
    else S i

def phiW {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjW c)
    (e : Fin n) : Fin n → ProjW c :=
  projectedEdge ring pairW S e

def phiR {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjR c)
    (e : Fin n) : Fin n → ProjR c :=
  projectedEdge ring pairR S e

def phiD {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c)
    (e : Fin n) : Fin n → ProjD c :=
  projectedEdge ring pairD S e

/-! Definitional dependency checks for the OLD owners. -/

theorem serW_ofAgent {c : Compiled} (x y : Agent c) :
    serW (ProjW.ofAgent x) (ProjW.ofAgent y) =
      serializerStep c x y (postEInfo x y) := rfl

theorem workerW_ofAgent {c : Compiled} (x y : Agent c) :
    workerW (ProjW.ofAgent x) (ProjW.ofAgent y) =
      siStep c x y (postEInfo x y)
        (serializerStep c x y (postEInfo x y)).hard := rfl

theorem rawR_ofAgent {c : Compiled} (x y : Agent c) :
    rawR (ProjR.ofAgent x) (ProjR.ofAgent y) =
      rawD1Step c x y (postEInfo x y) := rfl

/-! The literal top owner reads only the two OLD projected D records. -/
private theorem liveTopPair_of_fields (c : Compiled)
    (x x' y y' : Agent c) (bX bY : Bool)
    (hx_l : x.l = x'.l) (hy_l : y.l = y'.l)
    (hx_beta : x.beta = x'.beta) (hy_beta : y.beta = y'.beta)
    (hx_wBase : x.wBase = x'.wBase) (hy_wBase : y.wBase = y'.wBase)
    (hx_wOut : x.wOut = x'.wOut) (hy_wOut : y.wOut = y'.wOut)
    (hx_wIn : x.wIn = x'.wIn) (hy_wIn : y.wIn = y'.wIn)
    (hx_wCarry : x.wCarry = x'.wCarry) (hy_wCarry : y.wCarry = y'.wCarry)
    (hx_qOut : x.qOut = x'.qOut) (hy_qOut : y.qOut = y'.qOut)
    (hx_qIn : x.qIn = x'.qIn) (hy_qIn : y.qIn = y'.qIn)
    (hx_qCarry : x.qCarry = x'.qCarry) (hy_qCarry : y.qCarry = y'.qCarry)
    (hx_d : x.d = x'.d) (hy_d : y.d = y'.d)
    (hx_topDirty : x.topDirty = x'.topDirty) (hy_topDirty : y.topDirty = y'.topDirty) :
    liveTopPair c x y bX bY = liveTopPair c x' y' bX bY := by
  simp only [liveTopPair, topTerminal, topBorder, topInternal,
    hx_l, hy_l, hx_beta, hy_beta, hx_wBase, hy_wBase, hx_wOut, hy_wOut, hx_wIn, hy_wIn,
    hx_wCarry, hy_wCarry, hx_qOut, hy_qOut, hx_qIn, hy_qIn, hx_qCarry, hy_qCarry, hx_d, hy_d,
    hx_topDirty, hy_topDirty]
  congr 1
  all_goals (try congr 1)
  all_goals (try (with_reducible rfl))

private theorem liveTopPair_congr (c : Compiled)
    (x x' y y' : Agent c)
    (hx : ProjD.ofAgent x = ProjD.ofAgent x')
    (hy : ProjD.ofAgent y = ProjD.ofAgent y')
    (bX bY : Bool) :
    liveTopPair c x y bX bY = liveTopPair c x' y' bX bY :=
  liveTopPair_of_fields c x x' y y' bX bY
    (congrArg (fun p : ProjD c => p.word.native.l) hx)
    (congrArg (fun p : ProjD c => p.word.native.l) hy)
    (congrArg (fun p : ProjD c => p.word.beta) hx)
    (congrArg (fun p : ProjD c => p.word.beta) hy)
    (congrArg (fun p : ProjD c => p.top.wBase) hx)
    (congrArg (fun p : ProjD c => p.top.wBase) hy)
    (congrArg (fun p : ProjD c => p.top.wOut) hx)
    (congrArg (fun p : ProjD c => p.top.wOut) hy)
    (congrArg (fun p : ProjD c => p.top.wIn) hx)
    (congrArg (fun p : ProjD c => p.top.wIn) hy)
    (congrArg (fun p : ProjD c => p.top.wCarry) hx)
    (congrArg (fun p : ProjD c => p.top.wCarry) hy)
    (congrArg (fun p : ProjD c => p.top.qOut) hx)
    (congrArg (fun p : ProjD c => p.top.qOut) hy)
    (congrArg (fun p : ProjD c => p.top.qIn) hx)
    (congrArg (fun p : ProjD c => p.top.qIn) hy)
    (congrArg (fun p : ProjD c => p.top.qCarry) hx)
    (congrArg (fun p : ProjD c => p.top.qCarry) hy)
    (congrArg (fun p : ProjD c => p.top.d) hx)
    (congrArg (fun p : ProjD c => p.top.d) hy)
    (congrArg (fun p : ProjD c => p.top.topDirty) hx)
    (congrArg (fun p : ProjD c => p.top.topDirty) hy)

private theorem pairW_beta_left {c : Compiled}
    (x y : ProjW c) :
    (pairW x y).1.beta = (workerW x y).betaX := rfl

private theorem pairW_beta_right {c : Compiled}
    (x y : ProjW c) :
    (pairW x y).2.beta = (workerW x y).betaY := rfl

theorem topD_ofAgent {c : Compiled} (x y : Agent c) :
    topD (ProjD.ofAgent x) (ProjD.ofAgent y) =
      liveTopPair c x y
        (siStep c x y (postEInfo x y)
          (serializerStep c x y (postEInfo x y)).hard).betaX
        (siStep c x y (postEInfo x y)
          (serializerStep c x y (postEInfo x y)).hard).betaY := by
  have hx : ProjD.ofAgent ((ProjD.ofAgent x).lift) =
      ProjD.ofAgent x := ProjD.ofAgent_lift _
  have hy : ProjD.ofAgent ((ProjD.ofAgent y).lift) =
      ProjD.ofAgent y := ProjD.ofAgent_lift _
  calc
    topD (ProjD.ofAgent x) (ProjD.ofAgent y) =
        liveTopPair c ((ProjD.ofAgent x).lift)
          ((ProjD.ofAgent y).lift)
          (workerW (ProjD.ofAgent x).word (ProjD.ofAgent y).word).betaX
          (workerW (ProjD.ofAgent x).word (ProjD.ofAgent y).word).betaY := by
          unfold topD
          simp only [pairW_beta_left, pairW_beta_right]
    _ = liveTopPair c x y
          (workerW (ProjD.ofAgent x).word (ProjD.ofAgent y).word).betaX
          (workerW (ProjD.ofAgent x).word (ProjD.ofAgent y).word).betaY :=
      liveTopPair_congr c _ _ _ _ hx hy _ _
    _ = liveTopPair c x y
          (siStep c x y (postEInfo x y)
            (serializerStep c x y (postEInfo x y)).hard).betaX
          (siStep c x y (postEInfo x y)
            (serializerStep c x y (postEInfo x y)).hard).betaY := by
      rw [show (ProjD.ofAgent x).word = ProjW.ofAgent x from rfl,
        show (ProjD.ofAgent y).word = ProjW.ofAgent y from rfl, workerW_ofAgent]

private theorem projectedW_ext {c : Compiled}
    (x y : ProjW c)
    (hn : x.native = y.native)
    (hs : x.ser = y.ser)
    (hl : x.siLease = y.siLease)
    (hi : x.si = y.si)
    (hu : x.u = y.u)
    (hb : x.beta = y.beta) : x = y := by
  cases x
  cases y
  cases hn
  cases hs
  cases hl
  cases hi
  cases hu
  cases hb
  rfl

private theorem projectedR_ext {c : Compiled}
    (x y : ProjR c)
    (hw : x.word = y.word)
    (hk : x.rawKick = y.rawKick)
    (ht : x.rawTok = y.rawTok) : x = y := by
  cases x
  cases y
  cases hw
  cases hk
  cases ht
  rfl

private theorem projectedD_ext {c : Compiled}
    (x y : ProjD c)
    (hw : x.word = y.word)
    (ht : x.top = y.top) : x = y := by
  cases x
  cases y
  cases hw
  cases ht
  rfl

theorem transitionW_noFire (c : Compiled)
    (x y : Agent c) (hfire : oldFire x y = none) :
    (ProjW.ofAgent (transition c x y).1,
     ProjW.ofAgent (transition c x y).2) =
      pairW (ProjW.ofAgent x) (ProjW.ofAgent y) := by
  have hn :=
    congrArg
      (fun p : NativeCand × NativeCand =>
        (p.1.native, p.2.native))
      (transitionCandidate_noFire c x y hfire)
  apply Prod.ext
  · apply projectedW_ext
    · exact congrArg Prod.fst hn
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · apply projectedW_ext
    · exact congrArg Prod.snd hn
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

theorem transitionR_noFire (c : Compiled)
    (x y : Agent c) (hfire : oldFire x y = none) :
    (ProjR.ofAgent (transition c x y).1,
     ProjR.ofAgent (transition c x y).2) =
      pairR (ProjR.ofAgent x) (ProjR.ofAgent y) := by
  have hw := transitionW_noFire c x y hfire
  apply Prod.ext
  · apply projectedR_ext
    · exact congrArg Prod.fst hw
    · rfl
    · rfl
  · apply projectedR_ext
    · exact congrArg Prod.snd hw
    · rfl
    · rfl

private theorem certificate_top_pair (c : Compiled)
    (x y : Agent c) :
    ((ProjD.ofAgent (certificateStep c x y).1).top,
      (ProjD.ofAgent (certificateStep c x y).2.1).top) =
    ((liveTopPair c x y
       (siStep c x y (postEInfo x y)
         (serializerStep c x y (postEInfo x y)).hard).betaX
       (siStep c x y (postEInfo x y)
         (serializerStep c x y (postEInfo x y)).hard).betaY).x,
     (liveTopPair c x y
       (siStep c x y (postEInfo x y)
         (serializerStep c x y (postEInfo x y)).hard).betaX
       (siStep c x y (postEInfo x y)
         (serializerStep c x y (postEInfo x y)).hard).betaY).y) := by
  rfl

private theorem transition_top_pair (c : Compiled)
    (x y : Agent c) :
    ((ProjD.ofAgent (transition c x y).1).top,
      (ProjD.ofAgent (transition c x y).2).top) =
      ((ProjD.ofAgent (certificateStep c x y).1).top,
        (ProjD.ofAgent (certificateStep c x y).2.1).top) := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hx, hy⟩
  simp [transition, hc, hh, assemble, ProjD.ofAgent]

theorem transitionD_noFire (c : Compiled)
    (x y : Agent c) (hfire : oldFire x y = none) :
    (ProjD.ofAgent (transition c x y).1,
      ProjD.ofAgent (transition c x y).2) =
       pairD (ProjD.ofAgent x) (ProjD.ofAgent y) := by
  have hw := transitionW_noFire c x y hfire
  have ht := (transition_top_pair c x y).trans
    (certificate_top_pair c x y)
  have hd := topD_ofAgent x y
  apply Prod.ext
  · apply projectedD_ext
    · exact congrArg Prod.fst hw
    · calc
        (ProjD.ofAgent (transition c x y).1).top =
            (liveTopPair c x y
              (siStep c x y (postEInfo x y)
                (serializerStep c x y (postEInfo x y)).hard).betaX
              (siStep c x y (postEInfo x y)
                (serializerStep c x y (postEInfo x y)).hard).betaY).x :=
          congrArg Prod.fst ht
        _ = (topD (ProjD.ofAgent x) (ProjD.ofAgent y)).x :=
          (congrArg TopResult.x hd).symm
  · apply projectedD_ext
    · exact congrArg Prod.snd hw
    · calc
        (ProjD.ofAgent (transition c x y).2).top =
            (liveTopPair c x y
              (siStep c x y (postEInfo x y)
                (serializerStep c x y (postEInfo x y)).hard).betaX
              (siStep c x y (postEInfo x y)
                (serializerStep c x y (postEInfo x y)).hard).betaY).y :=
          congrArg Prod.snd ht
        _ = (topD (ProjD.ofAgent x) (ProjD.ofAgent y)).y :=
          (congrArg TopResult.y hd).symm

private theorem projectProtocolStep {q n : Nat} {A : Type}
    (project : Agent (compileAdvice q) → A)
    (pair : A → A → A × A)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hp :
      (project ((transition (compileAdvice q)
          (C e) (C (ring.rightNeighbor e))).1),
       project ((transition (compileAdvice q)
          (C e) (C (ring.rightNeighbor e))).2)) =
        pair (project (C e))
          (project (C (ring.rightNeighbor e)))) :
    (fun i => project ((protocol q).step ring C e i)) =
      projectedEdge ring pair (fun i => project (C i)) e := by
  funext i
  by_cases he : i = e
  · subst i
    simpa [PopulationProtocol.step, protocol, projectedEdge]
      using congrArg Prod.fst hp
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa [PopulationProtocol.step, protocol, projectedEdge, he]
        using congrArg Prod.snd hp
    · simp [PopulationProtocol.step, protocol, projectedEdge, he, hj]

theorem stepW_noFire {q n : Nat}
    (_hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none) :
    piW ((protocol q).step ring C e) =
      phiW ring (piW C) e := by
  exact projectProtocolStep (q := q) ProjW.ofAgent pairW ring C e
    (transitionW_noFire (compileAdvice q)
      (C e) (C (ring.rightNeighbor e)) hfire)

theorem stepR_noFire {q n : Nat}
    (_hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none) :
    piR ((protocol q).step ring C e) =
      phiR ring (piR C) e := by
  exact projectProtocolStep (q := q) ProjR.ofAgent pairR ring C e
    (transitionR_noFire (compileAdvice q)
      (C e) (C (ring.rightNeighbor e)) hfire)

theorem stepD_noFire {q n : Nat}
    (_hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none) :
    piD ((protocol q).step ring C e) =
      phiD ring (piD C) e := by
  exact projectProtocolStep (q := q) ProjD.ofAgent pairD ring C e
    (transitionD_noFire (compileAdvice q)
      (C e) (C (ring.rightNeighbor e)) hfire)


/-! Finite recurrence-origin receipts. -/

inductive WValidationStage where
  | requested | pending | observedInternal | observedLeaf
  | broadcaster | waiting | done | returned
  deriving DecidableEq, Repr

structure WValidationTicket where
  requestedAt : Nat
  startedAt : Nat
  stage : WValidationStage
  deriving DecidableEq, Repr

def wTicketStage (stage : WValidationStage)
    (ticket : Option WValidationTicket) : Option WValidationTicket :=
  ticket.map (fun t => { t with stage := stage })

def wTicketAt (stage : WValidationStage)
    (ticket : Option WValidationTicket) : Option WValidationTicket :=
  match ticket with
  | none => none
  | some t => if t.stage = stage then some t else none

def wParentTicket (ticket : Option WValidationTicket) :
    Option WValidationTicket :=
  match ticket with
  | none => none
  | some t =>
    if t.stage = .broadcaster ∨ t.stage = .waiting ∨ t.stage = .done
    then some t else none

def wJoinTickets (parent child : Option WValidationTicket) :
    Option WValidationTicket :=
  match parent, child with
  | some p, some q =>
    if p.requestedAt = q.requestedAt ∧ p.startedAt = q.startedAt
    then some p else none
  | _, _ => none

def wAdmitTickets (childStage : WValidationStage)
    (gx gy : Option WValidationTicket) : Option WValidationTicket :=
  wJoinTickets (wTicketAt .waiting gx) (wTicketAt childStage gy)

def wChallengeTickets (gx : Option WValidationTicket) :
    Option WValidationTicket × Option WValidationTicket :=
  let p := wParentTicket gx
  (wTicketStage .waiting p, wTicketStage .pending p)

/-- Every provenance decision uses the selected literal row and
its OLD subguards. Initial completion-looking bytes carry no ticket. -/
def wValidationPair {c : Compiled} (clock : Nat)
    (x y : ProjW c) (gx gy : Option WValidationTicket) :
    Option WValidationTicket × Option WValidationTicket :=
  let row := (serW x y).row
  let sx := x.ser
  let sy := y.ser
  if row = "S0" then
    (gx, some { requestedAt := clock, startedAt := clock,
                stage := .requested })
  else if row = "S1" then
    match wTicketAt .requested gx with
    | some request =>
      if x.siLease.val = 0 then
        let t : WValidationTicket :=
          { requestedAt := request.requestedAt,
            startedAt := clock, stage := .waiting }
        (some t, some { t with stage := .pending })
      else (none, none)
    | none => (none, none)
  else if row = "SR" then (none, none)
  else if row = "S6" then (none, gy)
  else if row = "S5" then
    if sx.phase == .C && sx.probe == .PENDING then
      (wTicketStage .observedLeaf
        (wJoinTickets (wParentTicket gy) (wTicketAt .pending gx)), gy)
    else if sx.phase == .B then (none, gy)
    else (gx, gy)
  else if row = "S2R" ∨ row = "S2N" then
    if sy.phase == .C then
      if sx.out == .WAIT && sy.probe == .PENDING then (gx, gy)
      else if sx.out == .WAIT && sy.probe == .INTERNAL_OK then
        let t := wAdmitTickets .observedInternal gx gy
        (wTicketStage .done t, wTicketStage .broadcaster t)
      else if sx.out == .WAIT && sy.probe == .LEAF_OK then
        let t := wAdmitTickets .observedLeaf gx gy
        (wTicketStage .done t, wTicketStage .returned t)
      else wChallengeTickets gx
    else if sy.phase == .B then
      if sx.out == .DONE then (gx, gy) else wChallengeTickets gx
    else if sy.phase == .F then
      if row = "S2N" ∧ sx.out = .DONE then
        let t := wJoinTickets (wTicketAt .done gx)
          (wTicketAt .returned gy)
        (wTicketStage .returned t, gy)
      else wChallengeTickets gx
    else (gx, gy)
  else if row = "S3" then
    let nextX :=
      if sx.probe == .PENDING && sy.phase == .C
      then wTicketStage .observedInternal (wTicketAt .pending gx)
      else gx
    let nextY := if sy.phase == .B || sy.phase == .F then none else gy
    (nextX, nextY)
  else if row = "S4" then
    (gx, if sy.phase == .B || sy.phase == .F then none else gy)
  else (gx, gy)

def wGenuineAcceptance {n : Nat} {c : Compiled}
    (root edge : Fin n) (x y : ProjW c)
    (gx gy : Option WValidationTicket) : Option WValidationTicket :=
  if edge = root ∧ (serW x y).row = "S6" ∧
      (serW x y).hard.hardAccept = true then
    wJoinTickets (wTicketAt .done gx) (wTicketAt .returned gy)
  else none

inductive WWorkerPhase where
  | prefixRun | backRun | sumRun | readyRun
  deriving DecidableEq, Repr

inductive WReadKind where
  | prefixRead | sumRead
  deriving DecidableEq, Repr

structure WReadReceipt (n : Nat) where
  service : Nat
  site : Fin n
  target : Fin n
  index : Nat
  value : Bool
  kind : WReadKind
  deriving DecidableEq, Repr

inductive WPublicationKind where
  | prefixZero | prefixEnd | target
  deriving DecidableEq, Repr

structure WPublicationReceipt (n : Nat) where
  service : Nat
  site : Fin n
  oldU : Bool
  oldBeta : Bool
  newU : Bool
  newBeta : Bool
  kind : WPublicationKind
  deriving DecidableEq, Repr

structure WWorkerTrail (n : Nat) where
  epoch : WValidationTicket
  acceptedAt : Nat
  phase : WWorkerPhase
  host : Fin n
  target : Fin n
  index : Nat
  reads : List (WReadReceipt n)
  publications : List (WPublicationReceipt n)
  deriving DecidableEq, Repr

structure WCompletionReceipt (n : Nat) where
  service : Nat
  worker : WWorkerTrail n
  deriving DecidableEq, Repr

def wWorkerAuthorityAt {n : Nat}
    (w : WWorkerTrail n) (i : Fin n) : Prop :=
  i = w.host ∨
    ((w.phase = .backRun ∨ w.phase = .sumRun) ∧ i = w.target)

instance decidableWWorkerAuthorityAt {n : Nat}
    (w : WWorkerTrail n) (i : Fin n) :
    Decidable (wWorkerAuthorityAt w i) := by
  unfold wWorkerAuthorityAt
  infer_instance

/-- Actual reads and publications of one causally launched worker.
Unrelated services frame it; destructive services retire its witness. -/
def wWorkerReceiptStep {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket)
    (old : Option (WWorkerTrail n)) :
    Option (WWorkerTrail n) × Option (WCompletionReceipt n) :=
  let si := workerW x y
  let hard := (serW x y).hard
  if si.row = "I0" then
    match accept with
    | none => (none, none)
    | some epoch =>
      (some { epoch := epoch, acceptedAt := clock, phase := .prefixRun,
              host := root, target := root, index := 0,
              reads := [], publications := [] }, none)
  else if hard.hardS1 then (none, none)
  else match old with
  | none => (none, none)
  | some w =>
    let keep := (some w, none)
    let stop := (none, none)
    if si.row = "F" then keep
    else if si.row = "I1" then
      if (hard.hardLeft = true ∧ wWorkerAuthorityAt w edge) ∨
          (hard.hardRight = true ∧ wWorkerAuthorityAt w next)
      then stop else keep
    else if si.row = "P1" ∧ w.phase = .prefixRun ∧ w.host = edge ∧
        x.si.j.val = w.index then
      let read : WReadReceipt n :=
        { service := clock, site := next, target := next,
          index := w.index, value := y.u, kind := .prefixRead }
      let publications :=
        if w.index + 1 < c.t then
          { service := clock, site := next, oldU := y.u,
            oldBeta := y.beta, newU := si.uY, newBeta := si.betaY,
            kind := WPublicationKind.prefixZero } :: w.publications
        else w.publications
      (some { w with host := next, index := w.index + 1, reads := read :: w.reads, publications := publications }, none)
    else if si.row = "P3" ∧ w.phase = .prefixRun ∧ w.host = edge ∧
        w.index = c.t then
      let publication : WPublicationReceipt n :=
        { service := clock, site := edge, oldU := x.u,
          oldBeta := x.beta, newU := si.uX, newBeta := si.betaX,
          kind := .prefixEnd }
      (some { w with phase := .backRun, host := next, target := next, index := c.t, publications := publication :: w.publications }, none)
    else if si.row = "B0" ∧ w.phase = .backRun ∧ w.host = next ∧
        y.si.j.val = w.index then
      (some { w with host := edge, index := w.index - 1 }, none)
    else if si.row = "B1" ∧ w.phase = .backRun ∧ w.host = next ∧
        w.index = 1 then
      (some { w with phase := .sumRun, host := edge, index := 0 }, none)
    else if si.row = "S0" ∧ w.phase = .sumRun ∧ w.host = edge ∧
        x.si.j.val = w.index then
      let read : WReadReceipt n :=
        { service := clock, site := edge, target := w.target,
          index := w.index, value := x.u, kind := .sumRead }
      (some { w with host := next, index := w.index + 1, reads := read :: w.reads }, none)
    else if si.row = "S1" ∧ w.phase = .sumRun ∧ w.host = edge ∧
        w.target = next ∧ x.si.j.val = w.index then
      let read : WReadReceipt n :=
        { service := clock, site := edge, target := next,
          index := w.index, value := x.u, kind := .sumRead }
      let publication : WPublicationReceipt n :=
        { service := clock, site := next, oldU := y.u,
          oldBeta := y.beta, newU := si.uY, newBeta := si.betaY,
          kind := .target }
      (some { w with phase := .readyRun, host := next, index := 0, reads := read :: w.reads, publications := publication :: w.publications }, none)
    else if si.row = "A1" ∧ w.phase = .readyRun ∧ w.host = edge then
      (some { w with phase := .backRun, host := next, target := next, index := c.t }, none)
    else if si.row = "A0" ∧ w.phase = .readyRun ∧ w.host = edge ∧
        next = root then
      (none, some { service := clock, worker := w })
    else if wWorkerAuthorityAt w edge ∨ wWorkerAuthorityAt w next
    then stop else keep

structure WEdgeReceipt (n : Nat) (c : Compiled) where
  service : Nat
  edge : Fin n
  oldSource : ProjW c
  oldDestination : ProjW c
  serializer : SerResult
  worker : SIResult c.t

structure WOriginGhost (n : Nat) (c : Compiled) where
  clock : Nat
  validation : Fin n → Option WValidationTicket
  worker : Option (WWorkerTrail n)
  completion : Option (WCompletionReceipt n)
  services : List (WEdgeReceipt n c)

def wOriginInitial {n : Nat} {c : Compiled} : WOriginGhost n c :=
  { clock := 0, validation := fun _ => none, worker := none,
    completion := none, services := [] }

def wOriginGhostStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjW c) (G : WOriginGhost n c)
    (e : Fin n) : WOriginGhost n c :=
  let j := ring.rightNeighbor e
  let x := S e
  let y := S j
  let stamp := G.clock + 1
  let tickets := wValidationPair stamp x y (G.validation e) (G.validation j)
  let accept := wGenuineAcceptance root e x y (G.validation e) (G.validation j)
  let work := wWorkerReceiptStep root e j stamp x y accept G.worker
  let receipt : WEdgeReceipt n c :=
    { service := stamp, edge := e, oldSource := x,
      oldDestination := y, serializer := serW x y, worker := workerW x y }
  { clock := stamp
    validation := fun i =>
      if i = e then tickets.1
      else if i = j then tickets.2 else G.validation i
    worker := work.1
    completion := work.2
    services := receipt :: G.services }

def WFixedRoot {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjW c) : Prop :=
  (S root).native.l = true ∧
  (∀ i : Fin n, (S i).native.l = true → i = root) ∧
  Protected ring (fun i => (S i).native)

/-- No private certificate or visible-word coordinate is restricted
at the initial cut. The size assumptions are the paper's domain. -/
inductive WOriginHistory {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) :
    (Fin n → ProjW c) → WOriginGhost n c → Prop where
  | start (S : Fin n → ProjW c)
      (ht : 2 ≤ c.t) (hn : c.t + (2 ^ c.t - 1) ≤ n)
      (hroot : WFixedRoot ring root S) :
      WOriginHistory ring root S wOriginInitial
  | next {S : Fin n → ProjW c} {G : WOriginGhost n c}
      (h : WOriginHistory ring root S G) (e : Fin n)
      (hroot : WFixedRoot ring root (phiW ring S e)) :
      WOriginHistory ring root (phiW ring S e)
        (wOriginGhostStep ring root S G e)

def WOriginComplete {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (G : WOriginGhost n c) : Prop :=
  ∃ done : WCompletionReceipt n,
    G.completion = some done ∧
    ∀ k : Fin n, 0 < k.val → k.val < c.t →
      ∃ publication : WPublicationReceipt n,
        publication ∈ done.worker.publications ∧
        publication.kind = .prefixZero ∧
        publication.site = PPL.shiftRight ring root k.val ∧
        publication.newBeta = false

def RecurrenceOrigin {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (S : Fin n → ProjW c) : Prop :=
  ∃ (root : Fin n) (G : WOriginGhost n c),
    WOriginHistory ring root S G ∧ WOriginComplete ring root G

inductive WordHistory {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) :
    (Fin n → ProjW c) → WOriginGhost n c → Prop where
  | origin {S : Fin n → ProjW c} {G : WOriginGhost n c}
      (h : WOriginHistory ring root S G)
      (hcomplete : WOriginComplete ring root G) :
      WordHistory ring root S G
  | next {S : Fin n → ProjW c} {G : WOriginGhost n c}
      (h : WordHistory ring root S G) (e : Fin n) :
      WordHistory ring root (phiW ring S e)
        (wOriginGhostStep ring root S G e)

def WZero {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (S : Fin n → ProjW c) : Prop :=
  ∃ (root : Fin n) (G : WOriginGhost n c), WordHistory ring root S G

theorem WZero_origin {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (S : Fin n → ProjW c)
    (h : RecurrenceOrigin ring S) : WZero ring S := by
  obtain ⟨root, G, hrun, hcomplete⟩ := h
  exact ⟨root, G, WordHistory.origin hrun hcomplete⟩

theorem WZero_phi_step {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (S : Fin n → ProjW c) (e : Fin n)
    (h : WZero ring S) : WZero ring (phiW ring S e) := by
  obtain ⟨root, G, hG⟩ := h
  exact ⟨root, wOriginGhostStep ring root S G e, WordHistory.next hG e⟩

theorem WZero_real_noFire {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : WZero ring (piW C)) :
    WZero ring (piW ((protocol q).step ring C e)) := by
  rw [stepW_noFire hn ring C e hfire]
  exact WZero_phi_step ring (piW C) e h


/-! Raw-reader identities and the extinction cut. -/

inductive RawIdentity (n : Nat) where
  | inherited (site : Fin n)
  | fresh (service : Nat)
  deriving DecidableEq, Repr

structure RawReadReceipt (c : Compiled) (n : Nat) where
  service : Nat
  edge : Fin n
  destination : Fin n
  oldU : Bool
  oldBeta : Bool
  postLeader : Bool
  before : Option (RawTok c.t)
  after : Option (RawTok c.t)

structure RawLineage (c : Compiled) (n : Nat) where
  identity : RawIdentity n
  cutToken : Option (RawTok c.t)
  reads : List (RawReadReceipt c n)

structure RawServiceReceipt (c : Compiled) (n : Nat) where
  service : Nat
  edge : Fin n
  oldSource : ProjR c
  oldDestination : ProjR c
  result : RawResult c.t

structure RawGhost (c : Compiled) (n : Nat) where
  clock : Nat
  residents : Fin n → Option (RawLineage c n)
  services : List (RawServiceReceipt c n)

def initialRawGhost {c : Compiled} {n : Nat}
    (S : Fin n → ProjR c) : RawGhost c n :=
  { clock := 0
    residents := fun i =>
      (S i).rawTok.map fun tok =>
        { identity := .inherited i
          cutToken := some tok
          reads := [] }
    services := [] }

def rawGhostStep {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjR c)
    (G : RawGhost c n) (e : Fin n) : RawGhost c n :=
  let j := ring.rightNeighbor e
  let x := S e
  let y := S j
  let result := rawR x y
  let stamp := G.clock + 1
  let receipt : RawReadReceipt c n :=
    { service := stamp
      edge := e
      destination := j
      oldU := y.word.u
      oldBeta := y.word.beta
      postLeader := (postW x.word y.word).eY.l
      before := x.rawTok
      after := result.tokY }
  let nextY : Option (RawLineage c n) :=
    match x.rawTok with
    | some tok =>
      if y.rawTok.isSome then G.residents j
      else if tok.j < c.t then
        (G.residents e).map fun g =>
          { g with reads := g.reads ++ [receipt] }
      else none
    | none =>
      if y.rawTok.isSome then G.residents j
      else if y.rawKick then
        if 0 < c.t then
          some
            { identity := .fresh stamp
              cutToken := none
              reads := [receipt] }
        else none
      else none
  { clock := stamp
    residents := fun i =>
      if i = e then none
      else if i = j then nextY
      else G.residents i
    services :=
      { service := stamp
        edge := e
        oldSource := x
        oldDestination := y
        result := result } :: G.services }

def RawExtinct {c : Compiled} {n : Nat}
    (G : RawGhost c n) : Prop :=
  ∀ (i : Fin n) (g : RawLineage c n),
    G.residents i = some g →
    ∀ site : Fin n, g.identity ≠ .inherited site

inductive RawSeedHistory {c : Compiled} {n : Nat}
    (ring : DirectedRing n) :
    (Fin n → ProjR c) → RawGhost c n → Prop where
  | origin (S : Fin n → ProjR c)
      (h : RecurrenceOrigin ring (fun i => (S i).word)) :
      RawSeedHistory ring S (initialRawGhost S)
  | next {S : Fin n → ProjR c} {G : RawGhost c n}
      (h : RawSeedHistory ring S G) (e : Fin n) :
      RawSeedHistory ring (phiR ring S e)
        (rawGhostStep ring S G e)

def RawOrigin {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjR c)
    (G : RawGhost c n) : Prop :=
  RawSeedHistory ring S G ∧ RawExtinct G

inductive ReaderHistory {c : Compiled} {n : Nat}
    (ring : DirectedRing n) :
    (Fin n → ProjR c) → RawGhost c n → Prop where
  | origin (S : Fin n → ProjR c) (G : RawGhost c n)
      (h : RawOrigin ring S G) :
      ReaderHistory ring S G
  | next {S : Fin n → ProjR c} {G : RawGhost c n}
      (h : ReaderHistory ring S G) (e : Fin n) :
      ReaderHistory ring (phiR ring S e)
        (rawGhostStep ring S G e)

def R {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjR c) : Prop :=
  ∃ G : RawGhost c n, ReaderHistory ring S G

theorem R_origin {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjR c)
    (G : RawGhost c n) (h : RawOrigin ring S G) :
    R ring S :=
  ⟨G, ReaderHistory.origin S G h⟩

theorem R_step {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjR c)
    (e : Fin n) (h : R ring S) :
    R ring (phiR ring S e) := by
  obtain ⟨G, hG⟩ := h
  exact ⟨rawGhostStep ring S G e, ReaderHistory.next hG e⟩

theorem R_real_noFire {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : R ring (piR C)) :
    R ring (piR ((protocol q).step ring C e)) := by
  rw [stepR_noFire hn ring C e hfire]
  exact R_step ring (piR C) e h


/-! Exact proof-only replay of both digit transport lanes. -/

inductive DigitLane
  | writer | comparison
  deriving DecidableEq, Repr

inductive DigitSlot
  | output | input | carry
  deriving DecidableEq, Repr

structure DigitStamp (n : Nat) where
  time : Nat
  site : Fin n
  lane : DigitLane
  deriving DecidableEq, Repr

inductive DigitAtom (n : Nat)
  | inherited (lane : DigitLane) (site : Fin n) (slot : DigitSlot)
  | sampled (id : DigitStamp n)
  | missing (id : DigitStamp n) (slot : DigitSlot)
  deriving DecidableEq, Repr

/-- An unread slot is a causal obligation, not a numerical sample. -/
inductive DigitUnread (n : Nat)
  | inherited (lane : DigitLane) (site : Fin n)
  | bootstrap (id : DigitStamp n)
  | afterTail (id : DigitStamp n) (tail : Option (DigitAtom n))
  deriving DecidableEq, Repr

inductive DigitOutGhost (n : Nat)
  | empty
  | unread (cause : DigitUnread n)
  | packet (origin : Option (DigitAtom n))
  deriving DecidableEq, Repr

def DigitOutGhost.atom {n : Nat} :
    DigitOutGhost n → Option (DigitAtom n)
  | .packet a => a
  | _ => none

def DigitOutGhost.obligation {n : Nat} :
    DigitOutGhost n → Option (DigitUnread n)
  | .unread a => some a
  | _ => none

structure DigitSample (c : Compiled) (n : Nat) where
  id : DigitStamp n
  value : Fin c.topA
  tail : Bool
  cause : Option (DigitUnread n)
  deriving DecidableEq, Repr

structure DigitUse (c : Compiled) (n : Nat) where
  time : Nat
  target : Fin n
  operand : Option (DigitAtom n)
  value : Fin c.topA
  tail : Bool
  targetDigit : Fin c.topA
  carryIn : Bool
  errorIn : Bool
  deriving DecidableEq, Repr

structure DigitCarryGhost (c : Compiled) (n : Nat) where
  inherited : Option (DigitAtom n)
  uses : List (DigitUse c n)
  deriving DecidableEq, Repr

structure DigitLaneGhost (c : Compiled) (n : Nat) where
  out : DigitOutGhost n
  input : Option (DigitAtom n)
  carry : Option (DigitCarryGhost c n)
  deriving DecidableEq, Repr

structure DigitExport (c : Compiled) (n : Nat) where
  time : Nat
  lane : DigitLane
  source : Fin n
  destination : Fin n
  operand : Option (DigitAtom n)
  value : Fin c.topA
  tail : Bool
  deriving DecidableEq, Repr

structure DigitTerminal (c : Compiled) (n : Nat) where
  time : Nat
  lane : DigitLane
  source : Fin n
  destination : Fin n
  ledger : Option (DigitCarryGhost c n)
  carryBit : Bool
  errorBit : Bool
  deriving DecidableEq, Repr

structure DigitLaneView (c : Compiled) where
  leader : Bool
  marker : Bool
  digit : Fin c.topA
  out : OutTok c.topA
  input : InTok c.topA
  carryLive : Bool
  carryBit : Bool
  carryError : Bool
  deriving DecidableEq, Repr

def digitLaneView {c : Compiled}
    (lane : DigitLane) (x : ProjD c) (marker : Bool) :
    DigitLaneView c :=
  match lane with
  | .writer =>
      { leader := x.word.native.l
        marker := marker
        digit := x.top.d
        out := x.top.wOut
        input := x.top.wIn
        carryLive := x.top.wCarry.isW
        carryBit := wcC x.top.wCarry
        carryError := false }
  | .comparison =>
      { leader := x.word.native.l
        marker := marker
        digit := x.top.d
        out := x.top.qOut
        input := x.top.qIn
        carryLive := x.top.qCarry.isL
        carryBit := qcC x.top.qCarry
        carryError := qcE x.top.qCarry }

def DigitLaneGhost.initial {c : Compiled} {n : Nat}
    (lane : DigitLane) (site : Fin n)
    (v : DigitLaneView c) : DigitLaneGhost c n :=
  { out :=
      match v.out with
      | .E => .empty
      | .U => .unread (.inherited lane site)
      | .D _ _ => .packet (some (.inherited lane site .output))
    input :=
      match v.input with
      | .E => none
      | _ => some (.inherited lane site .input)
    carry :=
      if v.carryLive then
        some
          { inherited := some (.inherited lane site .carry)
            uses := [] }
      else none }

structure DigitInputGhost (n : Nat) where
  x : Option (DigitAtom n)
  y : Option (DigitAtom n)
  fx : Bool
  fy : Bool

structure DigitLaneReplay (c : Compiled) (n : Nat) where
  x : DigitLaneGhost c n
  y : DigitLaneGhost c n
  sample : Option (DigitSample c n)
  exported : Option (DigitExport c n)
  terminal : Option (DigitTerminal c n)
  deriving DecidableEq, Repr

def digitLaneReplay {c : Compiled} {n : Nat}
    (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) : DigitLaneReplay c n :=
  let stamp : DigitStamp n :=
    { time := time, site := source, lane := lane }
  let roots := x.leader || y.leader
  let terminal := y.leader || y.marker
  let success :=
    x.carryLive && !terminal && !y.carryLive && y.input.isS
  let launch :=
    !x.leader && x.marker && !x.carryLive &&
      x.input.isS && !y.leader
  let offer := x.out.isD && y.marker
  let useAt :=
    fun (site : Fin n) (v : DigitLaneView c)
        (g : DigitLaneGhost c n) (ci ei : Bool) =>
      ({ time := time
         target := site
         operand := g.input
         value := inV c v.input
         tail := inT v.input
         targetDigit := v.digit
         carryIn := ci
         errorIn := ei } : DigitUse c n)
  let oldCarry : DigitCarryGhost c n :=
    gx.carry.getD
      { inherited := some (.missing stamp .carry), uses := [] }
  let carries :
      Option (DigitCarryGhost c n) ×
        Option (DigitCarryGhost c n) :=
    if roots then
      ((if x.carryLive then none else gx.carry),
       (if y.carryLive then none else gy.carry))
    else if x.carryLive then
      if !terminal && success then
        (none,
         some
           { oldCarry with
             uses := oldCarry.uses ++
               [useAt destination y gy x.carryBit x.carryError] })
      else (none, gy.carry)
    else if launch then
      (some
         { inherited := none
           uses := [useAt source x gx true false] },
       gy.carry)
    else (gx.carry, gy.carry)
  let inputs : DigitInputGhost n × Bool :=
    if roots then
      ({ x := none, y := none, fx := true, fy := true }, false)
    else
      let s : DigitInputGhost n :=
        { x := gx.input, y := gy.input, fx := false, fy := false }
      let s :=
        if !s.fx && x.carryLive then
          { s with x := none, fx := true }
        else s
      let s :=
        if !s.fy && y.carryLive then
          { s with y := none, fy := true }
        else s
      let s :=
        if !s.fx && x.input.isS && inT x.input && !x.marker then
          { s with x := gx.input, fx := true }
        else s
      let s :=
        if !s.fx && x.input.isX then
          let s := { s with x := none, fx := true }
          if !s.fy && !y.leader && !y.marker && y.input.isS then
            { s with y := gx.input, fy := true }
          else s
        else s
      let s :=
        if success && !s.fy then
          { s with y := none, fy := true }
        else s
      let s :=
        if launch && !s.fx then
          { s with x := none, fx := true }
        else s
      let s :=
        if !s.fx && x.input.isP then
          if terminal then
            if !inT x.input then
              { s with x := gx.input, fx := true }
            else if !x.marker then
              { s with x := none, fx := true }
            else s
          else if !y.leader && !y.marker &&
              y.input.isE && !y.carryLive && !s.fy then
            { x := none, y := gx.input, fx := true, fy := true }
          else if y.input.isS && !y.carryLive then
            { s with x := gx.input, fx := true }
          else s
        else s
      let accepted :=
        !s.fy && offer && y.input.isE && !y.carryLive
      let s :=
        if accepted then
          { s with y := gx.out.atom, fy := true }
        else s
      (s, accepted)
  let rearm : DigitOutGhost n :=
    if outT x.out then
      .unread (.afterTail stamp gx.out.atom)
    else .empty
  let outputs :
      DigitOutGhost n × DigitOutGhost n ×
        Option (DigitSample c n) :=
    if roots then
      (.empty, .empty, none)
    else if offer then
      if inputs.2 then
        (rearm, gy.out, none)
      else (gx.out, gy.out, none)
    else if x.out.isD && !y.marker && y.out.isE then
      (rearm, .packet gx.out.atom, none)
    else if x.out.isU then
      (.packet (some (.sampled stamp)), gy.out,
       some
         { id := stamp
           value := x.digit
           tail := x.marker
           cause := gx.out.obligation })
    else if x.marker && x.out.isE && !x.leader then
      (.unread (.bootstrap stamp), gy.out, none)
    else (gx.out, gy.out, none)
  let exported : Option (DigitExport c n) :=
    if inputs.2 then
      some
        { time := time
          lane := lane
          source := source
          destination := destination
          operand := gx.out.atom
          value := outV c x.out
          tail := outT x.out }
    else none
  let finished : Option (DigitTerminal c n) :=
    if !roots && x.carryLive && terminal then
      some
        { time := time
          lane := lane
          source := source
          destination := destination
          ledger := gx.carry
          carryBit := x.carryBit
          errorBit := x.carryError }
    else none
  { x :=
      { out := outputs.1
        input := inputs.1.x
        carry := carries.1 }
    y :=
      { out := outputs.2.1
        input := inputs.1.y
        carry := carries.2 }
    sample := outputs.2.2
    exported := exported
    terminal := finished }

inductive DigitBaseOrigin (n : Nat)
  | inherited (site : Fin n)
  | rootLaunch (time : Nat) (root destination : Fin n)
  deriving DecidableEq, Repr

structure DigitZeroProposal (n : Nat) where
  time : Nat
  site : Fin n
  origin : Option (DigitBaseOrigin n)
  deriving DecidableEq, Repr

structure DigitBaseMerge (n : Nat) where
  time : Nat
  source : Fin n
  destination : Fin n
  incoming : Option (DigitBaseOrigin n)
  survivor : Option (DigitBaseOrigin n)
  deriving DecidableEq, Repr

structure DigitBaseReplay (n : Nat) where
  x : Option (DigitBaseOrigin n)
  y : Option (DigitBaseOrigin n)
  proposal : Option (DigitZeroProposal n)
  merge : Option (DigitBaseMerge n)
  deriving DecidableEq, Repr

/-- A zero proposal is recorded even when OLD dirty suppresses
the visible write. Physical identity and covering obligation differ. -/
def digitBaseReplay {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : ProjD c) (betaY : Bool)
    (gx gy : Option (DigitBaseOrigin n)) :
    DigitBaseReplay n :=
  let rootX := x.word.native.l
  let rootY := y.word.native.l
  let collision : DigitBaseMerge n :=
    { time := time
      source := source
      destination := destination
      incoming := gx
      survivor := gy }
  if rootY then
    { x := none, y := gy, proposal := none, merge := none }
  else if rootX && !rootY then
    { x := none
      y :=
        if y.top.wBase == .NONE then
          some (.rootLaunch time source destination)
        else gy
      proposal := none
      merge := none }
  else if !rootX && x.top.wBase == .ZERO then
    { x := none
      y :=
        if !rootY && !betaY && y.top.wBase == .NONE then gx
        else gy
      proposal :=
        some { time := time, site := source, origin := gx }
      merge :=
        if !rootY && !betaY && y.top.wBase != .NONE then
          some collision
        else none }
  else if !rootX && x.top.wBase == .SEEK then
    { x := none
      y :=
        if !rootY && y.top.wBase == .NONE then gx
        else gy
      proposal := none
      merge :=
        if !rootY && y.top.wBase != .NONE then
          some collision
        else none }
  else
    { x := gx, y := gy, proposal := none, merge := none }

structure DigitGhost (c : Compiled) (n : Nat) where
  writer : DigitLaneGhost c n
  comparison : DigitLaneGhost c n
  base : Option (DigitBaseOrigin n)
  deriving DecidableEq, Repr

def DigitGhost.initial {c : Compiled} {n : Nat}
    (site : Fin n) (x : ProjD c) : DigitGhost c n :=
  { writer :=
      DigitLaneGhost.initial .writer site
        (digitLaneView .writer x x.word.beta)
    comparison :=
      DigitLaneGhost.initial .comparison site
        (digitLaneView .comparison x x.word.beta)
    base :=
      if x.top.wBase == .NONE then none
      else some (.inherited site) }

structure DigitService (c : Compiled) (n : Nat) where
  x : DigitGhost c n
  y : DigitGhost c n
  writer : DigitLaneReplay c n
  comparison : DigitLaneReplay c n
  base : DigitBaseReplay n
  dirtyClearedX : Bool
  dirtyClearedY : Bool
  deriving DecidableEq, Repr

def digitService {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : ProjD c) (gx gy : DigitGhost c n) :
    DigitService c n :=
  let worker := workerW x.word y.word
  let writer :=
    digitLaneReplay .writer time source destination
      (digitLaneView .writer x worker.betaX)
      (digitLaneView .writer y worker.betaY)
      gx.writer gy.writer
  let comparison :=
    digitLaneReplay .comparison time source destination
      (digitLaneView .comparison x x.word.beta)
      (digitLaneView .comparison y y.word.beta)
      gx.comparison gy.comparison
  let base :=
    digitBaseReplay time source destination
      x y worker.betaY gx.base gy.base
  { x :=
      { writer := writer.x
        comparison := comparison.x
        base := base.x }
    y :=
      { writer := writer.y
        comparison := comparison.y
        base := base.y }
    writer := writer
    comparison := comparison
    base := base
    dirtyClearedX := x.top.topDirty
    dirtyClearedY := y.top.topDirty }

def digitGhostInitial {c : Compiled} {n : Nat}
    (S : Fin n → ProjD c) : Fin n → DigitGhost c n :=
  fun i => DigitGhost.initial i (S i)

def digitGhostStep {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n)
    (time : Nat) (e : Fin n) : Fin n → DigitGhost c n :=
  let j := ring.rightNeighbor e
  let receipt := digitService time e j (S e) (S j) (G e) (G j)
  fun i =>
    if i = e then receipt.x
    else if i = j then receipt.y
    else G i


/-! Finite actual-edge logs. No arbitrary annotation injection. -/

structure DigitFrame (c : Compiled) (n : Nat) where
  time : Nat
  edge : Fin n
  old : Fin n → ProjD c
  oldGhost : Fin n → DigitGhost c n
  receipt : DigitService c n

structure DigitAudit (c : Compiled) (n : Nat) where
  start : Fin n → ProjD c
  clock : Nat
  current : Fin n → DigitGhost c n
  frames : List (DigitFrame c n)

def digitAuditInitial {c : Compiled} {n : Nat}
    (S : Fin n → ProjD c) : DigitAudit c n :=
  { start := S
    clock := 0
    current := digitGhostInitial S
    frames := [] }

def digitAuditStep {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) : DigitAudit c n :=
  let j := ring.rightNeighbor e
  let stamp := A.clock + 1
  { start := A.start
    clock := stamp
    current := digitGhostStep ring S A.current stamp e
    frames :=
      { time := stamp
        edge := e
        old := S
        oldGhost := A.current
        receipt := digitService stamp e j
          (S e) (S j) (A.current e) (A.current j) } :: A.frames }

/-- Both the recurrence certificate and its exact completion endpoint
are retained at the cut where arbitrary digit scratch is adjoined. -/
inductive DigitSeedHistory {c : Compiled} {n : Nat}
    (ring : DirectedRing n) :
    (Fin n → ProjD c) → DigitAudit c n → Prop where
  | origin (S : Fin n → ProjD c)
      (h : RecurrenceOrigin ring (fun i => (S i).word)) :
      DigitSeedHistory ring S (digitAuditInitial S)
  | next {S : Fin n → ProjD c} {A : DigitAudit c n}
      (h : DigitSeedHistory ring S A) (e : Fin n) :
      DigitSeedHistory ring (phiD ring S e)
        (digitAuditStep ring S A e)

/-- A cut is an endpoint of this finite past, never an extrapolation
of future physical services. -/
def DigitAt {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (A : DigitAudit c n)
    (cut : Nat) (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n) : Prop :=
  (cut = 0 ∧ S = A.start ∧ G = digitGhostInitial A.start) ∨
  ∃ f : DigitFrame c n,
    f ∈ A.frames ∧ f.time = cut ∧
    S = phiD ring f.old f.edge ∧
    G = digitGhostStep ring f.old f.oldGhost f.time f.edge

def DigitFirstCut (P : Nat → Prop) (cut : Nat) : Prop :=
  P cut ∧ ∀ earlier : Nat, earlier < cut → ¬ P earlier


def digitSpan (c : Compiled) : Nat :=
  2 ^ c.t - 1

def digitSite {n : Nat} (ring : DirectedRing n)
    (root : Fin n) : Nat → Fin n
  | 0 => root
  | k + 1 => ring.rightNeighbor (digitSite ring root k)

def DigitNonrootDelimiter {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (k : Nat) : Prop :=
  0 < k ∧ k < n ∧ (S (digitSite ring root k)).word.beta = true

def DigitFirstDelimiter {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (first : Nat) : Prop :=
  DigitNonrootDelimiter ring root S first ∧
  ∀ k : Nat, 0 < k → k < first →
    (S (digitSite ring root k)).word.beta = false

def DigitNextDelimiterOrRoot {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (start stop : Nat) : Prop :=
  DigitNonrootDelimiter ring root S start ∧
  start < stop ∧ stop ≤ n ∧
  (stop < n → (S (digitSite ring root stop)).word.beta = true) ∧
  ∀ k : Nat, start < k → k < stop →
    (S (digitSite ring root k)).word.beta = false

def DigitFirstSegment {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (first stop : Nat) : Prop :=
  DigitFirstDelimiter ring root S first ∧
  DigitNextDelimiterOrRoot ring root S first stop

def DigitCompleteBlock {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (start : Nat) : Prop :=
  DigitNextDelimiterOrRoot ring root S start (start + digitSpan c) ∧
  start + digitSpan c < n

def DigitCompletePair {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (source target : Nat) : Prop :=
  DigitCompleteBlock ring root S source ∧
  target = source + digitSpan c ∧
  DigitCompleteBlock ring root S target

/-- This includes a truncated first segment ending at the leader.
Only the leader-adjacent site is exempt from the base proposal. -/
def DigitFirstWritable {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (i : Fin n) : Prop :=
  ∃ (first stop k : Nat),
    DigitFirstSegment ring root S first stop ∧
    first ≤ k ∧ k < stop ∧ k + 1 < n ∧
    i = digitSite ring root k


def digitReceiptLane {c : Compiled} {n : Nat}
    (lane : DigitLane) (r : DigitService c n) :
    DigitLaneReplay c n :=
  match lane with
  | .writer => r.writer
  | .comparison => r.comparison

def DigitRecordedSample {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (s : DigitSample c n) : Prop :=
  ∃ f : DigitFrame c n,
    f ∈ A.frames ∧
    f.time = s.id.time ∧
    f.edge = s.id.site ∧
    (digitReceiptLane s.id.lane f.receipt).sample = some s ∧
    s.value = (f.old f.edge).top.d

def DigitRecordedExport {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (x : DigitExport c n) : Prop :=
  ∃ f : DigitFrame c n,
    f ∈ A.frames ∧
    f.time = x.time ∧
    f.edge = x.source ∧
    (digitReceiptLane x.lane f.receipt).exported = some x

def DigitRecordedTerminal {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (t : DigitTerminal c n) : Prop :=
  ∃ f : DigitFrame c n,
    f ∈ A.frames ∧
    f.time = t.time ∧
    f.edge = t.source ∧
    (digitReceiptLane t.lane f.receipt).terminal = some t

/-- Exact same-group receipts: reverse export order, forward aligned
consumption, one tail, no inherited carry, and an actual terminal.
There is deliberately no ordering constraint on sample times. -/
def DigitCompletion {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (A : DigitAudit c n)
    (root : Fin n) (source target : Nat)
    (lane : DigitLane) (cut : Nat)
    (terminal : DigitTerminal c n) : Prop :=
  let r := digitSpan c
  DigitCompletePair ring root A.start source target ∧
  DigitRecordedTerminal A terminal ∧
  terminal.lane = lane ∧
  terminal.source = digitSite ring root (target + (r - 1)) ∧
  terminal.destination = digitSite ring root (target + r) ∧
  terminal.time ≤ A.clock ∧
  ∃ (positive : 0 < r)
    (ledger : DigitCarryGhost c n)
    (samples : Fin r → DigitSample c n)
    (exports : Fin r → DigitExport c n)
    (uses : Fin r → DigitUse c n),
    let first : Fin r := ⟨0, positive⟩
    let last : Fin r := ⟨r - 1, by omega⟩
    terminal.ledger = some ledger ∧
    ledger.inherited = none ∧
    ledger.uses.length = r ∧
    (∀ j : Fin r,
      DigitRecordedSample A (samples j) ∧
      (samples j).id.lane = lane ∧
      (samples j).id.site =
        digitSite ring root (source + j.val) ∧
      cut < (samples j).id.time ∧
      (samples j).tail = decide (j.val = 0) ∧
      DigitRecordedExport A (exports j) ∧
      (exports j).lane = lane ∧
      (exports j).source =
        digitSite ring root (source + (r - 1)) ∧
      (exports j).destination = digitSite ring root target ∧
      (exports j).operand =
        some (DigitAtom.sampled (samples j).id) ∧
      (exports j).value = (samples j).value ∧
      (exports j).tail = (samples j).tail ∧
      ledger.uses[j.val]? = some (uses j) ∧
      (uses j).target = digitSite ring root (target + j.val) ∧
      (uses j).operand =
        some (DigitAtom.sampled (samples j).id) ∧
      (uses j).value = (samples j).value ∧
      (uses j).tail = (samples j).tail ∧
      (samples j).id.time < (exports j).time ∧
      (exports j).time < (uses j).time ∧
      (uses j).time < terminal.time) ∧
    (∀ i j : Fin r,
      i.val < j.val →
        (exports j).time < (exports i).time ∧
        (uses i).time < (uses j).time) ∧
    (∀ other : DigitExport c n,
      DigitRecordedExport A other →
      other.lane = lane →
      other.source =
        digitSite ring root (source + (r - 1)) →
      other.destination = digitSite ring root target →
      (exports last).time ≤ other.time →
      other.time ≤ (exports first).time →
      ∃ j : Fin r, other = exports j)

def DigitFirstStrictCompletion {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (A : DigitAudit c n)
    (root : Fin n) (source target : Nat)
    (lane : DigitLane) (cut : Nat)
    (terminal : DigitTerminal c n) : Prop :=
  DigitCompletion ring A root source target lane cut terminal ∧
  ∀ other : DigitTerminal c n,
    DigitCompletion ring A root source target lane cut other →
    terminal.time ≤ other.time

def DigitNextCompletion {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (A : DigitAudit c n)
    (root : Fin n) (source target : Nat)
    (lane : DigitLane) (after : Nat)
    (terminal : DigitTerminal c n) : Prop :=
  DigitCompletion ring A root source target lane 0 terminal ∧
  after < terminal.time ∧
  ∀ other : DigitTerminal c n,
    DigitCompletion ring A root source target lane 0 other →
    after < other.time →
    terminal.time ≤ other.time

def DigitFiveCompletions {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (A : DigitAudit c n)
    (root : Fin n) (source target : Nat)
    (lane : DigitLane) (after : Nat)
    (last : DigitTerminal c n) : Prop :=
  ∃ first second third fourth : DigitTerminal c n,
    DigitNextCompletion ring A root source target lane after first ∧
    DigitNextCompletion ring A root source target lane
      first.time second ∧
    DigitNextCompletion ring A root source target lane
      second.time third ∧
    DigitNextCompletion ring A root source target lane
      third.time fourth ∧
    DigitNextCompletion ring A root source target lane
      fourth.time last


def DigitActualBaseLaunch {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (A : DigitAudit c n)
    (time : Nat) : Prop :=
  ∃ f : DigitFrame c n,
    f ∈ A.frames ∧ f.time = time ∧ f.edge = root ∧
    f.receipt.base.y =
      some (.rootLaunch time root (ring.rightNeighbor root))

inductive DigitBaseLineage {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (A : DigitAudit c n) :
    Nat → List (DigitBaseOrigin n) → Nat → Prop where
  | launch (time : Nat) (h : DigitActualBaseLaunch ring root A time) :
      DigitBaseLineage ring root A time
        [.rootLaunch time root (ring.rightNeighbor root)] time
  | transfer {birth previous : Nat}
      {current : DigitBaseOrigin n} {past : List (DigitBaseOrigin n)}
      (h : DigitBaseLineage ring root A birth (current :: past) previous)
      (f : DigitFrame c n) (merge : DigitBaseMerge n)
      (survivor : DigitBaseOrigin n)
      (hf : f ∈ A.frames)
      (hm : f.receipt.base.merge = some merge)
      (ht : previous < f.time)
      (hclock : merge.time = f.time)
      (hin : merge.incoming = some current)
      (hout : merge.survivor = some survivor) :
      DigitBaseLineage ring root A birth
        (survivor :: current :: past) f.time

def DigitBaseExtinct {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (A : DigitAudit c n)
    (boundary retired : Nat) : Prop :=
  boundary ≤ retired ∧
  ∃ (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n),
    DigitAt ring A retired S G ∧
    ∀ i : Fin n,
      ((S i).top.wBase = .NONE ∧ (G i).base = none) ∨
      (∃ born : Nat,
        boundary < born ∧
        (S i).top.wBase ≠ .NONE ∧
        (G i).base =
          some (.rootLaunch born root (ring.rightNeighbor root)))

def DigitActualZeroProposal {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (proposal : DigitZeroProposal n) : Prop :=
  ∃ f : DigitFrame c n,
    f ∈ A.frames ∧ f.receipt.base.proposal = some proposal ∧
    proposal.time = f.time ∧ proposal.site = f.edge

def DigitCoverProposal {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (A : DigitAudit c n)
    (boundary retired cut : Nat) (chain : List (DigitBaseOrigin n))
    (site : Fin n) (proposal : DigitZeroProposal n) : Prop :=
  DigitActualZeroProposal A proposal ∧
  proposal.site = site ∧ retired < proposal.time ∧ proposal.time ≤ cut ∧
  ∃ born : Nat,
    boundary < born ∧
    proposal.origin =
      some (.rootLaunch born root (ring.rightNeighbor root)) ∧
    DigitBaseOrigin.rootLaunch born root (ring.rightNeighbor root) ∈ chain

/-- Cover columns may overlap in global time, but one actual service
cannot supply both receipts for a site. A collision transfers only
the uncovered obligation, not the incoming physical identity. -/
def DigitTwoBaseCovers {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (A : DigitAudit c n)
    (boundary retired cut : Nat) : Prop :=
  DigitBaseExtinct ring root A boundary retired ∧
  retired ≤ cut ∧ cut ≤ A.clock ∧
  ((∀ i : Fin n, ¬ DigitFirstWritable ring root A.start i) ∨
    ∃ (firstBorn secondBorn firstLast secondLast : Nat)
      (firstChain secondChain : List (DigitBaseOrigin n)),
      boundary < firstBorn ∧ firstBorn < secondBorn ∧
      DigitBaseLineage ring root A firstBorn firstChain firstLast ∧
      DigitBaseLineage ring root A secondBorn secondChain secondLast ∧
      firstLast ≤ cut ∧ secondLast ≤ cut ∧
      ∀ i : Fin n, DigitFirstWritable ring root A.start i →
        ∃ (first second : DigitZeroProposal n),
          DigitCoverProposal ring root A boundary retired cut firstChain i first ∧
          DigitCoverProposal ring root A boundary retired cut secondChain i second ∧
          first.time < second.time)

def DigitBaseValueCut {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (A : DigitAudit c n)
    (boundary retired cut : Nat) : Prop :=
  DigitFirstCut
    (fun k => DigitTwoBaseCovers ring root A boundary retired k) cut


/-! Finite structural boundary receipts, allowing inert payload. -/

def DigitLeadingInput {A : Nat} (input : InTok A) : Prop :=
  input = .E ∨ ∃ value : Fin A, input = .S value false

def DigitFinalInput {A : Nat} (input : InTok A) : Prop :=
  input = .E ∨
    ∃ (value : Fin A) (tail : Bool), input = .P value tail

def digitEndpointView {c : Compiled} {n : Nat}
    (lane : DigitLane) (S : Fin n → ProjD c) (i : Fin n) :
    DigitLaneView c :=
  digitLaneView lane (S i) (S i).word.beta

def DigitLastCarryInert {c : Compiled}
    (n offset : Nat) (v : DigitLaneView c) : Prop :=
  offset + 1 = n ∧ v.carryLive = true

def DigitLeadingBoundary {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) : Prop :=
  ∃ first stop : Nat,
    DigitFirstSegment ring root S first stop ∧
    (∀ (lane : DigitLane) (k : Nat),
      0 < k → k < first →
      let v := digitEndpointView lane S (digitSite ring root k)
      v.out = .E ∧
      v.carryLive = false ∧
      DigitLeadingInput v.input) ∧
    (∀ (lane : DigitLane) (k : Nat),
      first ≤ k → k < stop →
      let v := digitEndpointView lane S (digitSite ring root k)
      DigitLastCarryInert n k v ∨
        (v.carryLive = false ∧
          (if k = first then v.input = .E
           else DigitLeadingInput v.input)))

def DigitFinalBoundary {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) : Prop :=
  ∀ source last : Nat,
    DigitCompleteBlock ring root S source →
    last = source + digitSpan c →
    DigitNextDelimiterOrRoot ring root S last n →
    ∀ (lane : DigitLane) (k : Nat),
      last ≤ k → k < n →
      let v := digitEndpointView lane S (digitSite ring root k)
      DigitLastCarryInert n k v ∨
        (v.carryLive = false ∧ DigitFinalInput v.input)

def DigitBoundaryReceipt {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) : Prop :=
  DigitLeadingBoundary ring root S ∧
  DigitFinalBoundary ring root S

def DigitCurrentPacket {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n) (lane : DigitLane)
    (source cut now : Nat)
    (origin : Option (DigitAtom n))
    (value : Fin c.topA) (tail : Bool) : Prop :=
  ∃ (id : DigitStamp n) (sample : DigitSample c n) (offset : Nat),
    origin = some (.sampled id) ∧
    sample.id = id ∧
    DigitRecordedSample A sample ∧
    id.lane = lane ∧
    offset < digitSpan c ∧
    id.site = digitSite ring root (source + offset) ∧
    cut < id.time ∧
    id.time ≤ now ∧
    sample.value = value ∧
    sample.tail = tail

def DigitCurrentUse {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n) (lane : DigitLane)
    (source cut now : Nat) (use : DigitUse c n) : Prop :=
  use.time ≤ now ∧
  DigitCurrentPacket ring root A lane source cut now
    use.operand use.value use.tail ∧
  ∃ id : DigitStamp n,
    use.operand = some (.sampled id) ∧ id.time < use.time

def DigitCurrentCarry {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n) (lane : DigitLane)
    (source cut now : Nat)
    (carry : Option (DigitCarryGhost c n)) : Prop :=
  ∃ ledger : DigitCarryGhost c n,
    carry = some ledger ∧
    ledger.inherited = none ∧
    ledger.uses ≠ [] ∧
    ∀ use : DigitUse c n, use ∈ ledger.uses →
      DigitCurrentUse ring root A lane source cut now use

def digitEndpointGhost {c : Compiled} {n : Nat}
    (lane : DigitLane) (g : DigitGhost c n) : DigitLaneGhost c n :=
  match lane with
  | .writer => g.writer
  | .comparison => g.comparison

def DigitCurrentOutput {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n) (lane : DigitLane)
    (source cut now : Nat)
    (v : DigitLaneView c) (g : DigitLaneGhost c n) : Prop :=
  match v.out with
  | .E => True
  | .U => ∃ cause : DigitUnread n, g.out = .unread cause
  | .D value tail =>
      DigitCurrentPacket ring root A lane source cut now
        g.out.atom value tail

def DigitCurrentInput {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n) (lane : DigitLane)
    (source cut now : Nat)
    (v : DigitLaneView c) (g : DigitLaneGhost c n) : Prop :=
  match v.input with
  | .E => True
  | .X => False
  | .P value tail =>
      DigitCurrentPacket ring root A lane source cut now
        g.input value tail
  | .S value tail =>
      DigitCurrentPacket ring root A lane source cut now
        g.input value tail

def DigitPairCurrent {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (lane : DigitLane) (source target cut now : Nat) : Prop :=
  ∀ offset : Nat, offset < digitSpan c →
    let sourceSite := digitSite ring root (source + offset)
    let targetSite := digitSite ring root (target + offset)
    let sourceView := digitEndpointView lane S sourceSite
    let targetView := digitEndpointView lane S targetSite
    let sourceGhost := digitEndpointGhost lane (G sourceSite)
    let targetGhost := digitEndpointGhost lane (G targetSite)
    DigitCurrentOutput ring root A lane source cut now
      sourceView sourceGhost ∧
    DigitCurrentInput ring root A lane source cut now
      targetView targetGhost ∧
    (targetView.carryLive = true →
      DigitCurrentCarry ring root A lane source cut now
        targetGhost.carry)

def DigitComparisonsCurrent {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (restart now : Nat) : Prop :=
  ∀ source target : Nat,
    DigitCompletePair ring root A.start source target →
    DigitPairCurrent ring root A S G .comparison
      source target restart now


/-! Shared serial cohorts are distinct from individual packet IDs. -/

def DigitAnchor {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (A : DigitAudit c n)
    (root : Fin n) (source target : Nat)
    (lane : DigitLane) (anchor : DigitTerminal c n)
    (anchorTail : DigitStamp n) : Prop :=
  DigitFirstStrictCompletion ring A root source target lane 0 anchor ∧
  ∃ (ledger : DigitCarryGhost c n)
    (firstUse : DigitUse c n)
    (sample : DigitSample c n),
    anchor.ledger = some ledger ∧
    ledger.uses.head? = some firstUse ∧
    firstUse.operand = some (DigitAtom.sampled anchorTail) ∧
    DigitRecordedSample A sample ∧
    sample.id = anchorTail ∧
    sample.id.lane = lane ∧
    sample.id.site = digitSite ring root source ∧
    sample.tail = true

inductive DigitTailRank {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (lane : DigitLane)
    (source : Fin n) (anchorTail : DigitStamp n) :
    DigitStamp n → Nat → Prop where
  | anchor :
      DigitTailRank A lane source anchorTail anchorTail 0
  | successor
      {previous : DigitStamp n} {rank : Nat}
      (previousRank :
        DigitTailRank A lane source anchorTail previous rank)
      (sample : DigitSample c n) (rearm : DigitStamp n)
      (recorded : DigitRecordedSample A sample)
      (sampleLane : sample.id.lane = lane)
      (sampleSource : sample.id.site = source)
      (sampleTail : sample.tail = true)
      (cause :
        sample.cause =
          some (DigitUnread.afterTail rearm
            (some (DigitAtom.sampled previous))))
      (rearmLane : rearm.lane = lane)
      (rearmSource : rearm.site = source)
      (previousBefore : previous.time < rearm.time)
      (rearmBefore : rearm.time < sample.id.time) :
      DigitTailRank A lane source anchorTail sample.id (rank + 1)

def DigitAnchorMember {c : Compiled} {n : Nat}
    (anchor : DigitTerminal c n) (id : DigitStamp n) : Prop :=
  ∃ (ledger : DigitCarryGhost c n) (use : DigitUse c n),
    anchor.ledger = some ledger ∧
    use ∈ ledger.uses ∧
    use.operand = some (DigitAtom.sampled id)

/-- The preceding tail determines the successor cohort across
all source positions. Sample timestamps do not order cohorts. -/
def DigitSampleCohort {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (lane : DigitLane)
    (source : Fin n) (anchor : DigitTerminal c n)
    (anchorTail : DigitStamp n)
    (sample : DigitSample c n) (rank : Nat) : Prop :=
  DigitRecordedSample A sample ∧
  sample.id.lane = lane ∧
  ((rank = 0 ∧ DigitAnchorMember anchor sample.id) ∨
    ∃ (previous : DigitStamp n) (previousRank : Nat)
      (rearm : DigitStamp n),
      rank = previousRank + 1 ∧
      DigitTailRank A lane source anchorTail previous previousRank ∧
      sample.cause =
        some (DigitUnread.afterTail rearm
          (some (DigitAtom.sampled previous))) ∧
      rearm.lane = lane ∧
      rearm.site = sample.id.site ∧
      previous.time < rearm.time ∧
      rearm.time < sample.id.time)

def DigitAtomCohort {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (lane : DigitLane)
    (source : Fin n) (anchor : DigitTerminal c n)
    (anchorTail : DigitStamp n)
    (origin : Option (DigitAtom n)) (rank : Nat) : Prop :=
  ∃ sample : DigitSample c n,
    origin = some (DigitAtom.sampled sample.id) ∧
    DigitSampleCohort A lane source anchor anchorTail sample rank

/-- Designation before materialization, with no numerical sample. -/
def DigitUnreadCohort {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (lane : DigitLane)
    (source : Fin n) (anchorTail : DigitStamp n)
    (cause : DigitUnread n) (rank : Nat) : Prop :=
  ∃ (previous : DigitStamp n) (previousRank : Nat)
    (rearm : DigitStamp n),
    rank = previousRank + 1 ∧
    DigitTailRank A lane source anchorTail previous previousRank ∧
    cause =
      DigitUnread.afterTail rearm
        (some (DigitAtom.sampled previous)) ∧
    rearm.lane = lane ∧
    previous.time < rearm.time

def DigitTerminalRanked {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (lane : DigitLane)
    (source : Fin n) (anchor : DigitTerminal c n)
    (anchorTail : DigitStamp n)
    (terminal : DigitTerminal c n) : Prop :=
  ∃ (ledger : DigitCarryGhost c n) (rank : Nat),
    terminal.ledger = some ledger ∧
    ledger.inherited = none ∧
    ledger.uses ≠ [] ∧
    ∀ use : DigitUse c n,
      use ∈ ledger.uses →
      DigitAtomCohort A lane source anchor anchorTail use.operand rank

def DigitRankedOutput {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (lane : DigitLane) (source site : Fin n)
    (anchor : DigitTerminal c n) (anchorTail : DigitStamp n)
    (now : Nat) (v : DigitLaneView c)
    (g : DigitLaneGhost c n) : Prop :=
  match v.out with
  | .E => True
  | .U =>
      ∃ (cause : DigitUnread n) (rank : Nat),
        g.out = .unread cause ∧
        DigitUnreadCohort A lane source anchorTail cause rank ∧
        (match cause with
         | .afterTail rearm _ => rearm.site = site ∧ rearm.time ≤ now
         | _ => False)
  | .D _ _ =>
      ∃ rank : Nat,
        DigitAtomCohort A lane source anchor anchorTail
          g.out.atom rank

def DigitRankedInput {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (lane : DigitLane) (source : Fin n)
    (anchor : DigitTerminal c n) (anchorTail : DigitStamp n)
    (v : DigitLaneView c) (g : DigitLaneGhost c n) : Prop :=
  match v.input with
  | .E => True
  | .X => False
  | .P _ _ =>
      ∃ rank : Nat,
        DigitAtomCohort A lane source anchor anchorTail
          g.input rank
  | .S _ _ =>
      ∃ rank : Nat,
        DigitAtomCohort A lane source anchor anchorTail
          g.input rank

def DigitRankedCarry {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (lane : DigitLane) (source : Fin n)
    (anchor : DigitTerminal c n) (anchorTail : DigitStamp n)
    (carry : Option (DigitCarryGhost c n)) : Prop :=
  ∃ (ledger : DigitCarryGhost c n) (rank : Nat),
    carry = some ledger ∧
    ledger.inherited = none ∧
    ledger.uses ≠ [] ∧
    ∀ use : DigitUse c n, use ∈ ledger.uses →
      DigitAtomCohort A lane source anchor anchorTail
        use.operand rank

def DigitPairRanked {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (lane : DigitLane) (source target now : Nat)
    (anchor : DigitTerminal c n) (anchorTail : DigitStamp n) : Prop :=
  DigitAnchor ring A root source target lane anchor anchorTail ∧
  anchor.time ≤ now ∧
  ∀ offset : Nat, offset < digitSpan c →
    let sourceSite := digitSite ring root (source + offset)
    let targetSite := digitSite ring root (target + offset)
    let sourceView := digitEndpointView lane S sourceSite
    let targetView := digitEndpointView lane S targetSite
    let sourceGhost := digitEndpointGhost lane (G sourceSite)
    let targetGhost := digitEndpointGhost lane (G targetSite)
    let sourceBorder := digitSite ring root source
    DigitRankedOutput A lane sourceBorder sourceSite anchor anchorTail now
      sourceView sourceGhost ∧
    DigitRankedInput A lane sourceBorder anchor anchorTail
      targetView targetGhost ∧
    (targetView.carryLive = true →
      DigitRankedCarry A lane sourceBorder anchor anchorTail
        targetGhost.carry)

def DigitAllPairsRanked {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (now : Nat) : Prop :=
  ∀ source target : Nat,
    DigitCompletePair ring root A.start source target →
    ∀ lane : DigitLane,
      ∃ (anchor : DigitTerminal c n) (anchorTail : DigitStamp n),
        DigitPairRanked ring root A S G lane
          source target now anchor anchorTail

def DigitTerminalRank {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (lane : DigitLane) (source : Fin n)
    (anchor : DigitTerminal c n) (anchorTail : DigitStamp n)
    (terminal : DigitTerminal c n) (rank : Nat) : Prop :=
  terminal.lane = lane ∧
  ∃ ledger : DigitCarryGhost c n,
    terminal.ledger = some ledger ∧
    ledger.inherited = none ∧
    ledger.uses ≠ [] ∧
    ∀ use : DigitUse c n, use ∈ ledger.uses →
      DigitAtomCohort A lane source anchor anchorTail
        use.operand rank

inductive DigitSerialTerminalRanks {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (lane : DigitLane) (source : Fin n)
    (anchor : DigitTerminal c n) (anchorTail : DigitStamp n) :
    Nat → List (DigitTerminal c n) → Prop where
  | empty (rank : Nat) :
      DigitSerialTerminalRanks A lane source anchor anchorTail
        rank []
  | next (rank : Nat) (terminal : DigitTerminal c n)
      (rest : List (DigitTerminal c n))
      (head : DigitTerminalRank A lane source anchor anchorTail
        terminal rank)
      (tail : DigitSerialTerminalRanks A lane source anchor anchorTail
        (rank + 1) rest) :
      DigitSerialTerminalRanks A lane source anchor anchorTail
        rank (terminal :: rest)

/-- The next five actual terminal receipts, with their checked
consecutive cohort designations. Their samples may precede 'after'. -/
def DigitFiveCohortCompletions {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (A : DigitAudit c n)
    (root : Fin n) (source target : Nat)
    (lane : DigitLane) (after : Nat)
    (last : DigitTerminal c n) : Prop :=
  ∃ (first second third fourth anchor : DigitTerminal c n)
    (anchorTail : DigitStamp n) (firstRank : Nat),
    DigitNextCompletion ring A root source target lane after first ∧
    DigitNextCompletion ring A root source target lane first.time second ∧
    DigitNextCompletion ring A root source target lane second.time third ∧
    DigitNextCompletion ring A root source target lane third.time fourth ∧
    DigitNextCompletion ring A root source target lane fourth.time last ∧
    DigitAnchor ring A root source target lane anchor anchorTail ∧
    anchor.time ≤ after ∧ 0 < firstRank ∧
    DigitSerialTerminalRanks A lane (digitSite ring root source)
      anchor anchorTail firstRank [first, second, third, fourth, last]


/-! First completions of the concrete finite receipt lists. -/

def DigitBoundaryAt {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n) (cut : Nat) : Prop :=
  ∃ (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n),
    DigitAt ring A cut S G ∧ DigitBoundaryReceipt ring root S

def DigitStructuralAt {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n) (cut : Nat) : Prop :=
  cut ≤ A.clock ∧
  ∀ (source target : Nat) (lane : DigitLane),
    DigitCompletePair ring root A.start source target →
    ∃ terminal : DigitTerminal c n,
      DigitFirstStrictCompletion ring A root source target lane 0 terminal ∧
      terminal.time ≤ cut

/-- Clockwise value dependencies, beginning with the first
base-writable segment even if it is truncated. Each later complete
target receives the next five coherent writer terminal receipts. -/
inductive DigitValueChain {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n) (structural first baseCut : Nat) :
    Nat → Nat → List (Nat × Nat) → Prop where
  | start :
      DigitValueChain ring root A structural first baseCut
        first baseCut [(first, baseCut)]
  | next {source previous : Nat} {cuts : List (Nat × Nat)}
      (h : DigitValueChain ring root A structural first baseCut
        source previous cuts)
      (target : Nat) (terminal : DigitTerminal c n)
      (hp : DigitCompletePair ring root A.start source target)
      (hc : DigitFiveCohortCompletions ring A root source target .writer
        (max structural previous) terminal) :
      DigitValueChain ring root A structural first baseCut
        target terminal.time ((target, terminal.time) :: cuts)

def DigitWritersCurrent {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (structural now : Nat) (cuts : List (Nat × Nat)) : Prop :=
  ∀ source target : Nat,
    DigitCompletePair ring root A.start source target →
    ∃ stable : Nat,
      (source, stable) ∈ cuts ∧
      DigitPairCurrent ring root A S G .writer
        source target (max structural stable) now

/-- Restart only the comparison observer's age reference. No
physical packet or carry register is reset at this cut. -/
def DigitComparisonReady {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n) (restart cut : Nat) : Prop :=
  restart ≤ cut ∧ cut ≤ A.clock ∧
  (∀ source target : Nat,
    DigitCompletePair ring root A.start source target →
    ∃ (terminal anchor : DigitTerminal c n) (anchorTail : DigitStamp n),
      DigitFirstStrictCompletion ring A root source target
        .comparison restart terminal ∧ terminal.time ≤ cut ∧
      DigitAnchor ring A root source target .comparison anchor anchorTail ∧
      anchor.time ≤ cut ∧
      DigitTerminalRanked A .comparison (digitSite ring root source)
        anchor anchorTail terminal) ∧
  ∃ (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n),
    DigitAt ring A cut S G ∧
    DigitBoundaryReceipt ring root S ∧
    DigitComparisonsCurrent ring root A S G restart cut

/-- Each dirty bit present at the observer-completion cut has an
actual later incident service that saw and cleared OLD dirty. -/
def DigitDirtyDrained {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (A : DigitAudit c n)
    (cut finish : Nat) : Prop :=
  cut ≤ finish ∧
  ∃ (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n),
    DigitAt ring A cut S G ∧
    ∀ i : Fin n, (S i).top.topDirty = true →
      ∃ f : DigitFrame c n,
        f ∈ A.frames ∧ cut < f.time ∧ f.time ≤ finish ∧
        ((f.edge = i ∧ f.receipt.dirtyClearedX = true) ∨
         (ring.rightNeighbor f.edge = i ∧
           f.receipt.dirtyClearedY = true))

def DigitFinalReady {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n)
    (structural restart comparisonCut : Nat)
    (cuts : List (Nat × Nat)) (finish : Nat) : Prop :=
  comparisonCut ≤ finish ∧ finish ≤ A.clock ∧
  DigitDirtyDrained ring A comparisonCut finish ∧
  ∃ (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n),
    DigitAt ring A finish S G ∧
    DigitBoundaryReceipt ring root S ∧
    DigitWritersCurrent ring root A S G structural finish cuts ∧
    DigitComparisonsCurrent ring root A S G restart finish ∧
    DigitAllPairsRanked ring root A S G finish ∧
    ∀ i : Fin n, (S i).top.topDirty = false

/-- A finite receipt interpreter for the proof's concrete boundary
forms and causal cuts. No digit-correctness or all-future-silence
predicate substitutes for a receipt. -/
def DigitOriginReceipts {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) : Prop :=
  ∃ (root : Fin n)
    (first stop boundary retired baseCut structural last restart
      comparisonCut : Nat)
    (cuts : List (Nat × Nat)),
    WFixedRoot ring root (fun i => (A.start i).word) ∧
    DigitFirstSegment ring root A.start first stop ∧
    DigitFirstCut (DigitBoundaryAt ring root A) boundary ∧
    DigitFirstCut
      (DigitBaseExtinct ring root A boundary) retired ∧
    DigitBaseValueCut ring root A boundary retired baseCut ∧
    DigitFirstCut (DigitStructuralAt ring root A) structural ∧
    DigitValueChain ring root A structural first baseCut
      last restart cuts ∧
    (∀ block : Nat,
      DigitCompleteBlock ring root A.start block →
      ∃ stable : Nat, (block, stable) ∈ cuts) ∧
    DigitFirstCut
      (DigitComparisonReady ring root A restart) comparisonCut ∧
    DigitFirstCut
      (DigitFinalReady ring root A structural restart comparisonCut cuts)
      A.clock ∧
    DigitAt ring A A.clock S A.current

def DigitOrigin {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) : Prop :=
  DigitSeedHistory ring S A ∧ DigitOriginReceipts ring S A

inductive DigitHistory {c : Compiled} {n : Nat}
    (ring : DirectedRing n) :
    (Fin n → ProjD c) → DigitAudit c n → Prop where
  | origin {S : Fin n → ProjD c} {A : DigitAudit c n}
      (h : DigitOrigin ring S A) :
      DigitHistory ring S A
  | next {S : Fin n → ProjD c} {A : DigitAudit c n}
      (h : DigitHistory ring S A) (e : Fin n) :
      DigitHistory ring (phiD ring S e)
        (digitAuditStep ring S A e)

def Ddel {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c) : Prop :=
  ∃ A : DigitAudit c n, DigitHistory ring S A

theorem Ddel_origin {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (h : DigitOrigin ring S A) :
    Ddel ring S :=
  ⟨A, DigitHistory.origin h⟩

theorem Ddel_phi_step {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c)
    (e : Fin n) (h : Ddel ring S) :
    Ddel ring (phiD ring S e) := by
  obtain ⟨A, hA⟩ := h
  exact ⟨digitAuditStep ring S A e, DigitHistory.next hA e⟩

theorem Ddel_real_noFire {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : Ddel ring (piD C)) :
    Ddel ring (piD ((protocol q).step ring C e)) := by
  rw [stepD_noFire hn ring C e hfire]
  exact Ddel_phi_step ring (piD C) e h


/-!
Block-A finite receipt ALPHABETS and generic edge-history interface.

The types below contain no absolute clocks or unbounded lists. The
actual owner-case interpreters and their acceptance-closure proofs are
NOT claimed complete here. The legacy ghost interpreters above are
preserved solely so existing clients continue to have their names.
This namespace is not substituted into Target until the complete
first-match slot/row interpreters are proved.
-/
namespace BlockA

/-- A fixed-capacity sequence. The declared alphabet has at most k
entries and its storage is indexed by Fin k. E.G13, E.G19, E.G24. -/
structure FiniteLedger (A : Type) (k : Nat) where
  count : Fin (k + 1)
  entries : Fin k → Option A

/-- All complete-record serializer colors in E.G15. -/
inductive SerializerTag where
  | empty
  | rootWait
  | rootDone
  | pending
  | seenInt
  | seenLeaf
  | childNew
  | childWait
  | childDone
  | returning
  deriving DecidableEq, Repr

structure SerializerColor (n : Nat) where
  tag : SerializerTag
  parent : Option (Fin n)
  deriving DecidableEq, Repr

/-- The finite worker-color cases of E.G13. -/
inductive WorkerTag (n t : Nat) where
  | empty
  | prefix (j : Fin (t + 1)) (z a : Bool)
  | target (site : Fin n) (busy : Bool)
  | back (site : Fin n) (j : Fin (t + 1))
  | sum (site : Fin n) (j : Fin (t + 1)) (z p a : Bool)
  | ready (site : Fin n)
  deriving DecidableEq, Repr

/-- The actual service row is distinct from a coincident old/new value. -/
inductive SerializerReceiptCase where
  | request
  | hardStart
  | challenge
  | observeInt
  | observeLeaf
  | admit
  | feedback
  | hardTerminal
  | frame
  deriving DecidableEq, Repr

inductive WorkerReceiptCase where
  | init
  | erase
  | prefixExit
  | prefixMove
  | prefixTerminal
  | prefixPublish
  | backwardsMove
  | backwardsInit
  | sumMove
  | sumPublish
  | advance
  | terminal
  | frame
  deriving DecidableEq, Repr

inductive WordPhase where
  | awaitRequest
  | validate
  | worker
  | done
  deriving DecidableEq, Repr

structure PrefixSample (n : Nat) where
  source : Fin n
  oldBit : Bool
  deriving DecidableEq, Repr

structure SumSample (n : Nat) where
  source : Fin n
  oldBit : Bool
  tap : Bool
  deriving DecidableEq, Repr

inductive PublicationReceipt where
  | absent
  | prefixZero
  | prefixEnd
  | recurrence
  deriving DecidableEq, Repr

/-- E.G14: both worker-kind and cursor have colors. The recurrence
read order is represented by bounded ledgers, not a Nat clock. -/
structure WordControl (n : Nat) (c : Compiled) where
  root : Fin n
  phase : WordPhase
  requested : Bool
  serializer : Fin n → SerializerColor n
  workerKind : Fin n → WorkerTag n c.t
  workerCursor : Fin n → WorkerTag n c.t
  prefixReads : FiniteLedger (PrefixSample n) c.t
  sumReads : FiniteLedger (SumSample n) c.t
  publications : Fin n → PublicationReceipt
  visibleReceipts : Fin n → Bool
  prefixMarkers : Fin n → Bool

/- The actual OLD row names recognized by the raw owner E.G21. -/

/-- The selected serializer case is read from OLD owner guards;
the W ticket machine must also check the colored link. -/
def serializerCase {c : Compiled} (x y : ProjW c) :
    SerializerReceiptCase :=
  let s := serW x y
  if s.row == "S0" then .request
  else if s.hard.hardS1 then .hardStart
  else if s.hard.hardAccept then .hardTerminal
  else if s.hard.hardChallenge then .challenge
  else if s.row == "S3" && x.ser.probe == .PENDING &&
      y.ser.phase == .C then .observeInt
  else if s.row == "S5" && x.ser.probe == .PENDING &&
      x.ser.phase == .C then .observeLeaf
  else if (s.row == "S2N" || s.row == "S2R") &&
      x.ser.out == .WAIT &&
      (y.ser.probe == .INTERNAL_OK || y.ser.probe == .LEAF_OK) then .admit
  else if s.row == "S2N" && x.ser.out == .DONE &&
      y.ser.phase == .F then .feedback
  else .frame

/-- This is the literal SI row classification; an idempotent P1/S1
publication is still a publication. E.G16. -/
def workerCase {c : Compiled} (x y : ProjW c) :
    WorkerReceiptCase :=
  let row := (workerW x y).row
  if row == "I0" then .init
  else if row == "I1" then .erase
  else if row == "P0" then .prefixExit
  else if row == "P1" then .prefixMove
  else if row == "P2" then .prefixTerminal
  else if row == "P3" then .prefixPublish
  else if row == "B0" then .backwardsMove
  else if row == "B1" then .backwardsInit
  else if row == "S0" then .sumMove
  else if row == "S1" then .sumPublish
  else if row == "A1" then .advance
  else if row == "A0" then .terminal
  else .frame

/-- E.G8 restricted to W. The event is a pair of actual OLD-owner
classifications, not an inferred difference of records. -/
def actualWordCases {c : Compiled} (x y : ProjW c) :
    SerializerReceiptCase × WorkerReceiptCase :=
  (serializerCase x y, workerCase x y)

inductive ReaderReceiptCase where
  | collision
  | move
  | terminal
  | resident
  | kickArm
  | kickLaunch
  deriving DecidableEq, Repr


/-- The six exhaustive raw-reader OLD owner cases (E.G21). -/
def readerCase {c : Compiled} (x y : ProjR c) :
    ReaderReceiptCase :=
  let row := (rawR x y).row
  if row == "R0a" then .collision
  else if row == "R0b" then .move
  else if row == "R0c" then .terminal
  else if row == "R1a" then .resident
  else if row == "R1b" then .kickArm
  else .kickLaunch

/-- E.G8 restricted to R; the rawReject event is not a coordinate
of ProjR. -/
def actualReaderCases {c : Compiled} (x y : ProjR c) :
    SerializerReceiptCase × WorkerReceiptCase ×
      ReaderReceiptCase × Bool :=
  (serializerCase x.word y.word,
   workerCase x.word y.word,
   readerCase x y,
   (rawR x y).reject)

structure ReaderSample (n : Nat) where
  source : Fin n
  oldBit : Bool
  oldMarker : Bool
  postLeader : Bool
  deriving DecidableEq, Repr

/-- E.G19: inherited names never turn into fresh names merely because
their numeric token fields happen to match a sample fold. -/
inductive RawTag (n t : Nat) where
  | empty
  | inherited (identity : Fin n)
  | fresh (identity : Fin n) (length : Fin (t + 1))
      (samples : FiniteLedger (ReaderSample n) t)

inductive ReaderPhase where
  | retire
  | done
  deriving DecidableEq, Repr

/-- E.G20: H is a finite name set; each physical token site has one tag. -/
structure ReaderControl (n : Nat) (c : Compiled) where
  phase : ReaderPhase
  tags : Fin n → RawTag n c.t
  inheritedNames : Fin n → Bool


/-- Append one OLD-site read without ever exceeding the finite
sample capacity. No absolute timestamp is stored. -/
def FiniteLedger.push {A : Type} {k : Nat}
    (old : FiniteLedger A k) (entry : A) : FiniteLedger A k :=
  if h : old.count.val < k then
    { count := ⟨old.count.val + 1, by omega⟩
      entries := fun i =>
        if i.val = old.count.val then some entry else old.entries i }
  else old

def RawTag.identity? {n t : Nat} : RawTag n t → Option (Fin n)
  | .empty => none
  | .inherited name => some name
  | .fresh name _ _ => some name

/-- True exactly when a named reader is present in a tag array. -/
def readerNameUsed {n t : Nat}
    (tags : Fin n → RawTag n t) (name : Fin n) : Bool :=
  (List.ofFn (fun i : Fin n => tags i)).any
    (fun tag => tag.identity? == some name)

/-- Least free reusable name, after physical erasures, E.G19. -/
def readerFirstUnused {n t : Nat}
    (tags : Fin n → RawTag n t) : Option (Fin n) :=
  (List.ofFn (fun i : Fin n => i)).find?
    (fun name => !readerNameUsed tags name)

/-- Every new sample is from the selected OLD responder and
POST-elimination leader, never from the proposed new token. -/
def readerSelectedSample {n : Nat} {c : Compiled}
    (site : Fin n) (x y : ProjR c) : ReaderSample n :=
  { source := site
    oldBit := y.word.u
    oldMarker := y.word.beta
    postLeader := (postW x.word y.word).eY.l }

/-- The exact R0b transfer of an already colored identity; a fresh
lineage extends its bounded ledger and an inherited one stays old. -/
def readerTransfer {n : Nat} {c : Compiled}
    (tag : RawTag n c.t) (read : ReaderSample n) : RawTag n c.t :=
  match tag with
  | .empty => .empty
  | .inherited name => .inherited name
  | .fresh name index samples =>
      let nextIndex :=
        if h : index.val < c.t then
          (⟨index.val + 1, by omega⟩ : Fin (c.t + 1))
        else index
      .fresh name nextIndex (samples.push read)

/-- Deterministic E.G21 tag motion. Name allocation tests the array
after the OLD deletions; no resident token gains a fresh tag solely
because its numerical accumulators match a possible sample. -/
def readerControlNext {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : ReaderControl n c)
    (p : Fin n → ProjR c)
    (e : Fin n) (_p' : Fin n → ProjR c) :
    ReaderControl n c :=
  let j := ring.rightNeighbor e
  let x := p e
  let y := p j
  let row := readerCase x y
  let removedX :=
    if row == .collision || row == .move || row == .terminal
    then RawTag.empty else h.tags e
  let removedY :=
    if row == .terminal then RawTag.empty else h.tags j
  let afterErasure :=
    fun i : Fin n =>
      if i = e then removedX
      else if i = j then removedY
      else h.tags i
  let moved :=
    if row == .move then
      readerTransfer (h.tags e) (readerSelectedSample j x y)
    else if row == .kickLaunch then
      match readerFirstUnused afterErasure with
      | none => RawTag.empty
      | some name =>
        if ht : 0 < c.t then
          let sample := readerSelectedSample j x y
          let ledger : FiniteLedger (ReaderSample n) c.t :=
            { count := ⟨0, by omega⟩
              entries := fun _ => none }
          RawTag.fresh name ⟨1, by omega⟩ (ledger.push sample)
        else RawTag.empty
    else removedY
  let tags :=
    fun i : Fin n =>
      if i = e then removedX
      else if i = j then moved
      else h.tags i
  let inheritedNames :=
    fun name : Fin n =>
      (List.ofFn (fun i : Fin n =>
        match tags i with
        | .inherited old => old == name
        | _ => false)).any (fun b => b)
  let stillInherited :=
    (List.ofFn (fun name : Fin n => inheritedNames name)).any
      (fun b => b)
  { phase := if h.phase == .done || !stillInherited
      then .done else .retire
    tags := tags
    inheritedNames := inheritedNames }

inductive DigitLane where
  | writer
  | comparison
  deriving DecidableEq, Repr

/-- Exactly one base, three writer, three comparison and one dirty
slot per site, total 8n, as in E.G24. -/
inductive DigitSlot where
  | base
  | writerOut
  | writerIn
  | writerCarry
  | comparisonOut
  | comparisonIn
  | comparisonCarry
  | dirty
  deriving DecidableEq, Repr

structure OriginMask where
  fragment : Bool
  base : Bool
  other : Bool
  deriving DecidableEq, Repr

def OriginMask.empty : OriginMask :=
  { fragment := false, base := false, other := false }

def OriginMask.union (a b : OriginMask) : OriginMask :=
  { fragment := a.fragment || b.fragment
    base := a.base || b.base
    other := a.other || b.other }

def radixWidth (c : Compiled) : Nat := 2 ^ c.t - 1

def namePool (n : Nat) (c : Compiled) : Nat :=
  16 * n * (radixWidth c + 4) + 16

/-- All bounded operands of an actual carry consume, E.G24. -/
structure DigitOperand (n : Nat) (c : Compiled) where
  identity : Fin (namePool n c)
  position : Fin (radixWidth c)
  oldDigit : Fin c.topA
  afterCut : Fin (n + 2) → Bool

/-- E.G24: absence of a sample is represented by none, not digit zero.
The order ledger is bounded by the radix width. -/
inductive DigitStamp (n : Nat) (c : Compiled) where
  | none
  | invalid
  | live
      (origins : OriginMask)
      (identity : Option (Fin (namePool n c)))
      (cohort : Option (Fin (namePool n c)))
      (sourcePosition : Option (Fin (radixWidth c)))
      (oldDigit : Option (Fin c.topA))
      (afterCut : Fin (n + 2) → Bool)
      (operands : FiniteLedger (DigitOperand n c) (radixWidth c))

/-- The seven first-match stamp actions of E.G27–E.G28. -/
inductive SlotAction where
  | frame
  | erase
  | freshUnread
  | sample
  | copy
  | join
  | rootSeed
  deriving DecidableEq, Repr

/-- Named physical categories in the exhaustive E.G29 census. -/
inductive DigitReceiptCase where
  | baseRootEntry
  | baseSeekOrZero
  | outputUnread
  | outputMoveOrExport
  | outputEmptyBorder
  | inputMoveOrSettle
  | inputTailOrFront
  | carryLaunch
  | carryAdvance
  | carryRetireOrAbort
  | leaderSink
  | dirtyGate
  | frame
  deriving DecidableEq, Repr

/-- E.G25: order and group identity of genuine border exports. -/
structure ExportLedger (n : Nat) (c : Compiled) where
  cohort : Option (Fin (namePool n c))
  count : Fin (radixWidth c + 1)
  exports : FiniteLedger
    (Fin (radixWidth c) × Fin (namePool n c)) (radixWidth c)

inductive DigitPhase where
  | boundary
  | structure
  | base
  | wave
  | comparison
  | drain
  | done
  deriving DecidableEq, Repr

/-- E.G26: chronological cohort order, structural receipts, two
independent cover columns, currentness and first-hit phase are finite. -/
structure DigitControl (n : Nat) (c : Compiled) where
  stamps : Fin n → DigitSlot → DigitStamp n c
  exports : Fin n → DigitLane → ExportLedger n c
  liveCohortOrder : FiniteLedger
    (Fin (namePool n c)) (namePool n c)
  strict : Fin n → DigitLane → Bool
  baseCover : Fin 2 → Fin n → Bool
  baseCursor : Fin (n + 1)
  stableIndex : Fin (n + 1)
  stableReceipts : Fin n → Bool
  waveCount : Fin n → Fin 6
  comparisonCurrent : Fin n → Bool
  cutBits : Fin (n + 2) → Bool
  phase : DigitPhase

/-- All three decorations include an entire projected-state shadow.
A failed decoration is absorbing (E.G7). -/
inductive Decoration (P H : Type) where
  | failed
  | live (shadow : P) (control : H)

/-- The general deterministic E.G7 update. T is the case-specific
finite control update; it must read the OLD projected pair and its
winning assignments, not compare field values to infer a write. -/
noncomputable def update {n : Nat} {A H : Type}
    (ring : DirectedRing n)
    (phi : (Fin n → A) → Fin n → Fin n → A)
    (T : H → (Fin n → A) → Fin n → (Fin n → A) → H)
    (γ : Decoration (Fin n → A) H)
    (old : A × A) (e : Fin n)
    (successor : Fin n → A) :
    Decoration (Fin n → A) H := by
  classical
  exact match γ with
    | .failed => .failed
    | .live shadow h =>
        if old = (shadow e, shadow (ring.rightNeighbor e)) ∧
            successor = phi shadow e then
          .live successor (T h shadow e successor)
        else .failed

theorem update_failed {n : Nat} {A H : Type}
    (ring : DirectedRing n)
    (phi : (Fin n → A) → Fin n → Fin n → A)
    (T : H → (Fin n → A) → Fin n → (Fin n → A) → H)
    (old : A × A) (e : Fin n) (successor : Fin n → A) :
    update ring phi T (Decoration.failed : Decoration (Fin n → A) H)
        old e successor = .failed := rfl

/-- E.G9: an empty word is a run; appending a selected edge uses
the old pair, the unique projected successor, and E.G7. -/
inductive Run {n : Nat} {A H : Type}
    (ring : DirectedRing n)
    (phi : (Fin n → A) → Fin n → Fin n → A)
    (T : H → (Fin n → A) → Fin n → (Fin n → A) → H)
    (ρ : Fin n → A)
    (γ₀ : Decoration (Fin n → A) H) :
    List (Fin n) → (Fin n → A) →
      Decoration (Fin n → A) H → Prop where
  | empty : Run ring phi T ρ γ₀ [] ρ γ₀
  | next {w p γ} (h : Run ring phi T ρ γ₀ w p γ)
      (e : Fin n) :
      Run ring phi T ρ γ₀ (w ++ [e]) (phi p e)
        (update ring phi T γ
          (p e, p (ring.rightNeighbor e)) e (phi p e))

/-- Accepted generated histories have BOTH an initial and terminal
predicate; unlike the old prefix-closed ghost, this does not admit
a post-acceptance state without checking its receipt. E.G18/23/36. -/
def Generated {n : Nat} {A H : Type}
    (ring : DirectedRing n)
    (phi : (Fin n → A) → Fin n → Fin n → A)
    (T : H → (Fin n → A) → Fin n → (Fin n → A) → H)
    (J : (Fin n → A) → Decoration (Fin n → A) H → Prop)
    (Accept : (Fin n → A) →
      Decoration (Fin n → A) H → Prop)
    (p : Fin n → A) : Prop :=
  ∃ (ρ : Fin n → A) (γ₀ : Decoration (Fin n → A) H)
    (w : List (Fin n)) (γ : Decoration (Fin n → A) H),
    J ρ γ₀ ∧ Run ring phi T ρ γ₀ w p γ ∧ Accept p γ

/-- Exact continuation theorem, conditional on the missing acceptance
invariant for the concrete first-match case interpreter. -/
theorem generated_step {n : Nat} {A H : Type}
    (ring : DirectedRing n)
    (phi : (Fin n → A) → Fin n → Fin n → A)
    (T : H → (Fin n → A) → Fin n → (Fin n → A) → H)
    (J : (Fin n → A) → Decoration (Fin n → A) H → Prop)
    (Accept : (Fin n → A) →
      Decoration (Fin n → A) H → Prop)
    (hclosed : ∀ p γ e, Accept p γ →
      Accept (phi p e)
        (update ring phi T γ
          (p e, p (ring.rightNeighbor e)) e (phi p e)))
    (p : Fin n → A) (e : Fin n)
    (h : Generated ring phi T J Accept p) :
    Generated ring phi T J Accept (phi p e) := by
  obtain ⟨ρ, γ₀, w, γ, hj, hr, ha⟩ := h
  exact ⟨ρ, γ₀, w ++ [e],
    update ring phi T γ (p e, p (ring.rightNeighbor e))
      e (phi p e),
    hj, Run.next hr e, hclosed p γ e ha⟩


/-- The descending E.G10 elimination is a finite recursion on the
chosen state-bound. Instantiation must prove that this bound is the
actual finite-state cardinality. -/
def safeStage {n : Nat} {P : Type}
    (next : P → Fin n → P) (bad : P → Fin n → Prop) :
    Nat → P → Prop
  | 0, _ => True
  | k + 1, p =>
      safeStage next bad k p ∧
        (∀ e : Fin n,
          ¬ bad p e ∧ safeStage next bad k (next p e))

theorem safeStage_descends {n : Nat} {P : Type}
    (next : P → Fin n → P) (bad : P → Fin n → Prop)
    (k : Nat) (p : P)
    (h : safeStage next bad (k + 1) p) :
    safeStage next bad k p :=
  h.1

/-- E.G11, once the finite fixed-point bound has stabilized. -/
theorem safeStage_closed_of_fixed {n : Nat} {P : Type}
    (next : P → Fin n → P) (bad : P → Fin n → Prop)
    (k : Nat)
    (hfixed : ∀ p, safeStage next bad k p →
        safeStage next bad (k + 1) p)
    (p : P) (h : safeStage next bad k p)
    (e : Fin n) :
    ¬ bad p e ∧ safeStage next bad k (next p e) := by
  exact (hfixed p h).2 e

/-- E.G17 with the per-row recurrence proof and the
finite Q_W test supplied as parameters. The exact concrete recurrence
row interpreter is not yet instantiated. -/
def acceptsWord {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (validated : WordControl n c → Prop)
    (safeWord : (Fin n → ProjW c) → Prop)
    (p : Fin n → ProjW c)
    (γ : Decoration (Fin n → ProjW c) (WordControl n c)) : Prop :=
  match γ with
  | .failed => False
  | .live shadow h =>
      shadow = p ∧ h.phase = .done ∧ validated h ∧
        (∀ k : Fin n, 0 < k.val →
          let site := PPL.shiftRight ring h.root k.val
          if k.val < c.t then
            h.publications site = .prefixZero ∧
              h.prefixMarkers site = true ∧
              h.visibleReceipts site = true
          else if k.val = c.t then
            h.publications site = .prefixEnd ∧
              h.visibleReceipts site = true
          else h.publications site = .recurrence ∧
              h.visibleReceipts site = true) ∧
        safeWord p

/-- E.G22 with exact old/new name extinction and fresh read-ledger
shape; foldValid denotes the missing literal five-accumulator proof. -/
def acceptsReader {n : Nat} {c : Compiled}
    (foldValid : Fin n → Option (RawTok c.t) →
      Fin (c.t + 1) → FiniteLedger (ReaderSample n) c.t → Prop)
    (safeReader : (Fin n → ProjR c) → Prop)
    (p : Fin n → ProjR c)
    (γ : Decoration (Fin n → ProjR c) (ReaderControl n c)) : Prop :=
  match γ with
  | .failed => False
  | .live shadow h =>
      shadow = p ∧ h.phase = .done ∧
        (∀ name : Fin n, h.inheritedNames name = false) ∧
        (∀ i : Fin n, (p i).rawTok.isSome = true →
          ∃ (name : Fin n) (index : Fin (c.t + 1))
              (samples : FiniteLedger (ReaderSample n) c.t),
            h.tags i = .fresh name index samples ∧
              samples.count = index ∧
              foldValid i (p i).rawTok index samples) ∧
        safeReader p

/-- Superseded stronger D diagnostics from the pre-audit draft:
StructSafe and Inert are NOT premises of E.G35/E.G36 membership.
This predicate is deliberately renamed to prevent accidental use as
accepted weak-D membership. See AcceptedReceipts.BarredDigitClass. -/
def acceptsDigitAuxDiagnostic {n : Nat} {c : Compiled}
    (isPair : Fin n → DigitLane → Prop)
    (isBlock : Fin n → Prop)
    (isComparison : Fin n → Prop)
    (structSafe : (Fin n → ProjD c) → DigitControl n c → Prop)
    (inert : (Fin n → ProjD c) → DigitControl n c → Prop)
    (valueGood : (Fin n → ProjD c) → DigitControl n c → Prop)
    (safeDigit : (Fin n → ProjD c) → Prop)
    (p : Fin n → ProjD c)
    (γ : Decoration (Fin n → ProjD c) (DigitControl n c)) : Prop :=
  match γ with
  | .failed => False
  | .live shadow h =>
      shadow = p ∧ h.phase = .done ∧
        (∀ i lane, isPair i lane → h.strict i lane = true) ∧
        (∀ i, isBlock i → h.stableReceipts i = true) ∧
        (∀ i, isComparison i → h.comparisonCurrent i = true) ∧
        structSafe p h ∧ inert p h ∧ valueGood p h ∧
        (∀ i : Fin n, (p i).top.topDirty = false) ∧ safeDigit p

/-- Initial recurrence-origin states have a genuine protected
stationary singleton, no colored provenance and a zero requested bit.
The OLD physical serializer/worker records remain unrestricted. -/
def initializesWord {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c)
    (γ : Decoration (Fin n → ProjW c) (WordControl n c)) : Prop :=
  ∃ (root : Fin n) (h : WordControl n c),
    γ = .live p h ∧ h.root = root ∧
      WFixedRoot ring root p ∧
      2 ≤ c.t ∧ c.t + (2 ^ c.t - 1) ≤ n ∧
      h.phase = .awaitRequest ∧ h.requested = false ∧
      (∀ i, (h.serializer i).tag = .empty ∧
        (h.serializer i).parent = none ∧
        h.workerKind i = .empty ∧
        h.workerCursor i = .empty ∧
        h.publications i = .absent ∧
        h.visibleReceipts i = false ∧
        h.prefixMarkers i = false) ∧
      h.prefixReads.count.val = 0 ∧
      h.sumReads.count.val = 0

/-- Initial reader token sites are stamped inherited, never promoted
by numeric resemblance. The recurrence endpoint test is supplied
separately because it belongs to the W accepted history. -/
def initializesReader {n : Nat} {c : Compiled}
    (recurrenceOrigin : (Fin n → ProjW c) → Prop)
    (p : Fin n → ProjR c)
    (γ : Decoration (Fin n → ProjR c) (ReaderControl n c)) : Prop :=
  recurrenceOrigin (fun i => (p i).word) ∧
    ∃ h : ReaderControl n c,
      γ = .live p h ∧ h.phase = .retire ∧
      (∀ i : Fin n,
        if (p i).rawTok.isSome = true then
          h.tags i = .inherited i ∧ h.inheritedNames i = true
        else h.tags i = .empty ∧ h.inheritedNames i = false)

/-- The D initializer deliberately carries a supplied exact slot
classification, since one physical input may coexist with an OLD
carry; both must have their own inherited stamps. -/
def initializesDigit {n : Nat} {c : Compiled}
    (recurrenceOrigin : (Fin n → ProjW c) → Prop)
    (classifyInherited : (Fin n → ProjD c) →
      DigitControl n c → Prop)
    (p : Fin n → ProjD c)
    (γ : Decoration (Fin n → ProjD c) (DigitControl n c)) : Prop :=
  recurrenceOrigin (fun i => (p i).word) ∧
    ∃ h : DigitControl n c,
      γ = .live p h ∧
      classifyInherited p h ∧
      h.phase = .boundary ∧
      (∀ i lane, h.strict i lane = false) ∧
      (∀ i, h.stableReceipts i = false ∧
        h.comparisonCurrent i = false ∧
        h.waveCount i = (0 : Fin 6) ∧
        h.baseCover 0 i = false ∧ h.baseCover 1 i = false) ∧
      (∀ bit : Fin (n + 2), h.cutBits bit = false)


/-! E.G13--18: phase-local, bounded W provenance. The OLD
serializer and worker cases are selected by the actual owners above.
No arbitrary initial private byte is assigned a provenance color. -/

def wordEmptyLedger {A : Type} {k : Nat} : FiniteLedger A k :=
  { count := 0, entries := fun _ => none }

def wordPut {n : Nat} {A : Type} (f : Fin n → A)
    (i : Fin n) (a : A) : Fin n → A :=
  fun j => if j = i then a else f j

def wordColor {n : Nat} (tag : SerializerTag)
    (parent : Option (Fin n)) : SerializerColor n :=
  { tag := tag, parent := parent }

def wordClear {n : Nat} {c : Compiled}
    (h : WordControl n c) (request : Bool) : WordControl n c :=
  { h with
    phase := .awaitRequest
    requested := request
    serializer := fun _ => wordColor .empty none
    workerKind := fun _ => .empty
    workerCursor := fun _ => .empty
    prefixReads := wordEmptyLedger
    sumReads := wordEmptyLedger
    publications := fun _ => .absent
    visibleReceipts := fun _ => false
    prefixMarkers := fun _ => false }

/-- Request is evidence of an actual S0 OLD-root assignment, not
of the REQUESTED byte occurring in an arbitrary initial record. -/
def wordRequestNext {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) : Bool :=
  let j := ring.rightNeighbor e
  let x := p e
  let y := p j
  let s := serW x y
  if j = h.root ∧ s.row = "S0" then true
  else if e = h.root ∧ x.ser.cert = .REQUESTED ∧
      s.x.cert ≠ .REQUESTED then false
  else h.requested

/-- A requested zero-lease start is the only possible hard-epoch
origin. A positive-lease S1 is not a hard restart. -/
def wordIsHardStart {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) : Prop :=
  let x := p e
  let y := p (ring.rightNeighbor e)
  e = h.root ∧ h.requested = true ∧
    x.siLease.val = 0 ∧
    serializerCase x y = .hardStart ∧
    (serW x y).row = "S1" ∧
    workerCase x y = .erase

instance wordIsHardStart_decidable {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) :
    Decidable (wordIsHardStart ring h p e) := by
  dsimp only [wordIsHardStart]
  infer_instance

def wordHardLaunch {n : Nat} {c : Compiled}
    (h : WordControl n c) (e j : Fin n) : WordControl n c :=
  { (wordClear h false) with
    phase := .validate
    serializer :=
      wordPut
        (wordPut (fun _ => wordColor .empty none)
          e (wordColor .rootWait none))
        j (wordColor .pending (some e)) }

/-- All follower records are from the current colored round-trip,
including their actual clockwise parent links. -/
def wordAllReturned {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c) : Prop :=
  ∀ k : Fin n, 0 < k.val →
    let i := PPL.shiftRight ring h.root k.val
    (h.serializer i).tag = .returning ∧
      (h.serializer i).parent =
        some (PPL.shiftRight ring h.root (k.val - 1))

/-- The validated handoff has no uncolored effectful worker outside
the two endpoints of the selected canonical I0 service. -/
def wordOtherWorkersFree {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) : Prop :=
  ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
    freeSI (p i).si = true

instance wordAllReturned_decidable {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c) :
    Decidable (wordAllReturned ring h) := by
  dsimp only [wordAllReturned]
  infer_instance

instance wordOtherWorkersFree_decidable {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) :
    Decidable (wordOtherWorkersFree ring h p e) := by
  dsimp only [wordOtherWorkersFree]
  infer_instance

/-- Canonical worker launch takes place in the same OLD-selected
hard terminal, after the complete validation and scrub checks. -/
def wordWorkerLaunch {n : Nat} {c : Compiled}
    (h : WordControl n c) : WordControl n c :=
  { (wordClear h false) with
    phase := .worker
    workerKind := fun i =>
      if i = h.root then .prefix 0 false true else .empty }

/-- E.G15 colored serializer interpreter. Unexpected overwrites of
active tags cancel only the attempted history, not the physical edge.
The two sites are the OLD initiator and OLD responder. -/
def wordValidateNext {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) : WordControl n c :=
  let j := ring.rightNeighbor e
  let x := p e
  let y := p j
  let s := serW x y
  let si := workerW x y
  let oldX := h.serializer e
  let oldY := h.serializer j
  let cancel := wordClear h request
  match serializerCase x y with
  | .challenge =>
      if (oldX.tag = .rootWait ∨ oldX.tag = .childNew ∨
          oldX.tag = .childWait) ∧
          s.x.out = .WAIT ∧ s.y.probe = .PENDING ∧
          si.row = "I1" then
        { h with
          requested := request
          serializer :=
            wordPut (wordPut h.serializer e
              (wordColor (if e = h.root then .rootWait else .childWait)
                oldX.parent))
              j (wordColor .pending (some e)) }
      else cancel
  | .observeInt =>
      if oldX.tag = .pending ∧ x.ser.probe = .PENDING ∧
          s.x.probe = .INTERNAL_OK then
        { h with
          requested := request
          serializer := wordPut h.serializer e
            (wordColor .seenInt oldX.parent) }
      else cancel
  | .observeLeaf =>
      if j = h.root ∧ oldX.tag = .pending ∧
          x.ser.probe = .PENDING ∧ s.x.probe = .LEAF_OK then
        { h with
          requested := request
          serializer := wordPut h.serializer e
            (wordColor .seenLeaf oldX.parent) }
      else cancel
  | .admit =>
      if oldX.tag =
           (if e = h.root then .rootWait else .childWait) ∧
          oldY.parent = some e ∧
          ((oldY.tag = .seenInt ∧ s.y.phase = .B) ∨
           (oldY.tag = .seenLeaf ∧ s.y.phase = .F)) ∧
          s.x.out = .DONE then
        { h with
          requested := request
          serializer :=
            wordPut (wordPut h.serializer e
              (wordColor
                (if e = h.root then .rootDone else .childDone)
                oldX.parent))
              j (wordColor
                (if oldY.tag = .seenInt then .childNew else .returning)
                (some e)) }
      else cancel
  | .feedback =>
      if e ≠ h.root ∧ oldX.tag = .childDone ∧
          oldY.tag = .returning ∧ oldY.parent = some e ∧
          s.x.phase = .F then
        { h with
          requested := request
          serializer := wordPut h.serializer e
            (wordColor .returning oldX.parent) }
      else cancel
  | .hardTerminal =>
      if e = h.root ∧ oldX.tag = .rootDone ∧
          oldY.tag = .returning ∧ oldY.parent = some e ∧
          wordAllReturned ring h ∧
          wordOtherWorkersFree ring h p e ∧
          s.hard.hardAccept = true ∧
          si.row = "I0" ∧ si.x = launchPrefix c.t ∧
          freeSI si.y = true then
        wordWorkerLaunch h
      else cancel
  | _ =>
      if (s.x ≠ x.ser ∧ oldX.tag ≠ .empty) ∨
          (s.y ≠ y.ser ∧ oldY.tag ≠ .empty) then cancel
      else { h with requested := request }

/-- A receipt for each follower is required at an actual A0.
P1 below t is a zero-marker receipt, P3 at t is the initial
window receipt, and S1 thereafter is a recurrence receipt. -/
def wordAllPublished {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c) : Prop :=
  ∀ k : Fin n, 0 < k.val →
    let i := PPL.shiftRight ring h.root k.val
    if k.val < c.t then
      h.publications i = .prefixZero ∧
      h.prefixMarkers i = true ∧
      h.visibleReceipts i = true
    else if k.val = c.t then
      h.publications i = .prefixEnd ∧
      h.visibleReceipts i = true
    else h.publications i = .recurrence ∧
      h.visibleReceipts i = true

instance wordAllPublished_decidable {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c) :
    Decidable (wordAllPublished ring h) := by
  dsimp only [wordAllPublished]
  infer_instance

/-- Check the OR, parity and trailing AND against the OLD source
bit, with the first source excluded from the trailing AND. -/
def wordFold {c : Compiled} (j : Fin (c.t + 1))
    (z parity trailing source : Bool) : Bool × Bool × Bool :=
  (z || source,
   Bool.xor parity (c.taps j.val && source),
   if j.val = 0 then true else trailing && source)

/-- E.G16 worker interpreter. Every read ledger stores the actual
OLD source bit and tap; tag equality is not inferred from a
coincident post-service value. Soft serializer S1/S6/S2 events
are deliberately not used as worker-cancellation conditions. -/
def wordWorkerNext {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) : WordControl n c :=
  let j := ring.rightNeighbor e
  let x := p e
  let y := p j
  let s := serW x y
  let si := workerW x y
  let cancel := wordClear h request
  let keep := { h with requested := request }
  match workerCase x y with
  | .init => cancel
  | .erase =>
      if ((s.hard.hardLeft = true ∧
            (h.workerKind e ≠ .empty ∨ h.workerCursor e ≠ .empty)) ∨
          (s.hard.hardRight = true ∧
            (h.workerKind j ≠ .empty ∨ h.workerCursor j ≠ .empty))) then
        cancel
      else keep
  | .prefixMove =>
      match h.workerKind e with
      | .prefix idx z a =>
          if x.si.kind = .PREFIX ∧ x.si.busy = false ∧
              x.si.cur = .NONE ∧ x.si.j = idx ∧
              x.si.z = z ∧ x.si.a = a ∧
              h.prefixReads.count.val = idx.val ∧
              h.workerKind j = .empty ∧
              h.workerCursor j = .empty ∧
              si.y.kind = .PREFIX ∧
              si.y.j.val = idx.val + 1 ∧
              si.y.z = (z || y.u) ∧
              si.y.a = (a && y.u) ∧
              (idx.val + 1 < c.t → si.betaY = false) then
            let kinds := wordPut (wordPut h.workerKind e .empty)
              j (.prefix si.y.j si.y.z si.y.a)
            let reads := h.prefixReads.push
              { source := j, oldBit := y.u }
            let base := { keep with
              workerKind := kinds
              prefixReads := reads }
            if idx.val + 1 < c.t then
              { base with
                publications := wordPut base.publications j .prefixZero
                visibleReceipts := wordPut base.visibleReceipts j true
                prefixMarkers := wordPut base.prefixMarkers j true }
            else base
          else cancel
      | _ => cancel
  | .prefixPublish =>
      match h.workerKind e with
      | .prefix idx z a =>
          if idx.val = c.t ∧ x.si.kind = .PREFIX ∧
              x.si.cur = .NONE ∧ x.si.busy = false ∧
              x.si.j = idx ∧ x.si.z = z ∧ x.si.a = a ∧
              h.prefixReads.count.val = c.t ∧
              h.workerKind j = .empty ∧
              h.workerCursor j = .empty ∧
              si.uX = (if z = false then true else x.u) ∧
              si.betaX = a ∧
              si.y.kind = .ROOT ∧ si.y.busy = true ∧
              si.y.cur = .BACK ∧ si.y.j.val = c.t then
            { keep with
              workerKind :=
                wordPut (wordPut h.workerKind e .empty)
                  j (.target j true)
              workerCursor :=
                wordPut h.workerCursor j (.back j si.y.j)
              publications := wordPut h.publications e .prefixEnd
              visibleReceipts := wordPut h.visibleReceipts e true
              sumReads := wordEmptyLedger }
          else cancel
      | _ => cancel
  | .backwardsMove =>
      match h.workerCursor j with
      | .back target idx =>
          if h.workerKind target = .target target true ∧
              h.workerCursor e = .empty ∧
              y.si.cur = .BACK ∧ y.si.j = idx ∧
              si.x.cur = .BACK ∧ si.x.j.val + 1 = idx.val then
            { keep with
              workerCursor :=
                wordPut (wordPut h.workerCursor j .empty)
                  e (.back target si.x.j) }
          else cancel
      | _ => cancel
  | .backwardsInit =>
      match h.workerCursor j with
      | .back target idx =>
          if h.workerKind target = .target target true ∧
              h.workerCursor e = .empty ∧
              idx.val = 1 ∧ y.si.cur = .BACK ∧
              y.si.j = idx ∧ si.x.cur = .SUM ∧
              si.x.j.val = 0 then
            { keep with
              workerCursor :=
                wordPut (wordPut h.workerCursor j .empty)
                  e (.sum target si.x.j false false true)
              sumReads := wordEmptyLedger }
          else cancel
      | _ => cancel
  | .sumMove =>
      match h.workerCursor e with
      | .sum target idx z parity trailing =>
          let f := wordFold idx z parity trailing x.u
          if x.si.kind = .OFF ∧ x.si.cur = .SUM ∧
              x.si.j = idx ∧ x.si.z = z ∧
              x.si.p = parity ∧ x.si.a = trailing ∧
              h.workerKind target = .target target true ∧
              h.workerCursor j = .empty ∧
              h.sumReads.count.val = idx.val ∧
              si.y.cur = .SUM ∧
              si.y.j.val = idx.val + 1 ∧
              si.y.z = f.1 ∧ si.y.p = f.2.1 ∧
              si.y.a = f.2.2 then
            { keep with
              workerCursor :=
                wordPut (wordPut h.workerCursor e .empty)
                  j (.sum target si.y.j si.y.z si.y.p si.y.a)
              sumReads := h.sumReads.push
                { source := e, oldBit := x.u,
                  tap := c.taps idx.val } }
          else cancel
      | _ => cancel
  | .sumPublish =>
      match h.workerCursor e with
      | .sum target idx z parity trailing =>
          let f := wordFold idx z parity trailing x.u
          let bit := if f.1 then f.2.1 else true
          if target = j ∧
              h.workerKind j = .target j true ∧
              x.si.kind = .OFF ∧ x.si.cur = .SUM ∧
              x.si.j = idx ∧ x.si.z = z ∧
              x.si.p = parity ∧ x.si.a = trailing ∧
              h.sumReads.count.val = idx.val ∧
              idx.val + 1 = c.t ∧
              y.si.kind = .ROOT ∧ y.si.busy = true ∧
              si.uY = bit ∧ si.betaY = (f.2.2 && bit) ∧
              si.y.kind = .ROOT ∧ si.y.busy = false ∧
              si.y.cur = .NONE then
            { keep with
              workerKind := wordPut h.workerKind j (.ready j)
              workerCursor := wordPut h.workerCursor e .empty
              sumReads := h.sumReads.push
                { source := e, oldBit := x.u,
                  tap := c.taps idx.val }
              publications := wordPut h.publications j .recurrence
              visibleReceipts := wordPut h.visibleReceipts j true }
          else cancel
      | _ => cancel
  | .advance =>
      if h.workerKind e = .ready e ∧
          h.workerKind j = .empty ∧
          h.workerCursor j = .empty ∧
          x.si.kind = .ROOT ∧ x.si.busy = false ∧
          x.si.cur = .NONE ∧ si.y.kind = .ROOT ∧
          si.y.busy = true ∧ si.y.cur = .BACK ∧
          si.y.j.val = c.t then
        { keep with
          workerKind :=
            wordPut (wordPut h.workerKind e .empty)
              j (.target j true)
          workerCursor := wordPut h.workerCursor j (.back j si.y.j)
          sumReads := wordEmptyLedger }
      else cancel
  | .terminal =>
      if h.workerKind e = .ready e ∧
          j = h.root ∧
          x.si.kind = .ROOT ∧ x.si.busy = false ∧
          x.si.cur = .NONE ∧
          wordAllPublished ring h then
        { keep with phase := .done }
      else cancel
  | .prefixExit => cancel
  | .prefixTerminal => cancel
  | .frame => keep

/-- Complete E.G14 dispatch. The terminal phase freezes all
provenance while the projected shadow continues to evolve by phiW.
The successor parameter is checked separately by BlockA.update. -/
def wordT {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (_successor : Fin n → ProjW c) : WordControl n c :=
  if h.phase = .done then h
  else
    let request := wordRequestNext ring h p e
    if wordIsHardStart ring h p e then
      wordHardLaunch h e (ring.rightNeighbor e)
    else
      match h.phase with
      | .awaitRequest => wordClear h request
      | .validate => wordValidateNext ring h p e request
      | .worker => wordWorkerNext ring h p e request
      | .done => h

/-- At acceptance the finite receipt flags have consistent types.
These are supplementary to the complete follower test in
acceptsWord; they are not inferred from an OLD initial pattern. -/
def wordValidated {n : Nat} {c : Compiled}
    (_ring : DirectedRing n) (h : WordControl n c) : Prop :=
  (∀ i, h.publications i = .prefixZero →
    h.prefixMarkers i = true ∧ h.visibleReceipts i = true) ∧
  (∀ i, (h.publications i = .prefixEnd ∨
    h.publications i = .recurrence) →
    h.visibleReceipts i = true)

/-- After an accepted A0 all receipt data is immutable, even if
subsequent positive-lease serializer cycles occur. -/
theorem wordT_done {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (next : Fin n → ProjW c) (hd : h.phase = .done) :
    wordT ring h p e next = h := by
  simp [wordT, hd]

end BlockA

/-! The following layer is the first transcription of audited E.G6-12
and the WEAK E.G35-36. The existing LEGACY W/R/D proof witnesses
remain above for comparison and are not silently identified with the
accepted finite receipt automata. -/

namespace AcceptedReceipts

def wordProjection {c : Compiled} {n : Nat}
    (p : Fin n → ProjD c) : Fin n → ProjW c :=
  fun i => (p i).word

def wordProjectionR {c : Compiled} {n : Nat}
    (p : Fin n → ProjR c) : Fin n → ProjW c :=
  fun i => (p i).word

def digitVisible {c : Compiled} {n : Nat}
    (p : Fin n → ProjD c) (i : Fin n) :
      Bool × Bool × Fin c.topA :=
  ((p i).word.u, (p i).word.beta, (p i).top.d)

def wordVisible {c : Compiled} {n : Nat}
    (p : Fin n → ProjW c) (i : Fin n) : Bool × Bool :=
  ((p i).u, (p i).beta)

/-- E.G12 W: visible u/beta changes are bad even when no owner
report event is emitted. -/
def badWord {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (e : Fin n) : Prop :=
  ∃ i : Fin n, wordVisible (phiW ring p e) i ≠ wordVisible p i

/-- E.G12 R: read the ACTUAL old-raw owner output, not a field
difference or a terminal-looking token. -/
def badReader {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjR c)
    (e : Fin n) : Prop :=
  (rawR (p e) (p (ring.rightNeighbor e))).reject = true

/-- E.G12 D: old TOP owner report OR change of u/beta/d. An
idempotent digit assignment is NOT a change, as required for Q_D. -/
def badDigit {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjD c)
    (e : Fin n) : Prop :=
  (∃ i : Fin n,
    digitVisible (phiD ring p e) i ≠ digitVisible p i) ∨
  (topD (p e) (p (ring.rightNeighbor e))).topReject = true

/-! A semantic intersection of the E.G10 finite approximants.
When P is finite it equals Z_|P|; the cardinality stabilization
theorem remains an independent finite-state Lean obligation. -/

def SafeAll {n : Nat} {P : Type}
    (next : P → Fin n → P) (bad : P → Fin n → Prop)
    (p : P) : Prop :=
  ∀ k : Nat, BlockA.safeStage next bad k p

theorem safe_inclusion_at_stage
    {n : Nat} {P : Type}
    (next : P → Fin n → P) (bad : P → Fin n → Prop)
    (I : P → Prop)
    (hI : ∀ p, I p → ∀ e : Fin n, ¬ bad p e ∧ I (next p e)) :
    ∀ k : Nat, ∀ p : P, I p →
      BlockA.safeStage next bad k p := by
  intro k
  induction k with
  | zero =>
      intro p hp
      trivial
  | succ k ih =>
      intro p hp
      refine ⟨ih p hp, ?_⟩
      intro e
      obtain ⟨hno, hnext⟩ := hI p hp e
      exact ⟨hno, ih (next p e) hnext⟩

/-- Lemma e-safe-inclusion by induction on EVERY finite
approximant. No finite cardinality assumption is needed here. -/
theorem safe_inclusion
    {n : Nat} {P : Type}
    (next : P → Fin n → P) (bad : P → Fin n → Prop)
    (I : P → Prop)
    (hI : ∀ p, I p → ∀ e : Fin n, ¬ bad p e ∧ I (next p e))
    (p : P) (hp : I p) : SafeAll next bad p :=
  fun k => safe_inclusion_at_stage next bad I hI k p hp

theorem safe_inclusion_image
    {n : Nat} {P Physical : Type}
    (next : P → Fin n → P) (bad : P → Fin n → Prop)
    (witness : Physical → P → Prop)
    (hI : ∀ x p, witness x p →
       ∀ e : Fin n, ¬ bad p e ∧
          ∃ y : Physical, witness y (next p e))
    (p : P) (h : ∃ x, witness x p) :
    SafeAll next bad p := by
  let I : P → Prop := fun q => ∃ x, witness x q
  apply safe_inclusion next bad I
  · intro q hq e
    obtain ⟨x, hx⟩ := hq
    obtain ⟨hb, y, hy⟩ := hI x q hx e
    exact ⟨hb, ⟨y, hy⟩⟩
  · exact h

theorem safe_all_closed
    {n : Nat} {P : Type}
    (next : P → Fin n → P) (bad : P → Fin n → Prop)
    (p : P) (h : SafeAll next bad p) (e : Fin n) :
    ¬ bad p e ∧ SafeAll next bad (next p e) := by
  constructor
  · exact ((h 1).2 e).1
  · intro k
    exact ((h (k + 1)).2 e).2

def QWord {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjW c) : Prop :=
  SafeAll (phiW ring) (badWord ring) p

def QReader {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjR c) : Prop :=
  SafeAll (phiR ring) (badReader ring) p

def QDigit {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjD c) : Prop :=
  SafeAll (phiD ring) (badDigit ring) p

theorem qword_step {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (h : QWord ring p) (e : Fin n) :
    ¬ badWord ring p e ∧ QWord ring (phiW ring p e) :=
  safe_all_closed (phiW ring) (badWord ring) p h e

theorem qreader_step {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjR c)
    (h : QReader ring p) (e : Fin n) :
    ¬ badReader ring p e ∧ QReader ring (phiR ring p e) :=
  safe_all_closed (phiR ring) (badReader ring) p h e

theorem qdigit_step {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjD c)
    (h : QDigit ring p) (e : Fin n) :
    ¬ badDigit ring p e ∧ QDigit ring (phiD ring p e) :=
  safe_all_closed (phiD ring) (badDigit ring) p h e

theorem qword_visible_fixed {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (h : QWord ring p) (e i : Fin n) :
    wordVisible (phiW ring p e) i = wordVisible p i := by
  have hn := (qword_step ring p h e).1
  by_cases heq : wordVisible (phiW ring p e) i = wordVisible p i
  · exact heq
  · exact False.elim (hn ⟨i, heq⟩)

theorem qreader_no_rejection {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjR c)
    (h : QReader ring p) (e : Fin n) :
    (rawR (p e) (p (ring.rightNeighbor e))).reject = false := by
  have hn := (qreader_step ring p h e).1
  cases hrow : (rawR (p e) (p (ring.rightNeighbor e))).reject with
  | false => rfl
  | true => exact False.elim (hn hrow)

theorem qdigit_visible_fixed {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjD c)
    (h : QDigit ring p) (e i : Fin n) :
    digitVisible (phiD ring p e) i = digitVisible p i := by
  have hn := (qdigit_step ring p h e).1
  by_cases heq : digitVisible (phiD ring p e) i = digitVisible p i
  · exact heq
  · exact False.elim (hn (Or.inl ⟨i, heq⟩))

theorem qdigit_no_report {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjD c)
    (h : QDigit ring p) (e : Fin n) :
    (topD (p e) (p (ring.rightNeighbor e))).topReject = false := by
  have hn := (qdigit_step ring p h e).1
  cases hrow : (topD (p e) (p (ring.rightNeighbor e))).topReject with
  | false => rfl
  | true => exact False.elim (hn (Or.inr hrow))


/-! E.G35 finite digit-value equations, with no privileged
StructSafe, inherited-inertness or stable-receipt premise. The
physical block geometry depends on the fixed marker word only. -/

def digitValueView {c : Compiled} {n : Nat}
    (p : Fin n → ProjD c) : Fin n → Bool × Fin c.topA :=
  fun i => ((p i).word.beta, (p i).top.d)

def valueDelimiter {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (v : Fin n → Bool × Fin c.topA) (k : Nat) : Prop :=
  0 < k ∧ k < n ∧ (v (digitSite ring root k)).1 = true

def firstValueDelimiter {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (v : Fin n → Bool × Fin c.topA) (first : Nat) : Prop :=
  valueDelimiter ring root v first ∧
  ∀ k : Nat, 0 < k → k < first →
    (v (digitSite ring root k)).1 = false

def nextValueDelimiter {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (v : Fin n → Bool × Fin c.topA)
    (start stop : Nat) : Prop :=
  valueDelimiter ring root v start ∧
  start < stop ∧ stop ≤ n ∧
  (stop < n → (v (digitSite ring root stop)).1 = true) ∧
  ∀ k : Nat, start < k → k < stop →
    (v (digitSite ring root k)).1 = false

def firstValueWritable {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (v : Fin n → Bool × Fin c.topA) (i : Fin n) : Prop :=
  ∃ first stop k : Nat,
    firstValueDelimiter ring root v first ∧
    nextValueDelimiter ring root v first stop ∧
    first ≤ k ∧ k < stop ∧ k + 1 < n ∧
    i = digitSite ring root k

def completeValueBlock {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (v : Fin n → Bool × Fin c.topA) (start : Nat) : Prop :=
  nextValueDelimiter ring root v start (start + digitSpan c) ∧
    start + digitSpan c < n

def valueBlockID {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (v : Fin n → Bool × Fin c.topA) (start : Nat) : Nat :=
  (List.range (digitSpan c)).foldl
    (fun acc h =>
       acc + c.topA ^ h * (v (digitSite ring root (start + h))).2.val)
    0

/-- E.G32 static value equations. Empty blocks and final fragments
never imply a fictional comparison or write. -/
def DigitValuesCorrect {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (v : Fin n → Bool × Fin c.topA) : Prop :=
  (∀ i : Fin n, firstValueWritable ring root v i →
      (v i).2 = c.zeroDigit) ∧
  (∀ first : Nat, firstValueDelimiter ring root v first →
      completeValueBlock ring root v first →
        valueBlockID ring root v first = 0) ∧
  (∀ source target : Nat,
      completeValueBlock ring root v source →
      target = source + digitSpan c →
      completeValueBlock ring root v target →
        valueBlockID ring root v target =
          (valueBlockID ring root v source + 1) %
            (c.topA ^ digitSpan c))

/-- E.G35 safe-value set. Accepted W origin is explicitly indexed
by its fixed root; a numerical-looking fixed word is not an origin.
Its construction is an independent missing W finite-receipt step. -/
def WeakDigitGood {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (acceptedW : Fin n → (Fin n → ProjW c) → Prop)
    (p : Fin n → ProjD c) : Prop :=
  (∃ root : Fin n,
    acceptedW root (wordProjection p) ∧
      DigitValuesCorrect ring root (digitValueView p)) ∧
  (∀ i : Fin n, (p i).top.topDirty = false) ∧
  QDigit ring p

/-! Barred finite observer E.G35: its entire dynamic control is
one sticky bit. The ambient projected-state shadow and failed
decoration are already provided by BlockA.Decoration. -/

def barredDigitInit {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (acceptedW : Fin n → (Fin n → ProjW c) → Prop)
    (p : Fin n → ProjD c)
    (γ : BlockA.Decoration (Fin n → ProjD c) Bool) : Prop :=
  (∃ root : Fin n, acceptedW root (wordProjection p)) ∧
  ((WeakDigitGood ring acceptedW p ∧
       γ = .live p true) ∨
   (¬ WeakDigitGood ring acceptedW p ∧
       γ = .live p false))

noncomputable def barredDigitControlStep {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (acceptedW : Fin n → (Fin n → ProjW c) → Prop) :
    Bool → (Fin n → ProjD c) → Fin n →
      (Fin n → ProjD c) → Bool := by
  classical
  exact fun seen _ _ p' =>
    seen || decide (WeakDigitGood ring acceptedW p')

/-- E.G35 terminal acceptance: shadow agrees, sticky hit bit
true, AND CURRENT endpoint satisfies S_D. -/
def barredDigitAccept {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (acceptedW : Fin n → (Fin n → ProjW c) → Prop)
    (p : Fin n → ProjD c)
    (γ : BlockA.Decoration (Fin n → ProjD c) Bool) : Prop :=
  match γ with
  | .failed => False
  | .live shadow seen =>
      shadow = p ∧ seen = true ∧ WeakDigitGood ring acceptedW p

/-- E.G36 exactly as an accepted finite projected history, except
that the accepted-W finite row interpreter and finite Q bound still
need their separate certificates. No strong D control is used. -/
def BarredDigitClass {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (acceptedW : Fin n → (Fin n → ProjW c) → Prop)
    (p : Fin n → ProjD c) : Prop :=
  BlockA.Generated ring (phiD ring)
    (barredDigitControlStep ring acceptedW)
    (barredDigitInit ring acceptedW)
    (barredDigitAccept ring acceptedW) p

/-- If S_D is stable, barred acceptance is stable on the actual
projected successor. This is the exact small E.G37 digit step.
The needed S_D stability is proved by W origin, Q_D, fixed values,
and the OLD dirty row; it is not a structural diagnostic. -/
theorem barred_accept_step {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (acceptedW : Fin n → (Fin n → ProjW c) → Prop)
    (hgood : ∀ p e, WeakDigitGood ring acceptedW p →
       WeakDigitGood ring acceptedW (phiD ring p e))
    (p : Fin n → ProjD c)
    (γ : BlockA.Decoration (Fin n → ProjD c) Bool)
    (e : Fin n)
    (h : barredDigitAccept ring acceptedW p γ) :
    barredDigitAccept ring acceptedW (phiD ring p e)
      (BlockA.update ring (phiD ring)
        (barredDigitControlStep ring acceptedW) γ
        (p e, p (ring.rightNeighbor e)) e (phiD ring p e)) := by
  classical
  cases γ with
  | failed => exact False.elim h
  | live shadow seen =>
      change shadow = p ∧ seen = true ∧
        WeakDigitGood ring acceptedW p at h
      obtain ⟨rfl, rfl, hg⟩ := h
      have hnew := hgood _ e hg
      simpa [barredDigitAccept, BlockA.update,
        barredDigitControlStep, hnew]

theorem barred_generated_step {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (acceptedW : Fin n → (Fin n → ProjW c) → Prop)
    (hgood : ∀ p e, WeakDigitGood ring acceptedW p →
       WeakDigitGood ring acceptedW (phiD ring p e))
    (p : Fin n → ProjD c)
    (e : Fin n) (h : BarredDigitClass ring acceptedW p) :
    BarredDigitClass ring acceptedW (phiD ring p e) := by
  exact BlockA.generated_step ring (phiD ring)
    (barredDigitControlStep ring acceptedW)
    (barredDigitInit ring acceptedW)
    (barredDigitAccept ring acceptedW)
    (barred_accept_step ring acceptedW hgood) p e h

/-- Conditional real-step component of E.G37, transporting the
barred witness through the ACTUAL noFire projection equality E.G5. -/
theorem barred_real_noFire {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (acceptedW : Fin n →
      (Fin n → ProjW (compileAdvice q)) → Prop)
    (hgood : ∀ p e, WeakDigitGood ring acceptedW p →
       WeakDigitGood ring acceptedW (phiD ring p e))
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : BarredDigitClass ring acceptedW (piD C)) :
    BarredDigitClass ring acceptedW
      (piD ((protocol q).step ring C e)) := by
  rw [stepD_noFire hn ring C e hfire]
  exact barred_generated_step ring acceptedW hgood
    (piD C) e h


/-! W and R accepted classes, explicitly parameterized by the
missing concrete OLD-row validation/worker-color interpreter.
These definitions CANNOT yet replace public WZero/R: doing so
without proving that interpreter would turn the receipt theorem
into an assumption. The digit observer below can use this exact
type of accepted-W-at-root predicate once it is proved. -/

def WordAcceptAtRoot {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (validated : BlockA.WordControl n c → Prop)
    (p : Fin n → ProjW c)
    (γ : BlockA.Decoration
      (Fin n → ProjW c) (BlockA.WordControl n c)) : Prop :=
  BlockA.acceptsWord ring validated (QWord ring) p γ ∧
    match γ with
    | .failed => False
    | .live _ control => control.root = root

def AcceptedWordAtRoot {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (wordT : BlockA.WordControl n c →
      (Fin n → ProjW c) → Fin n →
      (Fin n → ProjW c) → BlockA.WordControl n c)
    (validated : BlockA.WordControl n c → Prop)
    (root : Fin n) (p : Fin n → ProjW c) : Prop :=
  BlockA.Generated ring (phiW ring) wordT
    (BlockA.initializesWord ring)
    (WordAcceptAtRoot ring root validated) p

def AcceptedWord {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (wordT : BlockA.WordControl n c →
      (Fin n → ProjW c) → Fin n →
      (Fin n → ProjW c) → BlockA.WordControl n c)
    (validated : BlockA.WordControl n c → Prop)
    (p : Fin n → ProjW c) : Prop :=
  ∃ root, AcceptedWordAtRoot ring wordT validated root p

theorem accepted_word_step_conditional {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (wordT : BlockA.WordControl n c →
      (Fin n → ProjW c) → Fin n →
      (Fin n → ProjW c) → BlockA.WordControl n c)
    (validated : BlockA.WordControl n c → Prop)
    (root : Fin n)
    (hclosed : ∀ p γ e, WordAcceptAtRoot ring root validated p γ →
      WordAcceptAtRoot ring root validated (phiW ring p e)
        (BlockA.update ring (phiW ring) wordT γ
          (p e, p (ring.rightNeighbor e)) e (phiW ring p e)))
    (p : Fin n → ProjW c) (e : Fin n)
    (h : AcceptedWordAtRoot ring wordT validated root p) :
    AcceptedWordAtRoot ring wordT validated root
      (phiW ring p e) :=
  BlockA.generated_step ring (phiW ring) wordT
    (BlockA.initializesWord ring)
    (WordAcceptAtRoot ring root validated) hclosed p e h

/-- E.G18: the concrete E.G14 monitor has no extra closure
hypothesis. This statement does NOT manufacture QWord at the first
A0: it transports the independently certified safety conjunct of
E.G17 and freezes the completed finite receipts. -/
private theorem word_accept_at_root_next {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (γ : BlockA.Decoration
      (Fin n → ProjW c) (BlockA.WordControl n c))
    (e : Fin n)
    (ha : WordAcceptAtRoot ring root (BlockA.wordValidated ring) p γ) :
    WordAcceptAtRoot ring root (BlockA.wordValidated ring)
      (phiW ring p e)
      (BlockA.update ring (phiW ring) (BlockA.wordT ring) γ
        (p e, p (ring.rightNeighbor e)) e (phiW ring p e)) := by
  cases γ with
  | failed =>
      exact False.elim ha.1
  | live shadow h =>
      obtain ⟨hacc, hroot⟩ := ha
      obtain ⟨hs, hd, hv, hpub, hq⟩ := hacc
      subst shadow
      have hupdate :
          BlockA.update ring (phiW ring) (BlockA.wordT ring)
            (BlockA.Decoration.live p h)
            (p e, p (ring.rightNeighbor e)) e (phiW ring p e) =
          BlockA.Decoration.live (phiW ring p e) h := by
        classical
        simp [BlockA.update, BlockA.wordT_done, hd]
      unfold WordAcceptAtRoot
      simp only [hupdate]
      exact ⟨⟨rfl, hd, hv, hpub,
        (qword_step ring p hq e).2⟩, hroot⟩

/-- Unconditional closure for the concrete W monitor. In contrast
to accepted_word_step_conditional, no external acceptance-invariance
premise is passed to this theorem. -/
theorem accepted_word_step {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (h : AcceptedWordAtRoot ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) root p) :
    AcceptedWordAtRoot ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) root (phiW ring p e) :=
  BlockA.generated_step ring (phiW ring) (BlockA.wordT ring)
    (BlockA.initializesWord ring)
    (WordAcceptAtRoot ring root (BlockA.wordValidated ring))
    (word_accept_at_root_next ring root) p e h

/-- E.G18 is closed for every individual projected, birth-free
edge; the existential root remains the same root. -/
theorem accepted_word_phi_step {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (e : Fin n)
    (h : AcceptedWord ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) p) :
    AcceptedWord ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) (phiW ring p e) := by
  obtain ⟨root, hr⟩ := h
  exact ⟨root, accepted_word_step ring root p e hr⟩


/-- E.G19-23, using the actual R0a-c, R1a-c OLD-action
tag update already implemented by BlockA.readerControlNext.
Only the numerical five-fold validation is a parameter. -/
def AcceptedReader {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (recurrenceOrigin : (Fin n → ProjW c) → Prop)
    (foldValid : Fin n → Option (RawTok c.t) →
      Fin (c.t + 1) →
      BlockA.FiniteLedger (BlockA.ReaderSample n) c.t → Prop)
    (p : Fin n → ProjR c) : Prop :=
  BlockA.Generated ring (phiR ring)
    (BlockA.readerControlNext ring)
    (BlockA.initializesReader recurrenceOrigin)
    (BlockA.acceptsReader foldValid (QReader ring)) p

theorem accepted_reader_step {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (recurrenceOrigin : (Fin n → ProjW c) → Prop)
    (foldValid : Fin n → Option (RawTok c.t) →
      Fin (c.t + 1) →
      BlockA.FiniteLedger (BlockA.ReaderSample n) c.t → Prop)
    (hclosed : ∀ p γ e,
      BlockA.acceptsReader foldValid (QReader ring) p γ →
      BlockA.acceptsReader foldValid (QReader ring)
        (phiR ring p e)
        (BlockA.update ring (phiR ring)
          (BlockA.readerControlNext ring) γ
          (p e, p (ring.rightNeighbor e)) e
          (phiR ring p e)))
    (p : Fin n → ProjR c) (e : Fin n)
    (h : AcceptedReader ring recurrenceOrigin foldValid p) :
    AcceptedReader ring recurrenceOrigin foldValid
      (phiR ring p e) :=
  BlockA.generated_step ring (phiR ring)
    (BlockA.readerControlNext ring)
    (BlockA.initializesReader recurrenceOrigin)
    (BlockA.acceptsReader foldValid (QReader ring))
    hclosed p e h

/-! The raw reader's nested W fields have exactly the same projected
step as the independent W owner. Only field read congruence is used. -/

private theorem pairR_word_left {c : Compiled}
    (x y : ProjR c) :
    (pairR x y).1.word = (pairW x.word y.word).1 := rfl

private theorem pairR_word_right {c : Compiled}
    (x y : ProjR c) :
    (pairR x y).2.word = (pairW x.word y.word).2 := rfl

theorem wordProjectionR_phiR {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjR c)
    (e : Fin n) :
    wordProjectionR (phiR ring p e) =
      phiW ring (wordProjectionR p) e := by
  funext i
  let j := ring.rightNeighbor e
  change
    (if i = e then (pairR (p e) (p j)).1
      else if i = j then (pairR (p e) (p j)).2
      else p i).word =
    (if i = e then (pairW (p e).word (p j).word).1
      else if i = j then (pairW (p e).word (p j).word).2
      else (p i).word)
  by_cases he : i = e
  · simp only [if_pos he]
    exact pairR_word_left (p e) (p j)
  · by_cases hj : i = j
    · simp only [if_neg he, if_pos hj]
      exact pairR_word_right (p e) (p j)
    · simp only [if_neg he, if_neg hj]

/-! The fixed-root word projection commutes with the D owner.
This equality does not expand the whole physical TOP row. -/

private theorem pairD_word_left {c : Compiled}
    (x y : ProjD c) :
    (pairD x y).1.word = (pairW x.word y.word).1 := rfl

private theorem pairD_word_right {c : Compiled}
    (x y : ProjD c) :
    (pairD x y).2.word = (pairW x.word y.word).2 := rfl

theorem wordProjection_phiD {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjD c)
    (e : Fin n) :
    wordProjection (phiD ring p e) =
      phiW ring (wordProjection p) e := by
  funext i
  let j := ring.rightNeighbor e
  change
    (if i = e then (pairD (p e) (p j)).1
      else if i = j then (pairD (p e) (p j)).2
      else p i).word =
    (if i = e then (pairW (p e).word (p j).word).1
      else if i = j then (pairW (p e).word (p j).word).2
      else (p i).word)
  by_cases he : i = e
  · simp only [if_pos he]
    exact pairD_word_left (p e) (p j)
  · by_cases hj : i = j
    · simp only [if_neg he, if_pos hj]
      exact pairD_word_right (p e) (p j)
    · simp only [if_neg he, if_neg hj]

theorem digitValueView_phiD {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjD c)
    (h : QDigit ring p) (e : Fin n) :
    digitValueView (phiD ring p e) = digitValueView p := by
  funext i
  have hh := qdigit_visible_fixed ring p h e i
  exact congrArg
    (fun z : Bool × Bool × Fin c.topA => (z.2.1, z.2.2)) hh

/-- S_D closure using exactly three independent facts:
recurrence root validity, Q_D visible quiescence, and the physical
OLD dirty owner. The last fact is a separate row lemma to discharge,
not an assumed StructSafe/inertness receipt. -/
theorem weak_digit_good_step {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (acceptedW : Fin n → (Fin n → ProjW c) → Prop)
    (hW : ∀ root p e, acceptedW root p →
      acceptedW root (phiW ring p e))
    (hDirty : ∀ p e, WeakDigitGood ring acceptedW p →
      ∀ i : Fin n, ((phiD ring p e) i).top.topDirty = false)
    (p : Fin n → ProjD c) (e : Fin n)
    (h : WeakDigitGood ring acceptedW p) :
    WeakDigitGood ring acceptedW (phiD ring p e) := by
  obtain ⟨⟨root, hr, hv⟩, hd, hq⟩ := h
  have hword := wordProjection_phiD ring p e
  have hview := digitValueView_phiD ring p hq e
  refine ⟨⟨root, ?_, ?_⟩, hDirty p e
    ⟨⟨root, hr, hv⟩, hd, hq⟩, (qdigit_step ring p hq e).2⟩
  · rw [hword]
    exact hW root (wordProjection p) e hr
  · rw [hview]
    exact hv


/-! A compositional accepted-target interface. This is NOT yet
the exported Target: the word interpreter and the raw fold
predicate still require their actual finite row certificates. -/

def AcceptedFactors {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (wordT : BlockA.WordControl n c →
      (Fin n → ProjW c) → Fin n →
      (Fin n → ProjW c) → BlockA.WordControl n c)
    (validated : BlockA.WordControl n c → Prop)
    (foldValid : Fin n → Option (RawTok c.t) →
      Fin (c.t + 1) →
      BlockA.FiniteLedger (BlockA.ReaderSample n) c.t → Prop)
    (pW : Fin n → ProjW c)
    (pR : Fin n → ProjR c)
    (pD : Fin n → ProjD c) : Prop :=
  AcceptedWord ring wordT validated pW ∧
  AcceptedReader ring
    (AcceptedWord ring wordT validated) foldValid pR ∧
  BarredDigitClass ring
    (AcceptedWordAtRoot ring wordT validated) pD

theorem accepted_word_real_noFire {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (wordT : BlockA.WordControl n (compileAdvice q) →
      (Fin n → ProjW (compileAdvice q)) → Fin n →
      (Fin n → ProjW (compileAdvice q)) →
        BlockA.WordControl n (compileAdvice q))
    (validated : BlockA.WordControl n (compileAdvice q) → Prop)
    (hclosed : ∀ root p γ e,
      WordAcceptAtRoot ring root validated p γ →
      WordAcceptAtRoot ring root validated (phiW ring p e)
        (BlockA.update ring (phiW ring) wordT γ
          (p e, p (ring.rightNeighbor e)) e (phiW ring p e)))
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : AcceptedWord ring wordT validated (piW C)) :
    AcceptedWord ring wordT validated
      (piW ((protocol q).step ring C e)) := by
  obtain ⟨root, hroot⟩ := h
  rw [stepW_noFire hn ring C e hfire]
  exact ⟨root, accepted_word_step_conditional ring wordT validated root
    (hclosed root) (piW C) e hroot⟩

theorem accepted_reader_real_noFire {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (recurrenceOrigin : (Fin n → ProjW (compileAdvice q)) → Prop)
    (foldValid : Fin n → Option (RawTok (compileAdvice q).t) →
      Fin ((compileAdvice q).t + 1) →
      BlockA.FiniteLedger (BlockA.ReaderSample n)
        (compileAdvice q).t → Prop)
    (hclosed : ∀ p γ e,
      BlockA.acceptsReader foldValid (QReader ring) p γ →
      BlockA.acceptsReader foldValid (QReader ring)
        (phiR ring p e)
        (BlockA.update ring (phiR ring)
          (BlockA.readerControlNext ring) γ
          (p e, p (ring.rightNeighbor e)) e (phiR ring p e)))
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : AcceptedReader ring recurrenceOrigin foldValid (piR C)) :
    AcceptedReader ring recurrenceOrigin foldValid
      (piR ((protocol q).step ring C e)) := by
  rw [stepR_noFire hn ring C e hfire]
  exact accepted_reader_step ring recurrenceOrigin foldValid
    hclosed (piR C) e h

/-- Conditional, but exact, E.G37 class transport once the two
finite W/R receipt invariances and the single OLD dirty-row
consequence of Q_D are supplied. No consumer proof is assumed. -/
theorem accepted_factors_real_noFire {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (wordT : BlockA.WordControl n (compileAdvice q) →
      (Fin n → ProjW (compileAdvice q)) → Fin n →
      (Fin n → ProjW (compileAdvice q)) →
        BlockA.WordControl n (compileAdvice q))
    (validated : BlockA.WordControl n (compileAdvice q) → Prop)
    (foldValid : Fin n → Option (RawTok (compileAdvice q).t) →
      Fin ((compileAdvice q).t + 1) →
      BlockA.FiniteLedger (BlockA.ReaderSample n)
        (compileAdvice q).t → Prop)
    (hW : ∀ root p γ e,
      WordAcceptAtRoot ring root validated p γ →
      WordAcceptAtRoot ring root validated (phiW ring p e)
        (BlockA.update ring (phiW ring) wordT γ
          (p e, p (ring.rightNeighbor e)) e (phiW ring p e)))
    (hR : ∀ p γ e,
      BlockA.acceptsReader foldValid (QReader ring) p γ →
      BlockA.acceptsReader foldValid (QReader ring)
        (phiR ring p e)
        (BlockA.update ring (phiR ring)
          (BlockA.readerControlNext ring) γ
          (p e, p (ring.rightNeighbor e)) e (phiR ring p e)))
    (hDirty : ∀ p e,
      WeakDigitGood ring (AcceptedWordAtRoot ring wordT validated) p →
      ∀ i : Fin n, ((phiD ring p e) i).top.topDirty = false)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : AcceptedFactors ring wordT validated foldValid
      (piW C) (piR C) (piD C)) :
    AcceptedFactors ring wordT validated foldValid
      (piW ((protocol q).step ring C e))
      (piR ((protocol q).step ring C e))
      (piD ((protocol q).step ring C e)) := by
  rcases h with ⟨hw, hr, hd⟩
  have hroot : ∀ root p e,
      AcceptedWordAtRoot ring wordT validated root p →
      AcceptedWordAtRoot ring wordT validated root
        (phiW ring p e) := by
    intro root p e hp
    exact accepted_word_step_conditional ring wordT validated root
      (hW root) p e hp
  have hgood := weak_digit_good_step ring
    (AcceptedWordAtRoot ring wordT validated) hroot hDirty
  exact ⟨
    accepted_word_real_noFire hn ring wordT validated hW
      C e hfire hw,
    accepted_reader_real_noFire hn ring
      (AcceptedWord ring wordT validated) foldValid hR
      C e hfire hr,
    barred_real_noFire hn ring
      (AcceptedWordAtRoot ring wordT validated) hgood
      C e hfire hd⟩

/-- Only a parameterized accepted target is sound before the
receipt automata are fully instantiated and their row theorems
proved. The original Target definition below is legacy. -/
def AuditedTargetInterface {q n : Nat}
    (ring : DirectedRing n)
    (wordT : BlockA.WordControl n (compileAdvice q) →
      (Fin n → ProjW (compileAdvice q)) → Fin n →
      (Fin n → ProjW (compileAdvice q)) →
        BlockA.WordControl n (compileAdvice q))
    (validated : BlockA.WordControl n (compileAdvice q) → Prop)
    (foldValid : Fin n → Option (RawTok (compileAdvice q).t) →
      Fin ((compileAdvice q).t + 1) →
      BlockA.FiniteLedger (BlockA.ReaderSample n)
        (compileAdvice q).t → Prop)
    (C : (protocol q).Configuration n) : Prop :=
  OneNativeLeader (nativeProjection C) ∧
  Protected ring (nativeProjection C) ∧
  C_native ring (nativeProjection C) ∧
  H_cand ring (fun i => NativeCand.ofAgent (C i)) ∧
  AcceptedFactors ring wordT validated foldValid
    (piW C) (piR C) (piD C) ∧
  ∀ i : Fin n,
    (C i).EU = false ∧ (C i).ED = false ∧ (C i).req = false


/-! Derived observable consequences of an ACCEPTED endpoint. These
are E.G11-12, not claims about arbitrary old private records. -/

theorem accepted_word_qword {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (wordT : BlockA.WordControl n c →
      (Fin n → ProjW c) → Fin n →
      (Fin n → ProjW c) → BlockA.WordControl n c)
    (validated : BlockA.WordControl n c → Prop)
    (p : Fin n → ProjW c)
    (h : AcceptedWord ring wordT validated p) :
    QWord ring p := by
  obtain ⟨root, ρ, γ₀, w, γ, hj, hr, ha⟩ := h
  have hacc : BlockA.acceptsWord ring validated
      (QWord ring) p γ := ha.1
  cases γ with
  | failed => exact False.elim hacc
  | live shadow control =>
      exact hacc.2.2.2.2


/-- The concrete accepted W factor satisfies the full E.G10 safety
test. This follows from the explicit safety conjunct in E.G17;
a separate origin-to-safety induction is still needed for entrance. -/
theorem accepted_word_qword_concrete {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (h : AcceptedWord ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) p) :
    QWord ring p :=
  accepted_word_qword ring (BlockA.wordT ring)
    (BlockA.wordValidated ring) p h

/-- The W-only birth-disabled physical-step consequence. -/
theorem accepted_word_real_noFire_concrete {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : AcceptedWord ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) (piW C)) :
    AcceptedWord ring (BlockA.wordT ring)
      (BlockA.wordValidated ring)
      (piW ((protocol q).step ring C e)) := by
  rw [stepW_noFire hn ring C e hfire]
  exact accepted_word_phi_step ring (piW C) e h

theorem accepted_reader_qreader {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (recurrenceOrigin : (Fin n → ProjW c) → Prop)
    (foldValid : Fin n → Option (RawTok c.t) →
      Fin (c.t + 1) →
      BlockA.FiniteLedger (BlockA.ReaderSample n) c.t → Prop)
    (p : Fin n → ProjR c)
    (h : AcceptedReader ring recurrenceOrigin foldValid p) :
    QReader ring p := by
  obtain ⟨ρ, γ₀, w, γ, hj, hr, ha⟩ := h
  cases γ with
  | failed => exact False.elim ha
  | live shadow control =>
      exact ha.2.2.2.2

theorem barred_digit_qdigit {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (acceptedW : Fin n → (Fin n → ProjW c) → Prop)
    (p : Fin n → ProjD c)
    (h : BarredDigitClass ring acceptedW p) :
    QDigit ring p := by
  obtain ⟨ρ, γ₀, w, γ, hj, hr, ha⟩ := h
  cases γ with
  | failed => exact False.elim ha
  | live shadow seen =>
      have hg : WeakDigitGood ring acceptedW p := ha.2.2
      exact hg.2.2

/-- E.G37's three output assertions at an OLD projected edge.
The membership factors themselves require the concrete W/R closure
invariants, supplied separately to accepted_factors_real_noFire. -/
theorem accepted_factors_quiescent {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (wordT : BlockA.WordControl n c →
      (Fin n → ProjW c) → Fin n →
      (Fin n → ProjW c) → BlockA.WordControl n c)
    (validated : BlockA.WordControl n c → Prop)
    (foldValid : Fin n → Option (RawTok c.t) →
      Fin (c.t + 1) →
      BlockA.FiniteLedger (BlockA.ReaderSample n) c.t → Prop)
    (w : Fin n → ProjW c)
    (r : Fin n → ProjR c)
    (d : Fin n → ProjD c) (e : Fin n)
    (h : AcceptedFactors ring wordT validated foldValid w r d) :
    (∀ i : Fin n,
       wordVisible (phiW ring w e) i = wordVisible w i) ∧
    (rawR (r e) (r (ring.rightNeighbor e))).reject = false ∧
    (∀ i : Fin n,
       digitVisible (phiD ring d e) i = digitVisible d i) ∧
    (topD (d e) (d (ring.rightNeighbor e))).topReject = false := by
  obtain ⟨hw, hr, hd⟩ := h
  have hqw := accepted_word_qword ring wordT validated w hw
  have hqr := accepted_reader_qreader ring
    (AcceptedWord ring wordT validated) foldValid r hr
  have hqd := barred_digit_qdigit ring
    (AcceptedWordAtRoot ring wordT validated) d hd
  exact ⟨
    (fun i => qword_visible_fixed ring w hqw e i),
    qreader_no_rejection ring r hqr e,
    (fun i => qdigit_visible_fixed ring d hqd e i),
    qdigit_no_report ring d hqd e⟩

/-! Bridging the semantic SafeAll to the finite E.G10 fixed point.
If a concrete finite-state cardinality K has been shown to satisfy
the displayed fixed-point equation, K iterations suffice exactly. -/

theorem safe_all_of_finite_fixed
    {n : Nat} {P : Type}
    (next : P → Fin n → P) (bad : P → Fin n → Prop)
    (bound : Nat)
    (hfixed : ∀ p, BlockA.safeStage next bad bound p →
      BlockA.safeStage next bad (bound + 1) p)
    (p : P) (h : BlockA.safeStage next bad bound p) :
    SafeAll next bad p := by
  let I : P → Prop := fun q => BlockA.safeStage next bad bound q
  apply safe_inclusion next bad I
  · intro q hq e
    exact (hfixed q hq).2 e
  · exact h

theorem safe_all_iff_finite_fixed
    {n : Nat} {P : Type}
    (next : P → Fin n → P) (bad : P → Fin n → Prop)
    (bound : Nat)
    (hfixed : ∀ p, BlockA.safeStage next bad bound p →
      BlockA.safeStage next bad (bound + 1) p)
    (p : P) :
    SafeAll next bad p ↔
      BlockA.safeStage next bad bound p := by
  constructor
  · intro h
    exact h bound
  · intro h
    exact safe_all_of_finite_fixed next bad bound hfixed p h

end AcceptedReceipts

/-- PINNED LEGACY Target retained only for compatibility with prior
compiled theorems. Its WZero, R, Ddel still refer to the old unbounded
ghost-prefix classes, NOT the audited E.G18/E.G23/E.G36 membership.
AcceptedReceipts.AuditedTargetInterface is the honest finite-receipt
replacement interface pending the concrete W validator and R fold. -/
def Target {q n : Nat} (ring : DirectedRing n) :
    (protocol q).Configuration n → Prop :=
  fun C =>
    OneNativeLeader (nativeProjection C) ∧
    Protected ring (nativeProjection C) ∧
    C_native ring (nativeProjection C) ∧
    H_cand ring (fun i => NativeCand.ofAgent (C i)) ∧
    WZero ring (piW C) ∧
    R ring (piR C) ∧
    Ddel ring (piD C) ∧
    ∀ i : Fin n,
      (C i).EU = false ∧ (C i).ED = false ∧ (C i).req = false


/-! Uncompiled: the deterministic birth-free W entrance bridge.
These statements do not assert the serializer-clock bound, that a
genuine A0 must occur, or that completed receipts alone imply QWord. -/
namespace AcceptedReceipts
namespace WordEntrance

abbrev WDecoration (n : Nat) (c : Compiled) :=
  BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c)

/-- No inherited serializer or worker byte is colored at the entrance.
The physical W projection itself is not modified or restricted. -/
def emptyWordControl {n : Nat} {c : Compiled}
    (root : Fin n) : BlockA.WordControl n c :=
  { root := root
    phase := .awaitRequest
    requested := false
    serializer := fun _ => BlockA.wordColor .empty none
    workerKind := fun _ => .empty
    workerCursor := fun _ => .empty
    prefixReads := BlockA.wordEmptyLedger
    sumReads := BlockA.wordEmptyLedger
    publications := fun _ => .absent
    visibleReceipts := fun _ => false
    prefixMarkers := fun _ => false }

/-- E.G13 entrance from the literal protected-singleton domain.
All old serializer, lease and worker values remain arbitrary. -/
theorem empty_is_initial {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hr : WFixedRoot ring root p)
    (ht : 2 ≤ c.t)
    (hn : c.t + (2 ^ c.t - 1) ≤ n) :
    BlockA.initializesWord ring p
      (.live p (emptyWordControl root)) := by
  refine ⟨root, emptyWordControl root, rfl, rfl,
    hr, ht, hn, rfl, rfl, ?_, rfl, rfl⟩
  intro i
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A coincident, completion-looking OLD private state cannot
authenticate an initial, uncolored monitor endpoint. -/
theorem empty_not_accepted {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) :
    ¬ WordAcceptAtRoot ring root (BlockA.wordValidated ring)
      p (.live p (emptyWordControl root)) := by
  intro ha
  have hd : (emptyWordControl root).phase = .done := ha.1.2.1
  cases hd

/-- A positive OLD lease excludes the zero-lease hard-launch
branch. Thus even an S1 serializer row continues through the
ordinary worker interpreter rather than resetting its provenance. -/
theorem positive_lease_worker_dispatch {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (successor : Fin n → ProjW c)
    (hphase : h.phase = .worker)
    (hpos : (p e).siLease.val ≠ 0) :
    BlockA.wordT ring h p e successor =
      BlockA.wordWorkerNext ring h p e
        (BlockA.wordRequestNext ring h p e) := by
  have hno : ¬ BlockA.wordIsHardStart ring h p e := by
    intro hs
    exact hpos hs.2.2.1
  simp [BlockA.wordT, hphase, hno]

/-- In particular, an OLD soft S1 with an ordinary worker frame
does not erase a current worker or its read/publication receipts. -/
theorem positive_lease_frame_keeps_receipts {n : Nat}
    {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (successor : Fin n → ProjW c)
    (hphase : h.phase = .worker)
    (hpos : (p e).siLease.val ≠ 0)
    (hframe :
      BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .frame) :
    BlockA.wordT ring h p e successor =
      { h with requested := BlockA.wordRequestNext ring h p e } := by
  rw [positive_lease_worker_dispatch ring h p e
    successor hphase hpos]
  simp [BlockA.wordWorkerNext, hframe]

/-- The OLD-pair and successor congruence checks in E.G7 succeed
definitionally along a genuine projected step. No provenance color
is inferred from equality of physical bytes. -/
theorem word_update_live {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (h : BlockA.WordControl n c) (e : Fin n) :
    BlockA.update ring (phiW ring) (BlockA.wordT ring)
      (.live p h) (p e, p (ring.rightNeighbor e))
      e (phiW ring p e) =
    .live (phiW ring p e)
      (BlockA.wordT ring h p e (phiW ring p e)) := by
  classical
  simp [BlockA.update]

/-- The exact physical-to-monitor service equation. In particular,
a birth-disabled real service cannot create .failed from a live,
synchronized W monitor. -/
theorem real_edge_update_live {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (h : BlockA.WordControl n (compileAdvice q))
    (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none) :
    BlockA.update ring (phiW ring) (BlockA.wordT ring)
      (.live (piW C) h)
      ((piW C) e, (piW C) (ring.rightNeighbor e))
      e (piW ((protocol q).step ring C e)) =
    .live (piW ((protocol q).step ring C e))
      (BlockA.wordT ring h (piW C) e
        (piW ((protocol q).step ring C e))) := by
  rw [stepW_noFire hn ring C e hfire]
  exact word_update_live ring (piW C) h e

/-- A finite real-protocol history and its phase-local decoration.
Every edge is selected by the real scheduler, and each OLD pair
satisfies noFire. In particular this trace does not replace the
protocol by its W projection. -/
inductive RealTrace {n q : Nat}
    (ring : DirectedRing n)
    (Cinitial : (protocol q).Configuration n)
    (hinitial : BlockA.WordControl n (compileAdvice q)) :
    List (Fin n) →
    (protocol q).Configuration n →
    WDecoration n (compileAdvice q) → Prop where
  | empty :
      RealTrace ring Cinitial hinitial []
        Cinitial (.live (piW Cinitial) hinitial)
  | next {w C γ}
      (previous : RealTrace ring Cinitial hinitial w C γ)
      (e : Fin n)
      (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none) :
      RealTrace ring Cinitial hinitial (w ++ [e])
        ((protocol q).step ring C e)
        (BlockA.update ring (phiW ring) (BlockA.wordT ring)
          γ ((piW C) e, (piW C) (ring.rightNeighbor e))
          e (piW ((protocol q).step ring C e)))

/-- Each real noFire trace is exactly a BlockA.Run of the
OLD-selected E.G14 monitor, including intermediate real states. -/
theorem realTrace_projected {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (Cinitial : (protocol q).Configuration n)
    (hinitial : BlockA.WordControl n (compileAdvice q))
    {w : List (Fin n)}
    {C : (protocol q).Configuration n}
    {γ : WDecoration n (compileAdvice q)}
    (hrun : RealTrace ring Cinitial hinitial w C γ) :
    BlockA.Run ring (phiW ring) (BlockA.wordT ring)
      (piW Cinitial) (.live (piW Cinitial) hinitial)
      w (piW C) γ := by
  induction hrun with
  | empty =>
      exact BlockA.Run.empty
  | @next w C γ previous e hfire ih =>
      rw [stepW_noFire hn ring C e hfire]
      exact BlockA.Run.next ih e

/-- The E.G7 monitor never fails on a genuine projected run,
regardless of whether the serializer itself cancels a phase. -/
theorem projected_run_live {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (pinitial : Fin n → ProjW c)
    (hinitial : BlockA.WordControl n c)
    {w : List (Fin n)}
    {p : Fin n → ProjW c}
    {γ : WDecoration n c}
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring)
      pinitial (.live pinitial hinitial) w p γ) :
    ∃ h : BlockA.WordControl n c, γ = .live p h := by
  induction hrun with
  | empty =>
      exact ⟨hinitial, rfl⟩
  | @next w p γ previous e ih =>
      obtain ⟨h, hh⟩ := ih
      refine ⟨BlockA.wordT ring h p e (phiW ring p e), ?_⟩
      rw [hh]
      exact word_update_live ring p h e

/-- Arbitrary initial OLD W records do not cause failure of the
shadow congruence checks on any birth-disabled real edge sequence. -/
theorem realTrace_live {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (Cinitial : (protocol q).Configuration n)
    (hinitial : BlockA.WordControl n (compileAdvice q))
    {w : List (Fin n)}
    {C : (protocol q).Configuration n}
    {γ : WDecoration n (compileAdvice q)}
    (hrun : RealTrace ring Cinitial hinitial w C γ) :
    ∃ h : BlockA.WordControl n (compileAdvice q),
      γ = .live (piW C) h :=
  projected_run_live ring (piW Cinitial) hinitial
    (realTrace_projected hn ring Cinitial hinitial hrun)

/-- The deterministic entrance bridge: a genuinely witnessed
monitor endpoint, including its QWord safety certificate, is an
AcceptedWordAtRoot witness originating at the actual physical cut. -/
theorem accepted_from_realTrace {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (Cinitial : (protocol q).Configuration n)
    (root : Fin n)
    (hr : WFixedRoot ring root (piW Cinitial))
    (ht : 2 ≤ (compileAdvice q).t)
    (hwidth : (compileAdvice q).t +
        (2 ^ (compileAdvice q).t - 1) ≤ n)
    {w : List (Fin n)}
    {C : (protocol q).Configuration n}
    {γ : WDecoration n (compileAdvice q)}
    (hrun : RealTrace ring Cinitial (emptyWordControl root)
      w C γ)
    (ha : WordAcceptAtRoot ring root (BlockA.wordValidated ring)
      (piW C) γ) :
    AcceptedWordAtRoot ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) root (piW C) := by
  refine ⟨piW Cinitial,
    .live (piW Cinitial) (emptyWordControl root),
    w, γ, ?_, ?_, ha⟩
  · exact empty_is_initial ring root (piW Cinitial)
      hr ht hwidth
  · exact realTrace_projected hn ring Cinitial
      (emptyWordControl root) hrun

/-- Explicit physical-coherence-to-accepted-endpoint interface.
The last premise is an independently established QWord certificate:
the colored publication flags by themselves do not prove safety. -/
theorem accepted_from_checked_endpoint {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (Cinitial : (protocol q).Configuration n)
    (root : Fin n)
    (hr : WFixedRoot ring root (piW Cinitial))
    (ht : 2 ≤ (compileAdvice q).t)
    (hwidth : (compileAdvice q).t +
        (2 ^ (compileAdvice q).t - 1) ≤ n)
    {w : List (Fin n)}
    {C : (protocol q).Configuration n}
    {γ : WDecoration n (compileAdvice q)}
    (hcontrol : BlockA.WordControl n (compileAdvice q))
    (hrun : RealTrace ring Cinitial (emptyWordControl root)
      w C γ)
    (hshadow : γ = .live (piW C) hcontrol)
    (hdone : hcontrol.phase = .done)
    (hvalidated : BlockA.wordValidated ring hcontrol)
    (hpublished : BlockA.wordAllPublished ring hcontrol)
    (hsameRoot : hcontrol.root = root)
    (hsafe : QWord ring (piW C)) :
    AcceptedWord ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) (piW C) := by
  have ha : WordAcceptAtRoot ring root
      (BlockA.wordValidated ring) (piW C) γ := by
    rw [hshadow]
    exact ⟨⟨rfl, hdone, hvalidated, hpublished, hsafe⟩,
      hsameRoot⟩
  exact ⟨root, accepted_from_realTrace hn ring Cinitial
    root hr ht hwidth hrun ha⟩

end WordEntrance
end AcceptedReceipts


/-! Worker-side core certificates.

The named CleanIZero hypothesis is the serializer-causality/scrub
interface permitted in this round. All data below are read from
the actual OLD selected projected pair; nothing is inserted into Agent.
The complete first-A0-to-QWord invariant is NOT claimed below. -/

namespace AcceptedReceipts
namespace WordEntrance
namespace CleanWorker

/-- The complete OLD-owner I0 acceptance and serializer scrub contract.
It includes the physical absence of workers outside the selected pair. -/
structure CleanIZero {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) : Prop where
  phase : h.phase = .validate
  noRestart : ¬ BlockA.wordIsHardStart ring h p e
  selected : BlockA.serializerCase (p e)
    (p (ring.rightNeighbor e)) = .hardTerminal
  root : e = h.root
  parentTag : (h.serializer e).tag = .rootDone
  childTag : (h.serializer (ring.rightNeighbor e)).tag = .returning
  childParent : (h.serializer (ring.rightNeighbor e)).parent = some e
  returned : BlockA.wordAllReturned ring h
  scrubbed : BlockA.wordOtherWorkersFree ring h p e
  accepted : (serW (p e) (p (ring.rightNeighbor e))).hard.hardAccept = true
  initialRow : (workerW (p e) (p (ring.rightNeighbor e))).row = "I0"
  prefixStart : (workerW (p e)
    (p (ring.rightNeighbor e))).x = launchPrefix c.t
  responderFree : freeSI (workerW (p e)
    (p (ring.rightNeighbor e))).y = true

/-- The actual hard-terminal validator selects the canonical I0
worker launch. All OLD first-match guards appear as hypotheses. -/
theorem cleanI0_validate {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (clean : CleanIZero ring h p e) :
    BlockA.wordValidateNext ring h p e request =
      BlockA.wordWorkerLaunch h := by
  have hroot : e = h.root := clean.root
  subst e
  have hcase :
      BlockA.serializerCase (p h.root)
        (p (ring.rightNeighbor h.root)) = .hardTerminal :=
    clean.selected
  have hguard :
      h.root = h.root ∧
      (h.serializer h.root).tag = .rootDone ∧
      (h.serializer (ring.rightNeighbor h.root)).tag = .returning ∧
      (h.serializer (ring.rightNeighbor h.root)).parent = some h.root ∧
      BlockA.wordAllReturned ring h ∧
      BlockA.wordOtherWorkersFree ring h p h.root ∧
      (serW (p h.root)
        (p (ring.rightNeighbor h.root))).hard.hardAccept = true ∧
      (workerW (p h.root)
        (p (ring.rightNeighbor h.root))).row = "I0" ∧
      (workerW (p h.root)
        (p (ring.rightNeighbor h.root))).x = launchPrefix c.t ∧
      freeSI (workerW (p h.root)
        (p (ring.rightNeighbor h.root))).y = true :=
    ⟨rfl, clean.parentTag, clean.childTag, clean.childParent,
      clean.returned, clean.scrubbed, clean.accepted,
      clean.initialRow, clean.prefixStart, clean.responderFree⟩
  dsimp only [BlockA.wordValidateNext]
  rw [hcase]
  all_goals
    first
    | exact if_pos hguard
    | simpa using (if_pos hguard)
    | simp [clean.parentTag, clean.childTag, clean.childParent,
        clean.returned, clean.scrubbed, clean.accepted,
        clean.initialRow, clean.prefixStart, clean.responderFree]

/-- The concrete E.G14 interpreter reaches worker phase on the
same physical I0 edge, not by matching a post-service byte pattern. -/
theorem cleanI0_wordT {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (successor : Fin n → ProjW c)
    (clean : CleanIZero ring h p e) :
    BlockA.wordT ring h p e successor =
      BlockA.wordWorkerLaunch h := by
  have hv := cleanI0_validate ring h p e
    (BlockA.wordRequestNext ring h p e) clean
  simp [BlockA.wordT, clean.phase, clean.noRestart, hv]

/-- After I0, all *colored* earlier work and all read/publication
ledgers are cleared. The root alone carries prefix index zero. -/
theorem workerLaunch_shape {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) :
    (BlockA.wordWorkerLaunch h).phase = .worker ∧
    (BlockA.wordWorkerLaunch h).workerKind h.root =
      .prefix 0 false true ∧
    (∀ i : Fin n, i ≠ h.root →
      (BlockA.wordWorkerLaunch h).workerKind i = .empty) ∧
    (∀ i : Fin n,
      (BlockA.wordWorkerLaunch h).workerCursor i = .empty ∧
      (BlockA.wordWorkerLaunch h).publications i = .absent ∧
      (BlockA.wordWorkerLaunch h).visibleReceipts i = false ∧
      (BlockA.wordWorkerLaunch h).prefixMarkers i = false) ∧
    (BlockA.wordWorkerLaunch h).prefixReads.count.val = 0 ∧
    (BlockA.wordWorkerLaunch h).sumReads.count.val = 0 := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl⟩
  · simp [BlockA.wordWorkerLaunch, BlockA.wordClear]
  · intro i hi
    simp [BlockA.wordWorkerLaunch, BlockA.wordClear, hi]
  · intro i
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exact fields of the SI owner at an OLD hard acceptance:
launching the worker is not itself a visible publication. -/
theorem hardAccept_worker_visible {c : Compiled}
    (x y : ProjW c)
    (hh : (serW x y).hard.hardAccept = true) :
    (workerW x y).uX = x.u ∧
    (workerW x y).uY = y.u ∧
    (workerW x y).betaX = x.beta ∧
    (workerW x y).betaY = y.beta := by
  unfold workerW
  simp [siStep, hh, ProjW.lift]

/-- The physical I0 projected edge preserves u and beta at both
endpoints, even though the native/serializer/worker fields change. -/
theorem hardAccept_pair_visible {c : Compiled}
    (x y : ProjW c)
    (hh : (serW x y).hard.hardAccept = true) :
    (pairW x y).1.u = x.u ∧
    (pairW x y).2.u = y.u ∧
    (pairW x y).1.beta = x.beta ∧
    (pairW x y).2.beta = y.beta := by
  change
    (workerW x y).uX = x.u ∧
    (workerW x y).uY = y.u ∧
    (workerW x y).betaX = x.beta ∧
    (workerW x y).betaY = y.beta
  exact hardAccept_worker_visible x y hh

/-- No visible word coordinate changes during an OLD hard I0 edge.
The ring-nonsingleton premise resolves source-wins priority. -/
theorem hardAccept_phi_visible {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hh : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = true) :
    ∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i := by
  intro i
  have hfields := hardAccept_pair_visible
    (p e) (p (ring.rightNeighbor e)) hh
  by_cases he : i = e
  · subst i
    simp only [wordVisible]
    simp only [phiW, projectedEdge, if_pos rfl]
    exact Prod.ext hfields.1 hfields.2.2.1
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp only [wordVisible]
      simp only [phiW, projectedEdge, if_neg hne, if_pos rfl]
      exact Prod.ext hfields.2.1 hfields.2.2.2
    · simp only [wordVisible, phiW, projectedEdge,
        if_neg he, if_neg hj]

/-- The physical post-I0 W state, not merely its monitor color,
has exactly the canonical root prefix and free other workers. -/
def WorkerCleanAfterIZero {n : Nat} {c : Compiled}
    (root : Fin n) (p : Fin n → ProjW c) : Prop :=
  (p root).si = launchPrefix c.t ∧
  ∀ i : Fin n, i ≠ root → freeSI (p i).si = true

theorem cleanI0_physical_launch {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (clean : CleanIZero ring h p e) :
    WorkerCleanAfterIZero h.root (phiW ring p e) := by
  have heq : e = h.root := clean.root
  subst e
  constructor
  · simp only [phiW, projectedEdge, if_pos rfl]
    change (workerW (p h.root)
      (p (ring.rightNeighbor h.root))).x = launchPrefix c.t
    exact clean.prefixStart
  · intro i hi
    by_cases hj : i = ring.rightNeighbor h.root
    · subst i
      simp only [phiW, projectedEdge, if_neg hne, if_pos rfl]
      change freeSI (workerW (p h.root)
        (p (ring.rightNeighbor h.root))).y = true
      exact clean.responderFree
    · simp only [phiW, projectedEdge, if_neg hi, if_neg hj]
      exact clean.scrubbed i hi hj

/-- Mathematical audit of prefix OLD reads. There is no invented
new bit: the constructor consumes precisely the selected oldBit. -/
structure PrefixAudit where
  count : Nat
  z : Bool
  a : Bool
  deriving DecidableEq, Repr

def prefixAuditEmpty : PrefixAudit :=
  { count := 0, z := false, a := true }

def prefixAuditStep (s : PrefixAudit) (oldBit : Bool) :
    PrefixAudit :=
  { count := s.count + 1
    z := s.z || oldBit
    a := s.a && oldBit }

def prefixAuditOf (reads : List Bool) : PrefixAudit :=
  reads.foldl prefixAuditStep prefixAuditEmpty

theorem prefixAudit_snoc (reads : List Bool) (oldBit : Bool) :
    prefixAuditOf (reads ++ [oldBit]) =
      prefixAuditStep (prefixAuditOf reads) oldBit := by
  simp [prefixAuditOf, List.foldl_append]

theorem prefixAudit_step_fields (s : PrefixAudit) (oldBit : Bool) :
    (prefixAuditStep s oldBit).count = s.count + 1 ∧
    (prefixAuditStep s oldBit).z = (s.z || oldBit) ∧
    (prefixAuditStep s oldBit).a = (s.a && oldBit) :=
  ⟨rfl, rfl, rfl⟩

/-- Prefix P3 cannot leave its initial t-window identically zero:
an all-zero OR triggers an actual 1 publication. -/
def prefixKick (z oldBit : Bool) : Bool :=
  if z then oldBit else true

theorem prefixKick_nonzero (z oldBit : Bool) :
    (z || prefixKick z oldBit) = true := by
  cases z <;> simp [prefixKick]

/-- Read-ledger algebra for the sum cursor, with the first source
excluded from trailing AND, exactly as in E.G16. -/
structure SumAudit where
  count : Nat
  z : Bool
  parity : Bool
  trailing : Bool
  deriving DecidableEq, Repr

def sumAuditEmpty : SumAudit :=
  { count := 0, z := false, parity := false, trailing := true }

def sumAuditStep {n : Nat}
    (s : SumAudit) (read : BlockA.SumSample n) : SumAudit :=
  { count := s.count + 1
    z := s.z || read.oldBit
    parity := Bool.xor s.parity (read.tap && read.oldBit)
    trailing := if s.count = 0 then true else s.trailing && read.oldBit }

def sumAuditOf {n : Nat}
    (reads : List (BlockA.SumSample n)) : SumAudit :=
  reads.foldl sumAuditStep sumAuditEmpty

theorem sumAudit_snoc {n : Nat}
    (reads : List (BlockA.SumSample n))
    (oldRead : BlockA.SumSample n) :
    sumAuditOf (reads ++ [oldRead]) =
      sumAuditStep (sumAuditOf reads) oldRead := by
  simp [sumAuditOf, List.foldl_append]

/-- At a cursor with j genuine earlier reads, its next ledger entry
reproduces the three physical wordFold assignments exactly, with
the tap attached to the OLD selected source. -/
theorem sumAudit_matches_wordFold {n : Nat}
    (c : Compiled) (s : SumAudit)
    (read : BlockA.SumSample n) (j : Fin (c.t + 1))
    (hindex : s.count = j.val)
    (htap : read.tap = c.taps j.val) :
    sumAuditStep s read =
      { count := s.count + 1
        z := (BlockA.wordFold j s.z s.parity s.trailing
          read.oldBit).1
        parity := (BlockA.wordFold j s.z s.parity s.trailing
          read.oldBit).2.1
        trailing := (BlockA.wordFold j s.z s.parity s.trailing
          read.oldBit).2.2 } := by
  cases s with
  | mk count z parity trailing =>
      have hcount : count = j.val := hindex
      have hzero : (count = 0) ↔ (j = 0) := by
        constructor
        · intro hz
          apply Fin.ext
          have hv : j.val = 0 := by omega
          simpa using hv
        · intro hj
          have hv : j.val = 0 := by
            rw [hj]
            rfl
          omega
      have hdec : decide (count = 0) = decide (j = 0) := by
        by_cases hz : count = 0
        · have hj : j = 0 := hzero.mp hz
          simp [hz, hj]
        · have hj : j ≠ 0 := fun he => hz (hzero.mpr he)
          simp [hz, hj]
      simp [sumAuditStep, BlockA.wordFold, htap, hdec]

theorem sumAudit_first_excludes_source {n : Nat}
    (s : SumAudit) (read : BlockA.SumSample n)
    (hfirst : s.count = 0) :
    (sumAuditStep s read).trailing = true := by
  simp [sumAuditStep, hfirst]

theorem sumAudit_later_includes_source {n : Nat}
    (s : SumAudit) (read : BlockA.SumSample n)
    (hlater : s.count ≠ 0) :
    (sumAuditStep s read).trailing =
      (s.trailing && read.oldBit) := by
  simp [sumAuditStep, hlater]

/-- S1 zero-kick ensures the new t-window is nonzero when the
OLD-source OR was false. This is the pure Boolean kernel of S1. -/
def sumPublishedBit (s : SumAudit) : Bool :=
  if s.z then s.parity else true

def sumPublishedMarker (s : SumAudit) : Bool :=
  s.trailing && sumPublishedBit s

theorem sumPublishedBit_nonzero (s : SumAudit) :
    (s.z || sumPublishedBit s) = true := by
  cases hs : s.z <;> simp [sumPublishedBit, hs]

theorem sumPublishedMarker_eq (s : SumAudit) :
    sumPublishedMarker s = (s.trailing && sumPublishedBit s) := rfl

/-- Actual S0/P1 and S1 ledger entries are from the OLD W sites,
not from an inferred POST publication. -/
theorem oldSumRead_fields {n : Nat} {c : Compiled}
    (p : Fin n → ProjW c) (e : Fin n)
    (j : Fin (c.t + 1)) :
    ({ source := e, oldBit := (p e).u,
       tap := c.taps j.val } : BlockA.SumSample n).oldBit =
       (p e).u ∧
    ({ source := e, oldBit := (p e).u,
       tap := c.taps j.val } : BlockA.SumSample n).tap =
       c.taps j.val := ⟨rfl, rfl⟩

/-- The A0 case is selected by the OLD SI row and all previously
published receipts. It changes only control phase and request. -/
structure CleanAZero {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) : Prop where
  phase : h.phase = .worker
  noRestart : ¬ BlockA.wordIsHardStart ring h p e
  selected : BlockA.workerCase (p e)
    (p (ring.rightNeighbor e)) = .terminal
  ready : h.workerKind e = .ready e
  seam : ring.rightNeighbor e = h.root
  rootKind : (p e).si.kind = .ROOT
  idle : (p e).si.busy = false
  noCursor : (p e).si.cur = .NONE
  allPublished : BlockA.wordAllPublished ring h

theorem cleanA0_workerNext {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (clean : CleanAZero ring h p e) :
    BlockA.wordWorkerNext ring h p e request =
      { h with requested := request, phase := .done } := by
  have hcase :
      BlockA.workerCase (p e) (p h.root) = .terminal := by
    simpa only [clean.seam] using clean.selected
  have hguard :
      h.workerKind e = .ready e ∧
      h.root = h.root ∧
      (p e).si.kind = .ROOT ∧
      (p e).si.busy = false ∧
      (p e).si.cur = .NONE ∧
      BlockA.wordAllPublished ring h :=
    ⟨clean.ready, rfl, clean.rootKind, clean.idle,
      clean.noCursor, clean.allPublished⟩
  dsimp only [BlockA.wordWorkerNext]
  rw [clean.seam]
  rw [hcase]
  all_goals
    first
    | exact if_pos hguard
    | simpa using (if_pos hguard)
    | simp [clean.ready, clean.rootKind, clean.idle,
        clean.noCursor, clean.allPublished]

theorem cleanA0_wordT {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (successor : Fin n → ProjW c)
    (clean : CleanAZero ring h p e) :
    BlockA.wordT ring h p e successor =
      { h with
        requested := BlockA.wordRequestNext ring h p e,
        phase := .done } := by
  have ht := cleanA0_workerNext ring h p e
    (BlockA.wordRequestNext ring h p e) clean
  simp [BlockA.wordT, clean.phase, clean.noRestart, ht]

/-- The actual accepted A0 freezes the finite provenance/receipt
arrays. This does NOT assert yet that the receipts establish QWord. -/
theorem cleanA0_retains_receipts {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (successor : Fin n → ProjW c)
    (clean : CleanAZero ring h p e) :
    (BlockA.wordT ring h p e successor).publications =
        h.publications ∧
    (BlockA.wordT ring h p e successor).visibleReceipts =
        h.visibleReceipts ∧
    (BlockA.wordT ring h p e successor).prefixMarkers =
        h.prefixMarkers ∧
    (BlockA.wordT ring h p e successor).sumReads =
        h.sumReads := by
  rw [cleanA0_wordT ring h p e successor clean]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- This is the exact outstanding safety induction, stated as a
named proof interface rather than assumed to follow from a finite
publication flag. Every future phiW edge must preserve the clean
worker provenance and avoid a visible change. -/
def FutureWorkerCertificate {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (I : (Fin n → ProjW c) → Prop) : Prop :=
  ∀ p, I p → ∀ e : Fin n,
    (∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i) ∧
    I (phiW ring p e)

/-- A proved row-local future-worker invariant implies all E.G10
finite safety approximants, with no arbitrary finite-state bound. -/
theorem futureWorkerCertificate_qword {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (I : (Fin n → ProjW c) → Prop)
    (hrows : FutureWorkerCertificate ring I)
    (p : Fin n → ProjW c) (hp : I p) :
    QWord ring p := by
  apply safe_inclusion (phiW ring) (badWord ring) I
  · intro s hs e
    obtain ⟨hvisible, hnext⟩ := hrows s hs e
    refine ⟨?_, hnext⟩
    intro hbad
    obtain ⟨i, hneq⟩ := hbad
    exact hneq (hvisible i)
  · exact hp

/-- The exact replacement for hsafe in the preexisting checked
endpoint bridge, conditional ONLY on an independently established
local row invariant (not an asserted QWord or an initial byte test).
Proving that row invariant from the canonical first-I0 worker epoch
is the remaining core obligation. -/
theorem accepted_from_checked_endpoint_of_worker_rows {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (Cinitial : (protocol q).Configuration n)
    (root : Fin n)
    (hr : WFixedRoot ring root (piW Cinitial))
    (ht : 2 ≤ (compileAdvice q).t)
    (hwidth : (compileAdvice q).t +
      (2 ^ (compileAdvice q).t - 1) ≤ n)
    {w : List (Fin n)}
    {C : (protocol q).Configuration n}
    {γ : WDecoration n (compileAdvice q)}
    (hcontrol : BlockA.WordControl n (compileAdvice q))
    (hrun : RealTrace ring Cinitial (emptyWordControl root)
      w C γ)
    (hshadow : γ = .live (piW C) hcontrol)
    (hdone : hcontrol.phase = .done)
    (hvalidated : BlockA.wordValidated ring hcontrol)
    (hpublished : BlockA.wordAllPublished ring hcontrol)
    (hsameRoot : hcontrol.root = root)
    (I : (Fin n → ProjW (compileAdvice q)) → Prop)
    (hfirst : I (piW C))
    (hrows : FutureWorkerCertificate ring I) :
    AcceptedWord ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) (piW C) := by
  have hsafe : QWord ring (piW C) :=
    futureWorkerCertificate_qword ring I hrows (piW C) hfirst
  exact accepted_from_checked_endpoint hn ring Cinitial
    root hr ht hwidth hcontrol hrun hshadow hdone
    hvalidated hpublished hsameRoot hsafe

end CleanWorker
end WordEntrance
end AcceptedReceipts


/-! Worker-row safety decomposition.

This addendum establishes the exact equivalence of a selected OLD
pair's four visible assignments and one-edge word quiescence.
It also supplies hard scrub and all-free physical row certificates,
and the publication algebra needed at P1/P2/P3/S1.

The global clean-worker provenance invariant through arbitrary
interruptions, and its first-A0 membership proof, remain open.
No claim of unconditional QWord follows from this section. -/

namespace AcceptedReceipts
namespace WordEntrance
namespace CleanWorker

/-- The four OLD-field equality checks are performed on the actual
winning SI owner, including hard-serializer priority. No comparison
of post-service private bytes is used to infer the selected case. -/
def SelectedWordQuiet {c : Compiled}
    (x y : ProjW c) : Prop :=
  (workerW x y).uX = x.u ∧
  (workerW x y).uY = y.u ∧
  (workerW x y).betaX = x.beta ∧
  (workerW x y).betaY = y.beta

/-- The E.G12 visible assignments of pairW are definitionally
precisely the actual OLD SI output's four public assignments. -/
theorem selectedWordQuiet_pair {c : Compiled}
    (x y : ProjW c) :
    SelectedWordQuiet x y ↔
      (pairW x y).1.u = x.u ∧
      (pairW x y).2.u = y.u ∧
      (pairW x y).1.beta = x.beta ∧
      (pairW x y).2.beta = y.beta :=
  Iff.rfl

/-- Full two-endpoint characterization for n≥2. This is the
unconditional exact row-local proof obligation for a single edge. -/
theorem selectedWordQuiet_iff_edge {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    SelectedWordQuiet (p e) (p (ring.rightNeighbor e)) ↔
      ∀ i : Fin n,
        wordVisible (phiW ring p e) i = wordVisible p i := by
  constructor
  · intro h i
    have hfields :
        (pairW (p e) (p (ring.rightNeighbor e))).1.u = (p e).u ∧
        (pairW (p e) (p (ring.rightNeighbor e))).2.u =
          (p (ring.rightNeighbor e)).u ∧
        (pairW (p e) (p (ring.rightNeighbor e))).1.beta =
          (p e).beta ∧
        (pairW (p e) (p (ring.rightNeighbor e))).2.beta =
          (p (ring.rightNeighbor e)).beta :=
      (selectedWordQuiet_pair (p e) (p (ring.rightNeighbor e))).mp h
    by_cases he : i = e
    · subst i
      simp only [wordVisible]
      simp only [phiW, projectedEdge, if_pos rfl]
      exact Prod.ext hfields.1 hfields.2.2.1
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simp only [wordVisible]
        simp only [phiW, projectedEdge, if_neg hne, if_pos rfl]
        exact Prod.ext hfields.2.1 hfields.2.2.2
      · simp only [wordVisible, phiW, projectedEdge,
          if_neg he, if_neg hj]
  · intro h
    have hx := h e
    have hy := h (ring.rightNeighbor e)
    simp only [wordVisible] at hx hy
    simp only [phiW, projectedEdge, if_pos rfl] at hx
    simp only [phiW, projectedEdge, if_neg hne, if_pos rfl] at hy
    apply (selectedWordQuiet_pair (p e)
      (p (ring.rightNeighbor e))).mpr
    exact ⟨congrArg Prod.fst hx,
      congrArg Prod.fst hy,
      congrArg Prod.snd hx,
      congrArg Prod.snd hy⟩

/-- The exact first-match hard-erasure row I1, after excluding the
higher-priority I0, has no U/beta publication. The worker objects
may be deleted, but the visible word is unchanged. -/
theorem hardErase_selectedWordQuiet {c : Compiled}
    (x y : ProjW c)
    (haccept : (serW x y).hard.hardAccept = false)
    (hscrub : ((serW x y).hard.hardLeft ||
      (serW x y).hard.hardRight) = true) :
    SelectedWordQuiet x y := by
  unfold SelectedWordQuiet workerW
  simp [siStep, haccept, hscrub, ProjW.lift]

/-- This is the corresponding visible no-op in the *actual phiW*.
It is independent of previous worker provenance and visible bits. -/
theorem hardErase_edge_quiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (haccept : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = false)
    (hscrub : ((serW (p e)
      (p (ring.rightNeighbor e))).hard.hardLeft ||
      (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardRight) = true) :
    ∀ i, wordVisible (phiW ring p e) i = wordVisible p i :=
  (selectedWordQuiet_iff_edge ring p e hne).mp
    (hardErase_selectedWordQuiet _ _ haccept hscrub)

/-- A physical free worker's relevant fields are OFF and NONE,
even though its other SI storage bits may be arbitrary. -/
theorem freeSI_kind_cur {t : Nat}
    (s : SI t) (h : freeSI s = true) :
    s.kind = .OFF ∧ s.cur = .NONE := by
  cases hk : s.kind <;> cases hc : s.cur <;>
    simp [freeSI, hk, hc] at h ⊢

/-- With both OLD SI workers free, I0/I1/F are the only possible
SI effects. All three leave public bits unchanged, regardless of
the OLD serializer records and native E leader outcome. -/
theorem bothFree_selectedWordQuiet {c : Compiled}
    (x y : ProjW c)
    (hx : freeSI x.si = true)
    (hy : freeSI y.si = true) :
    SelectedWordQuiet x y := by
  obtain ⟨hxKind, hxCur⟩ := freeSI_kind_cur x.si hx
  obtain ⟨hyKind, hyCur⟩ := freeSI_kind_cur y.si hy
  unfold SelectedWordQuiet workerW
  simp [siStep, ProjW.lift, hxKind, hxCur, hyKind, hyCur]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (repeat' split) <;> rfl

/-- Genuine one-edge physical quietness from an all-free worker
snapshot, including the selected incoming/outgoing root edge.
This is deliberately NOT asserted to be a closed invariant:
a subsequent I0 can launch a new prefix. -/
theorem allFree_one_edge_quiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e)
    (hfree : ∀ i : Fin n, freeSI (p i).si = true) :
    ∀ e i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i := by
  intro e i
  exact (selectedWordQuiet_iff_edge ring p e (hne e)).mp
    (bothFree_selectedWordQuiet (p e)
      (p (ring.rightNeighbor e))
      (hfree e) (hfree (ring.rightNeighbor e))) i

/-- The *one-edge*, genuinely row-local candidate invariant.
This alone does not claim closure through future worker moves. -/
def WordRowsQuiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) : Prop :=
  ∀ e : Fin n,
    SelectedWordQuiet (p e) (p (ring.rightNeighbor e))

theorem wordRowsQuiet_first_step {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e)
    (h : WordRowsQuiet ring p) :
    ∀ e i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i := by
  intro e i
  exact (selectedWordQuiet_iff_edge ring p e (hne e)).mp
    (h e) i

/-- An independently verified *propagation* theorem for physical
row coherence would turn WordRowsQuiet into the requested I.
The input still requires all-edge invariance, not merely a first
A0 receipt, and is the substantive missing worker induction. -/
theorem wordRowsQuiet_future_of_propagation {n : Nat}
    {c : Compiled} (ring : DirectedRing n)
    (hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e)
    (hnext : ∀ p : Fin n → ProjW c,
      WordRowsQuiet ring p →
      ∀ e, WordRowsQuiet ring (phiW ring p e)) :
    FutureWorkerCertificate (c := c) ring (WordRowsQuiet (c := c) ring) := by
  intro p hp e
  exact ⟨wordRowsQuiet_first_step ring p hne hp e,
    hnext p hp e⟩

/-- Arithmetic clause P1: clearing a prefix marker is idempotent
once the already-published marker is zero. -/
theorem prefixZero_idempotent (oldMarker : Bool)
    (hzero : oldMarker = false) :
    (false : Bool) = oldMarker := hzero.symm

/-- Arithmetic clause P2/P3: with a nonzero sampled prefix OR,
the kick leaves the old bit, and the genuine prefix AND equals the
already-published marker. -/
theorem prefixEnd_idempotent
    (sampledOr sampledAnd oldBit oldMarker : Bool)
    (hnonzero : sampledOr = true)
    (hmarker : sampledAnd = oldMarker) :
    (if sampledOr = false then true else oldBit) = oldBit ∧
      sampledAnd = oldMarker := by
  simp [hnonzero, hmarker]

/-- Arithmetic clause S1: if its OLD source window is nonzero
and the old target is already the recurrence/parity value with the
correct trailing-AND marker, both proposed publications are fixed. -/
theorem sumEnd_idempotent
    (sampledOr parity trailing oldBit oldMarker : Bool)
    (hnonzero : sampledOr = true)
    (hrec : parity = oldBit)
    (hmarker : (trailing && oldBit) = oldMarker) :
    (if sampledOr = false then true else parity) = oldBit ∧
      (trailing &&
        (if sampledOr = false then true else parity)) =
        oldMarker := by
  simp [hnonzero, hrec, hmarker]

end CleanWorker
end WordEntrance
end AcceptedReceipts


/-! Current-state clean-worker invariant.
The origin data, finite OLD-read receipts, static equations and
row-specific publication obligations all depend only on projected W
and WordControl, not on an unbounded execution history. -/

namespace AcceptedReceipts
namespace WordEntrance
namespace CleanWorker

/-- Actual U and marker at clockwise offset k. -/
def cwBit {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (k : Nat) : Bool :=
  (p (PPL.shiftRight ring root k)).u

def cwMarker {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (k : Nat) : Bool :=
  (p (PPL.shiftRight ring root k)).beta

/-- OR and AND over the actual follower prefix 1,...,length. -/
def cwPrefixOr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (length : Nat) : Bool :=
  (List.range length).foldl
    (fun z k => z || cwBit ring root p (k + 1)) false

def cwPrefixAnd {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (length : Nat) : Bool :=
  (List.range length).foldl
    (fun a k => a && cwBit ring root p (k + 1)) true

def cwSourceBit {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (target j : Nat) : Bool :=
  cwBit ring root p (target - c.t + j)

def cwSumOr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (target length : Nat) : Bool :=
  (List.range length).foldl
    (fun z j => z || cwSourceBit ring root p target j) false

def cwSumParity {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (target length : Nat) : Bool :=
  (List.range length).foldl
    (fun parity j =>
      Bool.xor parity (c.taps j && cwSourceBit ring root p target j))
    false

def cwSumTrailing {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (target length : Nat) : Bool :=
  (List.range length).foldl
    (fun a j =>
      if j = 0 then a else a && cwSourceBit ring root p target j)
    true

/-- The visible equations certified by clean-worker publication. -/
structure CleanWorkerWordValues {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop where
  /-- repair.tex:973: "writes beta_j=0" below the first window. -/
  prefixZeros : ∀ k : Fin n, 0 < k.val → k.val < c.t →
    cwMarker ring root p k.val = false
  /-- repair.tex:978-979: "first follower window" is nonzero. -/
  firstNonzero : cwPrefixOr ring root p c.t = true
  /-- repair.tex:996-1000: the recurrence never reaches zero. -/
  laterNonzero : ∀ k : Fin n, c.t < k.val →
    cwSumOr ring root p k.val c.t = true
  /-- repair.tex:993-1000: the next U is the XOR feedback. -/
  recurrence : ∀ k : Fin n, c.t < k.val →
    cwBit ring root p k.val =
      cwSumParity ring root p k.val c.t
  /-- repair.tex:991-999: the "trailing window" yields beta. -/
  markers : ∀ k : Fin n, c.t ≤ k.val →
    cwMarker ring root p k.val =
      (cwSumTrailing ring root p k.val c.t &&
        cwBit ring root p k.val)

/-- Current-state physical provenance. The last P3 prefix sample
remains an OLD value even when the selected P3 later kicks its U.
A0 clears the physical ready worker but freezes the monitor's color. -/
structure CleanWorkerInv {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop where
  /-- repair.tex:1002: "leader is never" an ordinary publication target. -/
  rootFixed : WFixedRoot ring h.root p
  /-- repair.tex:969-979: valid nonempty prefix geometry. -/
  width : 2 ≤ c.t ∧ c.t < n
  /-- repair.tex:955-963: a validating service "scrubs its worker". -/
  workerOrigin : ∀ i : Fin n, h.phase = .worker →
    freeSI (p i).si = true ∨
      h.workerKind i ≠ .empty ∨ h.workerCursor i ≠ .empty
  /-- repair.tex:970-977: genuine prefix OLD samples and their sites.
  The final sample may differ from U after the P3 zero kick. -/
  prefixReads : ∀ j : Fin c.t, j.val < h.prefixReads.count.val →
    ∃ oldBit : Bool,
      h.prefixReads.entries j =
        some { source := PPL.shiftRight ring h.root (j.val + 1)
               oldBit := oldBit } ∧
      (j.val + 1 = c.t ∨
        oldBit = cwBit ring h.root p (j.val + 1))
  /-- repair.tex:969-973: "OR accumulator" and AND of the prefix. -/
  prefixAcc : ∀ (i : Fin n) (idx : Fin (c.t + 1))
      (z a : Bool), h.workerKind i = .prefix idx z a →
    z = cwPrefixOr ring h.root p idx.val ∧
      a = cwPrefixAnd ring h.root p idx.val
  /-- repair.tex:969-974: current prefix tag and SI agree. -/
  prefixGeometry : ∀ (i : Fin n) (idx : Fin (c.t + 1))
      (z a : Bool), h.workerKind i = .prefix idx z a →
    (p i).si.kind = .PREFIX ∧
      (p i).si.cur = .NONE ∧
      (p i).si.j = idx ∧
      (p i).si.z = z ∧
      (p i).si.a = a ∧
      idx.val = PPL.cyclicOffset ring h.root i
  /-- repair.tex:975-1000: "Induction gives all" word equations. -/
  wordValues : CleanWorkerWordValues ring h.root p
  /-- repair.tex:982-985: "backward cursor" and its target. -/
  backGeometry : ∀ (i target : Fin n) (idx : Fin (c.t + 1)),
    h.workerCursor i = .back target idx →
      (p i).si.cur = .BACK ∧
      (p i).si.j = idx ∧
      h.workerKind target = .target target true
  /-- repair.tex:983-995: exact SUM OLD-bit/tap ledger. -/
  sumReads : ∀ (i target : Fin n) (idx : Fin (c.t + 1))
      (z parity trailing : Bool),
    h.workerCursor i = .sum target idx z parity trailing →
      ∀ j : Fin c.t, j.val < idx.val →
        h.sumReads.entries j =
          some { source := PPL.shiftRight ring h.root
                      (PPL.cyclicOffset ring h.root target - c.t + j.val)
                 oldBit := cwSourceBit ring h.root p
                      (PPL.cyclicOffset ring h.root target) j.val
                 tap := c.taps j.val }
  /-- repair.tex:983-996: SUM "exact invariant" of OR/XOR/AND. -/
  sumAcc : ∀ (i target : Fin n) (idx : Fin (c.t + 1))
      (z parity trailing : Bool),
    h.workerCursor i = .sum target idx z parity trailing →
      z = cwSumOr ring h.root p
        (PPL.cyclicOffset ring h.root target) idx.val ∧
      parity = cwSumParity ring h.root p
        (PPL.cyclicOffset ring h.root target) idx.val ∧
      trailing = cwSumTrailing ring h.root p
        (PPL.cyclicOffset ring h.root target) idx.val
  /-- repair.tex:983-996: current SUM cursor matches physical SI. -/
  sumGeometry : ∀ (i target : Fin n) (idx : Fin (c.t + 1))
      (z parity trailing : Bool),
    h.workerCursor i = .sum target idx z parity trailing →
      (p i).si.kind = .OFF ∧
      (p i).si.cur = .SUM ∧
      (p i).si.j = idx ∧
      (p i).si.z = z ∧
      (p i).si.p = parity ∧
      (p i).si.a = trailing ∧
      h.workerKind target = .target target true ∧
      h.sumReads.count.val = idx.val
  /-- repair.tex:996-1003: working-phase ready target geometry.
  A0 may clear the physical worker when h.phase becomes done. -/
  readyGeometry : ∀ i : Fin n,
    h.workerKind i = .ready i → h.phase = .worker →
      (p i).si.kind = .ROOT ∧
      (p i).si.busy = false ∧
      (p i).si.cur = .NONE
  /-- repair.tex:1009-1018: no unpaired orphan publishes a wrong value. -/
  orphanGuard : ∀ e : Fin n,
    h.workerKind e = .empty →
    h.workerCursor e = .empty →
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .sumPublish →
    SelectedWordQuiet (p e) (p (ring.rightNeighbor e))
  /-- repair.tex:1006-1010: "already-zero prefix markers" on P1. -/
  prefixMoveQuiet : ∀ e : Fin n,
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .prefixMove →
    SelectedWordQuiet (p e) (p (ring.rightNeighbor e))
  /-- repair.tex:974-979: P2 only republishes the correct marker. -/
  prefixTerminalQuiet : ∀ e : Fin n,
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .prefixTerminal →
    SelectedWordQuiet (p e) (p (ring.rightNeighbor e))
  /-- repair.tex:975-979: P3 bit/marker assignments are idempotent. -/
  prefixPublishQuiet : ∀ e : Fin n,
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .prefixPublish →
    SelectedWordQuiet (p e) (p (ring.rightNeighbor e))
  /-- repair.tex:991-1000: S1 has correct parity/marker output. -/
  sumPublishQuiet : ∀ e : Fin n,
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .sumPublish →
    SelectedWordQuiet (p e) (p (ring.rightNeighbor e))
  /-- repair.tex:1012-1024: remaining worker rows write no new value. -/
  nonPublishingQuiet : ∀ e : Fin n,
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) ≠ .prefixMove →
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) ≠ .prefixTerminal →
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) ≠ .prefixPublish →
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) ≠ .sumPublish →
    SelectedWordQuiet (p e) (p (ring.rightNeighbor e))

/-- Each potentially publishing OLD worker case carries an explicit
operational equality; the remaining cases have their own clause. -/
theorem cleanWorkerInv_wordRowsQuiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (inv : CleanWorkerInv ring h p) :
    WordRowsQuiet ring p := by
  intro e
  by_cases hp : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixMove
  · exact inv.prefixMoveQuiet e hp
  · by_cases ht : BlockA.workerCase (p e)
        (p (ring.rightNeighbor e)) = .prefixTerminal
    · exact inv.prefixTerminalQuiet e ht
    · by_cases hs : BlockA.workerCase (p e)
          (p (ring.rightNeighbor e)) = .prefixPublish
      · exact inv.prefixPublishQuiet e hs
      · by_cases hsum : BlockA.workerCase (p e)
            (p (ring.rightNeighbor e)) = .sumPublish
        · exact inv.sumPublishQuiet e hsum
        · exact inv.nonPublishingQuiet e hp ht hs hsum


/-- The literal worker result "B0" selects the backwardsMove case. -/
theorem cwWorkerCase_back {c : Compiled} (x y : ProjW c)
    (hrow : (workerW x y).row = "B0") :
    BlockA.workerCase x y = .backwardsMove := by
  simp [BlockA.workerCase, hrow]

/-- The literal worker result "B1" selects backwardsInit. -/
theorem cwWorkerCase_backInit {c : Compiled} (x y : ProjW c)
    (hrow : (workerW x y).row = "B1") :
    BlockA.workerCase x y = .backwardsInit := by
  simp [BlockA.workerCase, hrow]

/-- The literal worker result "A1" selects target advance. -/
theorem cwWorkerCase_advance {c : Compiled} (x y : ProjW c)
    (hrow : (workerW x y).row = "A1") :
    BlockA.workerCase x y = .advance := by
  simp [BlockA.workerCase, hrow]

private theorem cwBit_congr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i)
    (k : Nat) :
    cwBit ring root p' k = cwBit ring root p k := by
  simpa only [cwBit, wordVisible] using
    congrArg Prod.fst (hv (PPL.shiftRight ring root k))

private theorem cwMarker_congr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i)
    (k : Nat) :
    cwMarker ring root p' k = cwMarker ring root p k := by
  simpa only [cwMarker, wordVisible] using
    congrArg Prod.snd (hv (PPL.shiftRight ring root k))

private theorem cwFold_congr {α : Type}
    (len : Nat) (start : α)
    (f g : α → Nat → α)
    (hfg : ∀ z j, f z j = g z j) :
    (List.range len).foldl f start =
      (List.range len).foldl g start := by
  have hf : f = g := by
    funext z j
    exact hfg z j
  rw [hf]

private theorem cwPrefixOr_congr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i)
    (len : Nat) :
    cwPrefixOr ring root p' len = cwPrefixOr ring root p len := by
  unfold cwPrefixOr
  apply cwFold_congr
  intro z j
  rw [cwBit_congr ring root p' p hv (j + 1)]

private theorem cwPrefixAnd_congr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i)
    (len : Nat) :
    cwPrefixAnd ring root p' len = cwPrefixAnd ring root p len := by
  unfold cwPrefixAnd
  apply cwFold_congr
  intro a j
  rw [cwBit_congr ring root p' p hv (j + 1)]

private theorem cwSourceBit_congr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i)
    (target j : Nat) :
    cwSourceBit ring root p' target j =
      cwSourceBit ring root p target j := by
  unfold cwSourceBit
  exact cwBit_congr ring root p' p hv (target - c.t + j)

private theorem cwSumOr_congr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i)
    (target len : Nat) :
    cwSumOr ring root p' target len =
      cwSumOr ring root p target len := by
  unfold cwSumOr
  apply cwFold_congr
  intro z j
  rw [cwSourceBit_congr ring root p' p hv target j]

private theorem cwSumParity_congr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i)
    (target len : Nat) :
    cwSumParity ring root p' target len =
      cwSumParity ring root p target len := by
  unfold cwSumParity
  apply cwFold_congr
  intro parity j
  rw [cwSourceBit_congr ring root p' p hv target j]

private theorem cwSumTrailing_congr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i)
    (target len : Nat) :
    cwSumTrailing ring root p' target len =
      cwSumTrailing ring root p target len := by
  unfold cwSumTrailing
  apply cwFold_congr
  intro a j
  by_cases hj : j = 0
  · simp [hj]
  · simp only [if_neg hj]
    rw [cwSourceBit_congr ring root p' p hv target j]

/-- Every static recurrence, marker, and nonzero-window clause is
invariant under any projected edge which leaves U and beta fixed. -/
theorem cleanWorkerWordValues_congr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i)
    (h : CleanWorkerWordValues ring root p) :
    CleanWorkerWordValues ring root p' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hlt
    rw [cwMarker_congr ring root p' p hv k.val]
    exact h.prefixZeros k hk hlt
  · rw [cwPrefixOr_congr ring root p' p hv c.t]
    exact h.firstNonzero
  · intro k hk
    rw [cwSumOr_congr ring root p' p hv k.val c.t]
    exact h.laterNonzero k hk
  · intro k hk
    rw [cwBit_congr ring root p' p hv k.val,
      cwSumParity_congr ring root p' p hv k.val c.t]
    exact h.recurrence k hk
  · intro k hk
    rw [cwMarker_congr ring root p' p hv k.val,
      cwSumTrailing_congr ring root p' p hv k.val c.t,
      cwBit_congr ring root p' p hv k.val]
    exact h.markers k hk

/-- Only the static-value factor is propagated for every edge.
The physical colored worker/cursor invariant is a separate task. -/
theorem cleanWorkerInv_wordValues_step {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ∀ f : Fin n, ring.rightNeighbor f ≠ f)
    (inv : CleanWorkerInv ring h p) :
    CleanWorkerWordValues ring h.root (phiW ring p e) := by
  have hrows : WordRowsQuiet ring p :=
    cleanWorkerInv_wordRowsQuiet ring h p inv
  have hvisible := wordRowsQuiet_first_step ring p hne hrows e
  exact cleanWorkerWordValues_congr ring h.root
    (phiW ring p e) p hvisible inv.wordValues

/-- Case (a): an offroot edge touches two uncolored worker sites.
The phase-local scrub clause forces both actual SI records free. -/
theorem cleanWorker_frame_wordValues {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (_he : e ≠ h.root)
    (_hj : ring.rightNeighbor e ≠ h.root)
    (hworker : h.phase = .worker)
    (hleft : h.workerKind e = .empty ∧
      h.workerCursor e = .empty)
    (hright : h.workerKind (ring.rightNeighbor e) = .empty ∧
      h.workerCursor (ring.rightNeighbor e) = .empty)
    (inv : CleanWorkerInv ring h p) :
    CleanWorkerWordValues ring h.root (phiW ring p e) := by
  have hfreeLeft : freeSI (p e).si = true := by
    rcases inv.workerOrigin e hworker with hf | hk | hc
    · exact hf
    · exact False.elim (hk hleft.1)
    · exact False.elim (hc hleft.2)
  have hfreeRight :
      freeSI (p (ring.rightNeighbor e)).si = true := by
    rcases inv.workerOrigin (ring.rightNeighbor e) hworker with
      hf | hk | hc
    · exact hf
    · exact False.elim (hk hright.1)
    · exact False.elim (hc hright.2)
  have hvisible :
      ∀ i : Fin n, wordVisible (phiW ring p e) i =
        wordVisible p i :=
    (selectedWordQuiet_iff_edge ring p e hne).mp
      (bothFree_selectedWordQuiet (p e)
        (p (ring.rightNeighbor e)) hfreeLeft hfreeRight)
  exact cleanWorkerWordValues_congr ring h.root
    (phiW ring p e) p hvisible inv.wordValues

/-- Case (b): winning backward cursor B0 row and static values. -/
theorem cleanWorker_backwardsMove_wordValues {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ∀ f : Fin n, ring.rightNeighbor f ≠ f)
    (inv : CleanWorkerInv ring h p)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "B0") :
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
      .backwardsMove ∧
    CleanWorkerWordValues ring h.root (phiW ring p e) := by
  have hcase :
      BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
        .backwardsMove :=
    cwWorkerCase_back (p e) (p (ring.rightNeighbor e)) hrow
  exact ⟨hcase, cleanWorkerInv_wordValues_step ring h p e hne inv⟩

/-- Case (b): winning B1 backward-to-SUM row and static values. -/
theorem cleanWorker_backwardsInit_wordValues {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ∀ f : Fin n, ring.rightNeighbor f ≠ f)
    (inv : CleanWorkerInv ring h p)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "B1") :
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
      .backwardsInit ∧
    CleanWorkerWordValues ring h.root (phiW ring p e) := by
  have hcase :
      BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
        .backwardsInit :=
    cwWorkerCase_backInit (p e) (p (ring.rightNeighbor e)) hrow
  exact ⟨hcase, cleanWorkerInv_wordValues_step ring h p e hne inv⟩

/-- Case (c): winning A1 target-advance row and static values. -/
theorem cleanWorker_advance_wordValues {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ∀ f : Fin n, ring.rightNeighbor f ≠ f)
    (inv : CleanWorkerInv ring h p)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "A1") :
    BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
      .advance ∧
    CleanWorkerWordValues ring h.root (phiW ring p e) := by
  have hcase :
      BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
        .advance :=
    cwWorkerCase_advance (p e) (p (ring.rightNeighbor e)) hrow
  exact ⟨hcase, cleanWorkerInv_wordValues_step ring h p e hne inv⟩

/-- Case (d): positive-lease S1 is a soft serializer start;
the monitor's selected worker branch is not a hard restart. -/
theorem cleanWorker_softRoot_wordValues {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ∀ f : Fin n, ring.rightNeighbor f ≠ f)
    (inv : CleanWorkerInv ring h p)
    (hphase : h.phase = .worker)
    (_hroot : e = h.root)
    (hpos : (p e).siLease.val ≠ 0)
    (_hrow : (serW (p e)
      (p (ring.rightNeighbor e))).row = "S1") :
    BlockA.wordT ring h p e (phiW ring p e) =
      BlockA.wordWorkerNext ring h p e
        (BlockA.wordRequestNext ring h p e) ∧
    CleanWorkerWordValues ring h.root (phiW ring p e) := by
  refine ⟨positive_lease_worker_dispatch ring h p e
    (phiW ring p e) hphase hpos, ?_⟩
  exact cleanWorkerInv_wordValues_step ring h p e hne inv

/-- Case (d): hard root I1 erasure preserves all visible values
even if it removes worker control fields. -/
theorem cleanWorker_hardRoot_wordValues {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (_hroot : e = h.root)
    (inv : CleanWorkerInv ring h p)
    (haccept : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = false)
    (hscrub : ((serW (p e)
      (p (ring.rightNeighbor e))).hard.hardLeft ||
      (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardRight) = true) :
    CleanWorkerWordValues ring h.root (phiW ring p e) := by
  have hvisible := hardErase_edge_quiet ring p e hne haccept hscrub
  exact cleanWorkerWordValues_congr ring h.root
    (phiW ring p e) p hvisible inv.wordValues

/-- Full-structure preservation on an exact projected no-op; no
broader control/cursor preservation is claimed by this theorem. -/
theorem cleanWorkerInv_of_unchanged {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (inv : CleanWorkerInv ring h p)
    (hidentity : phiW ring p e = p) :
    CleanWorkerInv ring h (phiW ring p e) := by
  rw [hidentity]
  exact inv

end CleanWorker
end WordEntrance
end AcceptedReceipts

end L3


/-! No unconditional launch/full-frame theorem is asserted. -/

namespace L3
namespace AcceptedReceipts
namespace WordEntrance
namespace CleanWorker

/-- I0 leaves every public bit unchanged. Consequently the original
post-I0 invariant would force ALL five completed word equations to have
held already at the OLD pre-launch state. -/
theorem cwI0WordValuesNecessary {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (clean : CleanIZero ring h p e)
    (inv : CleanWorkerInv ring (BlockA.wordWorkerLaunch h)
      (phiW ring p e)) :
    CleanWorkerWordValues ring h.root p := by
  have hv := hardAccept_phi_visible ring p e hne clean.accepted
  exact cleanWorkerWordValues_congr ring h.root
    p (phiW ring p e) (fun i => (hv i).symm) inv.wordValues

/-- A zero OLD prefix formally refutes the literal post-I0 invariant. -/
theorem cwI0ZeroRefutesInv {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (clean : CleanIZero ring h p e)
    (hz : cwPrefixOr ring h.root p c.t = false) :
    ¬ CleanWorkerInv ring (BlockA.wordWorkerLaunch h)
       (phiW ring p e) := by
  intro inv
  have hnz :=
    (cwI0WordValuesNecessary ring h p e hne clean inv).firstNonzero
  rw [hz] at hnz
  cases hnz

/-- The same refutation at the GENUINE wordT launch, not merely at a
manually invented post-acceptance monitor color. -/
theorem cwI0WordTZeroRefutesInv {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (clean : CleanIZero ring h p e)
    (hz : cwPrefixOr ring h.root p c.t = false) :
    ¬ CleanWorkerInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  rw [cleanI0_wordT ring h p e (phiW ring p e) clean]
  exact cwI0ZeroRefutesInv ring h p e hne clean hz

/-- This weaker phase-local launch geometry IS established by the
genuine I0, without making pre-publication word-value claims. -/
structure CleanLaunchShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop where
  phase : h.phase = .worker
  rootTag : h.workerKind root = .prefix 0 false true
  rootPhysical : (p root).si = launchPrefix c.t
  otherSites : ∀ i : Fin n, i ≠ root →
    h.workerKind i = .empty ∧ freeSI (p i).si = true
  cursorsEmpty : ∀ i : Fin n, h.workerCursor i = .empty
  prefixLedgerEmpty : h.prefixReads.count.val = 0
  sumLedgerEmpty : h.sumReads.count.val = 0

theorem cwI0EstablishesLaunchShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (clean : CleanIZero ring h p e) :
    CleanLaunchShape ring h.root (BlockA.wordWorkerLaunch h)
      (phiW ring p e) := by
  rcases workerLaunch_shape h with
    ⟨hphase, hrootTag, hother, harrays, hprefix, hsum⟩
  rcases cleanI0_physical_launch ring h p e hne clean with
    ⟨hrootSI, hfree⟩
  refine ⟨hphase, hrootTag, hrootSI, ?_, ?_, hprefix, hsum⟩
  · intro i hi
    exact ⟨hother i hi, hfree i hi⟩
  · intro i
    exact (harrays i).1

/-- The concrete five-site, width-two, zero-U, beta[1]=true state.
The native projection has one leader at site 0 and no bullets. -/
def cwToyCfg : Compiled :=
  { q := 2, t := 2, s := 2, kappa := 0, taps := fun _ => false }

def cwToyRing : DirectedRing 5 := ⟨by decide⟩

def cwToyProjection (i : Fin 5) : ProjW cwToyCfg :=
  { native := { l := i == (0 : Fin 5), b := 0,
                sh := false, sg := false }
    ser :=
      if i = (0 : Fin 5) then
        { phase := .B, out := .DONE, probe := .NONE,
          cert := .RUNNING, wphase := .VALIDATING }
      else if i = (1 : Fin 5) then
        { phase := .F, out := .NEW, probe := .NONE,
          cert := .IDLE, wphase := .OFF }
      else
        { phase := .C, out := .NEW, probe := .NONE,
          cert := .IDLE, wphase := .OFF }
    siLease := 0
    si := offSI cwToyCfg.t
    u := false
    beta := i == (1 : Fin 5) }

def cwToyControl : BlockA.WordControl 5 cwToyCfg :=
  { root := 0
    phase := .validate
    requested := false
    serializer := fun i =>
      if i = (0 : Fin 5) then
        BlockA.wordColor .rootDone none
      else if i = (1 : Fin 5) then
        BlockA.wordColor .returning (some 0)
      else if i = (2 : Fin 5) then
        BlockA.wordColor .returning (some 1)
      else if i = (3 : Fin 5) then
        BlockA.wordColor .returning (some 2)
      else
        BlockA.wordColor .returning (some 3)
    workerKind := fun _ => .empty
    workerCursor := fun _ => .empty
    prefixReads := BlockA.wordEmptyLedger
    sumReads := BlockA.wordEmptyLedger
    publications := fun _ => .absent
    visibleReceipts := fun _ => false
    prefixMarkers := fun _ => false }

/-- All thirteen genuine OLD-row/monitor I0 fields, not only a
post-service prefix shape. Small checks use KERNEL decide. -/
theorem cwToyIsIZero :
    CleanIZero cwToyRing cwToyControl cwToyProjection
      (0 : Fin 5) := by
  refine {
    phase := by decide
    noRestart := by decide
    selected := by decide
    root := by decide
    parentTag := by decide
    childTag := by decide
    childParent := by decide
    returned := by decide
    scrubbed := by decide
    accepted := by decide
    initialRow := by decide
    prefixStart := by decide
    responderFree := by decide }

theorem cwToyWidth :
    2 ≤ cwToyCfg.t ∧
      cwToyCfg.t + (2 ^ cwToyCfg.t - 1) ≤ 5 := by
  decide

theorem cwToyZeroPrefix :
    cwPrefixOr cwToyRing (0 : Fin 5)
      cwToyProjection cwToyCfg.t = false := by
  decide

/-- Literal edge 0->1: the actual I0 state is not CleanWorkerInv. -/
theorem cwToyIZeroCounterexample :
    ¬ CleanWorkerInv cwToyRing
      (BlockA.wordT cwToyRing cwToyControl cwToyProjection
        (0 : Fin 5)
        (phiW cwToyRing cwToyProjection (0 : Fin 5)))
      (phiW cwToyRing cwToyProjection (0 : Fin 5)) := by
  exact cwI0WordTZeroRefutesInv cwToyRing cwToyControl
    cwToyProjection (0 : Fin 5) (by decide)
    cwToyIsIZero cwToyZeroPrefix

/-! Reusable field-by-field frame tools. All conclusions below are
restricted to what their hypotheses actually imply. -/

/-- Universal two-endpoint frame lemma for projectedEdge. -/
theorem cwProjectedEdgeFrame {A : Type} {n : Nat}
    (ring : DirectedRing n) (pair : A → A → A × A)
    (p : Fin n → A) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    projectedEdge ring pair p e i = p i := by
  simp only [projectedEdge, if_neg hi, if_neg hj]

theorem cwPhiWFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (phiW ring p e) i = p i :=
  cwProjectedEdgeFrame ring pairW p e i hi hj

/-- A two-site OLD pair remote from the selected edge is unchanged. -/
theorem cwRemoteWordPair {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (e f : Fin n)
    (hf : f ≠ e) (hfj : f ≠ ring.rightNeighbor e)
    (hs : ring.rightNeighbor f ≠ e)
    (hsj : ring.rightNeighbor f ≠ ring.rightNeighbor e) :
    ((phiW ring p e) f,
      (phiW ring p e) (ring.rightNeighbor f)) =
      (p f, p (ring.rightNeighbor f)) := by
  rw [cwPhiWFrame ring p e f hf hfj,
    cwPhiWFrame ring p e (ring.rightNeighbor f) hs hsj]

/-- Reuse that frame for ALL worker-row quietness obligations on
remote pairs; only pairs touching the changed endpoints remain. -/
theorem cwRemoteWorkerRowsQuiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e f : Fin n)
    (hf : f ≠ e) (hfj : f ≠ ring.rightNeighbor e)
    (hs : ring.rightNeighbor f ≠ e)
    (hsj : ring.rightNeighbor f ≠ ring.rightNeighbor e)
    (inv : CleanWorkerInv ring h p) :
    SelectedWordQuiet ((phiW ring p e) f)
      ((phiW ring p e) (ring.rightNeighbor f)) := by
  rw [cwPhiWFrame ring p e f hf hfj,
    cwPhiWFrame ring p e (ring.rightNeighbor f) hs hsj]
  exact (cleanWorkerInv_wordRowsQuiet ring h p inv) f

/-- Physical SI at colored sites is framed when the two selected
worker-kind colors are empty. -/
theorem cwFrameKindPhysical {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e i : Fin n)
    (hleft : h.workerKind e = .empty)
    (hright : h.workerKind (ring.rightNeighbor e) = .empty)
    (hcolor : h.workerKind i ≠ .empty) :
    ((phiW ring p e) i).si = (p i).si := by
  have hi : i ≠ e := by
    intro he
    subst i
    exact hcolor hleft
  have hj : i ≠ ring.rightNeighbor e := by
    intro he
    subst i
    exact hcolor hright
  rw [cwPhiWFrame ring p e i hi hj]

theorem cwFrameCursorPhysical {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e i : Fin n)
    (hleft : h.workerCursor e = .empty)
    (hright : h.workerCursor (ring.rightNeighbor e) = .empty)
    (hcolor : h.workerCursor i ≠ .empty) :
    ((phiW ring p e) i).si = (p i).si := by
  have hi : i ≠ e := by
    intro he
    subst i
    exact hcolor hleft
  have hj : i ≠ ring.rightNeighbor e := by
    intro he
    subst i
    exact hcolor hright
  rw [cwPhiWFrame ring p e i hi hj]

theorem cwPrefixReadsTransport {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i, wordVisible p' i = wordVisible p i)
    (inv : CleanWorkerInv ring h p) :
    ∀ j : Fin c.t, j.val < h.prefixReads.count.val →
      ∃ oldBit : Bool,
        h.prefixReads.entries j =
          some { source := PPL.shiftRight ring h.root (j.val + 1)
                 oldBit := oldBit } ∧
        (j.val + 1 = c.t ∨
          oldBit = cwBit ring h.root p' (j.val + 1)) := by
  intro j hj
  obtain ⟨oldBit, hsample, hcompat⟩ := inv.prefixReads j hj
  refine ⟨oldBit, hsample, ?_⟩
  rcases hcompat with hfinal | hvalue
  · exact Or.inl hfinal
  · right
    rw [cwBit_congr ring h.root p' p hv (j.val + 1)]
    exact hvalue

theorem cwPrefixAccTransport {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i, wordVisible p' i = wordVisible p i)
    (inv : CleanWorkerInv ring h p) :
    ∀ (i : Fin n) (idx : Fin (c.t + 1)) (z a : Bool),
      h.workerKind i = .prefix idx z a →
      z = cwPrefixOr ring h.root p' idx.val ∧
      a = cwPrefixAnd ring h.root p' idx.val := by
  intro i idx z a hk
  obtain ⟨hz, ha⟩ := inv.prefixAcc i idx z a hk
  constructor
  · calc
      z = cwPrefixOr ring h.root p idx.val := hz
      _ = cwPrefixOr ring h.root p' idx.val :=
        (cwPrefixOr_congr ring h.root p' p hv idx.val).symm
  · calc
      a = cwPrefixAnd ring h.root p idx.val := ha
      _ = cwPrefixAnd ring h.root p' idx.val :=
        (cwPrefixAnd_congr ring h.root p' p hv idx.val).symm

theorem cwSumReadsTransport {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i, wordVisible p' i = wordVisible p i)
    (inv : CleanWorkerInv ring h p) :
    ∀ (i target : Fin n) (idx : Fin (c.t + 1))
      (z parity trailing : Bool),
    h.workerCursor i = .sum target idx z parity trailing →
      ∀ j : Fin c.t, j.val < idx.val →
      h.sumReads.entries j =
        some { source := PPL.shiftRight ring h.root
                  (PPL.cyclicOffset ring h.root target - c.t + j.val)
               oldBit := cwSourceBit ring h.root p'
                  (PPL.cyclicOffset ring h.root target) j.val
               tap := c.taps j.val } := by
  intro i target idx z parity trailing hc j hj
  simpa only [cwSourceBit_congr ring h.root p' p hv
    (PPL.cyclicOffset ring h.root target) j.val] using
    (inv.sumReads i target idx z parity trailing hc j hj)

theorem cwSumAccTransport {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i, wordVisible p' i = wordVisible p i)
    (inv : CleanWorkerInv ring h p) :
    ∀ (i target : Fin n) (idx : Fin (c.t + 1))
      (z parity trailing : Bool),
    h.workerCursor i = .sum target idx z parity trailing →
      z = cwSumOr ring h.root p'
        (PPL.cyclicOffset ring h.root target) idx.val ∧
      parity = cwSumParity ring h.root p'
        (PPL.cyclicOffset ring h.root target) idx.val ∧
      trailing = cwSumTrailing ring h.root p'
        (PPL.cyclicOffset ring h.root target) idx.val := by
  intro i target idx z parity trailing hc
  obtain ⟨hz, hp, ha⟩ :=
    inv.sumAcc i target idx z parity trailing hc
  refine ⟨?_, ?_, ?_⟩
  · calc
      z = cwSumOr ring h.root p
        (PPL.cyclicOffset ring h.root target) idx.val := hz
      _ = cwSumOr ring h.root p'
        (PPL.cyclicOffset ring h.root target) idx.val :=
        (cwSumOr_congr ring h.root p' p hv
          (PPL.cyclicOffset ring h.root target) idx.val).symm
  · calc
      parity = cwSumParity ring h.root p
        (PPL.cyclicOffset ring h.root target) idx.val := hp
      _ = cwSumParity ring h.root p'
        (PPL.cyclicOffset ring h.root target) idx.val :=
        (cwSumParity_congr ring h.root p' p hv
          (PPL.cyclicOffset ring h.root target) idx.val).symm
  · calc
      trailing = cwSumTrailing ring h.root p
        (PPL.cyclicOffset ring h.root target) idx.val := ha
      _ = cwSumTrailing ring h.root p'
        (PPL.cyclicOffset ring h.root target) idx.val :=
        (cwSumTrailing_congr ring h.root p' p hv
          (PPL.cyclicOffset ring h.root target) idx.val).symm

theorem cwPrefixGeometryFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hleft : h.workerKind e = .empty)
    (hright : h.workerKind (ring.rightNeighbor e) = .empty)
    (inv : CleanWorkerInv ring h p) :
    ∀ (i : Fin n) (idx : Fin (c.t + 1)) (z a : Bool),
      h.workerKind i = .prefix idx z a →
      ((phiW ring p e) i).si.kind = .PREFIX ∧
      ((phiW ring p e) i).si.cur = .NONE ∧
      ((phiW ring p e) i).si.j = idx ∧
      ((phiW ring p e) i).si.z = z ∧
      ((phiW ring p e) i).si.a = a ∧
      idx.val = PPL.cyclicOffset ring h.root i := by
  intro i idx z a hk
  have hcolor : h.workerKind i ≠ .empty := by
    intro he
    rw [he] at hk
    cases hk
  have hsi := cwFrameKindPhysical ring h p e i hleft hright hcolor
  simpa only [hsi] using (inv.prefixGeometry i idx z a hk)

theorem cwBackGeometryFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hleft : h.workerCursor e = .empty)
    (hright : h.workerCursor (ring.rightNeighbor e) = .empty)
    (inv : CleanWorkerInv ring h p) :
    ∀ (i target : Fin n) (idx : Fin (c.t + 1)),
      h.workerCursor i = .back target idx →
      ((phiW ring p e) i).si.cur = .BACK ∧
      ((phiW ring p e) i).si.j = idx ∧
      h.workerKind target = .target target true := by
  intro i target idx hc
  have hcolor : h.workerCursor i ≠ .empty := by
    intro he
    rw [he] at hc
    cases hc
  have hsi := cwFrameCursorPhysical ring h p e i hleft hright hcolor
  simpa only [hsi] using (inv.backGeometry i target idx hc)

theorem cwSumGeometryFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hleft : h.workerCursor e = .empty)
    (hright : h.workerCursor (ring.rightNeighbor e) = .empty)
    (inv : CleanWorkerInv ring h p) :
    ∀ (i target : Fin n) (idx : Fin (c.t + 1))
      (z parity trailing : Bool),
      h.workerCursor i = .sum target idx z parity trailing →
      ((phiW ring p e) i).si.kind = .OFF ∧
      ((phiW ring p e) i).si.cur = .SUM ∧
      ((phiW ring p e) i).si.j = idx ∧
      ((phiW ring p e) i).si.z = z ∧
      ((phiW ring p e) i).si.p = parity ∧
      ((phiW ring p e) i).si.a = trailing ∧
      h.workerKind target = .target target true ∧
      h.sumReads.count.val = idx.val := by
  intro i target idx z parity trailing hc
  have hcolor : h.workerCursor i ≠ .empty := by
    intro he
    rw [he] at hc
    cases hc
  have hsi := cwFrameCursorPhysical ring h p e i hleft hright hcolor
  simpa only [hsi] using
    (inv.sumGeometry i target idx z parity trailing hc)

theorem cwReadyGeometryFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hleft : h.workerKind e = .empty)
    (hright : h.workerKind (ring.rightNeighbor e) = .empty)
    (inv : CleanWorkerInv ring h p) :
    ∀ i : Fin n, h.workerKind i = .ready i →
      h.phase = .worker →
      ((phiW ring p e) i).si.kind = .ROOT ∧
      ((phiW ring p e) i).si.busy = false ∧
      ((phiW ring p e) i).si.cur = .NONE := by
  intro i hk hp
  have hcolor : h.workerKind i ≠ .empty := by
    intro he
    rw [he] at hk
    cases hk
  have hsi := cwFrameKindPhysical ring h p e i hleft hright hcolor
  simpa only [hsi] using (inv.readyGeometry i hk hp)

end CleanWorker
end WordEntrance
end AcceptedReceipts
end L3

/-! Addendum: a phase/receipt-indexed invariant
with no requirements on unpublished prefix bits. Paper:
research/paper/l3/appendices/repair.tex:967-1024. -/

namespace L3
namespace AcceptedReceipts
namespace WordEntrance
namespace CleanWorker

/-- P1 certifies zero beta only at visited follower offsets < t.
Unvisited marker/public bits remain unconstrained. -/
def cwPhasePublishedPrefix {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (upto : Nat) : Prop :=
  ∀ k : Fin n, 0 < k.val → k.val ≤ upto → k.val < c.t →
    let site := PPL.shiftRight ring h.root k.val
    h.publications site = .prefixZero ∧
      h.visibleReceipts site = true ∧
      h.prefixMarkers site = true ∧
      cwMarker ring h.root p k.val = false

def cwPhasePrefixPhysical {n : Nat} {c : Compiled}
    (p : Fin n → ProjW c) (site : Fin n)
    (idx : Fin (c.t + 1)) (z a : Bool) : Prop :=
  (p site).si.kind = .PREFIX ∧
    (p site).si.cur = .NONE ∧
    (p site).si.j = idx ∧
    (p site).si.z = z ∧ (p site).si.a = a

/-- repair.tex:968-979, before P3. Every prefix sample is an OLD
bit; the OR/AND folds concern ONLY the first idx followers. -/
def cwPhasePrefix {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  ∃ (site : Fin n) (idx : Fin (c.t + 1)) (z a : Bool),
    h.phase = .worker ∧
    h.workerKind site = .prefix idx z a ∧
    h.prefixReads.count.val = idx.val ∧
    cwPhasePrefixPhysical p site idx z a ∧
    z = cwPrefixOr ring h.root p idx.val ∧
    a = cwPrefixAnd ring h.root p idx.val ∧
    (∀ j : Fin c.t, j.val < idx.val →
      h.prefixReads.entries j =
        some { source := PPL.shiftRight ring h.root (j.val + 1),
               oldBit := cwBit ring h.root p (j.val + 1) }) ∧
    cwPhasePublishedPrefix ring h p idx.val ∧
    (∀ i : Fin n, i ≠ site →
      h.workerKind i = .empty ∧
      h.workerCursor i = .empty ∧ freeSI (p i).si = true)

/-- After P3: the kick has made the actual first window nonzero;
the final marker is the AND of the NEW prefix. -/
def cwPhaseInitialPublished {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  cwPhasePublishedPrefix ring h p c.t ∧
    h.publications (PPL.shiftRight ring h.root c.t) = .prefixEnd ∧
    h.visibleReceipts (PPL.shiftRight ring h.root c.t) = true ∧
    cwPrefixOr ring h.root p c.t = true ∧
    cwMarker ring h.root p c.t =
      cwPrefixAnd ring h.root p c.t

/-- The past S1 targets, but not the current or future target, are
required to have the nonzero recurrence/trailing-marker values. -/
def cwPhaseEarlierPublished {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (upto : Nat) : Prop :=
  ∀ k : Fin n, c.t < k.val → k.val < upto →
    let site := PPL.shiftRight ring h.root k.val
    h.publications site = .recurrence ∧
      h.visibleReceipts site = true ∧
      cwSumOr ring h.root p k.val c.t = true ∧
      cwBit ring h.root p k.val =
        cwSumParity ring h.root p k.val c.t ∧
      cwMarker ring h.root p k.val =
        (cwSumTrailing ring h.root p k.val c.t &&
          cwBit ring h.root p k.val)

/-- repair.tex:980-985, BACK after P3 or A1. -/
def cwPhaseBack {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  ∃ (site target : Fin n) (idx : Fin (c.t + 1)),
    h.phase = .worker ∧
    h.workerKind target = .target target true ∧
    h.workerCursor site = .back target idx ∧
    (p site).si.cur = .BACK ∧ (p site).si.j = idx ∧
    (p target).si.kind = .ROOT ∧ (p target).si.busy = true ∧
    h.sumReads.count.val = 0 ∧
    cwPhaseInitialPublished ring h p ∧
    cwPhaseEarlierPublished ring h p
      (PPL.cyclicOffset ring h.root target)

/-- repair.tex:983-996, SUM. Every old-bit/tap source is recorded;
the first source is excluded from the marker trailing AND. -/
def cwPhaseSum {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  ∃ (site target : Fin n) (idx : Fin (c.t + 1))
      (z parity trailing : Bool),
    h.phase = .worker ∧
    h.workerKind target = .target target true ∧
    h.workerCursor site = .sum target idx z parity trailing ∧
    (p site).si.kind = .OFF ∧ (p site).si.cur = .SUM ∧
    (p site).si.j = idx ∧ (p site).si.z = z ∧
    (p site).si.p = parity ∧ (p site).si.a = trailing ∧
    h.sumReads.count.val = idx.val ∧
    (∀ j : Fin c.t, j.val < idx.val →
      h.sumReads.entries j =
        some {
          source := PPL.shiftRight ring h.root
            (PPL.cyclicOffset ring h.root target - c.t + j.val),
          oldBit := cwSourceBit ring h.root p
            (PPL.cyclicOffset ring h.root target) j.val,
          tap := c.taps j.val }) ∧
    z = cwSumOr ring h.root p
      (PPL.cyclicOffset ring h.root target) idx.val ∧
    parity = cwSumParity ring h.root p
      (PPL.cyclicOffset ring h.root target) idx.val ∧
    trailing = cwSumTrailing ring h.root p
      (PPL.cyclicOffset ring h.root target) idx.val ∧
    cwPhaseInitialPublished ring h p ∧
    cwPhaseEarlierPublished ring h p
      (PPL.cyclicOffset ring h.root target)

/-- repair.tex:996-1003: S1 has completed the target; A1/A0
has not yet moved/retired the ready worker. -/
def cwPhaseReady {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  ∃ target : Fin n,
    h.phase = .worker ∧
    h.workerKind target = .ready target ∧
    (p target).si.kind = .ROOT ∧
    (p target).si.busy = false ∧
    (p target).si.cur = .NONE ∧
    cwPhaseInitialPublished ring h p ∧
    cwPhaseEarlierPublished ring h p
      (PPL.cyclicOffset ring h.root target + 1)

/-- The old global static word/quietness package is demanded only
at DONE, never at a genuine I0 launch. -/
inductive CleanWorkerPhaseInv {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop where
  | «prefix» : cwPhasePrefix ring h p → CleanWorkerPhaseInv ring h p
  | back : cwPhaseBack ring h p → CleanWorkerPhaseInv ring h p
  | sum : cwPhaseSum ring h p → CleanWorkerPhaseInv ring h p
  | ready : cwPhaseReady ring h p → CleanWorkerPhaseInv ring h p
  | done : h.phase = .done → CleanWorkerInv ring h p →
      CleanWorkerPhaseInv ring h p

/-- Establish zero visited follower sites, without prescribing any
preexisting visible U/beta values. -/
theorem cwPhaseLaunchFromShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (h : BlockA.WordControl n c) (p : Fin n → ProjW c)
    (shape : CleanLaunchShape ring root h p) :
    cwPhasePrefix ring h p := by
  refine ⟨root, 0, false, true, shape.phase,
    shape.rootTag, shape.prefixLedgerEmpty,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [cwPhasePrefixPhysical, shape.rootPhysical, launchPrefix]
  · simp [cwPrefixOr]
  · simp [cwPrefixAnd]
  · intro j hj
    exact False.elim (Nat.not_lt_zero j.val hj)
  · intro k hk hle _hlt
    have hz : k.val = 0 := Nat.eq_zero_of_le_zero hle
    rw [hz] at hk
    cases hk
  · intro i hi
    obtain ⟨htag, hfree⟩ := shape.otherSites i hi
    exact ⟨htag, shape.cursorsEmpty i, hfree⟩

/-- Genuine I0: combine the compiled wordT and physical launch
lemmas, not a mere post-state pattern match. -/
theorem cwPhaseIZeroEstablishment {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (clean : CleanIZero ring h p e) :
    CleanWorkerPhaseInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  rw [cleanI0_wordT ring h p e (phiW ring p e) clean]
  exact CleanWorkerPhaseInv.prefix
    (cwPhaseLaunchFromShape ring h.root (BlockA.wordWorkerLaunch h)
      (phiW ring p e)
      (cwI0EstablishesLaunchShape ring h p e hne clean))

/-- This is the SAME real five-site I0 toy that refuted the
old invariant; its CleanIZero witness was kernel decided. -/
theorem cwToyPhaseEstablishment :
    CleanWorkerPhaseInv cwToyRing
      (BlockA.wordT cwToyRing cwToyControl cwToyProjection
        (0 : Fin 5)
        (phiW cwToyRing cwToyProjection (0 : Fin 5)))
      (phiW cwToyRing cwToyProjection (0 : Fin 5)) := by
  exact cwPhaseIZeroEstablishment cwToyRing cwToyControl
    cwToyProjection (0 : Fin 5) (by decide) cwToyIsIZero

/-- In DONE, exclude the four running cases and reuse the existing
static word and row-quietness implication. -/
theorem cwPhaseDoneValues {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hdone : h.phase = .done)
    (inv : CleanWorkerPhaseInv ring h p) :
    CleanWorkerWordValues ring h.root p ∧ WordRowsQuiet ring p := by
  cases inv with
  | «prefix» hp =>
      rcases hp with ⟨_, _, _, _, hw, _⟩
      cases hw.symm.trans hdone
  | back hb =>
      rcases hb with ⟨_, _, _, hw, _⟩
      cases hw.symm.trans hdone
  | sum hs =>
      rcases hs with ⟨_, _, _, _, _, _, hw, _⟩
      cases hw.symm.trans hdone
  | ready hr =>
      rcases hr with ⟨_, hw, _⟩
      cases hw.symm.trans hdone
  | done _ full =>
      exact ⟨full.wordValues,
        cleanWorkerInv_wordRowsQuiet ring h p full⟩

theorem cwPhaseDoneFirstStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e)
    (hdone : h.phase = .done)
    (inv : CleanWorkerPhaseInv ring h p) :
    ∀ e i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i := by
  exact wordRowsQuiet_first_step ring p hne
    (cwPhaseDoneValues ring h p hdone inv).2

/-- The P1 OLD read advances precisely its OR/AND fold and count.
The physical P1 site/ledger handoff is a separate obligation. -/
theorem cwPhasePrefixMoveFold (reads : List Bool) (oldBit : Bool) :
    (prefixAuditOf (reads ++ [oldBit])).count =
        (prefixAuditOf reads).count + 1 ∧
    (prefixAuditOf (reads ++ [oldBit])).z =
        ((prefixAuditOf reads).z || oldBit) ∧
    (prefixAuditOf (reads ++ [oldBit])).a =
        ((prefixAuditOf reads).a && oldBit) := by
  simp [prefixAudit_snoc, prefixAuditStep]

theorem cwPhasePrefixMoveZero (j t : Nat) (h : j < t) :
    (if j < t then false else true) = false := by
  simp [h]

/-- Exact OLD row classifications, rather than value coincidence. -/
theorem cwPhasePrefixMoveRow {c : Compiled} (x y : ProjW c)
    (hrow : (workerW x y).row = "P1") :
    BlockA.workerCase x y = .prefixMove := by
  simp [BlockA.workerCase, hrow]

theorem cwPhasePrefixTerminalRow {c : Compiled} (x y : ProjW c)
    (hrow : (workerW x y).row = "P2") :
    BlockA.workerCase x y = .prefixTerminal := by
  simp [BlockA.workerCase, hrow]

theorem cwPhasePrefixPublishRow {c : Compiled} (x y : ProjW c)
    (hrow : (workerW x y).row = "P3") :
    BlockA.workerCase x y = .prefixPublish := by
  simp [BlockA.workerCase, hrow]

/-- Installed wordWorkerNext cancels P2; it does not perform a
normal PREFIX->BACK transition. -/
theorem cwPhasePrefixTerminalCancels {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixTerminal) :
    BlockA.wordWorkerNext ring h p e request =
      BlockA.wordClear h request := by
  simp [BlockA.wordWorkerNext, hcase]

/-- P3: the kicked all-zero OLD prefix gives a nonzero NEW window. -/
theorem cwPhasePrefixPublishNonzero (z oldBit : Bool) :
    (z || prefixKick z oldBit) = true :=
  prefixKick_nonzero z oldBit

theorem cwPhasePrefixMoveReceipt {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (j : Fin n) :
    (BlockA.wordPut h.publications j .prefixZero) j = .prefixZero ∧
    (BlockA.wordPut h.visibleReceipts j true) j = true ∧
    (BlockA.wordPut h.prefixMarkers j true) j = true := by
  simp [BlockA.wordPut]

theorem cwPhasePrefixPublishReceipt {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (j : Fin n)
    (idx : Fin (c.t + 1)) :
    (BlockA.wordPut h.publications j .prefixEnd) j = .prefixEnd ∧
    (BlockA.wordPut h.visibleReceipts j true) j = true ∧
    (BlockA.wordPut h.workerCursor j (.back j idx)) j =
      .back j idx := by
  simp [BlockA.wordPut]

/-- An OLD F frame changes only the requested monitor flag. -/
theorem cwPhaseWorkerFrameControl {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .frame) :
    BlockA.wordWorkerNext ring h p e request =
      { h with requested := request } := by
  simp [BlockA.wordWorkerNext, hcase]

/-- Actual frame-case conditional prefix transport. The physical
premises are stated explicitly, not inferred from F alone. -/
theorem cwPhasePrefixFrameOfUnchangedFields
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool)
    (stage : cwPhasePrefix ring h p)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .frame)
    (hv : ∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i)
    (hsi : ∀ i : Fin n,
      ((phiW ring p e) i).si = (p i).si) :
    cwPhasePrefix ring
      (BlockA.wordWorkerNext ring h p e request)
      (phiW ring p e) := by
  rw [cwPhaseWorkerFrameControl ring h p e request hcase]
  rcases stage with
    ⟨site, idx, z, a, hphase, htag, hcount,
      hphysical, hor, hand, hreads, hpublished, hothers⟩
  refine ⟨site, idx, z, a, hphase, htag, hcount,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [cwPhasePrefixPhysical, hsi site] using hphysical
  · rw [cwPrefixOr_congr ring h.root (phiW ring p e) p hv idx.val]
    exact hor
  · rw [cwPrefixAnd_congr ring h.root (phiW ring p e) p hv idx.val]
    exact hand
  · intro j hj
    have hbit := cwBit_congr ring h.root
      (phiW ring p e) p hv (j.val + 1)
    simpa only [hbit] using hreads j hj
  · intro k hk hle hlt
    rcases hpublished k hk hle hlt with
      ⟨hpub, hvis, hflag, hbeta⟩
    refine ⟨hpub, hvis, hflag, ?_⟩
    rw [cwMarker_congr ring h.root
      (phiW ring p e) p hv k.val]
    exact hbeta
  · intro i hi
    rcases hothers i hi with ⟨ht, hc, hf⟩
    refine ⟨ht, hc, ?_⟩
    simpa only [hsi i] using hf

end CleanWorker
end WordEntrance
end AcceptedReceipts
end L3

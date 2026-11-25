import Leader.L4.BStarCopyDownstream
import Leader.L4.BStarGeneratedBandScan

namespace L4.BStarCopyGateAuthority
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongTransport BStarLongLiteral
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarAcquireForwardTrace
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetChartService BStarLongDoor
open BStarCopyOwnedFrozen BStarCopyEntryGates BStarClearanceDataChart BStarGeneratedBandScan
open BStarLongFixedRouting BStarLongEvents BStarResetChartIndex BStarAcquireRailCoverage BStarLongPackets
private theorem bind_back (g : LongGeometry) (j : Fin 11) (t : Token) (p : Payload)
    (E : BStarLongCommand.bind g j t=.forward p) (H : p.fault=0) :
    ∃ q, t=.forward q ∧ q.fault=0 ∧ q.opcode=p.opcode := by
  have no : fault false ≠ .forward p := by
    intro e
    unfold fault at e
    cases e
    contradiction
  cases t with
  | empty => contradiction
  | trail => contradiction
  | reply q =>
    simp only [BStarLongCommand.bind] at E
    split at E
    · contradiction
    · split at E <;> contradiction
  | forward q =>
    let n := q.opcode.toNat
    let r := q.race.toNat
    let ok := if gate n j g then decide (1≤r ∧ r≤5) else r==0
    change (if q.fault != 0 || decide (n≥413) || q.outcome != 0 || !ok then fault false
      else match forwardWidth n q.argument.toNat with
        | none => fault false
        | some w => .forward (cropped q w))=.forward p at E
    split at E
    · exact (no E).elim
    · split at E
      · exact (no E).elim
      · cases E
        exact ⟨q,rfl,H,rfl⟩

private theorem depart_origin (g : LongGeometry) (j : Fin 11) (p q : Payload)
    (H : depart g j p=some q) (F : q.fault=0) : p.fault=0 ∧ p.opcode=q.opcode := by
  unfold depart at H
  split at H
  · dsimp only at H
    split at H
    · contradiction
    · cases H; exact ⟨F,rfl⟩
  · cases H; exact ⟨F,rfl⟩

theorem checked_opcode_origin (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload)
    (G : (c,.advance p)∈gated g raw) (clean : p.fault=0) :
    ∃ q, readK raw c.source=.forward q ∧ q.fault=0 ∧ q.opcode=p.opcode := by
  have E := ((gated_mem g raw c _).mp G).2.symm
  have src : classifyOld g raw c=.advance p := by
    unfold gatedAt at E
    generalize K : classifyOld g raw c=o at E ⊢
    cases o <;> simp only [checkOffer] at E
    all_goals try contradiction
    rename_i q
    split at E
    · exact E
    · contradiction
    · cases E; contradiction
  let G := geometry g c.source.side
  let old := BStarLongCommand.bind G c.source.occurrence (readK raw c.source)
  let dst := (c.destination.map (bound g (readK raw))).getD .empty
  change classify c G old dst=.advance p at src
  unfold classify at src
  split at src
  · contradiction
  · cases E : old with
    | forward q =>
      rw [E] at src
      change (match depart G c.source.occurrence q with
        | none => Offer.hold | some v => Offer.advance v) = Offer.advance p at src
      cases D : depart G c.source.occurrence q with
      | none => simp [D] at src
      | some z =>
        rw [D] at src
        have eq := Offer.advance.inj src
        subst z
        obtain ⟨good,opc⟩ := depart_origin _ _ _ _ D clean
        exact bind_back _ _ _ _ E good |>.imp (fun q H => ⟨H.1,H.2.1,H.2.2.trans opc⟩)
    | empty =>
      rw [E] at src
      cases hc : c.kind <;> cases dstEq : dst <;> simp_all
    | trail =>
      rw [E] at src
      cases hc : c.kind <;> cases dstEq : dst <;> simp_all
    | reply q =>
      rw [E] at src
      cases hc : c.kind <;> cases dstEq : dst <;> simp_all

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "P" => production k₁ k₂ t₂ J₁ J₂ r c p c₁
local notation "X" => Fin n → LargeSite P
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Every winning preparation on this physical lane comes from the
actual controller's current healthy command, on its own historical
source launch. A foreign owner cannot write the gate. -/
theorem winning_prep_pc {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (e : Fin n) (a : BStarLongPrep.Offer)
    (own : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val)
    (win : a∈(arbitration (round (oldPair B (play x w) e)
      (((play x w) e).long,((play x w) (rightNeighbor e)).long)).prep).1) :
    prepOf (pc (play x w) (S.getD 0 fall).1)=some a.claim.op := by
  let y := play x w
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  obtain ⟨C,f,q,H,move,O,clean,_,A⟩ := winner_owner hp y e a win
  have eq : oldH6 B y=oldH6 B base := funext fun t => (congrArg Prod.fst (layout t)).symm
  rw [eq,own] at A
  obtain ⟨p,rawF,pClean,fOp⟩ := checked_opcode_origin g raw C f H clean
  cases m with
  | idle =>
    have cmem := ((gated_mem g raw C _).mp H).1
    have lens := chart.length
    let u : Pos n := address e C.source
    have uS : u∈S := by
      rcases selected_endpoint_or_link B base y hh layout o e C cmem A with ⟨_,_,R⟩|⟨_,_,R⟩|⟨d,dst,_⟩
      · change u=endpoint (oldH6 B base) hh o 0 at R
        rw [R,←chart.root,←List.getElem_eq_getD (h:=show 0<S.length by omega)]
        exact List.getElem_mem _
      · change u=endpoint (oldH6 B base) hh o 10 at R
        rw [R,←chart.terminal,←List.getElem_eq_getD (h:=show len<S.length by omega)]
        exact List.getElem_mem _
      · have bm := command_eq B y base (fun i => (layout i).symm) e ▸ cmem
        have act := (BStarAcquireChainEndpoints.link_endpoints _ C d bm dst).1
        apply chart.cover _ _ A
        cases hs : C.source.side <;> simpa [u,address,site,hs,geometry,oldPair] using act
    obtain ⟨k,hK,U⟩ := List.getElem_of_mem uS
    have U : S.getD k fall=u := (List.getElem_eq_getD _).symm.trans U
    have zero := now.2 k (by omega)
    change atCursor y (S.getD k fall)=.empty at zero
    rw [U] at zero
    exact Token.noConfusion (rawF.symm.trans ((old_read y e _).trans zero))
  | busy op z =>
    obtain ⟨j,J,K⟩ := actual_owner_departure hp chart layout e C q z move A now.2.1 now.2.2
    subst z
    have F : project (fun t => S.getD t fall) y j=.forward p := by
      change atCursor y (S.getD j fall)=_
      rw [K]; exact (old_read y e _).symm.trans rawF
    have E := (healthy_forward_origin hp chart sep hist now j now.2.1.1 p F f.opcode.toNat pClean
      (congrArg BitVec.toNat fOp)).1
    have opEq : op=f.opcode.toNat := by injection E
    have PC := now.1.2.2.2.trans opEq
    change pc y (S.getD 0 fall).1=f.opcode.toNat at PC
    rw [PC]; exact O

private theorem no_stop_code (k : Nat) (a : Prep) (H : prepOf k=some a)
    (h0 : k≠0) (h6 : k≠6) : a≠.stop ∧ a≠.rstop := by
  unfold prepOf at H
  split at H <;> simp_all
  all_goals subst a; decide

theorem generated_no_stop {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (e i : Fin n) (sh : Sheet) (own : dataOwner (oldH6 B base) i sh=o.val)
    (pc0 : pc (play x w) (S.getD 0 fall).1≠0)
    (pc6 : pc (play x w) (S.getD 0 fall).1≠6) :
    NoGateStop hp (play x w) e i sh := by
  intro s loc a win lane
  apply no_stop_code _ _
    (winning_prep_pc hp chart sep hist now layout e a (by rw [lane,loc]; exact own) win)
    pc0 pc6

/-- The true old gate at an INJECT mark follows from a selected earlier
ENABLE on the same physical lane and actual recovered histories with
the source PC excluding RSTOP/STOP. No guard about other owners is
assumed. -/
theorem gate_from_selected_enable {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (before between : List (Fin n)) (allow : Fin n) (a : BStarLongPrep.Offer)
    (ena : a.claim.op=.enable)
    (win : a∈(arbitration (round (oldPair B (play x before) allow)
      (((play x before) allow).long,((play x before) (rightNeighbor allow)).long)).prep).1) :
    let i := site allow a.claim.lane.side
    let sh := a.claim.lane.occurrence
    let began := step (play x before) allow
    dataOwner (oldH6 B base) i sh=o.val →
    (∀ u e v, between=u++e::v →
      ∃ m, GeneratedOwner hp base (fun j => S.getD j fall) len x .idle
        (before++allow::u) m ∧ Current hp base (fun j => S.getD j fall) len (play began u) m) →
    (∀ u e v, between=u++e::v → ∀ i,
      BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play began u) i) →
    (∀ u e v, between=u++e::v →
      pc (play began u) (S.getD 0 fall).1≠0 ∧ pc (play began u) (S.getD 0 fall).1≠6) →
    (readLane (Sheet.index sh) (play began between i).long).gate=true := by
  dsimp only
  intro own hist layout safe
  let began := step (play x before) allow
  let i := site allow a.claim.lane.side
  let sh := a.claim.lane.occurrence
  have enabled : (readLane (Sheet.index sh) (began i).long).gate=true :=
    congrArg Lane.gate (ring_enable hp (play x before) allow (sep allow) a ena win)
  apply gate_word hp began i sh between sep enabled
  intro u e v eq
  obtain ⟨m,G,I⟩ := hist u e v eq
  obtain ⟨no0,no6⟩ := safe u e v eq
  have replay : play x (before++allow::u)=play began u := by
    rw [BStarResetSchedule.run_append]; rfl
  have N := generated_no_stop hp chart sep G
  rw [replay] at N
  exact N I (layout u e v eq) e i sh own no0 no6

theorem history_prefix {base x : X} {addr : Nat → Pos n} {len : Nat}
    {m fin : Mode} (pre post : List (Fin n))
    (G : GeneratedOwner hp base addr len x m (pre++post) fin) :
    ∃ now, GeneratedOwner hp base addr len x m pre now ∧
      Current hp base addr len (play x pre) now := by
  induction pre generalizing x m with
  | nil =>
    cases G with
    | endpoint I => exact ⟨_,.endpoint I,I⟩
    | next I _ _ => exact ⟨_,.endpoint I,I⟩
  | cons e w ih =>
    cases G with
    | next I E tail =>
      obtain ⟨now,hist,I'⟩ := ih tail
      exact ⟨now,.next I E hist,I'⟩

/-- A selected ENABLE stays enabled through one actual whole history
whenever the enabled owner does not revisit an old STOP opcode. -/
theorem gate_actual_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead rest : List (Fin n)) (enable : Fin n) (a : BStarLongPrep.Offer) (m : Mode)
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle (lead++enable::rest) m)
    (ena : a.claim.op=.enable)
    (win : a∈(arbitration (round (oldPair B (play x lead) enable)
      (((play x lead) enable).long,((play x lead) (rightNeighbor enable)).long)).prep).1) :
    let i := site enable a.claim.lane.side
    let sh := a.claim.lane.occurrence
    let began := step (play x lead) enable
    dataOwner (oldH6 B base) i sh=o.val →
    (∀ u e v, rest=u++e::v → ∀ k,
      BStarLongFixedRouting.Layout B base k=BStarLongFixedRouting.Layout B (play began u) k) →
    (∀ u e v, rest=u++e::v →
      pc (play began u) (S.getD 0 fall).1≠0 ∧ pc (play began u) (S.getD 0 fall).1≠6) →
    (readLane (Sheet.index sh) (play x (lead++enable::rest) i).long).gate=true := by
  dsimp only
  intro own layout safe
  have replay : play x (lead++enable::rest)=play (step (play x lead) enable) rest := by
    rw [BStarResetSchedule.run_append]; rfl
  rw [replay]
  refine gate_from_selected_enable hp chart sep lead rest enable a ena win own ?_ layout safe
  intro u e v eq
  have whole : lead++enable::rest=(lead++enable::u)++e::v := by
    rw [eq,List.append_assoc,List.cons_append]
  have H := history_prefix hp (lead++enable::u) (e::v) (whole ▸ G)
  obtain ⟨now,hist,I⟩ := H
  refine ⟨now,hist,?_⟩
  rw [BStarResetSchedule.run_append] at I
  exact I

end L4.BStarCopyGateAuthority

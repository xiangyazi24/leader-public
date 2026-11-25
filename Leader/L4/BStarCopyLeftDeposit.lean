import Leader.L4.BStarCopyLeftMark
import Leader.L4.BStarCopyDownstream

namespace L4.BStarCopyLeftDeposit
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongCommandData BStarLongPrep BStarLongPackets BStarCopyFIFO
open BStarCopyFenceSaturation BStarCopyMarkedLedger BStarCopyDownstream BStarCopyLeftStrip BStarCopyLeftMark
open BStarCopyRightStrip (addr addr_next)
open BStarAcquireVisitOrder BStarResetChartTouch BStarAcquireLiteralChain

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

theorem k5_body (g : Pair LongGeometry) (body : g.2.axes.h6=false) :
    link (R 5) (L 5)∈orderedCommands g := by
  have F (I L J : Bool) :
      link (R 5) (BStarLongClaims.L 5)∈orderedCommands (geo false I L,geo false J false) := by
    cases I <;> cases L <;> cases J <;> decide +kernel
  let v := (geo false g.1.inside g.1.last,geo g.2.axes.h6 g.2.inside false)
  change link (R 5) (L 5)∈orderedCommands v
  have E : v=(geo false g.1.inside g.1.last,geo false g.2.inside false) := by simp [v,body]
  rw [E]
  exact F _ _ _

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- K5 command order is decreasing along the source LS word. If K5
has not yet departed here, every address behind this deposition in
data travel is still on the actual unvisited chart suffix. -/
theorem all_behind_unvisited {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (a : Fin n) (seam width i cut : Nat)
    (C : Strip B base a seam width) (hi : i<seam)
    (current : Unvisited S fall len cut false (addr a i)) :
    ∀ j, j≤i → Unvisited S fall len cut false (addr a j) := by
  have descend (k : Nat) (K : k≤i) : Unvisited S fall len cut false (addr a (i-k)) := by
    induction k with
    | zero => simpa using current
    | succ k ih =>
      let j := i-(k+1)
      have next : i-k=j+1 := by dsimp [j]; omega
      obtain ⟨q,hq,ql,Q⟩ := ih (by omega)
      rw [next] at Q
      have right := addr_next a j
      have body : (oldPair B base (addr a j)).2.axes.h6=false := by
        change oldH6 B base (rightNeighbor (addr a j))=false
        rw [←right]
        exact C.ls_body _ (by omega) (by omega)
      let u : Pos n := (addr a (j+1),5)
      let v : Pos n := (addr a j,5)
      have edge : Edge B base u v := ⟨addr a j,link (R 5) (L 5),L 5,
        k5_body _ body,rfl,Prod.ext right rfl,rfl⟩
      have lens := chart.length
      have qs : q<S.length := by omega
      have U : S.getD q fall=u := Q
      have uS : u∈S := by
        rw [←U,←List.getElem_eq_getD (h:=qs)]
        exact List.getElem_mem _
      obtain ⟨l,L,F,G⟩ := chart.edge u v uS edge
      have eq : l=q := (List.getD_inj (by omega) qs chart.nodup).mp (by
        rw [←List.getElem_eq_getD (h:=show l<S.length by omega),F,U])
      subst l
      exact ⟨q+1,by omega,by omega,(List.getElem_eq_getD _).symm.trans G⟩
  intro j J
  simpa only [show i-(i-j)=j by omega] using descend (i-j) (by omega)

theorem empty_behind_cut {Tag : Type} (digits : Tag→BitVec 36) (x : X) (a : Fin n)
    (seam i len cut : Nat) (hi : i<seam) (S : List (Pos n)) (fall : Pos n)
    (labels : Nat→Option Tag) (matched : UpstreamMatches digits x a seam labels)
    (vacant : CutVacant x S fall len cut false)
    (behind : ∀ j≤i,Unvisited S fall len cut false (addr a j)) :
    ∀ j≤i, labels j=none := by
  intro j J
  have A := matched j (by omega)
  have H := vacant _ (behind j J)
  unfold sample at A
  rw [rail,if_pos (show j<seam by omega)] at A
  change (readLane (Sheet.index .ls) (x (addr a j)).long).mobile=.empty at H
  rw [H] at A
  cases E : labels j with
  | none => rfl
  | some z => rw [E] at A; contradiction

def deposit {Tag : Type} (labels : Nat→Option Tag) (i : Nat) (tag : Tag) (j : Nat) :=
  if j=i then some tag else labels j

def headFirst {Tag : Type} (seam : Nat) (labels : Nat→Option Tag) : List Tag :=
  (upstreamWord seam labels).reverse

theorem append_at_cut {Tag : Type} (labels : Nat→Option Tag) (seam i : Nat)
    (hi : i<seam) (tag : Tag) (empty : ∀ j≤i,labels j=none) :
    headFirst seam (deposit labels i tag)=headFirst seam labels++[tag] := by
  have E : List.range seam=List.range' 0 i ++ i::List.range' (i+1) (seam-i-1) := by
    rw [List.range_eq_range',show seam=i+(seam-i-1+1) by omega,←List.range'_append]
    simp only [Nat.one_mul,Nat.zero_add]
    rw [List.range'_succ]
    rw [show i + (seam-i-1+1)-i-1=seam-i-1 by omega]
  have F : (List.range' 0 i).flatMap (fun j => (labels j).toList)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j M
    obtain ⟨k,K,P⟩ := List.mem_range'.mp M
    rw [empty j (by omega)]
    rfl
  have fl (q : List Nat) (safe : ∀ j∈q,j≠i) :
      q.flatMap (fun j => (deposit labels i tag j).toList)=
      q.flatMap (fun j => (labels j).toList) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro j J
    simp [deposit,safe j J]
  have p := fl (List.range' 0 i) (by
    intro j M; obtain ⟨k,K,P⟩ := List.mem_range'.mp M; omega)
  have q := fl (List.range' (i+1) (seam-i-1)) (by
    intro j M; obtain ⟨k,K,P⟩ := List.mem_range'.mp M; omega)
  unfold headFirst upstreamWord
  rw [E,List.flatMap_append,List.flatMap_append,p,F]
  simp only [List.nil_append,List.flatMap_cons,q,empty i (Nat.le_refl _),Option.toList_none]
  simp [deposit,List.reverse_cons]

/-- Same-mark old physical deposition and head-first ledger append.
This projects the deposition only; if this mark also crosses the
seam head, the crossing ledger update must be applied separately. -/
theorem deposit_at_cut {Tag : Type} (digits : Tag→BitVec 36) (tag : Tag)
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (a : Fin n) (seam width i cut : Nat)
    (C : Strip B base a seam width) (hi : i<seam)
    (current : Unvisited S fall len cut false (addr a i))
    (e : Fin n) (side : Side) (loc : site e side=addr a i) (sep : e≠rightNeighbor e)
    (labels : Nat→Option Tag) (matched : UpstreamMatches digits x a seam labels)
    (vacant : CutVacant x S fall len cut false)
    (winner : BStarCopyInjection.injection side false∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1)
    (gate : (sample x a seam i).gate=true)
    (frozen : (sample x a seam i).frozen=.data (digits tag))
    {plan : List Tag} {s : Ledger Tag} (todo : List Tag)
    (old : OrderedPrefix plan s (headFirst seam labels)) (next : s.release.pending=tag::todo) :
    (sample (step x e) a seam i).mobile=encode digits (some tag) ∧
    (sample (step x e) a seam i).frozen=encode digits none ∧
    OrderedPrefix plan (s.releaseOne tag todo) (headFirst seam (deposit labels i tag)) := by
  have behind := all_behind_unvisited hp chart a seam width i cut C hi current
  have emptyLabels := empty_behind_cut digits x a seam i len cut hi S fall labels matched vacant behind
  have E := vacant _ current
  unfold sample at gate frozen ⊢
  rw [rail,if_pos hi] at gate frozen ⊢
  have G := loc.symm ▸ gate
  have F := loc.symm ▸ frozen
  have A := loc.symm ▸ E
  have done := BStarCopyOperand.ring_inject hp x e sep side false (digits tag) winner G F A
  change readLane (Sheet.index .ls) (step x e (site e side)).long=_ at done
  rw [loc] at done
  rw [append_at_cut labels seam i hi tag emptyLabels]
  exact ⟨congrArg Lane.mobile done,congrArg Lane.frozen done,.mark old (.issue s _ tag todo next)⟩

/-- Strong ordinary-mark wrapper. Other LS slots either are off the
pair or must have no old emitted writes; LD effects need not be absent. -/
theorem upstream_of_deposition {Tag : Type} (digits : Tag→BitVec 36) (tag : Tag)
    (x : X) (e a : Fin n) (seam i : Nat) (sep : e≠rightNeighbor e)
    (labels : Nat→Option Tag) (old : UpstreamMatches digits x a seam labels)
    (write : (sample (step x e) a seam i).mobile=encode digits (some tag))
    (quiet : let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      ∀ j<seam, j≠i → ∀ z : At Sheet, site e z.side=addr a j → z.occurrence=.ls →
        z∉reserved (round g raw).prep ∧
        ∀ d∈orderedData g (reserved (round g raw).prep),
          ∀ leaf,(z,leaf)∉dataEffects g (view raw) d) :
    UpstreamMatches digits (step x e) a seam (deposit labels i tag) := by
  intro j J
  by_cases E : j=i
  · subst j
    rw [deposit,if_pos (rfl : i=i)]
    exact write
  · have A := spectator hp x e a seam j sep (by
      dsimp only
      intro z Z R
      change z.occurrence = rail seam j at R
      rw [rail,if_pos J] at R
      exact quiet j J E z Z R)
    rw [A,deposit,if_neg E]
    exact old j J

/-- At the sole-H6 seam, the healthy selected old LS→LD hop and the
winning new LS deposit have disjoint slots. These equalities refer to
one joined physical mark, so the new deposit cannot be the old head. -/
theorem seam_parallel {Tag : Type} (digits : Tag→BitVec 36) (head fresh : Tag)
    (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (winner : BStarCopyInjection.injection .right false∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1)
    (gate : (readLane (Sheet.index .ls) (x (rightNeighbor e)).long).gate=true)
    (frozen : (readLane (Sheet.index .ls) (x (rightNeighbor e)).long).frozen=.data (digits fresh))
    (empty : (readLane (Sheet.index .ls) (x (rightNeighbor e)).long).mobile=.empty) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let u := L .ls
    let v := R .ld
    hop u v∈orderedData g (reserved (round g raw).prep) →
    (view raw u).mobile=encode digits (some head) →
    let out := view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e))))
    let H := hopEffects (view raw u) (view raw v) (retains g v)
    (readLane (Sheet.index .ls) (step x e (rightNeighbor e)).long).mobile=encode digits (some fresh) ∧
    out u=typedLeaves (view raw u) H.1 ∧ out v=typedLeaves (view raw v) H.2 := by
  dsimp only
  intro M _
  have D := BStarCopyOperand.ring_inject hp x e sep .right false (digits fresh) winner gate frozen empty
  have N : L Sheet.ls≠R .ld := by intro E; cases congrArg At.side E
  exact ⟨congrArg Lane.mobile D,joined_exact hp (x e,x (rightNeighbor e)) _ _ N M⟩

/-- Serialization of the disjoint seam actions at the ledger level.
The credit for the head is from the old ledger, before the append. -/
theorem parallel_prefix {Tag : Type} {plan : List Tag} {s : Ledger Tag}
    (head fresh : Tag) (up todo : List Tag)
    (P : OrderedPrefix plan s (head::up))
    (vacant : (s.cells 0).mobile=none) (pending : s.release.pending=fresh::todo) :
    OrderedPrefix plan ((s.receiveFirst head).releaseOne fresh todo) (up++[fresh]) := by
  have credit := BStarCopyUpstreamTags.old_head_credit head up P
  exact .mark (.mark P (.cross s up head vacant credit)) (.issue _ up fresh todo pending)

end L4.BStarCopyLeftDeposit

import Leader.L4.BStarAcquireRailCoverage

namespace L4.BStarClearanceDataChart
open AllSizeProtocol BStarLongClaims BStarH6WordChart
open BStarAcquireRailCoverage BStarLongFiberOwner

def activeSheet (g : LongGeometry) : Sheet → Bool
  | .ls | .rd => true
  | .ld | .rs => g.inside

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

def expectedLeft (g : LongGeometry) : List Sheet :=
  [.ls] ++ (if g.inside then [.ld] else [])

def expectedRight (g : LongGeometry) : List Sheet :=
  [.rd] ++ (if g.inside then [.rs] else [])

/-- Across the two actual ports, each active data slot has exactly
one outgoing service claim before preparation reservations. LS and
LD depart on the site's right edge, whereas RS and RD depart on its
left edge. Inactive LD/RS have no outgoing service. -/
theorem service_ports (l m r : LongGeometry)
    (H : (!m.axes.h6 || m.inside)=true) (Rh : (!r.axes.h6 || r.inside)=true)
    (Q : continuation l m=true) (S : continuation m r=true) (s : Sheet) :
    ((orderedData (l,m) []).filter (fun d => d.source == R s)).length =
      (expectedRight m).count s ∧
    ((orderedData (m,r) []).filter (fun d => d.source == L s)).length =
      (expectedLeft m).count s := by
  have F (li ll mh mi ml rh ri : Bool) :
      (!mh || mi)=true → (!rh || ri)=true →
      continuation (geo false li ll) (geo mh mi ml)=true →
      continuation (geo mh mi ml) (geo rh ri false)=true →
      ∀ s : Sheet,
        ((orderedData (geo false li ll,geo mh mi ml) []).filter
          (fun d => d.source == R s)).length = (expectedRight (geo mh mi ml)).count s ∧
        ((orderedData (geo mh mi ml,geo rh ri false) []).filter
          (fun d => d.source == L s)).length = (expectedLeft (geo mh mi ml)).count s := by
    cases li <;> cases ll <;> cases mh <;> cases mi <;> cases ml <;> cases rh <;> cases ri <;>
      intro A B C D s <;> cases s <;> first | decide +kernel | contradiction
  exact F l.inside l.last m.axes.h6 m.inside m.last r.axes.h6 r.inside H Rh Q S s

private def terminalTest (g : Pair LongGeometry) (d : DataClaim) : Bool :=
  (d.destination.isNone) ==
    ((d.source == L .ld && ends g.1) || (d.source == R .rd && g.2.axes.h6))

/-- Terminal selection uses only genuine left LAST/LD or the old
right H6/RD. This applies to the actual selected list even on a mark
with preparation reservations; reservations may suppress a claim. -/
theorem terminal_case (g : Pair LongGeometry) (reserved : List (At Sheet))
    (d : DataClaim) (h : d∈orderedData g reserved) :
    d.destination.isNone =
      ((d.source == L .ld && ends g.1) || (d.source == R .rd && g.2.axes.h6)) := by
  obtain ⟨l,r⟩ := g
  have A (I T H J : Bool) :
      (dataClaims (geo false I T,geo H J false)).all
        (terminalTest (geo false I T,geo H J false))=true := by
    cases I <;> cases T <;> cases H <;> cases J <;> decide +kernel
  have raw := BStarLongFenceTopology.selected_data_raw (l,r) reserved d h
  change d∈dataClaims (geo false l.inside l.last,geo r.axes.h6 r.inside false) at raw
  exact beq_iff_eq.mp (List.all_eq_true.mp (A l.inside l.last r.axes.h6 r.inside) d raw)

/-- The physical modular owner of a data sheet. -/
def dataOwner {n : Nat} (h : Fin n → Bool) (i : Fin n) (s : Sheet) : Int :=
  owner (total h) (word h i) (dataDispl s)

/-- Any surviving physical data hop preserves its owner, for every
old reservation list. -/
theorem reserved_hop_owner {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (reserved : List (At Sheet))
    (C : DataClaim) (D : At Sheet) (hc : C∈orderedData (oldPair b x e) reserved)
    (hd : C.destination=some D) :
    dataOwner (oldH6 b x) (site e C.source.side) C.source.occurrence =
      dataOwner (oldH6 b x) (site e D.side) D.occurrence :=
  actual_data_owner b x e reserved C D hc hd

open BStarH6Ordinal

def clockwise : Sheet → Bool
  | .ls | .ld => true
  | .rs | .rd => false

def phase : Sheet → Nat
  | .ls | .rs => 1
  | .ld | .rd => 0

/-- A strictly decreasing service distance for data transfers.
The two outward sheet rails precede their respective destination
sheets. This is a ranking, not a count of enabled moves. -/
noncomputable def distance {n : Nat} (h : Fin n → Bool) (hh : ∃ j,h j=true)
    (i : Fin n) (s : Sheet) : Nat :=
  phase s*n + if clockwise s then n-1-ordinal h hh i else ordinal h hh i

private def hopTest (H : Bool) (C : DataClaim) : Bool :=
  match C.destination with
  | none => true
  | some D => decide (phase D.occurrence < phase C.source.occurrence) ||
    (C.source.occurrence == D.occurrence && !H &&
      if clockwise C.source.occurrence then
        C.source.side == .left && D.side == .right
      else C.source.side == .right && D.side == .left)

private theorem hop_test (g : Pair LongGeometry) (Rsv : List (At Sheet)) (C : DataClaim)
    (hc : C∈orderedData g Rsv) : hopTest g.2.axes.h6 C=true := by
  rcases g with ⟨x,y⟩
  have A (I T H J : Bool) :
      (dataClaims (geo false I T,geo H J false)).all (hopTest H)=true := by
    cases I <;> cases T <;> cases H <;> cases J <;> decide +kernel
  have raw := BStarLongFenceTopology.selected_data_raw (x,y) Rsv C hc
  change C∈dataClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false) at raw
  exact List.all_eq_true.mp (A x.inside x.last y.axes.h6 y.inside) C raw

private theorem block {n : Nat} (h : Fin n → Bool) (hh : ∃ j,h j=true)
    (i : Fin n) (s : Sheet) :
    phase s*n ≤ distance h hh i s ∧ distance h hh i s < (phase s+1)*n := by
  have H := (ordinal_spec h hh i).1
  unfold distance
  rw [Nat.add_mul]
  split <;> omega

/-- Every actual surviving physical hop decreases the ranked
distance in the very same fixed H6 chart. -/
theorem hop_decreases {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (hh : ∃ i, oldH6 b x i=true) (e : Fin n)
    (Rsv : List (At Sheet)) (C : DataClaim) (D : At Sheet)
    (hc : C∈orderedData (oldPair b x e) Rsv) (hd : C.destination=some D) :
    distance (oldH6 b x) hh (site e D.side) D.occurrence <
      distance (oldH6 b x) hh (site e C.source.side) C.source.occurrence := by
  have Q := hop_test _ Rsv C hc
  simp only [hopTest,hd,Bool.or_eq_true,decide_eq_true_eq] at Q
  rcases Q with J|J
  · have M := Nat.mul_le_mul_right n (show phase D.occurrence+1≤phase C.source.occurrence by omega)
    have A := (block _ hh (site e D.side) D.occurrence).2
    have C := (block _ hh (site e C.source.side) C.source.occurrence).1
    omega
  · simp only [Bool.and_eq_true,beq_iff_eq] at J
    obtain ⟨⟨eq,hs⟩,orient⟩ := J
    have Hs : oldH6 b x (rightNeighbor e)=false := by
      change (!oldH6 b x (rightNeighbor e))=true at hs
      cases T : oldH6 b x (rightNeighbor e) <;> simp_all
    have O := ordinal_body _ hh e Hs
    have N := (ordinal_spec _ hh (rightNeighbor e)).1
    rw [←eq]
    cases F : clockwise C.source.occurrence with
    | true =>
      simp [F] at orient
      simp only [distance,F,orient.1,orient.2,site,if_true]
      omega
    | false =>
      simp [F] at orient
      simp [distance,F,orient.1,orient.2,site,O]

#print axioms hop_decreases
#print axioms service_ports
#print axioms terminal_case
#print axioms reserved_hop_owner
end L4.BStarClearanceDataChart

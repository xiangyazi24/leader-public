import Leader.L4.BStarFenceLeftShadow

namespace L4.BStarFenceRightShadow
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarH6Ordinal BStarClearanceDataChart BStarGeneratedOwner BStarResetChartTouch
open BStarGeneratedBandScan BStarFenceOccupancy BStarFenceShadow BStarFencePorts
open BStarFenceFootprint BStarFenceLineGeometry
open BStarCopyRightStrip (addr addr_next)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def rightOcc (x : X) (root : Fin n) (d r' : Nat) (j : Fin (d+r')) : Bool :=
  occupied (readLane (BStarLongPackets.Sheet.index (rightRail d (rightCoord j)))
    (x (addr root (rightCoord j))).long)

private theorem addr_zero {n : Nat} (root : Fin n) : addr root 0=root :=
  Fin.ext (Nat.mod_eq_of_lt root.isLt)

/-- Reverse-ordered right line, all raw marks. END is on the incoming
edge of K10, and the rightmost clockwise RS cell has no ingress. -/
theorem right_mark {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (pc11 : pc (play x w) (S.getD 0 fall).1=11)
    {d r' : Nat}
    (F : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (tail : ends (longGeometry B (base (addr (S.getD len fall).1 (d+r'-1))))=true)
    (e : Fin n) :
    let root := (S.getD len fall).1
    Mark (rightPort root) e (rightOcc (play x w) root d r') (rightOcc (step (play x w) e) root d r') := by
  let q := play x w
  let y := step q e
  let root := (S.getD len fall).1
  let sh := rightRail d
  have rootOwner : commandOwner (oldH6 B base) root 10=o.val := by
    dsimp [root]
    rw [chart.terminal]
    exact (endpoint_spec _ hh o 10).2.1
  have own (i : Nat) (I : i<d+r') : dataOwner (oldH6 B base) (addr root i) (sh i)=o.val :=
    (right_owner F dp i I).trans rootOwner
  constructor
  · intro j h E
    let k := succIdx j h
    have L := (right_hop_endpoints root j h).1
    have R := (right_hop_endpoints root j h).2
    change e=rightPort root j at E
    have eL : e=addr root (rightCoord k) := E.trans L
    have eR : rightNeighbor e=addr root (rightCoord j) := by rw [E]; exact R
    have K : rightCoord k+1=rightCoord j := by
      have := j.isLt
      unfold rightCoord k succIdx
      dsimp only
      omega
    have J : rightCoord j<d+r' := by
      have := j.isLt
      unfold rightCoord
      omega
    let src := BStarLongClaims.R (sh (rightCoord j))
    let dst := BStarLongClaims.L (sh (rightCoord k))
    have N : hop src dst∈orderedData (oldPair B q e) [] := by
      rw [←data_eq B base q layout e,eL]
      have H := F.adjacent (rightCoord k) (by omega)
      rwa [K] at H
    have O : dataOwner (oldH6 B base) (rightNeighbor e) (sh (rightCoord j))=o.val := by
      rw [eR]
      exact own _ J
    have V := ring_owner_hop hp chart sep hist now layout pc11 e (hop src dst) dst N O
      rfl rfl (by intro eq; have T := congrArg At.side eq; contradiction)
      (rightOcc q root d r' j) (rightOcc q root d r' k)
    simp only [rightOcc] at V
    dsimp [src,dst] at V
    change
      (occupied (readLane (BStarLongPackets.Sheet.index (sh (rightCoord j))) (q (rightNeighbor e)).long)=true→_) →
      (occupied (readLane (BStarLongPackets.Sheet.index (sh (rightCoord k))) (q e).long)=true→_) →
      (occupied (readLane (BStarLongPackets.Sheet.index (sh (rightCoord j))) (y (rightNeighbor e)).long)=true→_) ∧
      (occupied (readLane (BStarLongPackets.Sheet.index (sh (rightCoord k))) (y e).long)=true→_) at V
    rw [eR,eL] at V
    exact V id id
  · intro j last E
    obtain ⟨port,idx⟩ := right_outlet root j last
    have mark := E.trans port
    have cell : rightNeighbor e=addr root (rightCoord j) := by
      rw [mark,RearTrace.right_predecessor,idx,addr_zero]
    have sheet : sh (rightCoord j)=.rd := by rw [idx]; exact if_pos dp
    have N : ending (R .rd)∈orderedData (oldPair B q e) [] := by
      rw [←data_eq B base q layout e,mark]
      exact right_terminal F
    have O : dataOwner (oldH6 B base) (rightNeighbor e) .rd=o.val := by
      rw [cell,←sheet]
      exact own _ (by have := j.isLt; unfold rightCoord; omega)
    have H := ring_owner_end hp chart sep hist now layout pc11 e (R .rd) N O
    change occupied (readLane (BStarLongPackets.Sheet.index .rd) (y (rightNeighbor e)).long)=false at H
    rw [cell,←sheet] at H
    exact H
  · intro j H noIn
    let p := rightCoord j
    have J := j.isLt
    have Q : p<d+r' := by dsimp [p,rightCoord]; omega
    have offR : rightNeighbor e≠addr root p := by
      intro E
      by_cases further : j.val+1<d+r'
      · have R := (right_hop_endpoints root j further).2
        have C := congrArg RearTrace.predecessor (E.trans R.symm)
        exact H (by simpa only [RearTrace.predecessor_right] using C)
      · obtain ⟨mark,idx⟩ := right_outlet root j further
        rw [show p=0 from idx,addr_zero] at E
        exact H ((RearTrace.predecessor_right e).symm.trans
          ((congrArg RearTrace.predecessor E).trans mark.symm))
    by_cases E : e=addr root p
    · have notIncoming : ¬p+1<d+r' := by
        intro I
        have P : 0<j.val := by dsimp [p,rightCoord] at I; omega
        have A : (predIdx j P).val+1<d+r' := by
          change j.val-1+1<d+r'
          omega
        have K : rightPort root (predIdx j P)=addr root p := by
          rw [rightPort,if_pos A]
          change addr root (d+r'-2-(j.val-1))=addr root p
          congr 1
          dsimp [p,rightCoord]
          omega
        exact noIn P (E.trans K.symm)
      have ownL : dataOwner (oldH6 B base) e (sh p)=o.val := by rw [E]; exact own _ Q
      have quiet (D : DataClaim) (N : D∈orderedData (oldPair B q e) []) :
          L (sh p)∉D.slots := by
        intro P
        have T := (right_footprint_layout .left F dp tail Q layout E D).mp ⟨N,P⟩
        simp [rightClaim,notIncoming] at T
      have W := ring_owner_quiet hp chart sep hist now layout pc11 e (L (sh p)) ownL quiet
      change readLane (BStarLongPackets.Sheet.index (sh p)) (y e).long=
        readLane (BStarLongPackets.Sheet.index (sh p)) (q e).long at W
      rw [E] at W
      exact congrArg occupied W
    · have W := quiet_outside_mark B q e (addr root p) (Ne.symm E) (Ne.symm offR)
      change occupied (readLane (BStarLongPackets.Sheet.index (sh p)) (y (addr root p)).long)=
        occupied (readLane (BStarLongPackets.Sheet.index (sh p)) (q (addr root p)).long)
      rw [show y (addr root p)=q (addr root p) from W]

/-- The right exterior inlet is the actual LAST site of the
following H6 word, not an artificial boundary in its padding. -/
theorem right_tail_from_flags {base : X} {hh : ∃ i,oldH6 B base i=true}
    {root : Fin n} {d r' : Nat} (F : RightFrame B base root d r')
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1) :
    ends (longGeometry B (base (addr root (d+r'-1))))=true := by
  have pos := F.width_pos
  have D := (BStarFenceReceiverChart.digit_from hp (hh:=hh) F.first_header r' notShort
    (r'-1) (by omega)).1
  rw [←BStarCopyLeftStrip.addr_from,show d+(r'-1)=d+r'-1 by omega] at D
  unfold ends
  rw [(flags _).1,(flags _).2,D]
  have A : r'-1<r' := by omega
  have B' : r'-1+1=r' := by omega
  simp [A,B']

/-- Both real lines satisfy the shadow comparison on the very same
selected mark, including mixed HOP/END and quiet combinations. -/
theorem both_mark {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (pc11 : pc (play x w) (S.getD 0 fall).1=11)
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (e : Fin n) (z : Two (l:=l+r') (r:=d+r')) :
    let Lroot := (S.getD 0 fall).1
    let Rroot := (S.getD len fall).1
    let phys := fun q : X => (⟨BStarFenceLeftShadow.leftOcc q Lroot l r',rightOcc q Rroot d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
    (phys (play x w)).below z →
      (phys (step (play x w) e)).below (Two.advance (leftPort Lroot) (rightPort Rroot) e z) := by
  dsimp only
  intro dom
  exact same_emitted _ _ e (BStarFenceLeftShadow.left_mark hp chart sep hist now layout pc11 LF e)
    (right_mark hp chart sep hist now layout pc11 RF dp (right_tail_from_flags hp RF flags notShort) e) dom

/-- An arbitrarily steered candidate prefix is coupled to both physical
lines until the paid phase stops. The state retains both histories.
A new mark uses the emitted label selected at the old prefix. -/
theorem actual_sweep {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    (idle : Current hp base (fun j => S.getD j fall) len x .idle)
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (emit : (List (Fin n) × List (Fin n)) → Fin n → Fin n)
    (phase : (List (Fin n) × List (Fin n)) → Bool)
    (fence : ∀ a,phase a=true→pc (play x a.2) (S.getD 0 fall).1=11)
    (p : List (Fin n) × List (Fin n)) (w : List (Fin n))
    (z : Two (l:=l+r') (r:=d+r')) :
    let Lroot := (S.getD 0 fall).1
    let Rroot := (S.getD len fall).1
    let phys := fun a : List (Fin n) × List (Fin n) =>
      (⟨BStarFenceLeftShadow.leftOcc (play x a.2) Lroot l r',rightOcc (play x a.2) Rroot d r'⟩ :
        Two (l:=l+r') (r:=d+r'))
    let next := fun (a : List (Fin n) × List (Fin n)) e => (a.1++[e],a.2++[emit a e])
    let s := sweep (leftPort Lroot) (rightPort Rroot) next emit phase p z w
    (phys p).below z → (phys s.1).below s.2 := by
  dsimp only
  intro dom
  let Lroot := (S.getD 0 fall).1
  let Rroot := (S.getD len fall).1
  let phys := fun a : List (Fin n) × List (Fin n) =>
    (⟨BStarFenceLeftShadow.leftOcc (play x a.2) Lroot l r',rightOcc (play x a.2) Rroot d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
  let next := fun (a : List (Fin n) × List (Fin n)) e => (a.1++[e],a.2++[emit a e])
  have one (a : List (Fin n) × List (Fin n)) (e : Fin n) (act : phase a=true) :
      Mark (leftPort Lroot) (emit a e) (phys a).left (phys (next a e)).left ∧
      Mark (rightPort Rroot) (emit a e) (phys a).right (phys (next a e)).right := by
    obtain ⟨m,hist,live,now⟩ := generated_word hp chart Q layout closed sep a.2 .idle I idle
    have Eq : play x (a.2++[emit a e])=step (play x a.2) (emit a e) := by
      rw [BStarResetSchedule.run_append]
      rfl
    dsimp only [phys,next]
    rw [Eq]
    exact ⟨BStarFenceLeftShadow.left_mark hp chart sep hist now (layout _ live) (fence a act) LF (emit a e),
      right_mark hp chart sep hist now (layout _ live) (fence a act) RF dp
        (right_tail_from_flags hp RF flags notShort) (emit a e)⟩
  exact (sweep_below (leftPort Lroot) (rightPort Rroot) next emit phase
    (fun _=>True) phys (fun _ _ _ _=>True.intro) (fun a e _ h =>one a e h) w p z True.intro dom).2

#print axioms right_mark
#print axioms right_tail_from_flags
#print axioms both_mark
#print axioms actual_sweep
end L4.BStarFenceRightShadow

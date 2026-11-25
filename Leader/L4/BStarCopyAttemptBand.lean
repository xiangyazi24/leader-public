import Leader.L4.BStarCopyGateAuthority
import Leader.L4.BStarGeneratedPCAncestry

namespace L4.BStarCopyAttemptBand
open AllSizeProtocol BStarTrace BStarLongWork BStarLongDoor BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarLongFixedRouting BStarGeneratedOwner BStarGeneratedBandScan BStarResetChartService
open BStarSeparatorControl BStarOwnerControlHistory BStarResetControllerEntry
open BStarGeneratedPCAncestry BStarCopyGateAuthority

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem snapshot_op {x y : BitVec LW} {a : Token} {f : BitVec 2}
    (H : snapshot y=((a,f),ctrlOp.read x)) :
    (ctrlOp.read y).toNat=(ctrlOp.read x).toNat :=
  congrArg (fun q : (Token × BitVec 2) × BitVec 9 => q.2.toNat) H

/-- In one actual recovered attempt inside the retained PC band,
old source PC cannot decrease. A consume can enter 6 only from 5,
so a legal later PC9/10 attempt cannot revisit STOP at PC6. -/
theorem band_step_exact {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    {m m' : Mode} (e : Fin n)
    (I : Current hp base (fun j => S.getD j fall) len x m)
    (E : Event hp (fun j => S.getD j fall) len x e m m')
    (post : Current hp base (fun j => S.getD j fall) len (step x e) m') :
    let root := (S.getD 0 fall).1
    Band x root → Band (step x e) root → (pc (step x e) root=pc x root ∨ pc (step x e) root=pc x root+1) := by
  dsimp only
  intro oldBand newBand
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let y := step x e
  change Band x root at oldBand
  change Band y root at newBand
  cases m with
  | idle =>
    rcases idle_launch_or_hold hp chart layout I.2 sep e I.1 with L|N|H
    · exact .inl (congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat) L.2.2.1)
    · have pc0 : pc y root=0 :=
        congrArg (fun q : (Token × BitVec 2) × BitVec 9 => q.2.toNat) N.2.2.1
      have lo := newBand.1
      omega
    · obtain ⟨_,⟨_,a,_,snap⟩,_,_⟩ := H
      exact .inl (snapshot_op snap)
  | busy op z =>
    cases E with
    | transit _ _ _ _ _ =>
      exact .inl (post.1.2.2.2.trans I.1.2.2.2.symm)
    | arrived_hold _ _ =>
      exact .inl (post.1.2.2.2.trans I.1.2.2.2.symm)
    | consume _ atDoor clean =>
      obtain ⟨head,rootIx⟩ := root_header hp chart layout
      have L := newBand.1
      have U := newBand.2
      have M := oldBand.1
      have ev : Event hp addr len x e (.busy op (.back 0)) .idle := .consume op atDoor clean
      by_cases low : pc y root=6
      · obtain ⟨op5,_⟩ := consume_to_six hp (base:=base) (x:=x) (addr:=addr) (len:=len)
          (op:=op) (e:=e) rootIx head (sep e) I ev low
        have old5 : pc x root=5 := I.1.2.2.2.trans op5
        omega
      · obtain ⟨next,_⟩ := consume_to_band hp (base:=base) (x:=x) (addr:=addr) (len:=len)
          (op:=op) (e:=e) rootIx head (sep e) I ev (by change 7≤pc y root; omega) U
        have oldPC : pc x root=op := I.1.2.2.2
        change pc y root=op+1 at next
        exact .inr (next.trans (congrArg (·+1) oldPC.symm))

theorem band_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    {m m' : Mode} (e : Fin n)
    (I : Current hp base (fun j => S.getD j fall) len x m)
    (E : Event hp (fun j => S.getD j fall) len x e m m')
    (post : Current hp base (fun j => S.getD j fall) len (step x e) m') :
    let root := (S.getD 0 fall).1
    Band x root → Band (step x e) root → pc x root≤pc (step x e) root := by
  dsimp only
  intro oldBand newBand
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let y := step x e
  change Band x root at oldBand
  change Band y root at newBand
  cases m with
  | idle =>
    rcases idle_launch_or_hold hp chart layout I.2 sep e I.1 with L|N|H
    · exact Nat.le_of_eq (congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat) L.2.2.1).symm
    · have pc0 : pc y root=0 :=
        congrArg (fun q : (Token × BitVec 2) × BitVec 9 => q.2.toNat) N.2.2.1
      have lo := newBand.1
      omega
    · obtain ⟨_,⟨_,a,_,snap⟩,_,_⟩ := H
      exact Nat.le_of_eq (snapshot_op snap).symm
  | busy op z =>
    cases E with
    | transit _ _ _ _ _ =>
      exact Nat.le_of_eq (I.1.2.2.2.trans post.1.2.2.2.symm)
    | arrived_hold _ _ =>
      exact Nat.le_of_eq (I.1.2.2.2.trans post.1.2.2.2.symm)
    | consume _ atDoor clean =>
      obtain ⟨head,rootIx⟩ := root_header hp chart layout
      have L := newBand.1
      have U := newBand.2
      have M := oldBand.1
      have ev : Event hp addr len x e (.busy op (.back 0)) .idle := .consume op atDoor clean
      by_cases low : pc y root=6
      · obtain ⟨op5,_⟩ := consume_to_six hp (base:=base) (x:=x) (addr:=addr) (len:=len)
          (op:=op) (e:=e) rootIx head (sep e) I ev low
        have old5 : pc x root=5 := I.1.2.2.2.trans op5
        omega
      · obtain ⟨next,_⟩ := consume_to_band hp (base:=base) (x:=x) (addr:=addr) (len:=len)
          (op:=op) (e:=e) rootIx head (sep e) I ev (by change 7≤pc y root; omega) U
        have oldPC : pc x root=op := I.1.2.2.2
        change pc y root=op+1 at next
        change pc x root≤pc y root
        omega

#print axioms band_step

theorem drop_history {base x : X} {addr : Nat → Pos n} {len : Nat}
    {m fin : Mode} (pre post : List (Fin n))
    (G : GeneratedOwner hp base addr len x m (pre++post) fin) :
    ∃ now, GeneratedOwner hp base addr len (play x pre) now post fin := by
  induction pre generalizing x m with
  | nil => exact ⟨m,G⟩
  | cons e w ih =>
    cases G with
    | next _ _ tail => exact ih tail

/-- Actual nondecrease over any finite subword wholly inside the
same-attempt band. Nothing is assumed about unrelated owner PCs. -/
theorem band_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m m' : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x m w m')
    (valid : ∀ a b, w=a++b →
      (∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x a) i) ∧
      Band (play x a) (S.getD 0 fall).1) :
    pc x (S.getD 0 fall).1≤pc (play x w) (S.getD 0 fall).1 := by
  induction G with
  | endpoint _ => exact Nat.le_refl _
  | @next x m e w mid fin I E tail ih =>
    have V := valid [] (e::w) rfl
    have N := valid [e] w rfl
    have J : Current hp base (fun j => S.getD j fall) len (step x e) mid := by
      cases tail with
      | endpoint K => exact K
      | next K _ _ => exact K
    have le := band_step hp chart sep V.1 e I E J V.2 N.2
    have q := ih (fun a b H => valid (e::a) b (congrArg (List.cons e) H))
    exact Nat.le_trans le q

/-- A selected actual ENABLE opens its owner lane and stays open at
the end of the same recovered COPY attempt. It suffices that the
actual marks starting at ENABLE and ending at INJECT lie in the
non-restarting controller band (not a separate no-STOP assumption). -/
theorem enable_through_same_attempt {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead rest : List (Fin n)) (e : Fin n) (a : BStarLongPrep.Offer) (m : Mode)
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle (lead++e::rest) m)
    (ena : a.claim.op=.enable)
    (win : a∈(BStarLongPrep.arbitration (BStarLongCommandData.round
      (oldPair B (play x lead) e) (((play x lead) e).long,((play x lead) (rightNeighbor e)).long)).prep).1) :
    let i := site e a.claim.lane.side
    let sh := a.claim.lane.occurrence
    let root := (S.getD 0 fall).1
    BStarClearanceDataChart.dataOwner (oldH6 B base) i sh=o.val →
    (∀ u v, e::rest=u++v →
      (∀ k,BStarLongFixedRouting.Layout B base k=BStarLongFixedRouting.Layout B (play (play x lead) u) k) ∧
      Band (play (play x lead) u) root) →
    (BStarLongPackets.readLane (BStarLongPackets.Sheet.index sh) (play x (lead++e::rest) i).long).gate=true := by
  dsimp only
  intro own valid
  obtain ⟨mid,H,cur⟩ := history_prefix hp lead (e::rest) G
  have p9 : pc (play x lead) (S.getD 0 fall).1=9 := by
    have E := winning_prep_pc hp chart sep H cur (valid [] (e::rest) rfl).1 e a own win
    rw [ena] at E
    unfold BStarLongCommandData.prepOf at E
    split at E <;> simp_all
  obtain ⟨start,tail⟩ := drop_history hp lead (e::rest) G
  apply gate_actual_word hp chart sep lead rest e a m G ena win own
  · intro u next v H
    exact (valid (e::u) (next::v) (congrArg (List.cons e) H)).1
  · intro u next v H
    have split : e::rest=(e::u)++next::v := congrArg (List.cons e) H
    have sides : e::rest=(e::u)++next::v := split
    rw [sides] at tail
    obtain ⟨ending,U,_⟩ := history_prefix hp (e::u) (next::v) tail
    have V := band_word hp chart sep U (fun c d E => valid c (d++next::v) (by rw [sides,E,List.append_assoc]))
    change pc (play x lead) (S.getD 0 fall).1 ≤ pc (play (step (play x lead) e) u) (S.getD 0 fall).1 at V
    rw [p9] at V
    exact ⟨by omega,by omega⟩

#print axioms band_word
#print axioms enable_through_same_attempt


/-- Every intermediate controller phase is crossed on the original
raw tape; a successful PC6-to-PC12 run cannot jump a setup phase. -/
theorem exact_crossing {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m m' : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x m w m')
    (valid : ∀ a b,w=a++b →
      (∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x a) i) ∧
      Band (play x a) (S.getD 0 fall).1)
    (j : Nat)
    (L : pc x (S.getD 0 fall).1≤j)
    (R : j<pc (play x w) (S.getD 0 fall).1) :
    ∃ pre e post, w=pre++e::post ∧
      pc (play x pre) (S.getD 0 fall).1=j ∧
      pc (step (play x pre) e) (S.getD 0 fall).1=j+1 := by
  induction G with
  | @endpoint x _ I =>
    change j<pc x (S.getD 0 fall).1 at R
    omega
  | @next x m e w mid fin I E tail ih =>
    let root := (S.getD 0 fall).1
    let y := step x e
    have V := valid [] (e::w) rfl
    have N := valid [e] w rfl
    have J : Current hp base (fun j => S.getD j fall) len y mid := by
      cases tail with
      | endpoint K => exact K
      | next K _ _ => exact K
    have h := band_step_exact hp chart sep V.1 e I E J V.2 N.2
    change pc x root≤j at L
    by_cases next : pc y root≤j
    · obtain ⟨pre,a,post,W,P,Q⟩ :=
        ih (fun u v H => valid (e::u) v (congrArg (List.cons e) H)) next R
      exact ⟨e::pre,a,post,congrArg (List.cons e) W,P,Q⟩
    · change pc y root=pc x root ∨ pc y root=pc x root+1 at h
      have old : pc x root=j := by rcases h with h|h <;> omega
      have now : pc y root=j+1 := by rcases h with h|h <;> omega
      exact ⟨[],e,w,rfl,old,now⟩

#print axioms band_step_exact
#print axioms exact_crossing
end L4.BStarCopyAttemptBand

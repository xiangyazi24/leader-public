import Leader.L4.BStarClearancePrepOwner
import Leader.L4.BStarClearanceMobileJoined
import Leader.L4.RearGeometry

namespace L4.BStarClearanceRightmost
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarTrace
open BStarClearanceDataChart BStarAcquireRailCoverage BStarLongPackets
open BStarClearancePrepOwner BStarLongEvents BStarLongFiberOwner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
abbrev Site := LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def mobile (x : Fin n → Site (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂)
    (r:=r) (c:=c) (p:=p) (c₁:=c₁)) (i : Fin n) (s : Sheet) : Digit9 :=
  (readLane (Sheet.index s) (x i).long).mobile

private theorem minimal {A : Type} (P : A → Prop) (rank : A → Nat) (H : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → rank x≤rank y := by
  classical
  have F : ∀ k, (∃ x, P x ∧ rank x=k) → ∃ x, P x ∧ ∀ y, P y → rank x≤rank y := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      rintro ⟨x,hx,hk⟩
      by_cases Q : ∃ y, P y ∧ rank y<k
      · obtain ⟨y,hy,h⟩ := Q
        exact ih _ h ⟨y,hy,rfl⟩
      · exact ⟨x,hx,fun y hy => by rw [hk]; exact Nat.le_of_not_gt (fun h => Q ⟨y,hy,h⟩)⟩
  obtain ⟨x,hx⟩ := H
  exact F (rank x) ⟨x,hx,rfl⟩

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

private theorem target_active (g : Pair LongGeometry) (U : List (At Sheet))
    (C : DataClaim) (D : At Sheet) (hc : C∈orderedData g U) (hd : C.destination=some D) :
    activeSheet (BStarLongCommand.geometry g D.side) D.occurrence=true := by
  obtain ⟨x,y⟩ := g
  let test (g : Pair LongGeometry) (C : DataClaim) : Bool :=
    match C.destination with
    | none => true
    | some D => activeSheet (BStarLongCommand.geometry g D.side) D.occurrence
  have F (I L H J : Bool) : (dataClaims (geo false I L,geo H J false)).all
      (test (geo false I L,geo H J false))=true := by
    cases I <;> cases L <;> cases H <;> cases J <;> decide +kernel
  have P := BStarLongFenceTopology.selected_data_raw (x,y) U C hc
  change C∈dataClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false) at P
  have S := List.all_eq_true.mp (F x.inside x.last y.axes.h6 y.inside) C P
  cases H : D.side <;> simpa [test,hd,H,BStarLongCommand.geometry,geo,activeSheet] using S

private theorem service_mark {a : LargeParams} (b : LargeRows a)
    (x : Fin n → LargeSite a)
    (head : ∀ i, let g := longGeometry b (x i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair b x i; continuation g.1 g.2=true)
    (i : Fin n) (s : Sheet) (H : activeSheet (longGeometry b (x i)) s=true) :
    ∃ e C, C∈orderedData (oldPair b x e) [] ∧ site e C.source.side=i ∧ C.source.occurrence=s := by
  let j := RearTrace.predecessor i
  let G (i : Fin n) := longGeometry b (x i)
  have J : rightNeighbor j=i := RearTrace.right_predecessor i
  have L : continuation (G j) (G i)=true := by
    have T := cont j
    change continuation (G j) (G (rightNeighbor j))=true at T
    rwa [J] at T
  have P := service_ports (G j) (G i) (G (rightNeighbor i)) (head i)
    (head (rightNeighbor i)) L (cont i) s
  have A (e : Fin n) (d : Side) (Q : 0<((orderedData (oldPair b x e) []).filter
      (fun C => C.source == ⟨d,s⟩)).length) (hi : site e d=i) :
      ∃ e C, C∈orderedData (oldPair b x e) [] ∧ site e C.source.side=i ∧ C.source.occurrence=s := by
    obtain ⟨C,hs⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos Q)
    obtain ⟨hC,hs⟩ := List.mem_filter.mp hs
    have E := beq_iff_eq.mp hs
    exact ⟨e,C,hC,by rw [E]; exact hi,by rw [E]⟩
  have Lv : 0<(expectedLeft (G i)).count s ∨ 0<(expectedRight (G i)).count s := by
    change activeSheet (G i) s=true at H
    cases K : (G i).inside <;> cases s <;>
      simp_all [activeSheet,expectedLeft,expectedRight] <;> decide
  rcases Lv with Z|Z
  · apply A i .left _ rfl
    change 0<((orderedData (G i,G (rightNeighbor i)) []).filter (fun C => C.source == BStarLongClaims.L s)).length
    rwa [P.2]
  · apply A j .right _ J
    change 0<((orderedData (G j,G (rightNeighbor j)) []).filter (fun C => C.source == R s)).length
    rwa [J,P.1]

/-- The minimum-rank occupied lane of a physical owner has a nominal
service at this mark. Its target is vacant (BAD is occupied), or it
is terminal. If prep suppresses the nominal service, a real advance
of the same owner is selected on this very old pair. -/
theorem nominate (hp : 0<p) (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (hh : ∃ i, oldH6 (BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x i=true)
    (o : Int) :
    let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let h := oldH6 b x
    (∀ i, let g := longGeometry b (x i); (!g.axes.h6 || g.inside)=true) →
    (∀ i, let g := oldPair b x i; continuation g.1 g.2=true) →
    (∃ i s, activeSheet (longGeometry b (x i)) s=true ∧ dataOwner h i s=o ∧ mobile x i s≠.empty) →
    ∃ e C, C∈orderedData (oldPair b x e) [] ∧
      dataOwner h (site e C.source.side) C.source.occurrence=o ∧
      mobile x (site e C.source.side) C.source.occurrence≠.empty ∧
      (∀ D, C.destination=some D → mobile x (site e D.side) D.occurrence=.empty) ∧
      let old : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      let g := oldPair b x e
      C∈orderedData g (BStarLongPrep.reserved (BStarLongCommandData.round g old).prep) ∨
      ∃ cmd q, (cmd,.advance q)∈actualOffers g old ∧ physicalOwner h e cmdDispl cmd.source=o := by
  dsimp only
  intro head cont occ
  let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let h := oldH6 b x
  let P (u : Fin n × Sheet) := activeSheet (longGeometry b (x u.1)) u.2=true ∧
    dataOwner h u.1 u.2=o ∧ mobile x u.1 u.2≠.empty
  obtain ⟨⟨i,s⟩,H,M⟩ := minimal P (fun u => distance h hh u.1 u.2)
    (by obtain ⟨i,s,H⟩ := occ; exact ⟨(i,s),H⟩)
  obtain ⟨e,C,hC,Si,Ss⟩ := service_mark b x head cont i s H.1
  refine ⟨e,C,hC,by rw [Si,Ss]; exact H.2.1,by rw [Si,Ss]; exact H.2.2,?_,?_⟩
  · intro D hD
    apply Classical.byContradiction
    intro N
    have Dact := target_active (oldPair b x e) [] C D hC hD
    have Da : activeSheet (longGeometry b (x (site e D.side))) D.occurrence=true := by
      cases S : D.side <;> simpa [S, site,oldPair,BStarLongCommand.geometry] using Dact
    have Own := (reserved_hop_owner b x e [] C D hC hD).symm
    rw [Si,Ss] at Own
    have Lower := M (site e D.side,D.occurrence) ⟨Da,Own.trans H.2.1,N⟩
    have Q := hop_decreases b x hh e [] C D hC hD
    rw [Si,Ss] at Q
    exact (Nat.not_lt_of_ge Lower Q)
  · let old : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    by_cases T : C∈orderedData (oldPair b x e)
      (BStarLongPrep.reserved (BStarLongCommandData.round (oldPair b x e) old).prep)
    · exact .inl T
    · obtain ⟨cmd,q,B,E⟩ := suppressed_nomination_actual b x e old C hC T
      rw [Si,Ss] at E
      exact .inr ⟨cmd,q,B,E.trans H.2.1⟩

/-- The nominated mobile is the actual decoded field of the
old ordered pair, and the post-pair mobile map is the literal
COPY round's map by joined-view transfer. -/
theorem pair_mobile (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (D : At Sheet) :
    let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let z := (x e,x (rightNeighbor e))
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair b x e
    (BStarLongPrep.view raw D).mobile = mobile x (site e D.side) D.occurrence ∧
    (BStarLongPrep.view (Pair.map LargeSite.long (largePair b z)) D).mobile =
      (BStarLongPrep.view (patchPair (BStarLongCommandData.patch g raw) raw) D).mobile := by
  dsimp only
  constructor
  · cases D with
    | mk s k => cases s <;> rfl
  · have E := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
    exact congrArg (fun f => (f D).mobile) E

end L4.BStarClearanceRightmost

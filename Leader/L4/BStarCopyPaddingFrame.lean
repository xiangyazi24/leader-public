import Leader.L4.BStarCopyOwnedFrozen

namespace L4.BStarCopyPaddingFrame
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets

private def pad (s : Sheet) : Prop := s=.ld ∨ s=.rs
private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

theorem prep_active (g : LongGeometry) (j : Fin 11) (op : Prep) (sh : Sheet)
    (P : pad sh) (M : sh∈prepSites g j op) : g.inside=true := by
  cases H : g.inside
  · rcases P with rfl|rfl <;> cases op <;> simp [prepSites,H] at M
    all_goals repeat' first | split at M
    all_goals simp_all
  · rfl

/-- Every real data-edge endpoint on LD or RS is inside. -/
theorem data_active (g : Pair LongGeometry) (rs : List (At Sheet)) (d : DataClaim) (a : At Sheet)
    (D : d∈orderedData g rs) (A : a∈d.slots) (P : pad a.occurrence) :
    (geometry g a.side).inside=true := by
  obtain ⟨l,r⟩ := g
  have test (I T H J : Bool) :
      (dataClaims (geo false I T,geo H J false)).all (fun c => c.slots.all fun s =>
        !(s.occurrence==.ld || s.occurrence==.rs) ||
          (geometry (geo false I T,geo H J false) s.side).inside)=true := by
    cases I <;> cases T <;> cases H <;> cases J <;> decide +kernel
  have raw := BStarLongFenceTopology.selected_data_raw (l,r) rs d D
  change d∈dataClaims (geo false l.inside l.last,geo r.axes.h6 r.inside false) at raw
  have E := List.all_eq_true.mp (List.all_eq_true.mp (test l.inside l.last r.axes.h6 r.inside) d raw) a A
  have sh : (a.occurrence==.ld || a.occurrence==.rs)=true :=
    Bool.or_eq_true_iff.mpr (P.imp (fun h => beq_iff_eq.mpr h) (fun h => beq_iff_eq.mpr h))
  rw [sh] at E
  cases X : a.side <;> simpa [X,geometry,geo] using E

private theorem fold_no_touch (A : List (At Sheet × Leaf)) (s : At Sheet) (old : At Sheet→Lane)
    (none : ∀ a∈A,a.1≠s) : (A.foldl update old) s=old s := by
  induction A generalizing old with
  | nil => rfl
  | cons a w ih =>
    rw [List.foldl_cons,ih _ (fun t ht => none t (List.mem_cons_of_mem _ ht))]
    unfold update
    split
    · rename_i E
      exact (none a List.mem_cons_self E.symm).elim
    · rfl

/-- Neither cleanup, LOAD, ENABLE, INJECT, mailbox movement nor joined
non-COPY rows write an inactive LD/RS sheet. This holds at arbitrary
packed values, not just already empty padding. -/
theorem pair_padding_held {k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat} (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : At Sheet)
    (P : pad s.occurrence)
    (I : (geometry (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x) s.side).inside=false) :
    view (Pair.map LargeSite.long (largePair (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x)) s=
      view (Pair.map LargeSite.long x) s := by
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw := Pair.map LargeSite.long x
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp,
      BStarLongCommandData.round_transfer]
  apply fold_no_touch
  intro a M A
  rcases List.mem_append.mp M with prep|data
  · obtain ⟨v,W,E⟩ := List.mem_flatMap.mp prep
    obtain ⟨l,_,Q⟩ := List.mem_map.mp E
    have same : v.claim.lane=s := (congrArg Prod.fst Q).trans A
    obtain ⟨C,_,_,_,_,_,_,_,side,ms⟩ := BStarCopyOwnedFrozen.winner_origin g raw v W
    rw [same] at side ms
    rw [side] at I
    exact Bool.noConfusion ((prep_active _ _ _ _ P ms).symm.trans I)
  · obtain ⟨d,D,E⟩ := List.mem_flatMap.mp data
    have mem := data_lane_claim g (view raw) d a.1 a.2 (by cases a; exact E)
    rw [A] at mem
    exact Bool.noConfusion ((data_active _ _ _ _ D mem P).symm.trans I)

open BStarH6WordChart BStarResetMarkAdapter
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem ring_padding_held (x : X) (e i : Fin n) (sh : Sheet) (sep : e≠rightNeighbor e)
    (P : sh=.ld ∨ sh=.rs) (I : (longGeometry B (x i)).inside=false) :
    readLane (Sheet.index sh) (step x e i).long=readLane (Sheet.index sh) (x i).long := by
  by_cases l : i=e
  · subst i
    have H := pair_padding_held hp (x e,x (rightNeighbor e)) (⟨.left,sh⟩ : At Sheet) P I
    simpa [view,AllSizeS1Geometry.step,Pair.map,lane,BStarTrace.lane,Ne.symm sep] using H
  · by_cases r : i=rightNeighbor e
    · subst i
      have H := pair_padding_held hp (x e,x (rightNeighbor e)) (⟨.right,sh⟩ : At Sheet) P I
      simpa [view,AllSizeS1Geometry.step,Pair.map,lane,BStarTrace.lane,Ne.symm sep] using H
    · simp [AllSizeS1Geometry.step,l,r]

/-- A stale padded value cannot be erased by any finite fixed-layout
raw tape, including STOP/RCLEAR/CLEAR and ENABLE. -/
theorem word_padding_held (x : X) (w : List (Fin n)) (i : Fin n) (sh : Sheet)
    (P : sh=.ld ∨ sh=.rs) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (inactive : ∀ pre e post,w=pre++e::post → (longGeometry B (play x pre i)).inside=false) :
    readLane (Sheet.index sh) (play x w i).long=readLane (Sheet.index sh) (x i).long := by
  induction w generalizing x with
  | nil => rfl
  | cons e tail ih =>
    have E := ring_padding_held hp x e i sh (sep e) P (inactive [] e tail rfl)
    exact (ih (step x e) (fun a f b Q => inactive (e::a) f b (congrArg (List.cons e) Q))).trans E

end L4.BStarCopyPaddingFrame

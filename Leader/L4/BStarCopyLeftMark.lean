import Leader.L4.BStarCopyLeftStrip
import Leader.L4.BStarCopyRightMark

namespace L4.BStarCopyLeftMark
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarTrace BStarLongWork
open BStarCopyLeftStrip
open BStarCopyRightStrip (addr addr_next addr_inj)

theorem raw_ls_send (g : Pair LongGeometry) (d : DataClaim) (D : d.source=L .ls) :
    d∈dataClaims g ↔
      (g.2.axes.h6=true ∧ g.2.inside=true ∧ d=hop (L .ls) (R .ld)) ∨
      (g.2.axes.h6=false ∧ d=hop (L .ls) (R .ls)) := by
  unfold dataClaims
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] <;> grind [L,R]

theorem raw_ld_send (g : Pair LongGeometry) (d : DataClaim) (D : d.source=L .ld) :
    d∈dataClaims g ↔
      (ends g.1=true ∧ d=ending (L .ld)) ∨
      (g.2.axes.h6=false ∧ g.1.inside=true ∧ g.2.inside=true ∧
        ends g.1=false ∧ d=hop (L .ld) (R .ld)) := by
  unfold dataClaims
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] <;> grind [L,R]

theorem no_right_send (g : Pair LongGeometry) (d : DataClaim) (M : d∈dataClaims g) :
    d.source≠R .ls ∧ d.source≠R .ld := by
  unfold dataClaims at M
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] at M <;> grind [L,R]

theorem selected_outgoing {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {base : Fin n} {seam width : Nat}
    (C : Strip b x base seam width) (i : Nat) (hi : i+1<seam+width)
    (rsv : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base i)) rsv)
    (S : d.source=L (rail seam i)) :
    d=hop (L (rail seam i)) (R (rail seam (i+1))) := by
  let g := oldPair b x (addr base i)
  have raw : d∈dataClaims g := BStarLongFenceTopology.selected_data_raw _ _ _ M
  have right := (addr_next base i).symm
  by_cases a0 : i<seam
  · simp only [rail,if_pos a0] at S ⊢
    have F := (raw_ls_send _ _ S).mp raw
    by_cases j : i+1<seam
    · have H : g.2.axes.h6=false := by
        change oldH6 b x (rightNeighbor (addr base i))=false
        rw [right]; exact C.ls_body _ (by omega) j
      simpa [H,rail,j] using F
    · have E : i+1=seam := by omega
      have H : g.2.axes.h6=true := by
        change oldH6 b x (rightNeighbor (addr base i))=true
        rw [right,E]; exact C.dest_header
      have I : g.2.inside=true := by
        change (longGeometry b (x (rightNeighbor (addr base i)))).inside=true
        rw [right]; exact C.ld_in _ (by omega) hi
      simpa [H,I,rail,j] using F
  · simp only [rail,if_neg a0,if_neg (show ¬i+1<seam by omega)] at S ⊢
    have F := (raw_ld_send _ _ S).mp raw
    have K : ends g.1=false := C.ld_before_last i (by omega) hi
    rcases F with ⟨J,_⟩|⟨_,_,_,_,E⟩
    · rw [K] at J
      exact Bool.noConfusion J
    · exact E

private theorem rail_cases (seam i : Nat) : rail seam i=.ls ∨ rail seam i=.ld := by
  unfold rail
  split <;> simp

/-- On the selected physical link the two indexed route endpoints
belong to no other data claim, even when other lanes on that mark
are simultaneously used. -/
theorem pair_claim {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {base : Fin n} {seam width : Nat}
    (C : Strip b x base seam width) (i : Nat) (hi : i+1<seam+width)
    (rsv : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base i)) rsv)
    (P : L (rail seam i)∈d.slots ∨ R (rail seam (i+1))∈d.slots) :
    d=hop (L (rail seam i)) (R (rail seam (i+1))) := by
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ M
  have l := no_left_receive _ _ raw
  have r := no_right_send _ _ raw
  have S : d.source≠R (rail seam (i+1)) := by
    rcases rail_cases seam (i+1) with A|A <;> rw [A]
    · exact r.1
    · exact r.2
  have D : d.destination≠some (L (rail seam i)) := by
    rcases rail_cases seam i with A|A <;> rw [A]
    · exact l.1
    · exact l.2
  have shape (s : At Sheet) (I : s∈d.slots) : s=d.source ∨ d.destination=some s := by
    cases X : d.destination <;> simpa [Claim.slots,X,eq_comm] using I
  rcases P with P|P
  · rcases shape _ P with Q|Q
    · exact selected_outgoing C i hi _ _ M Q.symm
    · exact (D Q).elim
  · rcases shape _ P with Q|Q
    · exact (S Q.symm).elim
    · exact selected_hop C i hi _ _ M Q

theorem ordered_hop_off_reservations (g : Pair LongGeometry) (u v : At Sheet)
    (rs : List (At Sheet)) (M : hop u v∈orderedData g rs) : u∉rs ∧ v∉rs := by
  have K := (data_reservations _ _).2 _ M
  exact ⟨K _ (by simp [Claim.slots,hop]),K _ (by simp [Claim.slots,hop])⟩

section Ring
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

def sample (x : X) (base : Fin n) (seam i : Nat) : Lane :=
  readLane (Sheet.index (rail seam i)) (x (addr base i)).long

/-- Generic actual-mark frame at any left strip position. Wrapped
visits on the other sheet are tested independently, not conflated
with the selected footprint. Arbitrary off-pair sites frame. -/
theorem spectator (x : X) (e base : Fin n) (seam i : Nat) (sep : e≠rightNeighbor e)
    (safe : let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      ∀ a : At Sheet, site e a.side=addr base i → a.occurrence=rail seam i →
        a∉reserved (round g raw).prep ∧
        ∀ d∈orderedData g (reserved (round g raw).prep),
          ∀ leaf,(a,leaf)∉dataEffects g (view raw) d) :
    sample (step x e) base seam i=sample x base seam i := by
  unfold sample
  by_cases h : addr base i=e
  · let a := L (rail seam i)
    have Q := safe a h.symm rfl
    have E := BStarCopyRightMark.joined_spectator hp (x e,x (rightNeighbor e)) a Q.1 Q.2
    change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a =
      view ((x e).long,(x (rightNeighbor e)).long) a at E
    rw [BStarCopyRightMark.new_access hp x e a sep,BStarCopyRightMark.old_access x e a] at E
    exact h.symm ▸ E
  · by_cases j : addr base i=rightNeighbor e
    · let a := R (rail seam i)
      have Q := safe a j.symm rfl
      have E := BStarCopyRightMark.joined_spectator hp (x e,x (rightNeighbor e)) a Q.1 Q.2
      change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a =
        view ((x e).long,(x (rightNeighbor e)).long) a at E
      rw [BStarCopyRightMark.new_access hp x e a sep,BStarCopyRightMark.old_access x e a] at E
      exact j.symm ▸ E
    · simp [AllSizeS1Geometry.step,h,j]

open BStarCopyFIFO BStarCopyUpstreamTags

/-- The exact immutable-old projection of a chosen hop, even if the
other LS/LD visit of this physical mark is active. -/
theorem joined_exact (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (u v : At Sheet)
    (ne : u≠v) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    hop u v∈orderedData g (reserved (round g raw).prep) →
    let out := view (Pair.map LargeSite.long (largePair B x))
    let H := hopEffects (view raw u) (view raw v) (retains g v)
    out u=typedLeaves (view raw u) H.1 ∧ out v=typedLeaves (view raw v) H.2 := by
  dsimp only
  intro M
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x]
  exact ⟨sender_exact _ _ u v (hop u v) rfl rfl rfl M ne,
    BStarLongCopyFence.receiver_exact _ _ u v (hop u v) rfl rfl rfl M ne⟩

/-- Disjoint LS and LD service read the same old pair and have four
independent exact write projections. Neither reads a new mobile or
retained value of the other visit. -/
theorem joined_simultaneous (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    let cs := orderedData g (reserved (round g raw).prep)
    hop (L .ls) (R .ls)∈cs → hop (L .ld) (R .ld)∈cs →
    let out := view (Pair.map LargeSite.long (largePair B x))
    ∀ d : Sheet, d=.ls ∨ d=.ld →
      let u := L d
      let v := R d
      let H := hopEffects (view raw u) (view raw v) (retains g v)
      out u=typedLeaves (view raw u) H.1 ∧ out v=typedLeaves (view raw v) H.2 := by
  dsimp only
  intro ls ld d D
  have ne : L d≠R d := by intro H; cases congrArg At.side H
  exact joined_exact hp x (L d) (R d) ne (by rcases D with rfl|rfl <;> assumption)

def UpstreamMatches {Label : Type} (digits : Label→BitVec 36) (x : X)
    (base : Fin n) (seam : Nat) (label : Nat→Option Label) : Prop :=
  ∀ j<seam, (sample x base seam j).mobile=encode digits (label j)

def moveTag {Label : Type} (label : Nat→Option Label) (i : Nat) (tag : Label)
    (j : Nat) : Option Label :=
  if j=i then none else if j=i+1 then some tag else label j

/-- One actual interior LS mark transports the old tag and frames
every other LS slot. A simultaneous LD service is permitted. -/
theorem ring_upstream {Label : Type} (digits : Label→BitVec 36) (tag : Label)
    (x : X) (base : Fin n) (seam width i : Nat) (hi : i+1<seam)
    (C : Strip B x base seam width) (label : Nat→Option Label)
    (old : UpstreamMatches digits x base seam label)
    (donor : label i=some tag) (vacancy : label (i+1)=none) :
    let e := addr base i
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    e≠rightNeighbor e →
    hop (L .ls) (R .ls)∈orderedData g (reserved (round g raw).prep) →
    ((view raw (L .ls)).gate && (view raw (R .ls)).gate)=true →
    UpstreamMatches digits (step x e) base seam (moveTag label i tag) := by
  dsimp only
  intro sep M G
  let e := addr base i
  have a0 : i<seam := by omega
  have near : addr base (i+1)=rightNeighbor e := addr_next base i
  have U := old i a0
  have V := old (i+1) hi
  have S : (view ((x e).long,(x (rightNeighbor e)).long) (L .ls)).mobile=
      encode digits (some tag) := by
    rw [BStarCopyRightMark.old_access]
    change (readLane (Sheet.index .ls) (x (addr base i)).long).mobile=_
    simpa only [sample,rail,if_pos a0,donor] using U
  have T : (view ((x e).long,(x (rightNeighbor e)).long) (R .ls)).mobile=
      encode digits none := by
    rw [BStarCopyRightMark.old_access]
    have H := V
    unfold sample at H
    rw [rail,if_pos hi,near,vacancy] at H
    exact H
  have neq : L Sheet.ls≠R .ls := by intro E; cases congrArg At.side E
  obtain ⟨A,D,_⟩ := nonretaining_tag_joined hp digits tag
    (x e,x (rightNeighbor e)) (hop (L .ls) (R .ls)) (L .ls) (R .ls)
    rfl rfl rfl M neq (by simp [retains,R]) G S T
  change (view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) (L .ls)).mobile=_ at A
  change (view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) (R .ls)).mobile=_ at D
  rw [BStarCopyRightMark.new_access hp x e (L .ls) sep] at A
  rw [BStarCopyRightMark.new_access hp x e (R .ls) sep] at D
  intro j hj
  unfold sample
  rw [rail,if_pos hj]
  by_cases equal : j=i
  · subst j
    rw [moveTag,if_pos (rfl : i=i)]
    exact A
  · by_cases next : j=i+1
    · subst j
      rw [near]
      rw [moveTag,if_neg equal,if_pos (rfl : i+1=i+1)]
      exact D
    · have Cn := C.seam_le
      have E : addr base j ≠ e :=
        fun K => equal (addr_inj base (by omega) (by omega) K)
      have F : addr base j ≠ rightNeighbor e := by
        rw [←near]
        exact fun K => next (addr_inj base (by omega) (by omega) K)
      have same : step x e (addr base j)=x (addr base j) := by
        simp [AllSizeS1Geometry.step,E,F]
      rw [same]
      simpa only [moveTag,if_neg equal,if_neg next,sample,rail,if_pos hj] using old j hj

end Ring

/-- Literal old geometry at positions 0→1 of a one-H6 width-2
word: both visits are selected, as LS indices 0→1 and LD indices
3→4 in the three-site ring. -/
theorem parallel_body_fixture :
    let a : LongGeometry := ⟨⟨false,false,false,false,false,true⟩,true,false,0,false⟩
    let b : LongGeometry := ⟨⟨false,false,false,false,false,false⟩,true,true,0,false⟩
    let base : Fin 3 := 0
    addr base 0=addr base 3 ∧ addr base 1=addr base 4 ∧
    hop (L .ls) (R .ls)∈orderedData (a,b) [] ∧
    hop (L .ld) (R .ld)∈orderedData (a,b) [] := by decide +kernel

def upstreamWord {Label : Type} (seam : Nat) (label : Nat→Option Label) : List Label :=
  (List.range seam).flatMap (fun j => (label j).toList)

theorem upstreamWord_move {Label : Type} (seam i : Nat) (hi : i+1<seam)
    (label : Nat→Option Label) (tag : Label)
    (donor : label i=some tag) (vacancy : label (i+1)=none) :
    upstreamWord seam (moveTag label i tag)=upstreamWord seam label := by
  let k := seam-(i+2)
  have len : seam=i+(2+k) := by omega
  have E : List.range seam=List.range' 0 i ++ i::(i+1)::List.range' (i+2) k := by
    rw [List.range_eq_range',len,←List.range'_append]
    simp only [Nat.one_mul,Nat.zero_add]
    rw [show 2+k=k+1+1 by omega,List.range'_succ,List.range'_succ]
  rw [upstreamWord,upstreamWord,E]
  have unchanged (j : Nat) (a : j≠i) (b : j≠i+1) :
      (moveTag label i tag j).toList=(label j).toList := by simp [moveTag,a,b]
  have P : (List.range' 0 i).flatMap (fun j => (moveTag label i tag j).toList)=
      (List.range' 0 i).flatMap (fun j => (label j).toList) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro j J
    obtain ⟨p,H,F⟩ := List.mem_range'.mp J
    exact unchanged j (by omega) (by omega)
  have Q : (List.range' (i+2) k).flatMap (fun j => (moveTag label i tag j).toList)=
      (List.range' (i+2) k).flatMap (fun j => (label j).toList) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro j J
    obtain ⟨p,H,F⟩ := List.mem_range'.mp J
    exact unchanged j (by omega) (by omega)
  rw [List.flatMap_append,List.flatMap_append,P]
  simp only [List.flatMap_cons]
  rw [Q,donor,vacancy]
  have A : moveTag label i tag i=none := by unfold moveTag; rw [if_pos (rfl : i=i)]
  have D : moveTag label i tag (i+1)=some tag := by
    unfold moveTag
    rw [if_neg (show i+1≠i by omega),if_pos (rfl : i+1=i+1)]
  rw [A,D]
  rfl

#print axioms parallel_body_fixture
#print axioms upstreamWord_move
#print axioms ring_upstream
#print axioms joined_simultaneous
#print axioms pair_claim
#print axioms spectator
end L4.BStarCopyLeftMark

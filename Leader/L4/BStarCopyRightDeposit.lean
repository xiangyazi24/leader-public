import Leader.L4.BStarCopyRightMark
import Leader.L4.BStarCopyDownstream

namespace L4.BStarCopyRightDeposit
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongCommandData BStarLongPrep BStarLongPackets BStarCopyFIFO
open BStarCopyRightStrip BStarCopyRightMark BStarCopyFenceSaturation
open BStarCopyMarkedLedger BStarCopyDownstream

def deposit {L : Type} (labels : Nat→Option L) (i : Nat) (tag : L) (j : Nat) : Option L :=
  if j=i then some tag else labels j

theorem stripWord_deposit {L : Type} (labels : Nat→Option L)
    (tail i : Nat) (ip : 0<i) (it : i≤tail)
    (tag : L) (empty : ∀ j, i≤j → j≤tail → labels j=none) :
    stripWord tail (deposit labels i tag)=stripWord tail labels++[tag] := by
  let pre := List.range' 1 (i-1)
  let post := List.range' (i+1) (tail-i)
  have ix : 1 + 1 * (i-1)=i := by omega
  have ll : i-1 + (tail-i+1)=tail := by omega
  have E : List.range' 1 tail=pre++i::post := by
    rw [←ll,←List.range'_append,ix,List.range'_succ]
  have nil_map : ∀ (a : List Nat) (f : Nat→List L), (∀ j∈a,f j=[]) → a.flatMap f=[] := by
    intro a f h
    induction a with
    | nil => rfl
    | cons a q ih =>
      rw [List.flatMap_cons,h _ (by simp),ih (fun i M => h i (List.mem_cons_of_mem _ M))]
      rfl
  have A : post.flatMap (fun j => (labels j).toList)=[] := by
    apply nil_map
    intro j M
    obtain ⟨k,K,E⟩ := List.mem_range'.mp M
    rw [empty j (by omega) (by omega)]
    rfl
  have D : post.flatMap (fun j => (deposit labels i tag j).toList)=[] := by
    apply nil_map
    intro j M
    obtain ⟨k,K,E⟩ := List.mem_range'.mp M
    simp [deposit,show j≠i by omega,empty j (by omega) (by omega)]
  have C : pre.flatMap (fun j => (deposit labels i tag j).toList)=
      pre.flatMap (fun j => (labels j).toList) := by
    suffices H : ∀ (a : List Nat), (∀ j∈a,j≠i) →
       a.flatMap (fun j => (deposit labels i tag j).toList)=
       a.flatMap (fun j => (labels j).toList) by
      apply H
      intro j M
      obtain ⟨k,K,E⟩ := List.mem_range'.mp M
      omega
    intro a h
    induction a with
    | nil => rfl
    | cons a q ih =>
      simp only [List.flatMap_cons,deposit,if_neg (h a (by simp))]
      exact congrArg _ (ih (fun j M => h j (List.mem_cons_of_mem _ M)))
  unfold stripWord
  rw [E]
  simp only [List.flatMap_append,List.flatMap_cons,C,D,A,empty i (by omega) it]
  simp [deposit]

theorem deposit_ordered {L : Type} (plan : List L) (s : Ledger L)
    (labels : Nat→Option L) (tail i : Nat) (ip : 0<i) (it : i≤tail)
    (tag : L) (todo : List L) (orig : s.release.pending=tag::todo)
    (empty : ∀ j, i≤j → j≤tail → labels j=none)
    (H : OrderedPrefix plan s (stripWord tail labels)) :
    OrderedPrefix plan (s.releaseOne tag todo) (stripWord tail (deposit labels i tag)) := by
  rw [stripWord_deposit labels tail i ip it tag empty]
  exact .mark H (.issue s _ tag todo orig)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "updateRing" => AllSizeS1Geometry.step (n:=n) B

/-- The physical unvisited suffix certificate gives ghost vacancies
even when arbitrary labels carry duplicate bytes. A nonempty ghost
label encodes DATA and cannot match a physically empty slot. -/
theorem empty_behind_cut {L : Type} (digits : L→BitVec 36)
    (x : X) (base : Fin n) (seam tail i : Nat) (is : seam≤i) (ip : 0<i)
    (labels : Nat→Option L) (matched : MobileMatches digits x base seam tail labels)
    (S : List (BStarAcquireVisitOrder.Pos n)) (fall : BStarAcquireVisitOrder.Pos n)
    (len cut : Nat) (vacant : CutVacant x S fall len cut true)
    (behind : ∀ j, i≤j → j≤tail → Unvisited S fall len cut true (addr base j)) :
    ∀ j, i≤j → j≤tail → labels j=none := by
  intro j I T
  have old := matched j (by omega) T
  have U := vacant _ (behind j I T)
  have H : rail seam j=.rs := if_neg (by omega)
  rw [H] at old
  change (readLane (Sheet.index .rs) (x (addr base j)).long).mobile=.empty at U
  rw [U] at old
  cases h : labels j with
  | none => rfl
  | some tag => rw [h] at old; contradiction

def lanes (x : X) (i : Fin n) (sh : Sheet) : Lane := readLane (Sheet.index sh) (x i).long

def NoPrepExcept (x : X) (e base : Fin n) (seam tail i : Nat) : Prop :=
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  ∀ (j : Nat) (s : Side), 0<j → j≤tail → j≠i → site e s=addr base j →
    (⟨s,rail seam j⟩ : At Sheet)∉reserved (round (oldPair B x e) raw).prep

theorem ring_blocked_spectator (x : X) (base : Fin n) (seam tail i k j : Nat)
    (C : Strip B x base seam tail) (kt : k<tail)
    (jp : 0<j) (jt : j≤tail) (J : j≠i)
    (scope : NoPrepExcept hp x (addr base k) base seam tail i)
    (block : let e := addr base k
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      let rs := reserved (round (oldPair B x e) raw).prep
      L (rail seam k)∈rs ∨ R (rail seam (k+1))∈rs)
    (sep : addr base k≠rightNeighbor (addr base k)) :
    lanes (updateRing x (addr base k)) (addr base j) (rail seam j) =
      lanes x (addr base j) (rail seam j) := by
  dsimp only at block
  let e := addr base k
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let rs := reserved (round (oldPair B x e) raw).prep
  have nobid := strip_reserved_blocks (b:=B) (x:=x) (base:=base) (seam:=seam) (i:=k) rs block
  have H := strip_pair_frame hp x base seam tail k kt C (Or.inl nobid)
  by_cases A : j=k
  · subst j
    let s := L (rail seam k)
    have S : s∉rs := scope k .left jp jt J rfl
    have Hs := H s (.inr rfl) S
    change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) s=view raw s at Hs
    rw [new_access hp x e s sep,old_access] at Hs
    exact Hs
  · by_cases E : j=k+1
    · subst j
      let s := R (rail seam (k+1))
      have V : site e .right=addr base (k+1) := (addr_next base k).symm
      have S : s∉rs := scope (k+1) .right jp jt J V
      have Hs := H s (.inl rfl) S
      change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) s=view raw s at Hs
      rw [new_access hp x e s sep,old_access] at Hs
      change readLane (Sheet.index (rail seam (k+1))) (updateRing x e (site e .right)).long =
        readLane (Sheet.index (rail seam (k+1))) (x (site e .right)).long at Hs
      rw [V] at Hs
      exact Hs
    · unfold lanes
      rw [ring_other_positions hp x base k j tail kt jp jt C.tail_lt A E]

theorem ring_tail_exterior (x : X) (base : Fin n) (seam tail j : Nat)
    (C : Strip B x base seam tail) (jp : 0<j) (jt : j≤tail) (ne : j≠tail) :
    updateRing x (addr base tail) (addr base j)=x (addr base j) := by
  have tailN := C.tail_lt
  apply ring_exterior_frame hp x base (addr base tail) j jp
  · intro H
    exact ne ((addr_inj base C.tail_lt (by omega) H).symm)
  · intro H
    have K := addr_inj base C.tail_lt (by omega) H
    omega

/-- Actual licensed deposition; its reservation suppresses simultaneous
data on the same strip link. Other upstream slots are framed, without
assuming anything about unrelated lanes. -/
theorem ring_deposit {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    (x : X) (e base : Fin n) (side : Side) (seam tail i : Nat)
    (C : Strip B x base seam tail) (is : seam≤i) (it : i≤tail)
    (loc : site e side=addr base i) (sep : e≠rightNeighbor e)
    (labels : Nat→Option Tag) (matched : MobileMatches digits x base seam tail labels)
    (scope : NoPrepExcept hp x e base seam tail i)
    (win : BStarCopyInjection.injection side true∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1)
    (gate : (lanes x (addr base i) .rs).gate=true)
    (captured : (lanes x (addr base i) .rs).frozen=.data (digits (atSource i)))
    (vacant : labels i=none) :
    MobileMatches digits (updateRing x e) base seam tail (deposit labels i (atSource i)) := by
  have ip : 0<i := by have := C.seam_pos; omega
  have rs : rail seam i=.rs := if_neg (by omega)
  have E := matched i ip it
  rw [vacant,rs] at E
  have old : (lanes x (addr base i) .rs).mobile=.empty := E
  have G : (lanes x (site e side) .rs).gate=true := loc.symm ▸ gate
  have F : (lanes x (site e side) .rs).frozen=.data (digits (atSource i)) := loc.symm ▸ captured
  have A : (lanes x (site e side) .rs).mobile=.empty := loc.symm ▸ old
  have out := congrArg Lane.mobile (BStarCopyOperand.ring_inject hp x e sep side true
    (digits (atSource i)) win G F A)
  change (lanes (updateRing x e) (site e side) .rs).mobile=.data (digits (atSource i)) at out
  rw [loc] at out
  have booked : (⟨side,rail seam i⟩ : At Sheet)∈
      reserved (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep := by
    rw [rs]
    exact List.mem_map.mpr ⟨_,win,rfl⟩
  intro j jp jt
  by_cases J : j=i
  · subst j
    rw [rs]
    change (lanes (updateRing x e) (addr base i) .rs).mobile =
      encode digits (deposit labels i (atSource i) i)
    rw [out]
    simp [deposit,encode]
  · have same : lanes (updateRing x e) (addr base j) (rail seam j)=lanes x (addr base j) (rail seam j) := by
      cases side with
      | left =>
        change e=addr base i at loc
        subst e
        by_cases V : i=tail
        · subst i
          unfold lanes
          rw [ring_tail_exterior hp x base seam tail j C jp jt J]
        · exact ring_blocked_spectator hp x base seam tail i i j C (by omega) jp jt J scope
            (Or.inl booked) sep
      | right =>
        have D : e=addr base (i-1) := by
          apply rightNeighbor_inj
          rw [←addr_next,show i-1+1=i by omega]
          exact loc
        subst e
        have G : i-1+1=i := by omega
        apply ring_blocked_spectator hp x base seam tail i (i-1) j C (by omega) jp jt J scope
        · apply Or.inr
          rw [G]
          exact booked
        · exact sep
    change (lanes (updateRing x e) (addr base j) (rail seam j)).mobile = _
    rw [same]
    simp only [deposit,if_neg J]
    exact matched j jp jt

/-- Same physical deposition extends the ordered ledger by the actual
captured occurrence. The original right-side plan is a table indexed
by strip address. At this visit the pending suffix must be the actual
not-yet-visited range, not an arbitrary list carrying equal bytes. -/
theorem deposit_at_cut {Tag : Type} (digits : Tag→BitVec 36) (atSource : Nat→Tag)
    (x : X) (e base : Fin n) (side : Side) (seam tail i : Nat)
    (C : Strip B x base seam tail) (is : seam≤i) (it : i≤tail)
    (loc : site e side=addr base i) (sep : e≠rightNeighbor e)
    (labels : Nat→Option Tag) (matched : MobileMatches digits x base seam tail labels)
    (scope : NoPrepExcept hp x e base seam tail i)
    (win : BStarCopyInjection.injection side true∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1)
    (gate : (lanes x (addr base i) .rs).gate=true)
    (captured : (lanes x (addr base i) .rs).frozen=.data (digits (atSource i)))
    (S : List (BStarAcquireVisitOrder.Pos n)) (fall : BStarAcquireVisitOrder.Pos n)
    (len cut : Nat) (vacant : CutVacant x S fall len cut true)
    (behind : ∀ j, i≤j → j≤tail → Unvisited S fall len cut true (addr base j))
    (s : Ledger Tag)
    (pending : s.release.pending=(List.range' i (tail+1-i)).map atSource)
    (old : OrderedPrefix ((List.range' seam (tail+1-seam)).map atSource) s (stripWord tail labels)) :
    let next := deposit labels i (atSource i)
    let rest := (List.range' (i+1) (tail-i)).map atSource
    MobileMatches digits (updateRing x e) base seam tail next ∧
      OrderedPrefix ((List.range' seam (tail+1-seam)).map atSource)
        (s.releaseOne (atSource i) rest) (stripWord tail next) := by
  dsimp only
  have ip : 0<i := by have := C.seam_pos; omega
  have empty := empty_behind_cut digits x base seam tail i is ip labels matched S fall len cut vacant behind
  have word : s.release.pending=atSource i::(List.range' (i+1) (tail-i)).map atSource := by
    rw [pending, show tail+1-i=(tail-i)+1 by omega, List.range'_succ]
    rfl
  exact ⟨ring_deposit hp digits atSource x e base side seam tail i C is it loc sep
    labels matched scope win gate captured (empty i (by omega) it),
    deposit_ordered _ s labels tail i ip it _ _ word empty old⟩

end L4.BStarCopyRightDeposit

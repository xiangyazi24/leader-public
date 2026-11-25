import Leader.L4.BStarDirtyReplySweep
import Leader.L4.BStarResetChartNomination
import Leader.L4.BStarClearanceReturnCharge
import Leader.L4.BStarClearanceIndexedSum

namespace L4.BStarClearanceReplyService
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarH6WordChart BStarLongFiberOwner
open BStarAcquireForwardTrace BStarLongFixedRouting BStarResetMarkAdapter BStarSeparatingProgress
open BStarClearanceReturnCharge BStarClearanceIndexedSum
open BStarLongTransport BStarLongRouting BStarLongCommand BStarLongEvents
open BStarDirtyReplySweep
open BStarResetChartTouch BStarAcquireRailCoverage

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem reverse_is_actual (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (q : Payload)
    (h : (C,.reverse (.reply q))∈BStarLongCommandData.gated g raw) :
    (C,.reverse (.reply q))∈actualOffers g raw := by
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round
  simp only [List.mem_map]
  refine ⟨_,⟨_,h,rfl⟩,?_⟩
  unfold BStarLongGrant.update
  dsimp only
  split <;> rfl

def replyDistance (S : List (Pos n)) (u : Pos n) := S.length+1-distance S u

theorem replyDistance_idx {S : List (Pos n)} (nd : S.Nodup)
    {j : Nat} (hj : j<S.length) : replyDistance S S[j]=j+1 := by
  unfold replyDistance
  rw [distance_idx nd hj]
  omega

/-- Reply rank depends only on the raw D-class and its chart address,
not on the operation-specific binding or failure bits. -/
theorem returnRank_count (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (d : Nat) :
    returnRank g a d (readRaw raw a)=d*BStarClearanceCommandFrame.returnCount (readK raw a) := by
  unfold returnRank
  exact congrArg (fun z : Nat × Nat × Nat => d*z.2.1)
    (BStarClearanceCommandFrame.bind_counts (geometry g a.side) a.occurrence (readK raw a))

/-- Nominate an actual mark for a noninitial old reply once its
predecessor is not a forward. Even a malformed reply is charged.
The resulting strict decrease is for exactly this selected two-slot
footprint, before adding the other disjoint owner footprints. -/
theorem nominate_reverse {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (same : ∀ i, Layout B base i=Layout B x i)
    {j : Nat} (hj : j<len) (pay : Payload)
    (D : atCursor x (S.getD (j+1) fall)=.reply pay)
    (noF : ∀ p, atCursor x (S.getD j fall)≠.forward p) :
    ∃ e C a q, let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))
      (C,.reverse (.reply q))∈actualOffers g raw ∧
      address e C.source=S.getD j fall ∧ address e a=S.getD (j+1) fall ∧
      C.destination=some a ∧
      returnRank g C.source (replyDistance S (address e C.source)) (readRaw y C.source)+
        returnRank g a (replyDistance S (address e a)) (readRaw y a) <
      returnRank g C.source (replyDistance S (address e C.source)) (readRaw raw C.source)+
        returnRank g a (replyDistance S (address e a)) (readRaw raw a) := by
  obtain ⟨e,E⟩ := BStarResetChartNomination.nominate hp chart head cont j (by omega)
  have L := E x same
  rw [if_pos hj] at L
  obtain ⟨_,C,a,hC,hA,U,V⟩ := (mem_link hp _ _ _ _ _).mp L
  change S.getD j fall=address e C.source at U
  change S.getD (j+1) fall=address e a at V
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have noF' : ∀ p, readK raw C.source≠.forward p := by
    intro q
    rw [BStarResetRailRing.old_read]
    change atCursor x (address e C.source)≠.forward q
    rw [←U]
    exact noF q
  have old : readK raw a=.reply pay := by
    rw [BStarResetRailRing.old_read]
    change atCursor x (address e a)=.reply pay
    rwa [←V]
  obtain ⟨q,_,G⟩ := reverse_predecessor g raw C a pay hC hA noF' old
  have act := reverse_is_actual g raw C q G
  have S0 := BStarAcquireReturn.link_shape g C a hC hA
  have dp : replyDistance S (address e a)=replyDistance S (address e C.source)+1 := by
    unfold replyDistance
    have length := chart.length
    rw [←U,←V,←List.getElem_eq_getD (h:=show j<S.length by omega),
      ←List.getElem_eq_getD (h:=show j+1<S.length by omega),
      distance_idx chart.nodup,distance_idx chart.nodup]
    omega
  have K := joined_reverse_pays k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
    C a (.reply q) (replyDistance S (address e C.source)) hA S0.1.symm act (by
      rintro b (rfl|rfl) h6 H
      · exact (S0.2.2 (by simpa [R] using congrArg (fun x : AtK => x.side) h6)
          (by simpa [R] using congrArg (fun x : AtK => x.occurrence) h6)).elim
      · have T := (BStarAcquireJoinedHop.k0_dest g C b hC hA
          (by simpa [R] using congrArg (fun x : AtK => x.occurrence.val) h6)).2
        change g.2.axes.h6=true at H
        rw [T] at H
        contradiction)
  refine ⟨e,C,a,q,act,U.symm,V.symm,hA,?_⟩
  rw [dp]
  exact K

/-- In an E/T suffix, a run of trails ends at the inclusive terminal
or has an empty next position. This uses no scheduler assumption. -/
private theorem terminal_or_empty (u : Nat → Token) (len : Nat)
    (quiet : ∀ j≤len, u j=.empty ∨ u j=.trail)
    (someT : ∃ j≤len, u j=.trail) :
    ∃ j≤len, u j=.trail ∧ (j=len ∨ j<len ∧ u (j+1)=.empty) := by
  obtain ⟨start,H,T⟩ := someT
  have go (d : Nat) : ∀ j, j≤len → len-j=d → u j=.trail →
      ∃ k≤len, u k=.trail ∧ (k=len ∨ k<len ∧ u (k+1)=.empty) := by
    induction d using Nat.strongRecOn with
    | ind d rec =>
      intro j bound E ht
      by_cases eq : j=len
      · exact ⟨j,bound,ht,.inl eq⟩
      rcases quiet (j+1) (by omega) with emp|next
      · exact ⟨j,bound,ht,.inr ⟨by omega,emp⟩⟩
      · exact rec (len-(j+1)) (by omega) (j+1) (by omega) rfl next
  exact go _ start H rfl T

private theorem safe_link_destination (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (a : AtK) (hc : C∈orderedCommands g) (ha : C.destination=some a) :
    BStarResetQuietTable.DoorSafe g raw a := by
  by_cases ar : a=R 0
  · subst a
    have h := (BStarAcquireJoinedHop.k0_dest g C (R 0) hc ha rfl).2
    refine ⟨fun _ H => by rw [h] at H; contradiction,?_⟩
    intro _ c k A _
    have M : c∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨_,A,rfl⟩
    have D := (BStarK0Frame.door_eq g raw c k A).1
    have hh := (BStarResetChartIndex.selected_door g c M (D ▸ rfl)).2.1
    rw [h] at hh
    contradiction
  · exact BStarResetQuietTable.safe_nonright g raw a ar

/-- From a nonempty E/T command rail, select a literal terminal/TE mark
that removes one trail. In TE the old Empty destination stays Empty. -/
theorem nominate_trail {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (same : ∀ i, Layout B base i=Layout B x i)
    (quiet : ∀ j≤len, atCursor x (S.getD j fall)=.empty ∨ atCursor x (S.getD j fall)=.trail)
    (someT : ∃ j≤len, atCursor x (S.getD j fall)=.trail) :
    ∃ e C, let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))
      (C,.clear) ∈ actualOffers g raw ∧
      (∃ j≤len, S.getD j fall=address e C.source) ∧
      ((C.kind=.terminal ∧ BStarClearanceCommandFrame.trail (readK y C.source)+1=
        BStarClearanceCommandFrame.trail (readK raw C.source)) ∨
        ∃ a, C.destination=some a ∧
          (BStarClearanceCommandFrame.trail (readK y C.source)+
            BStarClearanceCommandFrame.trail (readK y a))+1=
          BStarClearanceCommandFrame.trail (readK raw C.source)+
            BStarClearanceCommandFrame.trail (readK raw a)) := by
  obtain ⟨j,hj,T,R⟩ := terminal_or_empty (fun j => atCursor x (S.getD j fall)) len quiet someT
  obtain ⟨e,E⟩ := BStarResetChartNomination.nominate hp chart head cont j hj
  have H := E x same
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have boundT (C : CommandClaim) (U : S.getD j fall=address e C.source) :
      bound g (readK raw) C.source=.trail := by
    have D : readK raw C.source=.trail := by
      rw [BStarResetRailRing.old_read]
      change atCursor x (address e C.source)=.trail
      rwa [←U]
    exact (BStarResetQuiet.quiet_bound g (readK raw) C.source (.inr D)).trans D
  rcases R with rfl|⟨lt,next⟩
  · rw [if_neg (Nat.lt_irrefl _)] at H
    obtain ⟨C,Cm,kind,_,K,U⟩ := (mem_terminal hp _ _ _ _).mp H
    have safe : C.source≠R 0 := by
      intro Z
      rw [Z] at K
      contradiction
    exact ⟨e,C,BStarResetQuiet.actual_trail_terminal _ _ _ Cm kind (boundT C U),
      ⟨j,hj,U⟩,.inl ⟨kind,joined_trail_pays k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x e,x (rightNeighbor e)) C Cm (boundT C U) (.inl kind) (fun h _ => (safe h).elim)⟩⟩
  · rw [if_pos lt] at H
    obtain ⟨_,C,a,Cm,D,U,V⟩ := (mem_link hp _ _ _ _ _).mp H
    have Q := BStarAcquireReturn.link_shape g C a Cm D
    have emp : readK raw a=.empty := by
      rw [BStarResetRailRing.old_read]
      change atCursor x (address e a)=.empty
      change S.getD (j+1) fall=address e a at V
      rwa [←V]
    have Bm := (BStarResetQuiet.quiet_bound g (readK raw) a (.inl emp)).trans emp
    have nonzero : C.source≠R 0 := by
      intro M
      exact (Q.2.2 (by rw [M]; rfl)) (by rw [M]; rfl)
    exact ⟨e,C,actual_unsupported_trail g raw C a Cm Q.2.1 D (boundT C U) Bm,
      ⟨j,hj,U⟩,.inr ⟨a,D,joined_unsupported_pair_pays k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x e,x (rightNeighbor e)) C a Q.2.1 D Q.1.symm Cm (boundT C U) emp
        (not_discarded hp chart same e (j+1) (by omega) a V)
        (safe_link_destination g raw C a Cm D) (fun h _ => (nonzero h).elim)⟩⟩

end L4.BStarClearanceReplyService

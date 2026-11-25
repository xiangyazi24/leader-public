import Leader.L4.BStarClearanceForwardService

namespace L4.DirtyPrepFrontier
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongTransport BStarLongCommand BStarLongWork BStarLongRouting BStarLongEvents
open BStarClearanceGate BStarClearanceForward BStarResetQuiet BStarResetQuietTable

theorem incoming_holds (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK) (p : Payload)
    (hc : c∈orderedCommands g) (lk : c.kind=.link) (hd : c.destination=some a)
    (pre : ∀ q, bound g (readK x) c.source≠.forward q)
    (cur : bound g (readK x) a=.forward p) :
    (c,.hold)∈actualOffers g x := by
  have hv : classify c (geometry g c.source.side) (bound g (readK x) c.source)
      ((c.destination.map (bound g (readK x))).getD .empty)=.hold := by
    rw [hd]
    simp only [Option.map_some,Option.getD_some,cur]
    cases H : bound g (readK x) c.source with
    | forward q => exact (pre q H).elim
    | empty | trail | reply => simp [classify,lk] <;> rfl
  have C : (c,.hold)∈offersOn g (readK x) := List.mem_map.mpr
    ⟨c,hc,congrArg (Prod.mk c) hv⟩
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round BStarLongCommandData.gated
  simp only [List.mem_map]
  refine ⟨(c,.hold),⟨(c,.hold),⟨(c,.hold),C,rfl⟩,rfl⟩,?_⟩
  unfold BStarLongGrant.update
  dsimp only
  split <;> rfl

theorem incoming_debt (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (Cm : CommandClaim) (a : AtK) (pay : Payload)
    (lk : Cm.kind=.link) (hd : Cm.destination=some a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    Cm∈orderedCommands g →
    (∀ q, bound g (readK raw) Cm.source≠.forward q) →
    bound g (readK raw) a=.forward pay →
    DoorSafe g raw a →
    ranked g a 0 (readRaw y a)≤ranked g a 0 (readRaw raw a) := by
  dsimp only
  intro C P F S
  have H := incoming_holds _ _ Cm a pay C lk hd P F
  exact BStarClearanceNonforward.joined_idle_rank k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a 0
    (hold_avoids _ _ Cm H a (by simp [Claim.slots,hd])) S

theorem prep_no_fence (g : LongGeometry) (a : Fin 11) (h : a.val≤5) :
    BStarLongCommandData.fenceSheet g a=none := by
  have E : a.val=0 ∨ a.val=1 ∨ a.val=2 ∨ a.val=3 ∨ a.val=4 ∨ a.val=5 := by omega
  rcases E with E|E|E|E|E|E <;> simp [BStarLongCommandData.fenceSheet,E]

/-- For every prep occurrence, selected forward output cannot be held
by data. The only nonadvance alternative is an exact race observation
nomination. This statement does not equate nomination with an observed
write when normalization would win that raw mark. -/
theorem nominate_prep (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload)
    (hc : c∈orderedCommands g) (nd : c.kind≠.door)
    (prep : c.source.occurrence.val≤5)
    (old : bound g (readK raw) c.source=.forward p) :
    (∃ q,(c,.advance q)∈actualOffers g raw) ∨
    ((c,.hold)∈actualOffers g raw ∧
      ∃ side v, (p.race.toNat=2 → side=.left) ∧ (p.race.toNat=3 → side=.right) ∧
        observe ⟨side,c.source.occurrence⟩ (geometry g c.source.side) p=some v) := by
  rcases BStarClearanceBlockade.nominated_forward g raw c p hc nd old with A|R|F
  · exact .inl A
  · exact .inr R
  · obtain ⟨_,s,H,_⟩ := F
    rw [prep_no_fence _ _ prep] at H
    contradiction

private theorem healthy_normalization_avoids (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (p : Payload) (B : bound g (readK raw) a=.forward p)
    (H : p.fault=0) (J : a.occurrence.val=1) : avoids a (normalization g (readK raw)) := by
  intro w hw E
  rcases List.mem_append.mp hw with h|h
  · obtain ⟨q,_,h⟩ := List.mem_filterMap.mp h
    dsimp only at h
    split at h
    · rename_i F
      have eq : q=a := (congrArg Prod.fst (Option.some.inj h)).trans E
      subst q
      simp [B,isFault,H] at F
    · contradiction
  · obtain ⟨q,hq,h⟩ := List.mem_map.mp h
    have eq : q=a := (congrArg Prod.fst h).trans E
    subst q
    have K : a=L 8 ∨ a=L 9 ∨ a=R 8 ∨ a=R 9 := by
      unfold discarded at hq
      split at hq <;> split at hq <;> simp_all only [List.nil_append,List.append_nil,
        List.cons_append,List.not_mem_nil,List.mem_cons,or_false] <;> (first | exact .inr (.inr hq) | exact hq.elim (fun e => .inl e) (fun e => .inr (.inl e)) | exact hq | simp)
    rcases K with rfl|rfl|rfl|rfl <;> contradiction

/-- The exact incoming nominated mark for a least forward can only
observe the extant token. When the old wire is already normalized,
its successful race observation strictly reduces bounded debt. -/
theorem incoming_observes (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (a : AtK) (u v : Payload)
    (ha : a.occurrence.val≠0) (lk : C.kind=.link) (hd : C.destination=some a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    C∈orderedCommands g →
    (∀ q, bound g (readK raw) C.source≠.forward q) →
    bound g (readK raw) a=.forward u →
    avoids a (normalization g (readK raw)) →
    observe a (geometry g a.side) u=some v →
    readRaw y a=encode (.forward v) ∧
      ranked g a 0 (readRaw y a)<ranked g a 0 (readRaw raw a) := by
  dsimp only
  intro H N F A O
  have T := incoming_holds _ _ C a u H lk hd N F
  have M := hold_avoids _ _ C T a (by simp [Claim.slots,hd])
  exact BStarClearanceObserveJoined.observed_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a ha u v 0
    (fun w h => (List.mem_append.mp h).elim (A w) (M w)) F O

/-- No extra canonicalization hit is budgeted. Healthy observations
are exclusively at K1 and the normalization list cannot name that
healthy slot, even if unused argument padding was present. -/
theorem incoming_observes_exact (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (a : AtK) (u v : Payload)
    (lk : C.kind=.link) (hd : C.destination=some a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    C∈orderedCommands g →
    (∀ q, bound g (readK raw) C.source≠.forward q) →
    bound g (readK raw) a=.forward u →
    observe a (geometry g a.side) u=some v →
    readRaw y a=encode (.forward v) ∧
      ranked g a 0 (readRaw y a)<ranked g a 0 (readRaw raw a) := by
  dsimp only
  intro H N F O
  have G : (u.fault==0 && gate u.opcode.toNat a.occurrence
      (geometry (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x) a.side))=true := by
    unfold observe at O
    split at O
    · assumption
    · contradiction
  have L := beq_iff_eq.mp (Bool.and_eq_true_iff.mp G).1
  have K := (Bool.and_eq_true_iff.mp G).2
  unfold gate at K
  have J := beq_iff_eq.mp (Bool.and_eq_true_iff.mp K).1
  exact incoming_observes k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C a u v
    (by omega) lk hd H N F (healthy_normalization_avoids _ _ a u F L J) O

/-- Any actual touching mark before departure weakly spends or
preserves the old prep debt, unless it actually advances this slot.
The predecessor exclusion is supplied by least-forward order; the
explicit source-door hook covers WAIT rather than a fresh issue. -/
theorem prep_mark_cases (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (a : AtK) (u : Payload) (prep : a.occurrence.val≤5) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    bound g (readK raw) a=.forward u →
    DoorSafe g raw a →
    (∀ C∈orderedCommands g, C.destination=some a →
      (∀ q, bound g (readK raw) C.source≠.forward q)) →
    (∀ C∈orderedCommands g, C.kind=.door → C.source=a →
      ranked g a 0 (readRaw y a)≤ranked g a 0 (readRaw raw a)) →
    (∃ C q, (C,.advance q)∈actualOffers g raw ∧ C.source=a) ∨
      ranked g a 0 (readRaw y a)≤ranked g a 0 (readRaw raw a) := by
  classical
  dsimp only
  intro F S N D
  let g := Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  by_cases touch : ∃ C∈orderedCommands g,a∈C.slots
  · obtain ⟨C,H,A⟩ := touch
    have Which : a=C.source ∨ C.destination=some a := by
      cases E : C.destination <;> simpa [Claim.slots,E,eq_comm] using A
    rcases Which with E|E
    · subst a
      by_cases door : C.kind=.door
      · exact .inr (D C H door rfl)
      · rcases nominate_prep g raw C u H door prep F with ⟨q,Q⟩|⟨Q,_⟩
        · exact .inl ⟨C,q,Q,rfl⟩
        · exact .inr (BStarClearanceNonforward.joined_idle_rank k₁ k₂ t₂ J₁ J₂ r c p c₁
            hp x C.source 0 (hold_avoids g raw C Q C.source A) S)
    · have L := (BStarAcquireReturn.link_shape g C a H E).2.1
      exact .inr (incoming_debt k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C a u L E H (N C H E) F S)
  · exact .inr (BStarClearanceNonforward.joined_idle_rank k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a 0
      (BStarClearanceChartFootprint.no_touch_middle g raw a (fun C H A => touch ⟨C,H,A⟩)) S)

theorem prep_debt_bounded (g : Pair LongGeometry) (a : AtK) (raw : BitVec 52) :
    ranked g a 0 raw ≤ 2 := by
  unfold ranked
  cases bind (geometry g a.side) a.occurrence (decode raw) with
  | empty | trail | reply => exact Nat.zero_le _
  | forward p => simpa only [forwardRank,Nat.mul_zero,Nat.zero_add] using bounded (geometry g a.side) a.occurrence (.forward p)

end L4.DirtyPrepFrontier

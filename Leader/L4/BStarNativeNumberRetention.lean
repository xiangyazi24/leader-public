import Leader.L4.BStarNumericWordFrame
import Leader.L4.BStarNativeReceiptTape
import Leader.L4.BStarAliasRoster

namespace L4.BStarNativeNumberRetention
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongClaims
open BStarLongWork BStarLongTransport BStarNumericFrame BStarLongDoor

open BStarNumericCarry BStarLongEvents BStarLongCommand BStarLongArithmetic
open BStarLongRegisters BStarLongRouting

private theorem in_numeric (i b : Nat) (H : b<widthAt wordWidths i) :
    (numeric i).offset+b<728 := by
  have K := range_bound wordWidths i
  rw [manifest_registers.2.1] at K
  change offsetAt wordWidths i+b<728
  omega

private theorem field_of_frame (i : Nat) (q : Patch LW) (H : Frame q) :
    FieldFrame (numeric i) q := fun b B => H _ (in_numeric i b B)

private theorem visit_other (g : LongGeometry) (k : Fin 11) (x : BitVec LW) (p : Payload)
    (j : Nat) (excluded : p.fault=0 → nodeOf p.opcode.toNat≠some j) :
    FieldFrame (numeric j) (visit g k x p).1 := by
  by_cases h : p.fault=0
  · unfold visit
    split
    · exact field_of_frame _ _ zero
    split
    · exact field_of_frame _ _ zero
    · rename_i i I
      split
      · exact field_of_frame _ _ zero
      · exact digit_other _ _ i j p _ (fun e => excluded h (e ▸ I))
  · have E : (visit g k x p).1=.empty _ := by
      have V : (p.fault != 0)=true := bne_iff_ne.mpr h
      simp only [visit,V,Bool.or_true,if_true]
    rw [E]
    exact field_of_frame _ _ zero

private theorem selected_num_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) (j : Nat) (s : Bool)
    (guard : ∀ p, o.2=.advance p → (o.1.source.side==.right)=s →
      o.1.source.occurrence.val=1 → p.fault=0 → nodeOf p.opcode.toNat≠some j) :
    ∀ t∈(selected g x o).work,t.1=s → FieldFrame (numeric j) t.2 := by
  obtain ⟨c,q⟩ := o
  cases q <;> simp only [selected]
  all_goals try (intro t ht; simp at ht; done)
  · split
    · intro t ht; simp at ht
    · intro t ht _
      obtain rfl := List.mem_singleton.mp ht
      have hp := ‹BStarLongDoor.oldDoor _ _=.write _›
      apply field_of_frame
      unfold BStarLongDoor.oldDoor at hp
      dsimp only at hp
      repeat first
        | contradiction
        | (injection hp with hp'; rw [← hp']; exact repair_frame)
        | (injection hp with hp'; rw [← hp']; exact issue_frame _ _)
        | (injection hp with hp'; rw [← hp']; exact reply_frame _ _ _)
        | split at hp
    · intro t ht _
      obtain rfl := List.mem_singleton.mp ht
      exact field_of_frame _ _ (accept_frame _ _ _)
  · rename_i p
    intro t ht S
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · by_cases H : c.source.occurrence.val=1
      · exact visit_other _ _ _ _ j (guard p rfl S H)
      · rw [visit_padding _ _ _ _ (.inl H)]
        exact field_of_frame _ _ zero
    · exact field_of_frame _ _ (execute_frame _ _ _ _)

private theorem selected_fold_num_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (acc : Selected) (j : Nat) (s : Bool)
    (H : ∀ t∈acc.work,t.1=s → FieldFrame (numeric j) t.2)
    (rules : ∀ o∈os,∀ p, o.2=.advance p → (o.1.source.side==.right)=s →
      o.1.source.occurrence.val=1 → p.fault=0 → nodeOf p.opcode.toNat≠some j) :
    ∀ t∈(os.foldl (fun acc o => Selected.append acc (selected g x o)) acc).work,
        t.1=s → FieldFrame (numeric j) t.2 := by
  induction os generalizing acc with
  | nil => exact H
  | cons o os ih =>
    apply ih _ _ (fun q h => rules q (List.mem_cons_of_mem _ h))
    intro t ht E
    exact (List.mem_append.mp ht).elim (fun hm => H t hm E)
      (fun hm => selected_num_frame g x o j s (rules o List.mem_cons_self) t hm E)

/-- The actual ordered long-work list frames a numeric field unless
its own endpoint has a selected K1 advance decoding to that register. -/
theorem assignments_other (g : Pair LongGeometry) (x : Pair (BitVec LW)) (j : Nat) (s : Bool)
    (guard : ∀ C p, (C,.advance p)∈actualOffers g x → (C.source.side==.right)=s →
      C.source.occurrence.val=1 → p.fault=0 → nodeOf p.opcode.toNat≠some j) :
    ∀ t∈(longTrace g x).assignments,t.1=s → FieldFrame (numeric j) t.2 := by
  intro t ht E
  simp only [longTrace,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with (((((hn|(rfl|rfl))|ha)|hd)|hw)|hl)
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hn
    exact field_of_frame _ _ (route_frame a)
  · exact field_of_frame _ _ (clear_frame _)
  · exact field_of_frame _ _ (clear_frame _)
  · exact field_of_frame _ _ (grant_frame g x _ t ha)
  · exact field_of_frame _ _ (copy_frame g _ _ t hd)
  · apply selected_fold_num_frame g x (actualOffers g x) ⟨[],[],[]⟩ j s (by simp) _ t hw E
    rintro ⟨C,a⟩ use p rfl
    exact guard C p use
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hl
    exact field_of_frame _ _ (route_frame a)



private theorem scratch_numeric (g : Pair LongGeometry) (orig x : Pair (BitVec LW)) (j : Nat) (s : Bool) :
    (numeric j).read (lane s (patchPair (longScratch g orig) x))=(numeric j).read (lane s x) := by
  -- Scratch masks depend on the side only, not on bytes used to
  -- compute its assigned values.
  have mask : FieldFrame (numeric j) (lane s (longScratch g orig)) := by
    intro i H
    have I := in_numeric j i H
    obtain ⟨L,R⟩ := longScratch_mask g orig ((numeric j).offset+i)
    cases s
    · apply Bool.eq_false_iff.mpr
      intro q
      rcases L.mp q with e|e <;> omega
    · apply Bool.eq_false_iff.mpr
      intro q
      have E := R.mp q
      omega
  cases s <;> exact field_frame _ _ _ mask

/-- Outside an actual selected K1 departure decoding this register
on this endpoint, no literal packed write in the full joined step can
alter the numeric field. This includes foreign work, arbitrary
normalization, outer-door repair and scratch refresh. -/
theorem joined_other (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (j : Nat) (s : Bool) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (∀ C u, (C,.advance u)∈actualOffers g raw → (C.source.side==.right)=s →
      C.source.occurrence.val=1 → u.fault=0 → nodeOf u.opcode.toNat≠some j) →
    (numeric j).read (lane s (Pair.map LargeSite.long (largePair b x)))=
      (numeric j).read (lane s raw) := by
  dsimp only
  intro guard
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  have F : (numeric j).read (lane s (patchPair (longWork g raw) raw)) =
      (numeric j).read (lane s raw) := by
    rw [long_exec]
    exact fold_field _ s _ _ (assignments_other g raw j s guard)
  have Q := scratch_numeric g raw (patchPair w raw) j s
  cases s
  · change (numeric j).read ((w.1.compose q.1).apply raw.1)=(numeric j).read raw.1
    rw [Patch.compose_apply]
    exact Q.trans F
  · change (numeric j).read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      (w.2.compose q.2)).apply raw.2)=(numeric j).read raw.2
    have E : (numeric j).read ((w.2.compose q.2).apply raw.2)=(numeric j).read raw.2 := by
      rw [Patch.compose_apply]
      exact Q.trans F
    cases H : g.2.axes.h6
    · rw [LongDoorGuard.no_authority]; exact E
    · cases V : LongDoorGuard.valid manifest raw.2
      · rw [LongDoorGuard.invalid_override _ _ _ V,Patch.compose_apply]
        exact (field_frame (numeric j) _ _ (field_of_frame _ _ repair_frame)).trans E
      · rw [LongDoorGuard.valid_no_override _ _ _ V]; exact E



open BStarH6WordChart BStarLongLiteral

/-- The right endpoint can never be an old numeric-write initiator:
the literal unique K1 departure is always left-to-right. -/
theorem joined_right (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (j : Nat) :
    (numeric j).read (largePair (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x).2.long=
      (numeric j).read x.2.long := by
  apply joined_other k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x j true
  intro C u sel S K
  have hm : C∈orderedCommands (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x) := by
    rw [←actualOffers_claims _ (Pair.map LargeSite.long x)]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  rw [center_of _ C hm K] at S
  contradiction

/-- Full-ring one-mark field frame. Only the old initiator's actual
selected centre opcode has to be excluded. -/
theorem step_other {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e i : Fin n) (j : Nat) (sep : e≠rightNeighbor e) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    (i=e → ∀ C u, (C,.advance u)∈actualOffers g raw →
      C.source.occurrence.val=1 → u.fault=0 → nodeOf u.opcode.toNat≠some j) →
    (numeric j).read (AllSizeS1Geometry.step b x e i).long=(numeric j).read (x i).long := by
  dsimp only
  intro guard
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  by_cases E : i=e
  · subst i
    change (numeric j).read (AllSizeS1Geometry.step b x e e).long=(numeric j).read (x e).long
    simp only [AllSizeS1Geometry.step,if_pos rfl]
    exact joined_other _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) j false
      (fun C u sel _ J F => guard rfl C u sel J F)
  · by_cases H : i=rightNeighbor e
    · subst i
      change (numeric j).read (AllSizeS1Geometry.step b x e (rightNeighbor e)).long=_
      simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep)]
      exact joined_right _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) j
    · simp [AllSizeS1Geometry.step,E,H]




open BStarGeneratedOwner BStarGeneratedTapeCuts BStarOwnerLaunchOrigin
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors BStarResetChartTouch
open BStarResetMarkAdapter BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

/-- On a known owner's physical K1, every healthy selected write is
from that owner's actual current source instruction. The fact is
proved using old offer provenance and the genuine launch history,
not current byte equality across different owner incidences. -/
theorem selected_owner_pc {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w m)
    (e : Fin n) (k : Nat) (hk : k≤len) (atK : S.getD k fall=(e,1))
    (C : CommandClaim) (u : Payload)
    (sel : let x := run initial w
      (C,.advance u)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    (one : C.source.occurrence.val=1) (healthy : u.fault=0) :
    u.opcode.toNat=pc (run initial w) (S.getD 0 fall).1 := by
  let x := run initial w
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have sel' : (C,.advance u)∈actualOffers g raw := sel
  have M : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel',rfl⟩
  have side : C.source=L 1 := by rw [center_of g C M one]; rfl
  obtain ⟨q,Q,health,opEq⟩ := BStarForwardProvenance.offer_origin g raw C u sel' healthy
  rw [side] at Q
  have F : project (fun j => S.getD j fall) x k=.forward q := by
    change atCursor x (S.getD k fall)=.forward q
    rw [atK]
    exact Q
  have now := at_end hp T
  obtain ⟨mode,_⟩ := healthy_forward_origin hp chart sep T now k hk q F u.opcode.toNat
    health (congrArg BitVec.toNat opEq)
  rw [mode] at now
  exact now.1.2.2.2.symm

private theorem roster_nodup : BStarLongSignatures.tourNodes.Nodup := by
  decide +kernel

/-- Literal numeric node identity is injective over live opcodes. -/
theorem opcode_of_node {a b j : Nat} (A : nodeOf a=some j) (BB : nodeOf b=some j) :
    a=b := by
  have ha : ¬a<13 := by
    intro H
    simp [nodeOf,H] at A
  have hb : ¬b<13 := by
    intro H
    simp [nodeOf,H] at BB
  unfold nodeOf at A BB
  rw [if_neg ha] at A
  rw [if_neg hb] at BB
  have bound : a-13<BStarLongSignatures.tourNodes.length :=
    List.getElem?_eq_some_iff.mp A |>.choose
  have eq := (List.getElem?_inj bound roster_nodup).mp (A.trans BB.symm)
  omega

/-- The distributed word field on the actual owner K1 is retained
over any later region of the marked attempt. The premise is only a
PC exclusion on the original prefix, not a restriction on foreign
offers or on inactive/responder byte writes. -/
theorem retain_interval {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w m)
    (pre tape post : List (Fin n)) (W : w=pre++tape++post)
    (i : Fin n) (k : Nat) (hk : k≤len) (loc : S.getD k fall=(i,1))
    (oldOp j : Nat) (node : nodeOf oldOp=some j)
    (later : ∀ a e b,tape=a++e::b →
      pc (run initial (pre++a)) (S.getD 0 fall).1≠oldOp) :
    (numeric j).read (run (run initial pre) tape i).long=
      (numeric j).read (run initial pre i).long := by
  have frame (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tape=a++e::b) :
      (numeric j).read (step (run (run initial pre) a) e i).long=
        (numeric j).read (run (run initial pre) a i).long := by
    have Y : run (run initial pre) a=run initial (pre++a) :=
      (BStarResetSchedule.run_append step initial pre a).symm
    rw [Y]
    apply BStarNativeNumberRetention.step_other hp _ e i j (sep e)
    intro eq C u sel one hf P
    have D : w=(pre++a)++(e::b++post) := by
      rw [W,E]
      simp only [List.append_assoc,List.cons_append]
    obtain ⟨_,G,_⟩ := BStarGeneratedTapeCuts.split hp (pre++a) (e::b++post) (D ▸ T)
    have L : S.getD k fall=(e,1) := eq ▸ loc
    have origin := selected_owner_pc hp chart sep G e k hk L C u sel one hf
    exact later a e b E (origin.symm.trans (opcode_of_node P node))
  have fold (x : X) (ws : List (Fin n))
      (hold : ∀ a e b,ws=a++e::b →
        (numeric j).read (step (run x a) e i).long=(numeric j).read (run x a i).long) :
      (numeric j).read (run x ws i).long=(numeric j).read (x i).long := by
    induction ws generalizing x with
    | nil => rfl
    | cons e w ih =>
      have q := hold [] e w rfl
      have Q := ih (step x e) (fun a m b H => hold (e::a) m b (congrArg (List.cons e) H))
      exact Q.trans q
  exact fold _ tape frame

/-- After the consumed head has advanced its physical PC, the
entire remaining compiler subword, including intervening launches,
faulted offers and foreign work, retains its distributed word slot. -/
theorem retain_later_native {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode} (rootK : (S.getD 0 fall).2=0)
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w m)
    (band : BStarNativeReceiptTape.CompilerBand hp initial (S.getD 0 fall).1 w)
    (pre tape post : List (Fin n)) (W : w=pre++tape++post)
    (i : Fin n) (k : Nat) (hk : k≤len) (loc : S.getD k fall=(i,1))
    (oldOp j : Nat) (node : nodeOf oldOp=some j)
    (later : oldOp<pc (run initial pre) (S.getD 0 fall).1) :
    (numeric j).read (run (run initial pre) tape i).long=
      (numeric j).read (run initial pre i).long := by
  let root := (S.getD 0 fall).1
  apply retain_interval hp chart sep T pre tape post W i k hk loc oldOp j node
  intro a e b E
  have split : w=pre++(a++(e::b)++post) := by rw [W,E]; simp only [List.append_assoc]
  obtain ⟨_,_,G⟩ := BStarGeneratedTapeCuts.split hp pre (a++(e::b)++post) (split ▸ T)
  obtain ⟨_,F,_⟩ := BStarGeneratedTapeCuts.split hp a ((e::b)++post)
    (show GeneratedOwner hp base (fun r => S.getD r fall) len (run initial pre) _ (a++((e::b)++post)) m by
      simpa only [List.append_assoc] using G)
  have K : BStarNativeReceiptTape.CompilerBand hp (run initial pre) root a := by
    intro u v Eq
    have L : w=(pre++u)++(v++(e::b)++post) := by
      rw [split,Eq]
      simp only [List.append_assoc]
    have H := band (pre++u) (v++(e::b)++post) L
    rw [BStarResetSchedule.run_append] at H
    exact H
  have H := BStarNativeReceiptTape.end_monotone hp rootK sep F K
  rw [←BStarResetSchedule.run_append] at H
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le later H)

#print axioms retain_later_native
#print axioms retain_interval
#print axioms selected_owner_pc
end L4.BStarNativeNumberRetention

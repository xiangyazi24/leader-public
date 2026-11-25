import Leader.L4.BStarCopyCleanupWindow

namespace L4.BStarCopyDrainedHistory
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets
open BStarH6WordChart BStarLongFixedRouting BStarResetChartTouch BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarAcquireAnchors BStarClearanceDataChart
open BStarResetMarkAdapter BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin
open BStarCopyCleanupFrame BStarCopyCleanupCoverage BStarCopyEntryGates BStarCopyGateAuthority

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarCopyCleanupWindow BStarLongFiberOwner BStarClearanceMobileOwner

theorem drained_step {base x : X} (e : Fin n) (sep : e≠rightNeighbor e) (o : Int)
    (layout : ∀ i, Layout B base i=Layout B x i)
    (nextLayout : ∀ i, Layout B base i=Layout B (step x e) i)
    (old : DrainedOwner hp base x o) (no : NoOwnerInject hp base x e o) :
    DrainedOwner hp base (step x e) o := by
  intro i sh act own
  have E := congrArg (fun t : Bool×Bool×Bool => t.2.1) ((layout i).symm.trans (nextLayout i))
  have oldAct : activeSheet (longGeometry B (x i)) sh=true := by
    cases sh <;> first | rfl | exact E.trans act
  apply ring_drained hp x e i sh sep (old i sh oldAct own)
  · intro q Q U V
    exact no q Q (by rwa [U,V])
  · right
    let g := oldPair B x e
    let raw := ((x e).long,(x (rightNeighbor e)).long)
    dsimp only
    intro d M a ma I Sh
    let h := oldH6 B x
    have key (v : At Sheet) :
        pairOwner (total h) (word h e) g.2.axes.h6 dataDispl v =
        dataOwner (oldH6 B base) (site e v.side) v.occurrence := by
      have H : oldH6 B x=oldH6 B base := funext fun i => (congrArg Prod.fst (layout i)).symm
      change pairOwner (total h) (word h e) (h (rightNeighbor e)) dataDispl v=_
      rw [←physical_pair_owner]
      change dataOwner (oldH6 B x) _ _=_
      rw [H]
    have da : dataOwner (oldH6 B base) (site e d.source.side) d.source.occurrence=o := by
      rw [←key d.source]
      cases Ds : d.destination with
      | none =>
        have A : a=d.source := by simpa [Claim.slots,Ds] using ma
        rw [←A,key a,I,Sh]
        exact own
      | some b =>
        have A : a=d.source ∨ a=b := by simpa [Claim.slots,Ds] using ma
        rcases A with A|A
        · rw [←A,key a,I,Sh]
          exact own
        · subst b
          rw [data_owner g (total h) (word h e) _ d a M Ds,key a,I,Sh]
          exact own
    have srcM : d.source∈d.slots := by cases H : d.destination <;> simp [Claim.slots,H]
    have ac : activeSheet (longGeometry B (x (site e d.source.side))) d.source.occurrence=true := by
      cases J : d.source.occurrence
      · rfl
      · have K := BStarCopyPaddingFrame.data_active g _ d d.source M srcM (.inl J)
        cases hs : d.source.side <;> simpa [g,oldPair,geometry,site,hs,activeSheet] using K
      · have K := BStarCopyPaddingFrame.data_active g _ d d.source M srcM (.inr J)
        cases hs : d.source.side <;> simpa [g,oldPair,geometry,site,hs,activeSheet] using K
      · rfl
    have emp := (old _ _ ac da).1
    cases hs : d.source.side <;> simpa [raw,view,site,hs,lane,BStarTrace.lane] using emp

theorem drained_word {base x : X} (w : List (Fin n)) (o : Int)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (old : DrainedOwner hp base x o)
    (layout : ∀ a b,w=a++b → ∀ i, Layout B base i=Layout B (play x a) i)
    (safe : ∀ a e b,w=a++e::b → NoOwnerInject hp base (play x a) e o) :
    DrainedOwner hp base (play x w) o := by
  induction w generalizing x with
  | nil => exact old
  | cons e w ih =>
    refine ih (x:=step x e) (drained_step hp e (sep e) o
      (layout [] (e::w) rfl) (layout [e] w rfl) old (safe [] e w rfl)) ?_ ?_
    · intro a b E
      exact layout (e::a) b (congrArg (List.cons e) E)
    · intro a f b E
      exact safe (e::a) f b (congrArg (List.cons e) E)

open BStarCopyPreIssueEmpty

theorem no_enable_before_9 {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i, Layout B base i=Layout B (play x w) i)
    (small : pc (play x w) (S.getD 0 fall).1<9) (e : Fin n)
    (q : BStarLongPrep.Offer) (win : q∈
      (arbitration (round (oldPair B (play x w) e)
        (((play x w) e).long,((play x w) (rightNeighbor e)).long)).prep).1)
    (own : dataOwner (oldH6 B base) (site e q.claim.lane.side) q.claim.lane.occurrence=o.val) :
    q.claim.op≠.enable := by
  intro E
  have H := winning_prep_pc hp chart sep hist now layout e q own win
  rw [E] at H
  unfold prepOf at H
  split at H <;> simp_all

theorem keep_closed {base x : X} (e : Fin n) (sep : e≠rightNeighbor e) (o : Int)
    (layout : ∀ i,Layout B base i=Layout B x i)
    (nextLayout : ∀ i,Layout B base i=Layout B (step x e) i)
    (old : ClosedOwner hp base x o)
    (no : ∀ q∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1,
      dataOwner (oldH6 B base) (site e q.claim.lane.side) q.claim.lane.occurrence=o → q.claim.op≠.enable) :
    ClosedOwner hp base (step x e) o := by
  intro i sh act own
  have E := congrArg (fun t : Bool×Bool×Bool => t.2.1) ((layout i).symm.trans (nextLayout i))
  have oldAct : activeSheet (longGeometry B (x i)) sh=true := by
    cases sh <;> first | rfl | exact E.trans act
  exact ring_closed hp x e i sh sep (old i sh oldAct own) (fun q Q U V => no q Q (by rwa [U,V]))

/-- Part of the original generated attempt from a verified CLEAR cut
to the first PC10 state. Retained bytes and mobiles are both empty. -/
theorem drained_until_issue10 {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead tail : List (Fin n)) {m : Mode}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle (lead++tail) m)
    (old : DrainedOwner hp base (play x lead) o.val)
    (layout : ∀ a b, tail=a++b → ∀ i,Layout B base i=Layout B (play x (lead++a)) i)
    (pre10 : ∀ a e b,tail=a++e::b → pc (play x (lead++a)) (S.getD 0 fall).1<10) :
    DrainedOwner hp base (play x (lead++tail)) o.val := by
  rw [BStarResetSchedule.run_append]
  apply drained_word hp tail o.val sep old
  · intro a b E
    rw [←BStarResetSchedule.run_append]
    exact layout a b E
  · intro a e b E
    rw [←BStarResetSchedule.run_append]
    have W : lead++tail=(lead++a)++e::b := by rw [E,List.append_assoc]
    obtain ⟨mode,H,C⟩ := history_prefix hp (lead++a) (e::b) (W ▸ G)
    exact no_inject_before_10 hp chart sep H C (layout a (e::b) E) (pre10 a e b E) e

#print axioms drained_until_issue10
#print axioms no_enable_before_9
#print axioms drained_word
end L4.BStarCopyDrainedHistory

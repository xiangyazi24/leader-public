import Leader.L4.BStarCopyLeftOneCapture
import Leader.L4.BStarCopyRightPostload
import Leader.L4.BStarCopyRightLoadToInject
import Leader.L4.BStarCopyGateAuthority
import Leader.L4.BStarCopyLoadHistory

namespace L4.BStarCopyLeftFrozen
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarClearanceDataChart BStarAcquireVisitOrder BStarAcquireAnchors
open BStarResetChartTouch BStarAcquireLiteralChain BStarResetChartIndex
open BStarCopyOwnedFrozen BStarCopyGateAuthority
open BStarCopyOperand BStarGeneratedBandScan BStarGeneratedOwner BStarSeparatorControl BStarSeparatingRail BStarResetMarkAdapter BStarResetQuiet

private theorem prep_in_band (pc : Nat) (op : Prep) (low : 8≤pc) (hi : pc≤10)
    (H : prepOf pc=some op) : op=.load ∨ op=.enable ∨ op=.inject := by
  unfold prepOf at H
  split at H <;> first | contradiction | omega |
    exact Or.inl (Option.some.inj H).symm |
    exact Or.inr (Or.inl (Option.some.inj H).symm) |
    exact Or.inr (Or.inr (Option.some.inj H).symm)

private theorem ls_load_or_inject (g : LongGeometry) (j : Fin 11) (op : Prep)
    (P : op=.load ∨ op=.inject) (M : .ls∈prepSites g j op) :
    j=(if op=.load then 0 else 5) := by
  rcases P with rfl|rfl
  · simp only [prepSites] at M
    split at M
    · split at M
      · simp_all
      · split at M <;> simp_all
    · simp at M
  · simp only [prepSites] at M
    split at M
    · split at M
      · simp_all
      · split at M <;> simp_all
    · simp at M

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- Stop requiring arbitrary prep-frozen frame witnesses. On a real
8–10 owner history all LS writes to frozen come from that same
source's K0 LOAD or K5 INJECT. A visit to that
K2 during ENABLE is harmless, including simultaneous unrelated rows. -/
theorem ls_frozen_outward {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {op j : Nat}
    (hist : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle w (.busy op (.out j)))
    (now : Current hp base (fun k => S.getD k fall) len (play x w) (.busy op (.out j)))
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (e i : Fin n) (own : dataOwner (oldH6 B base) i .ls=o.val)
    (low : 8≤op) (hi : op≤10)
    (skipLoad : op=8 → S.getD j fall≠(i,0))
    (skipInject : op=10 → S.getD j fall≠(i,5)) :
    FrozenSafe hp (play x w) e i .ls := by
  apply safe_outward hp chart layout e i .ls j own now.2.1 now.2.2
  intro side siteEq offer win lane cursorAt
  have O : dataOwner (oldH6 B base) (site e offer.claim.lane.side) offer.claim.lane.occurrence=o.val := by
    rw [lane]
    exact siteEq.symm ▸ own
  have P := winning_prep_pc hp chart sep hist now layout e offer O win
  have PC : pc (play x w) (S.getD 0 fall).1=op := now.1.2.2.2
  rw [PC] at P
  have Sides : offer.claim.origin.side=side := by
    obtain ⟨C,_,_,_,_,_,_,orig,sh,_⟩ := winner_origin (oldPair B (play x w) e)
      (((play x w) e).long,((play x w) (rightNeighbor e)).long) offer win
    have h := congrArg At.side lane
    exact (congrArg At.side orig).trans (sh.symm.trans h)
  rcases prep_in_band op offer.claim.op low hi P with L|H
  · exfalso
    have opNot : op≠9 := by
      intro E
      simp [E,L,prepOf] at P
    obtain ⟨C,_,_,_,_,_,_,orig,_,M⟩ := winner_origin (oldPair B (play x w) e)
      (((play x w) e).long,((play x w) (rightNeighbor e)).long) offer win
    rw [lane,L] at M
    have K : offer.claim.origin.occurrence=0 := (congrArg At.occurrence orig).trans (ls_load_or_inject _ _ .load (.inl rfl) M)
    have E : address e offer.claim.origin=(i,0) := by
      change (site e offer.claim.origin.side,offer.claim.origin.occurrence)=(i,0)
      rw [Sides,siteEq,K]
    exact skipLoad (by unfold prepOf at P; split at P <;> simp_all) (cursorAt.symm.trans E)
  · rcases H with H|H
    · exact .inr (.inr H)
    · exfalso
      have opNot : op≠9 := by
        intro E
        simp [E,H,prepOf] at P
      obtain ⟨C,_,_,_,_,_,_,orig,_,M⟩ := winner_origin (oldPair B (play x w) e)
        (((play x w) e).long,((play x w) (rightNeighbor e)).long) offer win
      rw [lane,H] at M
      have K : offer.claim.origin.occurrence=5 := (congrArg At.occurrence orig).trans (ls_load_or_inject _ _ .inject (.inr rfl) M)
      have E : address e offer.claim.origin=(i,5) := by
        change (site e offer.claim.origin.side,offer.claim.origin.occurrence)=(i,5)
        rw [Sides,siteEq,K]
      exact skipInject (by unfold prepOf at P; split at P <;> simp_all) (cursorAt.symm.trans E)

/-- Lift exact freeze preservation to an original whole continuation.
The exclusions are same-site K0 at PC8 and K5 at PC10;
PC9 ENABLE needs no exclusion and arbitrary exterior rows are retained. -/
theorem ls_frozen_between {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (pre rest : List (Fin n)) (fin : Mode)
    (hist : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle (pre++rest) fin)
    (i : Fin n) (own : dataOwner (oldH6 B base) i .ls=o.val)
    (layout : ∀ a e b, rest=a++e::b →
      ∀ v,BStarLongFixedRouting.Layout B base v=BStarLongFixedRouting.Layout B (play x (pre++a)) v)
    (band : ∀ a e b, rest=a++e::b →
      ∀ op j, Current hp base (fun k => S.getD k fall) len (play x (pre++a)) (.busy op (.out j)) →
      8≤op ∧ op≤10 ∧ (op=8 → S.getD j fall≠(i,0)) ∧ (op=10 → S.getD j fall≠(i,5))) :
    (readLane (Sheet.index .ls) (play x (pre++rest) i).long).frozen=
      (readLane (Sheet.index .ls) (play x pre i).long).frozen := by
  induction rest generalizing pre with
  | nil => rw [List.append_nil]
  | cons e rest ih =>
    obtain ⟨now,H,I⟩ := history_prefix hp pre (e::rest) hist
    have A := layout [] e rest rfl
    simp only [List.append_nil] at A
    have F : FrozenSafe hp (play x pre) e i .ls := by
      cases now with
      | idle =>
        exact safe_idle hp chart A e i .ls own I.2
      | busy op cur =>
        cases cur with
        | back j =>
          exact safe_returning hp chart A e i .ls j own I.2.1
        | out j =>
          have Hband := band [] e rest rfl op j
          simp only [List.append_nil] at Hband
          have ⟨low,hi,noL,noI⟩ := Hband I
          exact ls_frozen_outward hp chart sep H I A e i own low hi noL noI
    have fr := ring_frozen_frame hp (play x pre) e i .ls (sep e) F
    have assoc : pre++e::rest=(pre++[e])++rest := by simp [List.append_assoc]
    have K := ih (pre++[e]) (assoc ▸ hist)
      (fun a f b P => by
        have V := layout (e::a) f b (congrArg (List.cons e) P)
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using V)
      (fun a f b P => by
        have V := band (e::a) f b (congrArg (List.cons e) P)
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using V)
    rw [assoc,K]
    rw [BStarResetSchedule.run_append]
    exact fr

end L4.BStarCopyLeftFrozen

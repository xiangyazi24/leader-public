import Leader.L4.BStarCopyRightAuthority
import Leader.L4.BStarCopyGateAuthority
import Leader.L4.BStarCopyLoadHistory

namespace L4.BStarCopyRightCapture
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

private theorem rs_load_or_inject (g : LongGeometry) (j : Fin 11) (op : Prep)
    (P : op=.load ∨ op=.inject) (M : .rs∈prepSites g j op) : j=2 := by
  rcases P with rfl|rfl
  · simp only [prepSites] at M
    split at M
    · split at M
      · simp at M
      · split at M <;> simp_all
    · simp at M
  · simp only [prepSites] at M
    split at M
    · split at M
      · simp at M
      · split at M <;> simp_all
    · simp at M

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- Stop requiring arbitrary prep-frozen frame witnesses. On a real
8–10 owner history all RS writes to frozen come from that same
source's K2 while executing its own LOAD or INJECT. A visit to that
K2 during ENABLE is harmless, including simultaneous unrelated rows. -/
theorem rs_frozen_outward {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {op j : Nat}
    (hist : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle w (.busy op (.out j)))
    (now : Current hp base (fun k => S.getD k fall) len (play x w) (.busy op (.out j)))
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (e i : Fin n) (own : dataOwner (oldH6 B base) i .rs=o.val)
    (low : 8≤op) (hi : op≤10)
    (skip : op≠9 → S.getD j fall≠(i,2)) :
    FrozenSafe hp (play x w) e i .rs := by
  apply safe_outward hp chart layout e i .rs j own now.2.1 now.2.2
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
    have K := (congrArg At.occurrence orig).trans (rs_load_or_inject _ _ .load (.inl rfl) M)
    have E : address e offer.claim.origin=(i,2) := by
      change (site e offer.claim.origin.side,offer.claim.origin.occurrence)=(i,2)
      rw [Sides,siteEq,K]
    exact skip opNot (cursorAt.symm.trans E)
  · rcases H with H|H
    · exact .inr (.inr H)
    · exfalso
      have opNot : op≠9 := by
        intro E
        simp [E,H,prepOf] at P
      obtain ⟨C,_,_,_,_,_,_,orig,_,M⟩ := winner_origin (oldPair B (play x w) e)
        (((play x w) e).long,((play x w) (rightNeighbor e)).long) offer win
      rw [lane,H] at M
      have K := (congrArg At.occurrence orig).trans (rs_load_or_inject _ _ .inject (.inr rfl) M)
      have E : address e offer.claim.origin=(i,2) := by
        change (site e offer.claim.origin.side,offer.claim.origin.occurrence)=(i,2)
        rw [Sides,siteEq,K]
      exact skip opNot (cursorAt.symm.trans E)

/-- Lift exact freeze preservation to an original whole continuation.
The only exclusion at PC8/10 is the actual same-site K2 cursor;
PC9 ENABLE needs no exclusion and arbitrary exterior rows are retained. -/
theorem rs_frozen_between {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (pre rest : List (Fin n)) (fin : Mode)
    (hist : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle (pre++rest) fin)
    (i : Fin n) (own : dataOwner (oldH6 B base) i .rs=o.val)
    (layout : ∀ a e b, rest=a++e::b →
      ∀ v,BStarLongFixedRouting.Layout B base v=BStarLongFixedRouting.Layout B (play x (pre++a)) v)
    (band : ∀ a e b, rest=a++e::b →
      ∀ op j, Current hp base (fun k => S.getD k fall) len (play x (pre++a)) (.busy op (.out j)) →
      8≤op ∧ op≤10 ∧ (op≠9 → S.getD j fall≠(i,2))) :
    (readLane (Sheet.index .rs) (play x (pre++rest) i).long).frozen=
      (readLane (Sheet.index .rs) (play x pre i).long).frozen := by
  induction rest generalizing pre with
  | nil => rw [List.append_nil]
  | cons e rest ih =>
    obtain ⟨now,H,I⟩ := history_prefix hp pre (e::rest) hist
    have A := layout [] e rest rfl
    simp only [List.append_nil] at A
    have F : FrozenSafe hp (play x pre) e i .rs := by
      cases now with
      | idle =>
        exact safe_idle hp chart A e i .rs own I.2
      | busy op cur =>
        cases cur with
        | back j =>
          exact safe_returning hp chart A e i .rs j own I.2.1
        | out j =>
          have Hband := band [] e rest rfl op j
          simp only [List.append_nil] at Hband
          have ⟨low,hi,no⟩ := Hband I
          exact rs_frozen_outward hp chart sep H I A e i own low hi no
    have fr := ring_frozen_frame hp (play x pre) e i .rs (sep e) F
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

open BStarCopyLoadHistory BStarLongDoor BStarLongCommand

/-- Authenticate the frozen source at any later pre-INJECT cut from
the actual historical LOAD launch and LOAD visit on the same word.
The old source table cell is named by a bank selected by the launch
capture, not supplied as a matching frozen-byte premise. -/
theorem original_load_to_cut {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead rest : List (Fin n)) (e : Fin n) (side : Side) (cl : CommandClaim) (cursor : Nat)
    (fin : Mode)
    (before : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle lead (.busy 8 (.out cursor)))
    (hist : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle ((lead++[e])++rest) fin)
    (loc : address e cl.source=S.getD cursor fall)
    (origin : cl.source=⟨side,2⟩)
    (selected : cl∈orderedCommands (oldPair B (play x lead) e))
    (noDoor : cl.kind≠.door)
    (inside : (geometry (oldPair B (play x lead) e) side).inside=true)
    (own : dataOwner (oldH6 B base) (site e side) .rs=o.val)
    (layout : ∀ a f b, rest=a++f::b →
      ∀ v,BStarLongFixedRouting.Layout B base v=BStarLongFixedRouting.Layout B (play x ((lead++[e])++a)) v)
    (band : ∀ a f b, rest=a++f::b →
      ∀ op j, Current hp base (fun k => S.getD k fall) len (play x ((lead++[e])++a)) (.busy op (.out j)) →
      8≤op ∧ op≤10 ∧ (op≠9 → S.getD j fall≠(site e side,2))) :
    ∃ (pre post : List (Fin n)) (launch : Fin n) (bank : Fin 3),
      lead=pre++launch::post ∧ launch=RearTrace.predecessor (S.getD 0 fall).1 ∧
      bank.val=(captures.read ((play x pre) (S.getD 0 fall).1).long).toNat % 4 ∧
      (readLane (Sheet.index .rs) (play x ((lead++[e])++rest) (site e side)).long).frozen=
        oldBankPacket ((play x lead) (site e side)).long bank := by
  obtain ⟨pre,post,launch,bank,decomp,door,index,freeze⟩ :=
    generated_freezes_bank hp chart sep before e side true cl loc own selected noDoor origin inside
  have retained := rs_frozen_between hp chart sep (lead++[e]) rest fin hist (site e side) own layout band
  have rerun : play x (lead++[e])=ring (play x lead) e := by
    rw [BStarResetSchedule.run_append]; rfl
  rw [rerun] at retained
  change (readLane (Sheet.index .rs) (play x ((lead++[e])++rest) (site e side)).long).frozen=
    (readLane (Sheet.index .rs) (ring (play x lead) e (site e side)).long).frozen at retained
  exact ⟨pre,post,launch,bank,decomp,door,index,retained.trans freeze⟩

end L4.BStarCopyRightCapture

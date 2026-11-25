import Leader.L4.BStarCopyRightMixed
import Leader.L4.BStarCopyAttemptBand

namespace L4.BStarCopyRightReady
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarCopyRightStrip BStarCopyRightRetained BStarCopyRightRetainedClassify BStarCopyRightDataSweep
open BStarCopyRightAuthority BStarCopyFenceSaturation
open BStarClearanceDataChart BStarCopyGateAuthority BStarCopyAttemptBand BStarGeneratedBandScan
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarAcquireAnchors
open BStarGeneratedOwner BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- All destination RD slots have the same actual owner as the right
strip's ingress. Also valid in the one-word aliased case. -/
theorem dest_owner {x : X} (root : Fin n) (width : Nat) (C : Dest B x root width) :
    ∀ j<width, dataOwner (oldH6 B x) (addr root j) .rd =
      dataOwner (oldH6 B x) (addr root (width-1)) .rd := by
  have adj (j : Nat) (J : j+1<width) :
      dataOwner (oldH6 B x) (addr root (j+1)) .rd =
        dataOwner (oldH6 B x) (addr root j) .rd := by
    let e := addr root j
    let g := oldPair B x e
    let d := hop (R .rd) (L .rd)
    have head : g.2.axes.h6=false := by
      change oldH6 B x (rightNeighbor e)=false
      rw [←addr_next root j]
      exact C.body _ (by omega) J
    have F : d∈dataClaims g := (raw_rd_receive g d rfl).mpr (.inl ⟨head,rfl⟩)
    have D := reserved_hop_owner B x e [] d (L .rd) (raw_is_selected_empty _ _ F) rfl
    change dataOwner (oldH6 B x) (rightNeighbor e) .rd=dataOwner (oldH6 B x) e .rd at D
    rw [←addr_next root j] at D
    exact D
  have H : ∀ d j, j+d<width → dataOwner (oldH6 B x) (addr root j) .rd =
      dataOwner (oldH6 B x) (addr root (j+d)) .rd := by
    intro d
    induction d with
    | zero => intro; simp
    | succ d ih =>
      intro j hj
      rw [Nat.add_succ]
      exact (ih j (by omega)).trans (adj (j+d) (by omega)).symm
  intro j hj
  have atEnd : j+(width-1-j)=width-1 := by omega
  simpa only [atEnd] using H (width-1-j) j (by omega)

def EnabledOn (origin : X) (w : List (Fin n)) (i : Fin n) (sh : Sheet) : Prop :=
  ∃ (lead : List (Fin n)) (e : Fin n) (rest : List (Fin n)) (offer : BStarLongPrep.Offer),
    w=lead++e::rest ∧ offer.claim.op=.enable ∧
    site e offer.claim.lane.side=i ∧ offer.claim.lane.occurrence=sh ∧
    offer∈(arbitration (round (oldPair B (play origin lead) e)
      (((play origin lead) e).long,((play origin lead) (rightNeighbor e)).long)).prep).1

open BStarLongDoor

theorem gate_from_enabled {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (m : Mode)
    (G : GeneratedOwner hp base (fun t => S.getD t fall) len x .idle w m)
    (valid : ∀ u v, w=u++v → (∀ j, Layout B base j=Layout B (play x u) j) ∧
      Band (play x u) (S.getD 0 fall).1)
    (i : Fin n) (sh : Sheet) (own : dataOwner (oldH6 B base) i sh=o.val)
    (ena : EnabledOn hp x w i sh) :
    (readLane (Sheet.index sh) (play x w i).long).gate=true := by
  obtain ⟨pre,e,post,a,E,op,iEq,shEq,win⟩ := ena
  have scope : ∀ u v,e::post=u++v →
      (∀ j, Layout B base j=Layout B (play (play x pre) u) j) ∧
      Band (play (play x pre) u) (S.getD 0 fall).1 := by
    intro u v H
    have F := valid (pre++u) v (by rw [E,H,List.append_assoc])
    rw [BStarResetSchedule.run_append] at F
    exact F
  have A := enable_through_same_attempt hp chart sep pre post e a m (E ▸ G) op win
    (by rwa [iEq,shEq]) scope
  change (readLane (Sheet.index a.claim.lane.occurrence)
    (play x (pre++e::post) (site e a.claim.lane.side)).long).gate=true at A
  rw [iEq,shEq,←E] at A
  exact A

/-- Given coverage of actual ENABLE winners, all the remaining
physical DataReady conditions follow on late PC11 marks of the same
generated attempt. No per-mark gate or no-reservation oracle. -/
theorem data_ready_late {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (m : Mode)
    (G : GeneratedOwner hp base (fun t => S.getD t fall) len x .idle w m)
    (valid : ∀ u v, w=u++v → (∀ j, Layout B base j=Layout B (play x u) j) ∧
      Band (play x u) (S.getD 0 fall).1)
    (late : 11≤pc (play x w) (S.getD 0 fall).1)
    (e root baseAddr : Fin n) (width seam tail : Nat)
    (baseDest : Dest B base root width) (baseStrip : Strip B base baseAddr seam tail)
    (dest : Dest B (play x w) root width) (strip : Strip B (play x w) baseAddr seam tail)
    (join : addr baseAddr 0=addr root (width-1))
    (ownHead : dataOwner (oldH6 B base) (addr baseAddr 0) (rail seam 0)=o.val)
    (rdCoverage : ∀ j<width, EnabledOn hp x w (addr root j) .rd)
    (upCoverage : ∀ j, 0<j → j≤tail → EnabledOn hp x w (addr baseAddr j) (rail seam j)) :
    DataReady hp (play x w) root baseAddr e width seam tail := by
  let y := play x w
  have f := valid w [] (by simp)
  have same := f.1
  have now := BStarGeneratedTapeCuts.at_end hp G
  have rsh : rail seam 0=.rd := if_pos baseStrip.seam_pos
  have headOwn : dataOwner (oldH6 B base) (addr root (width-1)) .rd=o.val := by
    rwa [rsh,join] at ownHead
  have rd (j : Nat) (J : j<width) :
      dataOwner (oldH6 B base) (addr root j) .rd=o.val :=
    (dest_owner hp root width baseDest j J).trans headOwn
  have up (j : Nat) (J : j≤tail) :
      dataOwner (oldH6 B base) (addr baseAddr j) (rail seam j)=o.val :=
    (strip_same_owner baseStrip j J).trans ownHead
  have noPrep (a : At Sheet)
      (own : dataOwner (oldH6 B base) (site e a.side) a.occurrence=o.val) :
      a∉reserved (round (oldPair B y e) ((y e).long,(y (rightNeighbor e)).long)).prep := by
    apply no_prep_late _ _ _ _ late
    intro offer win eq
    exact winning_prep_pc hp chart sep G now same e offer (by rwa [eq]) win
  exact ⟨dest,strip,
    fun j J => gate_from_enabled hp chart sep w m G valid _ _ (rd j J) (rdCoverage j J),
    fun j U J => gate_from_enabled hp chart sep w m G valid _ _ (up j J) (upCoverage j U J),
    fun j J s loc => noPrep ⟨s,.rd⟩ (by change dataOwner _ (site e s) .rd=o.val; rw [loc]; exact rd j J),
    fun j _ J s loc => noPrep ⟨s,rail seam j⟩ (by change dataOwner _ (site e s) (rail seam j)=o.val; rw [loc]; exact up j J)⟩

#print axioms gate_from_enabled
#print axioms data_ready_late

/-- ENABLE's literal right prep positions. RD uses K1 even on OUT
padding; RS uses K2 and needs INSIDE. Every such addressed K1/K2 is
a strict preterminal member of the chosen chart. -/
theorem chart_enable_position {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (i : Fin n) (sh : Sheet) (own : dataOwner (oldH6 B base) i sh=o.val)
    (kind : sh=.rd ∨ sh=.rs)
    (activeRS : sh=.rs → (longGeometry B (base i)).inside=true) :
    let field : Fin 11 := if sh=.rd then 1 else 2
    sh∈prepSites (longGeometry B (base i)) field .enable ∧
    ∃ k<len, S.getD k fall=(i,field) := by
  dsimp only
  let field : Fin 11 := if sh=.rd then 1 else 2
  have fieldOwner : commandOwner (oldH6 B base) i field=o.val := by
    rcases kind with rfl|rfl <;> exact own
  have fieldAct : BStarAcquireRailCoverage.active (longGeometry B (base i)) field=true := by
    rcases kind with rfl|rfl <;> simp [field,BStarAcquireRailCoverage.active]
  have fieldPrep : sh∈prepSites (longGeometry B (base i)) field .enable := by
    rcases kind with K|K
    · subst sh
      cases H : (longGeometry B (base i)).inside <;> simp [field,prepSites,H]
    · subst sh
      simp [field,prepSites,activeRS rfl]
  obtain ⟨k,kl,K⟩ := List.getElem_of_mem (chart.cover (i,field) fieldAct fieldOwner)
  have M : S.getD k fall=(i,field) := (List.getElem_eq_getD (h:=kl) fall).symm.trans K
  have Le : k≤len := by have := chart.length; omega
  have nEnd : k≠len := by
    intro E
    subst k
    have V := congrArg Prod.snd (chart.terminal.symm.trans M)
    change (10 : Fin 11)=field at V
    rcases kind with rfl|rfl <;> simp [field] at V <;> contradiction
  exact ⟨fieldPrep,k,by omega,M⟩

#print axioms chart_enable_position
end L4.BStarCopyRightReady

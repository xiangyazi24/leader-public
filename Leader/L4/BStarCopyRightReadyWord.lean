import Leader.L4.BStarCopyRightReady
import Leader.L4.BStarCopyEnableTerminal
import Leader.L4.BStarCopyEnableCoverage

namespace L4.BStarCopyRightReadyWord
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep BStarLongDoor
open BStarCopyRightStrip BStarCopyRightRetained BStarCopyRightDataSweep BStarCopyRightReady
open BStarCopyRightAuthority BStarClearanceDataChart BStarCopyEnableCoverage BStarCopyEnableTerminal
open BStarCopyGateAuthority BStarCopyAttemptBand BStarGeneratedBandScan
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarLongFixedRouting BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarSeparatingRail BStarResetMarkAdapter

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem dest_layout {x y : X} (root : Fin n) (width : Nat)
    (C : Dest B x root width) (H : ∀ i, Layout B x i=Layout B y i) :
    Dest B y root width := by
  have hh := fun i => congrArg Prod.fst (H i)
  have hi := fun i => congrArg (fun z : Bool × Bool × Bool => z.2.1) (H i)
  exact ⟨C.fit,C.pos,(hh _).symm.trans C.header,
    fun j p l => (hh _).symm.trans (C.body _ p l),
    fun j l => (hi _).symm.trans (C.inside _ l)⟩

private theorem strip_layout {x y : X} (base : Fin n) (seam tail : Nat)
    (C : Strip B x base seam tail) (H : ∀ i, Layout B x i=Layout B y i) :
    Strip B y base seam tail := by
  have hh := fun i => congrArg Prod.fst (H i)
  have hi := fun i => congrArg (fun z : Bool × Bool × Bool => z.2.1) (H i)
  have he (i : Fin n) : ends (longGeometry B (x i))=ends (longGeometry B (y i)) :=
    congrArg (fun z : Bool × Bool × Bool => z.2.1 && z.2.2) (H i)
  exact ⟨C.seam_pos,C.seam_le_tail,C.tail_lt,(hi _).symm.trans C.head_in,
    fun j l => (hh _).symm.trans (C.rd_noheader _ l),
    fun j p l => (hi _).symm.trans (C.pads_out _ p l),
    (hh _).symm.trans C.rs_header,
    fun j p l => (hh _).symm.trans (C.rs_nonheader _ p l),
    fun j p l => (hi _).symm.trans (C.rs_in _ p l),
    fun j p l => (he _).symm.trans (C.rs_nonlast _ p l),
    (he _).symm.trans C.tail_last⟩

private theorem extends_enabled (x : X) (w ext : List (Fin n)) (i : Fin n) (sh : Sheet)
    (E : EnabledOn hp x w i sh) : EnabledOn hp x (w++ext) i sh := by
  obtain ⟨pre,e,post,a,W,A,I,S,M⟩ := E
  exact ⟨pre,e,post++ext,a,by rw [W,List.append_assoc,List.cons_append],A,I,S,M⟩

/-- Obtain the original selected ENABLE witness at any physical owned
active lane directly from the completed successful PC9 raw tape. -/
theorem enabled_after_accept9 {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {ack : Fin n}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w (.busy 9 (.back 0)))
    (event : Event hp (fun j => S.getD j fall) len (play x w) ack (.busy 9 (.back 0)) .idle)
    (accepted : (ctrlOp.read (ring (play x w) ack (S.getD 0 fall).1).long).toNat=10) :
    ∀ i sh, activeSheet (longGeometry B (base i)) sh=true →
      dataOwner (oldH6 B base) i sh=o.val → EnabledOn hp x w i sh := by
  obtain ⟨pre,back,turn,f,W,found,oldF,good,op9⟩ := accepted9_terminal hp chart sep G event accepted
  obtain ⟨lead,tour,launch,preEq,_,_,_,flight⟩ := found
  let l := lead++[launch]
  have replay : play x l=ring (play x lead) launch := by rw [BStarResetSchedule.run_append]; rfl
  have W' : pre=l++tour := by rw [preEq]; simp [l,List.append_assoc]
  have F : project (fun j => S.getD j fall) (play (play x l) tour) len=.forward f := by
    rw [←BStarResetSchedule.run_append,←W']
    exact oldF
  intro i sh active own
  obtain ⟨a,e,b,offer,Q,R,K,M,A⟩ :=
    outward_enable hp chart sep (replay.symm ▸ flight) f F good op9 i sh active own
  have win : offer∈(arbitration (round (oldPair B (play x (l++a)) e)
    (((play x (l++a)) e).long,((play x (l++a)) (rightNeighbor e)).long)).prep).1 := by
    rw [BStarResetSchedule.run_append]
    exact A
  have E : EnabledOn hp x pre i sh := by
    refine ⟨l++a,e,b,offer,?_,R,K,M,win⟩
    -- prefix equation is wholly literal
    exact W'.trans ((congrArg (l++·) Q).trans (List.append_assoc l a (e::b)).symm)
  exact W.symm ▸ extends_enabled hp x pre (turn::back) i sh E

/-- Whole unreduced later PC11 tape: authenticate the old data-ready
predicate at every mark from one accepted PC9 prefix and its actual
continuation. Callers provide the successful phase cuts, fixed layout,
and in-band trace, never individual wins/gates/reservation facts. -/
theorem right_ready_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w9 bridge data : List (Fin n)) (ack : Fin n) (endMode : Mode)
    (G9 : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w9 (.busy 9 (.back 0)))
    (event : Event hp (fun j => S.getD j fall) len (play x w9) ack (.busy 9 (.back 0)) .idle)
    (accepted : (ctrlOp.read (ring (play x w9) ack (S.getD 0 fall).1).long).toNat=10)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle ((w9++ack::bridge)++data) endMode)
    (valid : ∀ u v, ((w9++ack::bridge)++data)=u++v →
      (∀ j, Layout B base j=Layout B (play x u) j) ∧ Band (play x u) (S.getD 0 fall).1)
    (late : 11≤pc (play x (w9++ack::bridge)) (S.getD 0 fall).1)
    (root bAddr : Fin n) (width seam tail : Nat)
    (dest : Dest B base root width) (strip : Strip B base bAddr seam tail)
    (join : addr bAddr 0=addr root (width-1))
    (ownHead : dataOwner (oldH6 B base) (addr bAddr 0) (rail seam 0)=o.val) :
    ∀ a e b,data=a++e::b →
      DataReady hp (play (play x (w9++ack::bridge)) a) root bAddr e width seam tail := by
  let lead := w9++ack::bridge
  have all := enabled_after_accept9 hp chart sep G9 event accepted
  have headRD : dataOwner (oldH6 B base) (addr root (width-1)) .rd=o.val := by
    rwa [show rail seam 0=.rd from if_pos strip.seam_pos,join] at ownHead
  intro a e b W
  let pre := lead++a
  have whole : lead++data=pre++e::b := by
    change lead++data=(lead++a)++e::b
    exact (congrArg (lead++·) W).trans (List.append_assoc lead a (e::b)).symm
  obtain ⟨m,G,I⟩ := history_prefix hp pre (e::b) (whole ▸ hist)
  have localBand (u v : List (Fin n)) (E : pre=u++v) :
      (∀ j, Layout B base j=Layout B (play x u) j) ∧ Band (play x u) (S.getD 0 fall).1 := by
    apply valid u (v++e::b)
    rw [←List.append_assoc,←E]
    exact whole
  have same := (localBand pre [] (by simp)).1
  obtain ⟨startMode,mid⟩ := drop_history hp lead a G
  have low := band_word hp chart sep mid (fun u v E => by
    have K := localBand (lead++u) v (by
      change lead++a=(lead++u)++v
      exact (congrArg (lead++·) E).trans (List.append_assoc lead u v).symm)
    rw [BStarResetSchedule.run_append] at K
    exact K)
  have replay : play x pre=play (play x lead) a := BStarResetSchedule.run_append _ _ _ _
  have pc11 : 11≤pc (play x pre) (S.getD 0 fall).1 := by
    rw [replay]
    exact Nat.le_trans late low
  have lift (i : Fin n) (sh : Sheet) (A : activeSheet (longGeometry B (base i)) sh=true)
      (O : dataOwner (oldH6 B base) i sh=o.val) : EnabledOn hp x pre i sh := by
    have W' : pre=w9++((ack::bridge)++a) := by simp [pre,lead,List.append_assoc]
    exact W'.symm ▸ extends_enabled hp x w9 ((ack::bridge)++a) i sh (all i sh A O)
  rw [←replay]
  refine data_ready_late hp chart sep pre m G localBand pc11 e root bAddr width seam tail
    dest strip (dest_layout hp root width dest same) (strip_layout hp bAddr seam tail strip same) join ownHead
    (fun j J => lift _ _ rfl ((dest_owner hp root width dest j J).trans headRD)) ?_
  intro j pos J
  apply lift
  · by_cases inside : j<seam
    · simp [rail,inside,activeSheet]
    · simp [rail,inside,activeSheet,strip.rs_in j (by omega) J]
  · exact (strip_same_owner strip j J).trans ownHead

#print axioms enabled_after_accept9
#print axioms right_ready_word
end L4.BStarCopyRightReadyWord

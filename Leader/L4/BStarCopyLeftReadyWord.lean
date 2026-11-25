import Leader.L4.BStarCopyRightReadyWord
import Leader.L4.BStarCopyLeftDataSweep

namespace L4.BStarCopyLeftReadyWord
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep BStarLongDoor
open BStarCopyRightStrip (addr addr_next)
open BStarCopyLeftStrip BStarCopyLeftMark BStarCopyLeftDataSweep
open BStarCopyRightReady (EnabledOn gate_from_enabled)
open BStarCopyRightReadyWord (enabled_after_accept9)
open BStarCopyRightAuthority (raw_is_selected_empty)
open BStarClearanceDataChart BStarAcquireAnchors
open BStarCopyGateAuthority BStarCopyAttemptBand BStarGeneratedBandScan
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarLongFixedRouting BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarSeparatingRail BStarResetMarkAdapter

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem strip_layout {x y : X} (base : Fin n) (seam width : Nat)
    (C : Strip B x base seam width) (H : ∀ i, Layout B x i=Layout B y i) :
    Strip B y base seam width := by
  have hh := fun i => congrArg Prod.fst (H i)
  have hi := fun i => congrArg (fun z : Bool × Bool × Bool => z.2.1) (H i)
  have he (i : Fin n) : ends (longGeometry B (x i))=ends (longGeometry B (y i)) :=
    congrArg (fun z : Bool × Bool × Bool => z.2.1 && z.2.2) (H i)
  exact ⟨C.seam_pos,C.seam_le,C.width_pos,C.width_le,(hh _).symm.trans C.source_header,
    fun j a b => (hh _).symm.trans (C.ls_body j a b),
    (hh _).symm.trans C.dest_header,
    fun j a b => (hh _).symm.trans (C.ld_body j a b),
    fun j a b => (hi _).symm.trans (C.ld_in j a b),
    fun j a b => (he _).symm.trans (C.ld_before_last j a b),
    (he _).symm.trans C.last⟩

theorem all_owner {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (a : Fin n) (seam width : Nat)
    (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1) :
    ∀ j<seam+width, dataOwner (oldH6 B base) (addr a j) (rail seam j)=o.val := by
  intro j
  induction j with
  | zero =>
    intro _
    have H := (endpoint_spec (oldH6 B base) hh o 0).2.1
    rw [←chart.root,←root] at H
    have A : addr a 0=a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
    rw [A,rail,if_pos strip.seam_pos]
    exact H
  | succ j ih =>
    intro J
    let e := addr a j
    let g := oldPair B base e
    let d := hop (L (rail seam j)) (R (rail seam (j+1)))
    have D := (raw_hop strip j J d rfl).mpr rfl
    have F := reserved_hop_owner B base e [] d (R (rail seam (j+1))) (raw_is_selected_empty _ _ D) rfl
    change dataOwner (oldH6 B base) (addr a j) (rail seam j)=
      dataOwner (oldH6 B base) (rightNeighbor (addr a j)) (rail seam (j+1)) at F
    rw [←addr_next] at F
    exact F.symm.trans (ih (by omega))

private theorem address_add (a : Fin n) (seam j : Nat) :
    addr (addr a seam) j=addr a (seam+j) := by
  have E : addr (addr a seam) 0=addr a seam := Fin.ext (Nat.mod_eq_of_lt (addr a seam).isLt)
  have A : addr (addr a seam) j=BStarFenceReceiverChart.digitFrom (addr a seam) j := by
    simpa only [Nat.zero_add,E] using (addr_from (addr a seam) 0 j)
  exact A.trans
    (addr_from a seam j).symm

private theorem extends_enabled (x : X) (w ext : List (Fin n)) (i : Fin n) (sh : Sheet)
    (E : EnabledOn hp x w i sh) : EnabledOn hp x (w++ext) i sh := by
  obtain ⟨pre,e,post,a,W,A,I,S,M⟩ := E
  exact ⟨pre,e,post++ext,a,by rw [W,List.append_assoc,List.cons_append],A,I,S,M⟩

/-- Whole unreduced later PC11 tape: authenticate the old data-ready
predicate at every mark from one accepted PC9 prefix and its actual
continuation. Callers provide the successful phase cuts, fixed layout,
and in-band trace, never individual wins/gates/reservation facts. -/
theorem left_ready_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
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
    (bAddr : Fin n) (seam width : Nat) (strip : Strip B base bAddr seam width)
    (root : bAddr=(S.getD 0 fall).1) :
    ∀ a e b,data=a++e::b →
      DataReady hp (play (play x (w9++ack::bridge)) a) bAddr e seam width := by
  let lead := w9++ack::bridge
  have all := enabled_after_accept9 hp chart sep G9 event accepted
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
  have sw := strip_layout hp bAddr seam width strip same
  have ow := all_owner hp chart bAddr seam width strip root
  have ld (j : Nat) (J : j<width) :
      dataOwner (oldH6 B base) (addr (addr bAddr seam) j) .ld=o.val := by
    rw [address_add]
    have F := ow (seam+j) (by omega)
    rwa [rail,if_neg (by omega : ¬seam+j<seam)] at F
  have ls (j : Nat) (J : j<seam) :
      dataOwner (oldH6 B base) (addr bAddr j) .ls=o.val := by
    have F := ow j (by omega)
    rwa [rail,if_pos J] at F
  have noPrep (slot : At Sheet)
      (own : dataOwner (oldH6 B base) (site e slot.side) slot.occurrence=o.val) :
      slot∉reserved (round (oldPair B (play x pre) e)
        (((play x pre) e).long,((play x pre) (rightNeighbor e)).long)).prep := by
    apply BStarCopyFenceSaturation.no_prep_late _ _ _ _ pc11
    intro offer win eq
    exact winning_prep_pc hp chart sep G I same e offer (by rwa [eq]) win
  refine ⟨sw,?_,?_,?_,?_⟩
  · intro j J
    have active : activeSheet (longGeometry B (base (addr (addr bAddr seam) j))) .ld=true := by
      change (longGeometry B (base (addr (addr bAddr seam) j))).inside=true
      rw [address_add]
      exact strip.ld_in _ (by omega) (by omega)
    exact gate_from_enabled hp chart sep pre m G localBand _ _ (ld j J) (lift _ _ active (ld j J))
  · intro j J
    unfold sample
    rw [rail,if_pos J]
    exact gate_from_enabled hp chart sep pre m G localBand _ _ (ls j J) (lift _ _ rfl (ls j J))
  · intro j J s loc
    apply noPrep ⟨s,.ld⟩
    change dataOwner _ (site e s) .ld=o.val
    rw [loc]; exact ld j J
  · intro j J s loc
    apply noPrep ⟨s,.ls⟩
    change dataOwner _ (site e s) .ls=o.val
    rw [loc]; exact ls j J

open BStarCopyLeftRetained BStarCopyLeftDeposit BStarCopyFenceSaturation BStarCopyMarkedLedger

/-- Apply the exact left data observer directly to the original late
PC11 word with all gates and owner-reservation exclusions discharged. -/
theorem left_data_word {Tag : Type} (digits : Tag→BitVec 36) {base x : X} {hh : ∃ i,oldH6 B base i=true}
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
    (bAddr : Fin n) (seam width : Nat) (strip : Strip B base bAddr seam width)
    (root : bAddr=(S.getD 0 fall).1)  
    (plan : List Tag) (size : plan.length=width) (s : Ledger Tag) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (headFirst seam label))
    (old : RetainedMatches digits (play x (w9++ack::bridge)) (addr bAddr seam) width s)
    (matched : UpstreamMatches digits (play x (w9++ack::bridge)) bAddr seam label) :
    ∃ t post, t.release=s.release ∧ OrderedPrefix plan t (headFirst seam post) ∧
      RetainedMatches digits (play (play x (w9++ack::bridge)) data) (addr bAddr seam) width t ∧
      UpstreamMatches digits (play (play x (w9++ack::bridge)) data) bAddr seam post := by
  exact data_word hp digits (play x (w9++ack::bridge)) data bAddr seam width sep plan size s label P old matched
    (left_ready_word hp chart sep w9 bridge data ack endMode G9 event accepted hist valid late bAddr seam width strip root)

#print axioms left_data_word
#print axioms all_owner
#print axioms left_ready_word
end L4.BStarCopyLeftReadyWord

import Leader.L4.BStarCopyLeftReturn
import Leader.L4.BStarCopyRightReadyWord
import Leader.L4.BStarCopyLeftDataSweep

namespace L4.BStarCopyLeftGeometryWord
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

open BStarCopyLeftReturn BStarCopyLeftReadyWord
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

theorem left_gates_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w9 rest : List (Fin n)) (ack : Fin n) (endMode : Mode)
    (G9 : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w9 (.busy 9 (.back 0)))
    (event : Event hp (fun j => S.getD j fall) len (play x w9) ack (.busy 9 (.back 0)) .idle)
    (accepted : (ctrlOp.read (ring (play x w9) ack (S.getD 0 fall).1).long).toNat=10)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle (w9++ack::rest) endMode)
    (valid : ∀ u v, w9++ack::rest=u++v →
      (∀ j, Layout B base j=Layout B (play x u) j) ∧ Band (play x u) (S.getD 0 fall).1)
    (bAddr : Fin n) (seam width : Nat)
    (strip : Strip B base bAddr seam width) (root : bAddr=(S.getD 0 fall).1) :
    ∀ a b, rest=a++b →
      GeometryGates hp base (play x (w9++ack::a)) bAddr seam width := by
  have all := enabled_after_accept9 hp chart sep G9 event accepted
  intro a b W
  let pre := w9++ack::a
  have whole : w9++ack::rest=pre++b := by
    calc
      _ = w9++ack::(a++b) := congrArg (fun v => w9++ack::v) W
      _ = (w9++ack::a)++b := by simp only [List.append_assoc,List.cons_append]
  obtain ⟨m,G,_⟩ := history_prefix hp pre b (whole ▸ hist)
  have localBand (u v : List (Fin n)) (E : pre=u++v) :
      (∀ j, Layout B base j=Layout B (play x u) j) ∧ Band (play x u) (S.getD 0 fall).1 := by
    apply valid u (v++b)
    rw [←List.append_assoc,←E]
    exact whole
  have same := (localBand pre [] (by simp)).1
  have gate (i : Fin n) (sh : Sheet) (A : activeSheet (longGeometry B (base i)) sh=true)
      (O : dataOwner (oldH6 B base) i sh=o.val) :
      (readLane (Sheet.index sh) (play x pre i).long).gate=true := by
    apply gate_from_enabled hp chart sep pre m G localBand i sh O
    exact extends_enabled hp x w9 (ack::a) i sh (all i sh A O)
  have O := all_owner hp chart bAddr seam width strip root
  refine ⟨same,strip_layout hp bAddr seam width strip same,?_,?_⟩
  · intro j J
    have loc := address_add bAddr seam j
    have org : dataOwner (oldH6 B base) (addr (addr bAddr seam) j) .ld=o.val := by
      rw [loc]
      simpa [rail,show ¬seam+j<seam by omega] using O (seam+j) (by omega)
    have inD : activeSheet (longGeometry B (base (addr (addr bAddr seam) j))) .ld=true := by
      change (longGeometry B (base (addr (addr bAddr seam) j))).inside=true
      rw [loc]
      exact strip.ld_in _ (by omega) (by omega)
    exact gate _ _ inD org
  · intro j J
    unfold sample
    rw [rail,if_pos J]
    exact gate _ _ rfl (by simpa [rail,J] using O j (by omega))

end L4.BStarCopyLeftGeometryWord

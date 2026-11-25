import Leader.L4.BStarCopyRightReadyWord
import Leader.L4.BStarFenceReceiverChart

namespace L4.BStarCopyRightFence
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets BStarLongWork
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarCopyRightStrip (addr addr_next)
open BStarCopyRightStrip BStarCopyRightMark BStarCopyRightRetained BStarCopyRightDataSweep
open BStarCopyRightReadyWord
open BStarCopyMarkedLedger BStarCopyFenceSaturation BStarCopyFIFO BStarSeparatingRail
open BStarFenceReceiverChart BStarClearanceDataChart BStarNativeReceiptTape

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem read_labels {Tag : Type} (digits : Tag→BitVec 36)
    (cells : Nat→Queue Tag) (lanes : Nat→Lane) (j count : Nat)
    (M : ∀ k, j≤k → k<j+count → Compatible digits (cells k) (lanes k))
    (R : ∀ k, j≤k → k<j+count → ∃ l,(cells k).retained=some l) :
    laneRead lanes j count=(heldFrom cells j count).map (Digit9.data ∘ digits) := by
  induction count generalizing j with
  | zero => rfl
  | succ count ih =>
    obtain ⟨d,D⟩ := R j (by omega) (by omega)
    have H := (M j (by omega) (by omega)).2
    rw [D] at H
    have T := ih (j+1) (fun k lo hi => M k (by omega) (by omega))
      (fun k lo hi => R k (by omega) (by omega))
    simp only [laneRead,heldFrom,D,Option.toList_some,List.singleton_append,List.map_cons,H,encode,
      Function.comp_apply,T]

def rdRead (x : X) (root : Fin n) (width j : Nat) : Lane :=
  readLane (Sheet.index .rd) (x (addr root (width-1-j))).long

/-- Old K10 tests RD at the header, i.e. the last receiver in travel
order. The ordered ledger makes that one retained datum a full drain
certificate for the tracked right strip. -/
theorem saturate_right {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root : Fin n) (width : Nat) (plan : List Tag)
    (size : plan.length=width) (hw : 0<width)
    {s : Ledger Tag} {u : List Tag}
    (P : OrderedPrefix plan s u) (M : RetainedMatches digits x root width s)
    (landed : ∃ d,(rdRead x root width (width-1)).retained=.data d) :
    (∀ j<width,(rdRead x root width j).mobile=.empty) ∧
    laneRead (rdRead x root width) 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
    u=[] ∧ s.release.pending=[] := by
  subst width
  obtain ⟨d,D⟩ := landed
  obtain ⟨pre,ord⟩ := ordered_prefix P
  have e : (s.cells (plan.length-1)).retained≠none := by
    intro E
    have R := (M 0 (by omega)).2
    change (readLane (Sheet.index .rd) (x (addr root 0)).long).retained=encode digits _ at R
    have loc : plan.length-1-(plan.length-1)=0 := by omega
    simp only [rdRead,loc] at D
    rw [Nat.sub_zero,E,D] at R
    cases R
  have sat := cell_saturation pre hw e
  have read := read_labels digits s.cells (rdRead x root plan.length) 0 plan.length
    (fun k _ K => by
      have V := M (plan.length-1-k) (by omega)
      rw [show plan.length-1-(plan.length-1-k)=k by omega] at V
      exact V)
    (fun k _ K => (sat k (by omega)).2.2.2)
  rw [retained_reverse pre hw e ord] at read
  refine ⟨?_,read,(saturated_release pre hw e ord).1,(saturated_release pre hw e ord).2.1⟩
  intro j J
  have R := (M (plan.length-1-j) (by omega)).1
  rw [show plan.length-1-(plan.length-1-j)=j by omega] at R
  rw [(sat j J).2.2.1] at R
  exact R

/-- On the original FENCE tape, read at the actual old K10 test,
not a replayed or post-ACK state. Physical padding outside the
tracked right strip does not enter this argument. -/
theorem accepted_right {Tag : Type} (digits : Tag→BitVec 36)
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (root a : Fin n) (seam tail : Nat) (rootAt : root=(S.getD len fall).1)
    (join : addr a 0=addr root (width-1))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (ack : Fin n)
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 11 (.back 0)))
    (H : Hit hp base (fun j=>S.getD j fall) len (play x w) ack 11)
    (plan : List Tag) (size : plan.length=width) (s : Ledger Tag) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (stripWord tail label))
    (old : RetainedMatches digits x root width s)
    (mobile : MobileMatches digits x a seam tail label)
    (ready : ∀ u e v,w=u++e::v → DataReady hp (play x u) root a e width seam tail) :
    ∃ (pre gap back : List (Fin n)) (mark turn : Fin n) (t : Ledger Tag) (post : Nat→Option Tag),
      w=pre++mark::(gap++turn::back) ∧
      let y := play x ((pre++[mark])++gap)
      let read := rdRead y root width
      (∀ j<width,(read j).mobile=.empty) ∧
      laneRead read 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      RetainedMatches digits y root width t ∧
      MobileMatches digits y a seam tail post ∧
      stripWord tail post=[] ∧ t.release.pending=[] := by
  obtain ⟨pre,gap,back,mark,turn,E,_,R⟩ := accepted_receivers hp chart hw inside notShort sep w ack T H
  let cut := (pre++[mark])++gap
  have W : w=cut++turn::back := E.trans (by simp [cut,List.append_assoc])
  have eval : play x cut=play (ring (play x pre) mark) gap := by
    simp only [cut,BStarResetSchedule.run_append]; rfl
  have accept : ∃ d,(rdRead (play x cut) root width (width-1)).retained=.data d := by
    have a0 : addr root 0=root := Fin.ext (Nat.mod_eq_of_lt root.isLt)
    have k : width-1-(width-1)=0 := by omega
    unfold rdRead
    rw [k,a0,rootAt,eval]
    obtain ⟨d,Hd⟩ := R.2
    exact ⟨d,Hd⟩
  have preReady (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (U : cut=u++e::v) :
      DataReady hp (play x u) root a e width seam tail := by
    apply ready u e (v++turn::back)
    simp only [W,U,List.append_assoc,List.cons_append]
  obtain ⟨t,post,_,Q,L,M⟩ := data_word hp digits x cut root a width seam tail join sep plan size
    s label P old mobile preReady
  obtain ⟨F,read,V,Z⟩ := saturate_right digits (play x cut) root width plan size hw Q L accept
  exact ⟨pre,gap,back,mark,turn,t,post,E,F,read,L,M,V,Z⟩

end L4.BStarCopyRightFence

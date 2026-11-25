import Leader.L4.BStarCopyLeftReturn
import Leader.L4.BStarCopyActiveVacancy

namespace L4.BStarCopyLeftFence

open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets BStarLongWork
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarCopyRightStrip (addr addr_next)
open BStarCopyLeftStrip BStarCopyLeftRetained BStarCopyLeftDeposit BStarCopyLeftDataSweep
open BStarCopyMarkedLedger BStarCopyFenceSaturation BStarCopyFIFO BStarSeparatingRail
open BStarFenceReceiverChart BStarClearanceDataChart BStarNativeReceiptTape

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- Every LS donor is active, even the OUT padding. The physical active
vacancy invariant supplies exactly the full old unvisited K5 vacancy. -/
theorem cutVacant_of_active (x : X) (S : List (Pos n)) (fall : Pos n) (len cut : Nat)
    (h : BStarCopyActiveVacancy.ActiveCutVacant hp x S fall len cut false) :
    BStarCopyDownstream.CutVacant x S fall len cut false :=
  fun i H => h i H rfl

theorem addr_digits {n : Nat} (a : Fin n) (j : Nat) : addr a j=digitFrom a j := by
  induction j with
  | zero => exact Fin.ext (Nat.mod_eq_of_lt a.isLt)
  | succ j ih =>
    rw [addr_next,ih]
    rfl

def ldRead (x : X) (root : Fin n) (j : Nat) : Lane :=
  readLane (Sheet.index .ld) (x (addr root j)).long

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

/-- If the old last LD endpoint physically has DATA, the exact ordered
ledger forces saturation with the original label order. -/
theorem saturate_left {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root : Fin n) (width : Nat) (plan : List Tag)
    (size : plan.length=width) (hw : 0<width)
    {s : Ledger Tag} {u : List Tag}
    (P : OrderedPrefix plan s u) (M : RetainedMatches digits x root width s)
    (landed : ∃ d,(ldRead x root (width-1)).retained=.data d) :
    (∀ j<width,(ldRead x root j).mobile=.empty) ∧
    laneRead (ldRead x root) 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
    u=[] ∧ s.release.pending=[] := by
  subst width
  obtain ⟨d,D⟩ := landed
  obtain ⟨pre,ord⟩ := ordered_prefix P
  have e : (s.cells (plan.length-1)).retained≠none := by
    intro E
    have R := (M (plan.length-1) (by omega)).2
    change (ldRead x root (plan.length-1)).retained=encode digits _ at R
    rw [E,D] at R
    cases R
  have sat := cell_saturation pre hw e
  have read := read_labels digits s.cells (ldRead x root) 0 plan.length
    (fun k _ K => M k (by omega))
    (fun k _ K => (sat k (by omega)).2.2.2)
  rw [retained_reverse pre hw e ord] at read
  refine ⟨?_,read,(saturated_release pre hw e ord).1,(saturated_release pre hw e ord).2.1⟩
  intro j J
  have R := (M j J).1
  rw [(sat j J).2.2.1] at R
  exact R

private theorem seam_unique {x : X} {a : Fin n} {seam seam' width : Nat}
    (s : Strip B x a seam width) (t : Strip B x a seam' width) : seam=seam' := by
  by_cases h : seam<seam'
  · have bad := t.ls_body seam s.seam_pos h
    rw [s.dest_header] at bad
    contradiction
  · by_cases j : seam'<seam
    · have bad := s.ls_body seam' t.seam_pos j
      rw [t.dest_header] at bad
      contradiction
    · omega

/-- The FENCE acceptance and left ledger refer to the same original
physical tape. Sweep only its prefix before the actual selected K7
test, then conclude the full LD readout there, not at an arbitrary
replayed state or a later ACK. The input ledger is the PC10 ACK
endpoint supplied by LeftReturn. -/
theorem accepted_left {Tag : Type} (digits : Tag→BitVec 36)
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    {a : Fin n} {seam : Nat} (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (ack : Fin n)
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 11 (.back 0)))
    (H : Hit hp base (fun j=>S.getD j fall) len (play x w) ack 11)
    (plan : List Tag) (size : plan.length=width) (s : Ledger Tag) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (headFirst seam label))
    (old : RetainedMatches digits x (addr a seam) width s)
    (mobile : BStarCopyLeftMark.UpstreamMatches digits x a seam label)
    (ready : ∀ u e v,w=u++e::v → DataReady hp (play x u) a e seam width) :
    ∃ (pre gap back : List (Fin n)) (mark turn : Fin n) (t : Ledger Tag) (post : Nat→Option Tag),
      w=pre++mark::(gap++turn::back) ∧
      let y := play x pre
      let read := ldRead y (addr a seam)
      (∀ j<width,(read j).mobile=.empty) ∧
      laneRead read 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      RetainedMatches digits y (addr a seam) width t ∧
      BStarCopyLeftMark.UpstreamMatches digits y a seam post ∧
      headFirst seam post=[] ∧ t.release.pending=[] := by
  rcases of_chart hp chart hw flags notShort with ⟨sc,C,center,_,_⟩
  have equal : seam=sc := seam_unique hp strip (root.symm ▸ C)
  have loc : addr a seam=(S.getD len fall).1 := by rw [equal,root]; exact center
  obtain ⟨pre,gap,back,mark,turn,E,L,_⟩ := accepted_receivers hp chart hw
    (fun i => (flags i).1) notShort sep w ack T H
  have accept : ∃ d,(ldRead (play x pre) (addr a seam) (width-1)).retained=.data d := by
    simpa only [ldRead,loc,addr_digits] using L.2
  have preReady (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (U : pre=u++e::v) :
      DataReady hp (play x u) a e seam width := by
    apply ready u e (v++mark::(gap++turn::back))
    simp only [E,U,List.append_assoc,List.cons_append]
  obtain ⟨t,post,_,Q,R,M⟩ := data_word hp digits x pre a seam width sep plan size s label P old mobile preReady
  obtain ⟨F,read,V,W⟩ := saturate_left digits (play x pre) (addr a seam) width plan size hw Q R accept
  exact ⟨pre,gap,back,mark,turn,t,post,E,F,read,R,M,V,W⟩

/-- Original same-tape form, with all late scoped readiness hypotheses
discharged by the genuine accepted PC9 tour and generated band. Here
`bridge` may be exactly the PC10 through-ACK11 prefix of LeftReturn. -/
theorem accepted_left_original {Tag : Type} (digits : Tag→BitVec 36)
    {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    {a : Fin n} {seam : Nat} (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w9 bridge w : List (Fin n)) (ack9 ack : Fin n)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event9 : Event hp (fun j=>S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted9 : (BStarLongDoor.ctrlOp.read (ring (play origin w9) ack9 (S.getD 0 fall).1).long).toNat=10)
    (hist : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle
      ((w9++ack9::bridge)++w) (.busy 11 (.back 0)))
    (valid : ∀ u v, ((w9++ack9::bridge)++w)=u++v →
      (∀ j,BStarLongFixedRouting.Layout B base j=BStarLongFixedRouting.Layout B (play origin u) j) ∧
      BStarGeneratedBandScan.Band (play origin u) (S.getD 0 fall).1)
    (late : 11≤BStarGeneratedBandScan.pc (play origin (w9++ack9::bridge)) (S.getD 0 fall).1)
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len (play origin (w9++ack9::bridge)) .idle w (.busy 11 (.back 0)))
    (H : Hit hp base (fun j=>S.getD j fall) len (play (play origin (w9++ack9::bridge)) w) ack 11)
    (plan : List Tag) (size : plan.length=width) (s : Ledger Tag) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (headFirst seam label))
    (old : RetainedMatches digits (play origin (w9++ack9::bridge)) (addr a seam) width s)
    (mobile : BStarCopyLeftMark.UpstreamMatches digits (play origin (w9++ack9::bridge)) a seam label) :
    ∃ (pre gap back : List (Fin n)) (mark turn : Fin n) (t : Ledger Tag) (post : Nat→Option Tag),
      w=pre++mark::(gap++turn::back) ∧
      let y := play origin ((w9++ack9::bridge)++pre)
      let read := ldRead y (addr a seam)
      (∀ j<width,(read j).mobile=.empty) ∧
      laneRead read 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      RetainedMatches digits y (addr a seam) width t ∧
      BStarCopyLeftMark.UpstreamMatches digits y a seam post ∧
      headFirst seam post=[] ∧ t.release.pending=[] := by
  have ready := BStarCopyLeftReadyWord.left_ready_word hp chart sep w9 bridge w ack9
    (.busy 11 (.back 0)) G9 event9 accepted9 hist valid late a seam width strip root
  simpa only [BStarResetSchedule.run_append] using accepted_left hp digits chart hw flags
    notShort strip root sep w ack T H plan size s label P old mobile ready

end L4.BStarCopyLeftFence

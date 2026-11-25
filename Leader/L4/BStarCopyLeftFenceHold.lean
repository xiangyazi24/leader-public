import Leader.L4.BStarCopyLeftFence

namespace L4.BStarCopyLeftFenceHold
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets BStarLongWork
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarLongPrep BStarLongCommandData
open BStarCopyRightStrip (addr addr_next)
open BStarCopyRightMark (rightNeighbor_inj)
open BStarCopyLeftStrip BStarCopyLeftMark BStarCopyLeftRetained BStarCopyLeftDeposit
open BStarCopyLeftDataSweep BStarCopyMarkedLedger BStarCopyFenceSaturation BStarCopyFIFO
open BStarFenceReceiverChart BStarCopyLeftFence BStarNativeReceiptTape BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

def Region {n : Nat} (a : Fin n) (seam width : Nat) (i : Fin n) (s : Sheet) : Prop :=
  ∃ j, j<seam+width ∧ addr a j=i ∧ rail seam j=s

theorem address_add {n : Nat} (a : Fin n) (seam j : Nat) :
    addr (addr a seam) j=addr a (seam+j) := by
  rw [addr_digits,addr_from]

private theorem first_address {n : Nat} (a : Fin n) : addr a 0=a := by
  rw [addr_digits]
  rfl

/-- The left settled strip is closed under all selected incoming data
claims. Even in the sole-header wrap the predecessor is on the
correct typed sheet, not an arbitrary site occurrence. -/
theorem ready_frozen (x : X) (a e : Fin n) (seam width : Nat)
    (H : DataReady hp x a e seam width) :
    FrozenRegion hp (Region a seam width) x e := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let Rsv := reserved (round g raw).prep
  refine ⟨?_,?_⟩
  · intro v member
    obtain ⟨j,jt,loc,ty⟩ := member
    by_cases js : j<seam
    · have E : v.occurrence=.ls := by simpa [rail,js] using ty.symm
      obtain ⟨side,sheet⟩ := v
      change sheet=.ls at E
      subst sheet
      exact H.lsPrep j js side loc.symm
    · have E : v.occurrence=.ld := by simpa [rail,js] using ty.symm
      obtain ⟨side,sheet⟩ := v
      change sheet=.ld at E
      subst sheet
      have eq : addr (addr a seam) (j-seam)=addr a j := by
        rw [address_add,show seam+(j-seam)=j by omega]
      exact H.ldPrep (j-seam) (by omega) side (loc.symm.trans eq.symm)
  · intro d D v V dest
    obtain ⟨j,jt,loc,ty⟩ := V
    have dr : d∈dataClaims g := BStarLongFenceTopology.selected_data_raw g Rsv d D
    obtain ⟨s,sh⟩ := v
    cases s with
    | left =>
      have C := no_left_receive g d dr
      have kind : sh=.ls ∨ sh=.ld := by
        change rail seam j=sh at ty
        by_cases q : j<seam
        · left; simpa [rail,q] using ty.symm
        · right; simpa [rail,q] using ty.symm
      rcases kind with rfl|rfl
      · exact False.elim (C.1 dest)
      · exact False.elim (C.2 dest)
    | right =>
      change addr a j=rightNeighbor e at loc
      change rail seam j=sh at ty
      subst sh
      by_cases z : j=0
      · subst j
        have header : g.2.axes.h6=true := by
          change oldH6 B x (rightNeighbor e)=true
          rw [←loc,first_address]
          exact H.strip.source_header
        have ls := (raw_ls_receive g d (by simpa [rail,R,H.strip.seam_pos] using dest)).mp dr
        rw [header] at ls
        exact False.elim (Bool.noConfusion ls.1)
      · have ne : e=addr a (j-1) := by
          apply rightNeighbor_inj
          rw [←addr_next,show j-1+1=j by omega]
          exact loc.symm
        subst e
        have eq : j-1+1=j := by omega
        have dd : d.destination=some (R (rail seam (j-1+1))) := by
          rw [eq]
          exact dest
        have m := selected_hop H.strip (j-1) (by omega) Rsv d D dd
        subst d
        exact ⟨j-1,by omega,rfl,rfl⟩

private theorem upstream_no_label {T : Type} (seam : Nat) (label : Nat→Option T)
    (h : headFirst seam label=[]) : ∀ j<seam,label j=none := by
  have hh : upstreamWord seam label=[] := by
    have e := congrArg List.reverse h
    simpa [headFirst] using e
  rw [upstreamWord,List.flatMap_eq_nil_iff] at hh
  intro j hj
  have J := hh j (List.mem_range.mpr hj)
  cases K : label j <;> simp_all

theorem drained_old {Tag : Type} (digits : Tag → BitVec 36) (x : X) (a : Fin n)
    (seam width : Nat) (label : Nat → Option Tag)
    (ld : ∀ j<width,(ldRead x (addr a seam) j).mobile=.empty)
    (up : UpstreamMatches digits x a seam label) (h : headFirst seam label=[]) :
    ∀ i sh,Region a seam width i sh → (readLane (Sheet.index sh) (x i).long).mobile=.empty := by
  intro i sh R
  obtain ⟨j,jt,rfl,rfl⟩ := R
  by_cases k : j<seam
  · have H := up j k
    rw [upstream_no_label seam label h j k] at H
    exact H
  · have H := ld (j-seam) (by omega)
    rw [ldRead,address_add,show seam+(j-seam)=j by omega] at H
    simpa only [rail,if_neg k] using H

theorem drained_after {Tag : Type} (digits : Tag → BitVec 36)
    (x : X) (a : Fin n) (seam width : Nat) (label : Nat → Option Tag)
    (ld : ∀ j<width,(ldRead x (addr a seam) j).mobile=.empty)
    (up : UpstreamMatches digits x a seam label) (h : headFirst seam label=[])
    (w : List (Fin n)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (ready : ∀ l e r,w=l++e::r → DataReady hp (play x l) a e seam width) :
    ∀ i sh,Region a seam width i sh →
      readLane (Sheet.index sh) (play x w i).long=readLane (Sheet.index sh) (x i).long :=
  drained_word_frame hp _ x w sep (drained_old digits x a seam width label ld up h)
    (fun l e r d=>ready_frozen hp (play x l) a e seam width (ready l e r d))

theorem ld_member {n : Nat} (a : Fin n) (seam width j : Nat) (hi : j<width) :
    Region a seam width (addr (addr a seam) j) .ld :=
  ⟨seam+j,by omega,(address_add a seam j).symm,by simp [rail]⟩

private theorem read_eq_of_cells (x y : Nat→Lane) (i cnt : Nat)
    (h : ∀ j,i≤j → j<i+cnt → x j=y j) :
    laneRead x i cnt=laneRead y i cnt := by
  induction cnt generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [laneRead,laneRead,h _ (by omega) (by omega)]
    congr 1
    exact ih _ (fun j lo hi => h j (by omega) (by omega))

/-- The old K7 validation is preserved on its own mark, through the
old/post states of actual FENCE ACK, and through any explicitly
certified late continuation (e.g. up to the numeric ISSUE12). The
conclusion is equality of physical lane views, not just of values
at a reconstructed ledger. -/
theorem through_ack {Tag : Type} (digits : Tag→BitVec 36)
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    {a : Fin n} {seam : Nat} (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w ext : List (Fin n)) (ack : Fin n)
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 11 (.back 0)))
    (H : Hit hp base (fun j=>S.getD j fall) len (play x w) ack 11)
    (plan : List Tag) (size : plan.length=width) (s : Ledger Tag) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (headFirst seam label))
    (old : RetainedMatches digits x (addr a seam) width s)
    (mobile : UpstreamMatches digits x a seam label)
    (ready : ∀ u e v,w++ack::ext=u++e::v → DataReady hp (play x u) a e seam width) :
    ∃ (pre gap back : List (Fin n)) (mark turn : Fin n),
      w=pre++mark::(gap++turn::back) ∧
      let y := play x pre
      let suffix := mark::((gap++turn::back)++ack::ext)
      laneRead (ldRead y (addr a seam)) 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      (∀ u v,suffix=u++v → ∀ j<width,
        ldRead (play x (pre++u)) (addr a seam) j=ldRead y (addr a seam) j) ∧
      laneRead (ldRead (play x w) (addr a seam)) 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      laneRead (ldRead (ring (play x w) ack) (addr a seam)) 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      laneRead (ldRead (play (ring (play x w) ack) ext) (addr a seam)) 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      (∀ i sh,Region a seam width i sh → (readLane (Sheet.index sh) ((ring (play x w) ack) i).long).mobile=.empty) := by
  have R (u : List (Fin n)) (e : Fin n) (v : List (Fin n)) (h : w=u++e::v) :
      DataReady hp (play x u) a e seam width := by
    apply ready u e (v++ack::ext)
    simp [h,List.append_assoc]
  obtain ⟨pre,gap,back,mark,turn,t,post,E,ld,read,_,up,empty,_⟩ :=
    accepted_left hp digits chart hw flags notShort strip root sep w ack T H plan size s label P old mobile R
  let suffix := mark::((gap++turn::back)++ack::ext)
  have full : w++ack::ext=pre++suffix := by
    simp only [E,suffix,List.append_assoc,List.cons_append]
  have frameAux (u v : List (Fin n)) (uv : suffix=u++v) :
      ∀ i sh, Region a seam width i sh →
        readLane (Sheet.index sh) (play x (pre++u) i).long=readLane (Sheet.index sh) (play x pre i).long := by
    have localReady (p : List (Fin n)) (e : Fin n) (q : List (Fin n)) (d : u=p++e::q) :
        DataReady hp (play (play x pre) p) a e seam width := by
      rw [←BStarResetSchedule.run_append]
      apply ready (pre++p) e (q++v)
      rw [full,uv,d]
      simp only [List.append_assoc,List.cons_append]
    have F := drained_after hp digits (play x pre) a seam width post ld up empty u sep localReady
    rw [BStarResetSchedule.run_append]
    exact F
  have frame (u v : List (Fin n)) (uv : suffix=u++v) :
      ∀ j<width,ldRead (play x (pre++u)) (addr a seam) j=ldRead (play x pre) (addr a seam) j := by
    intro j J
    exact frameAux u v uv _ _ (ld_member a seam width j J)
  have word (u v : List (Fin n)) (uv : suffix=u++v) :
      laneRead (ldRead (play x (pre++u)) (addr a seam)) 0 width=plan.reverse.map (Digit9.data ∘ digits) :=
    (read_eq_of_cells _ _ _ _ (fun j _ J=>frame u v uv j (by omega))).trans read
  let mid := mark::(gap++turn::back)
  have midEq : w=pre++mid := E
  have su : suffix=mid++ack::ext := rfl
  have oldWord := word mid (ack::ext) su
  rw [←midEq] at oldWord
  have ackWord := word (mid++[ack]) ext (by rw [su,List.append_assoc]; rfl)
  rw [←List.append_assoc,←midEq,BStarResetSchedule.run_append] at ackWord
  have endWord := word suffix [] (by simp)
  rw [←full,BStarResetSchedule.run_append] at endWord
  have drainedAtAck := frameAux (mid++[ack]) ext (by rw [su,List.append_assoc]; rfl)
  rw [←List.append_assoc,←midEq,BStarResetSchedule.run_append] at drainedAtAck
  refine ⟨pre,gap,back,mark,turn,E,read,frame,oldWord,ackWord,endWord,?_⟩
  intro i sh R
  have eql : readLane (Sheet.index sh) (ring (play x w) ack i).long =
      readLane (Sheet.index sh) (play x pre i).long := drainedAtAck i sh R
  rw [eql]
  exact drained_old digits (play x pre) a seam width post ld up empty i sh R

/-- Actual whole owner tape: late readiness follows from its accepted PC9
prefix and generated band, so no late service oracle is needed. -/
theorem original_through_ack {Tag : Type} (digits : Tag→BitVec 36)
    {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    {a : Fin n} {seam : Nat} (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w9 bridge w ext : List (Fin n)) (ack9 ack : Fin n) (endMode : Mode)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event9 : Event hp (fun j=>S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted9 : (BStarLongDoor.ctrlOp.read (ring (play origin w9) ack9 (S.getD 0 fall).1).long).toNat=10)
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle
      ((w9++ack9::bridge)++(w++ack::ext)) endMode)
    (valid : ∀ u v, ((w9++ack9::bridge)++(w++ack::ext))=u++v →
      (∀ j,BStarLongFixedRouting.Layout B base j=BStarLongFixedRouting.Layout B (play origin u) j) ∧
      BStarGeneratedBandScan.Band (play origin u) (S.getD 0 fall).1)
    (late : 11≤BStarGeneratedBandScan.pc (play origin (w9++ack9::bridge)) (S.getD 0 fall).1)
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len (play origin (w9++ack9::bridge)) .idle w (.busy 11 (.back 0)))
    (H : Hit hp base (fun j=>S.getD j fall) len (play (play origin (w9++ack9::bridge)) w) ack 11)
    (plan : List Tag) (size : plan.length=width) (s : Ledger Tag) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (headFirst seam label))
    (old : RetainedMatches digits (play origin (w9++ack9::bridge)) (addr a seam) width s)
    (mobile : UpstreamMatches digits (play origin (w9++ack9::bridge)) a seam label)
    :
    ∃ (pre gap back : List (Fin n)) (mark turn : Fin n),
      w=pre++mark::(gap++turn::back) ∧
      let y := play (play origin (w9++ack9::bridge)) pre
      let suffix := mark::((gap++turn::back)++ack::ext)
      laneRead (ldRead y (addr a seam)) 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      (∀ u v,suffix=u++v → ∀ j<width,
        ldRead (play (play origin (w9++ack9::bridge)) (pre++u)) (addr a seam) j=ldRead y (addr a seam) j) ∧
      laneRead (ldRead (play (play origin (w9++ack9::bridge)) w) (addr a seam)) 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      laneRead (ldRead (ring (play (play origin (w9++ack9::bridge)) w) ack) (addr a seam)) 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      laneRead (ldRead (play (ring (play (play origin (w9++ack9::bridge)) w) ack) ext) (addr a seam)) 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      (∀ i sh,Region a seam width i sh → (readLane (Sheet.index sh) ((ring (play (play origin (w9++ack9::bridge)) w) ack) i).long).mobile=.empty) := by
  have ready := BStarCopyLeftReadyWord.left_ready_word hp chart sep w9 bridge (w++ack::ext) ack9
    endMode G9 event9 accepted9 history valid late a seam width strip root
  exact through_ack hp digits chart hw flags notShort strip root sep w ext ack T H plan size s label P old mobile ready

end L4.BStarCopyLeftFenceHold

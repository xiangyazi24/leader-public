import Leader.L4.BStarCopyRightReturn

namespace L4.BStarCopyRightGeometryWord
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongDoor BStarGeneratedOwner BStarLongFixedRouting BStarGeneratedBandScan
open BStarCopyRightStrip BStarCopyRightRetained BStarCopyRightAuthority BStarCopyRightReady
open BStarCopyRightReadyWord BStarCopyRightReturn BStarCopyGateAuthority
open BStarClearanceDataChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarSeparatingRail

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


/-- All retained RD and upstream RD/RS gates in the right COPY
projection stay open at every original post-ACK9 cut of the same
compiler attempt, including PC10 release/turn/return and PC11.
No late PC premise and no per-slot winner/gate premise. -/
theorem right_gates_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w9 rest : List (Fin n)) (ack : Fin n) (endMode : Mode)
    (G9 : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w9 (.busy 9 (.back 0)))
    (event : Event hp (fun j => S.getD j fall) len (play x w9) ack (.busy 9 (.back 0)) .idle)
    (accepted : (ctrlOp.read (ring (play x w9) ack (S.getD 0 fall).1).long).toNat=10)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle (w9++ack::rest) endMode)
    (valid : ∀ u v, w9++ack::rest=u++v →
      (∀ j, Layout B base j=Layout B (play x u) j) ∧ Band (play x u) (S.getD 0 fall).1)
    (root bAddr : Fin n) (width seam tail : Nat)
    (dest : Dest B base root width) (strip : Strip B base bAddr seam tail)
    (join : addr bAddr 0=addr root (width-1))
    (ownHead : dataOwner (oldH6 B base) (addr bAddr 0) (rail seam 0)=o.val) :
    ∀ a b, rest=a++b →
      GeometryGates hp base (play x (w9++ack::a)) root bAddr width seam tail := by
  have all := enabled_after_accept9 hp chart sep G9 event accepted
  have headRD : dataOwner (oldH6 B base) (addr root (width-1)) .rd=o.val := by
    rwa [show rail seam 0=.rd from if_pos strip.seam_pos,join] at ownHead
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
  refine ⟨same,dest_layout hp root width dest same,strip_layout hp bAddr seam tail strip same,
    (fun j J => gate _ _ rfl ((dest_owner hp root width dest j J).trans headRD)),?_⟩
  intro j jp jt
  apply gate
  · by_cases h : j<seam
    · simp [rail,h,activeSheet]
    · simp [rail,h,activeSheet,strip.rs_in j (by omega) jt]
  · exact (strip_same_owner strip j jt).trans ownHead

#print axioms right_gates_word
end L4.BStarCopyRightGeometryWord

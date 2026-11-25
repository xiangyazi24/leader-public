import Leader.L4.BStarNumericChronology
import Leader.L4.BStarGrantWriterHistory

namespace L4.BStarCommitNoPrior
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongRouting
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarH6WordChart
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireHistorySample
open BStarGrantWriterHistory BStarResetSchedule BStarSeparatorControl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- A real publication at the tracked physical K1 reads a healthy old
forward at that slot and leaves its literal trail there. -/
theorem publishes_leaves {x : X} (e i : Fin n) (sep : e≠rightNeighbor e)
    (s : Side) (E : i=site e s) (a : Publication) (side : a.endpoint=s)
    (pub : a∈(longTrace (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).publications) :
    (∃ q, atCursor x (i,1)=.forward q ∧ BStarCommitLineage.CommitF q) ∧
      atCursor (step x e) (i,1)=.trail := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  obtain ⟨C,p,sel,endsrc,Lit⟩ := (literal_event_iff g raw a).mp pub
  have hm : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have CK := center_of g C hm Lit.1
  have src : C.source=L 1 := by rw [CK]; rfl
  have ES : s=C.source.side := side.symm.trans endsrc
  have I : (i,(1 : Fin 11))=address e C.source := by
    rw [src] at ES ⊢
    rw [ES] at E
    exact Prod.ext E rfl
  obtain ⟨q,Q,H,O⟩ := BStarForwardProvenance.offer_origin g raw C p sel Lit.2.2.1
  have old : atCursor x (i,1)=.forward q := by
    rw [I,←old_read x e C.source]
    exact Q
  have cQ : BStarCommitLineage.CommitF q := ⟨H,(congrArg BitVec.toNat O).trans Lit.2.2.2.1⟩
  refine ⟨⟨q,old,cQ⟩,?_⟩
  let d : AtK := R (if g.2.axes.h6 then 2 else 1)
  have dst : C.destination=some d := by rw [CK]; rfl
  have ne := (BStarAcquireReturn.link_shape g C d hm dst).1
  have T := (BStarClearanceForward.move_lands g raw C p d dst sel (Ne.symm ne)).1
  let pair := (x e,x (rightNeighbor e))
  have J := BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp pair C.source
      (fun hr _ => (by rw [src] at hr; contradiction))
  rw [I]
  rw [←new_read B x e sep C.source,J]
  change decode (readRaw (patchPair (longWork g raw) raw) C.source)=_
  rw [T,decode_encode]

private theorem single {x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {z d : Cursor} (seen : Seen step (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases seen with
  | cons _ _ t _ tail => cases tail; exact t

private theorem at_out {x : X} {addr : Nat → Pos n} {len : Nat}
    {i : Fin n} {k : Nat} (hi : k≤len) (A : addr k=(i,1))
    (z : Cursor) (G : Good anyTag len (project addr x) z)
    (clean : OutClean len (project addr x) z)
    (f : ∃ q, atCursor x (i,1)=.forward q ∧ BStarCommitLineage.CommitF q) :
    z=.out k := by
  obtain ⟨q,F,_⟩ := f
  have Q : anyTag.F (project addr x k) := ⟨q,by change atCursor x (addr k)=_; rw [A,F]⟩
  cases z with
  | back j => exact (BStarOwnerControlHistory.pointed_backward_no_forward _ len j G k hi Q).elim
  | out j =>
    have E := (BStarOwnerControlHistory.pointed_unique_forward _ len j G clean k hi).mp Q
    exact congrArg Cursor.out E.symm

/-- On a busy segment that still ends outward, the output cursor
index cannot rewind. This does not depend on the carried opcode. -/
theorem outward_mono {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x z w d) :
    ∀ k l, z=.out k → d=.out l → k≤l := by
  induction P with
  | nil x =>
    intro k l K L
    have := Cursor.out.inj (K.symm.trans L)
    omega
  | @cons x z d fin e w I E tail ih =>
    intro k l K L
    subst z
    obtain ⟨j,N⟩ := busy_no_back_to_out hp tail ⟨l,L⟩
    subst d
    have A : Advance len (.out k) (.out j) := by
      cases E with
      | transit _ _ _ _ seen => exact single hp seen
    have S := ih j l rfl L
    cases A <;> omega

/-- No publication at this header occurs on an uninterrupted busy
prefix ending at or before its outward K1. The statement is for every
raw split of the exact tape and the real publication records. -/
theorem before_center {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x z w d) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (hi : k≤len) (A : addr k=(i,1)) :
    ∀ l, d=.out l → l≤k → BeforePublication hp x i w := by
  induction P with
  | nil I =>
    intro l D L u e v H
    cases u <;> contradiction
  | @cons x z d fin e w I E tail ih =>
    intro l D L u mark v split
    cases u with
    | cons a u =>
      obtain ⟨eq,rest⟩ : e=a ∧ w=u++mark::v := List.cons.inj split
      subst a
      exact ih l D L u mark v rest
    | nil =>
      obtain ⟨eq,_⟩ : e=mark ∧ w=v := List.cons.inj split
      subst mark
      intro s addrEq a pub side
      have out := publishes_leaves hp (x := x) e i (sep e) s addrEq a side pub
      have Z := at_out hi A z I.2.1 I.2.2 out.1
      subst z
      obtain ⟨j,E'⟩ := busy_no_back_to_out hp tail ⟨l,D⟩
      subst d
      have M := outward_mono hp tail j l rfl D
      have Q : Advance len (.out k) (.out j) := by
        cases E with
        | transit _ _ _ _ seen => exact single hp seen
      cases Q with
      | forward => omega
      | stay =>
        have next := (busy_start hp tail).2.1.2.1
        change anyTag.F (atCursor (step x e) (addr k)) at next
        rw [A,out.2] at next
        exact (BStarSeparatorParked.forward_not_trail next).elim

/-- A recovered COMMIT launch paired with a current outward centre
cannot already have published at that centre on its post-launch tape.
The pre-launch prefix is deliberately outside this claim. -/
theorem found_before_center {base x : X} {addr : Nat → Pos n} {len k : Nat}
    {w : List (Fin n)} (F : Found hp base addr len BStarLongCommand.commitOp x w (.out k))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (hi : k≤len) (A : addr k=(i,1)) :
    ∃ pre post e, w=pre++e::post ∧
      let old := BStarResetSchedule.run step x pre
      let new := step old e
      e=RearTrace.predecessor (addr 0).1 ∧
      BStarClearanceSource.Launch (old (addr 0).1).long (new (addr 0).1).long ∧
      (BStarLongDoor.ctrlOp.read (old (addr 0).1).long).toNat=BStarLongCommand.commitOp ∧
      BusyOnly hp base addr len BStarLongCommand.commitOp new (.out 0) post (.out k) ∧
      BeforePublication hp new i post := by
  obtain ⟨pre,post,e,S,D,L,O,P⟩ := F
  exact ⟨pre,post,e,S,D,L,O,P,before_center hp P sep i k hi A k rfl (Nat.le_refl _)⟩

private def Past (k : Nat) : Cursor → Prop
  | .out j => k<j
  | .back _ => True

private theorem past_step {len k : Nat} {z d : Cursor}
    (P : Past k z) (S : Advance len z d) : Past k d := by
  cases S
  · exact P
  · unfold Past at *; omega
  · exact True.intro
  · exact True.intro

private theorem past_event {x : X} {addr : Nat → Pos n} {len op k : Nat}
    {e : Fin n} {z d : Cursor} (P : Past k z)
    (E : Event hp addr len x e (.busy op z) (.busy op d)) :
    Past k d := by
  cases E with
  | transit _ _ _ _ seen => exact past_step P (single hp seen)
  | arrived_hold _ => exact True.intro

private theorem no_pub_past {base x : X} {addr : Nat → Pos n} {len op k : Nat}
    {i : Fin n} {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x z w d) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (hi : k≤len) (addrK : addr k=(i,1)) (T : Past k z) :
    BeforePublication hp x i w := by
  induction P with
  | nil I => intro u e v H; cases u <;> contradiction
  | @cons x z d fin e w I E tail ih =>
    intro u mark v split
    cases u with
    | cons a u =>
      obtain ⟨eq,rest⟩ : e=a ∧ w=u++mark::v := List.cons.inj split
      subst a
      exact ih (past_event hp T E) u mark v rest
    | nil =>
      obtain ⟨eq,_⟩ : e=mark ∧ w=v := List.cons.inj split
      subst mark
      intro s eq a m side
      have old := (publishes_leaves hp (x := x) e i (sep e) s eq a side m).1
      have J := at_out hi addrK z I.2.1 I.2.2 old
      rw [J] at T
      exact (Nat.lt_irrefl k T).elim

/-- Once one same-header publication is selected during the busy
tour, every subsequent mark of that same tour is nonpublishing at
that header. Together with the literal one-event-per-mark bound,
this gives at most one publication at this header per busy tour. -/
theorem after_publication {base x : X} {addr : Nat → Pos n} {len op k : Nat}
    {i : Fin n} {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x z w d) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (hi : k≤len) (addrK : addr k=(i,1)) :
    ∀ pre e post, w=pre++e::post →
    ¬NoPublication hp (BStarResetSchedule.run step x pre) e i →
      BeforePublication hp (BStarResetSchedule.run step x (pre++[e])) i post := by
  classical
  induction P with
  | nil I => intro u e v H; cases u <;> contradiction
  | @cons x z d fin e w I E tail ih =>
    intro pre mark post split pub
    cases pre with
    | cons a pre =>
      obtain ⟨eq,rest⟩ : e=a ∧ w=pre++mark::post := List.cons.inj split
      subst a
      exact ih pre mark post rest pub
    | nil =>
      obtain ⟨eq,rest⟩ : e=mark ∧ w=post := List.cons.inj split
      subst mark
      subst post
      have actual : ∃ s : Side, ∃ a : Publication, i=site e s ∧ a.endpoint=s ∧
          a∈(longTrace (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).publications := by
        apply Classical.byContradiction
        intro N
        apply pub
        intro s eq a m side
        exact N ⟨s,a,eq,side,m⟩
      obtain ⟨s,a,eq,side,m⟩ := actual
      obtain ⟨old,T⟩ := publishes_leaves hp (x := x) e i (sep e) s eq a side m
      have J := at_out hi addrK z I.2.1 I.2.2 old
      subst z
      have Q : Advance len (.out k) d := by
        cases E with
        | transit _ _ _ _ seen => exact single hp seen
      apply no_pub_past hp tail sep hi addrK
      cases Q with
      | turn => exact True.intro
      | forward => exact Nat.lt_succ_self _
      | stay =>
        have next := (busy_start hp tail).2.1.2.1
        change anyTag.F (atCursor (step x e) (addr k)) at next
        rw [addrK,T] at next
        exact (BStarSeparatorParked.forward_not_trail next).elim

end L4.BStarCommitNoPrior

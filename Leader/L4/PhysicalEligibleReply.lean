import Leader.L4.PhysicalCustodyCommutation
import Leader.L4.BStarResetHealthyCycle
import Leader.L4.BStarGeneratedOwner

namespace L4.PhysicalEligibleReply
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarLongFixedRouting BStarAcquireForwardTrace BStarResetChartTouch
open BStarResetChartService BStarResetMarkAdapter BStarResetRailRing
open BStarResetSchedule BStarSeparatingRail BStarAcquireWaitControl
open BStarResetCycle BStarResetHealthyService BStarGeneratedOwner BStarClearanceSource
local notation "hp" => (show 0<2 by decide)

/-- The complete rail, not just the source byte, is ready for the
independent old reply-consume row. -/
def Eligible {s n : Nat} (base : Raw s n) (addr : Nat→Pos n) (len op : Nat) (y : Raw s n) : Prop :=
  Waiting hp base (addr 0).1 op y ∧ Clean (project addr) (healthyTag op) len y ∧
    project addr y 0=finish (BStarResetTaggedRows.resetPayload op)

/-- Clean post-consume issue state for every address of the same chart. -/
def Ready {s n : Nat} (addr : Nat→Pos n) (len op : Nat) (y : Raw s n) : Prop :=
  (∀ j≤len,project addr y j=.empty) ∧
  (ctrlPhase.read (y (addr 0).1).long).toNat=1 ∧
  (ctrlOp.read (y (addr 0).1).long).toNat=op

theorem away_of_disjoint {n : Nat} (root e : Fin n)
    (H : DisjointMarks e (RearTrace.predecessor root)) :
    e≠RearTrace.predecessor root ∧ rightNeighbor e≠root ∧ e≠root := by
  have right := RearTrace.right_predecessor root
  exact ⟨H.1,by rw [←right]; exact H.2.2.2,by rw [←right]; exact H.2.1⟩

/-- Endpoint-disjoint marks preserve the exact healthy old reply, the
waiting controller, and the empty suffix of the whole owner chart. -/
theorem eligible_gap {s n : Nat} {base y : Raw s n} {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (opSmall : op<3) (gap : List (Fin n))
    (ind : ∀ e∈gap,DisjointMarks e (RearTrace.predecessor (S.getD 0 fall).1))
    (q : Q y) (live : Eligible base (fun j=>S.getD j fall) len op y) :
    Q (rawRun y gap) ∧ Eligible base (fun j=>S.getD j fall) len op (rawRun y gap) := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  induction gap generalizing y with
  | nil => exact ⟨q,live⟩
  | cons e w ih =>
    have A := away_of_disjoint root e (ind e List.mem_cons_self)
    have E : rawNext s y e root=y root := by
      simp only [rawNext,AllSizeS1Geometry.step,if_neg (Ne.symm A.2.2),if_neg (Ne.symm A.2.1)]
    have H : project addr (rawNext s y e) 0=project addr y 0 := by
      change atSite (rawNext s y e root).long (addr 0).2=_
      rw [E]
      rfl
    have q' := closed _ e q
    have weak : Clean (project addr) BStarSeparatorControl.anyTag len y := by
      refine ⟨?_,live.2.1.2⟩
      have fin : finish (BStarResetTaggedRows.resetPayload op)=.reply (BStarResetTaggedRows.resetPayload op) := by
        have r : op=0 ∨ op=1 ∨ op=2 := by omega
        rcases r with r|r|r <;> subst op <;> decide
      exact ⟨_,live.2.2.trans fin⟩
    have suf := BStarResetConsumedClean.suffix_empty_any hp C (fiber _ q) weak e (sep e)
    have now : Eligible base addr len op (rawNext s y e) := by
      refine ⟨⟨fiber _ q',?_,?_,?_⟩,⟨?_,suf⟩,H.trans live.2.2⟩
      · rw [E]; exact live.1.2.1
      · rw [E]; exact live.1.2.2.1
      · rw [E]; exact live.1.2.2.2
      · rw [H]; exact live.2.1.1
    exact ih (fun f F => ind f (List.mem_cons_of_mem _ F)) q' now

/-- Genuine consumption of the healthy old payload leaves the entire
chart empty and advances the controller to the next ISSUE. -/
theorem consume {s n : Nat} {base y : Raw s n} {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (H : op<3) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (live : Eligible base (fun j=>S.getD j fall) len op y) :
    Ready (fun j=>S.getD j fall) len (op+1) (rawNext s y (RearTrace.predecessor (S.getD 0 fall).1)) := by
  have weak : Clean (project (fun j=>S.getD j fall)) (resetTag op) len y :=
    ⟨weakD op _ live.2.1.1,live.2.1.2⟩
  obtain ⟨empty,phase,pc⟩ := BStarResetConsumedClean.consumed_clean hp C op H live.1 weak sep
  have E := congrArg BitVec.toNat (pc live.2.2)
  have eq : (BitVec.ofNat 9 (op+1)).toNat=op+1 := (BitVec.toNat_ofNat _ _).trans (Nat.mod_eq_of_lt (by omega))
  exact ⟨empty,(congrArg BitVec.toNat phase),E.trans eq⟩

open BStarOwnerControlHistory

/-- Quiescent full chart between the actual first consume and the next
sampled source launch. This statement is pointwise on the chosen word. -/
theorem ready_gap {s n : Nat} {base y : Raw s n} {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (gap : List (Fin n))
    (ind : ∀ e∈gap,e≠RearTrace.predecessor (S.getD 0 fall).1)
    (q : Q y) (ready : Ready (fun j=>S.getD j fall) len op y) :
    Q (rawRun y gap) ∧ Ready (fun j=>S.getD j fall) len op (rawRun y gap) := by
  induction gap generalizing y with
  | nil => exact ⟨q,ready⟩
  | cons e w ih =>
    have z := idle_nonown hp C (fiber _ q) ready.1 e (sep e) (ind e List.mem_cons_self)
    have phase := congrArg (fun a : BitVec 2 × BitVec 9 => a.1.toNat) z.2
    have code := congrArg (fun a : BitVec 2 × BitVec 9 => a.2.toNat) z.2
    exact ih (fun a A => ind a (List.mem_cons_of_mem _ A)) (closed _ e q)
      ⟨z.1,phase.trans ready.2.1,code.trans ready.2.2⟩

def Launched {s n : Nat} (base : Raw s n) (addr : Nat→Pos n) (len op : Nat) (y : Raw s n) : Prop :=
  Current hp base addr len y (.busy op (.out 0)) ∧
    project addr y 0=.forward (BStarResetTaggedRows.resetPayload op)

/-- The literal next source mark launches its canonical zero-argument
reset, with the rest of this owner chart empty immediately after it. -/
theorem launch {s n : Nat} {base y : Raw s n} {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (H : op<3) (q : Q y) (ready : Ready (fun j=>S.getD j fall) len op y) :
    Launched base (fun j=>S.getD j fall) len op (rawNext s y (RearTrace.predecessor (S.getD 0 fall).1)) := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let z := rawNext s y door
  have R : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨head,slot⟩ := root_header hp C (fiber _ q)
  have hD : oldH6 (rows s) y (rightNeighbor door)=true := by rw [R]; exact head
  have P : (ctrlPhase.read (y (rightNeighbor door)).long).toNat=1 := by rw [R]; exact ready.2.1
  have O : (ctrlOp.read (y (rightNeighbor door)).long).toNat=op := by rw [R]; exact ready.2.2
  have F := genuine_wait hp y door (sep door) op H hD P O
  rw [R] at F
  have pt : project addr z 0=.forward (BStarResetTaggedRows.resetPayload op) := by
    change atSite (z root).long (S.getD 0 fall).2=_
    rw [slot]
    exact F.1
  refine ⟨⟨⟨fiber _ (closed _ door q),F.2⟩,
    ⟨Nat.zero_le _,⟨_,pt⟩,fun j J => (Nat.not_lt_zero j J).elim⟩,?_⟩,pt⟩
  intro j J L
  exact empty_away_from_door hp C (fiber _ q) ready.1 door (sep door) j (.inl J) L

/-- The two real adjacent replay doors, with the original healthy Seen
word for the first stage and the exact initialized second-stage chart.
The intervening disjoint marks are moved after the next launch. The
corresponding original consume→gap state is independently eligible to
launch too; this fact does not come from endpoint equality. -/
theorem eligible_reply_replay {s n : Nat} {base seed : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (H : op<2) (qs : Q seed) (pre gap tail : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let door := RearTrace.predecessor root
    let old := rawRun (rawNext s seed door) pre
    let consumed := rawNext s old door
    let replay := door::(pre++door::door::(gap++tail))
    Seen (rawNext s) (project addr) (healthyTag op) len (rawNext s seed door) (.out 0) pre (.back 0) →
    Eligible base addr len op old →
    (ctrlPhase.read (seed root).long).toNat=1 →
    (ctrlOp.read (seed root).long).toNat=op →
    (∀ e∈gap,DisjointMarks e door) →
    Commuted (door::(pre++door::(gap++door::tail))) replay ∧
    BStarResetHealthyCycle.Stage hp addr len op seed (door::(pre++[door])) consumed ∧
    Ready addr len (op+1) consumed ∧
    Launched base addr len (op+1) (rawNext s consumed door) ∧
    (∀ a b,gap=a++b → Ready addr len (op+1) (rawRun consumed a)) ∧
    Launched base addr len (op+1) (rawNext s (rawRun consumed gap) door) := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let old := rawRun (rawNext s seed door) pre
  let consumed := rawNext s old door
  intro seen live phase pc ind
  have runQ (st : Raw s n) (w : List (Fin n)) (q : Q st) : Q (rawRun st w) := by
    induction w generalizing st with
    | nil => exact q
    | cons e w ih => exact ih _ (closed _ e q)
  have qOld : Q old := runQ _ _ (closed _ door qs)
  have qD : Q consumed := closed _ door qOld
  have ready := consume C (by omega) sep live
  have after := launch C Q fiber closed sep (by omega : op+1<3) qD ready
  have gate (a b : List (Fin n)) (split : gap=a++b) :
      Q (rawRun consumed a) ∧ Ready addr len (op+1) (rawRun consumed a) :=
    ready_gap C Q fiber closed sep a
      (fun e mem => (away_of_disjoint root e (ind e (split.symm ▸ List.mem_append_left b mem))).1) qD ready
  have last := gate gap [] (List.append_nil gap).symm
  have original := launch C Q fiber closed sep (by omega : op+1<3) last.1 last.2
  have commute := commute_prefix (door::(pre++[door])) (bubble_door gap tail door ind)
  refine ⟨?_,?_,ready,after,fun a b eq => (gate a b eq).2,original⟩
  · simpa only [List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using commute
  · refine ⟨pre,rfl,?_,phase,pc,seen,live.2.2⟩
    change consumed=rawRun (rawNext s seed door) (pre++[door])
    exact (BStarResetSchedule.run_append (rawNext s) (rawNext s seed door) pre [door]).symm

open BStarResetChartNomination BStarSeparatingProgress BStarAcquireRailCoverage

private theorem root_frame {s n : Nat} (y : Raw s n) (root : Fin n) (w : List (Fin n))
    (ind : ∀ e∈w,DisjointMarks e (RearTrace.predecessor root)) :
    rawRun y w root=y root := by
  induction w generalizing y with
  | nil => rfl
  | cons e w ih =>
    have A := away_of_disjoint root e (ind e List.mem_cons_self)
    have E : rawNext s y e root=y root := by
      simp only [rawNext,AllSizeS1Geometry.step,if_neg (Ne.symm A.2.2),if_neg (Ne.symm A.2.1)]
    exact (ih _ (fun f F=>ind f (List.mem_cons_of_mem _ F))).trans E

/-- The marks bubbled past the launch become a real healthy Seen prefix
of that next reset. None touches its source; no back-zero can occur in
the reordered gap. -/
theorem launched_gap_seen {s n : Nat} {base y : Raw s n} {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair (rows s) base i; continuation g.1 g.2=true)
    (H : op<3) (qy : Q y) (F : Launched base (fun j=>S.getD j fall) len op y)
    (gap : List (Fin n)) (ind : ∀ e∈gap,DisjointMarks e (RearTrace.predecessor (S.getD 0 fall).1)) :
    let addr := fun j=>S.getD j fall
    Seen (rawNext s) (project addr) (healthyTag op) len y (.out 0) gap (.out 0) ∧
    Q (rawRun y gap) ∧ Waiting hp base (addr 0).1 op (rawRun y gap) := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let token := BStarResetTaggedRows.resetPayload op
  obtain ⟨noms,link,terminal⟩ := fixed_nominations hp C head cont
  have adapter := healthy_adapter_on hp C Q fiber (fun t q e=>closed t e q) sep op H noms link terminal
  have good : Good (healthyTag op) len (project addr y) (.out 0) :=
    ⟨Nat.zero_le _,F.2,fun j J=>(Nat.not_lt_zero j J).elim⟩
  have reflect (pre : List (Fin n)) (sub : ∀ e∈pre,e∈gap) :
      project addr (rawRun y pre) 0=.forward token := by
    change atSite (rawRun y pre (addr 0).1).long (addr 0).2=_
    rw [root_frame y (addr 0).1 pre (fun e E=>ind e (sub e E))]
    exact F.2
  rcases word_progress adapter gap y (.out 0) ⟨qy,F.1.1⟩ good with stopped|⟨d,seen,inv,G,live,_,_⟩
  · obtain ⟨pre,tail,W,_,_,CL⟩ := stopped
    have obs := reflect pre (fun e E=>W.symm ▸ List.mem_append_left tail E)
    have eq : project addr (rawRun y pre) 0=finish token := CL.1
    exact ((healthy_sane op H).incompatible _ eq obs).elim
  · have obs := reflect gap (fun _ E=>E)
    have E : d=.out 0 := by
      cases d with
      | out j =>
        cases j with
        | zero => rfl
        | succ j =>
          have trail := G.2.2 0 (Nat.zero_lt_succ j)
          exact Token.noConfusion (trail.symm.trans obs)
      | back j =>
        cases j with
        | zero => exact (live rfl).elim
        | succ j =>
          have trail := G.2.2.1 0 (Nat.zero_lt_succ j)
          exact Token.noConfusion (trail.symm.trans obs)
    exact ⟨E ▸ seen,inv⟩

/-- Both waits on a successful sampled doublet can be moved after its
two doors. The first wait separately preserves full old-reply
eligibility; the concatenated waits are the next stage's healthy Seen
prefix on the replay. -/
theorem two_gaps_replay {s n : Nat} {base seed : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair (rows s) base i; continuation g.1 g.2=true)
    (H : op<2) (qs : Q seed) (pre g₁ g₂ tail : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let door := RearTrace.predecessor root
    let old := rawRun (rawNext s seed door) pre
    let consumed := rawNext s old door
    let launched := rawNext s consumed door
    Seen (rawNext s) (project addr) (healthyTag op) len (rawNext s seed door) (.out 0) pre (.back 0) →
    Eligible base addr len op old →
    (ctrlPhase.read (seed root).long).toNat=1 →
    (ctrlOp.read (seed root).long).toNat=op →
    (∀ e∈g₁,DisjointMarks e door) → (∀ e∈g₂,DisjointMarks e door) →
    Commuted (door::(pre++(g₁++door::(g₂++door::tail)))) (door::(pre++door::door::((g₁++g₂)++tail))) ∧
    BStarResetHealthyCycle.Stage hp addr len op seed (door::(pre++[door])) consumed ∧
    (∀ a b,g₁=a++b → Eligible base addr len op (rawRun old a)) ∧
    Seen (rawNext s) (project addr) (healthyTag (op+1)) len launched (.out 0) (g₁++g₂) (.out 0) ∧
    Q (rawRun launched (g₁++g₂)) ∧ Waiting hp base root (op+1) (rawRun launched (g₁++g₂)) := by
  dsimp only
  intro seen live pc ph A D
  let root := (S.getD 0 fall).1
  let door := RearTrace.predecessor root
  let old := rawRun (rawNext s seed door) pre
  let consumed := rawNext s old door
  have qr (y : Raw s n) (w : List (Fin n)) (h : Q y) : Q (rawRun y w) := by
    induction w generalizing y with
    | nil => exact h
    | cons e w ih => exact ih _ (closed _ e h)
  have qOld := qr (rawNext s seed door) pre (closed _ door qs)
  have qF : Q (rawNext s consumed door) := closed _ door (closed _ door qOld)
  have AD : ∀ e∈g₁++g₂, DisjointMarks e door :=
    fun e mem=>(List.mem_append.mp mem).elim (A e) (D e)
  obtain ⟨R,Stage,_,F,_,_⟩ :=
    eligible_reply_replay C Q fiber closed sep H qs pre (g₁++g₂) tail seen live pc ph AD
  have bubble := commute_prefix (door::pre) (bubble_door g₁ (g₂++door::tail) door A)
  have T : Commuted (door::(pre++(g₁++door::(g₂++door::tail))))
      (door::(pre++door::((g₁++g₂)++door::tail))) := by
    simpa only [List.cons_append,List.append_assoc] using bubble
  have gap := launched_gap_seen C Q fiber closed sep head cont (by omega : op+1<3) qF F (g₁++g₂) AD
  refine ⟨.trans T R,Stage,?_,gap⟩
  intro a b W
  exact (eligible_gap C Q fiber closed sep (by omega : op<3) a
    (fun e mem=>A e (W.symm ▸ List.mem_append_left b mem)) qOld live).2

/-- A final successful one-door wait completes the healthy stage in
the middle of the replay, not necessarily at its final endpoint. The
disjoint gap is retained afterward. -/
theorem final_gap_replay {s n : Nat} {base seed : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (H : op<3) (qs : Q seed) (pre gap tail : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let door := RearTrace.predecessor root
    let old := rawRun (rawNext s seed door) pre
    let consumed := rawNext s old door
    Seen (rawNext s) (project addr) (healthyTag op) len (rawNext s seed door) (.out 0) pre (.back 0) →
    Eligible base addr len op old →
    (ctrlPhase.read (seed root).long).toNat=1 →
    (ctrlOp.read (seed root).long).toNat=op →
    (∀ e∈gap,DisjointMarks e door) →
    Commuted (door::(pre++(gap++door::tail))) (door::(pre++door::(gap++tail))) ∧
    BStarResetHealthyCycle.Stage hp addr len op seed (door::(pre++[door])) consumed ∧
    (∀ a b,gap=a++b → Eligible base addr len op (rawRun old a)) ∧
    Ready addr len (op+1) consumed := by
  dsimp only
  intro seen live phase pc ind
  let root := (S.getD 0 fall).1
  let door := RearTrace.predecessor root
  let old := rawRun (rawNext s seed door) pre
  let consumed := rawNext s old door
  have qr (x : Raw s n) (w : List (Fin n)) (h : Q x) : Q (rawRun x w) := by
    induction w generalizing x with
    | nil => exact h
    | cons e w ih => exact ih _ (closed _ e h)
  have W := commute_prefix (door::pre) (bubble_door gap tail door ind)
  refine ⟨by simpa only [List.cons_append] using W,
    ⟨pre,rfl,?_,phase,pc,seen,live.2.2⟩,?_,consume C H sep live⟩
  · change consumed=rawRun (rawNext s seed door) (pre++[door])
    exact (BStarResetSchedule.run_append (rawNext s) (rawNext s seed door) pre [door]).symm
  · intro a b E
    exact (eligible_gap C Q fiber closed sep H a
      (fun e mem=>ind e (E.symm ▸ List.mem_append_left b mem))
      (qr _ pre (closed _ door qs)) live).2

end L4.PhysicalEligibleReply

import Leader.L4.PhysicalRacePrefixes

namespace L4.PhysicalRaceCutAdapters
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarLongFixedRouting BStarAcquireForwardTrace BStarResetChartTouch
open BStarResetChartService BStarResetMarkAdapter BStarResetRailRing
open BStarResetSchedule BStarSeparatingRail BStarAcquireWaitControl
open BStarGeneratedOwner BStarClearanceSource BStarSeparatorControl
open PhysicalEligibleReply PhysicalRacePrefixes PhysicalDoorRace
open BStarResetHealthyService BStarAcquireRailCoverage

local notation "hp" => (show 0<2 by decide)

/-- Literal success on the separator race guarantees the arbitrary-op
consume on the replay receipt cut. The complete original suffix
is retained, and the commuted prefix has the same physical endpoint. -/
theorem accepted_separator_cut {s n : Nat} {base y : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (q : Q y) (wait : Waiting hp base (S.getD 0 fall).1 op y)
    (clean : Clean (project (fun j=>S.getD j fall)) anyTag len y)
    (w : List (Fin n))
    (race : accepted (RearTrace.predecessor (S.getD 0 fall).1) 1 w=1) :
    let addr := fun j=>S.getD j fall
    let door := RearTrace.predecessor (addr 0).1
    ∃ gap tail, w=gap++door::tail ∧
      (∀ e∈gap,DisjointMarks e door) ∧
      Commuted w (door::(gap++tail)) ∧
      rawRun y (gap++[door])=rawRun (rawNext s y door) gap ∧
      ∃ pc,(pc=0 ∨ (op<pc ∧ pc<413)) ∧
        Ready addr len pc (rawNext s y door) ∧ Ready addr len pc (rawRun y (gap++[door])) := by
  dsimp only
  let door := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨gap,tail,rfl,ind⟩ := one_gap ((accepted_iff door 1 w).1 race)
  obtain ⟨R,_,pc,range,ready,oldReady⟩ := separator_replay C Q fiber closed sep gap tail ind q wait clean
  have End : rawRun y (gap++[door])=rawNext s (rawRun y gap) door :=
    BStarResetSchedule.run_append _ _ _ _
  have Prefix := rawRun_of_commuted y (bubble_door gap [] door ind)
  exact ⟨gap,tail,rfl,ind,R,by
      change rawRun y (gap++[door])=rawRun y (door::gap)
      simpa only [List.append_nil] using Prefix,
    pc,range,ready,End.symm ▸ oldReady⟩

/-- Literal success on a middle reset doublet gives its genuine
completed stage and a certified initial path of the next healthy
reset on the commuted tape, without assuming either gap empty. -/
theorem accepted_middle_reset_cut {s n : Nat} {base seed : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair (rows s) base i; continuation g.1 g.2=true)
    (H : op<2) (qs : Q seed) (pre w : List (Fin n)) :
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
    accepted door 2 w=1 →
    ∃ g₁ g₂ tail, w=g₁++door::(g₂++door::tail) ∧
      (∀ e∈g₁,DisjointMarks e door) ∧ (∀ e∈g₂,DisjointMarks e door) ∧
      Commuted (door::(pre++w)) (door::(pre++door::door::((g₁++g₂)++tail))) ∧
      BStarResetHealthyCycle.Stage hp addr len op seed (door::(pre++[door])) consumed ∧
      Seen (rawNext s) (project addr) (healthyTag (op+1)) len launched (.out 0) (g₁++g₂) (.out 0) ∧
      Q (rawRun launched (g₁++g₂)) ∧ Waiting hp base root (op+1) (rawRun launched (g₁++g₂)) := by
  dsimp only
  intro seen ok ph pc race
  let door := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨g₁,g₂,tail,rfl,A,D⟩ := two_gaps ((accepted_iff door 2 w).1 race)
  obtain ⟨R,stage,_,path,I,W⟩ := two_gaps_replay C Q fiber closed sep head cont H qs pre g₁ g₂ tail
    seen ok ph pc A D
  exact ⟨g₁,g₂,tail,rfl,A,D,R,stage,path,I,W⟩

/-- Literal success on the final race earns the last reset's consumed
prefix; disjoint marks are moved to the replay tail, not credited. -/
theorem accepted_final_reset_cut {s n : Nat} {base seed : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (H : op<3) (qs : Q seed) (pre w : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let door := RearTrace.predecessor root
    let old := rawRun (rawNext s seed door) pre
    let consumed := rawNext s old door
    Seen (rawNext s) (project addr) (healthyTag op) len (rawNext s seed door) (.out 0) pre (.back 0) →
    Eligible base addr len op old →
    (ctrlPhase.read (seed root).long).toNat=1 →
    (ctrlOp.read (seed root).long).toNat=op →
    accepted door 1 w=1 →
    ∃ gap tail, w=gap++door::tail ∧
      (∀ e∈gap,DisjointMarks e door) ∧
      Commuted (door::(pre++w)) (door::(pre++door::(gap++tail))) ∧
      BStarResetHealthyCycle.Stage hp addr len op seed (door::(pre++[door])) consumed ∧
      Ready addr len (op+1) consumed := by
  dsimp only
  intro seen ok ph pc race
  let door := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨gap,tail,rfl,A⟩ := one_gap ((accepted_iff door 1 w).1 race)
  obtain ⟨R,stage,_,N⟩ := final_gap_replay C Q fiber closed sep H qs pre gap tail seen ok ph pc A
  exact ⟨gap,tail,rfl,A,R,stage,N⟩

/-- With both actual races credited, the old two physical door rows can
be moved to the front. The physical state at the start of the next
observed journey is unchanged. -/
theorem middle_race_endpoint {s n : Nat} (y : Raw s n)
    (d : Fin n) (g₁ g₂ : List (Fin n))
    (A : ∀ e∈g₁,DisjointMarks e d) (B : ∀ e∈g₂,DisjointMarks e d) :
    rawRun y (g₁++d::(g₂++[d])) =
      rawRun (rawNext s (rawNext s y d) d) (g₁++g₂) := by
  have H := bubble_door g₁ (g₂++[d]) d A
  have K := commute_prefix [d]
    (bubble_door (g₁++g₂) [] d (fun e L=>(List.mem_append.mp L).elim (A e) (B e)))
  have M : Commuted (g₁++d::(g₂++[d])) (d::d::(g₁++g₂)) := by
    apply Commuted.trans H
    simpa only [List.append_assoc,List.append_nil,List.cons_append,List.nil_append,
      List.singleton_append] using K
  change rawRun y _ = rawRun y (d::d::(g₁++g₂))
  exact rawRun_of_commuted y M

/-- Replay continuation of the exact next healthy journey. Its first
part is Certified Seen staying at out 0; the rest is the actual
sampled journey, transported only by equality of the cut bytes. -/
theorem append_next_seen {s n : Nat} {y : Raw s n} {addr : Nat→Pos n}
    {len op : Nat} {g₁ g₂ t : List (Fin n)} {d : Fin n}
    (A : ∀ e∈g₁,DisjointMarks e d) (B : ∀ e∈g₂,DisjointMarks e d)
    (first : Seen (rawNext s) (project addr) (healthyTag op) len
      (rawNext s (rawNext s y d) d) (.out 0) (g₁++g₂) (.out 0))
    (later : Seen (rawNext s) (project addr) (healthyTag op) len
      (rawRun y (g₁++d::(g₂++[d]))) (.out 0) t (.back 0)) :
    Seen (rawNext s) (project addr) (healthyTag op) len
      (rawNext s (rawNext s y d) d) (.out 0) ((g₁++g₂)++t) (.back 0) :=
  by
    apply Seen.append first
    change Seen (rawNext s) (project addr) (healthyTag op) len
      (rawRun (rawNext s (rawNext s y d) d) (g₁++g₂)) (.out 0) t (.back 0)
    rw [←middle_race_endpoint y d g₁ g₂ A B]
    exact later

end L4.PhysicalRaceCutAdapters

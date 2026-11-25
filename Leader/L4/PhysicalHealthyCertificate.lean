import Leader.L4.PhysicalHealthyRaces
import Leader.L4.PhysicalRaceExactCut
import Leader.L4.ScoredTapeCertificates
import Leader.L4.PhysicalSixRaceReplay

namespace L4.PhysicalHealthyCertificate
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarLongFixedRouting
open BStarLongDoor BStarSeparatingRail BStarClearanceResidual
open BStarResetChartTouch BStarResetChartService BStarAcquireAnchors
open BStarResetSchedule BStarResetMarkAdapter BStarResetHealthyService BStarAcquireRailCoverage
open PhysicalEligibleReply PhysicalResetFirstReceipt PhysicalHealthyRaces PhysicalRaceExactCut
local notation "hp" => (show 0<2 by decide)

def Paid0 {s n : Nat} (base x : Raw s n) (Q : Raw s n→Prop)
    (addr : Nat→Pos n) (len : Nat) (w : List (Fin n)) : Prop :=
  let d := RearTrace.predecessor (addr 0).1
  ∃ u a b,w=u++(a++d::(b++[d])) ∧
    FirstResetReceiptCut base x Q addr len 0 u ∧
    (∀ e∈a,DisjointMarks e d) ∧ (∀ e∈b,DisjointMarks e d) ∧
    Q (rawRun x w) ∧ Launched base addr len 1 (rawRun x w)

def Paid1 {s n : Nat} (base x : Raw s n) (Q : Raw s n→Prop)
    (addr : Nat→Pos n) (len : Nat) (w : List (Fin n)) : Prop :=
  let d := RearTrace.predecessor (addr 0).1
  ∃ u a b,w=u++(a++d::(b++[d])) ∧
    ArrivedHealthy base x Q addr len 1 u ∧
    (∀ e∈a,DisjointMarks e d) ∧ (∀ e∈b,DisjointMarks e d) ∧
    Q (rawRun x w) ∧ Launched base addr len 2 (rawRun x w)

def Paid2 {s n : Nat} (base x : Raw s n) (Q : Raw s n→Prop)
    (addr : Nat→Pos n) (len : Nat) (w : List (Fin n)) : Prop :=
  let d := RearTrace.predecessor (addr 0).1
  ∃ u a,w=u++(a++[d]) ∧
    ArrivedHealthy base x Q addr len 2 u ∧
    (∀ e∈a,DisjointMarks e d) ∧
    Q (rawRun x w) ∧ Ready addr len 3 (rawRun x w)

def HealthyPost {s n : Nat} (base x : Raw s n) (Q : Raw s n→Prop)
    (addr : Nat→Pos n) (len : Nat) (w : List (Fin n)) : Prop :=
  ∃ w₀ w₁ w₂,w=w₀++(w₁++w₂) ∧
    Paid0 base x Q addr len w₀ ∧
    Paid1 base (rawRun x w₀) Q addr len w₁ ∧
    Paid2 base (rawRun (rawRun x w₀) w₁) Q addr len w₂

theorem paid0_at_exact_cut {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (u v : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let d := RearTrace.predecessor (addr 0).1
    ValidFirst (FirstResetReceiptCut base x Q addr len 0) d 2 (.racing u v .accept) →
    Paid0 base x Q addr len (u++v) := by
  dsimp only
  intro H
  let addr := fun j=>S.getD j fall
  let d := RearTrace.predecessor (addr 0).1
  have E := (exact_of_validFirst_accept _ d 2 (by decide) u v H).2
  obtain ⟨arr,a,b,t,F,A,B,P⟩ := first_reset0_doublet_accept C Q fiber closed sep u v H.1
  have nil := double_tail_nil E F A B
  subst t
  refine ⟨u,a,b,congrArg (u++·) F,arr,A,B,?_⟩
  rw [F]
  exact P

theorem paid1_at_exact_cut {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (u v : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let d := RearTrace.predecessor (addr 0).1
    ValidFirst (ArrivedHealthy base x Q addr len 1) d 2 (.racing u v .accept) →
    Paid1 base x Q addr len (u++v) := by
  dsimp only
  intro H
  let addr := fun j=>S.getD j fall
  let d := RearTrace.predecessor (addr 0).1
  have E := (exact_of_validFirst_accept _ d 2 (by decide) u v H).2
  obtain ⟨arr,a,b,t,F,A,B,P⟩ := healthy_middle_accept C Q fiber closed sep (by decide : 1<2) u v H.1
  have nil := double_tail_nil E F A B
  subst t
  refine ⟨u,a,b,congrArg (u++·) F,arr,A,B,?_⟩
  rw [F]
  exact P

theorem paid2_at_exact_cut {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (u v : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let d := RearTrace.predecessor (addr 0).1
    ValidFirst (ArrivedHealthy base x Q addr len 2) d 1 (.racing u v .accept) →
    Paid2 base x Q addr len (u++v) := by
  dsimp only
  intro H
  let addr := fun j=>S.getD j fall
  let d := RearTrace.predecessor (addr 0).1
  have E := (exact_of_validFirst_accept _ d 1 (by decide) u v H).2
  obtain ⟨arr,a,t,F,A,P⟩ := healthy_final_accept C Q fiber closed sep (by decide : 2<3) u v H.1
  have nil := single_tail_nil E F A
  subst t
  refine ⟨u,a,congrArg (u++·) F,arr,A,?_⟩
  rw [F]
  exact P

open ScoredTapeCertificates
open StoppedDoorRaceIID (score)

theorem paid0_of_race {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let d := RearTrace.predecessor (addr 0).1
    RaceOutcome (FirstResetReceiptCut base x Q addr len 0) d 2 w →
    Paid0 base x Q addr len w := by
  dsimp only
  intro V
  let d := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨u,v,rfl,T,E⟩ := V
  have Tcopy := T
  obtain ⟨p,t,F,N,q,R,q',L,J,q'',el⟩ := Tcopy
  obtain ⟨a,b,rest,G,D1,D2,Y⟩ := PhysicalHealthyReturnClock.next_healthy_on_actual_doublet
    C Q fiber closed sep (by decide : 0<2) q'' el v E.1
  have Z := double_tail_nil E G D1 D2
  subst rest
  refine ⟨u,a,b,congrArg (u++·) G,T,D1,D2,?_⟩
  rw [G]
  change Q (BStarResetSchedule.run (rawNext s) x (u++(a++d::(b++[d])))) ∧
    Launched base (fun j=>S.getD j fall)  len 1 (BStarResetSchedule.run (rawNext s) x (u++(a++d::(b++[d]))))
  rw [BStarResetSchedule.run_append]
  exact Y

theorem paid1_of_race {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let d := RearTrace.predecessor (addr 0).1
    RaceOutcome (ArrivedHealthy base x Q addr len 1) d 2 w →
    Paid1 base x Q addr len w := by
  dsimp only
  intro V
  let d := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨u,v,rfl,T,E⟩ := V
  obtain ⟨a,b,rest,G,D1,D2,Y⟩ := PhysicalHealthyReturnClock.next_healthy_on_actual_doublet
    C Q fiber closed sep (by decide : 1<2) T.2.1 T.2.2 v E.1
  have Z := double_tail_nil E G D1 D2
  subst rest
  refine ⟨u,a,b,congrArg (u++·) G,T,D1,D2,?_⟩
  rw [G]
  change Q (BStarResetSchedule.run (rawNext s) x (u++(a++d::(b++[d])))) ∧
    Launched base (fun j=>S.getD j fall)  len 2 (BStarResetSchedule.run (rawNext s) x (u++(a++d::(b++[d]))))
  rw [BStarResetSchedule.run_append]
  exact Y

theorem paid2_of_race {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let d := RearTrace.predecessor (addr 0).1
    RaceOutcome (ArrivedHealthy base x Q addr len 2) d 1 w →
    Paid2 base x Q addr len w := by
  dsimp only
  intro V
  let d := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨u,v,rfl,T,E⟩ := V
  obtain ⟨a,rfl,D⟩ := exact_single_split E
  obtain ⟨q,el⟩ := eligible_gap C Q fiber closed sep (by decide : 2<3) a D T.2.1 T.2.2
  refine ⟨u,a,rfl,T,D,?_⟩
  change Q (BStarResetSchedule.run (rawNext s) x (u++(a++[d]))) ∧
    Ready _ _ _ (BStarResetSchedule.run (rawNext s) x (u++(a++[d])))
  rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append]
  exact ⟨closed _ _ q,PhysicalEligibleReply.consume C (by decide) sep el⟩

/-- Three physically certified healthy stages spend five wins on one
sampled tape. No fresh clock is run until the previous exact race cut. -/
noncomputable def certificate_from_issue0 {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (hn : 4≤n)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair (rows s) base i; continuation g.1 g.2=true)
    (I : Boundary Q (oldH6 (rows s) base) hh (fun j=>S.getD j fall) len x)
    (zero : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=0) :
    Certificate n 3 729
      ((n+n*(2*len+1)+n*2)+((n*(2*len+1)+n*2)+(n*(2*len+1)+n*1)))
      (HealthyPost base x Q (fun j=>S.getD j fall) len) := by
  let addr := fun j=>S.getD j fall
  let d := RearTrace.predecessor (addr 0).1
  let A0 := FirstResetReceiptCut base x Q addr len 0
  have h0 := first_reset0_receipt_of_boundary C (by omega) Q fiber closed sep head cont I zero
  let R0 : Certificate n 3 27 (n+n*(2*len+1)+n*2) (Paid0 base x Q addr len) :=
    (race hn A0 d 3 2 (by decide) (by decide) _ h0).map (paid0_of_race C Q fiber closed sep)
  refine (R0.bind (by omega) (fun w v => ∃ w₁ w₂,v=w₁++w₂ ∧
    Paid1 base (rawRun x w) Q addr len w₁ ∧
    Paid2 base (rawRun (rawRun x w) w₁) Q addr len w₂) (fun w P0=>?_)).map ?_
  · let y := rawRun x w
    have ql : Q y ∧ Launched base addr len 1 y := by
      obtain ⟨_,_,_,_,_,_,_,q,L⟩ := P0
      exact ⟨q,L⟩
    let A1 := ArrivedHealthy base y Q addr len 1
    have h1 := healthy_exact_receipt_clock C Q fiber closed sep head cont (by decide : 1<3) ql.1 ql.2
    let R1 : Certificate n 27 243 (n*(2*len+1)+n*2) (Paid1 base y Q addr len) :=
      (race hn A1 d 1 2 (by decide) (by decide) _ h1).map (paid1_of_race C Q fiber closed sep)
    refine R1.bind (by omega) (fun w v=>Paid2 base (rawRun y w) Q addr len v) (fun w1 P1=>?_)
    let z := rawRun y w1
    have ql' : Q z ∧ Launched base addr len 2 z := by
      obtain ⟨_,_,_,_,_,_,_,q,L⟩ := P1
      exact ⟨q,L⟩
    let A2 := ArrivedHealthy base z Q addr len 2
    have h2 := healthy_exact_receipt_clock C Q fiber closed sep head cont (by decide : 2<3) ql'.1 ql'.2
    exact (race hn A2 d 0 1 (by decide) (by decide) _ h2).map (paid2_of_race C Q fiber closed sep)
  · intro w K
    obtain ⟨w₀,v,E,H₀,w₁,w₂,F,H₁,H₂⟩ := K
    exact ⟨w₀,w₁,w₂,by rw [E,F],H₀,H₁,H₂⟩

open PhysicalSixRaceReplay (pairWord)

/-- Flatten the accepted physical healthy chain into the literal
components consumed by the existing six-cut replay theorem. -/
theorem healthy_post_parts {s n : Nat} {base x : Raw s n}
    {Q : Raw s n→Prop} {addr : Nat→Pos n} {len : Nat} {w : List (Fin n)}
    (H : HealthyPost base x Q addr len w) :
    let d := RearTrace.predecessor (addr 0).1
    ∃ p t₀ a₀ b₀ t₁ a₁ b₁ t₂ gF,
      w=p++[d]++t₀++pairWord d a₀ b₀++t₁++pairWord d a₁ b₁++t₂++(gF++[d]) ∧
      let y := rawRun x p
      let x₀ := rawNext s y d
      let y₀ := rawRun x₀ t₀
      let x₁ := rawRun y₀ (pairWord d a₀ b₀)
      let y₁ := rawRun x₁ t₁
      let x₂ := rawRun y₁ (pairWord d a₁ b₁)
      Ready addr len 0 y ∧
      Seen (rawNext s) (project addr) (healthyTag 0) len x₀ (.out 0) t₀ (.back 0) ∧
      Seen (rawNext s) (project addr) (healthyTag 1) len x₁ (.out 0) t₁ (.back 0) ∧
      Seen (rawNext s) (project addr) (healthyTag 2) len x₂ (.out 0) t₂ (.back 0) ∧
      (∀ e∈a₀,DisjointMarks e d) ∧ (∀ e∈b₀,DisjointMarks e d) ∧
      (∀ e∈a₁,DisjointMarks e d) ∧ (∀ e∈b₁,DisjointMarks e d) ∧
      (∀ e∈gF,DisjointMarks e d) := by
  dsimp only
  let d := RearTrace.predecessor (addr 0).1
  obtain ⟨w₀,w₁,w₂,E,H₀,H₁,H₂⟩ := H
  obtain ⟨u₀,a₀,b₀,E₀,A₀,D₀,D₀',_,_⟩ := H₀
  obtain ⟨p,t₀,F₀,_,_,R,_,_,J₀,_,_⟩ := A₀
  obtain ⟨t₁,a₁,b₁,E₁,A₁,D₁,D₁',_,_⟩ := H₁
  obtain ⟨t₂,gF,E₂,A₂,DF,_,_⟩ := H₂
  have rp (z : Raw s n) (a b : List (Fin n)) : rawRun z (a++b)=rawRun (rawRun z a) b :=
    BStarResetSchedule.run_append _ _ _ _
  have w₀cut : rawRun x w₀=rawRun (rawRun (rawNext s (rawRun x p) d) t₀) (pairWord d a₀ b₀) := by
    rw [E₀,rp x u₀ _,F₀,rp x p _]; rfl
  have w₁cut : rawRun (rawRun x w₀) w₁=
      rawRun (rawRun (rawRun x w₀) t₁) (pairWord d a₁ b₁) := by rw [E₁,rp]; rfl
  refine ⟨p,t₀,a₀,b₀,t₁,a₁,b₁,t₂,gF,?_,R,J₀,?_,?_,D₀,D₀',D₁,D₁',DF⟩
  · rw [E,E₀,F₀,E₁,E₂]
    simp [pairWord,List.append_assoc]
  · rw [←w₀cut]
    exact A₁.1
  · rw [←w₀cut,←w₁cut]
    exact A₂.1

end L4.PhysicalHealthyCertificate
